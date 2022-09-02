use crate::ast::{Module, VariableId, Expression, InfixOp, Pattern};
use crate::transform::collect_module_variables;
use ark_ff::PrimeField;
use ark_ec::TEModelParameters;
use plonk_core::circuit::Circuit;
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use std::collections::{BTreeMap, HashMap};
use std::marker::PhantomData;

// Make field elements from signed values
fn make_constant<F: PrimeField>(c: i32) -> F {
    if c >= 0 {
        F::from(c as u32)
    } else {
        -F::from((-c) as u32)
    }
}

/* Evaluate the given expression sourcing any variables from the given map. */
fn evaluate_expr(expr: &Expression, defs: &mut HashMap<VariableId, Expression>) -> i32 {
    match expr {
        Expression::Constant(c) => *c,
        Expression::Variable(v) => {
            let val = evaluate_expr(&defs[&v.id].clone(), defs);
            defs.insert(v.id, Expression::Constant(val));
            val
        },
        Expression::Negate(e) => -evaluate_expr(e, defs),
        Expression::Infix(InfixOp::Add, a, b) =>
            evaluate_expr(&a, defs) +
            evaluate_expr(&b, defs),
        Expression::Infix(InfixOp::Subtract, a, b) =>
            evaluate_expr(&a, defs) -
            evaluate_expr(&b, defs),
        Expression::Infix(InfixOp::Multiply, a, b) =>
            evaluate_expr(&a, defs) *
            evaluate_expr(&b, defs),
        Expression::Infix(InfixOp::Divide, a, b) =>
            evaluate_expr(&a, defs) /
            evaluate_expr(&b, defs),
        _ => unreachable!("encountered unexpected expression: {}", expr),
    }
}

pub struct PlonkModule<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>, {
    module: Module,
    variable_map: HashMap<VariableId, F>,
    phantom: PhantomData<P>,
}

impl<F, P> PlonkModule<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    /* Make new circuit with default assignments to all variables in module. */
    pub fn new(module: Module) -> PlonkModule<F, P> {
        let mut variables = HashMap::new();
        collect_module_variables(&module, &mut variables);
        let mut variable_map = HashMap::new();
        for variable in variables.keys() {
            variable_map.insert(*variable, F::default());
        }
        PlonkModule { module, variable_map, phantom: PhantomData }
    }

    /* Populate input and auxilliary variables from the given program inputs. */
    pub fn populate_variables(
        &mut self,
        var_assignments: HashMap<VariableId, i32>,
    ) {
        // Get the definitions necessary to populate auxiliary variables
        let mut definitions = HashMap::new();
        for def in &self.module.defs {
            if let Pattern::Variable(var) = &def.0.0 {
                definitions.insert(var.id, *def.0.1.clone());
            }
        }
        for (var, value) in &var_assignments {
            definitions.insert(*var, Expression::Constant(*value));
        }
        // Start deriving witnesses
        for (var, value) in &mut self.variable_map {
            let var_expr = Expression::Variable(crate::ast::Variable::new(*var));
            let expr_val = evaluate_expr(&var_expr, &mut definitions);
            *value = make_constant(expr_val);
        }
    }
}

impl<F, P> Circuit<F, P> for PlonkModule<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    const CIRCUIT_ID: [u8; 32] = [0xff; 32];

    fn gadget(
        &mut self,
        composer: &mut StandardComposer<F, P>,
    ) -> Result<(), Error> {
        let mut inputs = BTreeMap::new();
        for (var, field_elt) in &self.variable_map {
            inputs.insert(var, composer.add_input(*field_elt));
        }
        let zero = composer.zero_var();
        for expr in &self.module.exprs {
            if let Expression::Infix(InfixOp::Equal, lhs, rhs) = expr {
                match (&**lhs, &**rhs) {
                    // Variables on the LHS
                    // v1 = v2
                    (
                        Expression::Variable(v1),
                        Expression::Variable(v2),
                    ) => {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(zero))
                                .add(F::one(), -F::one())
                        });
                    },
                    // v1 = c2
                    (
                        Expression::Variable(v1),
                        Expression::Constant(c2),
                    ) => {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(-c2))
                        });
                    },
                    // v1 = -c2
                    (
                        Expression::Variable(v1),
                        Expression::Negate(e2),
                    ) if matches!(&**e2, Expression::Constant(c2) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(*c2))
                        });
                        true
                    }) => {},
                    // v1 = -v2
                    (
                        Expression::Variable(v1),
                        Expression::Negate(e2),
                    ) if matches!(&**e2, Expression::Variable(v2) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(zero))
                                .add(F::one(), F::one())
                        });
                        true
                    }) => {},
                    // v1 = c2 + c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(-c2-c3))
                        });
                        true
                    }) => {},
                    // v1 = v2 + c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(zero))
                                .add(F::one(), -F::one())
                                .constant(make_constant(-c3))
                        });
                        true
                    }) => {},
                    // v1 = c2 + v3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v3.id], Some(zero))
                                .add(F::one(), -F::one())
                                .constant(make_constant(-c2))
                        });
                        true
                    }) => {},
                    // v1 = v2 + v3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(inputs[&v3.id]))
                                .add(F::one(), -F::one())
                                .out(-F::one())
                        });
                        true
                    }) => {},
                    // v1 = c2 - c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(-c2+c3))
                        });
                        true
                    }) => {},
                    // v1 = v2 - c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(zero))
                                .add(F::one(), -F::one())
                                .constant(make_constant(*c3))
                        });
                        true
                    }) => {},
                    // v1 = c2 - v3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v3.id], Some(zero))
                                .add(F::one(), F::one())
                                .constant(make_constant(-c2))
                        });
                        true
                    }) => {},
                    // v1 = v2 - v3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(inputs[&v3.id]))
                                .add(F::one(), -F::one())
                                .out(F::one())
                        });
                        true
                    }) => {},
                    // v1 = c2 / c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        let op1: F = make_constant(*c2);
                        let op2: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(-(op1/op2))
                        });
                        true
                    }) => {},
                    // v1 = v2 / c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        let op2: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(zero))
                                .add(F::one(), -(F::one()/op2))
                        });
                        true
                    }) => {},
                    // v1 = c2 / v3 ***
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        let op1: F = make_constant(*c2);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v3.id], Some(zero))
                                .mul(F::one())
                                .constant(-op1)
                        });
                        true
                    }) => {},
                    // v1 = v2 / v3 ***
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v3.id], Some(inputs[&v2.id]))
                                .mul(F::one())
                                .out(-F::one())
                        });
                        true
                    }) => {},
                    // v1 = c2 * c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        let op1: F = make_constant(*c2);
                        let op2: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(-(op1*op2))
                        });
                        true
                    }) => {},
                    // v1 = v2 * c3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        let op2: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v2.id], Some(zero))
                                .add(F::one(), -op2)
                        });
                        true
                    }) => {},
                    // v1 = c2 * v3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        let op2: F = make_constant(*c2);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v1.id], inputs[&v3.id], Some(zero))
                                .add(F::one(), -op2)
                        });
                        true
                    }) => {},
                    // v1 = v2 * v3
                    (
                        Expression::Variable(v1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], inputs[&v3.id], Some(inputs[&v1.id]))
                                .mul(F::one())
                                .out(-F::one())
                        });
                        true
                    }) => {},
                    // Now for constants on the LHS
                    // c1 = v2
                    (
                        Expression::Constant(c1),
                        Expression::Variable(v2),
                    ) => {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(-c1))
                        });
                    },
                    // c1 = c2
                    (
                        Expression::Constant(c1),
                        Expression::Constant(c2),
                    ) => {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(zero, zero, Some(zero))
                                .add(F::zero(), F::zero())
                                .constant(make_constant(c2-c1))
                        });
                    },
                    // c1 = -c2
                    (
                        Expression::Constant(c1),
                        Expression::Negate(e2),
                    ) if matches!(&**e2, Expression::Constant(c2) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(zero, zero, Some(zero))
                                .add(F::zero(), F::zero())
                                .constant(make_constant(c1+*c2))
                        });
                        true
                    }) => {},
                    // c1 = -v2
                    (
                        Expression::Constant(c1),
                        Expression::Negate(e2),
                    ) if matches!(&**e2, Expression::Variable(v2) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(*c1))
                        });
                        true
                    }) => {},
                    // c1 = c2 + c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(zero, zero, Some(zero))
                                .add(F::zero(), F::zero())
                                .constant(make_constant(c1-c2-c3))
                        });
                        true
                    }) => {},
                    // c1 = v2 + c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(c3-c1))
                        });
                        true
                    }) => {},
                    // c1 = c2 + v3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v3.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(c2-c1))
                        });
                        true
                    }) => {},
                    // c1 = v2 + v3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Add, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], inputs[&v3.id], Some(zero))
                                .add(F::one(), F::one())
                                .constant(make_constant(-c1))
                        });
                        true
                    }) => {},
                    // c1 = c2 - c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(zero, zero, Some(zero))
                                .add(F::zero(), F::zero())
                                .constant(make_constant(c2-c3-c1))
                        });
                        true
                    }) => {},
                    // c1 = v2 - c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(-*c3-c1))
                        });
                        true
                    }) => {},
                    // c1 = c2 - v3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v3.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(make_constant(c1-c2))
                        });
                        true
                    }) => {},
                    // c1 = v2 - v3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Subtract, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], inputs[&v3.id], Some(zero))
                                .add(F::one(), -F::one())
                                .constant(make_constant(-c1))
                        });
                        true
                    }) => {},
                    // c1 = c2 / c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        let op2: F = make_constant(*c2);
                        let op3: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(zero, zero, Some(zero))
                                .add(F::zero(), F::zero())
                                .constant(op1-(op2/op3))
                        });
                        true
                    }) => {},
                    // c1 = v2 / c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        let op3: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], zero, Some(zero))
                                .add(F::one(), F::zero())
                                .constant(-(op1*op3))
                        });
                        true
                    }) => {},
                    // c1 = c2 / v3 ***
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        let op2: F = make_constant(*c2);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v3.id], zero, Some(zero))
                                .constant(-(op2/op1))
                        });
                        true
                    }) => {},
                    // c1 = v2 / v3 ***
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Divide, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], inputs[&v3.id], Some(zero))
                                .add(F::one(), -op1)
                        });
                        true
                    }) => {},
                    // c1 = c2 * c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Constant(c3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        let op2: F = make_constant(*c2);
                        let op3: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(zero, zero, Some(zero))
                                .add(F::zero(), F::zero())
                                .constant(op1-(op2*op3))
                        });
                        true
                    }) => {},
                    // c1 = v2 * c3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Constant(c3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        let op3: F = make_constant(*c3);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], zero, Some(zero))
                                .add(op3, F::zero())
                                .constant(-op1)
                        });
                        true
                    }) => {},
                    // c1 = c2 * v3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Constant(c2),
                        Expression::Variable(v3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        let op2: F = make_constant(*c2);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v3.id], zero, Some(zero))
                                .add(op2, F::zero())
                                .constant(-op1)
                        });
                        true
                    }) => {},
                    // c1 = v2 * v3
                    (
                        Expression::Constant(c1),
                        Expression::Infix(InfixOp::Multiply, e2, e3),
                    ) if matches!((&**e2, &**e3), (
                        Expression::Variable(v2),
                        Expression::Variable(v3),
                    ) if {
                        let op1: F = make_constant(*c1);
                        composer.arithmetic_gate(|gate| {
                            gate.witness(inputs[&v2.id], inputs[&v3.id], Some(zero))
                                .mul(F::one())
                                .constant(-op1)
                        });
                        true
                    }) => {},
                    _ => panic!("unsupported constraint encountered")
                }
            }
        }
        Ok(())
    }

    fn padded_circuit_size(&self) -> usize {
        1 << 10
    }
}
