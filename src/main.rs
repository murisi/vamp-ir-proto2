mod ast;
mod transform;
extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::fs;
use crate::ast::{Module, VariableId, Expression, InfixOp};
use crate::transform::{compile, collect_module_variables};
use ark_ff::PrimeField;
use ark_ec::TEModelParameters;
use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ed_on_bls12_381::EdwardsParameters as JubJubParameters;
use plonk_core::circuit::{verify_proof, Circuit};
use ark_poly_commit::{sonic_pc::SonicKZG10, PolynomialCommitment};
use ark_poly::polynomial::univariate::DensePolynomial;
use rand_core::OsRng;
use plonk::error::to_pc_error;
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::marker::PhantomData;
//use crate::ast::{Program, Literal, Expression, ArithOp, RelOp, Term, Predicate, Clause};
use std::io::Write;
use plonk_core::prelude::VerifierData;
//use crate::transform::{compile_program, collect_program_variables};

// Make field elements from signed values
fn make_constant<F: PrimeField>(c: i32) -> F {
    if c >= 0 {
        F::from(c as u32)
    } else {
        -F::from((-c) as u32)
    }
}

struct PlonkModule<F, P>
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
    fn new(module: Module) -> PlonkModule<F, P> {
        let mut variables = HashMap::new();
        collect_module_variables(&module, &mut variables);
        let mut variable_map = HashMap::new();
        for variable in variables.keys() {
            variable_map.insert(*variable, F::default());
        }
        PlonkModule { module, variable_map, phantom: PhantomData }
    }

    /* Populate the input and auxilliary variables from the given program inputs
       and choice points. */
    /*fn populate_variables(
        &mut self,
        var_assignments: BTreeMap<ast::Variable, i32>,
        choice_points: HashMap<Vec<usize>, i32>
    ) {
        // Get the definitions necessary to populate auxiliary variables
        let mut definitions = self.module.definitions.clone();
        // Hard-code constant definitions for choice points and variable
        // assignments
        let mut remaining_choices: BTreeSet<_> =
            self.module.choice_points.values().collect();
        for (path, choice) in &choice_points {
            let choice_var = self.module.choice_points[path].clone();
            remaining_choices.remove(&choice_var);
            definitions.insert(choice_var, Expression::Term(Term::Constant(*choice)));
        }
        // Set the remaining choices to arbitrary values since they will be
        // cancelled out in computations
        for choice_var in remaining_choices {
            definitions.insert(choice_var.clone(), Expression::Term(Term::Constant(0)));
        }
        for (var, value) in &var_assignments {
            definitions.insert(var.clone(), Expression::Term(Term::Constant(*value)));
        }
        // Start deriving witnesses
        for (var, value) in &mut self.variable_map {
            let var_expr = Expression::Term(Term::Variable(var.clone()));
            let expr_val = evaluate_expr(&var_expr, &mut definitions);
            *value = make_constant(expr_val);
        }
    }*/
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
                                .out(-op1)
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

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() < 2 {
        panic!("please supply the vamp-ir file path");
    }
    let unparsed_file = fs::read_to_string(args[1].clone()).expect("cannot read file");
    let module = Module::parse(&unparsed_file).unwrap();
    let module_3ac = compile(module);
    println!("{}\n", module_3ac);
}
