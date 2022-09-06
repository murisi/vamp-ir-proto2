use std::fmt::{self, Display};
use crate::ast::{Module, VariableId, Pattern, Variable, TExpr, InfixOp, Function, Definition, Expr};
use crate::transform::{VarGen, collect_pattern_variables};
use std::collections::{HashMap, HashSet};

/* Collect all polymorphic variables occuring in the given expression. */
fn collect_expr_poly_vars(
    expr: &TExpr,
    map: &mut HashMap<VariableId, Variable>,
) {
    match &expr.v {
        Expr::Variable(_) => {},
        Expr::Sequence(seq) => {
            for expr in seq {
                collect_expr_poly_vars(expr, map);
            }
        },
        Expr::Product(prod) => {
            for expr in prod {
                collect_expr_poly_vars(expr, map);
            }
        },
        Expr::Infix(_, expr1, expr2) => {
            collect_expr_poly_vars(expr1, map);
            collect_expr_poly_vars(expr2, map);
        },
        Expr::Negate(expr1) => {
            collect_expr_poly_vars(expr1, map);
        },
        Expr::Application(expr1, expr2) => {
            collect_expr_poly_vars(expr1, map);
            collect_expr_poly_vars(expr2, map);
        },
        Expr::Function(fun) => {
            collect_expr_poly_vars(&*fun.1, map);
        },
        Expr::LetBinding(binding, body) => {
            collect_expr_poly_vars(&*binding.1, map);
            collect_pattern_variables(&binding.0, map);
            collect_expr_poly_vars(body, map);
        },
        Expr::Constant(_) => {},
    }
}

/* Collect all polymorphic variables occuring in the given definition. */
fn collect_def_poly_vars(
    def: &Definition,
    map: &mut HashMap<VariableId, Variable>,
) {
    collect_expr_poly_vars(&*def.0.1, map);
    collect_pattern_variables(&def.0.0, map);
}

/* Collect all polymorphic variables occuring in the given module. */
pub fn collect_module_poly_vars(
    module: &Module,
    map: &mut HashMap<VariableId, Variable>,
) {
    for def in &module.defs {
        collect_def_poly_vars(def, map);
    }
    for expr in &module.exprs {
        collect_expr_poly_vars(expr, map);
    }
}

/* Generate a unique type variables for each expression. */
fn allocate_expr_types(
    expr: &mut TExpr,
    gen: &mut VarGen,
) {
    let new_var = gen.generate_id();
    expr.t = Some(Type::Variable(Variable::new(new_var)));
    
    match &mut expr.v {
        Expr::Sequence(seq) => {
            for expr in seq {
                allocate_expr_types(expr, gen);
            }
        },
        Expr::Product(prod) => {
            for expr in prod {
                allocate_expr_types(expr, gen);
            }
        },
        Expr::Infix(_, expr1, expr2) => {
            allocate_expr_types(expr1, gen);
            allocate_expr_types(expr2, gen);
        },
        Expr::Negate(expr1) => {
            allocate_expr_types(expr1, gen);
        },
        Expr::Application(expr1, expr2) => {
            allocate_expr_types(expr1, gen);
            allocate_expr_types(expr2, gen);
        },
        Expr::Function(fun) => {
            allocate_expr_types(&mut *fun.1, gen);
        },
        Expr::LetBinding(binding, body) => {
            allocate_expr_types(&mut *binding.1, gen);
            allocate_expr_types(body, gen);
        },
        Expr::Constant(_) | Expr::Variable(_) => {},
    }
}

/* Generate unique type variables for everything within this definition. */
fn allocate_def_types(
    def: &mut Definition,
    gen: &mut VarGen,
) {
    allocate_expr_types(&mut *def.0.1, gen);
}

/* Generate unique type variables for everything within the given module. */
pub fn allocate_module_types(
    module: &mut Module,
    gen: &mut VarGen,
) {
    for def in &mut module.defs {
        allocate_def_types(def, gen);
    }
    for expr in &mut module.exprs {
        allocate_expr_types(expr, gen);
    }
}

/* A representation of expression types. */
#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Variable(Variable),
    Function(Box<Type>, Box<Type>),
    Product(Vec<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "int"),
            Type::Variable(var) => write!(f, "{}", var),
            Type::Function(a, b) => write!(f, "{} -> {}", a, b),
            Type::Product(prod) => {
                write!(f, "(")?;
                let mut iter = prod.iter();
                if let Some(elt) = iter.next() {
                    write!(f, "{}", elt)?;
                }
                while let Some(elt) = iter.next() {
                    write!(f, ", {}", elt)?;
                }
                write!(f, ")")?;
                Ok(())
            },
        }
    }
}

/* Get or generate the type variable associated with a given expression. */
fn expr_type_var(expr: &TExpr) -> &Type {
    expr.t.as_ref().unwrap()
}

/* Generate the type of expressions the given pattern can match. */
fn pattern_type(pat: &Pattern) -> Type {
    match pat {
        Pattern::Constant(_) => Type::Int,
        Pattern::Variable(var) => Type::Variable(var.clone()),
        Pattern::As(pat, _name) => pattern_type(pat),
        Pattern::Product(prod) => {
            let mut types = vec![];
            for pat in prod {
                types.push(pattern_type(pat));
            }
            Type::Product(types)
        }
    }
}

/* Check if the given variable occurs in the type expression. */
fn occurs_in(
    var1: &Variable,
    type2: &Type,
    types: &mut HashMap<VariableId, Type>,
) -> bool {
    match type2 {
        Type::Variable(var2) if var1.id == var2.id => true,
        Type::Variable(var2) if types.contains_key(&var2.id) =>
            occurs_in(var1, &types[&var2.id].clone(), types),
        Type::Variable(_) => false,
        Type::Int => false,
        Type::Product(prod) => {
            for elt in prod {
                if occurs_in(var1, elt, types) { return true; }
            }
            false
        },
        Type::Function(a, b) =>
            occurs_in(var1, a, types) || occurs_in(var1, b, types),
    }
}

/* Unify the type variable with the given type. */
fn unify_variable(
    var1: &Variable,
    type2: &Type,
    types: &mut HashMap<VariableId, Type>,
) {
    match (var1, type2) {
        (var1, Type::Variable(var2)) if var1.id == var2.id => {},
        (var1, type2) if types.contains_key(&var1.id) =>
            unify_types(&types[&var1.id].clone(), type2, types),
        (var1, Type::Variable(var2)) if types.contains_key(&var2.id) =>
            unify_types(&Type::Variable(var1.clone()), &types[&var2.id].clone(), types),
        (var1, type2) if !occurs_in(var1, type2, types) => {
            types.insert(var1.id, type2.clone());
        }
        _ => panic!("unable to match {:?} with {}", var1, type2),
    }
}

/* Unify the two given types together. */
fn unify_types(
    type1: &Type,
    type2: &Type,
    types: &mut HashMap<VariableId, Type>,
) {
    match (type1, type2) {
        (Type::Int, Type::Int) => {},
        (Type::Function(a1, b1), Type::Function(a2, b2)) => {
            unify_types(&*a1, &*a2, types);
            unify_types(&*b1, &*b2, types);
        },
        (Type::Product(prod1), Type::Product(prod2))
            if prod1.len() == prod2.len() =>
        {
            for (p1, p2) in prod1.iter().zip(prod2.iter()) {
                unify_types(p1, p2, types);
            }
        },
        (Type::Variable(v1), type2) => unify_variable(v1, type2, types),
        (type1, Type::Variable(v2)) => unify_variable(v2, type1, types),
        _ => panic!("unable to match {} with {}", type1, type2),
    }
}

/* Fully expand the variables in the given type. */
fn expand_type(
    typ: &Type,
    types: &HashMap<VariableId, Type>,
) -> Type {
    match typ {
        Type::Int => Type::Int,
        Type::Variable(var) if types.contains_key(&var.id) =>
            expand_type(&types[&var.id], types),
        Type::Variable(_) => typ.clone(),
        Type::Function(a, b) => Type::Function(
            Box::new(expand_type(a, types)),
            Box::new(expand_type(b, types))
        ),
        Type::Product(prod) => {
            let mut elts = Vec::new();
            for elt in prod {
                elts.push(expand_type(elt, types));
            }
            Type::Product(elts)
        }
    }
}

/* Consistently replace all type variables occuring in type expression with
 * fresh ones. Useful for let polymorphism. */
fn refresh_type_vars(
    typ: &mut Type,
    map: &mut HashMap<VariableId, VariableId>,
    gen: &mut VarGen
) {
    match typ {
        Type::Int => {},
        Type::Variable(var) => {
            if let Some(target) = map.get(&var.id) {
                var.id = *target;
            } else {
                map.insert(var.id, gen.generate_id());
                var.id = map[&var.id];
            }
        },
        Type::Function(a, b) => {
            refresh_type_vars(a, map, gen);
            refresh_type_vars(b, map, gen);
        },
        Type::Product(prod) => {
            for elt in prod {
                refresh_type_vars(elt, map, gen);
            }
        }
    }
}

/* Recursively infer the types of expressions in the given expression tree.
 * Works by repeatedly generating and solving equations in the given typing
 * context. */
fn infer_expr_types(
    expr: &TExpr,
    polymorphics: &HashSet<VariableId>,
    types: &mut HashMap<VariableId, Type>,
    gen: &mut VarGen,
) {
    match &expr.v {
        Expr::Constant(_) => {
            let expr_var = expr_type_var(expr);
            // num: int
            unify_types(expr_var, &Type::Int, types);
        },
        Expr::Infix(InfixOp::Equal, expr1, expr2) => {
            infer_expr_types(expr1, polymorphics, types, gen);
            infer_expr_types(expr2, polymorphics, types, gen);
            let expr_var = expr_type_var(expr);
            let expr1_var = expr_type_var(expr1);
            let expr2_var = expr_type_var(expr2);
            // a = b: ()
            unify_types(&expr_var, &Type::Product(vec![]), types);
            // a: c |- b: c
            unify_types(&expr1_var, &expr2_var, types);
        },
        Expr::Infix(
            InfixOp::Add | InfixOp::Subtract | InfixOp::Multiply | InfixOp::Divide,
            expr1,
            expr2
        ) => {
            infer_expr_types(expr1, polymorphics, types, gen);
            infer_expr_types(expr2, polymorphics, types, gen);
            let expr_var = expr_type_var(expr);
            let expr1_var = expr_type_var(expr1);
            let expr2_var = expr_type_var(expr2);
            // a op b: int
            unify_types(&expr_var, &Type::Int, types);
            // a: int
            unify_types(&expr1_var, &Type::Int, types);
            // b: int
            unify_types(&expr2_var, &Type::Int, types);
        },
        Expr::Negate(expr1) => {
            infer_expr_types(expr1, polymorphics, types, gen);
            let expr_var = expr_type_var(expr);
            let expr1_var = expr_type_var(expr1);
            // (-a): int
            unify_types(&expr_var, &Type::Int, types);
            // a: int
            unify_types(&expr1_var, &Type::Int, types);
        },
        Expr::Sequence(seq) => {
            for expr in seq {
                infer_expr_types(expr, polymorphics, types, gen);
            }
            let last_expr = seq.last().expect("encountered empty sequence");
            let expr_var = expr_type_var(expr);
            let last_expr_var = expr_type_var(last_expr);
            // aN: c |- (a1; ...; aN): c
            unify_types(&expr_var, &last_expr_var, types);
        },
        Expr::Product(prod) => {
            let mut prod_types = vec![];
            for expr in prod {
                infer_expr_types(expr, polymorphics, types, gen);
                let expr_var = expr_type_var(expr);
                prod_types.push(expr_var.clone());
            }
            let expr_var = expr_type_var(expr);
            // a1: t1, ... aN: tN |- (a1, ..., aN): (t1, ..., tN)
            unify_types(
                &expr_var,
                &Type::Product(prod_types),
                types
            );
        },
        Expr::Application(expr1, expr2) => {
            infer_expr_types(expr1, polymorphics, types, gen);
            infer_expr_types(expr2, polymorphics, types, gen);
            let expr_var = expr_type_var(expr);
            let expr1_var = expr_type_var(expr1);
            let expr2_var = expr_type_var(expr2);
            // b: t, a b: u |- a: t -> u
            unify_types(
                &expr1_var,
                &Type::Function(
                    Box::new(expr2_var.clone()),
                    Box::new(expr_var.clone())
                ),
                types
            );
        },
        Expr::Function(Function(params, expr1)) => {
            infer_expr_types(expr1, polymorphics, types, gen);
            let expr_var = expr_type_var(expr);
            let expr1_var = expr_type_var(expr1);
            let mut func_var = expr1_var.clone();
            for param in params.iter().rev() {
                let param_var = pattern_type(param);
                func_var = Type::Function(Box::new(param_var), Box::new(func_var));
            }
            // a1: t1, ..., aN: tN |- b: u
            // fun a1 ... aN -> b : t1 -> ... -> tN -> u
            unify_types(&expr_var, &func_var, types);
        },
        Expr::LetBinding(def, expr2) => {
            infer_expr_types(&*def.1, polymorphics, types, gen);
            let param_var = pattern_type(&def.0);
            let expr_var = expr_type_var(expr);
            let expr1_var = expr_type_var(&*def.1);
            let expr2_var = expr_type_var(expr2);
            unify_types(&expr1_var, &param_var, types);
            infer_expr_types(expr2, polymorphics, types, gen);
            unify_types(&expr_var, &expr2_var, types);
        },
        Expr::Variable(var) => {
            let expr_var = expr_type_var(expr);
            if polymorphics.contains(&var.id) {
                // If this variable is polymorphic, then we need to copy its
                // type expression so that we don't affect the original
                // variables.
                let mut fresh = expand_type(&Type::Variable(var.clone()), types);
                let mut new_map = HashMap::new();
                refresh_type_vars(&mut fresh, &mut new_map, gen);
                unify_types(
                    &expr_var,
                    &fresh,
                    types
                );
            } else {
                // If the variable is monomorphic, then we do want its
                // definition to be affected by future constraints.
                unify_types(
                    &expr_var,
                    &Type::Variable(Variable::new(var.id)),
                    types
                );
            }
        },
    }
}

/* Infer the type of the definition bindings and its contained sub-expressions.
 */
fn infer_def_types(
    def: &Definition,
    polymorphics: &HashSet<VariableId>,
    types: &mut HashMap<VariableId, Type>,
    gen: &mut VarGen,
) {
    infer_expr_types(&*def.0.1, polymorphics, types, gen);
    let param_var = pattern_type(&def.0.0);
    let expr_var = expr_type_var(&*def.0.1);
    unify_types(&expr_var, &param_var, types);
}

/* Type check the module using Hindley Milner. */
pub fn infer_module_types(annotated: &mut Module, gen: &mut VarGen) {
    allocate_module_types(annotated, gen);
    let mut types = HashMap::new();
    let mut polymorphics = HashMap::new();
    collect_module_poly_vars(annotated, &mut polymorphics);
    let polymorphics: HashSet::<_> = polymorphics.into_keys().collect();
    for def in &mut annotated.defs {
        infer_def_types(def, &polymorphics, &mut types, gen);
    }
    for expr in &mut annotated.exprs {
        infer_expr_types(expr, &polymorphics, &mut types, gen);
    }
}
