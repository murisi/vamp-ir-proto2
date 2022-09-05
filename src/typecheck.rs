use std::fmt::{self, Display};
use std::hash::{Hash, Hasher};
use crate::ast::{Module, VariableId, Pattern, Variable, Expression, InfixOp, Function, Definition};
use crate::transform::VarGen;
use std::collections::HashMap;

/* Useful for annotating objects like expressions without modifying their
 * structure. */
struct Id<'a, T>(&'a T);

impl<'a, T> Hash for Id<'a, T> {
    fn hash<H>(&self, hasher: &mut H) where H: Hasher {
        (self.0 as *const T).hash(hasher);
    }
}

impl<'a, T> PartialEq for Id<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        (self.0 as *const T) == (other.0 as *const T)
    }
}

impl<'a, T> Eq for Id<'a, T> {}

impl<'a, T> PartialOrd for Id<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        (self.0 as *const T).partial_cmp(&(other.0 as *const T))
    }
}

impl<'a, T> Ord for Id<'a, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.0 as *const T).cmp(&(other.0 as *const T))
    }
}

/* A representation of expression types. */
#[derive(Debug, Clone)]
enum Type {
    Int,
    Variable(Variable),
    Function(Box<Type>, Box<Type>),
    Product(Vec<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
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
fn expr_type_var<'a>(
    expr: &'a Expression,
    expr_types: &mut HashMap<Id<'a, Expression>, VariableId>,
    gen: &mut VarGen,
) -> Variable {
    if let Some(id) = expr_types.get(&Id(expr)) {
        Variable::new(*id)
    } else {
        let new_var = gen.generate_id();
        expr_types.insert(Id(expr), new_var);
        Variable::new(new_var)
    }
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

/* Recursively infer the types of expressions in the given expression tree.
 * Works by repeatedly generating and solving equations in the given typing
 * context. */
fn infer_expr_types<'a>(
    expr: &'a Expression,
    expr_types: &mut HashMap<Id<'a, Expression>, VariableId>,
    types: &mut HashMap<VariableId, Type>,
    gen: &mut VarGen,
) {
    match expr {
        Expression::Constant(_) => {
            let expr_var = expr_type_var(expr, expr_types, gen);
            unify_types(&Type::Variable(expr_var), &Type::Int, types);
        },
        Expression::Infix(InfixOp::Equal, expr1, expr2) => {
            infer_expr_types(expr1, expr_types, types, gen);
            infer_expr_types(expr2, expr_types, types, gen);
            let expr_var = expr_type_var(expr, expr_types, gen);
            let expr1_var = expr_type_var(expr1, expr_types, gen);
            let expr2_var = expr_type_var(expr2, expr_types, gen);
            unify_types(&Type::Variable(expr_var), &Type::Product(vec![]), types);
            unify_types(
                &Type::Variable(expr1_var),
                &Type::Variable(expr2_var),
                types
            );
        },
        Expression::Infix(
            InfixOp::Add | InfixOp::Subtract | InfixOp::Multiply | InfixOp::Divide,
            expr1,
            expr2
        ) => {
            infer_expr_types(expr1, expr_types, types, gen);
            infer_expr_types(expr2, expr_types, types, gen);
            let expr_var = expr_type_var(expr, expr_types, gen);
            let expr1_var = expr_type_var(expr1, expr_types, gen);
            let expr2_var = expr_type_var(expr2, expr_types, gen);
            unify_types(&Type::Variable(expr_var), &Type::Int, types);
            unify_types(&Type::Variable(expr1_var), &Type::Int, types);
            unify_types(&Type::Variable(expr2_var), &Type::Int, types);
        },
        Expression::Negate(expr1) => {
            infer_expr_types(expr1, expr_types, types, gen);
            let expr_var = expr_type_var(expr, expr_types, gen);
            let expr1_var = expr_type_var(expr1, expr_types, gen);
            unify_types(&Type::Variable(expr_var), &Type::Int, types);
            unify_types(&Type::Variable(expr1_var), &Type::Int, types);
        },
        Expression::Sequence(seq) => {
            for expr in seq {
                infer_expr_types(expr, expr_types, types, gen);
            }
            let last_expr = seq.last().expect("encountered empty sequence");
            let expr_var = expr_type_var(expr, expr_types, gen);
            let last_expr_var = expr_type_var(last_expr, expr_types, gen);
            unify_types(
                &Type::Variable(expr_var),
                &Type::Variable(last_expr_var),
                types
            );
        },
        Expression::Product(prod) => {
            let mut prod_types = vec![];
            for expr in prod {
                infer_expr_types(expr, expr_types, types, gen);
                let expr_var = expr_type_var(expr, expr_types, gen);
                prod_types.push(Type::Variable(expr_var));
            }
            let expr_var = expr_type_var(expr, expr_types, gen);
            unify_types(
                &Type::Variable(expr_var),
                &Type::Product(prod_types),
                types
            );
        },
        Expression::Application(expr1, expr2) => {
            infer_expr_types(expr1, expr_types, types, gen);
            infer_expr_types(expr2, expr_types, types, gen);
            let expr_var = expr_type_var(expr, expr_types, gen);
            let expr1_var = expr_type_var(expr1, expr_types, gen);
            let expr2_var = expr_type_var(expr2, expr_types, gen);
            unify_types(
                &Type::Variable(expr1_var),
                &Type::Function(
                    Box::new(Type::Variable(expr2_var)),
                    Box::new(Type::Variable(expr_var))
                ),
                types
            );
        },
        Expression::Function(Function(params, expr1)) => {
            infer_expr_types(expr1, expr_types, types, gen);
            let expr_var = expr_type_var(expr, expr_types, gen);
            let expr1_var = expr_type_var(expr1, expr_types, gen);
            let mut func_var = Type::Variable(expr1_var);
            for param in params.iter().rev() {
                let param_var = pattern_type(param);
                func_var = Type::Function(Box::new(param_var), Box::new(func_var));
            }
            unify_types(&Type::Variable(expr_var), &func_var, types);
        },
        Expression::LetBinding(def, expr2) => {
            infer_expr_types(&*def.1, expr_types, types, gen);
            let param_var = pattern_type(&def.0);
            let expr_var = expr_type_var(expr, expr_types, gen);
            let expr1_var = expr_type_var(&*def.1, expr_types, gen);
            let expr2_var = expr_type_var(expr2, expr_types, gen);
            unify_types(&Type::Variable(expr1_var), &param_var, types);
            infer_expr_types(expr2, expr_types, types, gen);
            unify_types(&Type::Variable(expr_var), &Type::Variable(expr2_var), types);
        },
        Expression::Variable(var) => {
            let expr_var = expr_type_var(expr, expr_types, gen);
            unify_types(
                &Type::Variable(expr_var),
                &Type::Variable(Variable::new(var.id)),
                types
            );
        },
    }
}

/* Infer the type of the definition bindings and its contained sub-expressions.
 */
fn infer_def_types<'a>(
    def: &'a Definition,
    expr_types: &mut HashMap<Id<'a, Expression>, VariableId>,
    types: &mut HashMap<VariableId, Type>,
    gen: &mut VarGen,
) {
    infer_expr_types(&*def.0.1, expr_types, types, gen);
    let param_var = pattern_type(&def.0.0);
    let expr_var = expr_type_var(&*def.0.1, expr_types, gen);
    unify_types(&Type::Variable(expr_var), &param_var, types);
}

/* Type check the module using Hindley Milner. */
pub fn infer_module_types(annotated: &mut Module, gen: &mut VarGen) -> bool {
    let mut expr_types = HashMap::new();
    let mut types = HashMap::new();
    for def in &mut annotated.defs {
        infer_def_types(def, &mut expr_types, &mut types, gen);
    }
    for expr in &mut annotated.exprs {
        infer_expr_types(expr, &mut expr_types, &mut types, gen);
    }
    false
}
