extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::collections::HashMap;
mod ast;
use std::fs;
use crate::ast::{Module, Definition, Expression, Pattern, VariableId, LetBinding};

/* A structure for generating unique variable IDs. */
struct VarGen(VariableId);

impl VarGen {
    pub fn new() -> Self {
        VarGen(0)
    }
    pub fn generate_id(&mut self) -> VariableId {
        let curr_id = self.0;
        self.0 += 1;
        curr_id
    }
}

/* Replaces variable IDs in the given expression according to the given
 * substitution map. */
fn substitute_expr_variables(
    expr: &mut Expression,
    map: &HashMap<VariableId, VariableId>,
    gen: &mut VarGen,
) {
    match expr {
        Expression::Sequence(exprs) => {
            for expr in exprs {
                substitute_expr_variables(expr, map, gen);
            }
        },
        Expression::Product(exprs) => {
            for expr in exprs {
                substitute_expr_variables(expr, map, gen);
            }
        },
        Expression::Infix(_, expr1, expr2) => {
            substitute_expr_variables(expr1, map, gen);
            substitute_expr_variables(expr2, map, gen);
        },
        Expression::Negate(expr) => {
            substitute_expr_variables(expr, map, gen);
        },
        Expression::Application(expr1, expr2) => {
            substitute_expr_variables(expr1, map, gen);
            substitute_expr_variables(expr2, map, gen);
        },
        Expression::Constant(_) => {},
        Expression::Variable(var) => {
            if let Some(id) = map.get(&var.id) {
                var.id = *id;
            }
        },
        Expression::Function(fun) => {
            let mut map = map.clone();
            for param in &mut fun.0 {
                refresh_pattern_variables(param, &mut map, gen);
            }
            substitute_expr_variables(&mut fun.1, &map, gen);
        },
        Expression::LetBinding(binding, expr) => {
            substitute_expr_variables(&mut binding.1, map, gen);
            let mut map = map.clone();
            refresh_pattern_variables(&mut binding.0, &mut map, gen);
            substitute_expr_variables(expr, &map, gen);
        },
    }
}

/* Match the given expression against the given pattern. */
fn match_pattern_expr(
    pat: &Pattern,
    expr: &Expression,
    map: &mut HashMap<VariableId, Expression>,
) {
    match (pat, expr) {
        (Pattern::As(pat, var), _) => {
            match_pattern_expr(pat, expr, map);
            map.insert(var.id, expr.clone());
        },
        (Pattern::Product(pats), Expression::Product(exprs))
            if pats.len() == exprs.len() =>
        {
            for (pat, expr) in pats.iter().zip(exprs.iter()) {
                match_pattern_expr(pat, expr, map);
            }
        },
        (Pattern::Variable(var), _) => {
            map.insert(var.id, expr.clone());
        },
        (Pattern::Constant(a), Expression::Constant(b)) if a == b => {},
        _ => panic!("unable to match {} against {}", expr, pat),
    }
}

/* Refresh all the variables occuring in the given pattern. */
fn refresh_pattern_variables(
    pat: &mut Pattern,
    map: &mut HashMap<VariableId, VariableId>,
    gen: &mut VarGen,
) {
    match pat {
        Pattern::As(pat, var) => {
            refresh_pattern_variables(pat, map, gen);
            map.insert(var.id, gen.generate_id());
            var.id = map[&var.id];
        },
        Pattern::Product(pats) => {
            for pat in pats {
                refresh_pattern_variables(pat, map, gen);
            }
        },
        Pattern::Variable(var) => {
            map.insert(var.id, gen.generate_id());
            var.id = map[&var.id];
        },
        Pattern::Constant(_) => {},
    }
}

/* Gives each variable occuring in the pattern a unique ID. Assumes that no
 * variable is used more than once in the pattern. */
fn number_pattern_variables(
    pat: &mut Pattern,
    map: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    match pat {
        Pattern::As(pat, var) => {
            number_pattern_variables(pat, map, gen);
            if let Some(name) = &var.name {
                var.id = gen.generate_id();
                map.insert(name.clone(), var.id);
            }
        },
        Pattern::Product(pats) => {
            for pat in pats {
                number_pattern_variables(pat, map, gen);
            }
        },
        Pattern::Variable(var) => {
            if let Some(name) = &var.name {
                var.id = gen.generate_id();
                map.insert(name.clone(), var.id);
            }
        },
        Pattern::Constant(_) => {},
    }
}

/* Numbers each variable occuring in the expression according to the binding in
 * local. If there is no such binding, then the global variable map is searched.
 * If not found, then a new global variable binding is made. Binding expressions
 * introduce new local bindings. */
fn number_expr_variables(
    expr: &mut Expression,
    locals: &HashMap<String, VariableId>,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    match expr {
        Expression::Sequence(exprs) => {
            for expr in exprs {
                number_expr_variables(expr, locals, globals, gen);
            }
        },
        Expression::Product(exprs) => {
            for expr in exprs {
                number_expr_variables(expr, locals, globals, gen);
            }
        },
        Expression::Infix(_, expr1, expr2) => {
            number_expr_variables(expr1, locals, globals, gen);
            number_expr_variables(expr2, locals, globals, gen);
        },
        Expression::Negate(expr) => {
            number_expr_variables(expr, locals, globals, gen);
        },
        Expression::Application(expr1, expr2) => {
            number_expr_variables(expr1, locals, globals, gen);
            number_expr_variables(expr2, locals, globals, gen);
        },
        Expression::Constant(_) => {},
        Expression::Variable(var) => {
            if let Some(name) = &var.name {
                if let Some(id) = locals.get(name) {
                    var.id = *id;
                } else if let Some(id) = globals.get(name) {
                    var.id = *id;
                } else {
                    var.id = gen.generate_id();
                    globals.insert(name.clone(), var.id);
                }
            }
        },
        Expression::Function(fun) => {
            let mut locals = locals.clone();
            for param in &mut fun.0 {
                number_pattern_variables(param, &mut locals, gen);
            }
            number_expr_variables(&mut fun.1, &mut locals, globals, gen);
        },
        Expression::LetBinding(binding, expr) => {
            let mut locals = locals.clone();
            number_expr_variables(&mut binding.1, &mut locals, globals, gen);
            number_pattern_variables(&mut binding.0, &mut locals, gen);
            number_expr_variables(expr, &mut locals, globals, gen);
        },
    }
}

/* Numbers the variables occuring in the definition. Essentially numbers the
 * inner expression, and then numbers the definition pattern variables in global
 * scope. */
fn number_def_variables(
    def: &mut Definition,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    let locals = HashMap::new();
    number_expr_variables(&mut *def.0.1, &locals, globals, gen);
    number_pattern_variables(&mut def.0.0, globals, gen);
}

/* Numbers the variables occuring in the module definitions and then those
 * occuring in the module expressions. */
fn number_module_variables(
    module: &mut Module,
    gen: &mut VarGen,
) {
    let mut globals = HashMap::new();
    for def in &mut module.defs {
        number_def_variables(def, &mut globals, gen);
    }
    let locals = HashMap::new();
    for expr in &mut module.exprs {
        number_expr_variables(expr, &locals, &mut globals, gen);
    }
}

/* Replace each function application occuring in the expression with a let
 * binding containing an inlined body. */
fn apply_functions(
    expr: &mut Expression,
    bindings: &HashMap<VariableId, Expression>,
    gen: &mut VarGen,
) -> Expression {
    match expr {
        Expression::Application(expr1, expr2) => {
            match &mut **expr1 {
                Expression::Application(_, _) => {
                    apply_functions(expr1, bindings, gen);
                    apply_functions(expr, bindings, gen)
                },
                Expression::Variable(var) => {
                    if let Some(val) = bindings.get(&var.id) {
                        *expr = Expression::Application(Box::new(val.clone()), expr2.clone());
                        apply_functions(expr, bindings, gen)
                    } else {
                        panic!("encountered unbound variable {}", var)
                    }
                },
                Expression::Function(_) => {
                    let substitutions = HashMap::new();
                    substitute_expr_variables(expr1, &substitutions, gen);
                    if let Expression::Function(fun) = &mut **expr1 {
                        if fun.0.is_empty() {
                            unreachable!("functions should have at least one parameter");
                        }
                        let arg1 = fun.0.remove(0);
                        let new_body = if fun.0.is_empty() { &*fun.1 } else { expr1 };
                        let new_bind = LetBinding(arg1, expr2.clone());
                        *expr = Expression::LetBinding(new_bind, Box::new(new_body.clone()));
                        apply_functions(expr, bindings, gen)
                    } else {
                        unreachable!("refreshing variables changed expression type")
                    }
                },
                Expression::Sequence(seq) => {
                    if let Some(val) = seq.last_mut() {
                        *val = Expression::Application(Box::new(val.clone()), expr2.clone());
                        *expr = *expr1.clone();
                        apply_functions(expr, bindings, gen)
                    } else {
                        unreachable!("encountered an empty sequence")
                    }
                },
                Expression::LetBinding(_, body) => {
                    *body = Box::new(Expression::Application(body.clone(), expr2.clone()));
                    *expr = *expr1.clone();
                    apply_functions(expr, bindings, gen)
                },
                Expression::Infix(_, _, _) => {
                    panic!("cannot apply argument {} to infix {}", expr2, expr1)
                },
                Expression::Negate(_) => {
                    panic!("cannot apply argument {} to negation {}", expr2, expr1)
                },
                Expression::Product(_) => {
                    panic!("cannot apply argument {} to tuple {}", expr2, expr1)
                },
                Expression::Constant(_) => {
                    panic!("cannot apply argument {} to constant {}", expr2, expr1)
                },
            }
        },
        Expression::LetBinding(binding, body) => {
            let val = apply_functions(&mut *binding.1, bindings, gen);
            let mut bindings = bindings.clone();
            match_pattern_expr(&binding.0, &val, &mut bindings);
            apply_functions(body, &bindings, gen)
        },
        Expression::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(apply_functions(expr, &bindings, gen));
            }
            if let Some(val) = val {
                val
            } else {
                unreachable!("encountered an empty sequence")
            }
        },
        Expression::Product(prod) => {
            let mut vals = vec![];
            for expr in prod {
                vals.push(apply_functions(expr, &bindings, gen));
            }
            Expression::Product(vals)
        },
        Expression::Infix(op, expr1, expr2) => {
            let expr1 = apply_functions(expr1, &bindings, gen);
            let expr2 = apply_functions(expr2, &bindings, gen);
            Expression::Infix(op.clone(), Box::new(expr1), Box::new(expr2))
        },
        Expression::Negate(expr1) => {
            Expression::Negate(Box::new(apply_functions(expr1, &bindings, gen)))
        },
        Expression::Constant(val) => Expression::Constant(*val),
        Expression::Variable(var) => {
            if let Some(val) = bindings.get(&var.id) {
                val.clone()
            } else {
                expr.clone()
            }
        },
        Expression::Function(fun) => Expression::Function(fun.clone()),
    }
}

/* Replace each function application occuring in the definition with a let
 * binding containing an inlined body. */
fn apply_def_functions(
    def: &mut Definition,
    bindings: &mut HashMap<VariableId, Expression>,
    gen: &mut VarGen,
) {
    let val = apply_functions(&mut def.0.1, bindings, gen);
    match_pattern_expr(&def.0.0, &val, bindings);
}

/* Replace each function application occuring in the module with a let
 * binding containing an inlined body. */
fn apply_module_functions(
    module: &mut Module,
    gen: &mut VarGen,
) {
    let mut bindings = HashMap::new();
    for def in &mut module.defs {
        apply_def_functions(def, &mut bindings, gen);
    }
    for expr in &mut module.exprs {
        apply_functions(expr, &mut bindings, gen);
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() < 2 {
        panic!("please supply the vamp-ir file path");
    }
    let unparsed_file = fs::read_to_string(args[1].clone()).expect("cannot read file");
    let mut module = Module::parse(&unparsed_file).unwrap();
    let mut vg = VarGen::new();
    number_module_variables(&mut module, &mut vg);
    apply_module_functions(&mut module, &mut vg);
    println!("{}", module);
}
