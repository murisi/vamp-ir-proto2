extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::collections::HashMap;
mod ast;
use std::fs;
use crate::ast::{Module, Definition, Expression, Pattern, VariableId, LetBinding, Variable};

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
fn refresh_expr_variables(
    expr: &mut Expression,
    map: &HashMap<VariableId, VariableId>,
    gen: &mut VarGen,
) {
    match expr {
        Expression::Sequence(exprs) => {
            for expr in exprs {
                refresh_expr_variables(expr, map, gen);
            }
        },
        Expression::Product(exprs) => {
            for expr in exprs {
                refresh_expr_variables(expr, map, gen);
            }
        },
        Expression::Infix(_, expr1, expr2) => {
            refresh_expr_variables(expr1, map, gen);
            refresh_expr_variables(expr2, map, gen);
        },
        Expression::Negate(expr) => {
            refresh_expr_variables(expr, map, gen);
        },
        Expression::Application(expr1, expr2) => {
            refresh_expr_variables(expr1, map, gen);
            refresh_expr_variables(expr2, map, gen);
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
            refresh_expr_variables(&mut fun.1, &map, gen);
        },
        Expression::LetBinding(binding, expr) => {
            refresh_expr_variables(&mut binding.1, map, gen);
            let mut map = map.clone();
            refresh_pattern_variables(&mut binding.0, &mut map, gen);
            refresh_expr_variables(expr, &map, gen);
        },
    }
}

/* Match the given expression against the given pattern. */
fn match_pattern_expr(
    pat: &Pattern,
    expr: &Expression,
    map: &mut HashMap<VariableId, Expression>,
    gen: &mut VarGen,
) {
    match (pat, expr) {
        (pat, Expression::Variable(var)) if map.contains_key(&var.id) =>
            match_pattern_expr(pat, &map[&var.id].clone(), map, gen),
        (Pattern::As(pat, var), expr) => {
            match_pattern_expr(pat, expr, map, gen);
            map.insert(var.id, expr.clone());
        },
        (Pattern::Variable(var), expr) => {
            map.insert(var.id, expr.clone());
        },
        (Pattern::Product(pats), Expression::Product(exprs))
            if pats.len() == exprs.len() =>
        {
            for (pat, expr) in pats.iter().zip(exprs.iter()) {
                match_pattern_expr(pat, expr, map, gen);
            }
        },
        (Pattern::Product(pats), Expression::Variable(var)) => {
            let mut inner_exprs = vec![];
            for _ in pats {
                let new_var = Variable::new(gen.generate_id());
                inner_exprs.push(Expression::Variable(new_var));
            }
            map.insert(var.id, Expression::Product(inner_exprs));
            match_pattern_expr(pat, expr, map, gen);
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
 * binding containing an inlined body. Returns a normal form of the expression.
 */
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
                    refresh_expr_variables(expr1, &substitutions, gen);
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
            match_pattern_expr(&binding.0, &val, &mut bindings, gen);
            apply_functions(body, &bindings, gen)
        },
        Expression::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(apply_functions(expr, &bindings, gen));
            }
            val.expect("encountered empty sequence")
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
    match_pattern_expr(&def.0.0, &val, bindings, gen);
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

/* Try to determine the internal structure of variables by unifying all patterns
 * with their corresponding expressions. */
fn elaborate_variables(
    expr: &Expression,
    map: &mut HashMap<VariableId, Expression>,
    gen: &mut VarGen,
) -> Expression {
    match expr {
        Expression::LetBinding(binding, body) => {
            let val = elaborate_variables(&*binding.1, map, gen);
            match_pattern_expr(&binding.0, &val, map, gen);
            elaborate_variables(body, map, gen)
        },
        Expression::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(elaborate_variables(expr, map, gen))
            }
            val.expect("encountered empty sequence")
        },
        Expression::Product(prod) => {
            let mut vals = vec![];
            for expr in prod {
                vals.push(elaborate_variables(expr, map, gen));
            }
            Expression::Product(vals)
        },
        Expression::Infix(op, expr1, expr2) => {
            let expr1 = elaborate_variables(expr1, map, gen);
            let expr2 = elaborate_variables(expr2, map, gen);
            Expression::Infix(*op, Box::new(expr1.clone()), Box::new(expr2.clone()))
        },
        Expression::Negate(expr1) => {
            Expression::Negate(Box::new(elaborate_variables(expr1, map, gen)))
        },
        Expression::Variable(var) if map.contains_key(&var.id) => {
            elaborate_variables(&map[&var.id].clone(), map, gen)
        },
        Expression::Function(_) | Expression::Constant(_) |
        Expression::Variable(_) => expr.clone(),
        Expression::Application(_, _) => {
            unreachable!("cannot elaborate variable values before inlining");
        }
    }
}

/* Try to determine the internal structure of variables by unifying all patterns
 * with their corresponding expressions. */
fn elaborate_def_variables(
    def: &Definition,
    map: &mut HashMap<VariableId, Expression>,
    gen: &mut VarGen,
) {
    let val = elaborate_variables(&*def.0.1, map, gen);
    match_pattern_expr(&def.0.0, &val, map, gen);
}

/* Try to determine the internal structure of variables by unifying all patterns
 * with their corresponding expressions. */
fn elaborate_module_variables(
    module: &Module,
    map: &mut HashMap<VariableId, Expression>,
    gen: &mut VarGen,
) {
    for def in &module.defs {
        elaborate_def_variables(def, map, gen);
    }
    for expr in &module.exprs {
        elaborate_variables(expr, map, gen);
    }
}

/* Substitute variables into the pattern according to the map. */
fn substitute_pattern_variables(
    pat: &mut Pattern,
    pat_map: &HashMap<VariableId, Pattern>,
) {
    match pat {
        Pattern::Variable(var) if pat_map.contains_key(&var.id) => {
            *pat = pat_map[&var.id].clone();
            substitute_pattern_variables(pat, pat_map);
        },
        Pattern::Product(prod) => {
            for pat in prod {
                substitute_pattern_variables(pat, pat_map);
            }
        },
        Pattern::As(pat, _) => {
            substitute_pattern_variables(pat, pat_map);
        },
        Pattern::Variable(_) | Pattern::Constant(_) => {},
    }
}

/* Substitute variables into the expression according to the map. */
fn substitute_expr_variables(
    expr: &mut Expression,
    pat_map: &HashMap<VariableId, Pattern>,
    expr_map: &HashMap<VariableId, Expression>,
) {
    match expr {
        Expression::Variable(var) if expr_map.contains_key(&var.id) => {
            *expr = expr_map[&var.id].clone();
            substitute_expr_variables(expr, pat_map, expr_map);
        },
        Expression::Product(prod) => {
            for expr in prod {
                substitute_expr_variables(expr, pat_map, expr_map);
            }
        },
        Expression::Sequence(seq) => {
            for expr in seq {
                substitute_expr_variables(expr, pat_map, expr_map);
            }
        },
        Expression::Infix(_, expr1, expr2) => {
            substitute_expr_variables(expr1, pat_map, expr_map);
            substitute_expr_variables(expr2, pat_map, expr_map);
        },
        Expression::Application(expr1, expr2) => {
            substitute_expr_variables(expr1, pat_map, expr_map);
            substitute_expr_variables(expr2, pat_map, expr_map);
        },
        Expression::Negate(expr1) => {
            substitute_expr_variables(expr1, pat_map, expr_map);
        },
        Expression::LetBinding(binding, body) => {
            substitute_expr_variables(&mut binding.1, pat_map, expr_map);
            substitute_pattern_variables(&mut binding.0, pat_map);
            substitute_expr_variables(body, pat_map, expr_map);
        },
        Expression::Function(fun) => {
            for pat in &mut fun.0 {
                substitute_pattern_variables(pat, pat_map);
            }
            substitute_expr_variables(&mut fun.1, pat_map, expr_map);
        },
        Expression::Variable(_) | Expression::Constant(_) => {}
    }
}

/* Substitute variables into the definition according to the map. */
fn substitute_def_variables(
    def: &mut Definition,
    pat_map: &HashMap<VariableId, Pattern>,
    expr_map: &HashMap<VariableId, Expression>,
) {
    substitute_expr_variables(&mut *def.0.1, pat_map, expr_map);
    substitute_pattern_variables(&mut def.0.0, pat_map);
}

/* Substitute variables into the module according to the map. */
fn substitute_module_variables(
    module: &mut Module,
    pat_map: &HashMap<VariableId, Pattern>,
    expr_map: &HashMap<VariableId, Expression>,
) {
    for def in &mut module.defs {
        substitute_def_variables(def, pat_map, expr_map);
    }
    for expr in &mut module.exprs {
        substitute_expr_variables(expr, pat_map, expr_map);
    }
}

/* Generate a pattern that will match the given expression modulo the specific
 * constants inside it. */
fn generate_pattern_exprs(
    expr: &Expression,
    map: &HashMap<VariableId, Expression>,
    gen: &mut VarGen,
    name: &Option<String>,
) -> (Pattern, Expression) {
    match expr {
        Expression::Variable(var) if map.contains_key(&var.id) => {
            generate_pattern_exprs(&map[&var.id], map, gen, name)
        },
        Expression::Variable(_) => {
            let mut new_var = Variable::new(gen.generate_id());
            new_var.name = name.clone();
            (Pattern::Variable(new_var.clone()), Expression::Variable(new_var))
        },
        Expression::Function(_) | Expression::Infix(_, _, _) |
        Expression::Constant(_) | Expression::Negate(_) => {
            let mut var = Variable::new(gen.generate_id());
            var.name = name.clone();
            (Pattern::Variable(var.clone()), Expression::Variable(var))
        },
        Expression::Product(prod) => {
            let mut pats = vec![];
            let mut exprs = vec![];
            for (idx, expr) in prod.iter().enumerate() {
                let inner_name = name.clone().map(|x| x + "." + &idx.to_string());
                let (pat, expr) = generate_pattern_exprs(expr, map, gen, &inner_name);
                pats.push(pat);
                exprs.push(expr);
            }
            (Pattern::Product(pats), Expression::Product(exprs))
        },
        _ => unreachable!("unexpected normalized expression"),
    }
}

/* Collect all the variables occuring in the given pattern. */
fn collect_pattern_variables(
    pat: &Pattern,
    map: &mut HashMap<VariableId, Variable>,
) {
    match pat {
        Pattern::Variable(var) => {
            map.insert(var.id, var.clone());
        },
        Pattern::As(pat, var) => {
            map.insert(var.id, var.clone());
            collect_pattern_variables(pat, map);
        },
        Pattern::Product(prod) => {
            for pat in prod {
                collect_pattern_variables(pat, map);
            }
        },
        Pattern::Constant(_) => {}
    }
}

/* Collect all the variables occuring in the given expression. */
fn collect_expr_variables(
    expr: &Expression,
    map: &mut HashMap<VariableId, Variable>,
) {
    match expr {
        Expression::Variable(var) => {
            map.insert(var.id, var.clone());
        },
        Expression::Sequence(seq) => {
            for expr in seq {
                collect_expr_variables(expr, map);
            }
        },
        Expression::Product(prod) => {
            for expr in prod {
                collect_expr_variables(expr, map);
            }
        },
        Expression::Infix(_, expr1, expr2) => {
            collect_expr_variables(expr1, map);
            collect_expr_variables(expr2, map);
        },
        Expression::Negate(expr1) => {
            collect_expr_variables(expr1, map);
        },
        Expression::Application(expr1, expr2) => {
            collect_expr_variables(expr1, map);
            collect_expr_variables(expr2, map);
        },
        Expression::Function(fun) => {
            for param in &fun.0 {
                collect_pattern_variables(param, map);
            }
            collect_expr_variables(&*fun.1, map);
        },
        Expression::LetBinding(binding, body) => {
            collect_expr_variables(&*binding.1, map);
            collect_pattern_variables(&binding.0, map);
            collect_expr_variables(body, map);
        },
        Expression::Constant(_) => {},
    }
}

/* Collect all the variables occuring in the given definition. */
fn collect_def_variables(
    def: &Definition,
    map: &mut HashMap<VariableId, Variable>,
) {
    collect_expr_variables(&*def.0.1, map);
    collect_pattern_variables(&def.0.0, map);
}

/* Collect all the variables occuring in the given module. */
fn collect_module_variables(
    module: &Module,
    map: &mut HashMap<VariableId, Variable>,
) {
    for def in &module.defs {
        collect_def_variables(def, map);
    }
    for expr in &module.exprs {
        collect_expr_variables(expr, map);
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
    let mut map = HashMap::new();
    elaborate_module_variables(&module, &mut map, &mut vg);
    let mut vars = HashMap::new();
    collect_module_variables(&module, &mut vars);
    let mut expr_map = HashMap::new();
    let mut pat_map = HashMap::new();
    for (var, expr) in &map {
        let name = vars.get(var).and_then(|x| x.name.clone());
        let (pat, expr) = generate_pattern_exprs(&expr, &map, &mut vg, &name);
        expr_map.insert(*var, expr);
        pat_map.insert(*var, pat);
    }
    substitute_module_variables(&mut module, &pat_map, &expr_map);
    println!("{}", module);
}
