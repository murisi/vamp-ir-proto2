use std::collections::HashMap;
use crate::ast::{Module, Definition, Expression, Pattern, VariableId, LetBinding, Variable, InfixOp};

/* A structure for generating unique variable IDs. */
pub struct VarGen(VariableId);

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
pub fn number_module_variables(
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
pub fn apply_module_functions(
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
pub fn elaborate_module_variables(
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
pub fn substitute_module_variables(
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
pub fn generate_pattern_exprs(
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
pub fn collect_module_variables(
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

/* Replace all functions occuring in the given expression with 0-tuples. */
fn unitize_expr_functions(expr: &mut Expression) {
    match expr {
        Expression::Function(_) => *expr = Expression::Product(vec![]),
        Expression::Sequence(exprs) | Expression::Product(exprs) => {
            for expr in exprs {
                unitize_expr_functions(expr);
            }
        },
        Expression::Infix(_, expr1, expr2) | Expression::Application(expr1, expr2) => {
            unitize_expr_functions(expr1);
            unitize_expr_functions(expr2);
        },
        Expression::LetBinding(binding, body) => {
            unitize_expr_functions(&mut *binding.1);
            unitize_expr_functions(body);
        },
        Expression::Negate(expr1) => unitize_expr_functions(expr1),
        Expression::Constant(_) | Expression::Variable(_) => {}
    }
}

/* Replace all functions occuring in the given definition with 0-tuples. */
fn unitize_def_functions(def: &mut Definition) {
    unitize_expr_functions(&mut *def.0.1);
}

/* Replace all functions occuring in the given module with 0-tuples. */
pub fn unitize_module_functions(module: &mut Module) {
    for def in &mut module.defs {
        unitize_def_functions(def);
    }
    for expr in &mut module.exprs {
        unitize_expr_functions(expr);
    }
}

/* Produce the given binary operation making sure to do any straightforward
 * simplifications. */
fn infix_op(op: InfixOp, e1: Expression, e2: Expression) -> Expression {
    match (op, e1, e2) {
        (InfixOp::Multiply, Expression::Constant(1), e2) => e2,
        (InfixOp::Multiply, e1, Expression::Constant(1)) => e1,
        (InfixOp::Multiply, e1 @ Expression::Constant(0), _) => e1,
        (InfixOp::Multiply, _, e2 @ Expression::Constant(0)) => e2,
        (InfixOp::Divide, e1, Expression::Constant(1)) => e1,
        (InfixOp::Add, Expression::Constant(0), e2) => e2,
        (InfixOp::Add, e1, Expression::Constant(0)) => e1,
        (InfixOp::Subtract, e1, Expression::Constant(0)) => e1,
        (op, e1, e2) => Expression::Infix(op, Box::new(e1), Box::new(e2))
    }
}

/* Flatten the given binding down into the set of constraints it defines. */
fn flatten_binding(
    pat: &Pattern,
    expr: &Expression,
    flattened: &mut Module,
) {
    match (pat, expr) {
        (pat @ Pattern::Variable(_),
         expr @ (Expression::Variable(_) | Expression::Constant(_) |
         Expression::Infix(_, _, _) | Expression::Negate(_))) => {
            flattened.defs.push(Definition(LetBinding(
                pat.clone(),
                Box::new(expr.clone()),
            )));
        },
        (Pattern::Constant(pat),
         expr @ (Expression::Variable(_) | Expression::Constant(_) |
                 Expression::Infix(_, _, _) | Expression::Negate(_))) => {
            flattened.exprs.push(Expression::Infix(
                InfixOp::Equal,
                Box::new(Expression::Constant(*pat)),
                Box::new(expr.clone()),
            ));
        },
        (Pattern::As(pat, _name), expr) => {
            flatten_binding(pat, expr, flattened);
        },
        (Pattern::Product(pats), Expression::Product(exprs)) => {
            for (pat, expr) in pats.iter().zip(exprs.iter()) {
                flatten_binding(pat, expr, flattened);
            }
        }
        _ => unreachable!("encountered unexpected binding: {} = {}", pat, expr),
    }
}

/* Flatten the given equality down into the set of constraints it defines. */
fn flatten_equals(
    expr1: &Expression,
    expr2: &Expression,
    flattened: &mut Module,
) {
    match (expr1, expr2) {
        (Expression::Product(prod1), Expression::Product(prod2)) => {
            for (expr1, expr2) in prod1.iter().zip(prod2.iter()) {
                flatten_equals(expr1, expr2, flattened);
            }
        },
        (expr1 @ (Expression::Variable(_) | Expression::Negate(_) |
                  Expression::Infix(_, _, _) | Expression::Constant(_)),
         expr2 @ (Expression::Variable(_) | Expression::Negate(_) |
                  Expression::Infix(_, _, _) | Expression::Constant(_))) => {
            flattened.exprs.push(Expression::Infix(
                InfixOp::Equal,
                Box::new(expr1.clone()),
                Box::new(expr2.clone())
            ));
        },
        _ => unreachable!("encountered unexpected equality: {} = {}", expr1, expr2),
    }
}

/* Generate a constraint requiring that there be one position in the given
 * structures where the corresponding variables do not match. */
fn flatten_not_equals(
    expr1: &Expression,
    expr2: &Expression,
    witness: &Variable,
    def: &mut Expression,
    constraint: &mut Expression,
) {
    match (expr1, expr2) {
        (Expression::Product(prod1), Expression::Product(prod2)) => {
            for (expr1, expr2) in prod1.iter().zip(prod2.iter()) {
                flatten_not_equals(expr1, expr2, witness, def, constraint);
            }
        },
        (expr1 @ (Expression::Variable(_) | Expression::Negate(_) |
                  Expression::Infix(_, _, _) | Expression::Constant(_)),
         expr2 @ (Expression::Variable(_) | Expression::Negate(_) |
                  Expression::Infix(_, _, _) | Expression::Constant(_))) => {
            *constraint = infix_op(
                InfixOp::Multiply,
                constraint.clone(),
                infix_op(
                    InfixOp::Subtract,
                    Expression::Variable(witness.clone()),
                    infix_op(
                        InfixOp::Subtract,
                        expr1.clone(),
                        expr2.clone(),
                    ),
                )
            );
        },
        _ => unreachable!("encountered unexpected equality: {} = {}", expr1, expr2),
    }
}

/* Flatten the given expression down into the set of constraints it defines. */
fn flatten_expression(
    expr: &Expression,
    flattened: &mut Module,
) -> Expression {
    match expr {
        Expression::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(flatten_expression(expr, flattened));
            }
            val.expect("encountered empty sequence").clone()
        },
        Expression::Infix(InfixOp::Equal, expr1, expr2) => {
            let expr1 = flatten_expression(expr1, flattened);
            let expr2 = flatten_expression(expr2, flattened);
            flatten_equals(&expr1, &expr2, flattened);
            Expression::Product(vec![])
        },
        Expression::Infix(InfixOp::NotEqual, _expr1, _expr2) =>
            todo!("not equal expressions not supported yet"),
        Expression::Infix(op, expr1, expr2) => {
            let expr1 = flatten_expression(expr1, flattened);
            let expr2 = flatten_expression(expr2, flattened);
            Expression::Infix(*op, Box::new(expr1), Box::new(expr2))
        },
        Expression::Product(prod) => {
            let mut exprs = vec![];
            for expr in prod {
                exprs.push(flatten_expression(expr, flattened));
            }
            Expression::Product(exprs)
        },
        Expression::Negate(expr1) =>
            Expression::Negate(Box::new(flatten_expression(expr1, flattened))),
        Expression::Constant(_) | Expression::Variable(_) => expr.clone(),
        Expression::LetBinding(binding, body) => {
            let val = flatten_expression(&*binding.1, flattened);
            flatten_binding(&binding.0, &val, flattened);
            flatten_expression(body, flattened)
        }
        Expression::Function(_) | Expression::Application(_, _) =>
            unreachable!("functions must already by inlined and eliminated"),
    }
}

/* Flatten the given definition down into the set of constraints it defines. */
fn flatten_definition(
    def: &Definition,
    flattened: &mut Module,
) {
    let val = flatten_expression(&*def.0.1, flattened);
    flatten_binding(&def.0.0, &val, flattened);
}

/* Flatten the given module down into the set of constraints it defines. */
pub fn flatten_module(
    module: &Module,
    flattened: &mut Module,
) {
    for def in &module.defs {
        flatten_definition(def, flattened);
    }
    for expr in &module.exprs {
        flatten_expression(expr, flattened);
    }
}

/* Make an equality expression to constrain the values that satify the circuit.
 * Simultaneously also make a variable definition to enable provers to generate
 * the necessary auxiliary variables. */
fn push_constraint_def(module: &mut Module, out: Pattern, expr: Expression) {
    module.exprs.push(Expression::Infix(
        InfixOp::Equal,
        Box::new(out.to_expr()),
        Box::new(expr.clone())
    ));
    module.defs.push(Definition(LetBinding(out, Box::new(expr))));
}

/* Flatten the given expression down to a single term and place the definitions
 * of its parts into the given module. The parts always take the following form:
 * term1 = -term2 or term1 = term2 OP term3 */
fn flatten_expr_to_3ac(
    out: Option<Pattern>,
    expr: &Expression,
    flattened: &mut Module,
    gen: &mut VarGen,
) -> Pattern {
    match (out, expr) {
        (None, Expression::Constant(val)) => Pattern::Constant(*val),
        (None, Expression::Variable(var)) => Pattern::Variable(var.clone()),
        (Some(pat),
         Expression::Constant(_) | Expression::Variable(_)) => {
            push_constraint_def(flattened, pat.clone(), expr.clone());
            pat
        },
        (out, Expression::Negate(n)) => {
            let out1_term = flatten_expr_to_3ac(None, n, flattened, gen);
            let rhs = Expression::Negate(Box::new(out1_term.to_expr()));
            let out_var = Variable::new(gen.generate_id());
            let out = out.unwrap_or(Pattern::Variable(out_var.clone()));
            push_constraint_def(flattened, out.clone(), rhs);
            out
        },
        (out, Expression::Infix(op, e1, e2)) => {
            let out1_term = flatten_expr_to_3ac(None, e1, flattened, gen);
            let out2_term = flatten_expr_to_3ac(None, e2, flattened, gen);
            let rhs = infix_op(
                *op,
                out1_term.to_expr(),
                out2_term.to_expr(),
            );
            let out_var = Variable::new(gen.generate_id());
            let out = out.unwrap_or(Pattern::Variable(out_var.clone()));
            push_constraint_def(flattened, out.clone(), rhs);
            out
        },
        _ => panic!("encountered unexpected expression: {}", expr),
    }
}

/* Flatten the given definition into three-address form. */
fn flatten_def_to_3ac(
    def: &Definition,
    flattened: &mut Module,
    gen: &mut VarGen,
) {
    flatten_expr_to_3ac(Some(def.0.0.clone()), &*def.0.1, flattened, gen);
}

/* Flatten all definitions and expressions in this module into three-address
 * form. */
pub fn flatten_module_to_3ac(
    module: &Module,
    flattened: &mut Module,
    gen: &mut VarGen,
) {
    for def in &module.defs {
        flatten_def_to_3ac(def, flattened, gen);
    }
    for expr in &module.exprs {
        if let Expression::Infix(InfixOp::Equal, lhs, rhs) = expr {
            // Flatten this equality constraint into a series of definitions.
            // The last inserted definition is always an encoding of an equality
            // constraint.
            match (&**lhs, &**rhs) {
                (Expression::Variable(var), ohs) |
                (ohs, Expression::Variable(var)) => {
                    flatten_expr_to_3ac(
                        Some(Pattern::Variable(var.clone())),
                        ohs,
                        flattened,
                        gen
                    );
                },
                (Expression::Constant(val), ohs) |
                (ohs, Expression::Constant(val)) => {
                    flatten_expr_to_3ac(
                        Some(Pattern::Constant(*val)),
                        ohs,
                        flattened,
                        gen
                    );
                },
                (lhs, rhs) => {
                    let lhs = flatten_expr_to_3ac(None, lhs, flattened, gen);
                    let rhs = flatten_expr_to_3ac(None, rhs, flattened, gen);
                    flatten_expr_to_3ac(
                        Some(lhs),
                        &rhs.to_expr(),
                        flattened,
                        gen
                    );
                }
            }
            // Remove the last definition because it is solely an equality
            // constraint.
            flattened
                .defs
                .pop()
                .expect("a definition should have been made for the current expression");
        }
    }
}

/* Compile the given module down into three-address codes. */
pub fn compile(mut module: Module) -> Module {
    let mut vg = VarGen::new();
    number_module_variables(&mut module, &mut vg);
    apply_module_functions(&mut module, &mut vg);
    // Collect variable names for the variable we will create
    let mut vars = HashMap::new();
    collect_module_variables(&module, &mut vars);
    // Expand all variables into their constituents
    let mut map = HashMap::new();
    elaborate_module_variables(&module, &mut map, &mut vg);
    let mut expr_map = HashMap::new();
    let mut pat_map = HashMap::new();
    for (var, expr) in &map {
        let name = vars.get(var).and_then(|x| x.name.clone());
        let (pat, expr) = generate_pattern_exprs(&expr, &map, &mut vg, &name);
        expr_map.insert(*var, expr);
        pat_map.insert(*var, pat);
    }
    substitute_module_variables(&mut module, &pat_map, &expr_map);
    // Unitize all function variable expressions and patterns
    let mut map = HashMap::new();
    elaborate_module_variables(&module, &mut map, &mut vg);
    let mut expr_map = HashMap::new();
    let mut pat_map = HashMap::new();
    for (var, expr) in &map {
        if let Expression::Function(_) = expr {
            expr_map.insert(*var, Expression::Product(vec![]));
            pat_map.insert(*var, Pattern::Product(vec![]));
        }
    }
    substitute_module_variables(&mut module, &pat_map, &expr_map);
    // Unitize all function expressions
    unitize_module_functions(&mut module);
    println!("{}\n", module);
    // Start generating arithmetic constraints
    let mut constraints = Module::default();
    flatten_module(&module, &mut constraints);
    println!("{}\n", constraints);
    let mut module_3ac = Module::default();
    flatten_module_to_3ac(&constraints, &mut module_3ac, &mut vg);
    module_3ac
}
