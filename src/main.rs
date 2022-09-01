mod ast;
mod transform;
extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::collections::HashMap;
use std::fs;
use crate::ast::{Module, Expression, Pattern};
use crate::transform::*;

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
    println!("{}\n", module_3ac);
}
