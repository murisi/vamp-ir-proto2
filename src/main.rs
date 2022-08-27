extern crate pest;
#[macro_use]
extern crate pest_derive;
use pest::Parser;
use pest::iterators::Pair;
use std::fmt;

#[derive(Parser)]
#[grammar = "vamp_ir.pest"]
pub struct VampirParser;

#[derive(Debug, Clone)]
pub struct Module {
    pub defs: Vec<Definition>,
    pub exprs: Vec<Expression>,
}

impl Module {
    pub fn parse(unparsed_file: &str) -> Result<Self, pest::error::Error<Rule>> {
        let mut pairs = VampirParser::parse(Rule::moduleItems, &unparsed_file)?;
        let mut defs = vec![];
        let mut exprs = vec![];
        while let Some(pair) = pairs.next() {
            match pair.as_rule() {
                Rule::expr => {
                    let expr = Expression::parse(pair).expect("expected expression");
                    exprs.push(expr);
                },
                Rule::definition => {
                    let definition = Definition::parse(pair).expect("expected definition");
                    defs.push(definition);
                },
                Rule::EOI => return Ok(Self {
                    defs,
                    exprs,
                }),
                _ => unreachable!("module item should either be expression, definition, or EOI")
            }
        }
        unreachable!("EOI should have been encountered")
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for def in &self.defs {
            writeln!(f, "{};;", def)?;
        }
        for expr in &self.exprs {
            writeln!(f, "{};;", expr)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Definition(LetBinding);

impl Definition {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::definition { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("definition should have a single let binding");
        let binding = LetBinding::parse(pair).expect("definition should contain single binding");
        Some(Self(binding))
    }
}

impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {}", self.0)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum LetBinding {
    Value(Pattern, Box<Expression>),
    Function(Variable, Function),
}

impl LetBinding {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::letBinding { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("let binding should not be empty");
        let expr = Expression::parse(pair).expect("expression should end with expression");
        let pair = pairs.next().expect("let binding should have at least two parts");
        match pair.as_rule() {
            Rule::valueName => {
                let name = Variable::parse(pair).expect("expression should be value name");
                let mut pats = vec![];
                while let Some(pair) = pairs.next() {
                    let rhs = Pattern::parse(pair)
                        .expect("expected RHS to be a product");
                    pats.push(rhs);
                }
                Some(Self::Function(name, Function(pats, Box::new(expr))))
            },
            Rule::pattern => {
                let pat = Pattern::parse(pair).expect("pattern should start with pattern");
                Some(Self::Value(pat, Box::new(expr)))
            },
            _ => unreachable!("let binding is of unknown form")
        }
    }
}

impl fmt::Display for LetBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(pat, expr) => write!(f, "{} = {}", pat, expr)?,
            Self::Function(var, fun) => {
                write!(f, "{}", var)?;
                for pat in &fun.0 {
                    write!(f, " {}", pat)?;
                }
                write!(f, " = {}", fun.1)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Pattern {
    As(Box<Pattern>, Variable),
    Product(Vec<Pattern>),
    Variable(Variable),
    Constant(i32),
}

impl Pattern {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::pattern { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("pattern should not be empty");
        let mut pat =
            Self::parse_pat1(pair).expect("pattern should start with pattern");
        while let Some(pair) = pairs.next() {
            let name = Variable::parse(pair).expect("expected pattern name");
            pat = Self::As(Box::new(pat), name);
        }
        Some(pat)
    }

    pub fn parse_pat1(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::pattern1 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("pattern should not be empty");
        let mut pats =
            vec![Self::parse_pat2(pair).expect("expression should start with product")];
        while let Some(pair) = pairs.next() {
            let rhs = Self::parse_pat2(pair)
                .expect("expected RHS to be a product");
            pats.push(rhs);
        }
        Some(if pats.len() == 1 { pats[0].clone() } else { Self::Product(pats) })
    }

    pub fn parse_pat2(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::pattern2 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("expression should not be empty");
        match pair.as_rule() {
            Rule::constant => {
                let value = pair.as_str().parse().ok().expect("constant should be an integer");
                Some(Self::Constant(value))
            },
            Rule::valueName => {
                let name = Variable::parse(pair).expect("pattern should be value name");
                Some(Self::Variable(name))
            },
            Rule::pattern => Self::parse(pair),
            _ => unreachable!("pattern is of unknown form")
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::As(pat, name) => write!(f, "{} as {}", pat, name)?,
            Self::Product(pats) => {
                let mut iter = pats.iter();
                if let Some(pat) = iter.next() {
                    write!(f, "{}", pat)?;
                    while let Some(pat) = iter.next() {
                        write!(f, ", {}", pat)?;
                    }
                } else {
                    write!(f, "()")?;
                }
            },
            Self::Variable(var) => write!(f, "{}", var)?,
            Self::Constant(val) => write!(f, "{}", val)?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Expression {
    Sequence(Vec<Expression>),
    Product(Vec<Expression>),
    Infix(InfixOp, Box<Expression>, Box<Expression>),
    Negate(Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
    Constant(i32),
    Variable(Variable),
    Function(Function),
    Try(Box<Expression>),
    LetBinding(LetBinding, Box<Expression>),
}

impl Expression {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut exprs =
            vec![Self::parse_expr1(pair).expect("expression should start with product")];
        while let Some(pair) = pairs.next() {
            let rhs = Self::parse_expr1(pair)
                .expect("expected RHS to be a product");
            exprs.push(rhs);
        }
        Some(if exprs.len() == 1 { exprs[0].clone() } else { Self::Sequence(exprs) })
    }

    pub fn parse_expr1(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr1 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut exprs =
            vec![Self::parse_expr2(pair).expect("expression should start with product")];
        while let Some(pair) = pairs.next() {
            let rhs = Self::parse_expr2(pair)
                .expect("expected RHS to be a product");
            exprs.push(rhs);
        }
        Some(if exprs.len() == 1 { exprs[0].clone() } else { Self::Product(exprs) })
    }

    pub fn parse_expr2(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr2 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr3(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next() {
            let op = InfixOp::parse(pair).expect("expected arithmetic operator");
            let rhs_pair = pairs.next().expect("expected RHS product");
            let rhs = Self::parse_expr3(rhs_pair)
                .expect("expected RHS to be a product");
            expr = Self::Infix(op, Box::new(expr), Box::new(rhs));
        }
        Some(expr)
    }

    pub fn parse_expr3(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr3 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr4(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next_back() {
            if pair.as_rule() == Rule::negate {
                expr = Expression::Negate(Box::new(expr));
            } else {
                unreachable!("only negative signs should occur here");
            }
        }
        Some(expr)
    }

    pub fn parse_expr4(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr4 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr5(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next() {
            let rhs = Self::parse_expr5(pair)
                .expect("expected RHS to be a product");
            expr = Expression::Application(Box::new(expr), Box::new(rhs));
        }
        Some(expr)
    }

    pub fn parse_expr5(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr5 { return None }
        let string = pair.as_str();
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("expression should not be empty");
        if pair.as_rule() == Rule::constant {
            let value = pair.as_str().parse().ok().expect("constant should be an integer");
            Some(Self::Constant(value))
        } else if pair.as_rule() == Rule::valueName {
            let name = Variable::parse(pair).expect("expression should be value name");
            Some(Self::Variable(name))
        } else if string.starts_with("(") {
            Self::parse(pair)
        } else if string.starts_with("fun") {
            let body = Self::parse(pair).expect("expression should end with expression");
            let mut params = vec![];
            while let Some(pair) = pairs.next() {
                let param =
                    Pattern::parse(pair).expect("all prefixes to expression should be patterns");
                params.push(param);
            }
            Some(Self::Function(Function(params, Box::new(body))))
        } else if string.starts_with("try") {
            let body = Self::parse(pair).expect("expression should contain expression");
            Some(Self::Try(Box::new(body)))
        } else if string.starts_with("let") {
            let body = Self::parse(pair).expect("expression should end with expression");
            let pair = pairs.next().expect("body expression should be prefixed by binding");
            let binding = LetBinding::parse(pair).expect("expression should start with binding");
            Some(Self::LetBinding(binding, Box::new(body)))
        } else {
            unreachable!("expression is of unknown form")
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sequence(exprs) => {
                let mut iter = exprs.iter();
                if let Some(expr) = iter.next() {
                    write!(f, "{}", expr)?;
                    if let Some(expr) = iter.next() {
                        write!(f, "; {}", expr)?;
                    }
                } else {
                    write!(f, "()")?;
                }
            },
            Self::Product(exprs) => {
                let mut iter = exprs.iter();
                if let Some(expr) = iter.next() {
                    write!(f, "{}", expr)?;
                    if let Some(expr) = iter.next() {
                        write!(f, ", {}", expr)?;
                    }
                } else {
                    write!(f, "()")?;
                }
            },
            Self::Infix(op, expr1, expr2) => write!(f, "({}{}{})", expr1, op, expr2)?,
            Self::Negate(expr) => write!(f, "-{}", expr)?,
            Self::Application(expr1, expr2) => write!(f, "{} {}", expr1, expr2)?,
            Self::Constant(val) => write!(f, "{}", val)?,
            Self::Variable(var) => write!(f, "{}", var)?,
            Self::Function(fun) => {
                write!(f, "fun {}", fun.0[0])?;
                for pat in &fun.0[1..] {
                    write!(f, " {}", pat)?;
                }
                write!(f, " -> {}", fun.1)?;
            },
            Self::Try(expr) => write!(f, "try {}", expr)?,
            Self::LetBinding(binding, expr) => write!(f, "let {} in {}", binding, expr)?,
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum InfixOp {
    Divide,
    Multiply,
    Add,
    Subtract,
    Equal,
    NotEqual,
}

impl InfixOp {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::infixOp { return None }
        match pair.as_span().as_str() {
            "=" => Some(Self::Equal),
            "!=" => Some(Self::NotEqual),
            "/" => Some(Self::Divide),
            "*" => Some(Self::Multiply),
            "+" => Some(Self::Add),
            "-" => Some(Self::Subtract),
            _ => unreachable!("Encountered unknown infix operator")
        }
    }
}

impl fmt::Display for InfixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Divide => write!(f, "/"),
            Self::Multiply => write!(f, "*"),
            Self::Add => write!(f, "+"),
            Self::Subtract => write!(f, "-"),
            Self::Equal => write!(f, "="),
            Self::NotEqual => write!(f, "!="),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Variable(String);

impl Variable {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::valueName { return None }
        Some(Self(pair.as_str().to_string()))
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Function(Vec<Pattern>, Box<Expression>);

fn main() {
    println!("Hello, world!");
    let unsuccessful_parse = Module::parse(";; let aa = fun x y -> x + y;;");
    println!("{}", unsuccessful_parse.unwrap());
}
