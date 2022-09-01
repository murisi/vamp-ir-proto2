use pest::iterators::Pair;
use std::fmt;
use std::fmt::Write;
use crate::pest::Parser;
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
pub struct Definition(pub LetBinding);

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
        if let Expression::Function(Function(params, body)) = &*self.0.1 {
            write!(f, "let {}", self.0.0)?;
            for param in params {
                write!(f, " {}", param)?;
            }
            let mut body_str = String::new();
            write!(body_str, "{}", body)?;
            if body_str.contains("\n") {
                body_str = body_str.replace("\n", "\n    ");
                write!(f, " =\n    {}", body_str)?
            } else {
                write!(f, " = {}", body_str)?
            }
        } else {
            let mut val_str = String::new();
            write!(val_str, "{}", self.0.1)?;
            if val_str.contains("\n") {
                val_str = val_str.replace("\n", "\n    ");
                write!(f, "let {} =\n    {}", self.0.0, val_str)?
            } else {
                write!(f, "let {} = {}", self.0.0, val_str)?
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct LetBinding(pub Pattern, pub Box<Expression>);

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
                let expr = Box::new(Expression::Function(Function(pats, Box::new(expr))));
                Some(Self(Pattern::Variable(name), expr))
            },
            Rule::pattern => {
                let pat = Pattern::parse(pair).expect("pattern should start with pattern");
                Some(Self(pat, Box::new(expr)))
            },
            _ => unreachable!("let binding is of unknown form")
        }
    }
}

impl fmt::Display for LetBinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.1 {
            Expression::Function(fun) => {
                write!(f, "{}", self.0)?;
                for pat in &fun.0 {
                    write!(f, " {}", pat)?;
                }
                write!(f, " = {}", fun.1)?;
            },
            _ => write!(f, "{} = {}", self.0, self.1)?,
        };
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
                write!(f, "(")?;
                if let Some(pat) = iter.next() {
                    write!(f, "{}", pat)?;
                    while let Some(pat) = iter.next() {
                        write!(f, ", {}", pat)?;
                    }
                }
                write!(f, ")")?;
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
    LetBinding(LetBinding, Box<Expression>),
}

impl Expression {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr { return None }
        let string = pair.as_str();
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("expression should not be empty");
        if string.starts_with("fun") {
            Function::parse(pair).map(Self::Function)
        } else if string.starts_with("let") {
            let body = Self::parse(pair).expect("expression should end with expression");
            let pair = pairs.next().expect("body expression should be prefixed by binding");
            let binding = LetBinding::parse(pair).expect("expression should start with binding");
            Some(Self::LetBinding(binding, Box::new(body)))
        } else {
            Self::parse_expr1(pair)
        }
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
        Some(if exprs.len() == 1 { exprs[0].clone() } else { Self::Sequence(exprs) })
    }

    pub fn parse_expr2(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr2 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut exprs =
            vec![Self::parse_expr3(pair).expect("expression should start with product")];
        while let Some(pair) = pairs.next() {
            let rhs = Self::parse_expr3(pair)
                .expect("expected RHS to be a product");
            exprs.push(rhs);
        }
        Some(if exprs.len() == 1 { exprs[0].clone() } else { Self::Product(exprs) })
    }

    pub fn parse_expr3(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr3 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr4(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next() {
            let op = InfixOp::parse(pair).expect("expected arithmetic operator");
            let rhs_pair = pairs.next().expect("expected RHS product");
            let rhs = Self::parse_expr4(rhs_pair)
                .expect("expected RHS to be a product");
            expr = Self::Infix(op, Box::new(expr), Box::new(rhs));
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
            let op = InfixOp::parse(pair).expect("expected arithmetic operator");
            let rhs_pair = pairs.next().expect("expected RHS product");
            let rhs = Self::parse_expr5(rhs_pair)
                .expect("expected RHS to be a product");
            expr = Self::Infix(op, Box::new(expr), Box::new(rhs));
        }
        Some(expr)
    }

    pub fn parse_expr5(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr5 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr6(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next() {
            let op = InfixOp::parse(pair).expect("expected arithmetic operator");
            let rhs_pair = pairs.next().expect("expected RHS product");
            let rhs = Self::parse_expr6(rhs_pair)
                .expect("expected RHS to be a product");
            expr = Self::Infix(op, Box::new(expr), Box::new(rhs));
        }
        Some(expr)
    }

    pub fn parse_expr6(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr6 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr7(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next_back() {
            if pair.as_rule() == Rule::negate {
                expr = Expression::Negate(Box::new(expr));
            } else {
                unreachable!("only negative signs should occur here");
            }
        }
        Some(expr)
    }

    pub fn parse_expr7(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr7 { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut expr =
            Self::parse_expr8(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next() {
            let rhs = Self::parse_expr8(pair)
                .expect("expected RHS to be a product");
            expr = Expression::Application(Box::new(expr), Box::new(rhs));
        }
        Some(expr)
    }

    pub fn parse_expr8(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expr8 { return None }
        let string = pair.as_str();
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("expression should not be empty");
        if pair.as_rule() == Rule::constant {
            let value = pair.as_str().parse().ok().expect("constant should be an integer");
            Some(Self::Constant(value))
        } else if pair.as_rule() == Rule::valueName {
            let name = Variable::parse(pair).expect("expression should be value name");
            Some(Self::Variable(name))
        } else if string.starts_with("(") || string.starts_with("fun") |
        string.starts_with("let") {
            Self::parse(pair)
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
                    while let Some(expr) = iter.next() {
                        write!(f, ";\n{}", expr)?;
                    }
                } else {
                    write!(f, "()")?;
                }
            },
            Self::Product(exprs) => {
                let mut iter = exprs.iter();
                write!(f, "(")?;
                if let Some(expr) = iter.next() {
                    write!(f, "{}", expr)?;
                    while let Some(expr) = iter.next() {
                        write!(f, ", {}", expr)?;
                    }
                }
                write!(f, ")")?;
            },
            Self::Infix(op, expr1, expr2) => write!(f, "({}{}{})", expr1, op, expr2)?,
            Self::Negate(expr) => write!(f, "-{}", expr)?,
            Self::Application(expr1, expr2) => write!(f, "{} {}", expr1, expr2)?,
            Self::Constant(val) => write!(f, "{}", val)?,
            Self::Variable(var) => write!(f, "{}", var)?,
            Self::Function(fun) => write!(f, "{}", fun)?,
            Self::LetBinding(binding, expr) => {
                let mut body = String::new();
                write!(body, "{}", expr)?;
                if body.contains("\n") {
                    body = body.replace("\n", "\n    ");
                    write!(f, "let {} in\n    {}", binding, body)?
                } else {
                    write!(f, "let {} in {}", binding, expr)?
                }
            },
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
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

pub type VariableId = u32;

#[derive(Clone, Debug)]
pub struct Variable {
    pub name: Option<String>,
    pub id: VariableId,
}

impl Variable {
    pub fn new(id: VariableId) -> Self {
        Self { id, name: None }
    }
    
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::valueName { return None }
        Some(Self{name: Some(pair.as_str().to_string()), id: 0 })
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{}", name)?;
        }
        write!(f, "[{}]", self.id)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Function(pub Vec<Pattern>, pub Box<Expression>);

impl Function {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::function { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next_back().expect("function should not be empty");
        let body = Expression::parse(pair).expect("function should end with expression");
        let mut params = vec![];
        while let Some(pair) = pairs.next() {
            let param =
                Pattern::parse(pair).expect("all prefixes to function should be patterns");
            params.push(param);
        }
        Some(Self(params, Box::new(body)))
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fun {}", self.0[0])?;
        for pat in &self.0[1..] {
            write!(f, " {}", pat)?;
        }

        let mut body = String::new();
        write!(body, "{}", self.1)?;
        if body.contains("\n") {
            body = body.replace("\n", "\n    ");
            write!(f, " ->\n    {}", body)?
        } else {
            write!(f, " -> {}", body)?
        }
        Ok(())
    }
}
