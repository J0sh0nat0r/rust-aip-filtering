use std::fmt::{self, Display, Formatter};
use std::time::Duration;

use chrono::{DateTime, FixedOffset};
use itertools::Itertools;
use pest::error::Error;
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
pub struct FilterParser;

impl FilterParser {
    pub fn parse_str(input: &str) -> Result<Filter, Error<Rule>> {
        let mut pairs: Pairs<Rule> = Self::parse(Rule::filter, input)?;

        match pairs.next() {
            None => Ok(Filter::None),

            Some(pair) => Ok(Filter::Some(Expression::parse(pair).unwrap())),
        }
    }
}

pub type Filter<'a> = Option<Expression<'a>>;

#[derive(Debug)]
pub enum Value<'a> {
    Bool(bool),
    Duration(Duration),
    Float(f64),
    Int(i64),
    String(&'a str),
    Text(&'a str),
    Timestamp(DateTime<FixedOffset>),
}

impl<'a> Value<'a> {
    pub fn parse(pair: Pair<'a, Rule>) -> Result<Self, ()> {
        debug_assert_eq!(pair.as_rule(), Rule::value);

        let inner_pair = pair.into_inner().next().unwrap();

        match inner_pair.as_rule() {
            Rule::string => {
                let str = inner_pair.into_inner().as_str();

                if let Ok(value) = DateTime::parse_from_rfc3339(str) {
                    return Ok(Value::Timestamp(value));
                }

                return Ok(Value::String(str))
            }

            Rule::text => {
                let str = inner_pair.as_str();

                if let Ok(value) = str.parse() {
                    return Ok(Value::Bool(value));
                }

                if str.ends_with("s") {
                    if let Ok(secs) = str[..str.len() - 1].parse() {
                        return Ok(Value::Duration(Duration::from_secs_f64(secs)))
                    }
                }

                if let Ok(value) = str.parse() {
                    return Ok(Value::Int(value));
                }

                if let Ok(value) = str.parse() {
                    return Ok(Value::Float(value));
                }

                if let Ok(value) = DateTime::parse_from_rfc3339(str) {
                    return Ok(Value::Timestamp(value));
                }

                Ok(Value::Text(str))
            }

            _ => unreachable!()
        }
    }

    pub fn string_repr(&self) -> String {
        match self {
            Self::Bool(value) => value.to_string(),
            Self::Duration(value) => format!("{}s", value.as_secs_f64()),
            Self::Float(value) => value.to_string(),
            Self::Int(value) => value.to_string(),
            Self::String(value) => value.to_string(),
            Self::Text(value) => value.to_string(),
            Self::Timestamp(value) => value.to_rfc3339(),
        }
    }
}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Bool(value) => write!(f, "{}", value),
            Self::Duration(value) => write!(f, "{}s", value.as_secs_f64()),
            Self::Float(value) => write!(f, "{}", value),
            Self::Int(value) => write!(f, "{}", value),
            Self::String(value) => write!(f, "\"{}\"", value),
            Self::Text(value) => write!(f, "{}", value),
            Self::Timestamp(value) => write!(f, "\"{}\"", value.to_rfc3339()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Comparator {
    Eq,
    Gt,
    GtEq,
    Has,
    Lt,
    LtEq,
    Ne,
}

impl Comparator {
    pub fn parse(pair: Pair<Rule>) -> Result<Self, ()> {
        debug_assert_eq!(pair.as_rule(), Rule::comparator);

        let inner_pair = pair.into_inner().next().unwrap();

        Ok(match inner_pair.as_rule() {
            Rule::eq => Self::Eq,
            Rule::gt => Self::Gt,
            Rule::gt_eq => Self::GtEq,
            Rule::has => Self::Has,
            Rule::lt => Self::Lt,
            Rule::lt_eq => Self::LtEq,
            Rule::ne => Self::Ne,
            _ => return Err(()),
        })
    }
}

impl Display for Comparator {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Eq => " = ",
                Self::Gt => " > ",
                Self::GtEq => " >= ",
                Self::Has => ":",
                Self::Lt => " < ",
                Self::LtEq => " <= ",
                Self::Ne => " != ",
            }
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinOp {
    And,
    Or,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::And => " AND ",
                Self::Or => " OR ",
            }
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnOp {
    Neg,
    Not,
}

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Neg => "-",
                Self::Not => "NOT ",
            }
        )
    }
}

#[derive(Debug)]
pub enum Expression<'a> {
    Binary {
        lhs: Box<Expression<'a>>,
        op: BinOp,
        rhs: Box<Expression<'a>>,
    },

    FCall {
        name: &'a str,
        args: Vec<Expression<'a>>,
    },

    Member {
        value: Value<'a>,
        path: Vec<Value<'a>>,
    },

    Restriction {
        lhs: Box<Expression<'a>>,
        op: Comparator,
        rhs: Box<Expression<'a>>,
    },

    Sequence(Vec<Expression<'a>>),

    Unary {
        op: UnOp,
        rhs: Box<Expression<'a>>,
    },

    Value(Value<'a>),
}

impl<'a> Expression<'a> {
    pub fn parse(pair: Pair<'a, Rule>) -> Result<Self, ()> {
        debug_assert_eq!(pair.as_rule(), Rule::expression);

        let mut inner = pair.into_inner();

        let mut expr = Expression::parse_impl(inner.next().unwrap())?;

        while let Some(rhs_pair) = inner.next() {
            let rhs = Expression::parse_impl(rhs_pair)?;

            expr = Expression::Binary {
                lhs: Box::new(expr),
                op: BinOp::And,
                rhs: Box::new(rhs),
            }
        }

        Ok(expr)
    }

    fn parse_impl(pair: Pair<'a, Rule>) -> Result<Self, ()> {
        match pair.as_rule() {
            Rule::expression => Self::parse(pair),

            Rule::factor => {
                let mut inner = pair.into_inner();

                let mut expr = Expression::parse_impl(inner.next().unwrap())?;

                while let Some(rhs_pair) = inner.next() {
                    let rhs = Expression::parse_impl(rhs_pair)?;

                    expr = Expression::Binary {
                        lhs: Box::new(expr),
                        op: BinOp::Or,
                        rhs: Box::new(rhs),
                    };
                }

                Ok(expr)
            }

            Rule::sequence => {
                let mut inner = pair.into_inner();

                match inner.clone().count() {
                    0 => Err(()),

                    1 => Expression::parse_impl(inner.next().unwrap()),

                    _ => {
                        let exprs = inner
                            .map(|pair| Expression::parse_impl(pair))
                            .try_collect()?;

                        Ok(Expression::Sequence(exprs))
                    }
                }
            }

            Rule::term => {
                let mut inner = pair.into_inner();

                match inner.next().unwrap() {
                    inner_pair if inner_pair.as_rule() == Rule::negation => {
                        let op = match inner_pair.as_str() {
                            "-" => UnOp::Neg,
                            "NOT" => UnOp::Not,
                            _ => unreachable!(),
                        };

                        let term_pair = inner.next().unwrap();

                        let rhs = Expression::parse_impl(term_pair)?;

                        Ok(Expression::Unary {
                            op,
                            rhs: Box::new(rhs),
                        })
                    }

                    term_pair => Ok(Expression::parse_impl(term_pair)?),
                }
            }

            Rule::restriction => {
                let mut inner = pair.into_inner();

                let lhs = Expression::parse_impl(inner.next().unwrap())?;

                match inner.next() {
                    None => Ok(lhs),

                    Some(comparator_pair) => {
                        let op = Comparator::parse(comparator_pair)?;

                        let rhs = Expression::parse_impl(inner.next().unwrap())?;

                        Ok(Expression::Restriction {
                            lhs: Box::new(lhs),
                            op,
                            rhs: Box::new(rhs),
                        })
                    }
                }
            }

            Rule::member => {
                let mut inner = pair.into_inner();

                let value = Value::parse(inner.next().unwrap())?;

                match inner.peek() {
                    None => Ok(Expression::Value(value)),

                    Some(_) => {
                        let mut path = Vec::new();

                        for field_pair in inner {
                            // Should always be equal when coming from Pest
                            debug_assert_eq!(field_pair.as_rule(), Rule::field);

                            let inner_pair = field_pair.into_inner().next().unwrap();

                            path.push(parse_field(inner_pair)?);
                        }

                        Ok(Expression::Member { value, path })
                    }
                }
            }

            Rule::function => {
                let mut inner = pair.into_inner();

                let name = {
                    let name_pair = inner.next().unwrap();

                    debug_assert_eq!(name_pair.as_rule(), Rule::function_name);

                    name_pair.as_str()
                };

                let args = inner
                    .next()
                    .map(|arg_list_pair| {
                        debug_assert_eq!(arg_list_pair.as_rule(), Rule::arg_list);

                        arg_list_pair
                            .into_inner()
                            .map(|pair| Expression::parse_impl(pair))
                            .try_collect()
                    })
                    .unwrap_or_else(|| Ok(Vec::new()))?;

                Ok(Expression::FCall { name, args })
            }

            Rule::value => {
                let inner_pair = pair.into_inner().next().unwrap();

                Ok(Expression::Value(Value::parse(inner_pair)?))
            }

            _ => unimplemented!("{:?}", pair),
        }
    }
}

impl Display for Expression<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Binary { lhs, op, rhs } => write!(f, "({}{}{})", lhs, op, rhs),

            Self::FCall { name, args } => {
                let args_str = args
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<String>>()
                    .join(", ");

                write!(f, "({}({}))", name, args_str)
            }

            Self::Member { value, path } => {
                let path_str = path
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<String>>()
                    .join(".");

                write!(f, "({}.{})", value, path_str)
            }

            Self::Restriction { lhs, op, rhs } => write!(f, "({}{}{})", lhs, op, rhs),

            Self::Sequence(expressions) => {
                let joined_str = expressions
                    .iter()
                    .map(|expr| format!("{}", expr))
                    .collect::<Vec<String>>()
                    .join(" ");

                write!(f, "({})", joined_str)
            }

            Self::Unary { op, rhs } => write!(f, "({}{})", op, rhs),

            Self::Value(value) => value.fmt(f),
        }
    }
}

fn parse_field(pair: Pair<Rule>) -> Result<Value, ()> {
    match pair.as_rule() {
        Rule::value => Value::parse(pair),
        Rule::keyword => Ok(Value::Text(pair.as_str())),
        _ => Err(()),
    }
}
