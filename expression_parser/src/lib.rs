//! A high-level library for parsing and evaluating mathematical expressions.

use std::collections::HashMap;
use expression_core::expression::Expression;

/// Parses a string into an expression.
///
/// # Examples
///
/// ```
/// use expression_parser::parse;
///
/// let expr = parse("x^2 + 2*x + 1").unwrap();
/// ```
pub fn parse(input: &str) -> Result<Expression, String> {
    Expression::parse(input)
}

/// Evaluates a string expression with the given variables.
///
/// # Examples
///
/// ```
/// use expression_parser::evaluate;
/// use std::collections::HashMap;
///
/// let mut vars = HashMap::new();
/// vars.insert("x".to_string(), 2.0);
///
/// let result = evaluate("x^2 + 2*x + 1", &vars).unwrap();
/// assert_eq!(result, 9.0);
/// ```
pub fn evaluate(input: &str, variables: &HashMap<String, f64>) -> Result<f64, String> {
    parse(input)?.evaluate(variables)
}

/// Creates a function from a string expression.
///
/// # Examples
///
/// ```
/// use expression_parser::create_function;
///
/// let f = create_function("x^2 + y").unwrap();
///
/// let result = f(&[("x", 3.0), ("y", 1.0)]).unwrap();
/// assert_eq!(result, 10.0);
/// ```
pub fn create_function(
    input: &str,
) -> Result<impl Fn(&[(&str, f64)]) -> Result<f64, String>, String> {
    let expr = parse(input)?;

    Ok(move |args: &[(&str, f64)]| {
        let mut variables = HashMap::new();
        for (name, value) in args {
            variables.insert(name.to_string(), *value);
        }
        expr.evaluate(&variables)
    })
}

#[doc(inline)]
pub use expression_macro::expr;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_and_evaluate() {
        let mut vars = HashMap::new();
        vars.insert("x".to_string(), 2.0);

        let result = evaluate("x^2 + 3*x + 1", &vars).unwrap();
        assert_eq!(result, 11.0);
    }

    #[test]
    fn test_create_function() {
        let f = create_function("sin(x) + cos(y)").unwrap();

        let result = f(&[("x", 0.0), ("y", 0.0)]).unwrap();
        assert_eq!(result, 1.0);
    }

    #[test]
    fn test_expr_macro() {
        let expr = expr!("2*x + y");

        let mut vars = HashMap::new();
        vars.insert("x".to_string(), 3.0);
        vars.insert("y".to_string(), 1.0);

        let result = expr.evaluate(&vars).unwrap();
        assert_eq!(result, 7.0);
    }
}