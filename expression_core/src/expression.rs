use crate::parsing::*;
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum Expression {
    Number(f64),
    Variable(String),
    Add(Box<Expression>, Box<Expression>),
    Subtract(Box<Expression>, Box<Expression>),
    Multiply(Box<Expression>, Box<Expression>),
    Divide(Box<Expression>, Box<Expression>),
    Power(Box<Expression>, Box<Expression>),
    Sin(Box<Expression>),
    Cos(Box<Expression>),
    Tan(Box<Expression>),
    ArcSin(Box<Expression>),
    ArcCos(Box<Expression>),
    ArcTan(Box<Expression>),
}

impl Expression {
    pub fn evaluate(&self, variables: &HashMap<String, f64>) -> Result<f64, String> {
        match self {
            Expression::Number(n) => Ok(*n),
            Expression::Variable(name) => variables
                .get(name)
                .copied()
                .ok_or(format!("Variable '{}' not found", name)),
            Expression::Add(a, b) => Ok(a.evaluate(variables)? + b.evaluate(variables)?),
            Expression::Subtract(a, b) => Ok(a.evaluate(variables)? - b.evaluate(variables)?),
            Expression::Multiply(a, b) => Ok(a.evaluate(variables)? * b.evaluate(variables)?),
            Expression::Divide(a, b) => {
                let denominator = b.evaluate(variables)?;
                if denominator == 0.0 {
                    return Err("Division by 0".to_string());
                }
                Ok(a.evaluate(variables)? / denominator)
            }
            Expression::Power(base, exponent) => Ok(base
                .evaluate(variables)?
                .powf(exponent.evaluate(variables)?)),
            Expression::Sin(expr) => Ok(expr.evaluate(variables)?.sin()),
            Expression::Cos(expr) => Ok(expr.evaluate(variables)?.cos()),
            Expression::Tan(expr) => Ok(expr.evaluate(variables)?.tan()),
            Expression::ArcSin(expr) => {
                let val = expr.evaluate(variables)?;
                if val < -1.0 || val > 1.0 {
                    Err("Domain error: arcsin argument must be between -1 and 1".to_string())
                } else {
                    Ok(val.asin())
                }
            }
            Expression::ArcCos(expr) => {
                let val = expr.evaluate(variables)?;
                if val < -1.0 || val > 1.0 {
                    Err("Domain error: arccos argument must be between -1 and 1".to_string())
                } else {
                    Ok(val.acos())
                }
            }
            Expression::ArcTan(expr) => Ok(expr.evaluate(variables)?.atan()),
        }
    }

    pub fn parse(input: &str) -> Result<Expression, String> {
        Parser::new(tokenize(input)?).parse_expression()
    }
}

pub mod expr {
    use super::Expression;

    pub fn number(n: f64) -> Expression {
        Expression::Number(n)
    }

    pub fn variable(name: &str) -> Expression {
        Expression::Variable(name.to_string())
    }

    pub fn add(a: Expression, b: Expression) -> Expression {
        Expression::Add(Box::new(a), Box::new(b))
    }

    pub fn subtract(a: Expression, b: Expression) -> Expression {
        Expression::Subtract(Box::new(a), Box::new(b))
    }

    pub fn multiply(a: Expression, b: Expression) -> Expression {
        Expression::Multiply(Box::new(a), Box::new(b))
    }

    pub fn divide(a: Expression, b: Expression) -> Expression {
        Expression::Divide(Box::new(a), Box::new(b))
    }

    pub fn power(base: Expression, power: Expression) -> Expression {
        Expression::Power(Box::new(base), Box::new(power))
    }

    pub fn sin(expr: Expression) -> Expression {
        Expression::Sin(Box::new(expr))
    }

    pub fn cos(expr: Expression) -> Expression {
        Expression::Cos(Box::new(expr))
    }

    pub fn tan(expr: Expression) -> Expression {
        Expression::Tan(Box::new(expr))
    }

    pub fn arcsin(expr: Expression) -> Expression {
        Expression::ArcSin(Box::new(expr))
    }

    pub fn arccos(expr: Expression) -> Expression {
        Expression::ArcCos(Box::new(expr))
    }

    pub fn arctan(expr: Expression) -> Expression {
        Expression::ArcTan(Box::new(expr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    // Helper function to parse a string directly into an Expression
    fn parse_str(input: &str) -> Result<Expression, String> {
        let tokens = tokenize(input)?;
        Parser::new(tokens).parse_expression()
    }

    #[test]
    fn test_tokenize() {
        assert_eq!(
            tokenize("1 + 2").unwrap(),
            vec![Token::Number(1.0), Token::Plus, Token::Number(2.0)]
        );

        assert_eq!(
            tokenize("sin(x)").unwrap(),
            vec![
                Token::Function("sin".to_string()),
                Token::LParen,
                Token::Variable("x".to_string()),
                Token::RParen
            ]
        );

        assert_eq!(
            tokenize("x^2 + y^2").unwrap(),
            vec![
                Token::Variable("x".to_string()),
                Token::Caret,
                Token::Number(2.0),
                Token::Plus,
                Token::Variable("y".to_string()),
                Token::Caret,
                Token::Number(2.0)
            ]
        );

        assert_eq!(
            tokenize("  1  +  2  ").unwrap(),
            vec![Token::Number(1.0), Token::Plus, Token::Number(2.0)]
        );
    }

    #[test]
    fn test_parse_numbers_and_variables() {
        assert_eq!(parse_str("42").unwrap(), Expression::Number(42.0));
        assert_eq!(
            parse_str("3.141592653589793").unwrap(),
            Expression::Number(std::f64::consts::PI)
        );
        assert_eq!(
            parse_str("x").unwrap(),
            Expression::Variable("x".to_string())
        );
    }

    #[test]
    fn test_parse_operators() {
        // Addition
        assert_eq!(
            parse_str("1 + 2").unwrap(),
            Expression::Add(
                Box::new(Expression::Number(1.0)),
                Box::new(Expression::Number(2.0))
            )
        );

        // Subtraction
        assert_eq!(
            parse_str("5 - 3").unwrap(),
            Expression::Subtract(
                Box::new(Expression::Number(5.0)),
                Box::new(Expression::Number(3.0))
            )
        );

        // Multiplication
        assert_eq!(
            parse_str("2 * 3").unwrap(),
            Expression::Multiply(
                Box::new(Expression::Number(2.0)),
                Box::new(Expression::Number(3.0))
            )
        );

        // Division
        assert_eq!(
            parse_str("6 / 2").unwrap(),
            Expression::Divide(
                Box::new(Expression::Number(6.0)),
                Box::new(Expression::Number(2.0))
            )
        );

        // Power
        assert_eq!(
            parse_str("2 ^ 3").unwrap(),
            Expression::Power(
                Box::new(Expression::Number(2.0)),
                Box::new(Expression::Number(3.0))
            )
        );
    }

    #[test]
    fn test_parse_precedence() {
        // Test operator precedence: 1 + 2 * 3 = 1 + (2 * 3) = 7
        let expr = parse_str("1 + 2 * 3").unwrap();
        let vars = HashMap::new();
        assert_eq!(expr.evaluate(&vars).unwrap(), 7.0);

        // Test operator precedence with parentheses: (1 + 2) * 3 = 9
        let expr = parse_str("(1 + 2) * 3").unwrap();
        assert_eq!(expr.evaluate(&vars).unwrap(), 9.0);

        // Test complex expression: 2 * 3 + 4 ^ 2 / 2 = 6 + 8 = 14
        let expr = parse_str("2 * 3 + 4 ^ 2 / 2").unwrap();
        assert_eq!(expr.evaluate(&vars).unwrap(), 14.0);
    }

    #[test]
    fn test_parse_functions() {
        // Test trigonometric functions
        assert!(matches!(parse_str("sin(0)").unwrap(), Expression::Sin(_)));
        assert!(matches!(parse_str("cos(0)").unwrap(), Expression::Cos(_)));
        assert!(matches!(parse_str("tan(0)").unwrap(), Expression::Tan(_)));
        assert!(matches!(
            parse_str("arcsin(0)").unwrap(),
            Expression::ArcSin(_)
        ));
        assert!(matches!(
            parse_str("arccos(1)").unwrap(),
            Expression::ArcCos(_)
        ));
        assert!(matches!(
            parse_str("arctan(0)").unwrap(),
            Expression::ArcTan(_)
        ));

        // Test function with expression argument
        assert!(matches!(
            parse_str("sin(x + 1)").unwrap(),
            Expression::Sin(_)
        ));
    }

    #[test]
    fn test_parse_complex_expressions() {
        // Test nested expressions
        let expr = parse_str("(1 + 2) * (3 - 4) ^ 2").unwrap();
        let mut vars = HashMap::new();
        assert_eq!(expr.evaluate(&vars).unwrap(), 3.0);

        // Test with variables
        let expr = parse_str("x^2 + y^2").unwrap();
        vars.insert("x".to_string(), 3.0);
        vars.insert("y".to_string(), 4.0);
        assert_eq!(expr.evaluate(&vars).unwrap(), 25.0);

        // Test complex function usage
        let expr = parse_str("sin(x)^2 + cos(x)^2").unwrap();
        vars.insert("x".to_string(), 0.5);
        assert_eq!(expr.evaluate(&vars).unwrap(), 1.0);
    }

    #[test]
    fn test_parse_errors() {
        // Missing closing parenthesis
        assert!(parse_str("(1 + 2").is_err());

        // Unknown function
        assert!(parse_str("unknown(x)").is_err());

        // Invalid syntax
        assert!(parse_str("1 + + 2").is_err());

        // Empty expression
        assert!(parse_str("").is_err());

        // Expected parenthesis after function
        assert!(parse_str("sin x").is_err());

        // Invalid characters
        assert!(tokenize("1 @ 2").is_err());
    }

    #[test]
    fn test_domain_errors() {
        // Test arcsin domain error
        let expr = parse_str("arcsin(2)").unwrap();
        let vars = HashMap::new();
        assert!(expr.evaluate(&vars).is_err());

        // Test division by zero
        let expr = parse_str("1 / (x - 2)").unwrap();
        let mut vars = HashMap::new();
        vars.insert("x".to_string(), 2.0);
        assert!(expr.evaluate(&vars).is_err());
    }
}
