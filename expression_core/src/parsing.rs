//! Parser implementation for mathematical expressions.
//!
//! This module provides functionality to tokenize and parse expressions into an AST of `Expression` types that can be evaluated.

use crate::expression::Expression;

/// Represents a token. It is the smallest unit of language grammar, including numbers, variables, operators, function names and parenthesis
#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    /// Numeric Literal (e.g. 42.5)
    Number(f64),
    /// Variable identifier (e.g. x)
    Variable(String),
    /// Addition operator (+)
    Plus,
    /// Subtraction operator (-)
    Minus,
    /// Multiplication operator (*)
    Star,
    /// Division operator (/)
    Slash,
    /// Exponentiation (^)
    Caret,
    /// Left parenthesis
    LParen,
    /// Right parenthesis
    RParen,
    /// Function name (e.g. sin, cos)
    Function(String),
}

/// Parser for mathematical expressions
///
/// Converts a stream of tokens into an AST using mathematical operator precedence rules
pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    /// Creates a new parser with the given tokens.
    ///
    /// # Arguments
    ///
    /// * `tokens` - A vector of tokens to parse
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, current: 0 }
    }

    /// Returns the current token without consuming it
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.current)
    }

    // Consumes and returns the current token, advancing to the next token
    fn advance(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.current).cloned();
        self.current += 1;
        token
    }

    /// Parses a complete expression from the token stream.
    ///
    /// # Returns
    ///
    /// * `Ok(expression)` - Successfully parsed expression
    /// * `Err(String)` - Error if parsing fails
    pub fn parse_expression(&mut self) -> Result<Expression, String> {
        self.parse_addition()
    }

    /// Parses addition and subtraction operations.
    fn parse_addition(&mut self) -> Result<Expression, String> {
        let mut expr = self.parse_multiplication_division()?;

        while let Some(token) = self.peek() {
            match token {
                Token::Plus => {
                    self.advance();
                    expr = Expression::Add(
                        Box::new(expr),
                        Box::new(self.parse_multiplication_division()?),
                    );
                }
                Token::Minus => {
                    self.advance();
                    expr = Expression::Subtract(
                        Box::new(expr),
                        Box::new(self.parse_multiplication_division()?),
                    );
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    /// Parses multiplication and division operators.
    fn parse_multiplication_division(&mut self) -> Result<Expression, String> {
        let mut expr = self.parse_power()?;

        while let Some(token) = self.peek() {
            match token {
                Token::Star => {
                    self.advance();
                    expr = Expression::Multiply(Box::new(expr), Box::new(self.parse_power()?));
                }
                Token::Slash => {
                    self.advance();
                    expr = Expression::Divide(Box::new(expr), Box::new(self.parse_power()?));
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    /// Parses exponentiation.
    fn parse_power(&mut self) -> Result<Expression, String> {
        let mut expr = self.parse_primary()?;

        while let Some(Token::Caret) = self.peek() {
            self.advance();
            expr = Expression::Power(Box::new(expr), Box::new(self.parse_primary()?));
        }

        Ok(expr)
    }

    /// Parses primary expressions (numbers, variables, parenthesized expressions, functions).
    fn parse_primary(&mut self) -> Result<Expression, String> {
        let token = self.advance().ok_or("Unexpected end of input")?;

        match token {
            Token::Number(n) => Ok(Expression::Number(n)),
            Token::Variable(name) => {
                let name_clone = name.clone();

                if self.current < self.tokens.len()
                    && matches!(self.tokens[self.current], Token::LParen)
                {
                    self.advance();

                    let _ = self.parse_addition()?;

                    if self.advance() != Some(Token::RParen) {
                        return Err("Expected ')' after function argument".to_string());
                    }

                    return Err(format!("Unknown function: {}", name_clone));
                }

                Ok(Expression::Variable(name_clone))
            }
            Token::LParen => {
                let expr = self.parse_expression()?;
                if self.advance() != Some(Token::RParen) {
                    return Err("Expected closing parenthesis".to_string());
                }
                Ok(expr)
            }
            Token::Function(name) => {
                let func_name = name.clone();

                if self.advance() != Some(Token::LParen) {
                    return Err("Expected '(' after function name".to_string());
                }

                let arg = self.parse_expression()?;

                if self.advance() != Some(Token::RParen) {
                    return Err("Expected ')' after function argument".to_string());
                }

                match func_name.as_str() {
                    "sin" => Ok(Expression::Sin(Box::new(arg))),
                    "cos" => Ok(Expression::Cos(Box::new(arg))),
                    "tan" => Ok(Expression::Tan(Box::new(arg))),
                    "arcsin" => Ok(Expression::ArcSin(Box::new(arg))),
                    "arccos" => Ok(Expression::ArcCos(Box::new(arg))),
                    "arctan" => Ok(Expression::ArcTan(Box::new(arg))),
                    _ => Err(format!("Unknown function: {}", func_name)),
                }
            }
            _ => Err("Unexpected token".to_string()),
        }
    }
}

/// Converts a string mathematical expression into a sequence of tokens.
///
/// This function breaks down a mathematical expression into its constituent parts
/// (numbers, variables, operators, etc.) that can be processed by the parser.
///
/// # Arguments
///
/// * `input` - The string expression to tokenize
///
/// # Returns
///
/// * `Ok(Vec<Token>)` - Successfully tokenized expression
/// * `Err(String)` - Error message if tokenization fails
///
/// # Examples
///
/// ```
/// # use expression_core::parsing::{tokenize, Token};
/// let tokens = tokenize("x + 2").unwrap();
/// assert_eq!(tokens.len(), 3);
/// ```
pub fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();

    while let Some(&c) = chars.peek() {
        match c {
            ' ' | '\t' | '\r' => {
                chars.next();
            }
            '0'..='9' | '.' => {
                let mut num = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_ascii_digit() || c == '.' {
                        num.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::Number(num.parse().map_err(|_| "Invalid number")?));
            }
            'a'..='z' | 'A'..='Z' => {
                let mut name = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_ascii_alphabetic() {
                        name.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }

                match name.as_str() {
                    "sin" | "cos" | "tan" | "arcsin" | "arccos" | "arctan" => {
                        tokens.push(Token::Function(name));
                    }
                    _ => {
                        tokens.push(Token::Variable(name));
                    }
                }
            }
            '+' => {
                tokens.push(Token::Plus);
                chars.next();
            }
            '-' => {
                tokens.push(Token::Minus);
                chars.next();
            }
            '*' => {
                tokens.push(Token::Star);
                chars.next();
            }
            '/' => {
                tokens.push(Token::Slash);
                chars.next();
            }
            '^' => {
                tokens.push(Token::Caret);
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RParen);
                chars.next();
            }
            _ => return Err(format!("Unexpected character: {}", c)),
        }
    }

    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_str(input: &str) -> Result<Expression, String> {
        let tokens = tokenize(input)?;
        let mut parser = Parser::new(tokens);
        parser.parse_expression()
    }

    #[test]
    fn test_parse_number() {
        let expr = parse_str("42").unwrap();
        assert!(matches!(expr, Expression::Number(42.0)));
    }

    #[test]
    fn test_parse_variable() {
        let expr = parse_str("x").unwrap();
        assert!(matches!(expr, Expression::Variable(name) if name == "x"));
    }

    #[test]
    fn test_parse_addition() {
        let expr = parse_str("1 + 2").unwrap();
        match expr {
            Expression::Add(left, right) => {
                assert!(matches!(*left, Expression::Number(1.0)));
                assert!(matches!(*right, Expression::Number(2.0)));
            }
            _ => panic!("Expected Add expression"),
        }
    }

    #[test]
    fn test_parse_subtraction() {
        let expr = parse_str("3 - 1").unwrap();
        match expr {
            Expression::Subtract(left, right) => {
                assert!(matches!(*left, Expression::Number(3.0)));
                assert!(matches!(*right, Expression::Number(1.0)));
            }
            _ => panic!("Expected Subtract expression"),
        }
    }

    #[test]
    fn test_parse_multiplication() {
        let expr = parse_str("2 * 3").unwrap();
        match expr {
            Expression::Multiply(left, right) => {
                assert!(matches!(*left, Expression::Number(2.0)));
                assert!(matches!(*right, Expression::Number(3.0)));
            }
            _ => panic!("Expected Multiply expression"),
        }
    }

    #[test]
    fn test_parse_division() {
        let expr = parse_str("6 / 2").unwrap();
        match expr {
            Expression::Divide(left, right) => {
                assert!(matches!(*left, Expression::Number(6.0)));
                assert!(matches!(*right, Expression::Number(2.0)));
            }
            _ => panic!("Expected Divide expression"),
        }
    }

    #[test]
    fn test_parse_power() {
        let expr = parse_str("2 ^ 3").unwrap();
        match expr {
            Expression::Power(left, right) => {
                assert!(matches!(*left, Expression::Number(2.0)));
                assert!(matches!(*right, Expression::Number(3.0)));
            }
            _ => panic!("Expected Power expression"),
        }
    }

    #[test]
    fn test_parse_parentheses() {
        let expr = parse_str("2 * (3 + 4)").unwrap();
        match expr {
            Expression::Multiply(left, right) => {
                assert!(matches!(*left, Expression::Number(2.0)));
                match *right {
                    Expression::Add(add_left, add_right) => {
                        assert!(matches!(*add_left, Expression::Number(3.0)));
                        assert!(matches!(*add_right, Expression::Number(4.0)));
                    }
                    _ => panic!("Expected Add expression"),
                }
            }
            _ => panic!("Expected Multiply expression"),
        }
    }

    #[test]
    fn test_parse_functions() {
        let expr = parse_str("sin(x)").unwrap();
        match expr {
            Expression::Sin(inner) => {
                assert!(matches!(*inner, Expression::Variable(name) if name == "x"));
            }
            _ => panic!("Expected Sin expression"),
        }

        let expr = parse_str("cos(0)").unwrap();
        match expr {
            Expression::Cos(inner) => {
                assert!(matches!(*inner, Expression::Number(0.0)));
            }
            _ => panic!("Expected Cos expression"),
        }
    }

    #[test]
    fn test_parse_complex_expression() {
        let expr = parse_str("x^2 + 2*x + 1").unwrap();
        match expr {
            Expression::Add(left1, right1) => {
                match *left1 {
                    Expression::Add(left2, right2) => {
                        match *left2 {
                            Expression::Power(base, exp) => {
                                assert!(matches!(*base, Expression::Variable(name) if name == "x"));
                                assert!(matches!(*exp, Expression::Number(2.0)));
                            }
                            _ => panic!("Expected Power expression"),
                        }
                        match *right2 {
                            Expression::Multiply(left3, right3) => {
                                assert!(matches!(*left3, Expression::Number(2.0)));
                                assert!(
                                    matches!(*right3, Expression::Variable(name) if name == "x")
                                );
                            }
                            _ => panic!("Expected Multiply expression"),
                        }
                    }
                    _ => panic!("Expected Add expression"),
                }
                assert!(matches!(*right1, Expression::Number(1.0)));
            }
            _ => panic!("Expected Add expression"),
        }
    }

    #[test]
    fn test_operator_precedence() {
        // Test that 1 + 2 * 3 = 1 + (2 * 3) = 7, not (1 + 2) * 3 = 9
        let expr = parse_str("1 + 2 * 3").unwrap();
        match expr {
            Expression::Add(left, right) => {
                assert!(matches!(*left, Expression::Number(1.0)));
                match *right {
                    Expression::Multiply(mult_left, mult_right) => {
                        assert!(matches!(*mult_left, Expression::Number(2.0)));
                        assert!(matches!(*mult_right, Expression::Number(3.0)));
                    }
                    _ => panic!("Expected Multiply expression"),
                }
            }
            _ => panic!("Expected Add expression"),
        }
    }

    #[test]
    fn test_parse_errors() {
        assert!(parse_str("(1 + 2").is_err()); // Missing closing paren
        assert!(parse_str("sin(x").is_err()); // Missing closing paren after function
        assert!(parse_str("unknown(x)").is_err()); // Unknown function
        assert!(parse_str("1 +").is_err()); // Incomplete expression
    }
}
