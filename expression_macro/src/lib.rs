//! # Expression Macro
//!
//! This crate provides procedural macros for creating mathematical expressions at compile time.
//! It serves as a companion to the `expression_core` crate, providing syntactic sugar and
//! compile-time validation for mathematical expressions.
//!
//! ## Benefits of Compile-Time Expression Parsing
//!
//! - **Early Error Detection**: Syntax errors in expressions are caught at compile time
//! - **Performance Optimization**: Parsing happens during compilation rather than at runtime
//! - **Type Safety**: Ensures expressions are well-formed before execution
//!
//! ## Usage
//!
//! ```
//! use expression_macro::expr;
//! use std::collections::HashMap;
//!
//! let expr = expr!("x^2 + y^2");
//!
//! let mut vars = HashMap::new();
//! vars.insert("x".to_string(), 3.0);
//! vars.insert("y".to_string(), 4.0);
//!
//! let result = expr.evaluate(&vars).unwrap();
//! assert_eq!(result, 25.0);
//! ```

use expression_core::expression::Expression;
use expression_core::parsing;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{LitStr, parse_macro_input};

/// Creates an expression at compile time.
///
/// This macro allows you to parse expressions during compilation,
/// which provides better performance and catches syntax errors early.
///
/// # Examples
///
/// ```
/// use std::collections::HashMap;
/// use expression_macro::expr;
///
/// let expr = expr!("sin(x) + cos(y)");
///
/// let mut vars = HashMap::new();
/// vars.insert("x".to_string(), 0.0);
/// vars.insert("y".to_string(), 0.0);
///
/// let result = expr.evaluate(&vars).unwrap();
/// assert_eq!(result, 1.0);
/// ```
///
/// # Errors
///
/// If the expression contains syntax errors, compilation will fail with
/// appropriate error messages.
///
/// # Supported Syntax
///
/// ## Operators
/// - Addition: `+`
/// - Subtraction: `-`
/// - Multiplication: `*`
/// - Division: `/`
/// - Exponentiation: `^`
///
/// ## Functions
/// - Trigonometric: `sin`, `cos`, `tan`
/// - Inverse trigonometric: `arcsin`, `arccos`, `arctan`
///
/// ## Other Features
/// - Parentheses for grouping: `(expression)`
/// - Variables: any alphabetic identifier
/// - Number literals: both integers and floating-point
///
/// # Technical Details
///
/// This macro uses the tokenizer and parser from the `expression_core` crate to
/// parse the expression string at compile time and generate equivalent Rust code.
/// The output is an `Expression` object that can be evaluated with different variable values.

#[proc_macro]
pub fn expr(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as LitStr);
    let expr_str = input.value();

    // Use the core project's tokenizer and parser
    let tokens = match parsing::tokenize(&expr_str) {
        Ok(t) => t,
        Err(e) => {
            return syn::Error::new_spanned(&input, e).to_compile_error().into();
        }
    };

    let mut parser = parsing::Parser::new(tokens);
    let expr = match parser.parse_expression() {
        Ok(expr) => expr,
        Err(e) => {
            return syn::Error::new_spanned(&input, e).to_compile_error().into();
        }
    };

    // Convert the Expression to Rust code
    expression_to_tokens(&expr).into()
}

/// Converts an `Expression` object to Rust tokens using the `quote` crate.
///
/// This function recursively traverses the expression tree and generates
/// equivalent Rust code that creates the same expression structure at runtime.
///
/// # Arguments
///
/// * `expr` - The expression to convert to tokens
///
/// # Returns
///
/// A `TokenStream2` representing Rust code that creates the input expression
fn expression_to_tokens(expr: &Expression) -> TokenStream2 {
    match expr {
        Expression::Number(n) => {
            quote! { expression_core::expression::Expression::Number(#n) }
        }
        Expression::Variable(name) => {
            quote! { expression_core::expression::Expression::Variable(#name.to_string()) }
        }
        Expression::Add(left, right) => {
            let left_tokens = expression_to_tokens(left);
            let right_tokens = expression_to_tokens(right);
            quote! { expression_core::expression::Expression::Add(Box::new(#left_tokens), Box::new(#right_tokens)) }
        }
        Expression::Subtract(left, right) => {
            let left_tokens = expression_to_tokens(left);
            let right_tokens = expression_to_tokens(right);
            quote! { expression_core::expression::Expression::Subtract(Box::new(#left_tokens), Box::new(#right_tokens)) }
        }
        Expression::Multiply(left, right) => {
            let left_tokens = expression_to_tokens(left);
            let right_tokens = expression_to_tokens(right);
            quote! { expression_core::expression::Expression::Multiply(Box::new(#left_tokens), Box::new(#right_tokens)) }
        }
        Expression::Divide(left, right) => {
            let left_tokens = expression_to_tokens(left);
            let right_tokens = expression_to_tokens(right);
            quote! { expression_core::expression::Expression::Divide(Box::new(#left_tokens), Box::new(#right_tokens)) }
        }
        Expression::Power(base, exponent) => {
            let base_tokens = expression_to_tokens(base);
            let exponent_tokens = expression_to_tokens(exponent);
            quote! { expression_core::expression::Expression::Power(Box::new(#base_tokens), Box::new(#exponent_tokens)) }
        }
        Expression::Sin(inner) => {
            let inner_tokens = expression_to_tokens(inner);
            quote! { expression_core::expression::Expression::Sin(Box::new(#inner_tokens)) }
        }
        Expression::Cos(inner) => {
            let inner_tokens = expression_to_tokens(inner);
            quote! { expression_core::expression::Expression::Cos(Box::new(#inner_tokens)) }
        }
        Expression::Tan(inner) => {
            let inner_tokens = expression_to_tokens(inner);
            quote! { expression_core::expression::Expression::Tan(Box::new(#inner_tokens)) }
        }
        Expression::ArcSin(inner) => {
            let inner_tokens = expression_to_tokens(inner);
            quote! { expression_core::expression::Expression::ArcSin(Box::new(#inner_tokens)) }
        }
        Expression::ArcCos(inner) => {
            let inner_tokens = expression_to_tokens(inner);
            quote! { expression_core::expression::Expression::ArcCos(Box::new(#inner_tokens)) }
        }
        Expression::ArcTan(inner) => {
            let inner_tokens = expression_to_tokens(inner);
            quote! { expression_core::expression::Expression::ArcTan(Box::new(#inner_tokens)) }
        }
    }
}
