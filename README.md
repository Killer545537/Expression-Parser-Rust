# Mathematical Expression Parser

This is a Rust library used for parsing and evaluating mathematical expressions (want to add algebraic manipulations). It is inspired by `Sympy` from Python and I want to try to make this into a fully working project.

## Features

* Parse mathematical expressions from strings
* Evaluate expressions with variable substitution
* Build expression trees
* Compile-time expression parsing with proc-macros
* Support for
    * Basic arithmetic: `+, -, *, /, ^`
    * Trigonometric Functions: `sin`, `cos`, `tan`, `arcsin`, `arccos`, `arctan`

## Crate Structure

The project is organized into three crates:
* `expression_core`: Contains the `Expression` type and parsing logic
* `expression_macro`: Contains the proc-macro for compile-time expression parsing
* `expression_parser`: High-level API for parsing and evaluating expressions

## Installation

Add the following to your `Cargo.toml`:
```toml
[dependencies]
expression_parser = "0.1.0"
```

For compile-time expression parsing:
```toml
[dependencies]
expression_macro = "0.1.0"
```