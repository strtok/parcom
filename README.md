# Parcom [![Rust](https://github.com/strtok/parcom/actions/workflows/rust.yml/badge.svg)](https://github.com/strtok/parcom/actions/workflows/rust.yml)

Parcom is a trait + closure based parser combinator library loosely following the [Parsec Paper](https://www.microsoft.com/en-us/research/publication/parsec-direct-style-monadic-parser-combinators-for-the-real-world/)

# Example

The following is an example of a parser for a lisp like language:

```rust
pub fn identifier<'a>() -> impl Parser<&'a str, String> {
    let initial_identifier = || one_of!(alphabetic_char(), one_of_char("!$%&*/:<=>?^_~"));
    let peculiar_identifier = one_of_char("+-");
    let subsequent_identifier = one_of!(initial_identifier(), alphabetic_char(), digit_char());

    one_of!(
        seqc!(initial_identifier(), repeatc(subsequent_identifier)),
        peculiar_identifier
    )
}

pub fn variable<'a>() -> impl Parser<&'a str, Cell> {
    mapv(identifier(), Cell::Symbol)
}

pub fn number<'a>() -> impl Parser<&'a str, Cell> {
    let digit = one_of_char("0123456789");
    let sign = one_of_char("+-");
    let num10 = mapv(
        seqc!(optional(sign), collect(repeat1(digit))),
        |s: String| match s.parse::<i64>() {
            Ok(n) => Cell::Number(n),
            Err(_) => Cell::Number(0),
        },
    );

    mapv(one_of!(num10), Cell::from)
}

pub fn ows<'a>() -> impl Parser<&'a str, String> {
    discard(optional(whitespace_char()))
}

pub fn procedure_call<'a>() -> impl Parser<&'a str, Cell> {
    mapv(
        between(ch('('), repeat1(between(ows(), expression, ows())), ch(')')),
        Cell::new_list,
    )
}

pub fn expression(input: &str) -> ParseResult<&str, Cell> {
    one_of!(procedure_call(), number(), variable()).apply(input)
}
```
