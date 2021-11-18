/// The result of a parser application
///
/// ParseResult<I, O> is the result returned by parsers to propagate
/// recursively parsed results, or errors.
///
/// * Ok((I, Option<O>)) contains the remaining unparsed input (I)
/// and an optional output of the parser.
///
/// An Err result contains the input that could not be parsed.
pub type ParseResult<I, O> = Result<(I, Option<O>), I>;


/// A parser
///
/// A parser is applied on input, and returns a result containing
/// the remaining unparsed input and optional output, or an error.
pub trait Parser<I, O> {
    fn apply(&self, input: I) -> ParseResult<I, O>;
}

/// Implement Parser for functions in the parser form.
///
/// Any function in the form Fn(I) -> ParseResult<I, O> may be
/// treated as a parser.
impl<F, I, O> Parser<I, O> for F
where
    F: Fn(I) -> ParseResult<I, O>,
{
    fn apply(&self, input: I) -> ParseResult<I, O> {
        self(input)
    }
}

/// Empty
///
/// A parser that consumes no input and always returns an empty
/// result.
pub fn empty<I>(input: I) -> ParseResult<I, ()> {
    Ok((input, None))
}

/// Optional
///
/// Apply input to `parser`. If parser returns Err, then map
/// the error to an Ok(_, None) result.
///
/// # Arguments
/// * `parser` - The parser to apply
pub fn optional<P, I, O>(parser: P) -> impl Parser<I, O>
where
    P: Parser<I, O>,
    I: Copy,
{
    move |input| parser.apply(input).or(Ok((input, None)))
}

/// Discard
///
/// Apply input to `parser` and discard any output by mapping the
/// output to None.
///
/// # Arguments
/// * `parser` - The parser to apply
pub fn discard<P, I, O>(parser: P) -> impl Parser<I, O>
where
    P: Parser<I, O>,
    I: Copy,
{
    move |input| parser.apply(input).map(|(rest, _)| (rest, None))
}

/// Satisfy
///
/// Apply input to `parser`, and return it if f(input) evaluates to
/// true. Otherwise, return Err.
///
/// # Arguments
/// * `parser` - The parser to apply
/// * `f` - The function to apply the parser output to
pub fn satisfy<P, F, I, O>(parser: P, f: F) -> impl Parser<I, O>
where
    F: Fn(&O) -> bool,
    P: Parser<I, O>,
    I: Copy,
{
    move |input| match parser.apply(input) {
        Ok((rest, None)) => Ok((rest, None)),
        Ok((rest, Some(output))) if f(&output) => Ok((rest, Some(output))),
        _ => Err(input),
    }
}

/// Map
///
/// Apply input to `parser`, mapping any Ok value with the function f.
///
/// # Arguments
/// * `parser` - The parser to apply
/// * `f` - The function to map the parser output value with
pub fn map<P, F, I, A, B>(parser: P, f: F) -> impl Parser<I, B>
where
    P: Parser<I, A>,
    F: Fn(Option<A>) -> Option<B>,
{
    move |input| parser.apply(input).map(|(rest, output)| (rest, f(output)))
}

/// Mapv
///
/// Apply input to `parser`, mapping any Ok(Some(_)) value with the function f.
///
/// # Arguments
/// * `parser` - The parser to apply
/// * `f` - The function to map the parser output value with
pub fn mapv<P, F, I, A, B>(parser: P, f: F) -> impl Parser<I, B>
where
    P: Parser<I, A>,
    F: Fn(A) -> B,
{
    map(parser, move |output| output.map(|output| f(output)))
}

/// Repeat
///
/// Apply the parser continually until it return Err, returning a vector of
/// ParserResults containing the Ok(_) results.
///
/// # Arguments
/// * `parser` - The parser to apply repeatedly
pub fn repeat<P, I, O>(parser: P) -> impl Parser<I, Vec<O>>
where
    P: Parser<I, O>,
    I: Copy,
{
    move |input| {
        let mut outputs = Vec::new();
        let mut rest = input;
        while let Ok((next, output)) = parser.apply(rest) {
            rest = next;
            if let Some(output) = output {
                outputs.push(output);
            }
        }
        Ok((
            rest,
            match outputs.is_empty() {
                true => None,
                false => Some(outputs),
            },
        ))
    }
}

/// Repeat
///
/// Apply the parser continually until it return Err, returning a vector of
/// ParserResults containing the Ok(_) results. Return an error if the first
/// application of the parser returned Err.
///
/// # Arguments
/// * `parser` - The parser to apply repeatedly
pub fn repeat1<P, I, O>(parser: P) -> impl Parser<I, Vec<O>>
where
    P: Parser<I, O>,
    I: Copy,
{
    let parser = repeat(parser);
    move |input| match parser.apply(input) {
        Ok((_, None)) => Err(input),
        Ok(output) => Ok(output),
        Err(e) => Err(e),
    }
}

/// Repeatc
///
/// Apply repeat() and then collect the vector into the inferred type U.
///
/// # Arguments
/// * `parser` - The parser to apply repeatedly
pub fn repeatc<P, I, O, U>(parser: P) -> impl Parser<I, U>
where
    P: Parser<I, O>,
    I: Copy,
    U: std::iter::FromIterator<<Vec<O> as IntoIterator>::Item>,
{
    mapv(repeat(parser), |v| v.into_iter().collect())
}

/// One Of
///
/// Apply parsers in order until one returns an Ok result, returning the
/// result of that parser. If any parser returns Err, `one_of` will immediately
/// return that Err.
///
/// # Arguments
/// * `parsers` - A vector of parsers to apply in order
pub fn one_of<'a, I, O>(parsers: Vec<Box<dyn 'a + Parser<I, O>>>) -> impl 'a + Parser<I, O>
where
    I: Copy + 'a,
    O: 'a,
{
    move |input| {
        parsers
            .iter()
            .map(|p| p.apply(input))
            .find(|o| o.is_ok())
            .unwrap_or(Err(input))
    }
}

#[macro_export]
macro_rules! one_of {
    ( $( $x:expr ),* ) => {
        {
            let mut v = Vec::<Box<dyn Parser<_, _>>>::new();
            $(
                v.push(Box::new($x));
            )*
            one_of(v)
        }
    };
}

/// Sequence
///
/// Apply parsers in order, returning a vector of each parser's result.
///
/// * Any Ok((_, None)) results are filtered out
/// * Any parser that returns Err causes seq to immediately return Err
///
/// # Arguments
/// * `parsers` - The parsers to apply
pub fn seq<'a, I, O>(parsers: Vec<Box<dyn 'a + Parser<I, O>>>) -> impl 'a + Parser<I, Vec<O>>
where
    I: Copy + 'a,
    O: 'a,
{
    move |input| {
        let mut outputs = Vec::new();
        let mut rest = input;
        for parser in &parsers {
            match parser.apply(rest) {
                Ok((next, output)) => {
                    if let Some(output) = output {
                        outputs.push(output);
                    }
                    rest = next;
                }
                Err(_) => return Err(input),
            }
        }
        Ok((
            rest,
            match outputs.is_empty() {
                true => None,
                false => Some(outputs),
            },
        ))
    }
}

#[macro_export]
macro_rules! seq {
    ( $( $x:expr ),* ) => {
        {
            let mut v = Vec::<Box<dyn Parser<_, _>>>::new();
            $(
                v.push(Box::new($x));
            )*
            seq(v)
        }
    };
}

#[macro_export]
macro_rules! seqc {
    ( $( $x:expr ),* ) => {
        {
            let mut v = Vec::<Box<dyn Parser<_, _>>>::new();
            $(
                v.push(Box::new($x));
            )*
            collect(seq(v))
        }
    };
}

/// Between
///
/// Apply three parsers (prefix, paraser, suffix) and return the result of
/// `parser`'s output.
///
/// This parser may be used to parse expressions such as quoted strings (e.g. "foo")
/// or expressions like "(foo bar baz)".
///
/// # Arguments
/// `prefix` - The first parser to apply
/// `parser` - The parser to apply and return
/// `suffix` - The final parser to apply
pub fn between<A, B, C, OA, OB, OC, I>(prefix: A, parser: B, suffix: C) -> impl Parser<I, OB>
where
    A: Parser<I, OA>,
    B: Parser<I, OB>,
    C: Parser<I, OC>,
    I: Copy,
{
    move |input| {
        let mut rest = input;
        match prefix.apply(rest) {
            Ok((next, _)) => {
                rest = next;
            }
            Err(_) => return Err(input),
        }

        match parser.apply(rest) {
            Ok((next, output)) => {
                rest = next;
                match suffix.apply(rest) {
                    Ok((next, _)) => {
                        rest = next;
                        Ok((rest, output))
                    }
                    Err(_) => Err(input),
                }
            }
            Err(_) => Err(input),
        }
    }
}

/// Collect
///
/// Collect the results of `parser` into the type inferred by U.
///
/// # Arguments
/// * `parser` - The parser to apply
pub fn collect<P, I, O, U>(parser: P) -> impl Parser<I, U>
where
    P: Parser<I, O>,
    I: Copy,
    O: IntoIterator,
    U: std::iter::FromIterator<O::Item>,
{
    mapv(parser, |v| v.into_iter().collect())
}

pub fn into<P, I, O, U>(parser: P) -> impl Parser<I, U>
where
    P: Parser<I, O>,
    I: Copy,
    O: Into<U>,
{
    mapv(parser, |output| output.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn any_char(input: &str) -> ParseResult<&str, char> {
        match input.chars().next() {
            Some(c) => Ok((&input[c.len_utf8()..], Some(c))),
            None => Err(input),
        }
    }

    pub fn ch<'a>(expected: char) -> impl Parser<&'a str, char> {
        satisfy(any_char, move |&c| c == expected)
    }

    fn digit_char<'a>() -> impl Parser<&'a str, char> {
        satisfy(any_char, |&c| c.is_digit(10))
    }

    pub fn alphabetic_char<'a>() -> impl Parser<&'a str, char> {
        satisfy(any_char, |&c| c.is_alphabetic())
    }

    #[test]
    fn empty_does_not_consume() {
        assert_eq!(empty("dog"), Ok(("dog", None)));
    }

    #[test]
    fn satisfy_returns_matched_char() {
        assert_eq!(
            satisfy(any_char, |&c| c == 'd').apply("dog"),
            Ok(("og", Some('d')))
        );
        assert_eq!(satisfy(any_char, |&c| c == 'd').apply("cat"), Err("cat"));
    }

    #[test]
    fn map_all() {
        assert_eq!(
            map(any_char, |_| Some("x")).apply("dog"),
            Ok(("og", Some("x")))
        );
    }

    #[test]
    fn repeat_captures_while_satisfied() {
        // consume up to not satisfied
        assert_eq!(
            repeat(digit_char()).apply("123abc"),
            Ok(("abc", Some(vec!('1', '2', '3'))))
        );

        // consume full input
        assert_eq!(
            repeat(digit_char()).apply("123"),
            Ok(("", Some(vec!('1', '2', '3'))))
        );

        // zero is OK
        assert_eq!(repeat(digit_char()).apply("abc"), Ok(("abc", None)));
    }

    #[test]
    fn repeat1_captures_while_satisfied() {
        // consume up to not satisfied
        assert_eq!(
            repeat1(digit_char()).apply("123abc"),
            Ok(("abc", Some(vec!('1', '2', '3'))))
        );

        // consume full input
        assert_eq!(
            repeat1(digit_char()).apply("123"),
            Ok(("", Some(vec!('1', '2', '3'))))
        );

        // zero is NOT OK
        assert_eq!(repeat1(digit_char()).apply("abc"), Err("abc"));
    }

    #[test]
    fn digit_parsing() {
        let parser = mapv(repeat1(digit_char()), |v| {
            v.iter()
                .map(|&c| c as u8 - 48)
                .fold(0, |acc, e| acc * 10 + e)
        });
        assert_eq!(parser.apply("42"), Ok(("", Some(42))));
        assert_eq!(parser.apply("012"), Ok(("", Some(12))));
        assert_eq!(parser.apply("abc"), Err("abc"));
    }

    #[test]
    fn optional_maps_err_to_empty_value() {
        assert_eq!(optional(digit_char()).apply("dog"), Ok(("dog", None)));
        assert_eq!(optional(digit_char()).apply("123"), Ok(("23", Some('1'))));
    }

    #[test]
    fn discard_maps_value_to_empty_value() {
        assert_eq!(discard(digit_char()).apply("dog"), Err("dog"));
        assert_eq!(discard(digit_char()).apply("123"), Ok(("23", None)));
    }

    #[test]
    fn one_of_finds_a_successful_parser() {
        assert_eq!(
            one_of!(digit_char(), alphabetic_char()).apply("1a"),
            Ok(("a", Some('1')))
        );
        assert_eq!(
            one_of!(alphabetic_char(), digit_char()).apply("1a"),
            Ok(("a", Some('1')))
        );
        assert_eq!(one_of!(alphabetic_char()).apply("1a"), Err("1a"));
    }

    #[test]
    fn seq_parses_sequence_but_returns_first_err() {
        let parser = seq!(digit_char(), alphabetic_char(), digit_char());
        assert_eq!(parser.apply("1a2"), Ok(("", Some(vec!('1', 'a', '2')))));
        assert_eq!(
            parser.apply("1a2other"),
            Ok(("other", Some(vec!('1', 'a', '2'))))
        );
        assert_eq!(parser.apply("dog"), Err("dog"));
        assert_eq!(parser.apply("1dog"), Err("1dog"));
    }

    #[test]
    fn seq_ignores_none() {
        let parser = seq!(digit_char(), optional(alphabetic_char()), digit_char());
        assert_eq!(parser.apply("1a2"), Ok(("", Some(vec!('1', 'a', '2')))));
        assert_eq!(parser.apply("12"), Ok(("", Some(vec!('1', '2')))));
    }

    #[test]
    fn flatten() {
        fn parser<'a>() -> impl Parser<&'a str, String> {
            super::collect(seq!(digit_char(), alphabetic_char()))
        }

        assert_eq!(parser().apply("1a"), Ok(("", Some("1a".to_owned()))));
    }

    #[test]
    fn into() {
        fn parser<'a>() -> impl Parser<&'a str, String> {
            super::into(alphabetic_char())
        }

        assert_eq!(parser().apply("a"), Ok(("", Some("a".to_owned()))));
    }

    #[test]
    fn between() {
        fn parser<'a>() -> impl Parser<&'a str, String> {
            super::between(ch('('), collect(repeat(digit_char())), ch(')'))
        }
        assert_eq!(
            parser().apply("(12345)"),
            Ok(("", Some("12345".to_owned())))
        );
    }
}
