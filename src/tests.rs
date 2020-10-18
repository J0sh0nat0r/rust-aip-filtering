// Tests using examples from https://google.aip.dev/160

use crate::ast::FilterParser;

fn test_parse(input: &str, expected: &str) {
    let filter = FilterParser::parse_str(input).unwrap();

    assert_eq!(format!("{}", filter.unwrap()), expected);
}

// https://google.aip.dev/160#logical-operators
mod logical_operators {
    use crate::tests::test_parse;

    #[test]
    fn and() {
        test_parse("a AND b", "(a AND b)");
    }

    #[test]
    fn or() {
        test_parse("a OR b OR c", "((a OR b) OR c)");
    }
}

// https://google.aip.dev/160#negation-operators
mod negation_operators {
    use crate::tests::test_parse;

    #[test]
    fn neg() {
        test_parse("-a", "(-a)")
    }

    #[test]
    fn not() {
        test_parse("NOT a", "(NOT a)")
    }
}

// https://google.aip.dev/160#comparison-operators
mod comparison_operators {
    use crate::tests::test_parse;

    #[test]
    fn eq() {
        test_parse("a = true", "(a = true)")
    }

    #[test]
    fn ne() {
        test_parse("a != 42", "(a != 42)")
    }

    #[test]
    fn lt() {
        test_parse("a < 42", "(a < 42)")
    }

    #[test]
    fn gt() {
        test_parse("a > \"foo\"", "(a > \"foo\")")
    }

    #[test]
    fn lt_eq() {
        test_parse("a <= \"foo\"", "(a <= \"foo\")")
    }

    #[test]
    fn gt_eq() {
        test_parse("a >= 42", "(a >= 42)")
    }
}

// https://google.aip.dev/160#traversal-operator
#[test]
fn traversal_operator() {
    test_parse("a.b = true", "((a.b) = true)");
    test_parse("a.b > 42", "((a.b) > 42)");
    test_parse("a.b.c = \"foo\"", "((a.b.c) = \"foo\")");
}

// https://google.aip.dev/160#has-operator
#[test]
fn has_operator() {
    test_parse("r:42", "(r:42)");
    test_parse("r.foo:42", "((r.foo):42)");
    test_parse("m:foo", "(m:foo)");
    test_parse("m.foo:*", "((m.foo):*)");
    test_parse("m.foo:42", "((m.foo):42)");
}

// https://google.aip.dev/160#functions
#[test]
fn functions() {
    test_parse("main()", "(main())");
    test_parse(
        "regex(m.key, '^.*prod.*$')",
        "(regex((m.key), \"^.*prod.*$\"))",
    );
    test_parse("math.mem('30mb')", "(math.mem(\"30mb\"))");
}
