// lexer for cflat's front-end syntax.

use std::{
    ops::{Bound, Range, RangeBounds},
    sync::atomic::{AtomicU32, Ordering},
};
use Regex::*;

// use ordered sets and maps to allow for deterministic outputs.
pub use std::collections::{BTreeMap as Map, BTreeSet as Set};

use derive_more::Display;

pub mod implementation;
pub use implementation::*;

// tokenizes the given string; invalid lexemes are represented with Error tokens
// in the returned vector.
#[allow(dead_code)]
pub fn lex(code: &str) -> Vec<Token> {
    let lexer = implementation::Lexer::new();
    lexer.lex(code)
}

// SECTION: Tokens

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Range<usize>,
}

#[derive(Clone, Copy, Debug, Display, Eq, PartialEq)]
pub enum TokenKind {
    // represents invalid lexemes, i.e., unrecognized ASCII characters.
    Error,

    #[display(fmt = "num")]
    Num,

    #[display(fmt = "id")]
    Id,

    #[display(fmt = "int")]
    Int,

    #[display(fmt = "struct")]
    Struct,

    #[display(fmt = "nil")]
    Nil,

    #[display(fmt = "break")]
    Break,

    #[display(fmt = "continue")]
    Continue,

    #[display(fmt = "return")]
    Return,

    #[display(fmt = "if")]
    If,

    #[display(fmt = "else")]
    Else,

    #[display(fmt = "while")]
    While,

    #[display(fmt = "new")]
    New,

    #[display(fmt = "let")]
    Let,

    #[display(fmt = "extern")]
    Extern,

    #[display(fmt = "fn")]
    Fn,

    #[display(fmt = ":")]
    Colon,

    #[display(fmt = ";")]
    Semicolon,

    #[display(fmt = ",")]
    Comma,

    #[display(fmt = "_")]
    Underscore,

    #[display(fmt = "->")]
    Arrow,

    #[display(fmt = "&")]
    Address,

    #[display(fmt = "!")]
    Bang,

    #[display(fmt = "+")]
    Plus,

    #[display(fmt = "-")]
    Dash,

    #[display(fmt = "*")]
    Star,

    #[display(fmt = "/")]
    Slash,

    #[display(fmt = "==")]
    Equal,

    #[display(fmt = "!=")]
    NotEq,

    #[display(fmt = "<")]
    Lt,

    #[display(fmt = "<=")]
    Lte,

    #[display(fmt = ">")]
    Gt,

    #[display(fmt = ">=")]
    Gte,

    #[display(fmt = "and")]
    And,

    #[display(fmt = "or")]
    Or,

    #[display(fmt = ".")]
    Dot,

    #[display(fmt = "=")]
    Gets,

    #[display(fmt = "(")]
    OpenParen,

    #[display(fmt = ")")]
    CloseParen,

    #[display(fmt = "[")]
    OpenBracket,

    #[display(fmt = "]")]
    CloseBracket,

    #[display(fmt = "{{")]
    OpenBrace,

    #[display(fmt = "}}")]
    CloseBrace,
}

// SECTION: Regular expressions

// A character range, that may be open in either end.
//
// We implement this as a separate type because there is no super trait or type
// for Range, RangeInclusive, etc. that we can use easily and we have to store
// the lower and the upper bounds separately in the automaton.
type CharRange = (Bound<char>, Bound<char>);

// Check if the given character is contained in the given range.
fn in_bounds(range: &CharRange, c: char) -> bool {
    use Bound::*;

    (match range.0 {
        Included(l) => l <= c,
        Excluded(l) => l < c,
        Unbounded => true,
    }) && (match range.1 {
        Included(u) => c <= u,
        Excluded(u) => c < u,
        Unbounded => true,
    })
}

/// Build a character range from given Range-like type.
///
/// For example, char_range('a'..='z') produces a character range for a-z that
/// includes both sides.  This function is mainly useful for testing.
pub fn char_range<I: RangeBounds<char>>(r: I) -> CharRange {
    (r.start_bound().cloned(), r.end_bound().cloned())
}

// A regular expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Regex {
    /// The empty string
    Empty,
    /// The empty set
    Never,
    /// A range of characters, like `[a-z]`.  We represent a single character
    /// `c` using the range `[c-c]`.
    Chars(CharRange),
    /// Kleene star
    Star(Box<Regex>),
    /// Concatenation: r1r2
    Concat(Box<Regex>, Box<Regex>),
    /// Choice r1|r2
    Choice(Box<Regex>, Box<Regex>),
}

// Note: The Regex constructors below check `self` and `other` to perform some
// simplification.  Their implementation details aren't important for your
// lexer's correctness.

impl Regex {
    /// Compute Kleene star of self, (self)*.
    pub fn star(&self) -> Regex {
        match self {
            Star(_) => self.clone(),
            Never => Empty,
            Empty => Empty,
            _ => Star(Box::new(self.clone())),
        }
    }

    /// Compute (self)(other), that is the concatenation of self and other.
    pub fn then(&self, other: &Regex) -> Regex {
        match (self, other) {
            (Never, _) | (_, Never) => Never,
            (Empty, _) => other.clone(),
            (_, Empty) => self.clone(),
            _ => Concat(Box::new(self.clone()), Box::new(other.clone())),
        }
    }

    /// Compute the regex for given range.
    ///
    /// For example, `range('a'..='z')` corresponds to `[a-z]` in conventional
    /// notation.
    pub fn range<I: RangeBounds<char>>(r: I) -> Regex {
        Chars(char_range(r))
    }

    /// Compute a regex that matches any one of the characters in the given string.
    ///
    /// For example, `one_of("abc")` corresponds to `a|b|c`.
    pub fn one_of(s: &str) -> Regex {
        // an inefficient representation for char sets
        s.chars()
            .map(|c| Self::range(c..=c))
            .fold(Never, |r1, r2| r1.or(&r2))
    }

    /// Compute a regex that matches only the given string.
    ///
    /// For example, `symbol("abc")` accepts only the string "abc".
    pub fn symbol(s: &str) -> Regex {
        s.chars()
            .map(|c| Regex::range(c..=c))
            .fold(Empty, |r1, r2| r1.then(&r2))
    }

    /// Compute (self)|(other).
    pub fn or(&self, other: &Regex) -> Regex {
        match (self, other) {
            (Never, _) => other.clone(),
            (_, Never) => self.clone(),
            _ => Choice(Box::new(self.clone()), Box::new(other.clone())),
        }
    }

    /// Compute (self)+, that is (self)(self)*
    fn plus(&self) -> Regex {
        self.then(&self.star())
    }

    /// Build a regex that matches all characters except `c`.
    fn anything_but(c: char) -> Regex {
        Regex::range(..c).or(&Regex::range(char::from_u32(c as u32 + 1).unwrap()..))
    }
}

// SECTION: Nondeterministic finite automata

/// NFA states.  Never create a state object yourself, always use
/// `State::fresh`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct State(u32);

impl State {
    /// Generate a fresh state that hasn't been used before
    pub fn fresh() -> State {
        State(NEXT_STATE.fetch_add(1, Ordering::SeqCst))
    }
}

/// Next available state, do not use directly.  It is supposed to be only used
/// by `State::fresh`.
static NEXT_STATE: AtomicU32 = AtomicU32::new(0);

/// An NFA transition: A character range and a set of target states.
type Transition = (CharRange, Set<State>);

/// A DFA transition: A character range and a single target state.
type DfaTransition = (CharRange, State);

/// A nondeterministic finite automaton
#[derive(Debug)]
pub struct Nfa {
    // The set of states, Q
    pub states: Set<State>,
    // Transitions, the symbol portion of δ.  If a state doesn't have any
    // outgoing transitions, then it may not occur in this map.
    pub trans: Map<State, Vec<Transition>>,
    // ε transitions, the ε portion of δ.  If a state doesn't have any outgoing
    // ε transitions, then it may not occur in this map.
    pub epsilon_trans: Map<State, Set<State>>,
    // The start state, q₀
    pub init: State,
    // Accepting states, F
    pub accepting: Set<State>,
}

/// A deterministic finite automaton.  This is not always guaranteed to be
/// well-formed.
#[derive(Debug)]
pub struct Dfa {
    pub states: Set<State>,
    pub trans: Map<State, Vec<DfaTransition>>,
    pub init: State,
    pub accepting: Set<State>,
}
