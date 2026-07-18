#pragma once

#include <stdexcept>
#include <string>
#include <vector>

// Token categories for the .math surface language. Keywords get their own
// kinds so the parser can dispatch on TokenKind without re-comparing
// strings. Operator tokens cover both their Unicode and ASCII spellings.
enum class TokenKind {
    // Atoms and literals
    Identifier,
    NumericLiteral,

    // Top-level / declaration keywords
    KeywordModule, KeywordImport, KeywordUsing,
    KeywordInductive, KeywordDefinition, KeywordAxiom, KeywordTheorem,
    KeywordWhere,
    KeywordOperator,        // `operator (+) on (T1, T2) := F;` — operator overload
    KeywordOverload,        // `overload name := F;` — function-name overload alias
    KeywordCongruenceUnderBinder,  // `congruence_under_binder F := L;` — rewrite-under-binder lemma
    KeywordFoldOperation,   // `fold_operation (+) on T := W;` — register a fold-capable operation (W : IsMonoid(T, op, id))
    KeywordCoercion,        // `coercion (S, T) := F;` — explicit type coercion

    // Expression keywords
    KeywordFunction, KeywordLet, KeywordIn,
    KeywordType, KeywordProposition,
    KeywordMax, KeywordImax,

    // Proof keywords
    KeywordCalc, KeywordBy,
    KeywordOn,
    KeywordCase, KeywordCases, KeywordWith,
    KeywordApply,
    KeywordClaim,
    KeywordWitness,
    KeywordSuffices,
    KeywordByInduction,     // `by_induction` — case-split with IH
    KeywordByStrongInduction, // `by_strong_induction` — single-step strong induction
    KeywordByRepresentatives, // `by_representatives x as ⟨a,b⟩, … => body` — nested quotient-cases
    KeywordInduction,       // `induction` — after `claim P by`, opens claim-by-induction
    KeywordGoal,            // `goal` — refers to the elaborator's current expected type
    KeywordDone,            // `done` — bare-`claim` synonym; closes the surrounding goal via auto-prover
    KeywordOkay,            // `okay` — same as `done`. Math-professor style (Aroca).
    KeywordOpaque,          // `opaque` — modifier on `definition`; blocks δ-unfolding
    KeywordAutomatic,       // `automatic` — modifier on theorem/definition; auto-prover may use it unprompted across modules
    KeywordUnfold,          // `unfold X` — surface tactic to opt into δ-unfolding
    KeywordUnfolding,       // `by unfolding X` — δ-unfold X while discharging this step
    KeywordSubstitution,    // `by substitution` — auto-find equality + body
    KeywordSubstituting,    // `by substituting <eq>` — narrow to specified equality
    KeywordRecalling,       // `by <lemma> recalling <fact>, …` — facts in discharge scope
    KeywordContradiction,   // `contradiction` — close goal from P / ¬P
    KeywordObtain,          // RETIRED construct (A5) — kept only for the migration error
    KeywordSuppose,         // `suppose P as h;` — introduce hypothesis as a step
    KeywordChoose,          // `choose N such that P(N);` — Exists-elim via scope lookup
    KeywordFrom,            // separator for `obtain ⟨…⟩ from E;`
    KeywordSet,             // `set n := E;` — transparent local definition
    KeywordSorry,           // `sorry` — placeholder for an unwritten proof
    KeywordRing,            // `ring` — commutative-ring decision tactic
    KeywordGroup,           // `group` — group decision tactic (associativity + inverse cancellation)
    KeywordMonoid,          // `monoid` — monoid decision tactic (associativity + identity)
    KeywordField,           // `field` — field decision tactic (ring + reciprocal_function)
    KeywordLinearCombination,  // `linear_combination(e)` — ring + a known equation
    KeywordConvention,      // `convention p : T with H` — name-bound implicit binder
    KeywordConstruction,    // `construction Name(args) : T := mk(...)` — canonical quotient intro (transparent definition)
    KeywordInstance,        // `instance Name` — register a canonical structure instance (e.g. Integer ⇒ IsGroup)
    KeywordGiven,           // `given (P)` — look up the in-scope hypothesis of type P
    KeywordAs,              // `in (P) as h:` — name the arm's disjunct hypothesis
    KeywordRefining,        // `cases X refining h, …` — refine listed binders' types per case
    KeywordDecide,          // RETIRED construct (A4); contextual keyword kept for qualified names (Natural.decide) + the migration error
    KeywordTake,            // `take h : T;` — introduce a Pi-binder (math-style "take an arbitrary h : T")
    KeywordNote,            // `note goal : T;` / `note P;` — elaboration-time assertion / goal restatement
    KeywordChange,          // `change T;` — replace the goal by a definitionally-equal T
    KeywordIf,              // `if P then a else b` — value-level conditional (sugar for `decide`)
    KeywordThen,            // the `then` of an `if … then … else …`
    KeywordElse,            // the `else` of an `if … then … else …`

    // Punctuation
    LeftParen, RightParen,
    LeftBrace, RightBrace,
    LeftBracket, RightBracket, // "[" / "]" — postfix indexing (`p[k]`)
    LeftAngle, RightAngle,    // "⟨" / "⟩" — anonymous tuples
    Comma, Colon, Semicolon, Pipe,
    Dot,
    Ellipsis,        // "..." — fold/series notation (1 + 2 + ... + n)
    DotLeftBrace,    // ".{"  introduces universe-argument list
    Assign,          // ":="
    FatArrow,        // "=>"
    MapsTo,          // "↦"  introduces a lambda: (binders) ↦ body

    // Operators
    Plus, Minus, Star, Slash, Caret,
    CenterDot,       // "·" (binary operation symbol, multiplicative precedence)
    Bullet,          // "•" (scalar action, multiplicative precedence)
    Compose,         // "∘" (composition, multiplicative precedence)
    Monus,           // "∸" (truncated subtraction, additive precedence)
    InverseSuperscript,  // "⁻¹" (postfix operator symbol, e.g. group inverse)
    SquareSuperscript,   // "²" (postfix squaring; parse-time sugar for E * E)
    TransposeSuperscript, // "ᵀ" (postfix operator symbol, e.g. matrix transpose)
    Bang,            // "!" (postfix operator symbol, e.g. factorial). There is
                     // no "!=" spelling of ≠, so `k!=1` reads as `k! = 1`.
    Less, Greater, LessOrEqual, GreaterOrEqual,
    Equal, NotEqual,
    LogicalAnd, LogicalOr, LogicalNot,
    Divides,         // "∣" (divides relation on Naturals)
    NotDivides,      // "∤" (negated divides)
    NotLessOrEqual,  // "≰" (negated ≤)
    ElementOf,       // "∈" (set membership)
    NotElementOf,    // "∉" (negated membership)
    SubsetOf,        // "⊆" (subset)
    NotSubsetOf,     // "⊈" (negated subset)
    SetMinus,        // "∖" (set difference; on lists, element removal)
    Approx,          // "≈" (equinumerous / generic transitive relation)
    ForAll,          // "∀" (universal-quantifier prefix)
    Exists,          // "∃" (existential-quantifier prefix)
    Arrow,           // "→" or "->"
    Question,        // "?" — placeholder for an argument the elaborator
                     // should infer (by goal-unification + hypothesis
                     // search). At a function call, `f(?, b, c)` asks
                     // the elaborator to fill the first arg.

    EndOfFile,
};

// Returns true if `kind` names a keyword (any KeywordX variant). Useful
// for the parser when it needs to test "this is some keyword" generically.
bool isKeyword(TokenKind kind);

// Returns a human-readable name for a token kind (for error messages and
// debugging). Stable across compiles; not a localised user-facing string.
const char* tokenKindName(TokenKind kind);

struct Token {
    TokenKind kind;
    std::string lexeme;
    int line;
    int column;
};

struct LexError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

// Tokenises `source` into a sequence of Tokens, terminated by an
// EndOfFile token whose lexeme is empty. Throws LexError on unexpected
// characters or unterminated block comments.
std::vector<Token> lex(const std::string& source);
