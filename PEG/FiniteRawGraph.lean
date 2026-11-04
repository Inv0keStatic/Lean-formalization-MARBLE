import PEG.Counterexamples

set_option autoImplicit false
namespace PEG.Counterexamples.FiniteGraph
open Ford Raw

inductive Node where
  | Y | Q | H | J | X | S
  deriving DecidableEq, Repr

abbrev GExpr := Expr Char Node
def bStar : GExpr := .star (.terminal 'b')
def graphRules : Rules Char Node
  | .Y => .choice (.seq .fail bStar) (.seq .fail (.nonterminal .Y))
  | .Q => .choice (.seq .epsilon W) (.seq .fail (.nonterminal .Q))
  | .H => .choice (.seq .fail W) (.seq .fail (.nonterminal .Q))
  | .J => .notAhead (.nonterminal .H)
  | .X => .choice (.seq .fail (.nonterminal .X))
      (.seq (.nonterminal .J) (.nonterminal .X))
  | .S => .choice (.seq (.nonterminal .Y) (.terminal 'a'))
      (.seq (.nonterminal .X) .epsilon)

def meaning : Node → Name Char Empty
  | .Y => .derivative 'a' B
  | .Q => .derivative 'a' W
  | .H => .derivative 'a' (.seq (.terminal 'b') W)
  | .J => .delta 'a' (.notAhead (.terminal 'b'))
  | .X => .delta 'a' B
  | .S => .derivative 'a' StarSource

def lowerCall : Name Char Empty → Option GExpr
  | .original A => nomatch A
  | .derivative 'a' (.star (.terminal 'b')) => some (.nonterminal .Y)
  | .derivative 'a' (.star .wildcard) => some (.nonterminal .Q)
  | .derivative 'a' (.seq (.terminal 'b') (.star .wildcard)) => some (.nonterminal .H)
  | .delta 'a' (.notAhead (.terminal 'b')) => some (.nonterminal .J)
  | .delta 'a' (.star (.terminal 'b')) => some (.nonterminal .X)
  | .derivative 'a' (.seq (.star (.terminal 'b')) (.terminal 'a')) => some (.nonterminal .S)
  | .derivative _ .epsilon => some .fail
  | .derivative a (.terminal b) => some (if a = b then .epsilon else .fail)
  | .derivative _ .wildcard => some .epsilon
  | .derivative _ .fail => some .fail
  | .delta _ .epsilon => some .epsilon
  | .delta _ (.terminal _) | .delta _ .wildcard | .delta _ .fail => some .fail
  | _ => none

def lower : Expr Char (Name Char Empty) → Option GExpr
  | .epsilon => some .epsilon
  | .terminal a => some (.terminal a)
  | .nonterminal A => lowerCall A
  | .seq e f => return .seq (← lower e) (← lower f)
  | .choice e f => return .choice (← lower e) (← lower f)
  | .star e => return .star (← lower e)
  | .notAhead e => return .notAhead (← lower e)
  | .wildcard => some .wildcard
  | .fail => some .fail

theorem names_match (n : Node) : lowerCall (meaning n) = some (.nonterminal n) := by
  cases n <;> rfl

theorem equations_match (n : Node) :
    lower (Raw.rules baseRules (meaning n)) = some (graphRules n) := by
  cases n <;> rfl

theorem h_wf : WF graphRules (.nonterminal .H) :=
  .nonterminal (.choice (.seq .fail (by intro h; cases h))
    (.seq .fail (by intro h; cases h)))

theorem y_wf : WF graphRules (.nonterminal .Y) :=
  .nonterminal (.choice (.seq .fail (by intro h; cases h))
    (.seq .fail (by intro h; cases h)))

theorem j_wf : WF graphRules (.nonterminal .J) := .nonterminal (.notAhead h_wf)

theorem j_zero : Sim graphRules (.nonterminal .J) .zero :=
  .nonterminal (.notZero (.nonterminal
    (.choiceRight (.seqFailLeft .fail) (.seqFailLeft .fail))))

theorem x_cycle : Ford.Path graphRules (.nonterminal .X) (.nonterminal .X) :=
  .cons .nonterminal (.cons .choiceRight (.edge (.seqRight j_zero)))

theorem x_not_wf : ¬ WF graphRules (.nonterminal .X) := cycle_not_wf x_cycle

theorem s_not_wf : ¬ WF graphRules (.nonterminal .S) := by
  intro h
  cases h with
  | nonterminal h =>
      cases h with
      | choice _ h =>
          cases h with
          | seq hx _ => exact x_not_wf hx

theorem counterexample1_finite :
    GrammarWF baseRules StarSource ∧
    (∀ n, lower (Raw.rules baseRules (meaning n)) = some (graphRules n)) ∧
    ¬ WF graphRules (.nonterminal .S) :=
  ⟨star_source_grammar_wf, equations_match, s_not_wf⟩

end PEG.Counterexamples.FiniteGraph
