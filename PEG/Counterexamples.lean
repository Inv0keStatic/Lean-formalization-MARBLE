import PEG.Ford
import PEG.RawDerivative

set_option autoImplicit false
namespace PEG.Counterexamples
open Ford Raw

abbrev E := Expr Char Empty
def baseRules : Rules Char Empty := fun A => nomatch A
def R₁ := Raw.rules baseRules
def R₂ := Raw.rules R₁
def P : E := .choice .epsilon (.terminal 'a')
def Z : E := .notAhead .wildcard
def EndTest : E := .seq P Z
def FollowB : E := .seq P (.terminal 'b')
def B : E := .star (.terminal 'b')
def StarSource : E := .seq B (.terminal 'a')

theorem p_wf : WF baseRules P := .choice .epsilon .terminal
theorem z_wf : WF baseRules Z := .notAhead .wildcard
theorem w_wf : WF baseRules (W : E) := .star .wildcard (by intro h; cases h)
theorem b_wf : WF baseRules B := .star .terminal (by intro h; cases h)
theorem end_wf : WF baseRules EndTest := .seq p_wf (fun _ => z_wf)
theorem follow_wf : WF baseRules FollowB := .seq p_wf (fun _ => .terminal)
theorem star_source_wf : WF baseRules StarSource := .seq b_wf (fun _ => .terminal)

theorem p_grammar_wf : GrammarWF baseRules P :=
  ⟨p_wf, ⟨.epsilon, .terminal, trivial, trivial⟩, fun A => nomatch A⟩
theorem end_grammar_wf : GrammarWF baseRules EndTest :=
  ⟨end_wf, ⟨p_wf, z_wf, p_grammar_wf.2.1, .wildcard, trivial⟩, fun A => nomatch A⟩
theorem follow_grammar_wf : GrammarWF baseRules FollowB :=
  ⟨follow_wf, ⟨p_wf, .terminal, p_grammar_wf.2.1, trivial⟩, fun A => nomatch A⟩
theorem star_source_grammar_wf : GrammarWF baseRules StarSource :=
  ⟨star_source_wf, ⟨b_wf, .terminal, ⟨.terminal, trivial⟩, trivial⟩, fun A => nomatch A⟩

theorem wrapped_grammar_wf {e : E} (h : GrammarWF baseRules e) :
    GrammarWF baseRules (.seq e W) :=
  ⟨.seq h.1 (fun _ => w_wf), ⟨h.1, w_wf, h.2.1, .wildcard, trivial⟩, h.2.2⟩

theorem epsilon_result {α ν : Type} {R : Rules α ν} {w : List α} {out}
    (h : Parse R .epsilon w out) : out = some w := by cases h; rfl

theorem p_result {w : List Char} {out} (h : Parse baseRules P w out) : out = some w := by
  cases h with
  | choiceLeft h => exact epsilon_result h
  | choiceRight h _ => cases epsilon_result h

theorem p_leaves_input (w : List Char) : Parse baseRules P w (some w) :=
  Parse.choiceLeft (x := []) Parse.epsilon

theorem p_not_accepts_a : ¬ FullLanguage baseRules P ['a'] := by
  intro h
  cases p_result h

theorem derivative_p_empty : FullLanguage R₁ (D 'a' P) [] :=
  .nonterminal (.choiceRight (.nonterminal .fail) (.nonterminal .epsilon))

theorem counterexample3 :
    GrammarWF baseRules P ∧
    ¬ (Parse baseRules P ['a'] (some []) ↔ Parse R₁ (D 'a' P) [] (some [])) :=
  ⟨p_grammar_wf, fun h => p_not_accepts_a (h.mpr derivative_p_empty)⟩

theorem p_firsts : firsts baseRules P 'a' := by
  simp [P, firsts, Symbols.union, Symbols.empty, Symbols.singleton]

theorem derivative_p_nullable : Nu R₁ (D 'a' P) true :=
  nu_D_choice_right nu_D_terminal

theorem derivative_p_firsts_empty (c : Char) : ¬ firsts R₁ (D 'a' P) c := by
  simp [firsts, D, firsts'_nonterminal, R₁, rules, P, Symbols.union, Symbols.empty]

mutual
inductive Gen : {ν : Type} → Rules Char ν → Expr Char ν → Option (List Char) → Prop where
  | enough {ν : Type} {R : Rules Char ν} {e out} :
      GenFrom R e Symbols.empty out → Gen R e out
  | continue {ν : Type} {R : Rules Char ν} {e out} :
      GenFrom R e (firsts R e) out → Gen R e out
inductive GenFrom : {ν : Type} → Rules Char ν → Expr Char ν →
    Symbols Char → Option (List Char) → Prop where
  | emptySuccess {ν : Type} {R : Rules Char ν} {e T} :
      (∀ c, ¬ T c) → Nu R e true → GenFrom R e T (some [])
  | emptyFailure {ν : Type} {R : Rules Char ν} {e T} :
      (∀ c, ¬ T c) → Nu R e false → GenFrom R e T none
  | pickSuccess {ν : Type} {R : Rules Char ν} {e T a w} :
      T a → Gen (rules R) (D a e) (some w) → GenFrom R e T (some (a :: w))
  | pickFailure {ν : Type} {R : Rules Char ν} {e T a out} :
      T a → Gen (rules R) (D a e) none →
      GenFrom R e (fun c => T c ∧ c ≠ a) out → GenFrom R e T out
end

theorem generates_a : Gen baseRules P (some ['a']) :=
  .continue (.pickSuccess p_firsts
    (.continue (.emptySuccess derivative_p_firsts_empty derivative_p_nullable)))

theorem counterexample4 :
    GrammarWF baseRules P ∧ Gen baseRules P (some ['a']) ∧ ¬ FullLanguage baseRules P ['a'] :=
  ⟨p_grammar_wf, generates_a, p_not_accepts_a⟩

theorem end_rejects : Parse baseRules (.seq EndTest W) ['a'] none :=
  .seqFail (.seqStep (x := []) (p_leaves_input ['a']) (.notFail .wildcard))

theorem follow_rejects : Parse baseRules (.seq FollowB W) ['a', 'b'] none :=
  .seqFail (.seqStep (x := []) (p_leaves_input ['a', 'b']) (.terminalMismatch (by decide)))

theorem seq_after_p {f : E} {w : List Char} {out}
    (h : Parse baseRules (.seq P f) w out) : Parse baseRules f w out := by
  cases h with
  | seqFail h => cases p_result h
  | seqStep h hf => exact Option.some.inj (p_result h) ▸ hf

theorem seq_success_left {α ν : Type} {R : Rules α ν} {e f : Expr α ν}
    {w y : List α} (h : Parse R (.seq e f) w (some y)) :
    ∃ rest, Parse R e w (some rest) := by
  cases h with
  | seqStep h _ => exact ⟨_, h⟩

theorem end_result {out} (h : Parse baseRules EndTest ['a'] out) : out = none := by
  have hz := seq_after_p h
  cases hz with
  | notFail _ => rfl
  | notSuccess impossible => cases impossible

theorem follow_result {out} (h : Parse baseRules FollowB ['a', 'b'] out) : out = none := by
  have hb := seq_after_p h
  cases hb with
  | terminalMismatch _ => rfl

theorem end_not_accepts : ¬ FullLanguage baseRules (.seq EndTest W) ['a'] := by
  intro h
  obtain ⟨_, h⟩ := seq_success_left h
  cases end_result h

theorem follow_not_accepts : ¬ FullLanguage baseRules (.seq FollowB W) ['a', 'b'] := by
  intro h
  obtain ⟨_, h⟩ := seq_success_left h
  cases follow_result h

theorem end_derivative_nullable : Nu R₁ (D 'a' (.seq EndTest W)) true :=
  nu_D_seq_left (nu_D_seq_left derivative_p_nullable (.notAhead .wildcard)) .star

theorem counterexample2_end :
    GrammarWF baseRules EndTest ∧
    ¬ FullLanguage baseRules (.seq EndTest W) ['a'] ∧
    Nu R₁ (D 'a' (.seq EndTest W)) true :=
  ⟨end_grammar_wf, end_not_accepts, end_derivative_nullable⟩

theorem delta_derivative_p_nullable : Nu R₂ (delta 'b' (D 'a' P)) true := by
  apply nu_delta_nonterminal
  apply Nu.nonterminal
  apply Nu.choiceTrueRight
  apply Nu.seqTrue
  · apply Nu.nonterminal
    apply Nu.notAhead (b := false)
    apply Nu.nonterminal
    apply Nu.choiceFalse
    · apply Nu.seqFalseLeft
      apply Nu.nonterminal
      exact .nonterminal .fail
    · apply Nu.seqFalseLeft
      apply Nu.nonterminal
      exact .nonterminal .fail
  · apply nu_delta_nonterminal
    exact .nonterminal .epsilon

theorem follow_two_derivatives_nullable :
    Nu R₂ (D 'b' (D 'a' (.seq FollowB W))) true := by
  apply nu_D_nonterminal
  apply nu_D_choice_left
  apply nu_D_seq_left
  · apply nu_D_nonterminal
    apply nu_D_choice_left
    exact nu_D_seq_right delta_derivative_p_nullable nu_D_terminal
  · exact .star

theorem counterexample2_follow :
    GrammarWF baseRules FollowB ∧
    ¬ FullLanguage baseRules (.seq FollowB W) ['a', 'b'] ∧
    Nu R₂ (D 'b' (D 'a' (.seq FollowB W))) true :=
  ⟨follow_grammar_wf, follow_not_accepts, follow_two_derivatives_nullable⟩

theorem j_zero : Sim R₁ (delta 'a' (.notAhead (.terminal 'b') : E)) .zero :=
  .nonterminal (.notZero (.nonterminal
    (.choiceRight (.seqFailLeft (.nonterminal .fail))
      (.seqFailLeft (.nonterminal .fail)))))

theorem x_cycle : Ford.Path R₁ (delta 'a' B) (delta 'a' B) :=
  .cons .nonterminal (.cons .choiceRight (.edge (.seqRight j_zero)))

theorem x_not_wf : ¬ WF R₁ (delta 'a' B) := cycle_not_wf x_cycle

theorem star_derivative_not_wf : ¬ WF R₁ (D 'a' StarSource) := by
  intro h
  cases h with
  | nonterminal h =>
      cases h with
      | choice _ h =>
          cases h with
          | seq hx _ => exact x_not_wf hx

theorem counterexample1 :
    GrammarWF baseRules StarSource ∧ ¬ WF R₁ (D 'a' StarSource) :=
  ⟨star_source_grammar_wf, star_derivative_not_wf⟩

theorem conjecture1_false :
    ¬ (∀ e : E, GrammarWF baseRules e → ∀ a : Char, WF R₁ (D a e)) :=
  fun h => star_derivative_not_wf (h StarSource star_source_grammar_wf 'a')

theorem conjecture2_end_false :
    ¬ (FullLanguage baseRules (.seq EndTest W) ['a'] ↔
       Nu R₁ (D 'a' (.seq EndTest W)) true) :=
  fun h => end_not_accepts (h.mpr end_derivative_nullable)

theorem conjecture2_follow_false :
    ¬ (FullLanguage baseRules (.seq FollowB W) ['a', 'b'] ↔
       Nu R₂ (D 'b' (D 'a' (.seq FollowB W))) true) :=
  fun h => follow_not_accepts (h.mpr follow_two_derivatives_nullable)

theorem conjecture2_end_any_solution {n : Expr Char (Name Char Empty) → Bool}
    (hn : NuEquations R₁ n) :
    ¬ (FullLanguage baseRules (.seq EndTest W) ['a'] ↔
       n (D 'a' (.seq EndTest W)) = true) :=
  fun h => end_not_accepts (h.mpr (end_derivative_nullable.agrees hn))

theorem conjecture2_follow_any_solution
    {n : Expr Char (Name Char (Name Char Empty)) → Bool} (hn : NuEquations R₂ n) :
    ¬ (FullLanguage baseRules (.seq FollowB W) ['a', 'b'] ↔
       n (D 'b' (D 'a' (.seq FollowB W))) = true) :=
  fun h => follow_not_accepts (h.mpr (follow_two_derivatives_nullable.agrees hn))

theorem conjecture4_false :
    ¬ (Gen baseRules P (some ['a']) ↔ FullLanguage baseRules P ['a']) :=
  fun h => p_not_accepts_a (h.mp generates_a)

end PEG.Counterexamples
