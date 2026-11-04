import PEG.Firsts

set_option autoImplicit false
namespace PEG.Raw
universe u v
variable {α : Type u} {ν : Type v}

inductive Name (α : Type u) (ν : Type v) where
  | original (A : ν)
  | derivative (a : α) (e : Expr α ν)
  | delta (a : α) (e : Expr α ν)

def lift : Expr α ν → Expr α (Name α ν)
  | .epsilon => .epsilon
  | .terminal a => .terminal a
  | .nonterminal A => .nonterminal (.original A)
  | .seq e f => .seq (lift e) (lift f)
  | .choice e f => .choice (lift e) (lift f)
  | .star e => .star (lift e)
  | .notAhead e => .notAhead (lift e)
  | .wildcard => .wildcard
  | .fail => .fail

def W : Expr α ν := .star .wildcard
def D (a : α) (e : Expr α ν) : Expr α (Name α ν) := .nonterminal (.derivative a e)
def delta (a : α) (e : Expr α ν) : Expr α (Name α ν) := .nonterminal (.delta a e)

def rules [DecidableEq α] (R : Rules α ν) : Rules α (Name α ν)
  | .original A => lift (R A)
  | .derivative a e => match e with
    | .epsilon => .fail
    | .terminal b => if a = b then .epsilon else .fail
    | .nonterminal A => D a (R A)
    | .seq p q => .choice (.seq (D a p) (lift q)) (.seq (delta a p) (D a q))
    | .choice p q => .choice (D a p) (D a q)
    | .star p => .choice (.seq (D a p) (lift (.star p))) (.seq (delta a p) (D a (.star p)))
    | .notAhead _ => .fail
    | .wildcard => .epsilon
    | .fail => .fail
  | .delta a e => match e with
    | .epsilon => .epsilon
    | .terminal _ => .fail
    | .nonterminal A => delta a (R A)
    | .seq p q => .seq (delta a p) (delta a q)
    | .choice p q => .choice (delta a p) (.seq (delta a (.notAhead p)) (delta a q))
    | .star p => .choice (.seq (delta a p) (delta a (.star p)))
        (.seq (delta a (.notAhead p)) (delta a (.star p)))
    | .notAhead p => .notAhead (D a (.seq p W))
    | .wildcard => .fail
    | .fail => .fail

/-- Finite Booleans for Figure 4. We need-not examine non-feasible branches -/
inductive Nu (R : Rules α ν) : Expr α ν → Bool → Prop where
  | epsilon : Nu R .epsilon true
  | terminal {a} : Nu R (.terminal a) false
  | wildcard : Nu R .wildcard false
  | fail : Nu R .fail false
  | star {e} : Nu R (.star e) true
  | nonterminal {A b} : Nu R (R A) b → Nu R (.nonterminal A) b
  | seqTrue {e f} : Nu R e true → Nu R f true → Nu R (.seq e f) true
  | seqFalseLeft {e f} : Nu R e false → Nu R (.seq e f) false
  | seqFalseRight {e f} : Nu R f false → Nu R (.seq e f) false
  | choiceTrueLeft {e f} : Nu R e true → Nu R (.choice e f) true
  | choiceTrueRight {e f} : Nu R f true → Nu R (.choice e f) true
  | choiceFalse {e f} : Nu R e false → Nu R f false → Nu R (.choice e f) false
  | notAhead {e b} : Nu R e b → Nu R (.notAhead e) (!b)

def NuEquations (R : Rules α ν) (n : Expr α ν → Bool) : Prop :=
  (n .epsilon = true) ∧ (∀ a, n (.terminal a) = false) ∧
  (n .wildcard = false) ∧ (n .fail = false) ∧ (∀ e, n (.star e) = true) ∧
  (∀ A, n (.nonterminal A) = n (R A)) ∧
  (∀ e f, n (.seq e f) = (n e && n f)) ∧
  (∀ e f, n (.choice e f) = (n e || n f)) ∧
  (∀ e, n (.notAhead e) = !n e)

theorem Nu.agrees {R : Rules α ν} {e : Expr α ν} {b : Bool}
    (h : Nu R e b) {n : Expr α ν → Bool} (hn : NuEquations R n) : n e = b := by
  rcases hn with ⟨he, ht, hw, hf, hs, hr, hseq, hc, hnot⟩
  induction h with
  | epsilon => exact he
  | terminal => exact ht _
  | wildcard => exact hw
  | fail => exact hf
  | star => exact hs _
  | nonterminal _ ih => exact (hr _).trans ih
  | seqTrue _ _ ih₁ ih₂ => simp only [hseq, ih₁, ih₂]; rfl
  | seqFalseLeft _ ih => simp only [hseq, ih, Bool.false_and]
  | seqFalseRight _ ih => simp only [hseq, ih, Bool.and_false]
  | choiceTrueLeft _ ih => simp only [hc, ih, Bool.true_or]
  | choiceTrueRight _ ih => simp only [hc, ih, Bool.or_true]
  | choiceFalse _ _ ih₁ ih₂ => simp only [hc, ih₁, ih₂]; rfl
  | notAhead _ ih => simp only [hnot, ih]

theorem Nu.lift [DecidableEq α] {R : Rules α ν} {e : Expr α ν} {b : Bool}
    (h : Nu R e b) : Nu (rules R) (Raw.lift e) b := by
  induction h with
  | epsilon => exact .epsilon
  | terminal => exact .terminal
  | wildcard => exact .wildcard
  | fail => exact .fail
  | star => exact .star
  | nonterminal _ ih => exact .nonterminal ih
  | seqTrue _ _ ih₁ ih₂ => exact .seqTrue ih₁ ih₂
  | seqFalseLeft _ ih => exact .seqFalseLeft ih
  | seqFalseRight _ ih => exact .seqFalseRight ih
  | choiceTrueLeft _ ih => exact .choiceTrueLeft ih
  | choiceTrueRight _ ih => exact .choiceTrueRight ih
  | choiceFalse _ _ ih₁ ih₂ => exact .choiceFalse ih₁ ih₂
  | notAhead _ ih => exact .notAhead ih

section Lemmas
variable [DecidableEq α] {R : Rules α ν} {a : α} {e f : Expr α ν}

theorem nu_D_seq_left (he : Nu (rules R) (D a e) true) (hf : Nu R f true) :
    Nu (rules R) (D a (.seq e f)) true :=
  .nonterminal (.choiceTrueLeft (.seqTrue he hf.lift))

theorem nu_D_seq_right (he : Nu (rules R) (delta a e) true)
    (hf : Nu (rules R) (D a f) true) : Nu (rules R) (D a (.seq e f)) true :=
  .nonterminal (.choiceTrueRight (.seqTrue he hf))

theorem nu_D_choice_left (h : Nu (rules R) (D a e) true) :
    Nu (rules R) (D a (.choice e f)) true := .nonterminal (.choiceTrueLeft h)

theorem nu_D_choice_right (h : Nu (rules R) (D a f) true) :
    Nu (rules R) (D a (.choice e f)) true := .nonterminal (.choiceTrueRight h)

theorem nu_D_terminal : Nu (rules R) (D a (.terminal a)) true := by
  apply Nu.nonterminal
  simpa [rules] using (Nu.epsilon : Nu (rules R) .epsilon true)

theorem nu_D_nonterminal {A : ν} (h : Nu (rules R) (D a (R A)) true) :
    Nu (rules R) (D a (.nonterminal A)) true := .nonterminal h

theorem nu_delta_nonterminal {A : ν} (h : Nu (rules R) (delta a (R A)) true) :
    Nu (rules R) (delta a (.nonterminal A)) true := .nonterminal h

end Lemmas

end PEG.Raw
