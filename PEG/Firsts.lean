import PEG.Syntax

set_option autoImplicit false

namespace PEG

universe u v

abbrev Symbols (α : Type u) := α → Prop

namespace Symbols

variable {α : Type u}

def Subset (S T : Symbols α) : Prop := ∀ ⦃a⦄, S a → T a
def empty : Symbols α := fun _ => False
def univ : Symbols α := fun _ => True
def singleton (a : α) : Symbols α := fun b => b = a
def union (S T : Symbols α) : Symbols α := fun a => S a ∨ T a

end Symbols

infix:50 " ⊆ₛ " => Symbols.Subset

structure Approx (α : Type u) (ν : Type v) where
  eval : Expr α ν → Symbols α → Symbols α
  mono : ∀ (e) {S T}, S ⊆ₛ T → eval e S ⊆ₛ eval e T

variable {α : Type u} {ν : Type v}

instance : CoeFun (Approx α ν) (fun _ => Expr α ν → Symbols α → Symbols α) :=
  ⟨Approx.eval⟩

def Approx.LE (h k : Approx α ν) : Prop := ∀ e T, h e T ⊆ₛ k e T

infix:50 " ⊑ " => Approx.LE

theorem Approx.ext {h k : Approx α ν}
    (heq : ∀ e T a, h e T a ↔ k e T a) : h = k := by
  cases h with
  | mk he hm =>
    cases k with
    | mk ke km =>
      have hfun : he = ke := by
        funext e T a
        exact propext (heq e T a)
      cases hfun
      rfl

def step (R : Rules α ν) (h : Approx α ν) : Expr α ν → Symbols α → Symbols α
  | .epsilon, T => T
  | .terminal a, _ => Symbols.singleton a
  | .nonterminal A, T => h (R A) T
  | .seq e₁ e₂, T => h e₁ (h e₂ T)
  | .choice e₁ e₂, T => Symbols.union (h e₁ T) (h e₂ T)
  | .star e, T => Symbols.union T (h e T)
  | .notAhead _, T => T
  | .wildcard, _ => Symbols.univ
  | .fail, _ => Symbols.empty

theorem step_continuation_mono (R : Rules α ν) (h : Approx α ν)
    (e : Expr α ν) {S T : Symbols α} (hST : S ⊆ₛ T) :
    step R h e S ⊆ₛ step R h e T := by
  intro a ha
  cases e with
  | epsilon => exact hST ha
  | terminal b => exact ha
  | nonterminal A => exact h.mono (R A) hST ha
  | seq e₁ e₂ => exact h.mono e₁ (h.mono e₂ hST) ha
  | choice e₁ e₂ =>
    exact ha.elim
      (fun hx => Or.inl (h.mono e₁ hST hx))
      (fun hx => Or.inr (h.mono e₂ hST hx))
  | star e =>
    exact ha.elim
      (fun hx => Or.inl (hST hx))
      (fun hx => Or.inr (h.mono e hST hx))
  | notAhead e => exact hST ha
  | wildcard => trivial
  | fail => exact ha

def F (R : Rules α ν) (h : Approx α ν) : Approx α ν where
  eval := step R h
  mono := step_continuation_mono R h

theorem F_mono (R : Rules α ν) {h k : Approx α ν} (hhk : h ⊑ k) :
    F R h ⊑ F R k := by
  intro e T a ha
  cases e with
  | epsilon => exact ha
  | terminal b => exact ha
  | nonterminal A => exact hhk (R A) T ha
  | seq e₁ e₂ => exact k.mono e₁ (hhk e₂ T) (hhk e₁ (h e₂ T) ha)
  | choice e₁ e₂ =>
    exact ha.elim
      (fun hx => Or.inl (hhk e₁ T hx))
      (fun hx => Or.inr (hhk e₂ T hx))
  | star e => exact ha.elim Or.inl (fun hx => Or.inr (hhk e T hx))
  | notAhead e => exact ha
  | wildcard => trivial
  | fail => exact ha

def UpperSolution (R : Rules α ν) (h : Approx α ν) : Prop := F R h ⊑ h

def firstApprox (R : Rules α ν) : Approx α ν where
  eval e T a := ∀ h : Approx α ν, UpperSolution R h → h e T a
  mono := by
    intro e S T hST a ha h hh
    exact h.mono e hST (ha h hh)

theorem firstApprox_le_upper (R : Rules α ν) {h : Approx α ν}
    (hh : UpperSolution R h) : firstApprox R ⊑ h := by
  intro e T a ha
  exact ha h hh

theorem firstApprox_upper (R : Rules α ν) : UpperSolution R (firstApprox R) := by
  intro e T a ha h hh
  exact hh e T (F_mono R (firstApprox_le_upper R hh) e T ha)

theorem firstApprox_fixed (R : Rules α ν) : F R (firstApprox R) = firstApprox R := by
  apply Approx.ext
  intro e T a
  constructor
  · exact fun ha => firstApprox_upper R e T ha
  · exact fun ha => firstApprox_le_upper R (F_mono R (firstApprox_upper R)) e T ha

theorem firstApprox_least (R : Rules α ν) {h : Approx α ν}
    (hh : F R h = h) : firstApprox R ⊑ h := by
  apply firstApprox_le_upper R
  intro e T a ha
  rw [hh] at ha
  exact ha

def firsts' (R : Rules α ν) (e : Expr α ν) (T : Symbols α) : Symbols α :=
  firstApprox R e T

def firsts (R : Rules α ν) (e : Expr α ν) : Symbols α :=
  firsts' R e Symbols.empty

theorem firsts'_unfold (R : Rules α ν) (e : Expr α ν) (T : Symbols α) :
    firsts' R e T = step R (firstApprox R) e T := by
  exact congrArg (fun h : Approx α ν => h e T) (firstApprox_fixed R).symm

theorem firsts'_mono (R : Rules α ν) (e : Expr α ν) {S T : Symbols α}
    (hST : S ⊆ₛ T) : firsts' R e S ⊆ₛ firsts' R e T :=
  (firstApprox R).mono e hST

@[simp] theorem firsts'_epsilon (R : Rules α ν) (T : Symbols α) :
    firsts' R .epsilon T = T := firsts'_unfold R .epsilon T

@[simp] theorem firsts'_terminal (R : Rules α ν) (a : α) (T : Symbols α) :
    firsts' R (.terminal a) T = Symbols.singleton a := firsts'_unfold R (.terminal a) T

/-- Not a simp rule: repeatedly unfolding recursive nonterminals need not terminate. -/
theorem firsts'_nonterminal (R : Rules α ν) (A : ν) (T : Symbols α) :
    firsts' R (.nonterminal A) T = firsts' R (R A) T :=
  firsts'_unfold R (.nonterminal A) T

@[simp] theorem firsts'_seq (R : Rules α ν) (e₁ e₂ : Expr α ν) (T : Symbols α) :
    firsts' R (.seq e₁ e₂) T = firsts' R e₁ (firsts' R e₂ T) :=
  firsts'_unfold R (.seq e₁ e₂) T

@[simp] theorem firsts'_choice (R : Rules α ν) (e₁ e₂ : Expr α ν) (T : Symbols α) :
    firsts' R (.choice e₁ e₂) T = Symbols.union (firsts' R e₁ T) (firsts' R e₂ T) :=
  firsts'_unfold R (.choice e₁ e₂) T

@[simp] theorem firsts'_star (R : Rules α ν) (e : Expr α ν) (T : Symbols α) :
    firsts' R (.star e) T = Symbols.union T (firsts' R e T) :=
  firsts'_unfold R (.star e) T

@[simp] theorem firsts'_notAhead (R : Rules α ν) (e : Expr α ν) (T : Symbols α) :
    firsts' R (.notAhead e) T = T := firsts'_unfold R (.notAhead e) T

@[simp] theorem firsts'_wildcard (R : Rules α ν) (T : Symbols α) :
    firsts' R .wildcard T = Symbols.univ := firsts'_unfold R .wildcard T

@[simp] theorem firsts'_fail (R : Rules α ν) (T : Symbols α) :
    firsts' R .fail T = Symbols.empty := firsts'_unfold R .fail T

end PEG
