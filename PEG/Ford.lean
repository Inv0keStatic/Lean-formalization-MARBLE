import PEG.Syntax

set_option autoImplicit false
namespace PEG.Ford
universe u v
variable {α : Type u} {ν : Type v}

inductive Outcome where
  | zero | one | fail
  deriving DecidableEq

inductive Sim (R : Rules α ν) : Expr α ν → Outcome → Prop where
  | epsilon : Sim R .epsilon .zero
  | terminalOne {a} : Sim R (.terminal a) .one
  | terminalFail {a} : Sim R (.terminal a) .fail
  | nonterminal {A o} : Sim R (R A) o → Sim R (.nonterminal A) o
  | seqZero {e f} : Sim R e .zero → Sim R f .zero → Sim R (.seq e f) .zero
  | seqOneLeft {e f s} : Sim R e .one → Sim R f s → s ≠ .fail → Sim R (.seq e f) .one
  | seqOneRight {e f s} : Sim R e s → s ≠ .fail → Sim R f .one → Sim R (.seq e f) .one
  | seqFailLeft {e f} : Sim R e .fail → Sim R (.seq e f) .fail
  | seqFailRight {e f s} : Sim R e s → s ≠ .fail → Sim R f .fail → Sim R (.seq e f) .fail
  | choiceLeft {e f s} : Sim R e s → s ≠ .fail → Sim R (.choice e f) s
  | choiceRight {e f o} : Sim R e .fail → Sim R f o → Sim R (.choice e f) o
  | starOne {e} : Sim R e .one → Sim R (.star e) .one
  | starZero {e} : Sim R e .fail → Sim R (.star e) .zero
  | notFail {e s} : Sim R e s → s ≠ .fail → Sim R (.notAhead e) .fail
  | notZero {e} : Sim R e .fail → Sim R (.notAhead e) .zero
  | wildcardOne : Sim R .wildcard .one
  | wildcardFail : Sim R .wildcard .fail
  | fail : Sim R .fail .fail

inductive WF (R : Rules α ν) : Expr α ν → Prop where
  | epsilon : WF R .epsilon
  | terminal {a} : WF R (.terminal a)
  | nonterminal {A} : WF R (R A) → WF R (.nonterminal A)
  | seq {e f} : WF R e → (Sim R e .zero → WF R f) → WF R (.seq e f)
  | choice {e f} : WF R e → WF R f → WF R (.choice e f)
  | star {e} : WF R e → (¬ Sim R e .zero) → WF R (.star e)
  | notAhead {e} : WF R e → WF R (.notAhead e)
  | wildcard : WF R .wildcard
  | fail : WF R .fail

def AllWF (R : Rules α ν) : Expr α ν → Prop
  | .seq e f | .choice e f => WF R e ∧ WF R f ∧ AllWF R e ∧ AllWF R f
  | .star e | .notAhead e => WF R e ∧ AllWF R e
  | _ => True

def GrammarWF (R : Rules α ν) (e : Expr α ν) : Prop :=
  WF R e ∧ AllWF R e ∧ ∀ A, WF R (R A) ∧ AllWF R (R A)

inductive Before (R : Rules α ν) : Expr α ν → Expr α ν → Prop where
  | nonterminal {A} : Before R (R A) (.nonterminal A)
  | seqLeft {e f} : Before R e (.seq e f)
  | seqRight {e f} : Sim R e .zero → Before R f (.seq e f)
  | choiceLeft {e f} : Before R e (.choice e f)
  | choiceRight {e f} : Before R f (.choice e f)
  | star {e} : Before R e (.star e)
  | notAhead {e} : Before R e (.notAhead e)

theorem WF.accessible {R : Rules α ν} {e : Expr α ν} (h : WF R e) :
    Acc (Before R) e := by
  induction h with
  | epsilon => exact Acc.intro _ (by intro y hy; cases hy)
  | terminal => exact Acc.intro _ (by intro y hy; cases hy)
  | wildcard => exact Acc.intro _ (by intro y hy; cases hy)
  | fail => exact Acc.intro _ (by intro y hy; cases hy)
  | nonterminal _ ih => exact Acc.intro _ (by intro y hy; cases hy; exact ih)
  | seq _ _ ih₁ ih₂ =>
      exact Acc.intro _ (by intro y hy; cases hy with
                           | seqLeft => exact ih₁
                           | seqRight hzero => exact ih₂ hzero)
  | choice _ _ ih₁ ih₂ =>
      exact Acc.intro _ (by intro y hy; cases hy with
                           | choiceLeft => exact ih₁
                           | choiceRight => exact ih₂)
  | star _ _ ih => exact Acc.intro _ (by intro y hy; cases hy; exact ih)
  | notAhead _ ih => exact Acc.intro _ (by intro y hy; cases hy; exact ih)

inductive Path (R : Rules α ν) : Expr α ν → Expr α ν → Prop where
  | edge {e f} : Before R e f → Path R e f
  | cons {e f g} : Before R f g → Path R e f → Path R e g

theorem Path.trans {R : Rules α ν} {e f g : Expr α ν}
    (h : Path R e f) (k : Path R f g) : Path R e g := by
  induction k with
  | edge hfg => exact .cons hfg h
  | cons hfg _ ih => exact .cons hfg ih

theorem accessible_no_cycle {R : Rules α ν} {e : Expr α ν}
    (h : Acc (Before R) e) : ¬ Path R e e := by
  induction h with
  | intro e _ ih =>
      intro loop
      cases loop with
      | edge h => exact ih e h (.edge h)
      | cons h path => exact ih _ h (Path.trans (.edge h) path)

theorem cycle_not_wf {R : Rules α ν} {e : Expr α ν} (loop : Path R e e) :
    ¬ WF R e := fun h => accessible_no_cycle h.accessible loop

end PEG.Ford
