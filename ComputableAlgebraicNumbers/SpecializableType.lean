--import Mathlib.Tactic.TypeStar
import Mathlib

class ApproximationType (A : Type*) where
  improve : A → A

namespace ApproximationType

class isExact {A : Type*} [ApproximationType A] (p : A → Prop) where
  reachable : ∀ a, ∃ n, p (improve^[n] a)
  stable : ∀ a, p a → p (improve a)
  decidable : DecidablePred p := by infer_instance

instance {A : Type*} [ApproximationType A] (p : A → Prop) [hp : isExact p] (a : A) :
  Decidable (p a) := hp.decidable a

set_option pp.proofs true in
private lemma termination_lemma (A : Type*) [ApproximationType A] (p : A → Prop)
  [hp : isExact p] (a : A) (hnp : ¬p a) :
  Nat.find (hp.reachable (improve a)) < Nat.find (hp.reachable a) := by
    let n := Nat.find (hp.reachable a)
    have hn : n = Nat.find (hp.reachable a) := rfl
    apply (Nat.find_lt_iff _ n).2
    have : n ≠ 0 := fun h' ↦ hnp ((Nat.find_eq_zero _).1 h')
    use n - 1, Nat.sub_one_lt this
    have := Nat.succ_pred_eq_of_ne_zero this ▸ hn ▸ Nat.find_spec (hp.reachable a)
    assumption

def approximate {A : Type*} [ApproximationType A] (p : A → Prop)
  [hp : isExact p] (a : A) : A :=
    if p a then a else approximate p (improve a)
  termination_by Nat.find (hp.reachable a)
  decreasing_by apply termination_lemma; assumption

lemma approximate_spec {A : Type*} [ApproximationType A] (p : A → Prop)
  [hp : isExact p] (a : A) : p (approximate p a) := by
    unfold approximate
    rw [apply_ite p]
    apply ite_then_self.2
    intro
    exact approximate_spec p (improve a)
  termination_by Nat.find (hp.reachable a)
  decreasing_by apply termination_lemma; assumption

end ApproximationType
