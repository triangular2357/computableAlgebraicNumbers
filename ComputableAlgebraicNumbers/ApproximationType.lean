--import Mathlib.Tactic.TypeStar
import Mathlib

class ApproximationType (A : Type*) where
  improve : A → A

namespace ApproximationType

class isExact {A : Type*} [ApproximationType A] (p : A → Prop) where
  reachable : ∀ a, ∃ n, p (improve^[n] a)
  stable : ∀ a, p a → p (improve a)
  decidable : DecidablePred p := by infer_instance

lemma isExact_le_stable {A : Type*} [ApproximationType A] (p : A → Prop) [hp : isExact p]
  {n m : ℕ} (h : n ≤ m) : ∀ a, p (improve^[n] a) → p (improve^[m] a) := by
    intro a hn
    induction h with
    | refl => exact hn
    | step _ ih =>
      rw [Function.iterate_succ_apply']
      apply hp.stable _ ih

instance {A : Type*} [ApproximationType A] {p q : A → Prop} [hp : isExact p] [hq : isExact q] :
  isExact (fun a ↦ p a ∧ q a) where
  reachable := fun a ↦ Exists.intro (max (hp.reachable a).choose (hq.reachable a).choose)
    ⟨isExact_le_stable p (le_max_left ..) a (Exists.choose_spec (hp.reachable a)),
    isExact_le_stable q (le_max_right ..) a (Exists.choose_spec (hq.reachable a))⟩
  stable := fun a h ↦ ⟨hp.stable a h.left, hq.stable a h.right⟩
  decidable := fun a ↦ let := hp.decidable a; let := hq.decidable a; inferInstance

instance {A : Type*} [ApproximationType A] (p : A → Prop) [hp : isExact p] (a : A) :
  Decidable (p a) := hp.decidable a

set_option pp.proofs true in
private lemma termination_lemma (A : Type*) [ApproximationType A] (p : A → Prop)
  (hp : isExact p) (a : A) (hnp : ¬p a) :
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

instance {A B : Type*} [ApproximationType A] [ApproximationType B] : ApproximationType (A × B) where
  improve := fun (a, b) ↦ (improve a, improve b)

lemma iterate_improve_prod {A B : Type*} [ApproximationType A] [ApproximationType B]
  (a : A) (b : B) (n : ℕ) : improve^[n] (a, b) = (improve^[n] a, improve^[n] b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact congr_arg improve ih

instance {A B : Type*} [ApproximationType A] [ApproximationType B] (p : A → Prop)
  [hp : isExact p] : isExact (fun ((a, _) : A × B) ↦ p a) where
    reachable := fun (a, b) ↦ ⟨(hp.reachable a).choose,
      iterate_improve_prod a b _ ▸ (hp.reachable a).choose_spec⟩
    stable := fun (a, _) ↦ hp.stable a
    decidable := fun (a, _) ↦ hp.decidable a

instance {A B : Type*} [ApproximationType A] [ApproximationType B] (p : B → Prop)
  [hp : isExact p] : isExact (fun ((_, b) : A × B) ↦ p b) where
    reachable := fun (a, b) ↦ ⟨(hp.reachable b).choose,
      iterate_improve_prod a b _ ▸ (hp.reachable b).choose_spec⟩
    stable := fun (_, b) ↦ hp.stable b
    decidable := fun (_, b) ↦ hp.decidable b

end ApproximationType
