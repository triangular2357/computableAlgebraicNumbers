import Mathlib
import ComputableAlgebraicNumbers.CPoly

def find_eliminator {n : ℕ} : Vector (Vector ℚ n) (n + 1) → Vector ℚ (n + 1) := sorry

def reduce_mod_Monic (f : CPoly (CPoly ℚ)) (p q : CPoly ℚ) (hp : p.Monic) (hq : q.Monic) :
  CPoly (CPoly ℚ) :=
  (f.modByMonic (p.liftTo (CPoly ℚ)) (CPoly.Monic_liftTo hp)).map'
    fun g : CPoly ℚ ↦ g.modByMonic q hq

def reduce_mod (f : CPoly (CPoly ℚ)) (p q : CPoly ℚ) : CPoly (CPoly ℚ) :=
  if hp : p = 0 then 0 else if hq : q = 0 then 0 else reduce_mod_Monic f
  (normalize p) (normalize q) (CPoly.Monic_normalize p hp) (CPoly.Monic_normalize q hq)

def poly_to_coefs {n m : ℕ} (f : CPoly (CPoly ℚ)) : Vector ℚ (n * m) :=
  Vector.ofFn ((fun (⟨i, _⟩, ⟨j, _⟩) ↦ (f.toPolynomial.coeff i).toPolynomial.coeff j) ∘
  finProdFinEquiv.invFun)

def coefs_to_poly {n : ℕ} (v : Vector ℚ n) : CPoly ℚ :=
  CPoly.toCPoly v.toList

def poly_add (p q : CPoly ℚ) :=
  coefs_to_poly (find_eliminator (Vector.ofFn fun k : Fin (p.natDegree * q.natDegree + 1) ↦
  poly_to_coefs <| reduce_mod ((CPoly.X + CPoly.const CPoly.X) ^ k.val) p q))

def poly_mul (p q : CPoly ℚ) :=
  coefs_to_poly (find_eliminator (Vector.ofFn fun k : Fin (p.natDegree * q.natDegree + 1) ↦
  poly_to_coefs <| reduce_mod ((CPoly.X * CPoly.const CPoly.X) ^ k.val) p q))
