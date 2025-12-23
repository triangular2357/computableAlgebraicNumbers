import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace CPoly

private def _noLeadingZero {R : Type*} [Ring R] : List R → Prop
  | []     => True
  | x :: _ => x ≠ 0

def noTailingZero {R : Type*} [Ring R] (i : List R) : Prop :=
  _noLeadingZero i.reverse

end CPoly

structure CPoly (R : Type*) [Ring R] where
  coefs : List R -- `[c₀,c₁,c₂,...,cₙ]` and then `∑ Xⁱcᵢ`
  condition : CPoly.noTailingZero coefs

namespace CPoly

private def _removeLeadingZeros {R : Type*} [Ring R] [DecidableEq R] : List R → List R
  | []      => []
  | x :: xs => if x = 0 then _removeLeadingZeros xs else x :: xs

private lemma _noLeadingZero_removeLeadingZeros {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : _noLeadingZero (_removeLeadingZeros l) := by
  induction l with
  | nil => trivial
  | cons x xs ih =>
    unfold _removeLeadingZeros
    rw [apply_ite _noLeadingZero]
    by_cases h : x = 0
    · rwa [if_pos h]
    · rwa [if_neg h]

def removeTailingZeros {R : Type*} [Ring R] [DecidableEq R]
    (l : List R) : CPoly R :=
  ⟨(_removeLeadingZeros l.reverse).reverse, by
    unfold noTailingZero
    rw [List.reverse_reverse]
    apply _noLeadingZero_removeLeadingZeros
  ⟩

def list_add (R : Type*) [Ring R] : List R → List R → List R
  | []     , bs      => bs
  | as     , []      => as
  | a :: as, b :: bs => (a+b) :: (list_add R as bs)

def list_smul (R : Type*) [Ring R] : R → List R → List R
  | _,      [] => []
  | r, a :: as => (r*a) :: (list_smul R r as)

def list_mul (R : Type*) [Ring R] : List R → List R → List R
  | []     , _  => []
  | a :: as, bs => list_add R (list_smul R a bs) (0 :: list_mul R as bs)

 --semiring so Polys in ℕ work idk if this is useful
def list_eval {R : Type*} [Semiring R] : List R → R → R
  | [] => 0
  | a :: as => fun r ↦ a + r * list_eval as r


def ℤdiv : ℤ  → List ℤ → List ℤ
  | _,      [] => []
  | r, a :: as => (a/r) :: (ℤdiv r as)

def ℚdiv : ℚ  → List ℚ → List ℚ
  | _,      [] => []
  | r, a :: as => (a / r) :: (ℚdiv r as)

def ℤgcd : List ℤ → ℕ
  | [] => 0
  | r::[]=> r.natAbs
  | r::rs=> r.gcd (ℤgcd rs)

def ℚlcd : List ℚ → ℕ --least common denominator
  | [] => 1
  | r::[]=> r.den
  | r::rs=> r.den.lcm (ℚlcd rs)

def ℤnormalize (i : List ℤ):List ℤ :=
  let i' := (removeTailingZeros i).coefs --maybe make a new function only on lists?
  --last element must not be zero otherwise it breaks because then getLastD returns 0
  ℤdiv ((i'.getLastD 1).sign * ℤgcd i') i'

def toNormℤPoly (i : List ℤ):CPoly ℤ:=
  removeTailingZeros (ℤnormalize i)

def ℚnormalize (i : List ℚ):List ℚ := ℚdiv (i.getLastD 1) i

def toNormℚPoly (i : List ℚ):CPoly ℚ:=
  removeTailingZeros (ℚnormalize i)

def ℤℚconvert : List ℤ → List ℚ
  | [] => []
  | z::zs=> z :: ℤℚconvert zs

def ℚℤconvert (i : List ℚ) : List ℤ :=
  let rec _ℚℤmulConvert : ℤ → List ℚ → List ℤ
    | _, [] => []
    | x,z::zs=> (z*x).num / (z*x).den  :: _ℚℤmulConvert x zs
  _ℚℤmulConvert (ℚlcd i) i




#eval list_mul ℤ [1]           [3]
#eval list_mul ℤ [1,4]         [3]
#eval list_mul ℤ [1,4]       [3,4]
#eval list_mul ℤ [1,2,3,4]   [5,7]
#eval list_add ℤ [1,4]         [3]
#eval list_smul ℤ 2          [1,4]
#eval list_eval [4,2] 2
#eval list_eval [2,3,-1] (-1)
#eval list_eval [0,6] 2
#eval list_eval [0,0,0,0,1] 2

#eval ℤdiv   2 [4,2,0,-1,1,4]
#eval ℤnormalize   [4,2,0,4]
#eval ℤnormalize   [4,2,0]
#eval ℤnormalize   [-6]
#eval ℚdiv   2 [4,2,0,-1,1,4]
#eval ℚnormalize [4,2,0,-1,1,4]
#eval ℚℤconvert (ℚnormalize [4,2,0,-1,1,4])
#eval ℤℚconvert [4,2,0,-1,1,4]

end CPoly
