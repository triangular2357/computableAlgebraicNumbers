import Mathlib
--import Mathlib.Algebra.Ring.Defs

@[ext] structure Polynom (R : Type*) [Ring R] [DecidableEq R] where
  coeficients : List R
--TODO disallow tailing zeros
--TODO use this structure
--TODO in which order should polynomial be saved right now its `[c₀,c₁,c₂,...,cₙ]`


-- TODO is underscore a good marker for functions which should only be used internally
-- this method should only be used on reversed polynomials (or to factor X's out)
private def _removeLeadingZeros (R : Type*) [Ring R] [DecidableEq R] : List R → List R
  | [] => []
  | z::zs => if z=0 then (_removeLeadingZeros R zs) else z::zs

def removeTailingZeros (R : Type*) [Ring R] [DecidableEq R] (i : List R) : List R :=
  (_removeLeadingZeros R i.reverse).reverse

def add (R : Type*) [Ring R] : List R → List R → List R
  | []     , bs      => bs
  | as     , []      => as
  | a :: as, b :: bs => (a+b) :: (add R as bs)

def smul (R : Type*) [Ring R] : R → List R → List R
  | _,      [] => []
  | r, a :: as => (r*a) :: (smul R r as)

def ℤdiv : ℤ  → List ℤ → List ℤ
  | _,      [] => []
  | r, a :: as => (a/r) :: (ℤdiv r as)

def ℚdiv : ℚ  → List ℚ → List ℚ
  | _,      [] => []
  | r, a :: as => (a / r) :: (ℚdiv r as)

def mul (R : Type*) [Ring R] : List R → List R → List R
  | _      , []       => []
  | []     , _        => []
  | a :: [], b :: []  => [(a*b)]
  | a :: as, b :: bs  => (a*b) :: add R (add R (smul R b as) (smul R a bs)) (0 :: mul R as bs)

def ℤgcd : List ℤ → ℕ
  | [] => 0
  | r::[]=> r.natAbs
  | r::rs=> r.gcd (ℤgcd rs)

def ℚlcd : List ℚ → ℕ --least common denominator
  | [] => 1
  | r::[]=> r.den
  | r::rs=> r.den.lcm (ℚlcd rs)

def ℤnormalize (i : List ℤ):List ℤ :=
  let i' := removeTailingZeros ℤ i --last element must not be zero otherwise it breaks
  ℤdiv ((i'.getLastD 1).sign * ℤgcd i') i'

def ℚnormalize (i : List ℚ):List ℚ := ℚdiv (i.getLastD 1) i

def ℤℚconvert : List ℤ → List ℚ
  | [] => []
  | z::zs=> z :: ℤℚconvert zs

private def _ℚℤmulConvert : ℤ → List ℚ → List ℤ
  | _, [] => []
  | x,z::zs=> (z*x).num / (z*x).den  :: _ℚℤmulConvert x zs

def ℚℤconvert (i : List ℚ) : List ℤ :=
  _ℚℤmulConvert (ℚlcd i) i

#eval mul ℤ [1]           [3]
#eval mul ℤ [1,4]         [3]
#eval mul ℤ [1,4]       [3,4]
#eval mul ℤ [1,2,3,4]   [5,7]
#eval add ℤ [1,4]         [3]
#eval smul ℤ 2          [1,4]
#eval ℤdiv   2 [4,2,0,-1,1,4]
#eval ℤnormalize   [4,2,0,4]
#eval ℤnormalize   [4,2,0]
#eval ℤnormalize   [-6]
#eval ℚdiv   2 [4,2,0,-1,1,4]
#eval ℚnormalize [4,2,0,-1,1,4]
#eval ℚℤconvert (ℚnormalize [4,2,0,-1,1,4])
#eval ℤℚconvert [4,2,0,-1,1,4]


#min_imports
