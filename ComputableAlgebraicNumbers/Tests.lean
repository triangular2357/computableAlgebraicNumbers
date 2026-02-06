import Mathlib
import ComputableAlgebraicNumbers.AlgebraicNumber

#eval! (5 : RealAlgebraicNumber)

def ic (q : ℤ) : RealAlgebraicNumber := q

def sqrt (q : ℚ) (h : (q > 0) := by decide) : RealAlgebraicNumber := Quotient.mk equiv {
  min_poly := CPoly.X ^ 2 - CPoly.const q
  squarefree := sorry
  lower := if q < 1 then q else 1
  upper := |q| + 1
  lower_le_upper := by
    split_ifs with h'
    · rw [abs_of_pos h]
      apply le_add_of_nonneg_right
      norm_num
    · apply le_add_of_nonneg_left
      apply abs_nonneg
  ivt_condition := by
    split_ifs with h' <;> simp [toPolynomialSimp, abs_of_pos h]
    · ring_nf
      rw [show -q = -(q * 1 ^ 3) by simp only [one_pow, mul_one], neg_add_eq_sub, sub_nonpos,
        show q ^ 4 = q * q ^ 3 by ring]
      gcongr
    · ring_nf
      apply not_lt.1 at h'
      rw [sub_nonpos, show (1 : ℚ) = 1 ^ 3 by ring]
      gcongr
  deriv_nzero := sorry
}


#eval! ic 5 + 2 * sqrt 6
#eval! (sqrt 2 + sqrt 3) ^ 2

#eval! ic 5 + 2 * sqrt 6 = (sqrt 2 + sqrt 3) ^ 2
