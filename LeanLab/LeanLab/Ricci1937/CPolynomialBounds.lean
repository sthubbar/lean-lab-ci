import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, page 83: a coefficient bound for the polynomial values.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Finset
noncomputable section

/-- A positive integer coefficient bound for all polynomial values in an initial interval. -/
def valueCoeffBound (P : Polynomial ℤ) : ℕ :=
  (∑ i ∈ P.support, (P.coeff i).natAbs) + 1

/-- Division and taking the natural part do not increase the absolute integer value. -/
lemma Fval_le_natAbs_eval (P : Polynomial ℤ) (n : ℕ) :
    Fval P n ≤ (P.eval (n : ℤ)).natAbs := by
  unfold Fval
  have hpart := Int.toNat_add_toNat_neg_eq_natAbs (P.eval (n : ℤ) / fixedDivisor P)
  have hquot := Int.natAbs_ediv_le_natAbs (P.eval (n : ℤ)) (fixedDivisor P)
  omega

/-- A uniform coefficient bound on the absolute values for 0 ≤ n ≤ xi and xi ≥ 1. -/
lemma natAbs_eval_le_coeff_sum (P : Polynomial ℤ) {n ξ : ℕ} (hξ : 1 ≤ ξ) (hn : n ≤ ξ) :
    (P.eval (n : ℤ)).natAbs ≤
      (∑ i ∈ P.support, (P.coeff i).natAbs) * ξ ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  calc
    (∑ i ∈ P.support, P.coeff i * (n : ℤ) ^ i).natAbs ≤
        ∑ i ∈ P.support, (P.coeff i * (n : ℤ) ^ i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ i ∈ P.support, (P.coeff i).natAbs * ξ ^ P.natDegree := by
      apply sum_le_sum
      intro i hi
      simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left hn i).trans
        (Nat.pow_le_pow_right hξ (Polynomial.le_natDegree_of_ne_zero
          (Polynomial.mem_support_iff.mp hi)))
    _ = (∑ i ∈ P.support, (P.coeff i).natAbs) * ξ ^ P.natDegree := by
      rw [sum_mul]

/-- A strict version of the page 83 polynomial size bound, valid on every initial interval. -/
theorem Fval_lt_valueCoeffBound (P : Polynomial ℤ) {n ξ : ℕ} (hξ : 1 ≤ ξ) (hn : n ≤ ξ) :
    Fval P n < valueCoeffBound P * ξ ^ P.natDegree := by
  have hle := (Fval_le_natAbs_eval P n).trans (natAbs_eval_le_coeff_sum P hξ hn)
  have hp : 0 < ξ ^ P.natDegree := pow_pos (by omega) _
  exact lt_of_le_of_lt hle (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hp)

example : Fval (Polynomial.X : Polynomial ℤ) 5 <
    valueCoeffBound (Polynomial.X : Polynomial ℤ) * 5 ^ (Polynomial.X : Polynomial ℤ).natDegree :=
  Fval_lt_valueCoeffBound _ (by norm_num) le_rfl

example : ((Polynomial.X - 1 : Polynomial ℤ).eval (0 : ℤ)).natAbs ≤
    (∑ i ∈ (Polynomial.X - 1 : Polynomial ℤ).support,
      ((Polynomial.X - 1 : Polynomial ℤ).coeff i).natAbs) *
      1 ^ (Polynomial.X - 1 : Polynomial ℤ).natDegree :=
  natAbs_eval_le_coeff_sum _ (by norm_num) (by norm_num)

end
end LeanLab.Ricci1937
