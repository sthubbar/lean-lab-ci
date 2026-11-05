import LeanLab.LiuWang2002.GapBounds352
import LeanLab.LiuWang2002.GapLate352

/-!
Supply split of the middle theta leaf in Decomp345c.
Schoenfeld 1976 page 356, displays 9.2, 9.3 and the following proof.
The table values are on page 358.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task352
open Real

/-- LEAF. Page 358, rows 18.42068, 18.43, 18.45 and 18.5.
Only the upper psi estimates on the bounded middle interval are needed.
The first row is in the note beneath the table. -/
theorem middle_psi (X : ℝ) (hSmall : 10 ^ 8 < X) (hLarge : X < exp 18.7) :
    Chebyshev.psi X - X <
      (if X < exp 18.43 then 0.00119721 else
        if X < exp 18.45 then 0.0011930 else
          if X < exp 18.5 then 0.0011839 else 0.0011615) * X := by
  sorry

/-- LEAF. Page 356, display 9.3. This is the proper prime power lower
bound on the first middle interval, without any psi error estimate. -/
theorem middle_gap_early (X : ℝ) (hSmall : 10 ^ 8 < X) (hEnd : X < exp 18.43) :
    0.000104517 * X < Chebyshev.psi X - Chebyshev.theta X := by
  exact gap_early X hSmall hEnd

/-- LEAF. Page 356, the display after 9.3. This is the proper prime
power lower bound between exp 18.43 and exp 18.45. -/
theorem middle_gap_bridge (X : ℝ) (hStart : exp 18.43 ≤ X) (hEnd : X < exp 18.45) :
    0.000102563 * X < Chebyshev.psi X - Chebyshev.theta X := by
  exact gap_bridge X hStart hEnd

/-- Derived upper endpoints for the final two middle intervals on
page 356, proof of display 5.1 star. -/
theorem middle_endpoint_bounds : exp (18.5 : ℝ) < 110000000 ∧
    exp (18.7 : ℝ) < 133000000 := by
  have he : exp (1 : ℝ) ≤ 2.719 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h37 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ exp 1) he 37
  have h187 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ exp 1) he 187
  constructor
  · have hh : (exp (18.5 : ℝ)) ^ 2 ≤ (2.719 : ℝ) ^ 37 := by
      rw [← exp_nat_mul] at h37 ⊢
      norm_num at h37 ⊢
      exact h37
    norm_num at hh
    nlinarith [exp_pos (18.5 : ℝ)]
  · have hh : (exp (18.7 : ℝ)) ^ 10 ≤ (2.719 : ℝ) ^ 187 := by
      rw [← exp_nat_mul] at h187 ⊢
      norm_num at h187 ⊢
      exact h187
    have hnum : (2.719 : ℝ) ^ 187 < (133000000 : ℝ) ^ 10 := by norm_num
    have hlt : (exp (18.7 : ℝ)) ^ 10 < (133000000 : ℝ) ^ 10 := hh.trans_lt hnum
    exact (pow_lt_pow_iff_left₀ (exp_pos _).le (by positivity) (by norm_num : (10 : ℕ) ≠ 0)).mp hlt

/-- LEAF. Page 356, the last proper prime power lower bound in the proof
of 5.1 star. The printed c is 616.7872256 and log 467 is positive.
Discarding those positive margins gives this smaller sufficient input. -/
theorem middle_gap_late (X : ℝ) (hStart : exp 18.45 ≤ X) (hEnd : X < exp 18.7) :
    0.98 * sqrt X + 616 < Chebyshev.psi X - Chebyshev.theta X := by
  have hl : (100000000 : ℝ) < X := by
    have he : exp (18.43 : ℝ) ≤ exp 18.45 := exp_le_exp.mpr (by norm_num)
    have h := gap_endpoint_bounds.1
    rw [show (10 : ℝ) ^ 8 = 100000000 by norm_num] at h
    exact h.trans_le (he.trans hStart)
  exact gap_late X hl.le (hEnd.trans middle_endpoint_bounds.2).le

/-- The retained square root correction absorbs the two late table
excesses. Derived rational margins for page 356, display 5.1 star. -/
theorem middle_late_margins (X : ℝ) (hX : 10 ^ 8 < X) :
    (X < exp 18.5 → 0.0000909 * X < 0.98 * sqrt X + 616) ∧
    (X < exp 18.7 → 0.0000685 * X < 0.98 * sqrt X + 616) := by
  have hX0 : 0 ≤ X := by norm_num at hX; linarith
  have hs0 := sqrt_nonneg X
  have hs2 := sq_sqrt hX0
  have hs : 10000 < sqrt X := by norm_num at hX; nlinarith
  constructor
  · intro h
    have hu := h.trans middle_endpoint_bounds.1
    nlinarith
  · intro h
    have hu := h.trans middle_endpoint_bounds.2
    nlinarith

/-- The middle theta leaf with exactly the original statement.
CONDITIONAL ON the middle psi table. The three proper prime power
lower bounds are proved. Source page 356, proof of display 5.1 star. -/
theorem theta_middle (X : ℝ) (hSmall : 10 ^ 8 < X) (hLarge : X < exp 18.7) :
    Chebyshev.theta X < 1.001093 * X := by
  have hp := middle_psi X hSmall hLarge
  have hX0 : 0 < X := by norm_num at hSmall; linarith
  by_cases h43 : X < exp 18.43
  · rw [if_pos h43] at hp
    have hg := middle_gap_early X hSmall h43
    nlinarith
  · rw [if_neg h43] at hp
    by_cases h45 : X < exp 18.45
    · rw [if_pos h45] at hp
      have hg := middle_gap_bridge X (le_of_not_gt h43) h45
      nlinarith
    · rw [if_neg h45] at hp
      have hg := middle_gap_late X (le_of_not_gt h45) hLarge
      have hm := middle_late_margins X hSmall
      by_cases h5 : X < exp 18.5
      · rw [if_pos h5] at hp
        have ht := hm.1 h5
        linarith
      · rw [if_neg h5] at hp
        have ht := hm.2 hLarge
        linarith

end LeanLab.LiuWang2002.Task352

#print axioms LeanLab.LiuWang2002.Task352.middle_endpoint_bounds
#print axioms LeanLab.LiuWang2002.Task352.middle_late_margins
#print axioms LeanLab.LiuWang2002.Task352.theta_middle

#print axioms LeanLab.LiuWang2002.Task352.middle_gap_early
#print axioms LeanLab.LiuWang2002.Task352.middle_gap_bridge
#print axioms LeanLab.LiuWang2002.Task352.middle_gap_late
