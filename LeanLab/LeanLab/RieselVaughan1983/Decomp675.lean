import LeanLab.RieselVaughan1983.Decomp426b

/-!
Audit of the shared Dusart k = 2 route for the bounded theta bands.
Sources: Dusart 2010 page 4 Theorem 5.2 and page 15 Table 6.3.
The conditional transfers do not certify the cited analytic input.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.Task675

/-- The shared k = 2 threshold lies strictly between exp 22 and exp 23.
This leaves an initial part of the requested log band uncovered. -/
theorem k2_threshold_gap :
    exp (22 : ℝ) < 7713133853 ∧ (7713133853 : ℝ) < exp 23 := by
  constructor
  · have he : exp (1 : ℝ) < 2.72 := exp_one_lt_d9.trans (by norm_num)
    have hp : exp (1 : ℝ) ^ 22 < (2.72 : ℝ) ^ 22 := by
      gcongr
    have hid : exp (22 : ℝ) = exp (1 : ℝ) ^ 22 := by
      simpa using exp_nat_mul (22 : ℕ) (1 : ℝ)
    rw [← hid] at hp
    norm_num at hp
    linarith
  · have h := LeanLab.RieselVaughan1983.Lemma6Theta.exp_nat_ge 23
    norm_num at h
    linarith

/-- CONDITIONAL ON the shared k = 2 input. It gives both requested initial
signed estimates on the subband with log x at least 23. -/
theorem initial_signed_of_k2
    (hD : LeanLab.Common.ThetaWindow.DusartThm52k2)
    (x : ℝ) (hx : 0 < x) (h23 : 23 ≤ log x) :
    θ x - x < x / 36260 ∧
      -(1 / 1000 : ℝ) * x / log x < θ x - x := by
  have ht : (7713133853 : ℝ) ≤ x :=
    k2_threshold_gap.2.le.trans ((le_log_iff_exp_le hx).mp h23)
  have h := abs_le.mp (hD x ht)
  have hL : 0 < log x := by linarith
  have hsq : (23 : ℝ) ^ 2 ≤ log x ^ 2 := by nlinarith
  have hu : (0.01 : ℝ) * x / log x ^ 2 < x / 36260 := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hL) (by norm_num : (0 : ℝ) < 36260)).mpr
    nlinarith [mul_pos hx (show 0 < log x ^ 2 - (0.01 : ℝ) * 36260 by nlinarith)]
  have hl : (0.01 : ℝ) * x / log x ^ 2 < (1 / 1000 : ℝ) * x / log x := by
    apply (div_lt_div_iff₀ (sq_pos_of_pos hL) hL).mpr
    have hm := mul_pos (mul_pos hx hL)
      (show 0 < (1 / 1000 : ℝ) * log x - 0.01 by linarith)
    nlinarith
  constructor
  · exact h.2.trans_lt hu
  · simpa only [neg_mul, neg_div] using (neg_lt_neg hl).trans_le h.1

/-- CONDITIONAL ON the shared k = 2 input. The first two selected relative
rows follow with a strict coefficient margin. No upper endpoint is needed. -/
theorem early_relative_rows_of_k2
    (hD : LeanLab.Common.ThetaWindow.DusartThm52k2)
    (b ε x : ℝ)
    (hrow : (b, ε) ∈ ([(27, 3507 / 100000000),
      (28, 2308 / 100000000)] : List (ℝ × ℝ)))
    (hx : 0 < x) (hb : b ≤ log x) :
    |θ x - x| < ε * x := by
  have hb27 : 27 ≤ b := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
    rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have ht : (7713133853 : ℝ) ≤ x :=
    k2_threshold_gap.2.le.trans ((le_log_iff_exp_le hx).mp (by linarith))
  have hL : 0 < log x := by linarith
  have hbudget : (0.01 : ℝ) < ε * log x ^ 2 := by
    have hsq : b ^ 2 ≤ log x ^ 2 := by nlinarith
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
    rcases hrow with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at hsq ⊢ <;> nlinarith
  refine (hD x ht).trans_lt ?_
  apply (div_lt_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith [mul_pos hx (sub_pos.mpr hbudget)]

/-- At the last two lower endpoints the k = 2 relative error envelope permits
an error at least the requested epsilon. These are scalar countermodels only. -/
theorem late_relative_rows_obstruction :
    (∃ e : ℝ, 0 ≤ e ∧ e ≤ (0.01 : ℝ) / 32 ^ 2 ∧
      ¬e < 4057 / 1000000000) ∧
    (∃ e : ℝ, 0 ≤ e ∧ e ≤ (0.01 : ℝ) / 100 ^ 2 ∧
      ¬e < 2903 / 100000000000000) := by
  constructor
  · exact ⟨(0.01 : ℝ) / 32 ^ 2, by norm_num, le_rfl, by norm_num⟩
  · exact ⟨(0.01 : ℝ) / 100 ^ 2, by norm_num, le_rfl, by norm_num⟩

end LeanLab.RieselVaughan1983.Task675
