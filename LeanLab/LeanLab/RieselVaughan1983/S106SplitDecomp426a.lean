import LeanLab.RieselVaughan1983.Lemma6Theta

/-!
Split for the Schoenfeld table leaf schoenfeld_relative_rows of Decomp426a,
session S106, burst-20261122.
The two first selected rows of the Schoenfeld 1976 page 358 table, b = 18.42 and b = 20,
are only requested for log x at most 35, so every such x lies below 10^19, inside the
finite range of Buthe 2018 Theorem 2 display 1.5, arXiv 1511.02032 page 2.
The rows b = 35 and b = 1000 reach beyond 10^19 and remain one smaller cited LEAF.
The assembly theorem carries a statement identical to the original.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.S106SplitDecomp426a

/-- LEAF: Buthe 2018 Theorem 2, display 1.5, arXiv 1511.02032 page 2:
the absolute value of x minus psi x is at most 0.94 sqrt x for 11 < x ≤ 10^19.
A finite analytic computation, cited. The lab also has the narrower form
ChirreHagen2025 Decomp429e.psi_finite_range from 100000 on. Class HARD for Codex. -/
theorem buthe_psi_finite_range (x : ℝ) (hx : 11 < x) (hx1 : x ≤ 1e19) :
    |x - psi x| ≤ 0.94 * sqrt x := by
  sorry

/-- LEAF: Schoenfeld 1976 page 358 table, epsilon column at b = 35 and b = 1000.
Each fixed relative psi error is requested only on its bounded logarithmic band,
as in Task426.schoenfeld_relative_rows; only these two of its four rows remain cited.
Class HARD for Codex. -/
theorem schoenfeld_late_rows (b u ε t : ℝ)
    (hrow : (b, u, ε) ∈
      ([(35, 1000, 18314 / 1000000000), (1000, 1950, 70481 / 10000000000)] :
        List (ℝ × ℝ × ℝ)))
    (ht : 0 < t) (hb : b ≤ log t) (hu : log t ≤ u) :
    |psi t - t| < ε * t := by
  sorry

/-- Every t with log t at most 35 is below 10^19. -/
theorem le_1e19_of_log_le_35 (t : ℝ) (ht : 0 < t) (h35 : log t ≤ 35) :
    t ≤ 1e19 := by
  have ht' : t ≤ exp 35 := by
    rw [← exp_log ht]; exact exp_le_exp.mpr h35
  have he : exp (35 : ℝ) ≤ 3 ^ 35 := by
    have h1 : exp (1 : ℝ) ≤ 3 := (exp_one_lt_d9.trans (by norm_num)).le
    have : exp (35 : ℝ) = exp 1 ^ 35 := by
      rw [← exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (exp_pos 1).le h1 35
  linarith [show (3 : ℝ) ^ 35 ≤ 1e19 by norm_num]

/-- The two early page 358 rows on 18 ≤ log t ≤ 35 follow from Buthe display 1.5,
with the smaller of the two epsilons. CONDITIONAL ON the LEAF buthe_psi_finite_range. -/
theorem early_psi_rows_of_buthe (t : ℝ) (ht : 0 < t) (h18 : 18 ≤ log t)
    (h35 : log t ≤ 35) :
    |psi t - t| < (65759 / 100000000 : ℝ) * t := by
  have hE : exp 18 ≤ t := by
    rw [← exp_log ht]; exact exp_le_exp.mpr h18
  have he9 : (8100 : ℝ) ≤ exp 9 := by
    have h := Lemma6Theta.exp_nat_ge 9
    norm_num at h
    linarith
  have hsq : exp 9 ≤ sqrt t := by
    have : exp (18 : ℝ) = exp 9 ^ 2 := by
      rw [← exp_nat_mul]; norm_num
    rw [this] at hE
    calc exp 9 = sqrt (exp 9 ^ 2) := (sqrt_sq (exp_pos 9).le).symm
      _ ≤ sqrt t := sqrt_le_sqrt hE
  have hts : sqrt t * sqrt t = t := mul_self_sqrt ht.le
  have hs0 : 0 < sqrt t := by linarith
  have h11 : (11 : ℝ) < t := by nlinarith
  have hB := buthe_psi_finite_range t h11 (le_1e19_of_log_le_35 t ht h35)
  have hgap : 0.94 * sqrt t < (65759 / 100000000 : ℝ) * t := by
    have hk : (0.94 : ℝ) < (65759 / 100000000 : ℝ) * sqrt t := by linarith
    nlinarith [mul_lt_mul_of_pos_left hk hs0]
  rw [abs_sub_comm] at hB
  linarith

/-- Statement identical to Task426.schoenfeld_relative_rows.
CONDITIONAL ON the LEAFs buthe_psi_finite_range and schoenfeld_late_rows. -/
theorem schoenfeld_relative_rows (b u ε t : ℝ)
    (hrow : (b, u, ε) ∈
      ([(921 / 50, 20, 11976 / 10000000), (20, 35, 65759 / 100000000),
        (35, 1000, 18314 / 1000000000), (1000, 1950, 70481 / 10000000000)] :
        List (ℝ × ℝ × ℝ)))
    (ht : 0 < t) (hb : b ≤ log t) (hu : log t ≤ u) :
    |psi t - t| < ε * t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
  rcases hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have h := early_psi_rows_of_buthe t ht (by linarith) (by linarith)
    nlinarith
  · exact early_psi_rows_of_buthe t ht (by linarith) hu
  · exact schoenfeld_late_rows 35 1000 _ t (by simp) ht hb hu
  · exact schoenfeld_late_rows 1000 1950 _ t (by simp) ht hb hu

end LeanLab.RieselVaughan1983.S106SplitDecomp426a
