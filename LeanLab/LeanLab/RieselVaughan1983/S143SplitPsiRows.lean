import LeanLab.ChirreHagen2025.Decomp429e
import LeanLab.BS2022GRH.ThetaLeavesS63

/-!
Split of the two LEAFs of S106SplitDecomp426a, session S143, burst-20261122.
1. buthe_psi_finite_range, Buthe 2018 Theorem 2 display 1.5, arXiv 1511.02032 page 2,
   |x - psi x| ≤ 0.94 sqrt x for 11 < x ≤ 10^19. From x = 100000 on this is the shared lab
   leaf ChirreHagen2025.Decomp429e.psi_finite_range, the same display as quoted by JRT Lemma 7.
   The range 11 < x < 100000 remains one smaller LEAF, a finite computation.
2. schoenfeld_late_rows, Schoenfeld 1976 page 358 table, rows b = 35 and b = 1000.
   Row b = 1000, epsilon 7.0481e-9 on 1000 ≤ log t ≤ 1950, is proved from the shared lab
   leaf ThetaLeavesS63.broadbent2026_row40, Broadbent et al. 2026 Table 2 page 39, and the
   Mathlib bound psi - theta ≤ 2 sqrt x log x. Row b = 35 remains one LEAF: the row 40 of
   Broadbent et al. gives only 2.14e-8 at log t = 40, above the epsilon 1.8314e-8.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.S143SplitPsiRows

/-- LEAF: Buthe 2018 Theorem 2 display 1.5, arXiv 1511.02032 page 2, on the initial range
11 < x < 100000: |x - psi x| ≤ 0.94 sqrt x. Buthe covers this range by direct computation of
psi below 10^7, section 6. Class MEDIUM: a finite computation over the prime powers below
100000, with rational enclosures of their logarithms. -/
theorem buthe_psi_small (x : ℝ) (hx : 11 < x) (hx1 : x < 100000) :
    |x - psi x| ≤ 0.94 * sqrt x := by
  sorry

/-- Statement identical to S106SplitDecomp426a.buthe_psi_finite_range.
CONDITIONAL ON the LEAF buthe_psi_small and the shared lab leaf
ChirreHagen2025.Decomp429e.psi_finite_range. -/
theorem buthe_psi_finite_range_of_leaves (x : ℝ) (hx : 11 < x) (hx1 : x ≤ 1e19) :
    |x - psi x| ≤ 0.94 * sqrt x := by
  rcases lt_or_ge x 100000 with h | h
  · exact buthe_psi_small x hx h
  · rw [abs_sub_comm]
    exact LeanLab.ChirreHagen2025.Decomp429e.psi_finite_range x h (by norm_num at hx1 ⊢; linarith)

/-- LEAF: Schoenfeld 1976 page 358 table, epsilon column at b = 35:
|psi t - t| < 1.8314e-8 t on the band 35 ≤ log t ≤ 1000. Class HARD, cited analytic
computation with zeros of zeta. -/
theorem schoenfeld_row35 (t : ℝ) (ht : 0 < t) (hb : 35 ≤ log t) (hu : log t ≤ 1000) :
    |psi t - t| < (18314 / 1000000000 : ℝ) * t := by
  sorry

/-- exp 15 is at least 3.2 * 10^6. -/
theorem exp15_ge : (3200000 : ℝ) ≤ exp 15 := by
  have h := LeanLab.BS2022GRH.ThetaLeavesS63.exp_nat_ge 15
  norm_num at h
  linarith

/-- Schoenfeld 1976 page 358, row b = 1000, epsilon 7.0481e-9 on 1000 ≤ log t ≤ 1950.
CONDITIONAL ON the shared lab leaf ThetaLeavesS63.broadbent2026_row40. -/
theorem schoenfeld_row1000 (t : ℝ) (ht : 0 < t) (hb : 1000 ≤ log t) (hu : log t ≤ 1950) :
    |psi t - t| < (70481 / 10000000000 : ℝ) * t := by
  have hE : exp 40 < t := by
    rw [← exp_log ht]; exact exp_lt_exp.mpr (by linarith)
  have hB := LeanLab.BS2022GRH.ThetaLeavesS63.broadbent2026_row40 t hE
  have hL : 0 < log t := by linarith
  have hE30 : exp 30 ≤ t := by
    rw [← exp_log ht]; exact exp_le_exp.mpr (by linarith)
  have hsq : exp 15 ≤ sqrt t := by
    have : exp (30 : ℝ) = exp 15 ^ 2 := by
      rw [← exp_nat_mul]; norm_num
    rw [this] at hE30
    calc exp 15 = sqrt (exp 15 ^ 2) := (sqrt_sq (exp_pos 15).le).symm
      _ ≤ sqrt t := sqrt_le_sqrt hE30
  have he := exp15_ge
  have hs0 : 0 < sqrt t := by linarith
  have hts : sqrt t * sqrt t = t := mul_self_sqrt ht.le
  have h1 : (1 : ℝ) ≤ t := by nlinarith
  have hPT := Chebyshev.psi_sub_theta_le h1
  have hTP := Chebyshev.theta_le_psi t
  -- 2 sqrt t log t ≤ 3900 sqrt t ≤ 1e-9 t once sqrt t ≥ 3.9e12, which follows from exp 30.
  have hE60 : exp 60 ≤ t := by
    rw [← exp_log ht]; exact exp_le_exp.mpr (by linarith)
  have hsq30 : exp 15 * exp 15 ≤ sqrt t := by
    have : exp (60 : ℝ) = (exp 15 * exp 15) ^ 2 := by
      rw [← exp_add, ← exp_nat_mul]; norm_num
    rw [this] at hE60
    calc exp 15 * exp 15 = sqrt ((exp 15 * exp 15) ^ 2) :=
          (sqrt_sq (by positivity)).symm
      _ ≤ sqrt t := sqrt_le_sqrt hE60
  have hbig : (10240000000000 : ℝ) ≤ sqrt t := by nlinarith
  have hsmall : 2 * √t * log t ≤ (1 / 1000000000 : ℝ) * t := by
    have : 2 * log t ≤ (1 / 1000000000 : ℝ) * sqrt t := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this hs0.le]
  have hq : 8.5536e-7 * t / log t ≤ (1 / 1000000000 : ℝ) * t := by
    rw [div_le_iff₀ hL]
    nlinarith
  rw [abs_lt] at hB ⊢
  constructor <;> nlinarith

/-- Statement identical to S106SplitDecomp426a.schoenfeld_late_rows.
CONDITIONAL ON the LEAF schoenfeld_row35 and the shared lab leaf broadbent2026_row40. -/
theorem schoenfeld_late_rows_of_leaves (b u ε t : ℝ)
    (hrow : (b, u, ε) ∈
      ([(35, 1000, 18314 / 1000000000), (1000, 1950, 70481 / 10000000000)] :
        List (ℝ × ℝ × ℝ)))
    (ht : 0 < t) (hb : b ≤ log t) (hu : log t ≤ u) :
    |psi t - t| < ε * t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
  rcases hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact schoenfeld_row35 t ht hb hu
  · exact schoenfeld_row1000 t ht hb hu

end LeanLab.RieselVaughan1983.S143SplitPsiRows
