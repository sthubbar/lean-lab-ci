import LeanLab.BS2022GRH.ThetaInputs224

/-!
Split of the LEAF dusart_theta_late_rows of S106SplitDecomp426b, session S143,
burst-20261122. Dusart 2010, page 15, Table 6.3, theta column.
The row b = 32 with epsilon 4.057e-6 on 32 ≤ log x ≤ 100 is proved here from cited
lab leaves already shared by other folders: on 32 ≤ log x ≤ 40 every x lies below 10^19,
inside Buthe 2018 Theorem 2, displays 1.6 and 1.7, arXiv 1511.02032 page 2, which are
ThetaLeavesS63.buthe2018_display16 and ThetaInputs224.theta_buthe_1e19; on log x > 40
the corrected table of Broadbent et al. 2026, arXiv 2608.01498v1, Table 2 page 39,
row log x0 = 40, is ThetaLeavesS63.broadbent2026_row40.
Only the row b = 100, epsilon 2.903e-11, remains one smaller cited LEAF.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

open Real Chebyshev

namespace LeanLab.RieselVaughan1983.S143SplitDusartRows

/-- LEAF: Dusart 2010 page 15, Table 6.3, theta column, row b = 100:
|θ x - x| < 2.903e-11 x on the band 100 ≤ log x ≤ 300. The Broadbent et al. 2026 rows
shared in the lab, log x0 = 40 and 2500, are too weak on this band. Class HARD, cited
analytic computation with zeros of zeta. -/
theorem dusart_row100 (x : ℝ) (hx : 0 < x) (hb : 100 ≤ log x) (hu : log x ≤ 300) :
    |θ x - x| < (2903 / 100000000000000 : ℝ) * x := by
  sorry

/-- exp 16 is at least 8 * 10^6. -/
theorem exp16_ge : (8000000 : ℝ) ≤ exp 16 := by
  have h := LeanLab.BS2022GRH.ThetaLeavesS63.exp_nat_ge 16
  norm_num at h
  linarith

/-- Dusart 2010 Table 6.3, theta column, row b = 32, epsilon 4.057e-6, on the band
32 ≤ log x ≤ 100. CONDITIONAL ON the shared lab leaves buthe2018_display16,
theta_buthe_1e19 and broadbent2026_row40. -/
theorem dusart_row32 (x : ℝ) (hx : 0 < x) (hb : 32 ≤ log x) (hu : log x ≤ 100) :
    |θ x - x| < (4057 / 1000000000 : ℝ) * x := by
  rcases le_or_gt (log x) 40 with h40 | h40
  · have hx40 : x ≤ exp 40 := by
      rw [← exp_log hx]; exact exp_le_exp.mpr h40
    have h1e19 : x ≤ 1e19 :=
      hx40.trans LeanLab.BS2022GRH.ThetaLeavesS63.exp40_lt_1e19.le
    have hE : exp 32 ≤ x := by
      rw [← exp_log hx]; exact exp_le_exp.mpr hb
    have hsq : exp 16 ≤ sqrt x := by
      have : exp (32 : ℝ) = exp 16 ^ 2 := by
        rw [← exp_nat_mul]; norm_num
      rw [this] at hE
      calc exp 16 = sqrt (exp 16 ^ 2) := (sqrt_sq (exp_pos 16).le).symm
        _ ≤ sqrt x := sqrt_le_sqrt hE
    have he := exp16_ge
    have hxs : sqrt x * sqrt x = x := mul_self_sqrt hx.le
    have hs0 : 0 < sqrt x := by linarith
    have h1423 : (1423 : ℝ) ≤ x := by nlinarith
    have hU := LeanLab.BS2022GRH.ThetaLeavesS63.buthe2018_display16 x h1423 h1e19
    have hL := LeanLab.BS2022GRH.ThetaInputs224.theta_buthe_1e19 x (by linarith) h1e19
    have hgap : 1.95 * √x < (4057 / 1000000000 : ℝ) * x := by
      have hk : (1.95 : ℝ) < (4057 / 1000000000 : ℝ) * sqrt x := by linarith
      nlinarith [mul_lt_mul_of_pos_left hk hs0]
    have hU' : x - θ x ≤ 1.95 * √x := hU
    rw [abs_lt]
    constructor <;> nlinarith
  · have hE : exp 40 < x := by
      rw [← exp_log hx]; exact exp_lt_exp.mpr h40
    have hB := LeanLab.BS2022GRH.ThetaLeavesS63.broadbent2026_row40 x hE
    have hL : 0 < log x := by linarith
    have hq : 8.5536e-7 * x / log x < (4057 / 1000000000 : ℝ) * x := by
      rw [div_lt_iff₀ hL]
      nlinarith
    linarith

/-- Statement identical to S106SplitDecomp426b.dusart_theta_late_rows.
CONDITIONAL ON the LEAF dusart_row100 and the shared lab leaves used by dusart_row32. -/
theorem dusart_theta_late_rows_of_leaves (b u ε x : ℝ)
    (hrow : (b, u, ε) ∈
      ([(32, 100, 4057 / 1000000000), (100, 300, 2903 / 100000000000000)] :
        List (ℝ × ℝ × ℝ)))
    (hx : 0 < x) (hb : b ≤ log x) (hu : log x ≤ u) :
    |θ x - x| < ε * x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrow
  rcases hrow with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact dusart_row32 x hx hb hu
  · exact dusart_row100 x hx hb hu

end LeanLab.RieselVaughan1983.S143SplitDusartRows
