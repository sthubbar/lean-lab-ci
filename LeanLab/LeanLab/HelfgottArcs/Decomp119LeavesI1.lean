/-
P0013 page 70, the Type I logarithmic bound before equation 5.58, split into leaves.
The original statement is Decomp119.typeI₁_bound; this file imports Decomp119,
so the assembly is stated here as typeI₁_bound_of_leaves.
The paper works with a new approximation 2α = a'/q' + δ'/x with q' ≤ Q = x^{2/3}/(500√6).
The leaves keep that re-approximation explicit, since the totient check of page 70 fails
for denominators as large as the 3/4 x^{2/3} allowed by MinorHyp, for example at
x = 2.16e20 and q the product of the primes up to 37.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119

namespace LeanLab.HelfgottArcs.Decomp119LeavesI1
open LeanLab.HelfgottArcs.Decomp119

/-- LEAF: page 70, equation 5.2 for the second choice of U, V, Q and the new
approximation of 2α with denominator q' ≤ Q, in case a or case b. Class HARD.
P0013 page 70, display ending in 1.063/10000 x^{2/3} (log x)^2, c'_0 = 0.798437 of
page 59; the term 0.090843 x^{2/3} of the next display is kept and the squared log
coefficient is taken as the larger 0.001063. -/
theorem typeI₁_eq52 (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ∃ q' : ℕ, ∃ δ' : ℝ, 1 ≤ q' ∧ (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      (x ^ ((1 : ℝ) / 3) / 6 < q' ∨
        (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')) ∧
      ‖I₁ α x‖ ≤ x / q' * min 1 (0.798437 / δ' ^ 2) *
          (2 / 3 * Real.log x - 4.99944 + 1.00303 * ((q' : ℝ) / Nat.totient q')) +
        0.090843 * x ^ ((2 : ℝ) / 3) + 0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 := by
  sorry

/-- LEAF: page 70, q'/φ(q') ≤ ̥(Q) with ̥ as in display 5.55, and the check
1.00303 ̥(Q) ≤ 0.0327 log x + 4.99944. Class HARD. P0013 page 70, lines after the
display for S_{I,1}; an explicit Rosser and Schoenfeld type bound for q/φ(q). -/
theorem totient_ratio_bound (x : ℝ) (hx : 2.16e20 ≤ x) (q' : ℕ) (hq1 : 1 ≤ q')
    (hqQ : (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6)) :
    1.00303 * ((q' : ℝ) / Nat.totient q') ≤ 0.0327 * Real.log x + 4.99944 := by
  sorry

/-- Page 70: with q > y = x^{1/3}/6 the factor x/q is at most x/y = 6 x^{2/3}. -/
theorem x_div_q_le (x : ℝ) (q : ℕ) (hx : 0 < x) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    x / q ≤ 6 * x ^ ((2 : ℝ) / 3) := by
  have hy : 0 < x ^ ((1 : ℝ) / 3) / 6 := by positivity
  have hq0 : (0 : ℝ) < q := hy.trans hq
  have hsplit : x = x ^ ((1 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hx]; norm_num
  rw [div_le_iff₀ hq0]
  calc x = 6 * x ^ ((2 : ℝ) / 3) * (x ^ ((1 : ℝ) / 3) / 6) := by
        nth_rewrite 1 [hsplit]; ring
    _ ≤ 6 * x ^ ((2 : ℝ) / 3) * q := by
        apply mul_le_mul_of_nonneg_left hq.le; positivity

/-- Page 70: in case a or case b the factor x/q' min(1, c'_0/δ'^2) is at most x/y. -/
theorem case_factor_le (x : ℝ) (hx : 0 < x) (q' : ℕ) (δ' : ℝ) (hq1 : 1 ≤ q')
    (hc : x ^ ((1 : ℝ) / 3) / 6 < q' ∨
      (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')) :
    x / q' * min 1 (0.798437 / δ' ^ 2) ≤ 6 * x ^ ((2 : ℝ) / 3) := by
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  have hM0 : 0 ≤ x / q' := by positivity
  rcases hc with hc | ⟨hd, hdq⟩
  · calc x / q' * min 1 (0.798437 / δ' ^ 2) ≤ x / q' * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hM0
      _ ≤ _ := by rw [mul_one]; exact x_div_q_le x q' hx hc
  · set y := x ^ ((1 : ℝ) / 3) / 6 with hy
    have hy0 : 0 < y := by positivity
    have hsplit : x = 6 * x ^ ((2 : ℝ) / 3) * y := by
      have hs : x = x ^ ((1 : ℝ) / 3) * x ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hx]; norm_num
      rw [hy]; nth_rewrite 1 [hs]; ring
    have hd0 : 0 < |δ'| := by linarith
    have hsq : δ' ^ 2 = |δ'| * |δ'| := by rw [← sq_abs]; ring
    have hbig : 64 * y < q' * δ' ^ 2 := by
      rw [hsq]; nlinarith
    have hpos : 0 < (q' : ℝ) * δ' ^ 2 := by linarith
    calc x / q' * min 1 (0.798437 / δ' ^ 2) ≤ x / q' * (0.798437 / δ' ^ 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hM0
      _ = x * 0.798437 / (q' * δ' ^ 2) := by
          field_simp
      _ ≤ x / y := by
          rw [div_le_div_iff₀ hpos hy0]; nlinarith
      _ = 6 * x ^ ((2 : ℝ) / 3) := by
          rw [div_eq_iff hy0.ne']; exact hsplit

/-- Assembly of Decomp119.typeI₁_bound from the two leaves, exact parent statement. -/
theorem typeI₁_bound_of_leaves (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ)
    (h : MinorHyp x α a q δ) (hq : x ^ ((1 : ℝ) / 3) / 6 < q) :
    ‖I₁ α x‖ ≤ 4.1982 * x ^ ((2 : ℝ) / 3) * Real.log x +
      0.001063 * x ^ ((2 : ℝ) / 3) * Real.log x ^ 2 := by
  obtain ⟨q', δ', hq1, hqQ, hc, h1⟩ := typeI₁_eq52 x α a q δ h hq
  have hx : 2.16e20 ≤ x := h.1
  have h2 := totient_ratio_bound x hx q' hq1 hqQ
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hL : 46.45 < Real.log x :=
    MinorMain.L_bounds.1.trans_le (Real.log_le_log (by norm_num) hx)
  have hq0 : (0 : ℝ) < q' := by exact_mod_cast hq1
  have hmin0 : 0 ≤ min (1 : ℝ) (0.798437 / δ' ^ 2) := le_min (by norm_num) (by positivity)
  have hrat : 1 ≤ (q' : ℝ) / Nat.totient q' := by
    have ht : (Nat.totient q' : ℝ) ≤ q' := by exact_mod_cast Nat.totient_le q'
    have ht0 : (0 : ℝ) < Nat.totient q' := by
      have : 0 < Nat.totient q' := Nat.totient_pos.mpr hq1
      exact_mod_cast this
    rw [le_div_iff₀ ht0]; linarith
  set F := 2 / 3 * Real.log x - 4.99944 + 1.00303 * ((q' : ℝ) / Nat.totient q') with hF
  have hF0 : 0 ≤ F := by rw [hF]; nlinarith
  have hFle : F ≤ 0.69937 * Real.log x := by rw [hF]; linarith
  have hMm := case_factor_le x hx0 q' δ' hq1 hc
  set P := x ^ ((2 : ℝ) / 3) with hP
  have hP0 : 0 ≤ P := by positivity
  have hprod : x / q' * min (1 : ℝ) (0.798437 / δ' ^ 2) * F ≤ 6 * P * (0.69937 * Real.log x) :=
    mul_le_mul hMm hFle hF0 (by positivity)
  have hlow : 0.090843 * P ≤ 0.002 * P * Real.log x := by nlinarith
  nlinarith

end LeanLab.HelfgottArcs.Decomp119LeavesI1
