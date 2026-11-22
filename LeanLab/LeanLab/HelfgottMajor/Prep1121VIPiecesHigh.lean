import Mathlib

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part D, the subintervals of [1.2, 10].
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 35, the integral
printed 226.844 after display 4.12. Its only hard part is g(τ) = log(τ² + 9/4)² / (1/4 + τ²),
see `Prep1121VIIntegral`. Each LEAF bounds ∫ g over one subinterval [a, b] by a decimal V that
exceeds the stated quadrature rule by at least 0.004 and the true value by at least 0.0043,
checked with mpmath at 30 digits. The paper's integration used VNODE-LP, footnote 4.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIPiecesHigh
open Real

/-- Helper for pieces 07 to 10, P0014 page 35, g as in the module doc. Continuity of g, so that every interval integral below exists. -/
private theorem g_cont : Continuous (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) := by
  refine Continuous.div ?_ (by fun_prop) (fun τ => by positivity)
  exact (Continuous.log (by fun_prop) (fun τ => by positivity)).pow 2

/-- Helper for pieces 07 to 10, P0014 page 35, g as in the module doc. The derivative of g by the quotient and chain rules. -/
private theorem g_hasDeriv (τ : ℝ) : HasDerivAt (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))
    ((2 * Real.log (τ ^ 2 + 9 / 4) * (2 * τ / (τ ^ 2 + 9 / 4)) * (1 / 4 + τ ^ 2) -
      Real.log (τ ^ 2 + 9 / 4) ^ 2 * (2 * τ)) / (1 / 4 + τ ^ 2) ^ 2) τ := by
  have hv : HasDerivAt (fun τ : ℝ => τ ^ 2 + 9 / 4) (2 * τ) τ := by
    simpa using (hasDerivAt_pow 2 τ).add_const (9 / 4 : ℝ)
  have hL := hv.log (by positivity)
  have hD : HasDerivAt (fun τ : ℝ => 1 / 4 + τ ^ 2) (2 * τ) τ := by
    simpa using (hasDerivAt_pow 2 τ).const_add (1 / 4 : ℝ)
  have := (hL.pow 2).div hD (by positivity)
  convert this using 1
  simp

/-- Helper for pieces 07 to 10, P0014 page 35, g as in the module doc. g is antitone on [0, ∞): the derivative is 2τ L (2 - 4/v - L)/(1/4 + τ²)² with v = τ² + 9/4 and L = log v, and L ≥ log 4 + 1 - 4/v > 2 - 4/v. -/
private theorem g_antitone : AntitoneOn (fun τ : ℝ => Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2))
    (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) g_cont.continuousOn
    (fun τ _ => (g_hasDeriv τ).differentiableAt.differentiableWithinAt) ?_
  intro τ hτ
  rw [interior_Ici] at hτ
  have hτ0 : 0 < τ := hτ
  rw [(g_hasDeriv τ).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  set v := τ ^ 2 + 9 / 4 with hv
  have hv0 : 0 < v := by positivity
  have hD : 1 / 4 + τ ^ 2 = v - 2 := by rw [hv]; ring
  set L := Real.log v
  have h4 : 1 - (v / 4)⁻¹ ≤ Real.log (v / 4) := Real.one_sub_inv_le_log_of_pos (by positivity)
  rw [Real.log_div hv0.ne' (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow,
    inv_div] at h4
  have hl2 := Real.log_two_gt_d9
  have hL : 2 - 4 / v ≤ L := by push_cast at h4; linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [hv]; nlinarith)
  rw [hD]
  have key : 2 * L * (2 * τ / v) * (v - 2) - L ^ 2 * (2 * τ) = 2 * τ * L * ((2 - 4 / v) - L) := by
    field_simp; ring
  rw [key]
  have : 0 ≤ 2 * τ * L := by positivity
  nlinarith

/-- Helper for pieces 07 to 10, P0014 page 35, g as in the module doc. Left endpoint bound on one step, from `g_antitone`: ∫_x^y g ≤ (y - x) g(x) for 0 ≤ x ≤ y. -/
private theorem step_le (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∫ τ in x..y, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤
      (y - x) * (Real.log (x ^ 2 + 9 / 4) ^ 2 / (1 / 4 + x ^ 2)) := by
  have h := intervalIntegral.integral_mono_on hxy (g_cont.intervalIntegrable x y)
    (intervalIntegrable_const (μ := MeasureTheory.volume)) (fun τ hτ => g_antitone (Set.mem_Ici.2 hx)
      (Set.mem_Ici.2 (hx.trans hτ.1)) hτ.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-- Helper for pieces 07 to 10, P0014 page 35, g as in the module doc. Rational upper bound for log v: m log v = k log 2 + log(v^m/2^k) ≤ k log 2 + v^m/2^k - 1, with log 2 < 0.6931471808. -/
private theorem log_ub (v : ℝ) (m k : ℕ) (hm : 0 < m) (hv : 0 < v) :
    Real.log v ≤ (k * 0.6931471808 + (v ^ m / 2 ^ k - 1)) / m := by
  have hy : 0 < v ^ m / 2 ^ k := by positivity
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
  have hl2 := Real.log_two_lt_d9
  have hk : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg k)
  rw [le_div_iff₀ (by exact_mod_cast hm)]
  linarith

/-- Helper for pieces 07 to 10, P0014 page 35, g as in the module doc. Replacing log(x² + 9/4) by an upper bound U in g(x). -/
private theorem g_le (x U : ℝ) (_hx : 0 ≤ x) (h : Real.log (x ^ 2 + 9 / 4) ≤ U) :
    Real.log (x ^ 2 + 9 / 4) ^ 2 / (1 / 4 + x ^ 2) ≤ U ^ 2 / (1 / 4 + x ^ 2) := by
  have h0 : 0 ≤ Real.log (x ^ 2 + 9 / 4) := Real.log_nonneg (by nlinarith)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h 2) (by positivity)

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [1.2, 1.6]: ∫ g ≤ 0.382;
the true value is 0.3751. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here 2026-11-22 by CLAUDE S7: left endpoint sums, n steps, using that g is antitone on
[0, ∞), with log bounds by `log_ub`. -/
theorem piece_07 :
    ∫ τ in (1.2 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.382 := by
  have s0 : ∫ τ in (1.2 : ℝ)..1.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.080702 := by
    calc ∫ τ in (1.2 : ℝ)..1.28, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.28 - 1.2) * (Real.log ((1.2 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.2 : ℝ) ^ 2)) :=
          step_le 1.2 1.28 (by norm_num) (by norm_num)
      _ ≤ (1.28 - 1.2) * (1.305686 ^ 2 / (1 / 4 + (1.2 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.2 1.305686 (by norm_num)
            ((log_ub _ 9 17 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.080702 := by norm_num
  have s1 : ∫ τ in (1.28 : ℝ)..1.36, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.078172 := by
    calc ∫ τ in (1.28 : ℝ)..1.36, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.36 - 1.28) * (Real.log ((1.28 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.28 : ℝ) ^ 2)) :=
          step_le 1.28 1.36 (by norm_num) (by norm_num)
      _ ≤ (1.36 - 1.28) * (1.358395 ^ 2 / (1 / 4 + (1.28 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.28 1.358395 (by norm_num)
            ((log_ub _ 1 2 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.078172 := by norm_num
  have s2 : ∫ τ in (1.36 : ℝ)..1.44, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.075881 := by
    calc ∫ τ in (1.36 : ℝ)..1.44, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.44 - 1.36) * (Real.log ((1.36 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.36 : ℝ) ^ 2)) :=
          step_le 1.36 1.44 (by norm_num) (by norm_num)
      _ ≤ (1.44 - 1.36) * (1.411195 ^ 2 / (1 / 4 + (1.36 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.36 1.411195 (by norm_num)
            ((log_ub _ 1 2 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.075881 := by norm_num
  have s3 : ∫ τ in (1.44 : ℝ)..1.52, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.073802 := by
    calc ∫ τ in (1.44 : ℝ)..1.52, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.52 - 1.44) * (Real.log ((1.44 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.44 : ℝ) ^ 2)) :=
          step_le 1.44 1.52 (by norm_num) (by norm_num)
      _ ≤ (1.52 - 1.44) * (1.464092 ^ 2 / (1 / 4 + (1.44 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.44 1.464092 (by norm_num)
            ((log_ub _ 9 19 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.073802 := by norm_num
  have s4 : ∫ τ in (1.52 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.071945 := by
    calc ∫ τ in (1.52 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.6 - 1.52) * (Real.log ((1.52 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.52 : ℝ) ^ 2)) :=
          step_le 1.52 1.6 (by norm_num) (by norm_num)
      _ ≤ (1.6 - 1.52) * (1.517422 ^ 2 / (1 / 4 + (1.52 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.52 1.517422 (by norm_num)
            ((log_ub _ 16 35 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.071945 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.2 : ℝ) 1.28) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.28 : ℝ) 1.36)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.2 : ℝ) 1.36) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.36 : ℝ) 1.44)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.2 : ℝ) 1.44) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.44 : ℝ) 1.52)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.2 : ℝ) 1.52) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.52 : ℝ) 1.6)
  linarith [s0, s1, s2, s3, s4, e1, e2, e3, e4]

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [1.6, 2.1]: ∫ g ≤ 0.417;
the true value is 0.4109. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here 2026-11-22 by CLAUDE S7: left endpoint sums, n steps, using that g is antitone on
[0, ∞), with log bounds by `log_ub`. -/
theorem piece_08 :
    ∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.417 := by
  have s0 : ∫ τ in (1.6 : ℝ)..1.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.043899 := by
    calc ∫ τ in (1.6 : ℝ)..1.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.65 - 1.6) * (Real.log ((1.6 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.6 : ℝ) ^ 2)) :=
          step_le 1.6 1.65 (by norm_num) (by norm_num)
      _ ≤ (1.65 - 1.6) * (1.570699 ^ 2 / (1 / 4 + (1.6 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.6 1.570699 (by norm_num)
            ((log_ub _ 15 34 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.043899 := by norm_num
  have s1 : ∫ τ in (1.65 : ℝ)..1.7, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.043274 := by
    calc ∫ τ in (1.65 : ℝ)..1.7, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.7 - 1.65) * (Real.log ((1.65 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.65 : ℝ) ^ 2)) :=
          step_le 1.65 1.7 (by norm_num) (by norm_num)
      _ ≤ (1.7 - 1.65) * (1.603932 ^ 2 / (1 / 4 + (1.65 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.65 1.603932 (by norm_num)
            ((log_ub _ 16 37 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.043274 := by norm_num
  have s2 : ∫ τ in (1.7 : ℝ)..1.75, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.042675 := by
    calc ∫ τ in (1.7 : ℝ)..1.75, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.75 - 1.7) * (Real.log ((1.7 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.7 : ℝ) ^ 2)) :=
          step_le 1.7 1.75 (by norm_num) (by norm_num)
      _ ≤ (1.75 - 1.7) * (1.637063 ^ 2 / (1 / 4 + (1.7 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.7 1.637063 (by norm_num)
            ((log_ub _ 11 26 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.042675 := by norm_num
  have s3 : ∫ τ in (1.75 : ℝ)..1.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.042106 := by
    calc ∫ τ in (1.75 : ℝ)..1.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.8 - 1.75) * (Real.log ((1.75 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.75 : ℝ) ^ 2)) :=
          step_le 1.75 1.8 (by norm_num) (by norm_num)
      _ ≤ (1.8 - 1.75) * (1.670170 ^ 2 / (1 / 4 + (1.75 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.75 1.670170 (by norm_num)
            ((log_ub _ 5 12 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.042106 := by norm_num
  have s4 : ∫ τ in (1.8 : ℝ)..1.85, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.041548 := by
    calc ∫ τ in (1.8 : ℝ)..1.85, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.85 - 1.8) * (Real.log ((1.8 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.8 : ℝ) ^ 2)) :=
          step_le 1.8 1.85 (by norm_num) (by norm_num)
      _ ≤ (1.85 - 1.8) * (1.702942 ^ 2 / (1 / 4 + (1.8 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.8 1.702942 (by norm_num)
            ((log_ub _ 11 27 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.041548 := by norm_num
  have s5 : ∫ τ in (1.85 : ℝ)..1.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.041014 := by
    calc ∫ τ in (1.85 : ℝ)..1.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.9 - 1.85) * (Real.log ((1.85 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.85 : ℝ) ^ 2)) :=
          step_le 1.85 1.9 (by norm_num) (by norm_num)
      _ ≤ (1.9 - 1.85) * (1.735638 ^ 2 / (1 / 4 + (1.85 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.85 1.735638 (by norm_num)
            ((log_ub _ 2 5 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.041014 := by norm_num
  have s6 : ∫ τ in (1.9 : ℝ)..1.95, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.040499 := by
    calc ∫ τ in (1.9 : ℝ)..1.95, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (1.95 - 1.9) * (Real.log ((1.9 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.9 : ℝ) ^ 2)) :=
          step_le 1.9 1.95 (by norm_num) (by norm_num)
      _ ≤ (1.95 - 1.9) * (1.768197 ^ 2 / (1 / 4 + (1.9 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.9 1.768197 (by norm_num)
            ((log_ub _ 9 23 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.040499 := by norm_num
  have s7 : ∫ τ in (1.95 : ℝ)..2.0, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.039997 := by
    calc ∫ τ in (1.95 : ℝ)..2.0, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.0 - 1.95) * (Real.log ((1.95 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (1.95 : ℝ) ^ 2)) :=
          step_le 1.95 2.0 (by norm_num) (by norm_num)
      _ ≤ (2.0 - 1.95) * (1.800479 ^ 2 / (1 / 4 + (1.95 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 1.95 1.800479 (by norm_num)
            ((log_ub _ 5 13 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.039997 := by norm_num
  have s8 : ∫ τ in (2.0 : ℝ)..2.05, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.039511 := by
    calc ∫ τ in (2.0 : ℝ)..2.05, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.05 - 2.0) * (Real.log ((2.0 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.0 : ℝ) ^ 2)) :=
          step_le 2.0 2.05 (by norm_num) (by norm_num)
      _ ≤ (2.05 - 2.0) * (1.832585 ^ 2 / (1 / 4 + (2.0 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.0 1.832585 (by norm_num)
            ((log_ub _ 14 37 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.039511 := by norm_num
  have s9 : ∫ τ in (2.05 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.039038 := by
    calc ∫ τ in (2.05 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.1 - 2.05) * (Real.log ((2.05 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.05 : ℝ) ^ 2)) :=
          step_le 2.05 2.1 (by norm_num) (by norm_num)
      _ ≤ (2.1 - 2.05) * (1.864487 ^ 2 / (1 / 4 + (2.05 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.05 1.864487 (by norm_num)
            ((log_ub _ 13 35 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.039038 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.65) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.65 : ℝ) 1.7)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.7) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.7 : ℝ) 1.75)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.75) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.75 : ℝ) 1.8)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.8) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.8 : ℝ) 1.85)
  have e5 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.85) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.85 : ℝ) 1.9)
  have e6 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.9) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.9 : ℝ) 1.95)
  have e7 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 1.95) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.95 : ℝ) 2.0)
  have e8 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 2.0) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.0 : ℝ) 2.05)
  have e9 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (1.6 : ℝ) 2.05) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.05 : ℝ) 2.1)
  linarith [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [2.1, 2.8]: ∫ g ≤ 0.506;
the true value is 0.4995. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here 2026-11-22 by CLAUDE S7: left endpoint sums, n steps, using that g is antitone on
[0, ∞), with log bounds by `log_ub`. -/
theorem piece_09 :
    ∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.506 := by
  have s0 : ∫ τ in (2.1 : ℝ)..2.17, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.054008 := by
    calc ∫ τ in (2.1 : ℝ)..2.17, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.17 - 2.1) * (Real.log ((2.1 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.1 : ℝ) ^ 2)) :=
          step_le 2.1 2.17 (by norm_num) (by norm_num)
      _ ≤ (2.17 - 2.1) * (1.896137 ^ 2 / (1 / 4 + (2.1 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.1 1.896137 (by norm_num)
            ((log_ub _ 15 41 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.054008 := by norm_num
  have s1 : ∫ τ in (2.17 : ℝ)..2.24, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.053129 := by
    calc ∫ τ in (2.17 : ℝ)..2.24, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.24 - 2.17) * (Real.log ((2.17 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.17 : ℝ) ^ 2)) :=
          step_le 2.17 2.24 (by norm_num) (by norm_num)
      _ ≤ (2.24 - 2.17) * (1.940023 ^ 2 / (1 / 4 + (2.17 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.17 1.940023 (by norm_num)
            ((log_ub _ 5 14 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.053129 := by norm_num
  have s2 : ∫ τ in (2.24 : ℝ)..2.31, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.052280 := by
    calc ∫ τ in (2.24 : ℝ)..2.31, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.31 - 2.24) * (Real.log ((2.24 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.24 : ℝ) ^ 2)) :=
          step_le 2.24 2.31 (by norm_num) (by norm_num)
      _ ≤ (2.31 - 2.24) * (1.983458 ^ 2 / (1 / 4 + (2.24 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.24 1.983458 (by norm_num)
            ((log_ub _ 7 20 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.052280 := by norm_num
  have s3 : ∫ τ in (2.31 : ℝ)..2.38, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.051453 := by
    calc ∫ τ in (2.31 : ℝ)..2.38, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.38 - 2.31) * (Real.log ((2.31 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.31 : ℝ) ^ 2)) :=
          step_le 2.31 2.38 (by norm_num) (by norm_num)
      _ ≤ (2.38 - 2.31) * (2.026318 ^ 2 / (1 / 4 + (2.31 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.31 2.026318 (by norm_num)
            ((log_ub _ 13 38 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.051453 := by norm_num
  have s4 : ∫ τ in (2.38 : ℝ)..2.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.050653 := by
    calc ∫ τ in (2.38 : ℝ)..2.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.45 - 2.38) * (Real.log ((2.38 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.38 : ℝ) ^ 2)) :=
          step_le 2.38 2.45 (by norm_num) (by norm_num)
      _ ≤ (2.45 - 2.38) * (2.068742 ^ 2 / (1 / 4 + (2.38 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.38 2.068742 (by norm_num)
            ((log_ub _ 1 3 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.050653 := by norm_num
  have s5 : ∫ τ in (2.45 : ℝ)..2.52, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.049892 := by
    calc ∫ τ in (2.45 : ℝ)..2.52, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.52 - 2.45) * (Real.log ((2.45 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.45 : ℝ) ^ 2)) :=
          step_le 2.45 2.52 (by norm_num) (by norm_num)
      _ ≤ (2.52 - 2.45) * (2.111005 ^ 2 / (1 / 4 + (2.45 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.45 2.111005 (by norm_num)
            ((log_ub _ 1 3 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.049892 := by norm_num
  have s6 : ∫ τ in (2.52 : ℝ)..2.59, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.049109 := by
    calc ∫ τ in (2.52 : ℝ)..2.59, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.59 - 2.52) * (Real.log ((2.52 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.52 : ℝ) ^ 2)) :=
          step_le 2.52 2.59 (by norm_num) (by norm_num)
      _ ≤ (2.59 - 2.52) * (2.151856 ^ 2 / (1 / 4 + (2.52 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.52 2.151856 (by norm_num)
            ((log_ub _ 10 31 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.049109 := by norm_num
  have s7 : ∫ τ in (2.59 : ℝ)..2.66, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.048364 := by
    calc ∫ τ in (2.59 : ℝ)..2.66, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.66 - 2.59) * (Real.log ((2.59 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.59 : ℝ) ^ 2)) :=
          step_le 2.59 2.66 (by norm_num) (by norm_num)
      _ ≤ (2.66 - 2.59) * (2.192576 ^ 2 / (1 / 4 + (2.59 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.59 2.192576 (by norm_num)
            ((log_ub _ 6 19 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.048364 := by norm_num
  have s8 : ∫ τ in (2.66 : ℝ)..2.73, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.047637 := by
    calc ∫ τ in (2.66 : ℝ)..2.73, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.73 - 2.66) * (Real.log ((2.66 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.66 : ℝ) ^ 2)) :=
          step_le 2.66 2.73 (by norm_num) (by norm_num)
      _ ≤ (2.73 - 2.66) * (2.232766 ^ 2 / (1 / 4 + (2.66 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.66 2.232766 (by norm_num)
            ((log_ub _ 9 29 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.047637 := by norm_num
  have s9 : ∫ τ in (2.73 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.046931 := by
    calc ∫ τ in (2.73 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.8 - 2.73) * (Real.log ((2.73 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.73 : ℝ) ^ 2)) :=
          step_le 2.73 2.8 (by norm_num) (by norm_num)
      _ ≤ (2.8 - 2.73) * (2.272512 ^ 2 / (1 / 4 + (2.73 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.73 2.272512 (by norm_num)
            ((log_ub _ 11 36 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.046931 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.17) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.17 : ℝ) 2.24)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.24) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.24 : ℝ) 2.31)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.31) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.31 : ℝ) 2.38)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.38) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.38 : ℝ) 2.45)
  have e5 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.45) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.45 : ℝ) 2.52)
  have e6 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.52) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.52 : ℝ) 2.59)
  have e7 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.59) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.59 : ℝ) 2.66)
  have e8 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.66) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.66 : ℝ) 2.73)
  have e9 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.1 : ℝ) 2.73) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.73 : ℝ) 2.8)
  linarith [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [2.8, 3.8]: ∫ g ≤ 0.604;
the true value is 0.5970. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds.
PROVED here 2026-11-22 by CLAUDE S7: left endpoint sums, n steps, using that g is antitone on
[0, ∞), with log bounds by `log_ub`. -/
theorem piece_10 :
    ∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.604 := by
  have s0 : ∫ τ in (2.8 : ℝ)..2.85, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.033024 := by
    calc ∫ τ in (2.8 : ℝ)..2.85, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.85 - 2.8) * (Real.log ((2.8 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.8 : ℝ) ^ 2)) :=
          step_le 2.8 2.85 (by norm_num) (by norm_num)
      _ ≤ (2.85 - 2.8) * (2.311547 ^ 2 / (1 / 4 + (2.8 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.8 2.311547 (by norm_num)
            ((log_ub _ 3 10 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.033024 := by norm_num
  have s1 : ∫ τ in (2.85 : ℝ)..2.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.032677 := by
    calc ∫ τ in (2.85 : ℝ)..2.9, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.9 - 2.85) * (Real.log ((2.85 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.85 : ℝ) ^ 2)) :=
          step_le 2.85 2.9 (by norm_num) (by norm_num)
      _ ≤ (2.9 - 2.85) * (2.339159 ^ 2 / (1 / 4 + (2.85 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.85 2.339159 (by norm_num)
            ((log_ub _ 8 27 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.032677 := by norm_num
  have s2 : ∫ τ in (2.9 : ℝ)..2.95, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.032335 := by
    calc ∫ τ in (2.9 : ℝ)..2.95, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (2.95 - 2.9) * (Real.log ((2.9 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.9 : ℝ) ^ 2)) :=
          step_le 2.9 2.95 (by norm_num) (by norm_num)
      _ ≤ (2.95 - 2.9) * (2.366517 ^ 2 / (1 / 4 + (2.9 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.9 2.366517 (by norm_num)
            ((log_ub _ 12 41 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.032335 := by norm_num
  have s3 : ∫ τ in (2.95 : ℝ)..3.0, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.031998 := by
    calc ∫ τ in (2.95 : ℝ)..3.0, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.0 - 2.95) * (Real.log ((2.95 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (2.95 : ℝ) ^ 2)) :=
          step_le 2.95 3.0 (by norm_num) (by norm_num)
      _ ≤ (3.0 - 2.95) * (2.393573 ^ 2 / (1 / 4 + (2.95 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 2.95 2.393573 (by norm_num)
            ((log_ub _ 11 38 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.031998 := by norm_num
  have s4 : ∫ τ in (3.0 : ℝ)..3.05, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.031667 := by
    calc ∫ τ in (3.0 : ℝ)..3.05, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.05 - 3.0) * (Real.log ((3.0 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.0 : ℝ) ^ 2)) :=
          step_le 3.0 3.05 (by norm_num) (by norm_num)
      _ ≤ (3.05 - 3.0) * (2.420400 ^ 2 / (1 / 4 + (3.0 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.0 2.420400 (by norm_num)
            ((log_ub _ 2 7 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.031667 := by norm_num
  have s5 : ∫ τ in (3.05 : ℝ)..3.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.031341 := by
    calc ∫ τ in (3.05 : ℝ)..3.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.1 - 3.05) * (Real.log ((3.05 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.05 : ℝ) ^ 2)) :=
          step_le 3.05 3.1 (by norm_num) (by norm_num)
      _ ≤ (3.1 - 3.05) * (2.446939 ^ 2 / (1 / 4 + (3.05 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.05 2.446939 (by norm_num)
            ((log_ub _ 15 53 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.031341 := by norm_num
  have s6 : ∫ τ in (3.1 : ℝ)..3.15, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.031018 := by
    calc ∫ τ in (3.1 : ℝ)..3.15, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.15 - 3.1) * (Real.log ((3.1 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.1 : ℝ) ^ 2)) :=
          step_le 3.1 3.15 (by norm_num) (by norm_num)
      _ ≤ (3.15 - 3.1) * (2.473191 ^ 2 / (1 / 4 + (3.1 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.1 2.473191 (by norm_num)
            ((log_ub _ 7 25 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.031018 := by norm_num
  have s7 : ∫ τ in (3.15 : ℝ)..3.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.030701 := by
    calc ∫ τ in (3.15 : ℝ)..3.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.2 - 3.15) * (Real.log ((3.15 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.15 : ℝ) ^ 2)) :=
          step_le 3.15 3.2 (by norm_num) (by norm_num)
      _ ≤ (3.2 - 3.15) * (2.499217 ^ 2 / (1 / 4 + (3.15 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.15 2.499217 (by norm_num)
            ((log_ub _ 5 18 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.030701 := by norm_num
  have s8 : ∫ τ in (3.2 : ℝ)..3.25, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.030388 := by
    calc ∫ τ in (3.2 : ℝ)..3.25, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.25 - 3.2) * (Real.log ((3.2 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.2 : ℝ) ^ 2)) :=
          step_le 3.2 3.25 (by norm_num) (by norm_num)
      _ ≤ (3.25 - 3.2) * (2.524929 ^ 2 / (1 / 4 + (3.2 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.2 2.524929 (by norm_num)
            ((log_ub _ 14 51 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.030388 := by norm_num
  have s9 : ∫ τ in (3.25 : ℝ)..3.3, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.030083 := by
    calc ∫ τ in (3.25 : ℝ)..3.3, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.3 - 3.25) * (Real.log ((3.25 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.25 : ℝ) ^ 2)) :=
          step_le 3.25 3.3 (by norm_num) (by norm_num)
      _ ≤ (3.3 - 3.25) * (2.550541 ^ 2 / (1 / 4 + (3.25 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.25 2.550541 (by norm_num)
            ((log_ub _ 3 11 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.030083 := by norm_num
  have s10 : ∫ τ in (3.3 : ℝ)..3.35, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.029776 := by
    calc ∫ τ in (3.3 : ℝ)..3.35, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.35 - 3.3) * (Real.log ((3.3 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.3 : ℝ) ^ 2)) :=
          step_le 3.3 3.35 (by norm_num) (by norm_num)
      _ ≤ (3.35 - 3.3) * (2.575666 ^ 2 / (1 / 4 + (3.3 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.3 2.575666 (by norm_num)
            ((log_ub _ 7 26 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.029776 := by norm_num
  have s11 : ∫ τ in (3.35 : ℝ)..3.4, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.029477 := by
    calc ∫ τ in (3.35 : ℝ)..3.4, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.4 - 3.35) * (Real.log ((3.35 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.35 : ℝ) ^ 2)) :=
          step_le 3.35 3.4 (by norm_num) (by norm_num)
      _ ≤ (3.4 - 3.35) * (2.600655 ^ 2 / (1 / 4 + (3.35 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.35 2.600655 (by norm_num)
            ((log_ub _ 4 15 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.029477 := by norm_num
  have s12 : ∫ τ in (3.4 : ℝ)..3.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.029182 := by
    calc ∫ τ in (3.4 : ℝ)..3.45, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.45 - 3.4) * (Real.log ((3.4 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.4 : ℝ) ^ 2)) :=
          step_le 3.4 3.45 (by norm_num) (by norm_num)
      _ ≤ (3.45 - 3.4) * (2.625406 ^ 2 / (1 / 4 + (3.4 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.4 2.625406 (by norm_num)
            ((log_ub _ 14 53 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.029182 := by norm_num
  have s13 : ∫ τ in (3.45 : ℝ)..3.5, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.028893 := by
    calc ∫ τ in (3.45 : ℝ)..3.5, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.5 - 3.45) * (Real.log ((3.45 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.45 : ℝ) ^ 2)) :=
          step_le 3.45 3.5 (by norm_num) (by norm_num)
      _ ≤ (3.5 - 3.45) * (2.649954 ^ 2 / (1 / 4 + (3.45 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.45 2.649954 (by norm_num)
            ((log_ub _ 11 42 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.028893 := by norm_num
  have s14 : ∫ τ in (3.5 : ℝ)..3.55, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.028605 := by
    calc ∫ τ in (3.5 : ℝ)..3.55, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.55 - 3.5) * (Real.log ((3.5 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.5 : ℝ) ^ 2)) :=
          step_le 3.5 3.55 (by norm_num) (by norm_num)
      _ ≤ (3.55 - 3.5) * (2.674150 ^ 2 / (1 / 4 + (3.5 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.5 2.674150 (by norm_num)
            ((log_ub _ 7 27 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.028605 := by norm_num
  have s15 : ∫ τ in (3.55 : ℝ)..3.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.028323 := by
    calc ∫ τ in (3.55 : ℝ)..3.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.6 - 3.55) * (Real.log ((3.55 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.55 : ℝ) ^ 2)) :=
          step_le 3.55 3.6 (by norm_num) (by norm_num)
      _ ≤ (3.6 - 3.55) * (2.698199 ^ 2 / (1 / 4 + (3.55 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.55 2.698199 (by norm_num)
            ((log_ub _ 9 35 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.028323 := by norm_num
  have s16 : ∫ τ in (3.6 : ℝ)..3.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.028044 := by
    calc ∫ τ in (3.6 : ℝ)..3.65, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.65 - 3.6) * (Real.log ((3.6 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.6 : ℝ) ^ 2)) :=
          step_le 3.6 3.65 (by norm_num) (by norm_num)
      _ ≤ (3.65 - 3.6) * (2.721962 ^ 2 / (1 / 4 + (3.6 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.6 2.721962 (by norm_num)
            ((log_ub _ 14 55 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.028044 := by norm_num
  have s17 : ∫ τ in (3.65 : ℝ)..3.7, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.027777 := by
    calc ∫ τ in (3.65 : ℝ)..3.7, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.7 - 3.65) * (Real.log ((3.65 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.65 : ℝ) ^ 2)) :=
          step_le 3.65 3.7 (by norm_num) (by norm_num)
      _ ≤ (3.7 - 3.65) * (2.745870 ^ 2 / (1 / 4 + (3.65 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.65 2.745870 (by norm_num)
            ((log_ub _ 1 4 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.027777 := by norm_num
  have s18 : ∫ τ in (3.7 : ℝ)..3.75, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.027499 := by
    calc ∫ τ in (3.7 : ℝ)..3.75, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.75 - 3.7) * (Real.log ((3.7 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.7 : ℝ) ^ 2)) :=
          step_le 3.7 3.75 (by norm_num) (by norm_num)
      _ ≤ (3.75 - 3.7) * (2.768839 ^ 2 / (1 / 4 + (3.7 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.7 2.768839 (by norm_num)
            ((log_ub _ 1 4 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.027499 := by norm_num
  have s19 : ∫ τ in (3.75 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.027235 := by
    calc ∫ τ in (3.75 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)
        ≤ (3.8 - 3.75) * (Real.log ((3.75 : ℝ) ^ 2 + 9 / 4) ^ 2 / (1 / 4 + (3.75 : ℝ) ^ 2)) :=
          step_le 3.75 3.8 (by norm_num) (by norm_num)
      _ ≤ (3.8 - 3.75) * (2.792120 ^ 2 / (1 / 4 + (3.75 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (g_le 3.75 2.792120 (by norm_num)
            ((log_ub _ 1 4 (by norm_num) (by norm_num)).trans (by norm_num))) (by norm_num)
      _ ≤ 0.027235 := by norm_num
  have e1 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 2.85) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.85 : ℝ) 2.9)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 2.9) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.9 : ℝ) 2.95)
  have e3 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 2.95) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.95 : ℝ) 3.0)
  have e4 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.0) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.0 : ℝ) 3.05)
  have e5 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.05) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.05 : ℝ) 3.1)
  have e6 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.1) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.1 : ℝ) 3.15)
  have e7 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.15) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.15 : ℝ) 3.2)
  have e8 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.2) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.2 : ℝ) 3.25)
  have e9 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.25) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.25 : ℝ) 3.3)
  have e10 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.3) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.3 : ℝ) 3.35)
  have e11 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.35) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.35 : ℝ) 3.4)
  have e12 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.4) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.4 : ℝ) 3.45)
  have e13 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.45) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.45 : ℝ) 3.5)
  have e14 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.5) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.5 : ℝ) 3.55)
  have e15 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.55) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.55 : ℝ) 3.6)
  have e16 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.6) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.6 : ℝ) 3.65)
  have e17 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.65) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.65 : ℝ) 3.7)
  have e18 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.7) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.7 : ℝ) 3.75)
  have e19 := intervalIntegral.integral_add_adjacent_intervals (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (2.8 : ℝ) 3.75) (g_cont.intervalIntegrable (μ := MeasureTheory.volume) (3.75 : ℝ) 3.8)
  linarith [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19]

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [3.8, 5.2]: ∫ g ≤ 0.675;
the true value is 0.6647. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_11 :
    ∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.675 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [5.2, 7.2]: ∫ g ≤ 0.728;
the true value is 0.7145. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_12 :
    ∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.728 := by
  sorry

/-- LEAF: P0014 page 35, the integral after display 4.12, subinterval [7.2, 10]: ∫ g ≤ 0.732;
the true value is 0.7147. Method: the trapezoid rule (b - a)(g(a) + g(b))/2, an upper bound because g is convex on [0.289, ∞), with rational bounds for the values of
log(τ² + 9/4) needed. Class EASY: one interval, an inequality chain and log bounds. -/
theorem piece_13 :
    ∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2) ≤ 0.732 := by
  sorry

/-- P0014 page 35: the sum of the subinterval bounds of this file, 4.044. -/
theorem sum_high :
    (∫ τ in (1.2 : ℝ)..1.6, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (1.6 : ℝ)..2.1, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.1 : ℝ)..2.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (2.8 : ℝ)..3.8, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (3.8 : ℝ)..5.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (5.2 : ℝ)..7.2, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) +
      (∫ τ in (7.2 : ℝ)..10, Real.log (τ ^ 2 + 9 / 4) ^ 2 / (1 / 4 + τ ^ 2)) ≤ 4.044 := by
  linarith [piece_07, piece_08, piece_09, piece_10, piece_11, piece_12, piece_13]

end LeanLab.HelfgottMajor.Prep1121VIPiecesHigh

#print axioms LeanLab.HelfgottMajor.Prep1121VIPiecesHigh.piece_07
#print axioms LeanLab.HelfgottMajor.Prep1121VIPiecesHigh.piece_08
#print axioms LeanLab.HelfgottMajor.Prep1121VIPiecesHigh.piece_09
#print axioms LeanLab.HelfgottMajor.Prep1121VIPiecesHigh.piece_10
