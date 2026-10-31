/-
AI wrote the Lean code. Codex task04, 2026-10-22.
Keep the exact Chebyshev coefficient throughout Abel summation.
All formulas are derived from local proofs. Goldbach is open.
-/
import LeanLab.ChebyshevExplicit.PiUpperAsymptotic

open Real Finset Chebyshev

noncomputable section
namespace LeanLab.ChebyshevExplicit

/-- The strongest quadratic theta bound on a real interval. -/
theorem theta_le_chebyshev30_quadratic_real {x : ℝ} (hx : 2 ≤ x) :
    θ x ≤ (6 / 5 * A) * x + 5 / (4 * log 6) * log x ^ 2 + 5 / 4 * log x := by
  have hf1 : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hfR : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hf1
  have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hl0 : 0 ≤ log (⌊x⌋₊ : ℝ) := log_nonneg hfR
  have hl : log (⌊x⌋₊ : ℝ) ≤ log x := log_le_log (by linarith) hfx
  have hs := pow_le_pow_left₀ hl0 hl 2
  have hb : 0 ≤ (5 : ℝ) / (4 * log 6) := by positivity
  have hbs := mul_le_mul_of_nonneg_left hs hb
  calc
    θ x = θ (⌊x⌋₊ : ℝ) := theta_eq_theta_coe_floor x
    _ ≤ ψ (⌊x⌋₊ : ℝ) := theta_le_psi _
    _ ≤ (6 / 5 * A) * (⌊x⌋₊ : ℝ) + 5 / (4 * log 6) * log (⌊x⌋₊ : ℝ) ^ 2
        + 5 / 4 * log (⌊x⌋₊ : ℝ) := psi_le_chebyshev30_quadratic _
    _ ≤ _ := by nlinarith [A_pos]

/-- Integrate the strongest theta error, leaving the leading integral explicit. -/
theorem integral_theta_le_chebyshev30_quadratic {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, θ t / (t * log t ^ 2) ≤
      (6 / 5 * A) * (∫ t in 2..x, 1 / log t ^ 2)
        + 5 / (4 * log 6) * (log x - log 2)
        + 5 / 4 * (log (log x) - log (log 2)) := by
  have h6 : log (6 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  have hi1 := intervalIntegrable_one_div_log_sq (by norm_num : (1 : ℝ) < 2)
    (by linarith : 1 < x)
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact (continuousAt_id.inv₀ (by dsimp; linarith [ht.1])).continuousWithinAt
  have hi3 : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ / log t)
      MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlt : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  calc
    _ ≤ ∫ t in 2..x, (6 / 5 * A) * (1 / log t ^ 2)
        + 5 / (4 * log 6) * t⁻¹ + 5 / 4 * (t⁻¹ / log t) := by
      refine intervalIntegral.integral_mono_on hx ?_
        (((hi1.const_mul _).add (hi2.const_mul _)).add (hi3.const_mul _)) ?_
      · rw [intervalIntegrable_iff, Set.uIoc_of_le hx,
          ← integrableOn_Icc_iff_integrableOn_Ioc]
        exact integrableOn_theta_div_id_mul_log_sq x
      · intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        have hlt : 0 < log t := log_pos (by linarith [ht.1])
        calc θ t / (t * log t ^ 2)
            ≤ ((6 / 5 * A) * t + 5 / (4 * log 6) * log t ^ 2 + 5 / 4 * log t)
                / (t * log t ^ 2) :=
              div_le_div_of_nonneg_right (theta_le_chebyshev30_quadratic_real ht.1)
                (by positivity)
          _ = _ := by field_simp
    _ = _ := by
      rw [intervalIntegral.integral_add ((hi1.const_mul _).add (hi2.const_mul _))
          (hi3.const_mul _),
        intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [integral_inv_of_pos (by norm_num) (by linarith),
        integral_inv_div_log (by norm_num) (by linarith),
        log_div (by linarith : x ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]

/-- Abel summation with the strongest error and an unevaluated leading integral. -/
theorem pi_le_chebyshev30_integral {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (6 / 5 * A) * x / log x + (6 / 5 * A) * (∫ t in 2..x, 1 / log t ^ 2)
        + 5 / (2 * log 6) * log x - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by
  have hl : 0 < log x := log_pos (by linarith)
  have h6 : log (6 : ℝ) ≠ 0 := (log_pos (by norm_num)).ne'
  calc
    _ = θ x / log x + ∫ t in 2..x, θ t / (t * log t ^ 2) :=
      primeCounting_eq_theta_div_log_add_integral hx
    _ ≤ ((6 / 5 * A) * x + 5 / (4 * log 6) * log x ^ 2 + 5 / 4 * log x) / log x
        + ((6 / 5 * A) * (∫ t in 2..x, 1 / log t ^ 2)
          + 5 / (4 * log 6) * (log x - log 2)
          + 5 / 4 * (log (log x) - log (log 2))) :=
      add_le_add (div_le_div_of_nonneg_right (theta_le_chebyshev30_quadratic_real hx) hl.le)
        (integral_theta_le_chebyshev30_quadratic hx)
    _ = _ := by field_simp; ring

/-- The square-root split with the strongest smaller error polynomial. -/
theorem pi_le_chebyshev30_quadratic_real {x : ℝ} (hx : 4 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (6 / 5 * A) * x / log x + (24 / 5 * A) * x / log x ^ 2
        + (6 / 5 * A) * x.sqrt / log 2 ^ 2 + 5 / (2 * log 6) * log x
        - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by
  have hA := A_pos
  have h := pi_le_chebyshev30_integral (by linarith : 2 ≤ x)
  have hj := mul_le_mul_of_nonneg_left (integral_one_div_log_sq_le hx)
    (by positivity : (0 : ℝ) ≤ (6 / 5 * A))
  calc
    _ ≤ (6 / 5 * A) * x / log x + (6 / 5 * A) * (4 * x / log x ^ 2 + x.sqrt / log 2 ^ 2)
        + 5 / (2 * log 6) * log x - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by linarith
    _ = _ := by ring

/-- A fully explicit pi bound for any valid selected split point. -/
theorem pi_le_chebyshev30_split {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (6 / 5 * A) * x / log x + (6 / 5 * A) * ((y - 2) / log 2 ^ 2 + (x - y) / log y ^ 2)
        + 5 / (2 * log 6) * log x - 5 / (4 * log 6) * log 2
        + 5 / 4 * (1 + log (log x) - log (log 2)) := by
  have hA := A_pos
  have h := pi_le_chebyshev30_integral (hy.trans hyx)
  have hj := mul_le_mul_of_nonneg_left (integral_one_div_log_sq_le_split hy hyx)
    (by positivity : (0 : ℝ) ≤ (6 / 5 * A))
  linarith
/-- Absorb the lower-order terms into a single reciprocal-log correction. -/
theorem pi_exp_le_chebyshev30_add_five_div (L : ℝ) (hL : 32 ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤ (6 / 5 * A + 5 / L) * exp L / L := by
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < exp L := exp_pos _
  have hs0 : 0 < exp (L / 2) := exp_pos _
  have hsquare : exp (L / 2) ^ 2 = exp L := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hsqrt : (exp L).sqrt = exp (L / 2) := by
    rw [← hsquare, sqrt_sq_eq_abs, abs_of_pos hs0]
  have he := pow_div_factorial_le_exp L hL0.le 6
  norm_num at he
  have hse := pow_div_factorial_le_exp (L / 2) (by linarith : 0 ≤ L / 2) 6
  norm_num [div_pow] at hse
  have hL4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 4
  have hL6a : (32 : ℝ) ^ 4 * L ^ 2 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL4 (sq_nonneg L)
    nlinarith only [h]
  have hLS : L ^ 2 ≤ (1 / 12 : ℝ) * exp (L / 2) := by
    norm_num at hL6a
    nlinarith only [hL6a, hse, sq_nonneg L]
  have hroot : exp (L / 2) * L ^ 2 ≤ (1 / 12 : ℝ) * exp L := by
    have h := mul_le_mul_of_nonneg_left hLS hs0.le
    nlinarith only [h, hsquare]
  have hL3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hL 3
  have hL6b : (32 : ℝ) ^ 3 * L ^ 3 ≤ L ^ 6 := by
    have h := mul_le_mul_of_nonneg_right hL3 (by positivity : 0 ≤ L ^ 3)
    nlinarith only [h]
  have hLcube : L ^ 3 ≤ (1 / 30 : ℝ) * exp L := by
    norm_num at hL6b
    nlinarith only [hL6b, he, (show 0 ≤ L ^ 3 by positivity)]
  have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2 : (2 / 3 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hlog2sq : (4 / 9 : ℝ) ≤ log 2 ^ 2 := by
    nlinarith only [hlog2, sq_nonneg (log (2 : ℝ) - 2 / 3)]
  have h6pos : 0 < log (6 : ℝ) := log_pos (by norm_num)
  have h6raw : (5 : ℝ) / 2 * log 2 ≤ log 6 :=
    log_ge_of_pow 6 5 2 (by norm_num) (by norm_num)
  have h6lower : (5 / 3 : ℝ) ≤ log 6 := by linarith
  have hb2 : (5 : ℝ) / (2 * log 6) ≤ 3 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hinv2 : (1 : ℝ) / log 2 ≤ 3 / 2 := by
    rw [div_le_iff₀ hlog2pos]
    linarith
  have hll2 : -1 ≤ log (log (2 : ℝ)) := by
    have h := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / log 2)
    rw [log_div (by norm_num : (1 : ℝ) ≠ 0) hlog2pos.ne', log_one] at h
    linarith
  let E : ℝ := 5 / (2 * log 6) * L - 5 / (4 * log 6) * log 2
    + 5 / 4 * (1 + log L - log (log 2))
  have herr : E ≤ 3 * L := by
    have hbl := mul_le_mul_of_nonneg_right hb2 hL0.le
    have hneg : 0 ≤ (5 : ℝ) / (4 * log 6) * log 2 := by positivity
    have hlogL := log_le_sub_one_of_pos hL0
    dsimp [E]
    linarith
  have herrL : E * L ^ 2 ≤ 0.1 * exp L := by
    have h := mul_le_mul_of_nonneg_right herr (sq_nonneg L)
    nlinarith only [h, hLcube]
  have hrootTerm : 1.10556 * exp (L / 2) / log 2 ^ 2 * L ^ 2 ≤ 0.21 * exp L := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hlog2pos)]
    have h := mul_le_mul_of_nonneg_left hlog2sq
      (by positivity : 0 ≤ (0.21 : ℝ) * exp L)
    nlinarith only [hroot, h, hx0]
  have hc : 6 / 5 * A ≤ (1.10556 : ℝ) := by linarith [A_lt_09213]
  have hbound : (6 / 5 * A) * exp (L / 2) / log 2 ^ 2 ≤
      1.10556 * exp (L / 2) / log 2 ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hs0.le) (sq_nonneg _)
  have hsecBound : (24 / 5 * A) * exp L / L ^ 2 ≤ 4.42224 * exp L / L ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg L)
    exact mul_le_mul_of_nonneg_right (by linarith only [hc]) hx0.le
  have hp := pi_le_chebyshev30_quadratic_real (x := exp L) (by linarith [add_one_le_exp L])
  simp only [log_exp, hsqrt] at hp
  have hp' : (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤
      (6 / 5 * A) * exp L / L + 4.42224 * exp L / L ^ 2
        + 1.10556 * exp (L / 2) / log 2 ^ 2 + E := by
    dsimp [E]
    linarith only [hp, hbound, hsecBound]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hL0)).mp
  calc
    _ ≤ ((6 / 5 * A) * exp L / L + 4.42224 * exp L / L ^ 2
        + 1.10556 * exp (L / 2) / log 2 ^ 2 + E) * L ^ 2 :=
      mul_le_mul_of_nonneg_right hp' (sq_nonneg L)
    _ = (6 / 5 * A) * exp L * L + 4.42224 * exp L
        + 1.10556 * exp (L / 2) / log 2 ^ 2 * L ^ 2 + E * L ^ 2 := by
      field_simp [hL0.ne', hlog2pos.ne']
    _ ≤ (6 / 5 * A + 5 / L) * exp L / L * L ^ 2 := by
      have heq : (6 / 5 * A + 5 / L) * exp L / L * L ^ 2 =
          (6 / 5 * A) * exp L * L + 5 * exp L := by field_simp
      rw [heq]
      nlinarith only [hrootTerm, herrL, hx0]

/-- An explicit threshold for every coefficient above 6 / 5 * A. -/
theorem pi_exp_le_chebyshev30_add_epsilon (ε L : ℝ) (hε : 0 < ε)
    (hL : max 32 (5 / ε) ≤ L) :
    (Nat.primeCounting ⌊exp L⌋₊ : ℝ) ≤ (6 / 5 * A + ε) * exp L / L := by
  have h32 : (32 : ℝ) ≤ L := (le_max_left _ _).trans hL
  have hthreshold : 5 / ε ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hcorrection : 5 / L ≤ ε := by
    rw [div_le_iff₀ hL0]
    have h := (div_le_iff₀ hε).mp hthreshold
    nlinarith only [h]
  apply (pi_exp_le_chebyshev30_add_five_div L h32).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : 6 / 5 * A + 5 / L ≤ 6 / 5 * A + ε)
      (exp_pos L).le) hL0.le

end LeanLab.ChebyshevExplicit
