/-
The periodic prime second moment on arbitrary scales in P0079 page 10.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.PrimeMoment353
import LeanLab.LZPowersOfTwo.Decomp353d
import LeanLab.LZPowersOfTwo.TailSummation418

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5. Real logarithmic weights make the prime-sum norm even. -/
theorem primeSum_norm_neg418 (ε X α : ℝ) :
    ‖primeSum293 ε X (-α)‖ = ‖primeSum293 ε X α‖ := by
  have hc : primeSum293 ε X (-α) = starRingEnd ℂ (primeSum293 ε X α) := by
    simp only [primeSum293, mul_neg, character_neg353, map_sum, map_mul, Complex.conj_ofReal]
  rw [hc, Complex.norm_conj]

/-- P0079 page 10, Section 5. The kernel-weighted prime moment is even. -/
theorem primeMoment_even418 (l η ε X α : ℝ) :
    primeMoment353 l η ε X (-α) = primeMoment353 l η ε X α := by
  simp only [primeMoment353, mul_neg, primeSum_norm_neg418, kernel293, Real.sinc_neg]

/-- P0079 page 10, Section 5. Replacing lambda by its absolute value preserves the moment. -/
theorem primeMoment_abs418 (l η ε X α : ℝ) :
    primeMoment353 |l| η ε X α = primeMoment353 l η ε X α := by
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
  · rw [abs_of_nonpos hl]
    simp only [primeMoment353, neg_mul, primeSum_norm_neg418]

/-- P0079 page 10, Section 5, the change of variable before the unit-interval sum.
A positive lambda changes the period to its reciprocal. -/
theorem prime_second_moment_scaled418 (l ε X a : ℝ) (hl : 0 < l) :
    (∫ α in a..a + 1 / l, ‖primeSum293 ε X (l * α)‖ ^ 2) =
      (1 / l) * ∑ p ∈ (range (⌊X⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), (log p) ^ 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => ‖primeSum293 ε X t‖ ^ 2) hl.ne']
  rw [show l * (a + 1 / l) = l * a + 1 by field_simp]
  rw [prime_second_moment_unit353]
  simp only [inv_eq_one_div, smul_eq_mul]

/-- P0079 page 10, Section 5. Kernel decay bounds each interval of the scaled period. -/
theorem primeMoment_scaled_unit_le418 (l ε X η a : ℝ)
    (hl : 0 < l) (hX : 2 ≤ X) (ha : 0 < a) :
    (∫ α in a..a + 1 / l, primeMoment353 l η ε X α) ≤
      ((1 / Real.pi ^ 2) / a ^ 2) * (1 / l) * (log 4 * X * log X) := by
  have hk : ∀ α ∈ Set.Icc a (a + 1 / l),
      kernel293 η α ≤ (1 / Real.pi ^ 2) / a ^ 2 := by
    intro α hα
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    have hsq : a ^ 2 ≤ α ^ 2 := by nlinarith [hα.1]
    nlinarith [kernel_mul_sq_le293 η α, kernel_nonneg293 η α]
  have hs : Continuous (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  have hker : Continuous (kernel293 η) := by unfold kernel293; fun_prop
  calc
    _ ≤ ∫ α in a..a + 1 / l,
        ((1 / Real.pi ^ 2) / a ^ 2) * ‖primeSum293 ε X (l * α)‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith [one_div_pos.mpr hl])
        ((hs.mul hker).intervalIntegrable _ _)
        ((hs.const_mul _).intervalIntegrable _ _)
      intro α hα
      change ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η α ≤ _
      calc
        _ ≤ ‖primeSum293 ε X (l * α)‖ ^ 2 * ((1 / Real.pi ^ 2) / a ^ 2) :=
          mul_le_mul_of_nonneg_left (hk α hα) (sq_nonneg _)
        _ = _ := mul_comm _ _
    _ = ((1 / Real.pi ^ 2) / a ^ 2) * (1 / l) *
        (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul, prime_second_moment_scaled418 l ε X a hl,
        prime_second_moment353]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_second_moment_le353 ε X hX) (by positivity)

/-- P0079 page 10, Section 5. Summing the scaled unit intervals bounds the positive tail. -/
theorem primeMoment_positive_tail418 (l ε X η R : ℝ)
    (hl : 0 < l) (hX : 2 ≤ X) (hR : 1 / l ≤ R) :
    (∫ α in Set.Ioi R, primeMoment353 l η ε X α) ≤
      (2 / Real.pi ^ 2) * (log 4 * X * log X) / R := by
  let B := log 4 * X * log X
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (log_nonneg (by norm_num)) (by linarith))
      (log_nonneg (by linarith))
  have hh : 0 < 1 / l := one_div_pos.mpr hl
  have hR0 : 0 < R := hh.trans_le hR
  have hinterval (n : ℕ) :
      (∫ α in (R + (n : ℝ) * (1 / l))..(R + ((n + 1 : ℕ) : ℝ) * (1 / l)),
        primeMoment353 l η ε X α) ≤
          ((1 / Real.pi ^ 2) * (1 / l) * B) / (R + (n : ℝ) * (1 / l)) ^ 2 := by
    have hn : 0 ≤ (n : ℝ) * (1 / l) := mul_nonneg (Nat.cast_nonneg _) hh.le
    have ha : 0 < R + (n : ℝ) * (1 / l) := by linarith
    have H := primeMoment_scaled_unit_le418 l ε X η (R + (n : ℝ) * (1 / l)) hl hX ha
    have he : R + ((n + 1 : ℕ) : ℝ) * (1 / l) =
        (R + (n : ℝ) * (1 / l)) + 1 / l := by push_cast; ring
    rw [he]
    convert H using 1
    dsimp [B]
    ring
  calc
    _ ≤ 2 * ((1 / Real.pi ^ 2) * (1 / l) * B) / ((1 / l) * R) :=
      integral_tail_of_interval_bounds418 _ (primeMoment_integrable353 l η ε X)
        R (1 / l) ((1 / Real.pi ^ 2) * (1 / l) * B) hh hR (by positivity) hinterval
    _ = _ := by dsimp [B]; field_simp

/-- P0079 page 10, Section 5. Both tails have an explicit bound for every nonzero lambda. -/
theorem primeMoment_tail418 (l ε X η R : ℝ)
    (hl : l ≠ 0) (hX : 2 ≤ X) (hR : 1 / |l| ≤ R) :
    (∫ α in {α : ℝ | R < |α|}, primeMoment353 l η ε X α) ≤
      (4 / Real.pi ^ 2) * (log 4 * X * log X) / R := by
  have habs : 0 < |l| := abs_pos.mpr hl
  have hR0 : 0 ≤ R := (one_div_pos.mpr habs).le.trans hR
  rw [integral_abs_tail_even418 _ (primeMoment_integrable353 l η ε X)
    (primeMoment_even418 l η ε X) R hR0]
  have H := primeMoment_positive_tail418 |l| ε X η R habs hX hR
  simp_rw [primeMoment_abs418] at H
  calc
    _ ≤ 2 * ((2 / Real.pi ^ 2) * (log 4 * X * log X) / R) := by linarith
    _ = _ := by ring

end LeanLab.LZPowersOfTwo
