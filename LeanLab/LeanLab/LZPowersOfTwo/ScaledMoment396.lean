/-
P0079 page 10, Section 5, the change of variable in the prime moment.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.PrimeMoment353
import LeanLab.LZPowersOfTwo.Decomp353d
import LeanLab.LZPowersOfTwo.TailEstimate396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5. Reflecting a prime sum conjugates it,
so its norm is even. -/
theorem primeSum_norm_neg396 (ε X α : ℝ) :
    ‖primeSum293 ε X (-α)‖ = ‖primeSum293 ε X α‖ := by
  have H : primeSum293 ε X (-α) = starRingEnd ℂ (primeSum293 ε X α) := by
    unfold primeSum293
    simp only [map_sum, map_mul, Complex.conj_ofReal, mul_neg, character_neg353]
  rw [H]
  exact Complex.norm_conj _

/-- P0079 page 10, Section 5. The norm of the scaled prime sum depends
only on the absolute value of its real scale. -/
theorem primeSum_norm_abs396 (ε X l α : ℝ) :
    ‖primeSum293 ε X (|l| * α)‖ = ‖primeSum293 ε X (l * α)‖ := by
  by_cases hl : 0 ≤ l
  · rw [abs_of_nonneg hl]
  · rw [abs_of_neg (lt_of_not_ge hl), neg_mul, primeSum_norm_neg396]

/-- P0079 page 10, Section 5. Changing variables transports the exact
unit moment to an interval of length the reciprocal of absolute lambda. -/
theorem prime_scaled_moment_unit396 (ε X l a : ℝ) (hl : l ≠ 0) :
    (∫ α in a..a + 1 / |l|, ‖primeSum293 ε X (l * α)‖ ^ 2) =
      (1 / |l|) * ∑ p ∈ (range (⌊X⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), (log p) ^ 2 := by
  have hc : 0 < |l| := abs_pos.mpr hl
  simp_rw [← primeSum_norm_abs396 ε X l]
  rw [intervalIntegral.integral_comp_mul_left
    (fun α : ℝ => ‖primeSum293 ε X α‖ ^ 2) hc.ne']
  have he : |l| * (a + 1 / |l|) = |l| * a + 1 := by field_simp
  rw [he, prime_second_moment_unit353]
  simp [one_div, smul_eq_mul]

/-- P0079 page 10, Section 5. Kernel decay and the scaled periodic
moment give the inverse-square estimate on each positive period interval. -/
theorem primeMoment_scaled_unit_le396 (ε X η l a : ℝ)
    (hX : 2 ≤ X) (hl : l ≠ 0) (ha : 0 < a) :
    (∫ α in a..a + 1 / |l|, primeMoment353 l η ε X α) ≤
      ((log 4 * X * log X) / Real.pi ^ 2) * (1 / |l|) / a ^ 2 := by
  have hc : 0 < |l| := abs_pos.mpr hl
  have hs : Continuous (fun α : ℝ => ‖primeSum293 ε X (l * α)‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  have hk : Continuous (kernel293 η) := by unfold kernel293; fun_prop
  have hbound : ∀ α ∈ Set.Icc a (a + 1 / |l|),
      kernel293 η α ≤ (1 / Real.pi ^ 2) / a ^ 2 := by
    intro α hα
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    have hsq : a ^ 2 ≤ α ^ 2 := by nlinarith [hα.1]
    nlinarith [kernel_nonneg293 η α, kernel_mul_sq_le293 η α]
  calc
    _ ≤ ∫ α in a..a + 1 / |l|,
        ((1 / Real.pi ^ 2) / a ^ 2) * ‖primeSum293 ε X (l * α)‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (le_add_of_nonneg_right (by positivity))
        ((hs.mul hk).intervalIntegrable _ _) ((hs.const_mul _).intervalIntegrable _ _)
      intro α hα
      change ‖primeSum293 ε X (l * α)‖ ^ 2 * kernel293 η α ≤ _
      calc
        _ ≤ ‖primeSum293 ε X (l * α)‖ ^ 2 * ((1 / Real.pi ^ 2) / a ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound α hα) (sq_nonneg _)
        _ = _ := mul_comm _ _
    _ = ((1 / Real.pi ^ 2) / a ^ 2) * ((1 / |l|) *
        (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2)) := by
      rw [intervalIntegral.integral_const_mul, prime_scaled_moment_unit396 ε X l a hl,
        prime_second_moment353]
    _ ≤ ((1 / Real.pi ^ 2) / a ^ 2) * ((1 / |l|) * (log 4 * X * log X)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (prime_second_moment_le353 ε X hX) (by positivity))
        (by positivity)
    _ = _ := by ring

/-- P0079 page 10, Section 5. Summing the scaled period intervals bounds
one positive tail of the weighted prime moment. -/
theorem primeMoment_positive_tail396 (ε X η l a : ℝ)
    (hX : 2 ≤ X) (hl : l ≠ 0) (ha : 1 / |l| ≤ a) :
    (∫ α in Set.Ioi a, primeMoment353 l η ε X α) ≤
      2 * ((log 4 * X * log X) / Real.pi ^ 2) / a := by
  have hc : 0 < |l| := abs_pos.mpr hl
  apply integral_tail_of_blocks396 _ (primeMoment_integrable353 l η ε X)
    a (1 / |l|) ((log 4 * X * log X) / Real.pi ^ 2) (by positivity) ha
    (by have hlog := log_nonneg (show 1 ≤ X by linarith); positivity)
  intro n
  have han : 0 < a + (n : ℝ) * (1 / |l|) := by
    have ha0 : 0 < a := (by positivity : 0 < 1 / |l|).trans_le ha
    positivity
  have H := primeMoment_scaled_unit_le396 ε X η l (a + n * (1 / |l|)) hX hl han
  simpa only [add_mul, one_mul, add_assoc] using H

/-- P0079 page 10, Section 5. The kernel and the prime norm are even,
so the weighted prime moment is even for every real scale. -/
theorem primeMoment_even396 (l η ε X α : ℝ) :
    primeMoment353 l η ε X (-α) = primeMoment353 l η ε X α := by
  simp [primeMoment353, mul_neg, primeSum_norm_neg396, kernel293, Real.sinc_neg]

/-- P0079 page 10, Section 5. Reflection and the positive-tail estimate
give the two-sided weighted prime second-moment bound. -/
theorem primeMoment_tail396 (ε X η l a : ℝ)
    (hX : 2 ≤ X) (hl : l ≠ 0) (ha : 1 / |l| ≤ a) :
    (∫ α in {α : ℝ | a < |α|}, primeMoment353 l η ε X α) ≤
      4 * ((log 4 * X * log X) / Real.pi ^ 2) / a := by
  have hc : 0 < |l| := abs_pos.mpr hl
  have ha0 : 0 < a := (by positivity : 0 < 1 / |l|).trans_le ha
  have hset : {α : ℝ | a < |α|} = Set.Iio (-a) ∪ Set.Ioi a := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, lt_abs]
    constructor <;> intro H <;> rcases H with H | H
    · exact Or.inr H
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl H
  have hd : Disjoint (Set.Iio (-a)) (Set.Ioi a) := by
    apply Set.disjoint_left.mpr
    intro α hα hα'
    simp only [Set.mem_Iio, Set.mem_Ioi] at hα hα'
    linarith
  rw [hset, setIntegral_union hd measurableSet_Ioi
    (primeMoment_integrable353 l η ε X).integrableOn
    (primeMoment_integrable353 l η ε X).integrableOn]
  have hsym := integral_comp_neg_Ioi a (primeMoment353 l η ε X)
  simp_rw [primeMoment_even396] at hsym
  have hpos := primeMoment_positive_tail396 ε X η l a hX hl ha
  rw [← integral_Iic_eq_integral_Iio, ← hsym]
  calc
    _ ≤ 2 * ((log 4 * X * log X) / Real.pi ^ 2) / a +
        2 * ((log 4 * X * log X) / Real.pi ^ 2) / a := add_le_add hpos hpos
    _ = _ := by ring

end LeanLab.LZPowersOfTwo
