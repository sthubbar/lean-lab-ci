/-
P0076, Proposition 2.1, pages 7 to 8. Elementary estimates for its Fourier argument.
The proof uses a scaled square in place of the printed Cauchy inequality.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.BohrFourier

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The large spectrum has bounded size from the cubic Fourier moment. -/
theorem large_spectrum_card {A : Type*} (s : Finset A) (a : A → ℝ) {K θ : ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hθ : 0 < θ) (hK : ∑ i ∈ s, a i ^ 3 ≤ K) :
    (#{i ∈ s | θ ≤ a i} : ℝ) * θ ^ 3 ≤ K := by
  calc
    _ = ∑ i ∈ s.filter (fun i => θ ≤ a i), θ ^ 3 := by simp
    _ ≤ ∑ i ∈ s.filter (fun i => θ ≤ a i), a i ^ 3 := by
      apply sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ hθ.le (mem_filter.mp hi).2 3
    _ ≤ ∑ i ∈ s, a i ^ 3 := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by
      intro i hi _
      exact pow_nonneg (ha i hi) _)
    _ ≤ K := hK

/-- A scaled square gives the small frequency estimate without fractional powers. -/
theorem small_frequency_estimate {a c t : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (ht : 0 < t) (hat : a ≤ t ^ 2) :
    4 * a ^ 2 * c ^ 2 ≤ 2 * t * (a ^ 3 + c ^ 4) := by
  have hs := mul_nonneg ha (sq_nonneg (t * a - c ^ 2))
  have hh : a * c ^ 4 ≤ t ^ 2 * c ^ 4 := mul_le_mul_of_nonneg_right hat (by positivity)
  apply (mul_le_mul_iff_of_pos_left ht).mp
  nlinarith

/-- The large frequency estimate is the elementary fourth moment inequality. -/
theorem large_frequency_estimate {a c u : ℝ} (hu : 0 ≤ u) :
    a ^ 2 * (u * c) ^ 2 ≤ u ^ 2 / 2 * (a ^ 4 + c ^ 4) := by
  have h := mul_nonneg (sq_nonneg u) (sq_nonneg (a ^ 2 - c ^ 2))
  nlinarith

/-- The spectral upper bound in the proof of Proposition 2.1. -/
theorem spectral_error_bound {A : Type*} (s Ω : Finset A) (F G H : A → ℂ) {t u K : ℝ}
    (ht : 0 < t) (hu : 0 ≤ u) (hK : 0 ≤ K)
    (hF3 : ∑ i ∈ s, ‖F i‖ ^ 3 ≤ K) (hF4 : ∑ i ∈ s, ‖F i‖ ^ 4 ≤ K)
    (hG4 : ∑ i ∈ s, ‖G i‖ ^ 4 ≤ K)
    (hH : ∀ i ∈ s, ‖H i‖ ≤ 2 * ‖G i‖)
    (hsmall : ∀ i ∈ s, i ∉ Ω → ‖F i‖ ≤ t ^ 2)
    (hlarge : ∀ i ∈ s, i ∈ Ω → ‖H i‖ ≤ u * ‖G i‖) :
    ∑ i ∈ s, ‖F i * H i‖ ^ 2 ≤ (4 * t + u ^ 2) * K := by
  have hp : ∀ i ∈ s, ‖F i * H i‖ ^ 2 ≤
      2 * t * (‖F i‖ ^ 3 + ‖G i‖ ^ 4) + u ^ 2 / 2 * (‖F i‖ ^ 4 + ‖G i‖ ^ 4) := by
    intro i hi
    rw [norm_mul, mul_pow]
    by_cases hΩ : i ∈ Ω
    · have h1 : ‖F i‖ ^ 2 * ‖H i‖ ^ 2 ≤ ‖F i‖ ^ 2 * (u * ‖G i‖) ^ 2 := by
        gcongr
        exact hlarge i hi hΩ
      have h2 := large_frequency_estimate (a := ‖F i‖) (c := ‖G i‖) hu
      have h3 : 0 ≤ 2 * t * (‖F i‖ ^ 3 + ‖G i‖ ^ 4) := by positivity
      linarith
    · have h1 : ‖F i‖ ^ 2 * ‖H i‖ ^ 2 ≤ 4 * ‖F i‖ ^ 2 * ‖G i‖ ^ 2 := by
        calc _ ≤ ‖F i‖ ^ 2 * (2 * ‖G i‖) ^ 2 := by gcongr; exact hH i hi
             _ = _ := by ring
      have h2 := small_frequency_estimate (norm_nonneg (F i)) (norm_nonneg (G i)) ht
        (hsmall i hi hΩ)
      have h3 : 0 ≤ u ^ 2 / 2 * (‖F i‖ ^ 4 + ‖G i‖ ^ 4) := by positivity
      linarith
  calc
    _ ≤ ∑ i ∈ s, (2 * t * (‖F i‖ ^ 3 + ‖G i‖ ^ 4) +
        u ^ 2 / 2 * (‖F i‖ ^ 4 + ‖G i‖ ^ 4)) := sum_le_sum hp
    _ = 2 * t * ((∑ i ∈ s, ‖F i‖ ^ 3) + ∑ i ∈ s, ‖G i‖ ^ 4) +
        u ^ 2 / 2 * ((∑ i ∈ s, ‖F i‖ ^ 4) + ∑ i ∈ s, ‖G i‖ ^ 4) := by
      simp_rw [sum_add_distrib, ← mul_sum]
      simp only [sum_add_distrib]
    _ ≤ 2 * t * (K + K) + u ^ 2 / 2 * (K + K) := by gcongr
    _ = _ := by ring

/-- Parameters can be chosen with eta below 0.05 for every positive delta and epsilon. -/
theorem prop21_parameters {K δ ε : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ t η : ℝ, 0 < t ∧ 0 < η ∧ η < 1 / 20 ∧
      (4 * t + (30 * η) ^ 2) * K ≤ δ ^ 4 * ε / 10 := by
  have hK0 : 0 < K := by linarith
  let t := δ ^ 4 * ε / (1000 * K)
  let η := min (1 / 40) (δ ^ 4 * ε / (100000 * K))
  have ht : 0 < t := by dsimp [t]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 40 := min_le_left _ _
  have hη2 : η ≤ δ ^ 4 * ε / (100000 * K) := min_le_right _ _
  have hη2' : η * (100000 * K) ≤ δ ^ 4 * ε := (le_div_iff₀ (by positivity)).mp hη2
  have ht' : t * (1000 * K) = δ ^ 4 * ε := by dsimp [t]; field_simp
  refine ⟨t, η, ht, hη, by linarith, ?_⟩
  have hs : η ^ 2 ≤ η := by nlinarith
  have hsK := mul_le_mul_of_nonneg_right hs hK0.le
  nlinarith

example : (1 : ℝ) ≤ 1 ^ 2 ∧ 4 * (1 : ℝ) ^ 2 * 1 ^ 2 ≤ 2 * 1 * (1 ^ 3 + 1 ^ 4) := by
  norm_num

#print axioms large_spectrum_card
#print axioms small_frequency_estimate
#print axioms large_frequency_estimate
#print axioms spectral_error_bound
#print axioms prop21_parameters

end LeanLab.Teravainen2016
