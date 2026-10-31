/-
P0076, Section 4, Proposition 4.2 and its deduction of Proposition 3.3, pages 13 to 14.
The restriction estimate is a cited input, represented as a predicate.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.NaturalConvolution

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

noncomputable def complexFhat (N : ℕ) (a : ℕ → ℂ) (ξ : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, a n * eC (-((ξ : ℝ) * n / N))

/-- Proposition 4.2 on representatives 0 through N minus 1.
The weight at residue zero is transported from the paper endpoint N. -/
def Restriction42 (N : ℕ) (β : ℕ → ℝ) (r C : ℝ) : Prop :=
  ∀ a : ℕ → ℂ,
    (∑ ξ ∈ range N, ‖complexFhat N (fun n => a n * (β n : ℂ)) ξ‖ ^ r) ^ (1 / r) ≤
      C * ((N : ℝ)⁻¹ * ∑ n ∈ range N, ‖a n‖ ^ 2 * β n) ^ ((1 : ℝ) / 2)

/-- Division by the majorant reconstructs a dominated nonnegative function, even at zero. -/
theorem quotient_reconstruct {g β c : ℝ} (hg : 0 ≤ g) (hβ : 0 ≤ β) (hgb : g ≤ c * β) :
    (g / β) * β = g := by
  by_cases h0 : β = 0
  · subst β
    have : g = 0 := by linarith
    simp [this]
  · field_simp

/-- The energy quotient in the proof of Proposition 3.3 is bounded pointwise. -/
theorem quotient_energy_le {g β c : ℝ} (hg : 0 ≤ g) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hgb : g ≤ c * β) : (g / β) ^ 2 * β ≤ c ^ 2 * β := by
  by_cases h0 : β = 0
  · simp [h0]
  · have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm h0)
    have hquot : g / β ≤ c := (div_le_iff₀ hβp).mpr hgb
    have hquot0 : 0 ≤ g / β := div_nonneg hg hβ
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hquot0 hquot 2) hβ

/-- The averaged quotient energy is at most c squared times the mean majorant bound. -/
theorem quotient_mean_energy_le (N : ℕ) (g β : ℕ → ℝ) {c κ : ℝ}
    (hg : ∀ n, 0 ≤ g n) (hβ : ∀ n, 0 ≤ β n) (hc : 0 ≤ c)
    (hgb : ∀ n < N, g n ≤ c * β n)
    (hmean : (N : ℝ)⁻¹ * ∑ n ∈ range N, β n ≤ κ) :
    (N : ℝ)⁻¹ * ∑ n ∈ range N, (g n / β n) ^ 2 * β n ≤ c ^ 2 * κ := by
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ range N, c ^ 2 * β n := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun n hn => quotient_energy_le (hg n) (hβ n) hc (hgb n (mem_range.mp hn)))
    _ = c ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ range N, β n) := by rw [← mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean (sq_nonneg c)

/-- Proposition 3.3's root moment bound, CONDITIONAL ON Proposition 4.2 for beta. -/
theorem restriction_dominated_root (N : ℕ) (g β : ℕ → ℝ) {r C c κ : ℝ}
    (hβ : ∀ n, 0 ≤ β n) (hg : ∀ n, 0 ≤ g n) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hgb : ∀ n < N, g n ≤ c * β n)
    (hmean : (N : ℝ)⁻¹ * ∑ n ∈ range N, β n ≤ κ)
    (h42 : Restriction42 N β r C) :
    (∑ ξ ∈ range N, ‖fhat N g ξ‖ ^ r) ^ (1 / r) ≤ C * (c ^ 2 * κ) ^ ((1 : ℝ) / 2) := by
  let a : ℕ → ℂ := fun n => ((g n / β n : ℝ) : ℂ)
  have hrec : ∀ ξ, complexFhat N (fun n => a n * (β n : ℂ)) ξ = fhat N g ξ := by
    intro ξ
    unfold complexFhat fhat
    congr 1
    apply sum_congr rfl
    intro n hn
    dsimp [a]
    rw [← Complex.ofReal_mul, quotient_reconstruct (hg n) (hβ n) (hgb n (mem_range.mp hn))]
  have h := h42 a
  simp_rw [hrec] at h
  have hnorm : ∀ n, ‖a n‖ ^ 2 = (g n / β n) ^ 2 := by
    intro n
    dsimp [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hg n) (hβ n))]
  simp_rw [hnorm] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.rpow_le_rpow (by
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun n _ => mul_nonneg (sq_nonneg _) (hβ n)))
    (quotient_mean_energy_le N g β hg hβ hc hgb hmean) (by norm_num)

/-- The powered restriction bound, CONDITIONAL ON Proposition 4.2 for beta. -/
theorem restriction_dominated_moment (N : ℕ) (g β : ℕ → ℝ) {r C c κ : ℝ}
    (hr : 2 < r) (hβ : ∀ n, 0 ≤ β n) (hg : ∀ n, 0 ≤ g n) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hgb : ∀ n < N, g n ≤ c * β n)
    (hmean : (N : ℝ)⁻¹ * ∑ n ∈ range N, β n ≤ κ)
    (h42 : Restriction42 N β r C) :
    ∑ ξ ∈ range N, ‖fhat N g ξ‖ ^ r ≤ (C * (c ^ 2 * κ) ^ ((1 : ℝ) / 2)) ^ r := by
  have h := restriction_dominated_root N g β hβ hg hc hC hgb hmean h42
  have hsum : 0 ≤ ∑ ξ ∈ range N, ‖fhat N g ξ‖ ^ r :=
    sum_nonneg (fun ξ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hr0 : 0 < r := by linarith
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) h hr0.le
  rwa [← Real.rpow_mul hsum, one_div_mul_cancel hr0.ne', Real.rpow_one] at hh

example : (0 : ℝ) / 0 * 0 = 0 := quotient_reconstruct (by norm_num) (by norm_num) (c := 1) (by norm_num)

example : Restriction42 1 (fun _ => 0) 3 1 := by
  intro a
  norm_num [complexFhat]

#print axioms quotient_reconstruct
#print axioms quotient_energy_le
#print axioms quotient_mean_energy_le
#print axioms restriction_dominated_root
#print axioms restriction_dominated_moment

end LeanLab.Teravainen2016
