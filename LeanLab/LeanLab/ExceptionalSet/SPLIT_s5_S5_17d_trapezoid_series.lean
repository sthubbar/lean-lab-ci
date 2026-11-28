/-
Split of `Feed1122ParityCore.leaf_trapezoid_fourier_series` of
`SPLIT_leaf_parity_trapezoid_fourier`, burst-20261127 unit S5-17d, KEEP GOING after S5-17b,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into the construction of the trapezoid with its coefficient bound, the
remaining LEAF `leaf_trapezoid_circle` of class MEDIUM, and the convergence of its Fourier
series, proved here from Mathlib's `has_pointwise_sum_fourier_series_of_summable` and the
summability of the weight `trapW`, a consequence of the proved `leaf_trapezoid_weight_sums`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_parity_trapezoid_fourier

namespace LeanLab.ExceptionalSet.Feed1122ParityCore

open LeanLab.ExceptionalSet.U1539 (eC)

/-- The circle `ℝ / 2ℤ` of period two carries the Fourier theory used below. -/
local instance fact_two_pos_s5d : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/-- LEAF: P0082 page 370 display (40), the trapezoid and its coefficients. Class MEDIUM.
For `0 < A ≤ 1 / 4` there is a continuous function on the circle `ℝ / 2ℤ`, the period two
trapezoid, one on `[k + A, k + 1 - A]` for `k` even, zero there for `k` odd, linear on the
ramps of width `2 A` around the integers, with real values in `[0, 1]`, equal off the ramps to
the indicator of `⌊x⌋` even, whose Fourier coefficients satisfy
`|c_h| ≤ C min(1, A ^ (-1) h ^ (-2))`, by integrating by parts twice. -/
theorem leaf_trapezoid_circle :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 →
      ∃ f : C(AddCircle (2 : ℝ), ℂ), (∀ h : ℤ, ‖fourierCoeff f h‖ ≤ C * trapW A h) ∧
        (∀ y : AddCircle (2 : ℝ), (f y).im = 0 ∧ 0 ≤ (f y).re ∧ (f y).re ≤ 1) ∧
        ∀ x : ℝ, A ≤ Int.fract x → Int.fract x ≤ 1 - A →
          f (x : AddCircle (2 : ℝ)) = if Even ⌊x⌋ then 1 else 0 := by
  sorry

/-- Proved: the weight `trapW` is summable over `ℤ`, from `leaf_trapezoid_weight_sums` at
`H = 1`. -/
theorem summable_trapW_s5 {A : ℝ} (hA : 0 < A) (hA4 : A ≤ 1 / 4) : Summable (trapW A) := by
  obtain ⟨C, _, hC⟩ := leaf_trapezoid_weight_sums
  obtain ⟨h1, h2⟩ := hC A hA hA4 1 le_rfl
  have hnn : ∀ h : ℤ, 0 ≤ trapW A h := by
    intro h
    unfold trapW
    split_ifs
    · exact zero_le_one
    · exact le_min zero_le_one (by positivity)
  refine summable_of_sum_le (c := C * A ^ (-(1 / 2 : ℝ)) + C / (A * (1 : ℕ)))
    (fun h => hnn h) (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u (fun h => h ∈ Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ))]
  refine add_le_add ((Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hnn h)).trans h1)
    (h2 _ ?_)
  · intro h hh
    exact (Finset.mem_filter.1 hh).2
  · rw [Finset.disjoint_left]
    intro h hh
    exact (Finset.mem_filter.1 hh).2

/-- Proved: `leaf_trapezoid_fourier_series` verbatim, CONDITIONAL ON `leaf_trapezoid_circle`;
the convergence of the Fourier series is Mathlib's
`has_pointwise_sum_fourier_series_of_summable`. -/
theorem leaf_trapezoid_fourier_series_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * trapW A h) ∧
        ∀ x : ℝ, ∃ T : ℝ, 0 ≤ T ∧ T ≤ 1 ∧
          (A ≤ Int.fract x → Int.fract x ≤ 1 - A → (T : ℂ) = if Even ⌊x⌋ then 1 else 0) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) (T : ℂ) := by
  obtain ⟨C, hC, hf⟩ := leaf_trapezoid_circle
  refine ⟨C, hC, fun A hA hA4 => ?_⟩
  obtain ⟨f, hcoef, hreal, hval⟩ := hf A hA hA4
  have hsum : Summable (fourierCoeff f) :=
    Summable.of_norm_bounded ((summable_trapW_s5 hA hA4).mul_left C) hcoef
  refine ⟨fourierCoeff f, hcoef, fun x => ?_⟩
  obtain ⟨him, hre0, hre1⟩ := hreal (x : AddCircle (2 : ℝ))
  have hT : (((f (x : AddCircle (2 : ℝ))).re : ℝ) : ℂ) = f (x : AddCircle (2 : ℝ)) :=
    Complex.ext (by simp) (by simp [him])
  refine ⟨(f (x : AddCircle (2 : ℝ))).re, hre0, hre1, fun h1 h2 => ?_, ?_⟩
  · rw [hT]; exact hval x h1 h2
  · rw [hT]
    have hp := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (2 : ℝ))
    refine hp.congr_fun (fun h => ?_)
    rw [smul_eq_mul, fourier_coe_apply]
    unfold eC
    congr 2
    push_cast
    ring

example : type_of% @leaf_trapezoid_fourier_series := leaf_trapezoid_fourier_series_of_leaves

end LeanLab.ExceptionalSet.Feed1122ParityCore

#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.summable_trapW_s5
#print axioms LeanLab.ExceptionalSet.Feed1122ParityCore.leaf_trapezoid_fourier_series_of_leaves
