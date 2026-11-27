/-
Split of `U1539.leaf_smoothed_square_wave_series` of `SPLIT_leaf_square_wave_trig_approx`,
burst-20261127 unit S5-17c, KEEP GOING after S5-17,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into the construction of the smoothed square wave with its coefficient
bound, the remaining LEAF `leaf_smoothed_square_wave_circle` of class MEDIUM, and the
convergence of its Fourier series, which is proved here from Mathlib's
`has_pointwise_sum_fourier_series_of_summable` and the summability of the weight `sqW`, itself
a consequence of the proved `leaf_square_wave_weight_sums`.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_square_wave_trig_approx

namespace LeanLab.ExceptionalSet.U1539

/-- The circle `ℝ / 2ℤ` of period two carries the Fourier theory used below. -/
local instance fact_two_pos_s5 : Fact ((0 : ℝ) < 2) := ⟨by norm_num⟩

/-- LEAF: P0082 page 370 display (40), the smoothed square wave and its coefficients. Class
MEDIUM. For `0 < Δ ≤ 1 / 4` there is a continuous function on the circle `ℝ / 2ℤ`, for example
the square wave `(-1) ^ ⌊x⌋` with its jumps replaced by linear ramps of width `2 Δ` around the
integers, equal to `(-1) ^ ⌊x⌋` when `Δ ≤ {x} ≤ 1 - Δ`, whose Fourier coefficients satisfy
`|c_h| ≤ C min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`, by integrating by parts once and twice. -/
theorem leaf_smoothed_square_wave_circle :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ f : C(AddCircle (2 : ℝ), ℂ), (∀ h : ℤ, ‖fourierCoeff f h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ →
          f (x : AddCircle (2 : ℝ)) = (-1 : ℂ) ^ ⌊x⌋ := by
  sorry

/-- Proved: the weight `sqW` is summable over `ℤ`, from `leaf_square_wave_weight_sums` at
`H = 1`. -/
theorem summable_sqW_s5 {Δ : ℝ} (hΔ : 0 < Δ) (hΔ4 : Δ ≤ 1 / 4) : Summable (sqW Δ) := by
  obtain ⟨C, _, hC⟩ := leaf_square_wave_weight_sums
  obtain ⟨h1, h2⟩ := hC Δ hΔ hΔ4 1 le_rfl
  have hnn : ∀ h : ℤ, 0 ≤ sqW Δ h := by
    intro h
    unfold sqW
    split_ifs
    · exact zero_le_one
    · exact le_min (by positivity) (by positivity)
  refine summable_of_sum_le (c := C * (1 + Real.log (1 / Δ)) + C / (Δ * (1 : ℕ)))
    (fun h => hnn h) (fun u => ?_)
  rw [← Finset.sum_filter_add_sum_filter_not u (fun h => h ∈ Finset.Icc (-((1 : ℕ) : ℤ)) (1 : ℕ))]
  refine add_le_add ((Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hnn h)).trans h1)
    (h2 _ ?_)
  · intro h hh
    exact (Finset.mem_filter.1 hh).2
  · rw [Finset.disjoint_left]
    intro h hh
    exact (Finset.mem_filter.1 hh).2

/-- Proved: `leaf_smoothed_square_wave_series` verbatim, CONDITIONAL ON
`leaf_smoothed_square_wave_circle`; the convergence of the Fourier series is Mathlib's
`has_pointwise_sum_fourier_series_of_summable`. -/
theorem leaf_smoothed_square_wave_series_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, ∃ T : ℂ,
          (Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ → T = (-1 : ℂ) ^ ⌊x⌋) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) T := by
  obtain ⟨C, hC, hf⟩ := leaf_smoothed_square_wave_circle
  refine ⟨C, hC, fun Δ hΔ hΔ4 => ?_⟩
  obtain ⟨f, hcoef, hval⟩ := hf Δ hΔ hΔ4
  have hsum : Summable (fourierCoeff f) :=
    Summable.of_norm_bounded ((summable_sqW_s5 hΔ hΔ4).mul_left C) hcoef
  refine ⟨fourierCoeff f, hcoef, fun x => ⟨f (x : AddCircle (2 : ℝ)),
    fun h1 h2 => hval x h1 h2, ?_⟩⟩
  have hp := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (2 : ℝ))
  refine hp.congr_fun (fun h => ?_)
  rw [smul_eq_mul, fourier_coe_apply]
  unfold eC
  congr 2
  push_cast
  ring

example : type_of% @leaf_smoothed_square_wave_series := leaf_smoothed_square_wave_series_of_leaves

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.summable_sqW_s5
#print axioms LeanLab.ExceptionalSet.U1539.leaf_smoothed_square_wave_series_of_leaves
