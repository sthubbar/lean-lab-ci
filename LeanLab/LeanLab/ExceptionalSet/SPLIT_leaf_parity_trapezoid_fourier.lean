import LeanLab.ExceptionalSet.SPLIT_feed1122_parity_removal_core

/-!
Split of `Feed1122ParityCore.leaf_parity_trapezoid_fourier`, burst-20261124 unit S6-02b,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into its two analytic ingredients:

* `leaf_trapezoid_fourier_series`, MEDIUM: the trapezoid function of ramp width `2 A` has an
  absolutely convergent Fourier series in the frequencies `h / 2` with
  `c_h ≪ min(1, A ^ (-1) h ^ (-2))`, its value lies in `[0, 1]` and equals the indicator of
  `⌊x⌋` even off the ramps.
* `leaf_trapezoid_weight_sums`, EASY: the weight `min(1, A ^ (-1) h ^ (-2))` sums to
  `≪ A ^ (-1 / 2)` over `|h| ≤ H` and to `≪ A ^ (-1) H ^ (-1)` over any finite set of `|h| > H`.

`leaf_parity_trapezoid_fourier_of_split` proves the parent statement verbatim from them.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Feed1122ParityCore

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)

/-- The coefficient weight of display (40): `1` at `h = 0`, else `min(1, A ^ (-1) h ^ (-2))`. -/
noncomputable def trapW (A : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 1 else min 1 (1 / (A * (h : ℝ) ^ 2))

/-- Proved helper: every trapezoid weight is at most one. -/
theorem trapW_le_one (A : ℝ) (h : ℤ) : trapW A h ≤ 1 := by
  unfold trapW
  split_ifs
  · norm_num
  · exact min_le_left _ _

/-- Proved helper: at a nonzero frequency the trapezoid weight is at most the
reciprocal-square weight. -/
theorem trapW_le_inv_sq (A : ℝ) (h : ℤ) (hA : 0 < A) (hne : h ≠ 0) :
    trapW A h ≤ 1 / (A * (h : ℝ) ^ 2) := by
  unfold trapW
  rw [if_neg hne]
  exact min_le_right _ _

/-- LEAF: P0082 page 370 display (40), the Fourier series of the trapezoid. Class MEDIUM.
For `0 < A ≤ 1 / 4` the period two trapezoid, one on `[k + A, k + 1 - A]` for `k` even, zero
there for `k` odd, linear on the ramps of width `2 A` around the integers, has coefficients
`c_h` in the frequencies `h / 2` with `|c_h| ≤ C min(1, A ^ (-1) h ^ (-2))`, the series
converges to it at every `x`, its value lies in `[0, 1]`, and off the ramps it is the
indicator of `⌊x⌋` even. Poisson summation, or integration by parts twice. -/
theorem leaf_trapezoid_fourier_series :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * trapW A h) ∧
        ∀ x : ℝ, ∃ T : ℝ, 0 ≤ T ∧ T ≤ 1 ∧
          (A ≤ Int.fract x → Int.fract x ≤ 1 - A → (T : ℂ) = if Even ⌊x⌋ then 1 else 0) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) (T : ℂ) := by
  sorry

/-- LEAF: the two elementary sums of the weight `trapW`. Class EASY. For `0 < A ≤ 1 / 4` and
`H ≥ 1`, the sum over `|h| ≤ H` is at most `C A ^ (-1 / 2)`, and the sum over any finite set
of integers disjoint from `[-H, H]` is at most `C / (A H)`, by comparison with `∫ t ^ (-2)`. -/
theorem leaf_trapezoid_weight_sums :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, trapW A h) ≤ C * A ^ (-(1 / 2 : ℝ)) ∧
      ∀ S : Finset ℤ, Disjoint S (Finset.Icc (-(H : ℤ)) H) →
        (∑ h ∈ S, trapW A h) ≤ C / (A * H) := by
  sorry

/-- Proved: the tail of a convergent series past a finite set `I` is bounded by any bound on
the norms over finite sets disjoint from `I`. -/
theorem norm_sub_partial_le_of_hasSum {g : ℤ → ℂ} {T : ℂ} (hg : HasSum g T) (I : Finset ℤ)
    (B : ℝ) (hB : ∀ S : Finset ℤ, Disjoint S I → (∑ h ∈ S, ‖g h‖) ≤ B) :
    ‖T - ∑ h ∈ I, g h‖ ≤ B := by
  have ht : Filter.Tendsto (fun s : Finset ℤ => ‖(∑ h ∈ s, g h) - ∑ h ∈ I, g h‖)
      Filter.atTop (nhds ‖T - ∑ h ∈ I, g h‖) :=
    ((hg.sub_const (∑ h ∈ I, g h))).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop I] with s hs
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  exact (norm_sum_le _ _).trans (hB _ Finset.sdiff_disjoint)

/-- Proved: `leaf_parity_trapezoid_fourier` verbatim, CONDITIONAL ON
`leaf_trapezoid_fourier_series` and `leaf_trapezoid_weight_sums`. -/
theorem leaf_parity_trapezoid_fourier_of_split :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      ∃ c : ℤ → ℂ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ C * A ^ (-(1 / 2 : ℝ)) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖ ≤
            (if A ≤ Int.fract x ∧ Int.fract x ≤ 1 - A then C / (A * H)
              else 2 + C / (A * H)) := by
  obtain ⟨C1, hC1, hser⟩ := leaf_trapezoid_fourier_series
  obtain ⟨C2, hC2, hsum⟩ := leaf_trapezoid_weight_sums
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun A hA hA4 H hH => ?_⟩
  obtain ⟨c, hc, hx⟩ := hser A hA hA4
  obtain ⟨hs1, hs2⟩ := hsum A hA hA4 H hH
  refine ⟨c, ?_, fun x => ?_⟩
  · calc (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖)
        ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, C1 * trapW A h := Finset.sum_le_sum (fun h _ => hc h)
      _ = C1 * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, trapW A h := by rw [Finset.mul_sum]
      _ ≤ C1 * (C2 * A ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hs1 hC1.le
      _ = C1 * C2 * A ^ (-(1 / 2 : ℝ)) := by ring
  obtain ⟨T, hT0, hT1, hTeq, hTs⟩ := hx x
  have htail : ‖(T : ℂ) - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖ ≤
      C1 * C2 / (A * H) := by
    refine norm_sub_partial_le_of_hasSum hTs _ _ (fun S hS => ?_)
    calc (∑ h ∈ S, ‖c h * eC ((h : ℝ) / 2 * x)‖)
        = ∑ h ∈ S, ‖c h‖ := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [norm_mul, eC_norm, mul_one]
      _ ≤ ∑ h ∈ S, C1 * trapW A h := Finset.sum_le_sum (fun h _ => hc h)
      _ = C1 * ∑ h ∈ S, trapW A h := by rw [Finset.mul_sum]
      _ ≤ C1 * (C2 / (A * H)) := mul_le_mul_of_nonneg_left (hs2 S hS) hC1.le
      _ = C1 * C2 / (A * H) := by ring
  have hsplit : (if Even ⌊x⌋ then (1 : ℂ) else 0) -
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x) =
      ((if Even ⌊x⌋ then (1 : ℂ) else 0) - (T : ℂ)) +
      ((T : ℂ) - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)) := by ring
  by_cases hoff : A ≤ Int.fract x ∧ Int.fract x ≤ 1 - A
  · rw [if_pos hoff, hsplit, ← hTeq hoff.1 hoff.2, sub_self, zero_add]
    exact htail
  · rw [if_neg hoff, hsplit]
    refine (norm_add_le _ _).trans ?_
    have hind : ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) - (T : ℂ)‖ ≤ 2 := by
      split_ifs
      · rw [show (1 : ℂ) - (T : ℂ) = ((1 - T : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      · rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_le]
        constructor <;> linarith
    linarith

end LeanLab.ExceptionalSet.Feed1122ParityCore
