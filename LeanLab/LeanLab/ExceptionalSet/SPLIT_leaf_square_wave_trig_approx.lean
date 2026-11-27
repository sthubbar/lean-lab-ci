import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_signed_fourier_large_translate

/-!
Split of `U1539.leaf_square_wave_trig_approx`, burst-20261124 unit S6-10b,
P0082 Bruedern and Perelli 1998, section 7, page 370, display (40).

The leaf is split into its two analytic ingredients:

* `leaf_smoothed_square_wave_series`, MEDIUM: the square wave `(-1) ^ ⌊x⌋` smoothed at scale
  `Δ` has an absolutely convergent Fourier series in the frequencies `h / 2` with
  `c_h ≪ min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`, and equals `(-1) ^ ⌊x⌋` at distance at least `Δ`
  from the integers.
* `leaf_square_wave_weight_sums`, EASY: the weight `min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))` sums to
  `≪ 1 + log (1 / Δ)` over `|h| ≤ H` and to `≪ Δ ^ (-1) H ^ (-1)` over any finite set of `|h| > H`.

`leaf_square_wave_trig_approx_of_split` proves the parent statement verbatim from them.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539

/-- The coefficient weight of display (40) for the square wave: `1` at `h = 0`, else
`min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`. -/
noncomputable def sqW (Δ : ℝ) (h : ℤ) : ℝ :=
  if h = 0 then 1 else min (1 / |(h : ℝ)|) (1 / (Δ * (h : ℝ) ^ 2))

/-- LEAF: P0082 page 370 display (40), the Fourier series of the smoothed square wave. Class
MEDIUM. For `0 < Δ ≤ 1 / 4` the square wave `(-1) ^ ⌊x⌋` convolved with a kernel of width `Δ`,
for example the trapezoid with ramps of width `2 Δ` around the integers, has coefficients `c_h`
in the frequencies `h / 2` with `|c_h| ≤ C min(|h| ^ (-1), Δ ^ (-1) h ^ (-2))`, its Fourier
series converges to it at every `x`, and it equals `(-1) ^ ⌊x⌋` when `Δ ≤ {x} ≤ 1 - Δ`. -/
theorem leaf_smoothed_square_wave_series :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, ∃ T : ℂ,
          (Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ → T = (-1 : ℂ) ^ ⌊x⌋) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) T := by
  sorry

/-- LEAF: the two elementary sums of the weight `sqW`. Class EASY. For `0 < Δ ≤ 1 / 4` and
`H ≥ 1`, the sum over `|h| ≤ H` is at most `C (1 + log (1 / Δ))`, splitting at `|h| = 1 / Δ`,
and the sum over any finite set of integers disjoint from `[-H, H]` is at most `C / (Δ H)`. -/
theorem leaf_square_wave_weight_sums :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, sqW Δ h) ≤ C * (1 + Real.log (1 / Δ)) ∧
      ∀ S : Finset ℤ, Disjoint S (Finset.Icc (-(H : ℤ)) H) →
        (∑ h ∈ S, sqW Δ h) ≤ C / (Δ * H) := by
  sorry

private theorem eC_norm_sw (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Proved: the tail of a convergent series past a finite set `I` is bounded by any bound on
the norms over finite sets disjoint from `I`. -/
theorem norm_sub_partial_le_of_hasSum_sw {g : ℤ → ℂ} {T : ℂ} (hg : HasSum g T) (I : Finset ℤ)
    (B : ℝ) (hB : ∀ S : Finset ℤ, Disjoint S I → (∑ h ∈ S, ‖g h‖) ≤ B) :
    ‖T - ∑ h ∈ I, g h‖ ≤ B := by
  have ht : Filter.Tendsto (fun s : Finset ℤ => ‖(∑ h ∈ s, g h) - ∑ h ∈ I, g h‖)
      Filter.atTop (nhds ‖T - ∑ h ∈ I, g h‖) :=
    ((hg.sub_const (∑ h ∈ I, g h))).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop I] with s hs
  rw [← Finset.sum_sdiff hs, add_sub_cancel_right]
  exact (norm_sum_le _ _).trans (hB _ Finset.sdiff_disjoint)

/-- Proved: `leaf_square_wave_trig_approx` verbatim, CONDITIONAL ON
`leaf_smoothed_square_wave_series` and `leaf_square_wave_weight_sums`. -/
theorem leaf_square_wave_trig_approx_of_split :
    ∃ A : ℝ, 0 < A ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      ∃ c : ℤ → ℂ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ A * (1 + Real.log (1 / Δ)) ∧
        ∀ x : ℝ, Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ →
          ‖(-1 : ℂ) ^ ⌊x⌋ - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖
            ≤ A / (Δ * H) := by
  obtain ⟨C1, hC1, hser⟩ := leaf_smoothed_square_wave_series
  obtain ⟨C2, hC2, hsum⟩ := leaf_square_wave_weight_sums
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun Δ hΔ hΔ4 H hH => ?_⟩
  obtain ⟨c, hc, hx⟩ := hser Δ hΔ hΔ4
  obtain ⟨hs1, hs2⟩ := hsum Δ hΔ hΔ4 H hH
  refine ⟨c, ?_, fun x hx1 hx2 => ?_⟩
  · calc (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖)
        ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) H, C1 * sqW Δ h := Finset.sum_le_sum (fun h _ => hc h)
      _ = C1 * ∑ h ∈ Finset.Icc (-(H : ℤ)) H, sqW Δ h := by rw [Finset.mul_sum]
      _ ≤ C1 * (C2 * (1 + Real.log (1 / Δ))) := mul_le_mul_of_nonneg_left hs1 hC1.le
      _ = C1 * C2 * (1 + Real.log (1 / Δ)) := by ring
  obtain ⟨T, hTeq, hTs⟩ := hx x
  rw [← hTeq hx1 hx2]
  refine norm_sub_partial_le_of_hasSum_sw hTs _ _ (fun S hS => ?_)
  calc (∑ h ∈ S, ‖c h * eC ((h : ℝ) / 2 * x)‖)
      = ∑ h ∈ S, ‖c h‖ := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [norm_mul, eC_norm_sw, mul_one]
    _ ≤ ∑ h ∈ S, C1 * sqW Δ h := Finset.sum_le_sum (fun h _ => hc h)
    _ = C1 * ∑ h ∈ S, sqW Δ h := by rw [Finset.mul_sum]
    _ ≤ C1 * (C2 / (Δ * H)) := mul_le_mul_of_nonneg_left (hs2 S hS) hC1.le
    _ = C1 * C2 / (Δ * H) := by ring

end LeanLab.ExceptionalSet.U1539
