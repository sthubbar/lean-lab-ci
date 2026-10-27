import LeanLab.GoldbachAverage.ThetaWindowNorm

/-!
The full layer range analogue of lemma1_full, with N at least two.
Source: P0051 arXiv 2110.14250v2 pages 4 and 20 and the existing RH layer lemma.
The remaining input is weighted short interval variance.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.ThetaLayers
open Complex Finset MeasureTheory Filter Topology Set
open LeanLab.LZCesaroShort

/-- The full Fourier range from one over 2N through one half. -/
def ThetaLemma1Full (theta : ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧
  ∀ N : ℕ, 2 ≤ N → ∀ ξ : ℝ, 1 / (2 * (N : ℝ)) ≤ ξ → ξ ≤ 1 / 2 →
    ∫ α in (-ξ)..ξ, ‖St N α - 1 / zz N α‖ ^ 2 ≤
      K * (N : ℝ) ^ (2 * theta) * ξ * (1 + Real.log N) ^ 4

/-- The full theta range, CONDITIONAL ON the weighted variance input. -/
theorem theta_lemma1_full_of_weighted_variance (theta : ℝ) (htheta0 : 0 ≤ theta)
    (hv : ThetaWeightedVariance theta) : ThetaLemma1Full theta := by
  obtain ⟨C, hC, hb⟩ := theta_lemma1_range theta htheta0 hv
  refine ⟨4 * C, by positivity, fun N hN ξ hξlo hξhi => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξlo
  set y := 1 / (2 * ξ) with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hyN : y ≤ N := by
    rw [hy, div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ (by positivity : 0 < 2 * (N : ℝ))).mp hξlo
    linarith
  set L := ⌊y⌋₊ with hL
  have hL1 : 1 ≤ L := (Nat.one_le_floor_iff y).mpr hy1
  have hLN : L ≤ N := Nat.floor_le_of_le hyN
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLy : (L : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyL : y < (L : ℝ) + 1 := Nat.lt_floor_add_one y
  have hy2L : y < 2 * L := by
    have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    linarith
  have hξL : ξ ≤ 1 / (2 * L) := by
    rw [hy, le_div_iff₀ (by positivity)] at hLy
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hLξ : 1 / (L : ℝ) ≤ 4 * ξ := by
    rw [hy, div_lt_iff₀ (by positivity)] at hy2L
    rw [div_le_iff₀ hL0]
    linarith
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (show -(1 / (2 * (L : ℝ))) ≤ -ξ by linarith)
    (show -ξ ≤ ξ by linarith) hξL
    (Filter.Eventually.of_forall fun α => sq_nonneg ‖St N α - 1 / zz N α‖)
    ((continuous_St_sub (by omega : 1 ≤ N)).intervalIntegrable (μ := volume) _ _)
  refine hmono.trans ((hb N L hN hL1 hLN).trans ?_)
  have hp : 0 ≤ C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 := by positivity
  calc C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4 / L
      = (C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4) * (1 / L) := by ring
    _ ≤ (C * (N : ℝ) ^ (2 * theta) * (1 + Real.log N) ^ 4) * (4 * ξ) :=
      mul_le_mul_of_nonneg_left hLξ hp
    _ = _ := by ring

/-- The full range supplies the narrower range needed by the dyadic layers. -/
theorem theta_lemma1_of_full {theta : ℝ} (hf : ThetaLemma1Full theta) : ThetaLemma1 theta := by
  obtain ⟨K, hK, hb⟩ := hf
  refine ⟨K, hK, fun N hN ξ hlo hhi => hb N hN ξ ?_ hhi⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    apply one_div_le_one_div_of_le hN0
    linarith
  exact h.trans hlo

/-- An unconditional concrete instance at theta equals two. -/
theorem theta_lemma1_full_two : ThetaLemma1Full 2 :=
  theta_lemma1_full_of_weighted_variance 2 (by norm_num) theta_weighted_variance_two

/-- BHMSTheorem6E follows from the full range input. -/
theorem bhms_of_full (hf : ThetaLemma1Full Theta) : GSCor2.BHMSTheorem6E :=
  bhms_theorem6E_proved (theta_lemma1_of_full hf)

end LeanLab.GoldbachAverage.ThetaLayers
