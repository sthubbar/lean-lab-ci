import LeanLab.GoldbachAverage.VarianceComparison124

/-!
The elementary reduction of P0051 eq. 19 to the remaining infinite Fourier comparison.
The comparison itself is a displayed hypothesis, not an axiom or a new Prop definition.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.GallagherReduction124
open MeasureTheory Filter
open WeightedPrefix82 WeightedPrefixBound82 I2Bound124 VarianceTails124 VarianceComparison124

/-- I1 from P0051 page 9 eq. 49. -/
def I1 (N : ℕ) (h : ℝ) : ℝ := ∫ t in (0 : ℝ)..h, weightedPrefix N t ^ 2

/-- LEAF. P0051 pages 10 and 11 eqs. 54 and 56, summed with explicit constants. -/
theorem I1_I2_bound (N : ℕ) (hN : 1 ≤ N) {h : ℝ} (hh : 0 ≤ h) (hhN : h ≤ N) :
    I1 N h + I2 N h ≤ 8 * InghamTheta.H h +
      12 * (Real.exp 2 + 1) * (h / N) ^ 2 *
        (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) +
      12 * (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h) +
      (24 * Real.exp 2 + 56) * N := by
  have h1 := weighted_prefix_square_bound N hN hh hhN
  have h2 := I2_HJ_bound N hN hh hhN
  change I1 N h ≤ _ at h1
  nlinarith only [h1, h2, hhN]

/-- LEAF. P0051 page 11 eq. 57 and page 4 eq. 19.
CONDITIONAL ON the displayed infinite weighted Fourier comparison from page 9 eq. 48.
Every H and J estimate and every convergence assertion is proved separately. -/
theorem gallagher_of_fourier
    (hFourier : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ h : ℝ, 1 ≤ h → h ≤ N →
      GSInputs.W N h ≤ K * ((I1 N h + I2 N h) / h ^ 2)) :
    GSInputs.GSGallagherVarianceBound := by
  obtain ⟨K, hK, hF⟩ := hFourier
  refine ⟨K * (36 * Real.exp 2 + 88), by positivity, fun N hN h hh hhN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh0 : 0 < h := by linarith
  have hh0' : 0 ≤ h := hh0.le
  have hH := H_series_summable hN0
  have hJ := J_series_summable hN0 hh0'
  refine ⟨hH, hJ, ?_⟩
  let A : ℝ := InghamTheta.H h / h ^ 2
  let B : ℝ := (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
    InghamTheta.H (((j : ℝ) + 1) * N)) / (N : ℝ) ^ 2
  let C : ℝ := (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
    GSInputs.J (((j : ℝ) + 1) * N) h) / h ^ 2
  let D : ℝ := (N : ℝ) / h ^ 2
  let V : ℝ := A + B + C + D
  have hA : 0 ≤ A := div_nonneg
    (intervalIntegral.integral_nonneg hh0' (fun _ _ => sq_nonneg _)) (sq_nonneg h)
  have hB : 0 ≤ B := by
    apply div_nonneg _ (sq_nonneg _)
    apply tsum_nonneg
    intro j
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _))
  have hC : 0 ≤ C := by
    apply div_nonneg _ (sq_nonneg _)
    apply tsum_nonneg
    intro j
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg (by positivity) (fun _ _ => sq_nonneg _))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAV : A ≤ V := by dsimp [V]; linarith
  have hBV : B ≤ V := by dsimp [V]; linarith
  have hCV : C ≤ V := by dsimp [V]; linarith
  have hDV : D ≤ V := by dsimp [V]; linarith
  have hi := div_le_div_of_nonneg_right (I1_I2_bound N (by omega) hh0' hhN) (sq_nonneg h)
  have heq : (8 * InghamTheta.H h +
      12 * (Real.exp 2 + 1) * (h / N) ^ 2 *
        (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * InghamTheta.H (((j : ℝ) + 1) * N)) +
      12 * (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * GSInputs.J (((j : ℝ) + 1) * N) h) +
      (24 * Real.exp 2 + 56) * N) / h ^ 2 =
      8 * A + 12 * (Real.exp 2 + 1) * B + 12 * C + (24 * Real.exp 2 + 56) * D := by
    dsimp [A, B, C, D]
    field_simp [hh0.ne', hN0.ne']
    <;> ring
  rw [heq] at hi
  have hsum : 8 * A + 12 * (Real.exp 2 + 1) * B + 12 * C +
      (24 * Real.exp 2 + 56) * D ≤ (36 * Real.exp 2 + 88) * V := by
    have h1 := mul_le_mul_of_nonneg_left hAV (by norm_num : (0 : ℝ) ≤ 8)
    have h2 := mul_le_mul_of_nonneg_left hBV
      (show 0 ≤ 12 * (Real.exp 2 + 1) by positivity)
    have h3 := mul_le_mul_of_nonneg_left hCV (by norm_num : (0 : ℝ) ≤ 12)
    have h4 := mul_le_mul_of_nonneg_left hDV
      (show 0 ≤ 24 * Real.exp 2 + 56 by positivity)
    nlinarith only [h1, h2, h3, h4]
  change GSInputs.W N h ≤ K * (36 * Real.exp 2 + 88) * V
  calc GSInputs.W N h ≤ K * ((I1 N h + I2 N h) / h ^ 2) := hF N hN h hh hhN
    _ ≤ K * ((36 * Real.exp 2 + 88) * V) :=
      mul_le_mul_of_nonneg_left (hi.trans hsum) hK
    _ = _ := by ring

end LeanLab.GoldbachAverage.GallagherReduction124
