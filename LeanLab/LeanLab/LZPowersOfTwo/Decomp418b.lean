/-
P0079 page 9, the prime versus integer input in the J2 argument.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp418d
import LeanLab.LZPowersOfTwo.Decomp396b
import LeanLab.LZPowersOfTwo.Decomp396a

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 33, J2, and the written analogous estimate
following display 35. The S minus U contribution replaces the first prime sum
by the integer sum while the second factor is continuous. Lemmas 6 and 7
supply the prime discrepancy. Saffari Vaughan Section 6, pages 24 to 25,
gives the cited unsmoothed Selberg argument. No U minus T error occurs here. -/
theorem major_first_discrepancy418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, discreteFirstModel418 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  exact major_first_discrepancy_l2418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- P0079 page 9, J2 in display 33. CONDITIONAL ON major_first_discrepancy418.
The exact major_first_replacement375 statement uses the proved quadrature bridge. -/
theorem major_first_replacement418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_first_discrepancy418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_first_riemann418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X hd hr
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

/-- P0079 page 9, display 35. CONDITIONAL ON prime_integer_l2_small418. This is the exact major_replacement353 statement. -/
theorem major_replacement418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_replacement_l2418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_first_replacement418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X hsecond hfirst
  change ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
    (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ ≤ _ at hsecond
  calc
    _ ≤ ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ +
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- P0079 page 9, the conclusion after display 35. CONDITIONAL ON
prime_integer_l2_small418. The continuous model input is proved. This is the exact major target. -/
theorem major_lower418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ := l1 * ε / (4 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_replacement418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ,
    major_model_lower396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'] with X he hm
  have hre := Complex.re_le_norm
    ((∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α))
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re] at hre
  have hc : (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 - δ =
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 := by dsimp [δ]; ring
  nlinarith only [hre, he, hm, congrArg (fun c : ℝ => c * X * (cutoff293 s μ ε X) ^ s) hc]


end LeanLab.LZPowersOfTwo
