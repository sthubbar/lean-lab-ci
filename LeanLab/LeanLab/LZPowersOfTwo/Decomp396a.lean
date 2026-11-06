/-
P0079 page 9, display 33 and the two replacement errors.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp353b
import LeanLab.LZPowersOfTwo.Decomp396c

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 32. The continuous prime model is continuous. -/
theorem continuousPrime_continuous396 (ε X : ℝ) : Continuous (continuousPrime353 ε X) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry character293
  fun_prop

/-- P0079 page 9, display 33. The intermediate product replaces only the
second prime sum by its continuous model. -/
def hybridModel396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  primeSum293 ε X (l1 * α) * continuousPrime353 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- LEAF. P0079 page 9, display 33, J3 and its written estimate after
Lemma 7. Replacing the second prime sum alone has little o error.
This leaf says nothing about replacing the first prime sum. -/
theorem major_second_replacement396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, hybridModel396 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  simpa only [hybridModel396, mixedModel375] using
    major_second_replacement_decomp396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- LEAF. P0079 page 9, display 33, J2 and the final sentence of the
replacement proof. Replacing the first prime sum after the second one has
little o error. This leaf contains no error from the second replacement. -/
theorem major_first_replacement396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, hybridModel396 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  simpa only [hybridModel396, mixedModel375] using
    major_first_replacement375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- P0079 page 9, display 35. CONDITIONAL ON major_second_replacement396
and major_first_replacement396. This is the exact major_replacement353 statement. -/
theorem major_replacement396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_replacement396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_first_replacement396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X hsecond hfirst
  calc
    _ ≤ ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, hybridModel396 s l1 l2 μ γ η ε X α)‖ +
      ‖(∫ α in major293 X, hybridModel396 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

end LeanLab.LZPowersOfTwo
