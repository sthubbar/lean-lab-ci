/-
P0079 page 10, displays 36 and 37, full model and truncation.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp375c
import LeanLab.LZPowersOfTwo.FullModel396
import LeanLab.LZPowersOfTwo.ModelTail396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- LEAF. P0079 page 10, display 36. Extending the continuous major model
to the full line has error little o of X L to the s. This is only the
truncation estimate and contains no geometric lower bound. -/
theorem major_model_truncation396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  exact major_model_tail396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- LEAF. P0079 page 10, display 37 and the finite exponent sum after it.
The full continuous model has the geometric lower bound after spending
one quarter of lambda1 epsilon on the floor-count loss. This leaf contains
no truncation error and no prime-sum replacement. -/
theorem full_model_lower396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (13 / 4 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X *
        (cutoff293 s μ ε X) ^ s ≤
          (∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α).re := by
  exact major_full_lower396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- P0079 page 10, display 34. CONDITIONAL ON major_model_truncation396
and full_model_lower396. This is exactly the major_model_lower353 statement. -/
theorem major_model_lower396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X *
        (cutoff293 s μ ε X) ^ s ≤
          (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ := l1 * ε / (8 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_model_truncation396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ,
    full_model_lower396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'] with X he hm
  have hre := Complex.re_le_norm
    ((∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α))
  simp only [Complex.sub_re] at hre
  have hc : (1 - (13 / 4 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 - δ =
      (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 := by dsimp [δ]; ring
  nlinarith only [hre, he, hm, congrArg (fun c : ℝ => c * X * (cutoff293 s μ ε X) ^ s) hc]

end LeanLab.LZPowersOfTwo
