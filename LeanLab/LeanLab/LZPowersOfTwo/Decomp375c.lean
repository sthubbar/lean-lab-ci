/-
P0079 pages 9 to 10, continuous geometry and major-arc truncation.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp375b
import LeanLab.LZPowersOfTwo.ModelFourier353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- LEAF. P0079 page 10, displays 36 and 37, the full-line continuous model.
The rectangle lower bound has coefficient 1 minus 3 lambda1 epsilon.
Passing from the finite exponent count to L to the s spends one quarter lambda1
epsilon here. This leaf has no restriction to the major arc and no prime sum. -/
theorem major_full_lower375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (13 / 4 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X *
        (cutoff293 s μ ε X) ^ s ≤
          (∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α).re := by
  sorry

/-- LEAF. P0079 page 10, display 36, its O of eta squared X to the two thirds
L to the s truncation term, obtained from display 32 and the kernel bound.
Removing the complement of the major arc changes only the continuous model
by little o of X L to the s. This leaf has no geometric lower bound. -/
theorem major_model_tail375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- P0079 pages 9 to 10, display 34. CONDITIONAL ON major_full_lower375
and major_model_tail375. This is the exact sealed continuous-major target. -/
theorem major_model_lower375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X *
        (cutoff293 s μ ε X) ^ s ≤
          (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ : ℝ := l1 * ε / (8 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_full_lower375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε',
    major_model_tail375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ] with X hfull htail
  have hre := Complex.re_le_norm
    ((∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α))
  simp only [Complex.sub_re] at hre
  have heq : (1 - (13 / 4 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 - δ =
      (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 := by dsimp [δ]; ring
  nlinarith only [hfull, htail, hre,
    congrArg (fun c : ℝ => c * X * (cutoff293 s μ ε X) ^ s) heq]

/-- P0079 page 9, conclusion after display 35. CONDITIONAL ON the four
smaller major leaves in Decomp375b and Decomp375c. This is the exact major target. -/
theorem major_lower375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ := l1 * ε / (4 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_replacement375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ,
    major_model_lower375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'] with X he hm
  have hre := Complex.re_le_norm
    ((∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α))
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re] at hre
  have hc : (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 - δ =
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 := by dsimp [δ]; ring
  nlinarith only [hre, he, hm, congrArg (fun c : ℝ => c * X * (cutoff293 s μ ε X) ^ s) hc]

end LeanLab.LZPowersOfTwo
