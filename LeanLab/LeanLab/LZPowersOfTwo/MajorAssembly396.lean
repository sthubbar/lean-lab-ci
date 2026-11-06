/-
P0079 page 9, major-arc assembly with the continuous model proved.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp396a
import LeanLab.LZPowersOfTwo.Decomp396b

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, displays 33 to 35. CONDITIONAL ON
major_first_replacement375 and major_second_discrepancy396. Both continuous model inputs have clean proofs.
This is exactly the statement of major_lower375. -/
theorem major_lower396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ := l1 * ε / (4 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_replacement396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ,
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
