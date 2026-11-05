/-
P0079 pages 9 to 10, the major arc model and its replacement error.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 32. The continuous model for the prime sum. -/
def continuousPrime353 (ε X α : ℝ) : ℂ :=
  ∫ t in (ε * X)..X, character293 (t * α)

/-- P0079 page 9, display 33. The integrand of J1 replaces both prime sums
by their continuous models and keeps the power sums and the kernel. -/
def majorModel353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  continuousPrime353 ε X (l1 * α) * continuousPrime353 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- LEAF. P0079 page 9, displays 33 and 35. The combined J2 and J3 error
is little o of X L to the s. The written proof uses Lemmas 6 and 7 and the
prime number theorem. This leaf contains no lower bound for J1. -/
theorem major_replacement353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- LEAF. P0079 pages 9 to 10, displays 34, 36 and 37. The continuous
major model J1 has the stronger coefficient 1 minus seven halves lambda1 epsilon.
This leaf contains no approximation of the prime sums by the continuous model. -/
theorem major_model_lower353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X *
        (cutoff293 s μ ε X) ^ s ≤
          (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α).re := by
  sorry

/-- P0079 page 9, the conclusion after display 35. CONDITIONAL ON
major_replacement353 and major_model_lower353. This is the exact major target. -/
theorem major_lower353 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ := l1 * ε / (4 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_replacement353 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ,
    major_model_lower353 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'] with X he hm
  have hre := Complex.re_le_norm
    ((∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α))
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re] at hre
  have hc : (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 - δ =
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 := by dsimp [δ]; ring
  nlinarith only [hre, he, hm, congrArg (fun c : ℝ => c * X * (cutoff293 s μ ε X) ^ s) hc]

end LeanLab.LZPowersOfTwo
