/-
P0079 page 9, the discrete intermediary in the written J3 proof.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.DiscreteModel396
import LeanLab.LZPowersOfTwo.RiemannMajor396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- LEAF. P0079 page 9, the displayed J3 estimate using Lemmas 6 and 7.
The S minus U contribution has little o size. Its proof needs the Selberg
integral input. This leaf contains no U minus T error. -/
theorem major_second_discrepancy396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, discreteSecondModel396 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- LEAF. P0079 page 9, the first displayed partial-summation estimate
in the J3 proof. The U minus T contribution has little o size from
T minus U bounded by 1 plus X absolute alpha and the trivial prime bound.
This leaf contains no prime versus integer discrepancy. -/
theorem major_second_riemann396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, discreteSecondModel396 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  exact major_second_riemann_complete396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- P0079 page 9, J3 in display 33. CONDITIONAL ON
major_second_discrepancy396 and major_second_riemann396. This is the exact
major_second_replacement375 statement, assembled without its old OPEN input. -/
theorem major_second_replacement_decomp396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_discrepancy396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_second_riemann396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X h1 h2
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

end LeanLab.LZPowersOfTwo
