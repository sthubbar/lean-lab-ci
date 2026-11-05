/-
P0079 page 9, display 33 and the two separate replacement errors.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp353b

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 9, display 33. The intermediate model replaces only the
second prime sum by its continuous model. -/
def mixedModel375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α : ℝ) : ℂ :=
  primeSum293 ε X (l1 * α) * continuousPrime353 ε X (l2 * α) *
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
    character293 (γ * α) * kernel293 η α

/-- LEAF. P0079 page 9, display 33, the J3 estimate ending before display 35.
Only the second prime sum is replaced. The written proof uses partial summation,
Cauchy Schwarz, Lemmas 6 and 7, and the prime second moment. See also Saffari
and Vaughan, Section 6, pages 24 to 25, Lemma 6 and its written proof. -/
theorem major_second_replacement375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- LEAF. P0079 page 9, after display 35, the analogous J2 estimate.
Only the first prime sum is replaced and the second factor is already continuous.
The written proof uses display 32 instead of the prime number theorem.
Saffari and Vaughan, Section 6, pages 24 to 25, gives the cited Selberg step. -/
theorem major_first_replacement375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  sorry

/-- P0079 page 9, display 35. CONDITIONAL ON major_second_replacement375
and major_first_replacement375. This is the exact sealed replacement target. -/
theorem major_replacement375 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_replacement375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' (δ / 2) (by positivity),
    major_first_replacement375 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' (δ / 2) (by positivity)] with X hsecond hfirst
  calc
    _ ≤ ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
          (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ +
        ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
          (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith only [hsecond, hfirst]

end LeanLab.LZPowersOfTwo
