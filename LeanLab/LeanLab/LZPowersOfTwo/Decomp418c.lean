/-
P0079 pages 8 to 9, a one-prime truncated second moment for the J2 input.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ModelMoment418
import LeanLab.LZPowersOfTwo.WeightedMajor418

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- LEAF. P0079 page 8, Lemmas 6 and 7, and page 9, the Cauchy Schwarz
estimate before display 36. The truncated squared norm of S minus U is
little o of X divided by log X. The written Selberg bound gives arbitrary logarithmic saving.
Saffari Vaughan Section 6, pages 24 to 25, proves the cited variance input.
This leaf has one prime sum, one integer sum, and no power sums or shift. -/
theorem prime_integer_l2_small418 (ε l : ℝ) (hl : l ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      (∫ α in major293 X,
        ‖primeSum293 ε X (l * α) - discretePrime396 ε X (l * α)‖ ^ 2) ≤ δ * X / log X := by
  sorry

set_option maxHeartbeats 800000 in
/-- P0079 page 9, the J2 estimate after display 35.
CONDITIONAL ON prime_integer_l2_small418. This is the exact first-prime
discrepancy target. The continuous second moment and weighted Cauchy Schwarz are proved. -/
theorem major_first_discrepancy_l2418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, discreteFirstModel418 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  let C := 2 + 2 * (1 / (Real.pi * |l2|)) ^ 2
  let b := C + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : 0 < b := by dsimp [b]; linarith
  intro δ hδ
  let a := δ / (η ^ 2 * b)
  have ha : 0 < a := by dsimp [a]; positivity
  filter_upwards [prime_integer_l2_small418 ε l1 (by linarith) hε hε1 (a ^ 2) (by positivity),
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (1 : ℝ),
    tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with X hdisc hL hX hlog
  let f : ℝ → ℂ := fun α => primeSum293 ε X (l1 * α) - discretePrime396 ε X (l1 * α)
  let g : ℝ → ℂ := fun α => continuousPrime353 ε X (l2 * α)
  let h : ℝ → ℂ := fun α =>
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
      character293 (γ * α) * kernel293 η α
  have hf : Continuous f := by
    dsimp [f]
    unfold primeSum293 discretePrime396 character293
    fun_prop
  have hg : Continuous g :=
    (continuousPrime_continuous418 ε X).comp (continuous_const.mul continuous_id)
  have hh : Continuous h := by
    dsimp [h]
    unfold powerSum293 character293 kernel293
    fun_prop
  have hH : ∀ α ∈ major293 X, ‖h α‖ ≤ η ^ 2 * (cutoff293 s μ ε X) ^ s := by
    intro α _
    have hG : ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤
        (cutoff293 s μ ε X) ^ s := by
      calc
        _ ≤ ∏ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ := norm_prod_le _ _
        _ ≤ ∏ _ : Fin s, cutoff293 s μ ε X := by
          apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i hi
          exact (powerSum_norm_le293 _ _).trans (by simpa using Nat.floor_le hL)
        _ = _ := by simp
    simp only [h, norm_mul, character_norm293, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg293 η α)]
    exact (mul_le_mul hG (kernel_le293 η α) (kernel_nonneg293 η α) (pow_nonneg hL s)).trans_eq
      (mul_comm _ _)
  have hG : (∫ α in major293 X, ‖g α‖ ^ 2) ≤ b ^ 2 * X := by
    have hi := continuousPrime_square_integrable418 ε X l2 (by linarith)
    calc
      _ ≤ ∫ α : ℝ, ‖g α‖ ^ 2 :=
        setIntegral_le_integral hi (Eventually.of_forall (fun α => sq_nonneg _))
      _ ≤ C * X := continuousPrime_second_moment418 ε X l2 (by linarith)
        (by linarith) hε.le hε1.le
      _ ≤ b ^ 2 * X := mul_le_mul_of_nonneg_right (by dsimp [b]; nlinarith [sq_nonneg C]) (by linarith)
  have hdisc' : (∫ α in major293 X, ‖f α‖ ^ 2) ≤ a ^ 2 * X :=
    hdisc.trans (div_le_self (by positivity) hlog)
  have H := weighted_major_product418 f g h hf hg hh X
    (η ^ 2 * (cutoff293 s μ ε X) ^ s) a b X (by positivity) ha hb hH hdisc' hG
  have he : (fun α => mixedModel375 s l1 l2 μ γ η ε X α -
      discreteFirstModel418 s l1 l2 μ γ η ε X α) = (fun α => f α * g α * h α) := by
    funext α
    dsimp [f, g, h, mixedModel375, discreteFirstModel418]
    ring
  have hT : Continuous (continuousPrime353 ε X) := continuousPrime_continuous418 ε X
  have hdis : Continuous (discreteFirstModel418 s l1 l2 μ γ η ε X) := by
    unfold discreteFirstModel418 discretePrime396 powerSum293 character293 kernel293
    fun_prop
  have hmix : Continuous (mixedModel375 s l1 l2 μ γ η ε X) := by
    unfold mixedModel375 primeSum293 powerSum293 character293 kernel293
    fun_prop
  rw [← integral_sub (continuous_major_integrable418 _ hmix X)
    (continuous_major_integrable418 _ hdis X), he]
  apply H.trans_eq
  dsimp [a]
  field_simp

end LeanLab.LZPowersOfTwo
