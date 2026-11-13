/-
ROUTE BURST session 8, part 2 of the LZPowersOfTwo split: the new top-level assembly.
Paper: P0079 A. Languasco and A. Zaccagnini, "On a Diophantine problem with two primes and
s powers of two", arXiv 0811.3663v2, 2 Apr 2009.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

`lz_theorem_tr_of_p2 : MainStatement nuTr IsTr` is the session 4 assembly
`Burst4Split.lz_theorem_tr_of_split` with its three cited leaves replaced by the burst 8
proofs, each with no open step of its own:
* `paired_second_moment_p2`, Burst8Lemma4.lean, for `paired_second_moment_sharpB4`;
* `minor_bad_tr_p2`, Burst8MinorBad.lean, for `minor_bad353`;
* `prime_integer_l2_small_p3`, Burst8Gallagher.lean, for `prime_integer_l2_small418`.
The proofs below are copies of the existing folder proofs of Decomp418c, Decomp418d,
Decomp418b and Burst4Split, with only the names of the replaced inputs changed. The theorem
is CONDITIONAL ON the cited outside inputs listed in research/burst-20261112/LZPowersOfTwo-p2.md.
-/
import LeanLab.LZPowersOfTwo.Burst8Lemma4
import LeanLab.LZPowersOfTwo.Burst8Gallagher
import LeanLab.LZPowersOfTwo.Burst8MinorBad

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst8P2

open LeanLab.LZPowersOfTwo LeanLab.LZPowersOfTwo.Burst4Split

/-! ### Display (16), the major arc, copied from Decomp418c, Decomp418d and Decomp418b -/

set_option maxHeartbeats 800000 in
/-- P0079 page 9, the J2 estimate after display 35.
CONDITIONAL ON prime_integer_l2_small_p3. This is the exact first-prime
discrepancy target. The continuous second moment and weighted Cauchy Schwarz are proved. -/
theorem major_first_discrepancy_l2_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
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
  filter_upwards [prime_integer_l2_small_p3 ε l1 (by linarith) hε hε1 (a ^ 2) (by positivity),
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

set_option maxHeartbeats 800000 in
/-- P0079 page 9, the J3 Cauchy Schwarz estimate before display 36.
CONDITIONAL ON prime_integer_l2_small_p3. This preserves the exact statement
of major_second_discrepancy396 and shares the first-prime variance input. -/
theorem major_second_discrepancy_l2_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, discreteSecondModel396 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  let C := log 4 / |l1|
  let b := C + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : 0 < b := by dsimp [b]; linarith
  intro δ hδ
  let a := δ / (η ^ 2 * b)
  have ha : 0 < a := by dsimp [a]; positivity
  filter_upwards [prime_integer_l2_small_p3 ε l2 (by linarith) hε hε1 (a ^ 2) (by positivity),
    prime_major_moment418 ε l1 (by linarith),
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (1 : ℝ),
    tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with X hdisc hprime hL hX hlog
  let f : ℝ → ℂ := fun α => primeSum293 ε X (l1 * α)
  let g : ℝ → ℂ := fun α => primeSum293 ε X (l2 * α) - discretePrime396 ε X (l2 * α)
  let h : ℝ → ℂ := fun α =>
    (∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)) *
      character293 (γ * α) * kernel293 η α
  have hf : Continuous f := by
    dsimp [f]
    unfold primeSum293 character293
    fun_prop
  have hg : Continuous g := by
    dsimp [g]
    unfold primeSum293 discretePrime396 character293
    fun_prop
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
  have hroot : 0 < sqrt (log X) := sqrt_pos.mpr hlog
  have hF : (∫ α in major293 X, ‖f α‖ ^ 2) ≤ (b * sqrt (log X)) ^ 2 * X := by
    calc
      _ ≤ C * X * log X := hprime
      _ ≤ b ^ 2 * X * log X := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp [b]; nlinarith [sq_nonneg C]) (by linarith)) hlog.le
      _ = _ := by rw [mul_pow, sq_sqrt hlog.le]; ring
  have hG : (∫ α in major293 X, ‖g α‖ ^ 2) ≤ (a / sqrt (log X)) ^ 2 * X := by
    have heq : (a / sqrt (log X)) ^ 2 = a ^ 2 / log X := by
      calc
        _ = a ^ 2 / (sqrt (log X)) ^ 2 := div_pow a _ 2
        _ = _ := by rw [sq_sqrt hlog.le]
    apply hdisc.trans_eq
    rw [heq]
    ring
  have H := weighted_major_product418 f g h hf hg hh X
    (η ^ 2 * (cutoff293 s μ ε X) ^ s) (b * sqrt (log X)) (a / sqrt (log X)) X
      (by positivity) (by positivity) (by positivity) hH hF hG
  have he : (fun α => integrand293 s l1 l2 μ γ η ε X α -
      discreteSecondModel396 s l1 l2 μ γ η ε X α) = (fun α => f α * g α * h α) := by
    funext α
    dsimp [f, g, h, integrand293, discreteSecondModel396]
    ring
  have hdis : Continuous (discreteSecondModel396 s l1 l2 μ γ η ε X) := by
    unfold discreteSecondModel396 discretePrime396 primeSum293 powerSum293 character293 kernel293
    fun_prop
  rw [← integral_sub (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn
    (continuous_major_integrable418 _ hdis X), he]
  apply H.trans_eq
  dsimp [a]
  field_simp

/-- P0079 page 9, J3 in display 33. CONDITIONAL ON prime_integer_l2_small_p3.
This is the exact major_second_replacement375 statement. Both quadrature terms are proved. -/
theorem major_second_replacement_l2_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_discrepancy_l2_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_second_riemann_complete396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X hd hr
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

/-- P0079 page 9, display 33, J2, and the written analogous estimate
following display 35. The S minus U contribution replaces the first prime sum
by the integer sum while the second factor is continuous. Lemmas 6 and 7
supply the prime discrepancy. Saffari Vaughan Section 6, pages 24 to 25,
gives the cited unsmoothed Selberg argument. No U minus T error occurs here. -/
theorem major_first_discrepancy_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, discreteFirstModel418 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  exact major_first_discrepancy_l2_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'

/-- P0079 page 9, J2 in display 33. CONDITIONAL ON major_first_discrepancy_p2.
The exact major_first_replacement375 statement uses the proved quadrature bridge. -/
theorem major_first_replacement_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_first_discrepancy_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_first_riemann418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X hd hr
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

/-- P0079 page 9, display 35. CONDITIONAL ON prime_integer_l2_small_p3. This is the exact major_replacement353 statement. -/
theorem major_replacement_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_replacement_l2_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_first_replacement_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
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
prime_integer_l2_small_p3. The continuous model input is proved. This is the exact major target. -/
theorem major_lower_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X * (cutoff293 s μ ε X) ^ s ≤
        (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α).re := by
  have hp : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  let δ := l1 * ε / (4 * |l1 * l2|) * η ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [major_replacement_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε' δ hδ,
    major_model_lower396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'] with X he hm
  have hre := Complex.re_le_norm
    ((∫ α in major293 X, majorModel353 s l1 l2 μ γ η ε X α) -
      (∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α))
  rw [norm_sub_rev] at hre
  simp only [Complex.sub_re] at hre
  have hc : (1 - (7 / 2 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 - δ =
      (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 := by dsimp [δ]; ring
  nlinarith only [hre, he, hm, congrArg (fun c : ℝ => c * X * (cutoff293 s μ ε X) ^ s) hc]


/-! ### (18), the minor arc, with the constant of (28) -/

/-- P0079 page 11, display (41), ordinary part of the minor arc.
CONDITIONAL ON `paired_second_moment_p2`. The proof is the one of `minor_good396`
with the constant of display (28). -/
theorem minor_good_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1)
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X),
        integrand293 s l1 l2 μ γ η ε X α‖ ≤
          (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  have hν : 0 ≤ ν := by
    rcases hc with h | h
    · rw [h.1]; exact nuTr_pos.le
    · rw [h.1]; exact nuAlg_pos.le
  have hA : 0 < log 2 + bigCSharpB4 * Sprime r1.den := add_pos_of_pos_of_nonneg
    (log_pos (by norm_num)) (mul_nonneg bigCSharp_pos.le (Sprime_pos293 _).le)
  have hB : 0 < log 2 + bigCSharpB4 * Sprime r2.den := add_pos_of_pos_of_nonneg
    (log_pos (by norm_num)) (mul_nonneg bigCSharp_pos.le (Sprime_pos293 _).le)
  let a := sqrt (log 2 + bigCSharpB4 * Sprime r1.den)
  let b := sqrt (log 2 + bigCSharpB4 * Sprime r2.den)
  have ha : 0 < a := sqrt_pos.mpr hA
  have hb : 0 < b := sqrt_pos.mpr hB
  intro δ hδ
  filter_upwards [paired_second_moment_p2 s μ l1 (μ 0) η ε hM (by linarith) (hμ 0)
    r1 hr1 hη hη1 hε hε1,
    paired_second_moment_p2 s μ l2 (μ 1) η ε hM (by linarith) (hμ 1)
    r2 hr2 hη hη2 hε hε1,
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (2 : ℝ)] with X hm1 hm2 hL hX
  let E := minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hE : MeasurableSet E := by
    apply MeasurableSet.diff _ hbad
    unfold minor293
    measurability
  have hG : ∀ α ∈ E, ∀ i : Fin s,
      ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ ν * cutoff293 s μ ε X := by
    intro α hα i
    by_contra H
    exact hα.2 ⟨i, lt_of_not_ge H⟩
  have hm1' : (∫ α : ℝ, pairedMoment396 l1 (μ 0) (cutoff293 s μ ε X) η ε X α) ≤
      a ^ 2 * (η * X * (cutoff293 s μ ε X) ^ 2) := by
    simpa only [a, sq_sqrt hA.le, mul_assoc] using hm1
  have hm2' : (∫ α : ℝ, pairedMoment396 l2 (μ 1) (cutoff293 s μ ε X) η ε X α) ≤
      b ^ 2 * (η * X * (cutoff293 s μ ε X) ^ 2) := by
    simpa only [b, sq_sqrt hB.le, mul_assoc] using hm2
  have H := paired_integral_bound396 s l1 l2 μ γ η ε X (ν * cutoff293 s μ ε X)
    a b (η * X * (cutoff293 s μ ε X) ^ 2) E hE hs (mul_nonneg hν hL) ha hb hG hm1' hm2'
  have hp : (cutoff293 s μ ε X) ^ (s - 2) * (cutoff293 s μ ε X) ^ 2 =
      (cutoff293 s μ ε X) ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have he : (ν * cutoff293 s μ ε X) ^ (s - 2) * a * b *
      (η * X * (cutoff293 s μ ε X) ^ 2) =
        ν ^ (s - 2) * CqSharpB4 r1.den r2.den * η * X * (cutoff293 s μ ε X) ^ s := by
    calc
      _ = ν ^ (s - 2) * CqSharpB4 r1.den r2.den * η * X *
          ((cutoff293 s μ ε X) ^ (s - 2) * (cutoff293 s μ ε X) ^ 2) := by
        dsimp [a, b, CqSharpB4]
        rw [mul_pow]
        ring
      _ = _ := by rw [hp]
  apply H.trans
  rw [he]
  have hW : 0 ≤ η * X * (cutoff293 s μ ε X) ^ s := by positivity
  nlinarith only [mul_nonneg hδ.le hW]

/-- P0079 pages 11 to 12, displays (41) to (43), the conclusion (18) with the constant of
display (28), for `λ1/λ2` transcendental, section 7.
CONDITIONAL ON `paired_second_moment_p2` and `minor_bad_tr_p2`. -/
theorem minor_upper_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : ν = nuTr ∧ IsTr (l1 / l2))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [minor_good_p2 ν s l1 l2 μ γ η ε hs h1 h2 (Or.inl hc) hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity),
    minor_bad_tr_p2 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity)] with X hg hb
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hsplit := integral_inter_add_sdiff (s := minor293 X (cutoff293 s μ ε X)) hbad
    (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn
  rw [← hsplit]
  calc
    _ ≤ ‖∫ α in minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ +
      ‖∫ α in minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### Assembly of (13), (16), (17), (18), (19) -/

/-- P0079 pages 4 to 5, displays (13) to (19), with the minor constant of display (28).
CONDITIONAL ON `prime_integer_l2_small_p3`, `paired_second_moment_p2` and
`minor_bad_tr_p2`. Counting, display (13), is `count_integral353`, PROVED; the trivial arc,
display (17), is `trivial_small418`, PROVED; the major arc, display (16), is
`major_lower_p2`. The proof follows `count_bound_at_margin418`. -/
theorem count_bound_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : ν = nuTr ∧ IsTr (l1 / l2))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1))
    (hM : 0 < ∑ i : Fin s, |μ i|)
    (hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η -
      ν ^ (s - 2) * CqSharpB4 r1.den r2.den) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c * X * (cutoff293 s μ ε X) ^ s ≤
        η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  let gap := (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * CqSharpB4 r1.den r2.den
  have hg : 0 < gap := hgap
  have hε1 : ε < 1 := by
    have hd : 1 / (8 * l1) < (1 : ℝ) := (div_lt_one (by positivity)).mpr (by linarith)
    exact hε'.trans hd
  have Hmajor := major_lower_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
  have Hminor := minor_upper_p2 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (gap / 4) (by positivity)
  have Htrivial := trivial_small418 s l1 l2 μ γ η ε hs (by linarith) (by linarith)
    hμ hη hε hε1 (gap * η / 4) (by positivity)
  refine ⟨gap * η / 2, by positivity, ?_⟩
  filter_upwards [Hmajor, Hminor, Htrivial, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2 * ∑ i : Fin s, |μ i|) / ε)] with X hmajor hminor htrivial hX hXM
  obtain ⟨hint, hcount⟩ := count_integral353 s l1 l2 μ γ η ε X hη hε hX
  have hL : 0 ≤ cutoff293 s μ ε X := cutoff_nonneg293 s μ ε X hM
    (by simpa [mul_comm] using (div_le_iff₀ hε).mp hXM)
  have hW : 0 ≤ X * (cutoff293 s μ ε X) ^ s := mul_nonneg (by linarith) (pow_nonneg hL _)
  have hbound := arc_lower293 (integrand293 s l1 l2 μ γ η ε X) hint X
    (cutoff293 s μ ε X)
    ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2)
    ((ν ^ (s - 2) * CqSharpB4 r1.den r2.den + gap / 4) * η)
    (gap * η / 4) (X * (cutoff293 s μ ε X) ^ s)
    (by nlinarith only [hmajor]) (by nlinarith only [hminor]) (by nlinarith only [htrivial])
  have heq : ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 -
      (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + gap / 4) * η - gap * η / 4) = gap * η / 2 := by
    dsimp [gap]
    ring
  rw [heq] at hbound
  nlinarith only [hbound, hcount]

/-! ### The main theorem from the split -/

/-- P0079 Theorem, `λ1/λ2` transcendental, `s0` from (2), the exact type of
`LeanLab.LZPowersOfTwo.lz_theorem_tr`. CONDITIONAL ON `prime_integer_l2_small_p3`,
`paired_second_moment_p2` and `minor_bad_tr_p2`; this proof itself has no open step.
The threshold `η0` is `1`: every `η` allowed by the lattice bounds works. -/
theorem lz_theorem_tr_of_p2 : MainStatement nuTr IsTr := by
  intro l1 l2 μ h1 h2 hr hi hk hμ r1 r2 hr1 hr2
  refine ⟨1, one_pos, fun η hη _ hη1 hη2 γ s hs hs0 => ?_⟩
  have hη1' : η < |l1 / r1.num| := hη1.trans_le (le_abs_self _)
  have hl : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  obtain ⟨ε, hε, hε', hgap⟩ := margin_B4 nuTr l1 l2 η r1.den r2.den s nuTr_pos nuTr_lt_one
    h1 hl hη hs hs0
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hc : nuTr = nuTr ∧ IsTr (l1 / l2) := ⟨rfl, hk⟩
  obtain ⟨c, hc', H⟩ := count_bound_p2 nuTr s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ
    r1 r2 hr1 hr2 hη hη1' hη2 hε hε' hM hgap
  exact infinite_of_NX_lower293 (count_to_density293 s l1 l2 μ γ η ε c hs hM hη hε hc' H)

/-- The type agrees with the cited statement. -/
example : MainStatement nuTr IsTr := lz_theorem_tr_of_p2

/-- The type agrees with the cited statement `LeanLab.LZPowersOfTwo.lz_theorem_tr`. -/
example : MainStatement nuTr IsTr := lz_theorem_tr_of_p2

/-- P0079 pages 11 to 12, displays (41) to (43), the conclusion (18) with the constant of
display (28). CONDITIONAL ON `paired_second_moment_p2` and `minor_bad_p2`. -/
theorem minor_upper_gen_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [minor_good_p2 ν s l1 l2 μ γ η ε hs h1 h2 hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity),
    minor_bad_p2 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity)] with X hg hb
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hsplit := integral_inter_add_sdiff (s := minor293 X (cutoff293 s μ ε X)) hbad
    (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn
  rw [← hsplit]
  calc
    _ ≤ ‖∫ α in minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ +
      ‖∫ α in minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### Both cases of (18), and the algebraic case of the Theorem -/

/-- P0079 pages 4 to 5, displays (13) to (19), with the minor constant of display (28).
CONDITIONAL ON `prime_integer_l2_small_p3`, `paired_second_moment_p2` and
`minor_bad_p2`. Counting, display (13), is `count_integral353`, PROVED; the trivial arc,
display (17), is `trivial_small418`, PROVED; the major arc, display (16), is
`major_lower_p2`. The proof follows `count_bound_at_margin418`. -/
theorem count_bound_gen_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1))
    (hM : 0 < ∑ i : Fin s, |μ i|)
    (hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η -
      ν ^ (s - 2) * CqSharpB4 r1.den r2.den) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c * X * (cutoff293 s μ ε X) ^ s ≤
        η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  let gap := (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * CqSharpB4 r1.den r2.den
  have hg : 0 < gap := hgap
  have hε1 : ε < 1 := by
    have hd : 1 / (8 * l1) < (1 : ℝ) := (div_lt_one (by positivity)).mpr (by linarith)
    exact hε'.trans hd
  have Hmajor := major_lower_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
  have Hminor := minor_upper_gen_p2 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (gap / 4) (by positivity)
  have Htrivial := trivial_small418 s l1 l2 μ γ η ε hs (by linarith) (by linarith)
    hμ hη hε hε1 (gap * η / 4) (by positivity)
  refine ⟨gap * η / 2, by positivity, ?_⟩
  filter_upwards [Hmajor, Hminor, Htrivial, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2 * ∑ i : Fin s, |μ i|) / ε)] with X hmajor hminor htrivial hX hXM
  obtain ⟨hint, hcount⟩ := count_integral353 s l1 l2 μ γ η ε X hη hε hX
  have hL : 0 ≤ cutoff293 s μ ε X := cutoff_nonneg293 s μ ε X hM
    (by simpa [mul_comm] using (div_le_iff₀ hε).mp hXM)
  have hW : 0 ≤ X * (cutoff293 s μ ε X) ^ s := mul_nonneg (by linarith) (pow_nonneg hL _)
  have hbound := arc_lower293 (integrand293 s l1 l2 μ γ η ε X) hint X
    (cutoff293 s μ ε X)
    ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2)
    ((ν ^ (s - 2) * CqSharpB4 r1.den r2.den + gap / 4) * η)
    (gap * η / 4) (X * (cutoff293 s μ ε X) ^ s)
    (by nlinarith only [hmajor]) (by nlinarith only [hminor]) (by nlinarith only [htrivial])
  have heq : ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 -
      (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + gap / 4) * η - gap * η / 4) = gap * η / 2 := by
    dsimp [gap]
    ring
  rw [heq] at hbound
  nlinarith only [hbound, hcount]

/-- P0079 Theorem, `λ1/λ2` algebraic, `s0` from (2), the exact type of
`LeanLab.LZPowersOfTwo.lz_theorem_alg`, by the same route with section 6 for the minor arc.
CONDITIONAL ON `prime_integer_l2_small_p3`, `paired_second_moment_p2` and `minor_bad_p2`,
hence on `saffari_vaughan_lemma7_p2`, `chen_lemma3_p2`, `khalfalah_pintz_lemma1_p2`,
`lemma5_alg_p2` and `bcp39_alg_p2`; this proof itself has no open step. -/
theorem lz_theorem_alg_of_p2 : MainStatement nuAlg IsAlg := by
  intro l1 l2 μ h1 h2 hr hi hk hμ r1 r2 hr1 hr2
  refine ⟨1, one_pos, fun η hη _ hη1 hη2 γ s hs hs0 => ?_⟩
  have hη1' : η < |l1 / r1.num| := hη1.trans_le (le_abs_self _)
  have hl : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  obtain ⟨ε, hε, hε', hgap⟩ := margin_B4 nuAlg l1 l2 η r1.den r2.den s nuAlg_pos nuAlg_lt_one
    h1 hl hη hs hs0
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hc : (nuAlg = nuTr ∧ IsTr (l1 / l2)) ∨ (nuAlg = nuAlg ∧ IsAlg (l1 / l2)) :=
    Or.inr ⟨rfl, hk⟩
  obtain ⟨c, hc', H⟩ := count_bound_gen_p2 nuAlg s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ
    r1 r2 hr1 hr2 hη hη1' hη2 hε hε' hM hgap
  exact infinite_of_NX_lower293 (count_to_density293 s l1 l2 μ γ η ε c hs hM hη hε hc' H)

/-- The type agrees with the cited statement `LeanLab.LZPowersOfTwo.lz_theorem_alg`. -/
example : MainStatement nuAlg IsAlg := lz_theorem_alg_of_p2

end LeanLab.LZPowersOfTwo.Burst8P2
