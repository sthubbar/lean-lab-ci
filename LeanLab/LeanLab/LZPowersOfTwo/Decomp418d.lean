/-
P0079 page 9, sharing the one-prime discrepancy input between J2 and J3.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp418c
import LeanLab.LZPowersOfTwo.PrimeMajorMoment418
import LeanLab.LZPowersOfTwo.RiemannMajor396

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

set_option maxHeartbeats 800000 in
/-- P0079 page 9, the J3 Cauchy Schwarz estimate before display 36.
CONDITIONAL ON prime_integer_l2_small418. This preserves the exact statement
of major_second_discrepancy396 and shares the first-prime variance input. -/
theorem major_second_discrepancy_l2418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
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
  filter_upwards [prime_integer_l2_small418 ε l2 (by linarith) hε hε1 (a ^ 2) (by positivity),
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

/-- P0079 page 9, J3 in display 33. CONDITIONAL ON prime_integer_l2_small418.
This is the exact major_second_replacement375 statement. Both quadrature terms are proved. -/
theorem major_second_replacement_l2418 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖(∫ α in major293 X, integrand293 s l1 l2 μ γ η ε X α) -
        (∫ α in major293 X, mixedModel375 s l1 l2 μ γ η ε X α)‖ ≤
          δ * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [major_second_discrepancy_l2418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity),
    major_second_riemann_complete396 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
    (δ / 2) (by positivity)] with X hd hr
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

end LeanLab.LZPowersOfTwo
