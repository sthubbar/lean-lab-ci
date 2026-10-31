/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
Normalized dense approximants with a full integer Fourier error estimate.
The full density range follows from the proved Lemma43.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSLemma43Full
import LeanLab.Ternary.MMSFullConvolution
namespace LeanLab.Ternary.MMS
open Finset

theorem prop31_approximation_general {ε K q τ κ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hK : 0 ≤ K) (hq : 2 < q) (hq3 : q < 3)
    (hτ : 0 < τ) (hκ : 0 < κ) :
    ∃ η₀ > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ f₁ f₂ f₃ : ℕ → ℝ,
      Prop31Hyp N η ε K q f₁ → Prop31Hyp N η ε K q f₂ → Prop31Hyp N η ε K q f₃ →
      ∃ u₁ u₂ u₃ : ℕ → ℝ, UnitValued N u₁ ∧ UnitValued N u₂ ∧ UnitValued N u₃ ∧
        DenseOnAPs N τ (ε / 4) u₁ ∧ DenseOnAPs N τ (ε / 4) u₂ ∧
        DenseOnAPs N τ (ε / 4) u₃ ∧
        ∀ n : ℕ, conv3 N u₁ u₂ u₃ n - conv3 N f₁ f₂ f₃ n ≤ κ * (N : ℝ) ^ 2 := by
  obtain ⟨δ₀, hδ₀, hδ₀1, herr₀⟩ := exists_uniform_error_scale hK hq3 (by positivity : 0 < κ / 3)
  let δ := min δ₀ (ε * τ / 2)
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have herr : δ ^ (3 - q) * K ^ q ≤ κ / 3 := by
    apply le_trans _ herr₀
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hδ.le (min_le_left _ _) (by linarith)) (Real.rpow_nonneg hK _)
  have hδτ : δ / ε ≤ τ / 2 := by
    apply (div_le_iff₀ hε).mpr
    have := min_le_right δ₀ (ε * τ / 2)
    dsimp [δ]
    linarith
  obtain ⟨C, hC, hmodel⟩ := lemma43_general_density hε hε1.le hK (by linarith : 0 < q) hδ
  let η₀ := min (ε / (4 * (C + 1))) (min (τ / 2) (1 / 2))
  have hη₀ : 0 < η₀ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηsmall N hN f₁ f₂ f₃ hf₁ hf₂ hf₃
  have hηC : η ≤ ε / (4 * (C + 1)) := hηsmall.trans (min_le_left _ _)
  have hητ : η ≤ τ / 2 := hηsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηhalf : η ≤ 1 / 2 := hηsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hη1 : η < 1 := by linarith
  have hCη : C * η ≤ ε / 4 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 4 * (C + 1))).mp hηC
    nlinarith
  have hscale : η + δ / ε ≤ τ := by linarith
  obtain ⟨g₁, h₁, hd₁, hb₁, hu₁, ha₁, hRg₁, hRh₁⟩ := hmodel η hη hη1 N hN f₁ hf₁
  obtain ⟨g₂, h₂, hd₂, hb₂, hu₂, ha₂, hRg₂, hRh₂⟩ := hmodel η hη hη1 N hN f₂ hf₂
  obtain ⟨g₃, h₃, hd₃, hb₃, hu₃, ha₃, hRg₃, hRh₃⟩ := hmodel η hη hη1 N hN f₃ hf₃
  have hεlt : ε < 1 := by linarith
  have hunit (g : ℤ →₀ ℝ) (hb : ∀ n : ℤ, 0 ≤ g n ∧ g n ≤ 1 + C * η) :
      UnitValued N (fun n => g n / (1 + ε / 4)) := by
    apply unitValued_normalize hε.le
    intro n hn
    exact ⟨(hb n).1, by linarith [(hb n).2]⟩
  have hdense (g : ℤ →₀ ℝ) (ha : DenseOnAPs N (η + δ / ε) (ε / 2) (fun n => g n)) :
      DenseOnAPs N τ (ε / 4) (fun n => g n / (1 + ε / 4)) := by
    apply denseOnAPs_normalize hε hεlt
    intro P hP hlen
    apply ha P hP
    exact (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg N)).trans hlen
  refine ⟨(fun n => g₁ n / (1 + ε / 4)), (fun n => g₂ n / (1 + ε / 4)),
    (fun n => g₃ n / (1 + ε / 4)), hunit g₁ hb₁, hunit g₂ hb₂, hunit g₃ hb₃,
    hdense g₁ ha₁, hdense g₂ ha₂, hdense g₃ ha₃, ?_⟩
  intro n
  let E := δ ^ (3 - q) * K ^ q * (N : ℝ) ^ 2
  have hNpos : 0 < N := by omega
  have hR₁ : intLq (intervalLift N f₁) q ≤ K * (N : ℝ) ^ (1 - 1 / q) := by
    simpa only [intLq_intervalLift] using hf₁.2.2.2
  have hR₂ : intLq (intervalLift N f₂) q ≤ K * (N : ℝ) ^ (1 - 1 / q) := by
    simpa only [intLq_intervalLift] using hf₂.2.2.2
  have hR₃ : intLq (intervalLift N f₃) q ≤ K * (N : ℝ) ^ (1 - 1 / q) := by
    simpa only [intLq_intervalLift] using hf₃.2.2.2
  have herror (u v w : ℤ →₀ ℝ) (hu : ∀ γ : ℝ, ‖intHat u γ‖ ≤ δ * N)
      (hRu : intLq u q ≤ K * (N : ℝ) ^ (1 - 1 / q))
      (hRv : intLq v q ≤ K * (N : ℝ) ^ (1 - 1 / q))
      (hRw : intLq w q ≤ K * (N : ℝ) ^ (1 - 1 / q)) :
      |fullConv3 u v w n| ≤ E :=
    abs_int_triple_uniform_bound u v w n hNpos hδ.le hK hq hq3 hu hRu hRv hRw
  have he₁ : |fullConv3 h₁ (g₂ + h₂) (g₃ + h₃) n| ≤ E := by
    rw [← hd₂, ← hd₃]
    exact herror h₁ _ _ hu₁ hRh₁ hR₂ hR₃
  have he₂ : |fullConv3 g₁ h₂ (g₃ + h₃) n| ≤ E := by
    rw [fullConv3_swap_left, ← hd₃]
    exact herror h₂ _ _ hu₂ hRh₂ hRg₁ hR₃
  have he₃ : |fullConv3 g₁ g₂ h₃ n| ≤ E := by
    rw [fullConv3_swap_right, fullConv3_swap_left]
    exact herror h₃ _ _ hu₃ hRh₃ hRg₁ hRg₂
  have hcomp := conv3_ge_of_integer_decomposition N n f₁ f₂ f₃ g₁ g₂ g₃ h₁ h₂ h₃ E
    hd₁ hd₂ hd₃ (fun n => (hb₁ n).1) (fun n => (hb₂ n).1) (fun n => (hb₃ n).1) he₁ he₂ he₃
  have hconv : 0 ≤ conv3 N (fun n => g₁ n) (fun n => g₂ n) (fun n => g₃ n) n :=
    conv3_nonneg (fun a ha => (hb₁ a).1) (fun a ha => (hb₂ a).1) (fun a ha => (hb₃ a).1)
  have hs : 1 ≤ (1 + ε / 4) ^ (3 : ℕ) := by
    exact one_le_pow₀ (by linarith)
  have hdiv := div_le_self hconv hs
  have hE : 3 * E ≤ κ * (N : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right herr (sq_nonneg (N : ℝ))
    dsimp [E]
    nlinarith
  rw [conv3_div]
  linarith
theorem prop31_small_density_approximation {ε K q τ κ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) (hK : 0 ≤ K) (hq : 2 < q) (hq3 : q < 3)
    (hτ : 0 < τ) (hκ : 0 < κ) :
    ∃ η₀ > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ N : ℕ, 1 ≤ N →
      ∀ f₁ f₂ f₃ : ℕ → ℝ,
      Prop31Hyp N η ε K q f₁ → Prop31Hyp N η ε K q f₂ → Prop31Hyp N η ε K q f₃ →
      ∃ u₁ u₂ u₃ : ℕ → ℝ, UnitValued N u₁ ∧ UnitValued N u₂ ∧ UnitValued N u₃ ∧
        DenseOnAPs N τ (ε / 4) u₁ ∧ DenseOnAPs N τ (ε / 4) u₂ ∧
        DenseOnAPs N τ (ε / 4) u₃ ∧
        ∀ n : ℕ, conv3 N u₁ u₂ u₃ n - conv3 N f₁ f₂ f₃ n ≤ κ * (N : ℝ) ^ 2 := by
  exact prop31_approximation_general hε (by linarith) hK hq hq3 hτ hκ

/-- The earlier analytic approximation interface is now proved. -/
theorem prop31_approximation_proved : Prop31Approximation := by
  intro ε hε hε1 τ κ hτ hκ K q hK hq hq3
  obtain ⟨η₀, hη₀, hA⟩ := prop31_approximation_general hε hε1
    (by linarith : 0 ≤ K) hq hq3 hτ hκ
  refine ⟨η₀, hη₀, 1, ?_⟩
  intro η hη hηsmall N f₁ f₂ f₃ hN hf₁ hf₂ hf₃
  obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hd₁, hd₂, hd₃, herr⟩ :=
    hA η hη hηsmall N hN f₁ f₂ f₃ hf₁ hf₂ hf₃
  exact ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hd₁, hd₂, hd₃, fun n _ _ => herr n⟩

end LeanLab.Ternary.MMS
