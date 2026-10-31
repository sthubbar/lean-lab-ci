/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
The dense proposition implies sparse transference with no additional analytic input.
Both implications remain CONDITIONAL ON their explicit dense or regularity input.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSApproximation
namespace LeanLab.Ternary.MMS

theorem prop31_of_prop32 (H32 : Prop32) : Prop31 := by
  intro ε hε hε1
  let e := min ε (1 / 6)
  have he : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 / 6 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  obtain ⟨τ, hτ, d, hd, Nd, hD⟩ := H32 (e / 4) (by positivity)
  refine ⟨d / 2, by positivity, ?_⟩
  intro K q hK hq hq3
  obtain ⟨η₀, hη₀, hA⟩ := prop31_small_density_approximation he he1
    (by linarith : 0 ≤ K) hq hq3 hτ (by positivity : 0 < d / 2)
  refine ⟨(d / 2) / η₀, ?_⟩
  intro η hη hη1
  refine ⟨max Nd 1, ?_⟩
  intro N f₁ f₂ f₃ hN hf₁ hf₂ hf₃ n hn hnN
  have hN0 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  by_cases hsmall : η ≤ η₀
  · have h₁ : Prop31Hyp N η e K q f₁ :=
      ⟨hf₁.1, dense_mono heε hf₁.2.1, hf₁.2.2⟩
    have h₂ : Prop31Hyp N η e K q f₂ :=
      ⟨hf₂.1, dense_mono heε hf₂.2.1, hf₂.2.2⟩
    have h₃ : Prop31Hyp N η e K q f₃ :=
      ⟨hf₃.1, dense_mono heε hf₃.2.1, hf₃.2.2⟩
    obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hd₁, hd₂, hd₃, herr⟩ :=
      hA η hη hsmall N ((le_max_right _ _).trans hN) f₁ f₂ f₃ h₁ h₂ h₃
    have hmain := hD N u₁ u₂ u₃ ((le_max_left _ _).trans hN)
      hu₁ hu₂ hu₃ hd₁ hd₂ hd₃ n hn hnN
    have he := herr n
    have hC : 0 ≤ (d / 2) / η₀ * η := by positivity
    have hCN := mul_nonneg hC hN0
    nlinarith
  · have hlarge : η₀ ≤ η := (lt_of_not_ge hsmall).le
    have hC : d / 2 ≤ (d / 2) / η₀ * η := by
      calc d / 2 = (d / 2) / η₀ * η₀ := by field_simp
           _ ≤ (d / 2) / η₀ * η := mul_le_mul_of_nonneg_left hlarge (by positivity)
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hC) hN0).trans
      (conv3_nonneg hf₁.1 hf₂.1 hf₃.1)

theorem prop31_of_thm41 (H41 : Thm41) : Prop31 :=
  prop31_of_prop32 (prop32_of_thm41 H41)
end LeanLab.Ternary.MMS
