/-
Shao Theorem 1.3 with an explicit residue profile and a reusable lifting step.
Source: https://arxiv.org/abs/1206.6139v2 pages 15 to 17.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408a
import LeanLab.DensityGoldbach.Profiles408
import LeanLab.DensityGoldbach.U1488Window

open Finset

namespace LeanLab.DensityGoldbach.Decomp408b

/-- LEAF. Shao page 17 Lemma 4.6 at q = 5/2, citing Green
math/0302311 Lemma 6.6. The lab's Green66p uses expectation normalization;
scaling by 1/N gives Shao's probability weight normalization. -/
theorem restriction_five_halves : U1488.Green66p (5 / 2) := by
  sorry

/-- LEAF. Shao pages 15 to 16, equation 29 and the sentence defining alpha_i.
The prime number theorem in progressions turns the mod 3 density inequalities
and the mod W lower bound into a positive finite profile. No sumset conclusion
or transference theorem occurs here. -/
theorem local_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Set ℕ) (hA : A ⊆ P)
    (h1 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 1 3 + lowerDensityRes A 2 3)
    (h2 : 3 / 2 + δ ≤ 2 * lowerDensityRes A 2 3 + lowerDensityRes A 1 3)
    (hlocal : ∀ b, b < primorial z → Nat.Coprime b (primorial z) →
      δ ≤ lowerDensityRes A b (primorial z)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := Profiles408.halfProfile A z n δ m
      (∀ b, 0 ≤ f b ∧ f b ≤ 1) ∧ (∀ b ∈ unitsMod m, 0 < f b) ∧
      3 / 2 < 2 * alphaRes m f 1 + alphaRes m f 2 ∧
      3 / 2 < 2 * alphaRes m f 2 + alphaRes m f 1 := by
  sorry

/-- LEAF. Li and Pan math/0701240v3 pages 8 to 12, Sections 3 and 4,
and Shao pages 16 to 17 after equation 30. The three set version of the
explicit profile lifting. All three mass margins and Fourier bounds enter
AlsetriProp41 separately. There is no lower density assumption. -/
theorem weighted_lifting_mixed (H : AlsetriProp41) (R : U1488.Green66p (5 / 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z₀ : ℕ, 3 ≤ z₀ ∧ ∀ z : ℕ, z₀ ≤ z → ∀ A : Fin 3 → Set ℕ, (∀ i, A i ⊆ P) →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n → ∀ m : ℕ, ∀ [NeZero m],
        m = primorial z / 2 → ∀ b₁ ∈ unitsMod m, ∀ b₂ ∈ unitsMod m, ∀ b₃ ∈ unitsMod m,
        (n : ZMod m) = b₁ + b₂ + b₃ →
        0 < Profiles408.halfProfile (A 0) z n δ m b₁ →
        0 < Profiles408.halfProfile (A 1) z n δ m b₂ →
        0 < Profiles408.halfProfile (A 2) z n δ m b₃ →
        3 / 2 < Profiles408.halfProfile (A 0) z n δ m b₁ +
          Profiles408.halfProfile (A 1) z n δ m b₂ + Profiles408.halfProfile (A 2) z n δ m b₃ →
        IsSum3 (A 0) (A 1) (A 2) n := by
  sorry

/-- LEAF. Shao pages 16 to 17, after equation 30 through Lemmas 4.5 and 4.6.
Given the transference principle and the restriction estimate, an admissible
triple of explicit truncated residue weights lifts to an integer representation.
This has no lower density assumption. It is shared with Theorem 1.1. -/
theorem weighted_lifting (H : AlsetriProp41) (R : U1488.Green66p (5 / 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z₀ : ℕ, 3 ≤ z₀ ∧ ∀ z : ℕ, z₀ ≤ z → ∀ A : Set ℕ, A ⊆ P →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n → ∀ m : ℕ, ∀ [NeZero m],
        m = primorial z / 2 → ∀ b₁ ∈ unitsMod m, ∀ b₂ ∈ unitsMod m, ∀ b₃ ∈ unitsMod m,
        (n : ZMod m) = b₁ + b₂ + b₃ →
        0 < Profiles408.halfProfile A z n δ m b₁ →
        0 < Profiles408.halfProfile A z n δ m b₂ →
        0 < Profiles408.halfProfile A z n δ m b₃ →
        3 / 2 < Profiles408.halfProfile A z n δ m b₁ +
          Profiles408.halfProfile A z n δ m b₂ + Profiles408.halfProfile A z n δ m b₃ →
        IsSum3 A A A n := by
  obtain ⟨z₀, hz₀, hLift⟩ := weighted_lifting_mixed H R δ hδ
  refine ⟨z₀, hz₀, ?_⟩
  intro z hz A hA
  exact hLift z hz (fun _ => A) (fun _ => hA)


/-- Exact original Shao Theorem 1.3 statement. The threshold on n is retained.
CONDITIONAL ON the cited supply leaves, including the transference decomposition. -/
theorem shao_1_3_decomposed : Shao13 := by
  intro δ hδ
  let d : ℝ := min δ (1 / 8)
  have hd : 0 < d := lt_min hδ (by norm_num)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdsmall : d ≤ 1 / 8 := min_le_right _ _
  obtain ⟨z, hz, hLift⟩ := weighted_lifting Decomp408a.alsetri_prop_4_1_decomposed
    restriction_five_halves d hd
  refine ⟨primorial z, primorial_pos z, ?_⟩
  intro A hA h1 h2 hlocal
  obtain ⟨Np, hProfile⟩ := local_profile d hd hdsmall z hz A hA (by linarith) (by linarith)
    (fun b hb hc => hdδ.trans (hlocal b hb hc))
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd
  obtain ⟨hbound, hpositive, hα1, hα2⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, hsum⟩ :=
    shao_prop16 m hmodd hmsq hm3 (Profiles408.halfProfile A z n d m) hα1 hα2 (n : ZMod m)
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃ he
    (hpositive b₁ hb₁) (hpositive b₂ hb₂) (hpositive b₃ hb₃) hsum

end LeanLab.DensityGoldbach.Decomp408b

#print axioms LeanLab.DensityGoldbach.Decomp408b.shao_1_3_decomposed
