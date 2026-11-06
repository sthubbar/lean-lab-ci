/-
Shao Theorem 1.1 from the explicit residue profile and the shared lifting step.
Source: https://arxiv.org/abs/1206.6139v2 pages 15 to 17.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408b
import LeanLab.DensityGoldbach.Prop14Full

open Finset

namespace LeanLab.DensityGoldbach.Decomp408c

/-- LEAF. Shao page 15, equation 28. PNT in progressions gives the cap 1
on every fixed reduced class. Global relative density above 5/8 gives a total
profile mass above 5/8 times phi of the modulus. There is no representation
conclusion and no transference input. -/
theorem global_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Set ℕ) (hA : A ⊆ P)
    (hdensity : 5 / 8 + δ ≤ lowerDensity A) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := Profiles408.halfProfile A z n δ m
      (∀ b, 0 ≤ f b ∧ f b ≤ 1) ∧
      5 / 8 * (m.totient : ℝ) < ∑ b ∈ unitsMod m, f b := by
  sorry

/-- Shao page 16, equation 30. Nonnegative values with positive product
are individually positive. -/
theorem positive_factors (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hprod : 0 < a * b * c) : 0 < a ∧ 0 < b ∧ 0 < c := by
  have hab : 0 < a * b := pos_of_mul_pos_left hprod hc
  exact ⟨pos_of_mul_pos_left hab hb, pos_of_mul_pos_right hab ha,
    pos_of_mul_pos_right hprod (mul_nonneg ha hb)⟩

/-- Exact original Shao Theorem 1.1 statement.
CONDITIONAL ON the global profile and shared analytic supply leaves. -/
theorem shao_1_1_decomposed : Shao11 := by
  intro A hA hden
  let δ : ℝ := min ((lowerDensity A - 5 / 8) / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  have hδden : 5 / 8 + δ ≤ lowerDensity A := by
    have := min_le_left ((lowerDensity A - 5 / 8) / 2) (1 / 8)
    linarith
  obtain ⟨z, hz, hLift⟩ := Decomp408b.weighted_lifting Decomp408a.alsetri_prop_4_1_decomposed
    Decomp408b.restriction_five_halves δ hδ
  obtain ⟨Np, hProfile⟩ := global_profile δ hδ hδsmall z hz A hA hδden
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd
  obtain ⟨hbound, hmass⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  let f := Profiles408.halfProfile A z n δ m
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, hp, hs⟩ :=
    prop_1_4_proved m hmodd hmsq f hbound hmass (n : ZMod m)
  obtain ⟨h1, h2, h3⟩ := positive_factors (f b₁) (f b₂) (f b₃)
    (hbound b₁).1 (hbound b₂).1 (hbound b₃).1 hp
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃ he h1 h2 h3 hs

end LeanLab.DensityGoldbach.Decomp408c

#print axioms LeanLab.DensityGoldbach.Decomp408c.positive_factors
#print axioms LeanLab.DensityGoldbach.Decomp408c.shao_1_1_decomposed
