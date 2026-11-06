/-
Li and Pan's density theorem through explicit profiles and their local corollary.
Sources: https://arxiv.org/abs/math/0701240v3 pages 7 to 12 and
https://arxiv.org/abs/1206.6139v2 page 1 Theorem 1.2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408c
import LeanLab.DensityGoldbach.LiPanCor21

open Finset

namespace LeanLab.DensityGoldbach.Decomp408e

/-- LEAF. Li and Pan pages 7 to 8, Section 3, choosing the W-tricked
residues from the positive global density margin. The logarithmic cutoff
and normalization here are Shao page 15's profile. The local inequality is
Corollary 2.1's hypothesis and does not assert an integer representation. -/
theorem mixed_global_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Fin 3 → Set ℕ) (hA : ∀ i, A i ⊆ P)
    (hdensity : 2 + δ ≤ lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := fun i => Profiles408.halfProfile (A i) z n δ m
      (∀ i b, 0 ≤ f i b ∧ f i b ≤ 1) ∧
      2 * (m.totient : ℝ) < ∑ b ∈ unitsMod m, (f 0 b + f 1 b + f 2 b) := by
  sorry

/-- Exact original LiPan stub. The local result is already proved in the lab.
CONDITIONAL ON the mixed profile and shared analytic supply leaves. -/
theorem liPan_decomposed : LiPan := by
  intro A₁ A₂ A₃ hA₁ hA₂ hA₃ hden
  let A : Fin 3 → Set ℕ := ![A₁, A₂, A₃]
  have hA : ∀ i, A i ⊆ P := by
    intro i
    fin_cases i
    · exact hA₁
    · exact hA₂
    · exact hA₃
  let δ : ℝ := min ((lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃ - 2) / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  have hδden : 2 + δ ≤ lowerDensity (A 0) + lowerDensity (A 1) + lowerDensity (A 2) := by
    have := min_le_left ((lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃ - 2) / 2) (1 / 8)
    change 2 + δ ≤ lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃
    linarith
  obtain ⟨z, hz, hLift⟩ := Decomp408b.weighted_lifting_mixed Decomp408a.alsetri_prop_4_1_decomposed
    Decomp408b.restriction_five_halves δ hδ
  obtain ⟨Np, hProfile⟩ := mixed_global_profile δ hδ hδsmall z hz A hA hδden
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd
  obtain ⟨hbound, hmass⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  let f := fun i => Profiles408.halfProfile (A i) z n δ m
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, hsum, hprod⟩ :=
    liPanCor21_odd m hmodd hmsq (f 0) (f 1) (f 2) (hbound 0) (hbound 1) (hbound 2)
      hmass (n : ZMod m)
  have hp : 0 < f 0 b₁ * f 1 b₂ * f 2 b₃ := lt_of_le_of_ne
    (mul_nonneg (mul_nonneg (hbound 0 b₁).1 (hbound 1 b₂).1) (hbound 2 b₃).1) (Ne.symm hprod)
  obtain ⟨h1, h2, h3⟩ := Decomp408c.positive_factors (f 0 b₁) (f 1 b₂) (f 2 b₃)
    (hbound 0 b₁).1 (hbound 1 b₂).1 (hbound 2 b₃).1 hp
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃
    he.symm h1 h2 h3 (by linarith)

end LeanLab.DensityGoldbach.Decomp408e

#print axioms LeanLab.DensityGoldbach.Decomp408e.liPan_decomposed
