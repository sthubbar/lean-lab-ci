/-
Alsetri Theorem 1.1 through the shared explicit residue profile.
Source: https://arxiv.org/abs/2505.09648v3 pages 13 to 14.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Decomp408b
import LeanLab.DensityGoldbach.AlsetriFull

open Finset

namespace LeanLab.DensityGoldbach.Decomp408d

/-- LEAF. Alsetri page 13, the profile definition and the display
sum f greater than phi of W divided by 4. The strict cutoff from Shao is
used here. Removing the possible endpoint changes the logarithmic sum by
at most log n, and the fixed density margin absorbs that error.
Only the explicit finite profile and its support are asserted. -/
theorem class_one_profile (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (z : ℕ) (hz : 3 ≤ z) (A : Set ℕ) (hA : A ⊆ P)
    (hsupport : ∀ a ∈ A, a % 3 = 1)
    (hdensity : 1 / 2 + δ ≤ lowerDensityRes A 1 3) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ m : ℕ, ∀ [NeZero m], m = primorial z / 2 →
      let f := Profiles408.halfProfile A z n δ m
      (∀ b, 0 ≤ f b ∧ f b ≤ 1) ∧ (∀ b, b.val % 3 ≠ 1 → f b = 0) ∧
      (m.totient : ℝ) / 4 < ∑ b ∈ unitsMod m, f b := by
  sorry

/-- Exact original Alsetri Theorem 1.1 statement.
CONDITIONAL ON the class profile and shared analytic supply leaves. -/
theorem alsetri_1_1_decomposed : Alsetri11 := by
  intro A hA hsupport hden
  let δ : ℝ := min ((lowerDensityRes A 1 3 - 1 / 2) / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 8 := min_le_right _ _
  have hδden : 1 / 2 + δ ≤ lowerDensityRes A 1 3 := by
    have := min_le_left ((lowerDensityRes A 1 3 - 1 / 2) / 2) (1 / 8)
    linarith
  obtain ⟨z, hz, hLift⟩ := Decomp408b.weighted_lifting Decomp408a.alsetri_prop_4_1_decomposed
    Decomp408b.restriction_five_halves δ hδ
  obtain ⟨Np, hProfile⟩ := class_one_profile δ hδ hδsmall z hz A hA hsupport hδden
  obtain ⟨Nl, hNl⟩ := hLift z le_rfl A hA
  obtain ⟨hmpos, hmodd, hmsq, hm3⟩ := half_primorial_props hz
  let m := primorial z / 2
  have : NeZero m := ⟨hmpos.ne'⟩
  refine ⟨max Np Nl, ?_⟩
  intro n hn hnodd hn3
  obtain ⟨hbound, hsup, hmass⟩ := hProfile n (le_trans (le_max_left _ _) hn) m rfl
  let f := Profiles408.halfProfile A z n δ m
  have hx : (n : ZMod m).val % 3 = 0 := by
    rw [ZMod.val_natCast]
    have := (Nat.dvd_mod_iff hm3).mpr (Nat.dvd_of_mod_eq_zero hn3)
    exact Nat.mod_eq_zero_of_dvd this
  obtain ⟨b₁, hb₁, b₂, hb₂, b₃, hb₃, he, h1, h2, h3, hs⟩ :=
    alsetri12_proved m hmodd hmsq hm3 f hbound hsup hmass (n : ZMod m) hx
  exact hNl n (le_trans (le_max_right _ _) hn) hnodd m rfl b₁ hb₁ b₂ hb₂ b₃ hb₃ he h1 h2 h3 hs

end LeanLab.DensityGoldbach.Decomp408d

#print axioms LeanLab.DensityGoldbach.Decomp408d.alsetri_1_1_decomposed
