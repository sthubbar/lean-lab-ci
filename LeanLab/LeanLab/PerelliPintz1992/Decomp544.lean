/-
P0070, pages 356 and 358 to 364, the averaged WA reduction and dependent estimate assemblies.
The relocated declarations retain their original names and exact statement text.
They moved from Decomp1624 and Burst4Split to avoid import cycles with the proved replacements.
Import this module to use the canonical reduction and estimate assemblies.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Burst9Top

namespace LeanLab.PerelliPintz1992.Decomp1624
open Real ArithmeticFunction MeasureTheory Set Filter Topology Decomp97
noncomputable section

/-- Pages 363 and 364, displays 22 to 27, with WA in place of W.
The proof uses the existing Burst9 end block averaging construction.
Its Parseval cost is proportional to the removed cardinality times L squared.
Choosing the end block exponent A plus four absorbs this loss in the stated remainder.
Gallagher's lemma, P. X. Gallagher, Invent. Math. 11, 1970, pp. 329 to 339,
is applied at window q Q / 2 and radius `1 / (q Q)`. The exponent c depends on A. -/
theorem reduction27A :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  obtain ⟨ε₁, hε₁, hred⟩ := Burst9.reduction27A_wide_p3
  refine ⟨ε₁, hε₁, ?_⟩
  intro ε hε hεsmall A hA
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεsmall A hA
  exact ⟨C, c, N₀, hC, hc,
    fun N hN ξ _ _ E hE henergy => hbound N hN ξ E hE henergy⟩

/-- The exact existing Estimate7 Prop from the re-cut leaves.
CONDITIONAL ON energy_decayA. The reduction27A input is proved above. -/
theorem estimate7_recut : Estimate7 := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27A
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall A hA
  have hεred : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεden : ε < 1 / 12 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεred A hA
  obtain ⟨K, N₁, hK, hdecay⟩ := energy_decayA ε hε hεden (A + 1 + c) (by linarith)
  refine ⟨C * (K + 1), max (max N₀ N₁) 2, ?_⟩
  intro N hN ξ hξ hξ'
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have he := hbound N hN₀ ξ hξ hξ' (K * L N ^ (-(A + 1 + c)))
    (by positivity) (hdecay N hN₁ ξ hξ hξ')
  have hprod : L N ^ c * (K * L N ^ (-(A + 1 + c))) = K * L N ^ (-(A + 1)) := by
    calc
      _ = K * (L N ^ c * L N ^ (-(A + 1 + c))) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  change (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
    ‖S N α‖ ^ 2) ≤ _
  calc
    _ ≤ C * N * (L N ^ c * (K * L N ^ (-(A + 1 + c))) + L N ^ (-(A + 1))) := he
    _ = (C * (K + 1)) * N / L N ^ (A + 1) := by
      rw [hprod, Real.rpow_neg hL.le]
      ring

#print axioms reduction27A
#print axioms estimate7_recut

end
end LeanLab.PerelliPintz1992.Decomp1624

namespace LeanLab.PerelliPintz1992.Burst4Split
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
noncomputable section

/-- CONDITIONAL ON Burst8P2.shiu_d2. Section 4, pp. 359 to 362, displays 8 to 20: the major arcs estimate 6, p. 359,
`Σ_{k=V}^{V+H} |∫_𝔐 |S(α)|² e(-2kα) dα - 𝔖(2k)(N-2k)|² ≪ H N² L^{-A}` with `H = N^{1/2+ε}`,
for block starts `V < N/2`, as the paper's sentence "clearly sufficient to prove the case
`H = N^{1/2+ε}`", p. 358, uses it; see QUESTION Q-P0070-7 part iii. The proof in the paper:
display 8 splits 𝔐 into arcs, display 9 the integral of `|T|²`, displays 13 to 17 the bound on
`R` by Siegel and Walfisz, displays 19 and 20 the singular series with Shiu's Theorem 2.
`Decomp1519.estimate6_explicit` already proves the explicit form; the Siegel and Walfisz input is proved in Burst8P2. The Shiu input remains open. -/
theorem major_arcs_estimate6 : Estimate6Wide := by
  exact Burst8P2.estimate6Wide_of_split

/-- Section 5, pp. 363 and 364, displays 22 to 27: the Farey dissection of 𝔪 and
Gallagher's lemma, P. X. Gallagher, Invent. Math. 11, 1970, pp. 329 to 339, reduce the window
integral in 7 to the character expression of 27, here in the averaged form `energyA` of
`Decomp1624`. This is `Decomp1624.reduction27A` read for every real centre ξ, which 7 needs
since 𝔪 ⊆ (1/Q, 1 + 1/Q] reaches past 1, QUESTION Q-P0070-7 part ii; the paper's argument is
pointwise in ξ, and the Farey arc of 1/1 has radius 1/Q, so the same proof reads for ξ ∈ ℝ. -/
theorem reduction27A_wide :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  exact Burst9.reduction27A_wide_p3

/-- 7 for every real centre, `Estimate7Wide`, from the proved Section 5 reduction and the open Section 6 input.
CONDITIONAL ON `Decomp1624.energy_decayA`. The wide reduction is proved above. -/
theorem estimate7Wide_of_split : Estimate7Wide := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27A_wide
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall A hA
  have hεred : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεden : ε < 1 / 12 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεred A hA
  obtain ⟨K, N₁, hK, hdecay⟩ := energy_decayA ε hε hεden (A + 1 + c) (by linarith)
  refine ⟨C * (K + 1), max (max N₀ N₁) 2, ?_⟩
  intro N hN ξ
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have hξ0 : 0 ≤ clamp01 ξ := le_max_left _ _
  have hξ1 : clamp01 ξ ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hE : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N →
      energyA N ε ξ M ≤ K * L N ^ (-(A + 1 + c)) := fun M hM1 hM2 =>
    (energyA_le_clamp (by omega) ε ξ M).trans (hdecay N hN₁ (clamp01 ξ) hξ0 hξ1 M hM1 hM2)
  have he := hbound N hN₀ ξ (K * L N ^ (-(A + 1 + c))) (by positivity) hE
  have hprod : L N ^ c * (K * L N ^ (-(A + 1 + c))) = K * L N ^ (-(A + 1)) := by
    calc
      _ = K * (L N ^ c * L N ^ (-(A + 1 + c))) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  change (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
    ‖S N α‖ ^ 2) ≤ _
  calc
    _ ≤ C * N * (L N ^ c * (K * L N ^ (-(A + 1 + c))) + L N ^ (-(A + 1))) := he
    _ = (C * (K + 1)) * N / L N ^ (A + 1) := by
      rw [hprod, Real.rpow_neg hL.le]
      ring

/-! ### The assembly -/

/-- **Perelli and Pintz 1992, the Theorem, p. 356**, same type as `perelliPintz`, from the split:
Section 2 by `mainTheorem_of_wide`, Section 4 by `major_arcs_estimate6`, Sections 5 and 6 by
`estimate7Wide_of_split`. CONDITIONAL ON Burst8P2.shiu_d2 and Decomp1624.energy_decayA. -/
theorem perelliPintz_of_split : MainTheorem :=
  mainTheorem_of_wide major_arcs_estimate6 estimate7Wide_of_split

#print axioms major_arcs_estimate6
#print axioms reduction27A_wide
#print axioms estimate7Wide_of_split
#print axioms perelliPintz_of_split
end
end LeanLab.PerelliPintz1992.Burst4Split
