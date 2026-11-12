/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372.

ROUTE BURST session 4, 2026-11-12. The Theorem, p. 356, `perelliPintz` in Statements.lean,
split into the paper's own top-level structure:

* Section 2, displays 4 and 5, pp. 357 to 359: the reduction of the Theorem to 6 and 7.
  PROVED earlier, reused: `MainAssembly.mainTheorem_of_wide`.
* Section 4, displays 8 to 20, pp. 359 to 362: the major arcs estimate 6. LEAF, sorry,
  `major_arcs_estimate6` below.
* Section 5, displays 22 to 27, pp. 363 and 364: the Farey and Gallagher reduction of 7 to the
  character expression. LEAF, sorry, `reduction27A_wide` below, every real centre.
* Sections 5 and 6, pp. 365 to 372: every logarithmic saving for the character expression.
  LEAF, sorry, reused unchanged: `Decomp1624.energy_decayA`.
* Glue, PROVED here: the character expression at any real centre is bounded by its value at the
  centre clamped to [0, 1], `energyA_le_clamp`; hence `estimate7Wide_of_split`.

`perelliPintz_of_split` has the type `MainTheorem` of `perelliPintz` and no sorry of its own.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.MainAssembly
import LeanLab.PerelliPintz1992.Decomp1624

namespace LeanLab.PerelliPintz1992.Burst4Split
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ### The leaves -/

/-- LEAF, Section 4, pp. 359 to 362, displays 8 to 20: the major arcs estimate 6, p. 359,
`Σ_{k=V}^{V+H} |∫_𝔐 |S(α)|² e(-2kα) dα - 𝔖(2k)(N-2k)|² ≪ H N² L^{-A}` with `H = N^{1/2+ε}`,
for block starts `V < N/2`, as the paper's sentence "clearly sufficient to prove the case
`H = N^{1/2+ε}`", p. 358, uses it; see QUESTION Q-P0070-7 part iii. The proof in the paper:
display 8 splits 𝔐 into arcs, display 9 the integral of `|T|²`, displays 13 to 17 the bound on
`R` by Siegel and Walfisz, displays 19 and 20 the singular series with Shiu's Theorem 2.
`Decomp1519.estimate6_explicit` already proves the explicit form; the Siegel and Walfisz input
and the Shiu input with the asymptotic count remain. -/
theorem major_arcs_estimate6 : Estimate6Wide := by
  sorry

/-- LEAF, Section 5, pp. 363 and 364, displays 22 to 27: the Farey dissection of 𝔪 and
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
  sorry

/-! ### Glue, proved -/

/-- The centre ξ clamped to [0, 1]. -/
def clamp01 (ξ : ℝ) : ℝ := max 0 (min ξ 1)

attribute [-instance] Finset.decidableExistsAndFinsetCoe Finset.decidableExistsAndFinset in
/-- The Farey modulus family of p. 363 at a real centre is contained in the family at the
clamped centre. Every arc `a/q` has `1 ≤ a ≤ q`, so it lies in [0, 1]. PROVED. -/
theorem Y_subset_clamp {N : ℕ} (hN : 1 ≤ N) (ε ξ : ℝ) (M : ℕ) :
    Y N ε ξ M ⊆ Y N ε (clamp01 ξ) M := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH : 0 < 1 / H N ε := one_div_pos.mpr (Real.rpow_pos_of_pos hNp _)
  intro q hq
  obtain ⟨hb, hM, hM', a, ha, hc, α, hα, hx⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hb, hM, hM', a, ha, hc, ?_⟩
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have haq : (a : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp ha).2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.pos
  have haq0 : 0 < (a : ℝ) / q := div_pos (by linarith) hq0
  have haq1 : (a : ℝ) / q ≤ 1 := (div_le_one hq0).mpr haq
  rcases le_or_gt ξ 0 with h0 | h0
  · have hcl : clamp01 ξ = 0 := by
      unfold clamp01; rw [min_eq_left (by linarith)]; exact max_eq_left h0
    rw [hcl]
    rcases le_or_gt 0 α with hα0 | hα0
    · refine ⟨α, hα, ?_⟩
      rw [sub_zero, abs_of_nonneg hα0]
      have := (abs_lt.mp hx).2
      linarith
    · refine ⟨0, ?_, by simpa using hH⟩
      have h1 := (abs_le.mp hα).1
      rw [zero_sub, abs_neg, abs_of_pos haq0]
      linarith
  rcases le_or_gt ξ 1 with h1 | h1
  · have hcl : clamp01 ξ = ξ := by
      unfold clamp01; rw [min_eq_left h1]; exact max_eq_right h0.le
    rw [hcl]; exact ⟨α, hα, hx⟩
  · have hcl : clamp01 ξ = 1 := by
      unfold clamp01; rw [min_eq_right h1.le]; exact max_eq_right zero_le_one
    rw [hcl]
    rcases le_or_gt α 1 with hα1 | hα1
    · refine ⟨α, hα, ?_⟩
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have := (abs_lt.mp hx).1
      linarith
    · refine ⟨1, ?_, by simpa using hH⟩
      have h2 := (abs_le.mp hα).2
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- The character expression at a real centre is at most its value at the clamped centre.
PROVED. -/
theorem energyA_le_clamp {N : ℕ} (hN : 1 ≤ N) (ε ξ : ℝ) (M : ℕ) :
    energyA N ε ξ M ≤ energyA N ε (clamp01 ξ) M := by
  unfold energyA
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Y_subset_clamp hN ε ξ M)
    (fun q _ _ => sq_nonneg _)

/-- 7 for every real centre, `Estimate7Wide`, from the two Section 5 and 6 leaves.
CONDITIONAL ON `reduction27A_wide` and `Decomp1624.energy_decayA`. -/
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
`estimate7Wide_of_split`. CONDITIONAL ON the three analytic leaves. No sorry in this proof. -/
theorem perelliPintz_of_split : MainTheorem :=
  mainTheorem_of_wide major_arcs_estimate6 estimate7Wide_of_split

example : MainTheorem := perelliPintz
#check (perelliPintz_of_split : MainTheorem)

#print axioms Y_subset_clamp
#print axioms energyA_le_clamp
#print axioms perelliPintz_of_split

end
end LeanLab.PerelliPintz1992.Burst4Split
