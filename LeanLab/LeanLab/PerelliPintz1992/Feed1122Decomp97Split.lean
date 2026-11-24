/-
P0070, A. Perelli and J. Pintz, Compositio Math. 82, 1992, estimate 7 on p. 359 and display 27
on p. 364. Feed unit of burst-20261122-S105 for `Decomp97.reduction27`.

`reduction27` asks for the bound of 27 under the hypothesis `energy ≤ E` on the clipped W energy.
Its conclusion carries the additive remainder `C N L ^ (-(A + 1))`, so it already follows from
estimate 7 alone, the hypothesis on E being unused. Estimate 7 is assembled in
`Decomp1624.estimate7_recut`, in Decomp544.lean, from the proved averaged reduction `Decomp1624.reduction27A` and the
open Section 6 leaf `Decomp1624.energy_decayA`. Hence `reduction27` is no harder than
`energy_decayA`: the theorem below has the identical statement and is
CONDITIONAL ON `Decomp1624.energy_decayA` only, with no placeholder of its own and no new leaf.
`Decomp97.energy_decay`, the clipped decay leaf, is not touched; see the QUESTION there.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Decomp544

namespace LeanLab.PerelliPintz1992.Feed1122Decomp97Split
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97

noncomputable section

/-- Estimate 7 on p. 359, the printed Prop `Estimate7`, gives display 27 on p. 364 in the form of
`Decomp97.reduction27`, for every nonnegative E, with c = 1. PROVED, plain real arithmetic. -/
theorem reduction27_of_estimate7 (h7 : Estimate7) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energy N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  obtain ⟨ε₁, hε₁, h⟩ := h7
  refine ⟨ε₁, hε₁, fun ε hε hεs A hA => ?_⟩
  obtain ⟨C, N₀, hb⟩ := h ε hε hεs A hA
  refine ⟨max C 1, 1, max N₀ 2, lt_of_lt_of_le one_pos (le_max_right _ _), one_pos, ?_⟩
  intro N hN ξ hξ hξ' E hE _
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key := hb N hN₀ ξ hξ hξ'
  have hHdef : H N ε = (N : ℝ) ^ (1 / 2 + ε) := rfl
  rw [hHdef]
  refine key.trans ?_
  have hpow : 0 ≤ L N ^ (-(A + 1)) := Real.rpow_nonneg hL.le _
  have hdiv : C * N / L N ^ (A + 1) = C * (N * L N ^ (-(A + 1))) := by
    rw [Real.rpow_neg hL.le]; ring
  rw [hdiv]
  have hx : 0 ≤ (N : ℝ) * L N ^ (-(A + 1)) := mul_nonneg hNn hpow
  have hLE : 0 ≤ L N ^ (1 : ℝ) * E := mul_nonneg (Real.rpow_nonneg hL.le _) hE
  calc
    C * (N * L N ^ (-(A + 1))) ≤ max C 1 * (N * L N ^ (-(A + 1))) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hx
    _ ≤ max C 1 * N * (L N ^ (1 : ℝ) * E + L N ^ (-(A + 1))) := by
      have hm : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
      nlinarith [mul_nonneg (mul_nonneg hm hNn) hLE]

/-- `Decomp97.reduction27`, identical statement. CONDITIONAL ON `Decomp1624.energy_decayA`
through `Decomp1624.estimate7_recut` in Decomp544.lean. No sorry in this proof. -/
theorem reduction27_of_energy_decayA :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energy N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) :=
  reduction27_of_estimate7 Decomp1624.estimate7_recut

#print axioms reduction27_of_estimate7
#print axioms reduction27_of_energy_decayA

end
end LeanLab.PerelliPintz1992.Feed1122Decomp97Split
