/-
Split of `lemma4` in ExceptionalSet/State1539.lean for task FREE-nv-minimax2 task2078.

The target `lemma4 : Lemma4` in State1539.lean is class CITED.  The five steps of the
Vinogradov argument that proves it sit as LEAF statements in DecompF2078Leaves.lean;
`lemma4_F2078` below assembles the statement `Lemma4` from them, with no `sorry` of its
own and without using `lemma4`.  AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.DecompF2078Leaves

namespace LeanLab.ExceptionalSet.U1539

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Assembly -/

/-- `Lemma4` (P0082, p. 359): the count of `N/2 < n ≤ N` with
`z₂ ≤ {αF(n)} < z₁` is `(z₁ - z₂)N/2` up to `O(N exp(-κ (log N)^{3-2γ}))`,
uniformly for `F(N)^{-1/2} < |α| ≤ 1`.  Proved from the five leaves above,
with no `sorry` here and without using the target theorem `lemma4`. -/
theorem lemma4_F2078 : Lemma4 := by
  intro γ hγ1 hγ2
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hsum⟩ :=
    leaf_F2078_exp_sum_bound γ hγ1 hγ2 ((γ - 1) / 2) (by linarith) (by linarith)
  obtain ⟨N₀, hN₀⟩ := leaf_F2078_log_regime γ hγ1 hγ2 ((γ - 1) / 2) (by linarith)
  obtain ⟨κ, B, hκ, hB, habs⟩ := leaf_F2078_absorption γ hγ1 hγ2 κ₁ B₁ hκ₁ hB₁
  obtain ⟨B₂, -, hsmall⟩ := leaf_F2078_small_N γ hγ1 hγ2 κ hκ (max N₀ 1)
  refine ⟨κ, max B B₂, hκ, ?_⟩
  intro N hN α hlow hhigh z₁ z₂ hz₂ hz1 hz₁
  have hE : (0 : ℝ) ≤ Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
  rcases lt_or_ge N (max N₀ 1) with hlt | hge
  · have hs := hsmall N hN (le_of_lt hlt) α z₁ z₂ hz₂ hz1 hz₁
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hs
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · obtain ⟨h3, -, -, hceilF⟩ := hN₀ N (le_trans (le_max_left _ _) hge)
    have hfej := leaf_F2078_fejer_majorant γ α z₁ z₂ N (Nat.ceil (Real.log N)) hz₂ hz1 hz₁
    have hterm : ∀ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) := by
      intro h hh
      obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
      have hhF : (h : ℝ) ≤ F γ N ^ ((γ - 1) / 2) := by
        refine le_trans (by exact_mod_cast hh2) hceilF
      exact hsum N hN α hlow hhigh h hh1 hhF
    have hS : ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
        ≤ B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      have ht := hterm h hh
      have hpos : (0 : ℝ) ≤ ((h : ℝ) + 1)⁻¹ := by positivity
      calc ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
          = ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ * ((h : ℝ) + 1)⁻¹ := by
            ring
        _ ≤ (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))) * ((h : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right ht hpos
        _ = B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) * (1 / ((h : ℝ) + 1)) := by
            ring
    have hstep : 4 * N * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
        ≤ 4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have hmain : |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) :=
      le_trans hfej (le_trans (add_le_add_right hstep _) (habs N h3))
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hmain
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end LeanLab.ExceptionalSet.U1539
