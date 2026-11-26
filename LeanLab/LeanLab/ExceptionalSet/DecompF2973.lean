/- Split of `lemma4` in ExceptionalSet/State1539.lean for task FREE-nv-glm3 task2973.

The target `lemma4 : Lemma4` in State1539.lean is class CITED.  The Vinogradov
equidistribution steps that prove it sit as LEAF statements below;
`lemma4_F2973` below assembles the statement `Lemma4` from them, with no `sorry`
of its own and without using the target theorem `lemma4`.  AI wrote the Lean code.
Binary Goldbach is open.
-/

import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Assembly -/

/-- `Lemma4` (P0082, p. 359): the count of `N/2 < n ≤ N` with
`z₂ ≤ {αF(n)} < z₁` is `(z₁ - z₂)N/2` up to `O(N exp(-κ (log N)^{3-2γ}))`,
uniformly for `F(N)^{-1/2} < |α| ≤ 1`.  Proved from the leaves below,
with no `sorry` here and without using the target theorem `lemma4`. -/
theorem lemma4_F2973 : Lemma4 := by
  intro γ hγ1 hγ2
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hsum⟩ :=
    leaf_F2973_exp_sum_bound γ hγ1 hγ2 ((γ - 1) / 2) (by linarith) (by linarith)
  obtain ⟨N₀, hN₀⟩ :=
    leaf_F2973_log_regime γ hγ1 hγ2 ((γ - 1) / 2) (by linarith)
  obtain ⟨κ, B, hκ, hB, habs⟩ :=
    leaf_F2973_absorption γ hγ1 hγ2 κ₁ B₁ hκ₁ hB₁
  obtain ⟨B₂, _, hsmall⟩ :=
    leaf_F2973_small_N γ hγ1 hγ2 κ hκ (max N₀ 1)
  refine ⟨κ, max B B₂, hκ, ?_⟩
  intro N hN α hlow hhigh z₁ z₂ hz₂ hz1 hz₁
  have hE : (0 : ℝ) ≤ Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
  rcases lt_or_ge N (max N₀ 1) with hlt | hge
  · -- small N: the trivial bound is absorbed by a large constant
    have hs := hsmall N hN (le_of_lt hlt) α z₁ z₂ hz₂ hz1 hz₁
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hs
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · -- large N: Fejer majorant plus exponential sums, absorbed past the log regime
    obtain ⟨h3, _, _, hceilF⟩ := hN₀ N (le_trans (le_max_left _ _) hge)
    have hfej := leaf_F2973_fejer_majorant γ α z₁ z₂ N (Nat.ceil (Real.log N)) hz₂ hz1 hz₁
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

/-! ### Leaves -/

/-- LEAF: Step 1, the exponential-sum input at frequencies `hα`: each sum
`Σ_{N/2 < n ≤ N} e(hαF(n))` is bounded by `B N exp(-κ (log N)^{3-2γ})` uniformly
in `h ≤ F(N)^C`, for `F(N)^{-1/2} < |α| ≤ 1`.  This is the Theorem 2 bound
specialised at `c = 1/2`, applied at frequency `hα` on `N/2 < n ≤ N`. -/
theorem leaf_F2973_exp_sum_bound :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 →
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
        (h : ℝ) ≤ F γ N ^ C →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF: Step 2, the logarithmic regime: past a threshold depending on `γ` and `C`,
`N ≥ 3`, `log N ≥ 1`, `⌈log N⌉ ≥ 1`, and `⌈log N⌉ ≤ F(N)^C` for every `C > 0`.
This lets the exponential-sum bound be applied at every integer frequency
`h ≤ ⌈log N⌉`. -/
theorem leaf_F2973_log_regime :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧
        (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C := by
  sorry

/-- LEAF: Step 3, the bookkeeping of the geometric decay: with `H = ⌈log N⌉`, the
term `4N/(H+1)` and the sum of the exponential-sum bounds weighted by `1/(h+1)`
are both dominated by `B N exp(-κ (log N)^{3-2γ})` for a strictly smaller `κ` and
a large enough `B`, once `N ≥ 3`. -/
theorem leaf_F2973_absorption :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ₁ B₁ : ℝ, 0 < κ₁ → 0 < B₁ →
      ∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF: Step 4, the finitely many small `N`: below any fixed bound the trivial
bound `|count - (z₁ - z₂)N/2| ≤ N` is absorbed by a large constant times
`N exp(-κ (log N)^{3-2γ})`, since on that finite range the `exp` factor is
bounded below. -/
theorem leaf_F2973_small_N :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ : ℝ, 0 < κ → ∀ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ N₀ → ∀ α z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
        |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF: Step 5, the Fejer-kernel discrepancy bound: the count of points whose
fractional parts lie in `[z₂, z₁)` differs from `(z₁ - z₂)N/2` by at most
`4N/(H+1) + 4N * Σ_{h≤H} ‖Σ e(hαF(n))‖/(h+1)`, for `H = ⌈log N⌉`. -/
theorem leaf_F2973_fejer_majorant (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * N / 2| ≤
    4 * N / ((H : ℝ) + 1) +
      4 * N * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  sorry
