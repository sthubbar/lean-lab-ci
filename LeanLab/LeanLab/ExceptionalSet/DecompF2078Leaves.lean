/-
Leaves of the split of `lemma4` in ExceptionalSet/State1539.lean, task FREE-nv-minimax2 task2078.

The target is `lemma4 : Lemma4` in State1539.lean, class CITED.
Lemma 4 of P0082 (p. 359) is proved from Theorem 2 with `c = 1/2` by Vinogradov's
equidistribution argument: a Fejer-kernel majorant controls the discrepancy of the
fractional-part count by exponential sums, which Theorem 2 bounds.

This file holds the five steps of that argument, in the order the assembly in
DecompF2078.lean uses them.  Every step below is one LEAF.  AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.Decomp547a

namespace LeanLab.ExceptionalSet.U1539

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: Step 1 of Vinogradov's argument, the Fejer-kernel majorant: for every `H`,
the excess of the number of `N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` over `(z₁ - z₂)N/2`
is at most `4N/(H+1)` plus the first `H` exponential sums at frequencies `hα`, each
weighted by `4N/(h+1)`.  This is the standard discrepancy bound for the indicator of
an interval of fractional parts. -/
theorem leaf_F2078_fejer_majorant (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * N / 2| ≤
    4 * N / ((H : ℝ) + 1) +
      4 * N * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  sorry

/-- LEAF: Step 2, the exponential-sum input at frequencies `hα`: each sum
`Σ_{N/2 < n ≤ N} e(hαF(n))` is bounded by `B N exp(-κ (log N)^{3-2γ})` uniformly
in `h ≤ F(N)^C`, for `F(N)^{-1/2} < |α| ≤ 1`.  This follows from Theorem 2
(specialised at `c = 1/2`) applied at frequency `hα` on the index range
`N/2 < n ≤ N`. -/
theorem leaf_F2078_exp_sum_bound :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 →
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
        (h : ℝ) ≤ F γ N ^ C →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  intro γ hγ1 hγ2 C hC hCγ
  exact Decomp547a.integer_multiple_decay_full theorem2_via_karacuba γ hγ1 hγ2 C hC hCγ

/-! ### Helpers for the logarithmic regime -/

/-- For every `N ≥ 3` the real logarithm of `N` is at least `1`, since `3 > e` and
`log` is monotone. -/
theorem f2078_log_ge_one (N : ℕ) (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have hx : Real.exp 1 ≤ (N : ℝ) := by
    calc Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      _ ≤ N := by exact_mod_cast hN
  exact (Real.le_log_iff_exp_le (by positivity)).mpr hx

/-- The ceiling of a real number that is at least `1` is at least `1`. -/
theorem f2078_ceil_ge_one (x : ℝ) (hx : 1 ≤ x) : (1 : ℝ) ≤ (Nat.ceil x : ℝ) := by
  calc (1 : ℝ) ≤ x := hx
    _ ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x

/-- The ceiling of a logarithm that is at least `1` is at most twice that logarithm. -/
theorem f2078_ceil_le_two_log (N : ℕ) (hN : 1 ≤ Real.log N) :
    (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := by
  have h1 : (Nat.ceil (Real.log N) : ℝ) < Real.log N + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

/-- For `1 < γ` and every `C > 0`, past a threshold twice the logarithm is at most
`C` times its `γ`-th power: `(log N)^{γ-1} → ∞`. -/
theorem f2078_two_log_le_rpow (γ : ℝ) (hγ : 1 < γ) (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 * Real.log N ≤ C * Real.log N ^ γ := by
  have h1 : Filter.Tendsto (fun x : ℝ ↦ x ^ (γ - 1)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by linarith)
  have h2 : Filter.Tendsto (fun x : ℝ ↦ C * x ^ (γ - 1)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hC h1
  obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp h2 2
  have h3 : Filter.Tendsto (fun n : ℕ ↦ Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.tendsto_atTop_atTop.mp h3 (max M 1)
  refine ⟨N₀, fun N hN => ?_⟩
  have hlog_ge : max M 1 ≤ Real.log N := hN₀ N hN
  have hlog_M : M ≤ Real.log N := le_trans (le_max_left _ _) hlog_ge
  have hlog_pos : 0 < Real.log N := by
    calc 0 < 1 := zero_lt_one
      _ ≤ max M 1 := le_max_right _ _
      _ ≤ Real.log N := hlog_ge
  have h4 := hM (Real.log N) hlog_M
  have h5 : 2 * Real.log N ≤ (C * Real.log N ^ (γ - 1)) * Real.log N := by
    nlinarith
  have h6 : Real.log N ^ (γ - 1) * Real.log N = Real.log N ^ γ := by
    have h7 : Real.log N = Real.log N ^ (1 : ℝ) := (Real.rpow_one _).symm
    nth_rw 2 [h7]
    rw [← Real.rpow_add hlog_pos]
    ring_nf
  calc 2 * Real.log N ≤ (C * Real.log N ^ (γ - 1)) * Real.log N := h5
    _ = C * (Real.log N ^ (γ - 1) * Real.log N) := mul_assoc _ _ _
    _ = C * Real.log N ^ γ := by rw [h6]

/-- LEAF: Step 3, the logarithmic regime: past a threshold depending on `γ` and `C`,
`N ≥ 3`, `log N ≥ 1`, `⌈log N⌉ ≥ 1`, and `⌈log N⌉ ≤ F(N)^C` for every `C > 0`.
This lets step 2 be applied at every integer frequency `h ≤ ⌈log N⌉`. -/
theorem leaf_F2078_log_regime :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧
        (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C := by
  intro γ hγ1 _hγ2 C hC
  obtain ⟨N₁, hN₁⟩ := f2078_two_log_le_rpow γ hγ1 C hC
  refine ⟨max N₁ 3, fun N hN => ?_⟩
  have h3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hlog1 : 1 ≤ Real.log N := f2078_log_ge_one N h3
  have hceil1 : (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) := f2078_ceil_ge_one _ hlog1
  have hceil2 : (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := f2078_ceil_le_two_log N hlog1
  have hdiv : 2 * Real.log N ≤ C * Real.log N ^ γ := hN₁ N (le_trans (le_max_left _ _) hN)
  have hF : F γ N ^ C = Real.exp (C * Real.log N ^ γ) := by
    unfold F
    rw [← Real.exp_mul, mul_comm]
  have hkey : (Nat.ceil (Real.log N) : ℝ) ≤ Real.exp (C * Real.log N ^ γ) := by
    calc (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := hceil2
      _ ≤ C * Real.log N ^ γ := hdiv
      _ ≤ C * Real.log N ^ γ + 1 := by linarith
      _ ≤ Real.exp (C * Real.log N ^ γ) := Real.add_one_le_exp _
  exact ⟨h3, hlog1, hceil1, by rw [hF]; exact hkey⟩

/-- LEAF: Step 4, the bookkeeping of the geometric decay: with `H = ⌈log N⌉`, the
term `4N/(H+1)` and the sum of the exponential-sum bounds weighted by `1/(h+1)` are
both dominated by `B N exp(-κ (log N)^{3-2γ})` for a strictly smaller `κ` and a
large enough `B`, once `N ≥ 3`. -/
theorem leaf_F2078_absorption :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ₁ B₁ : ℝ, 0 < κ₁ → 0 < B₁ →
      ∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF: Step 5, the finitely many small `N`: below any fixed bound the trivial
bound `|count - (z₁ - z₂)N/2| ≤ N` is absorbed by a large constant times
`N exp(-κ (log N)^{3-2γ})`, since on that finite range the `exp` factor is bounded below. -/
theorem leaf_F2078_small_N :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ : ℝ, 0 < κ → ∀ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ N₀ → ∀ α z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
        |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

end LeanLab.ExceptionalSet.U1539
