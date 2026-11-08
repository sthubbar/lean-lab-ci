/-
Split of `leaf_log_regime` in ExceptionalSet/SPLIT_lemma4.lean into smaller leaves.

The statement being split, verbatim after its name:

: ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧ (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C

`leaf_log_regime_split` below proves it from the leaves, with no `sorry` of its own and
without using the target theorem.  The leaves are the four steps of the regime, in the
order the assembly uses them:

1. `leaf_log_ge_one` - past `N = 3` the real logarithm of `N` is at least `1`, because
   `3 > e`; this is the hypothesis every later step is stated under.
2. `leaf_ceil_ge_one` - the ceiling of a real number that is at least `1` is at least `1`.
3. `leaf_ceil_le_two_log` - the ceiling of a logarithm that is at least `1` is at most twice
   that logarithm, `⌈t⌉ < t + 1 ≤ 2t`.
4. `leaf_two_log_le_rpow` - for `1 < γ` and every `C > 0`, past a threshold twice the
   logarithm is at most `C` times its `γ`-th power; this is the growth comparison
   `(log N)^{γ-1} → ∞` that makes `⌈log N⌉ ≤ F(N)^C` hold at every `C`.

The assembly needs in addition only `(exp u) ^ C = exp (C u)` and `u ≤ exp u`, both one-line
rewrites of library facts, so nothing but the four leaves is assumed.

AI wrote the Lean code.  The leaves are open; the assembly is proved.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma4

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step 1, the lower bound on the logarithm: for every `N ≥ 3` the real logarithm of
`N` is at least `1`, since `3 > e` and `log` is monotone. -/
theorem leaf_log_ge_one (N : ℕ) (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  sorry

/-- LEAF. Step 2, the ceiling of a number that is at least `1` is at least `1`. -/
theorem leaf_ceil_ge_one (x : ℝ) (hx : 1 ≤ x) : (1 : ℝ) ≤ (Nat.ceil x : ℝ) := by
  sorry

/-- LEAF. Step 3, the ceiling is at most twice the number once the number is at least `1`:
`⌈t⌉ < t + 1 ≤ 2t` for `t ≥ 1`. -/
theorem leaf_ceil_le_two_log (N : ℕ) (hN : 1 ≤ Real.log N) :
    (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := by
  sorry

/-- LEAF. Step 4, the growth comparison: for `1 < γ` and every `C > 0`, past a threshold,
twice the logarithm is at most `C` times its `γ`-th power.  Here `(log N)^{γ-1}` grows
without bound, so this is the whole content of the regime at large `N`. -/
theorem leaf_two_log_le_rpow (γ : ℝ) (hγ : 1 < γ) (C : ℝ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 * Real.log N ≤ C * Real.log N ^ γ := by
  sorry

/-! ### Assembly -/

/-- `leaf_log_regime`: past a threshold, `N ≥ 3`, `log N ≥ 1`, `⌈log N⌉ ≥ 1`, and
`⌈log N⌉ ≤ F(N)^C` for every `C > 0`.  Proved from the leaves above, with no `sorry` here
and without using the target theorem. -/
theorem leaf_log_regime_split :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧
        (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C := by
  intro γ hγ1 _hγ2 C hC
  obtain ⟨N₁, hN₁⟩ := leaf_two_log_le_rpow γ hγ1 C hC
  refine ⟨max N₁ 3, ?_⟩
  intro N hN
  have h3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hlog1 : 1 ≤ Real.log N := leaf_log_ge_one N h3
  have hceil1 : (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) := leaf_ceil_ge_one _ hlog1
  have hceil2 : (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := leaf_ceil_le_two_log N hlog1
  have hdiv : 2 * Real.log N ≤ C * Real.log N ^ γ :=
    hN₁ N (le_trans (le_max_left _ _) hN)
  have hF : F γ N ^ C = Real.exp (C * Real.log N ^ γ) := by
    unfold F
    rw [← Real.exp_mul, mul_comm]
  have hkey : (Nat.ceil (Real.log N) : ℝ) ≤ Real.exp (C * Real.log N ^ γ) := by
    calc (Nat.ceil (Real.log N) : ℝ) ≤ 2 * Real.log N := hceil2
      _ ≤ C * Real.log N ^ γ := hdiv
      _ ≤ C * Real.log N ^ γ + 1 := by linarith
      _ ≤ Real.exp (C * Real.log N ^ γ) := Real.add_one_le_exp _
  exact ⟨h3, hlog1, hceil1, by rw [hF]; exact hkey⟩

end LeanLab.ExceptionalSet.U1539
