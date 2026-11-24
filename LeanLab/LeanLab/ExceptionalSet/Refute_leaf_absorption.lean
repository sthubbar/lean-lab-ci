/-
Refutation of the leaf `leaf_absorption` of `LeanLab.ExceptionalSet.SPLIT_lemma4`, step 4 of the
split of Lemma 4 of P0082, the bookkeeping of the geometric decay.

The leaf asks, for every `1 < γ < 3/2` and every `κ₁, B₁ > 0`, for `κ > 0` and `B ≥ 1` with
`4N/(⌈log N⌉ + 1) + (a nonnegative term) ≤ B N exp(-κ (log N)^(3-2γ))` for all `N ≥ 3`.
The first term alone is at least `4N/(log N + 2)`, and `exp(κ L^p)/L → ∞` for `p = 3 - 2γ > 0`,
so no `κ, B` can work. The root cause is the choice `H = ⌈log N⌉` in the Erdős–Turán step of
`lemma4_split`; Vinogradov's argument needs `H` of size `exp(κ' (log N)^(3-2γ))`.

Counterexample family: `γ = 5/4`, `κ₁ = B₁ = 1`. Given `κ, B`, put `s = 9B/(2κ³) + 1`,
`L₀ = max 2 s²` and `N = ⌈exp L₀⌉`. The leaf would give `4 exp(κ √L) ≤ B (L + 2)` with
`L = log N ≥ s²`, against `exp y ≥ y³/6`.

The statement below is the leaf's statement verbatim, under `¬`; it is self-contained, so this file
imports Mathlib only. This file states no new definition. AI wrote this code, found by session S91
worker w5 in burst-20261122. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.U1539.Refute1122

open Real

/-- The leaf `leaf_absorption` of `SPLIT_lemma4` is false: its negation, kernel checked. -/
theorem refute_leaf_absorption : ¬ (∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ₁ B₁ : ℝ, 0 < κ₁ → 0 < B₁ →
      ∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))) := by
  intro hall
  obtain ⟨κ, B, hκ, hB, hN⟩ := hall (5 / 4) (by norm_num) (by norm_num) 1 1 one_pos one_pos
  set s : ℝ := 9 * B / (2 * κ ^ 3) + 1 with hs
  have hs0 : 0 < s := by positivity
  set L0 : ℝ := max 2 (s ^ 2) with hL0
  set N : ℕ := Nat.ceil (Real.exp L0) with hNdef
  have hexpL0 : Real.exp L0 ≤ (N : ℝ) := Nat.le_ceil _
  have hL02 : (2 : ℝ) ≤ L0 := le_max_left _ _
  have h7 : (7 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h1' : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
    nlinarith [Real.exp_one_gt_d9]
  have hN3 : 3 ≤ N := by
    have : (3 : ℝ) ≤ (N : ℝ) := by
      have := Real.exp_le_exp.mpr hL02
      linarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set L := Real.log (N : ℝ) with hLdef
  have hLL0 : L0 ≤ L := (Real.le_log_iff_exp_le hNpos).mpr hexpL0
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hsqrt : s ≤ Real.sqrt L := by
    rw [show s = Real.sqrt (s ^ 2) from (Real.sqrt_sq hs0.le).symm]
    exact Real.sqrt_le_sqrt (le_trans (le_max_right _ _) hLL0)
  have hp : L ^ (3 - 2 * (5 / 4 : ℝ)) = Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have h := hN N hN3
  rw [hp] at h
  -- the second summand is nonnegative
  have hsum0 : 0 ≤ 4 * (N : ℝ) * (1 * N * Real.exp (-1 * Real.sqrt L)
      * ∑ h ∈ Finset.Icc 1 (Nat.ceil L), 1 / ((h : ℝ) + 1)) := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => by positivity
  have hceil : (Nat.ceil L : ℝ) + 1 ≤ L + 2 := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ L); linarith
  have hfirst : 4 * (N : ℝ) / (L + 2) ≤ 4 * (N : ℝ) / ((Nat.ceil L : ℝ) + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hceil
  have hmain : 4 * (N : ℝ) / (L + 2) ≤ B * N * Real.exp (-κ * Real.sqrt L) := by linarith
  -- so 4 exp(κ √L) ≤ B (L + 2)
  have hE : 0 < Real.exp (κ * Real.sqrt L) := Real.exp_pos _
  have hkey : 4 ≤ B * (L + 2) * Real.exp (-κ * Real.sqrt L) := by
    have h2 : 4 * (N : ℝ) / (L + 2) * (L + 2) ≤ B * N * Real.exp (-κ * Real.sqrt L) * (L + 2) :=
      mul_le_mul_of_nonneg_right hmain (by linarith)
    rw [div_mul_cancel₀ _ (by linarith)] at h2
    have h3 : 4 * (N : ℝ) ≤ (B * (L + 2) * Real.exp (-κ * Real.sqrt L)) * N := by linarith
    exact le_of_mul_le_mul_right h3 hNpos
  have hkey2 : 4 * Real.exp (κ * Real.sqrt L) ≤ B * (L + 2) := by
    have := mul_le_mul_of_nonneg_right hkey hE.le
    rw [mul_assoc, ← Real.exp_add, show -κ * Real.sqrt L + κ * Real.sqrt L = 0 by ring,
      Real.exp_zero, mul_one] at this
    linarith
  -- but exp(κ √L) ≥ (κ √L)^3 / 6
  have hcube := Real.pow_div_factorial_le_exp (κ * Real.sqrt L) (by positivity) 3
  have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at hcube
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt (by linarith)
  have hcubeL : (κ * Real.sqrt L) ^ 3 = κ ^ 3 * L * Real.sqrt L := by
    rw [mul_pow, show Real.sqrt L ^ 3 = Real.sqrt L ^ 2 * Real.sqrt L by ring, hsq]; ring
  rw [hcubeL] at hcube
  have hκ3 : 0 < κ ^ 3 := by positivity
  have hsB : κ ^ 3 * s = 9 * B / 2 + κ ^ 3 := by
    rw [hs]; field_simp
  have hbig : κ ^ 3 * L * s ≤ κ ^ 3 * L * Real.sqrt L :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have : κ ^ 3 * L * s = L * (9 * B / 2 + κ ^ 3) := by rw [← hsB]; ring
  nlinarith

end LeanLab.ExceptionalSet.U1539.Refute1122

#print axioms LeanLab.ExceptionalSet.U1539.Refute1122.refute_leaf_absorption
