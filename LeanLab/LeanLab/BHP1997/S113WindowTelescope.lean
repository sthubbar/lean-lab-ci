/-
Burst 2026-11-22, BHP1997, session S113, step window-s113. P0069 Baker Harman Pintz 1997, page
51, display 5.17, "a straightforward consequence of the prime number theorem, with error term
`Y exp(-ε L^(1/2))`". This file proves the window form of `LowerShortC165.buchstab_telescope`,
the integral equation of the Buchstab function in summed form, with the error
`b exp(-N (log X)^(1/3))` of 5.17 in place of a log power. The proof is the one of the log
power form: each term is at most `(2 / c + 6) / z` and `1 / z ≤ X ^ (-c)` is below every
`exp(-N (log X)^(1/3))`, `rpow_neg_le_exp_stretched`.

Nothing is left open in this file. No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.RoughDensity517b

namespace LeanLab.BHP1997.S113WindowTelescope
open Classical
open scoped BigOperators
open LeanLab.ChenDoubleSieve.Wu04Functional
open LeanLab.BHP1997.LowerShortC165 (buchstab_telescope_term)

/-- Page 51 display 5.17: a negative power of `X` is below every stretched exponential
`exp(-N (log X)^(1/3))`, the form in which errors of size `b / z` with `z ≥ X ^ c` are
absorbed into the error of 5.17. From `N l ≤ c l ^ 3 + N + N ^ 2 / c`. -/
theorem rpow_neg_le_exp_stretched {c : ℝ} (hc : 0 < c) (N : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 3 ≤ X →
      X ^ (-c) ≤ K * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  refine ⟨Real.exp (|N| + N ^ 2 / c), Real.exp_pos _, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hlx : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  set l := Real.log X ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log X := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  rw [Real.rpow_def_of_pos hX0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : N * l ≤ c * l ^ 3 + |N| + N ^ 2 / c := by
    have hNa : N ≤ |N| := le_abs_self N
    have hN2 : 0 ≤ N ^ 2 / c := by positivity
    rcases le_or_gt l 1 with h1 | h1
    · have : N * l ≤ |N| * l := mul_le_mul_of_nonneg_right hNa hl0
      have : |N| * l ≤ |N| := by nlinarith [abs_nonneg N]
      nlinarith [pow_nonneg hl0 3]
    · rcases le_or_gt (|N|) (c * l ^ 2) with h2 | h2
      · have : |N| * l ≤ c * l ^ 2 * l := mul_le_mul_of_nonneg_right h2 hl0
        nlinarith [abs_nonneg N]
      · have hlN : l < |N| / c := by
          rw [lt_div_iff₀ hc]
          have hpos : 0 < c * l * (l - 1) := mul_pos (mul_pos hc (by linarith)) (by linarith)
          nlinarith
        have : |N| * l ≤ |N| * (|N| / c) := mul_le_mul_of_nonneg_left hlN.le (abs_nonneg N)
        have e : |N| * (|N| / c) = N ^ 2 / c := by rw [← sq_abs N]; ring
        nlinarith [pow_nonneg hl0 3, abs_nonneg N]
  rw [← hl3]
  nlinarith

/-- PROVED: page 51 display 5.17, the integral equation `u ω(u) = 1 + ∫_1^{u-1} ω` in summed
form with the error of 5.17, the window form of `LowerShortC165.buchstab_telescope`. Used in
`S113WindowRough.buchstab_main_term_window` in place of a LEAF. -/
theorem leaf_buchstab_telescope_window_s113 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log n else 0) +
            ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨K, hK, hKX⟩ := rpow_neg_le_exp_stretched hc N
  have hc6 : 0 < 2 * (1 / c) + 6 := by positivity
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) * K, by positivity,
    fun X hX z hzX a b ha hb => ?_⟩
  have hK2 : 0 < (2 * (1 / c) + 6) * K := by positivity
  have hX3 : 3 ≤ X := by linarith [le_max_right ((3 : ℝ) ^ (1 / c)) 3]
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by linarith [le_max_left ((3 : ℝ) ^ (1 / c)) 3]
  have hX0 : 0 < X := by linarith
  have h3z : (3 : ℝ) ≤ z := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz3 : 3 ≤ z := by exact_mod_cast h3z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
      (2 * (1 / c) + 6) / (z : ℝ) := by
    intro n hn
    obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases hzn : z ≤ n
    · rw [ite_eq_left hzn]
      refine buchstab_telescope_term hω hz hz3 hzn ?_
      exact (Real.log_le_log hn0 (le_trans (by exact_mod_cast hnb) hb)).trans hlogz
    · rw [ite_eq_right hzn, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero,
        sub_zero]
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log hn0 (by exact_mod_cast (by omega : n < z))
      rw [hz _ hu, zero_div, abs_zero]
      positivity
  have hzinv : 1 / (z : ℝ) ≤ K * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have h1 : 1 / (z : ℝ) ≤ X ^ (-c) := by
      rw [Real.rpow_neg hX0.le, one_div]
      exact inv_anti₀ (Real.rpow_pos_of_pos hX0 c) hzX
    exact h1.trans (hKX X hX3)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hLA : 0 ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  calc _ ≤ ∑ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ioc a b, (2 * (1 / c) + 6) / (z : ℝ) := Finset.sum_le_sum hterm
    _ = ((b - a : ℕ) : ℝ) * ((2 * (1 / c) + 6) * (1 / (z : ℝ))) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        ring
    _ ≤ (b : ℝ) * ((2 * (1 / c) + 6) * (K * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)))) := by
        have : ((b - a : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b a
        gcongr
    _ = (2 * (1 / c) + 6) * K * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) * K) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have : (0 : ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
        gcongr
        linarith

end LeanLab.BHP1997.S113WindowTelescope
