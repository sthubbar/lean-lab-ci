/-
Refinement of the existing explicit S1 to S4 chain.
The numerical constants are lab derivations, not numerals quoted from Nathanson.
The framework is Nathanson Chapter 7, pages 177 to 209.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannExplicit.Sharper6

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach.Task63

open LeanLab.SchnirelmannExplicit LeanLab.SchnirelmannExplicit.Sharper
open LeanLab.SchnirelmannExplicit.Sharper3 LeanLab.SchnirelmannExplicit.Sharper4
open LeanLab.SchnirelmannExplicit.Sharper5 LeanLab.SchnirelmannExplicit.Sharper6
open LeanLab.SchnirelmannExplicit.DysonBasis

/-- A tangent bound normalized at the exact power 8192. -/
theorem log_le_u_8192 (u : ℝ) (hu : 0 < u) : Real.log u ≤ u / 8192 + 8.011 := by
  have h := Real.log_le_sub_one_of_pos (x := u / 8192) (by positivity)
  rw [Real.log_div hu.ne' (by norm_num)] at h
  have he : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_lt_d9]

/-- The source floor range has the smaller explicit logarithmic budget 12000. -/
theorem log_le_of_lt_12000 (n : ℕ) (hn : n < N₂) (h1 : 1 ≤ n) :
    Real.log n ≤ 12000 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h1
  have hnN : (n : ℝ) ≤ N₂ := by exact_mod_cast hn.le
  have h := Real.log_le_log hnpos hnN
  rw [log_N₂] at h
  have hdiv := Real.log_le_sub_one_of_pos (x := (3 : ℝ) / 2) (by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at hdiv
  have hlog3 : Real.log (3 : ℝ) ≤ 1.2 := by linarith [Real.log_two_lt_d9]
  nlinarith

set_option maxHeartbeats 1000000 in
open LeanLab.SchnirelmannGoldbach.S1 in
/-- **S1u, for huge `N`.** For `N ≥ N₂ = 3^10000` and `1 ≤ n ≤ N`,
`r n ≤ 32.54 N / log² N · singProd n`. Sieve level `z = N / log^9 N`. -/
theorem S1u_3254 : ∀ N : ℕ, N₂ ≤ N → ∀ n ∈ Icc 1 N,
    (r n : ℝ) ≤ 32.54 * N / (Real.log N) ^ 2 * singProd n := by
  intro N hN n hn
  simp only [mem_Icc] at hn
  have hu := log_ge_of_ge N hN
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (le_trans (by norm_num) N₂_ge) hN
    exact_mod_cast this
  clear hN
  have hNpos : (0 : ℝ) < N := by linarith
  set u := Real.log N with hu_def
  have hupos : 0 < u := by linarith
  have hsp := one_le_singProd n
  have hexpu : Real.exp u = N := Real.exp_log hNpos
  have hNl : (N : ℝ) / u ^ 2 ≥ 1 / 4 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith [log_sq_le N hN1]
  by_cases hev : Even n ∧ 4 ≤ n
  · obtain ⟨hev, hn4⟩ := hev
    have hlu := log_le_u_8192 u hupos
    set w := u - 9 * Real.log u with hw
    have hw_ge : 0.99169 * u ≤ w := by
      have hw' : w = u - 9 * Real.log u := hw
      linarith
    have hwpos : 0 < w := by linarith
    set z := Real.exp w with hz
    have hz1 : 1 < z := by rw [hz]; exact Real.one_lt_exp_iff.mpr hwpos
    have hrz := r_le_of_even hev (by omega) hz1
    have hlogz : Real.log z = w := Real.log_exp _
    rw [hlogz] at hrz
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    -- z = N / u^9
    have hz_eq : z * u ^ 9 = N := by
      rw [hz, hw, Real.exp_sub, ← hexpu]
      have : Real.exp (9 * Real.log u) = u ^ 9 := by
        rw [show (9 : ℝ) * Real.log u = ((9 : ℕ) : ℝ) * Real.log u by norm_num,
          Real.exp_nat_mul, Real.exp_log hupos]
      rw [this]
      field_simp
    have hzpos : 0 < z := by positivity
    -- main term
    have hmain : 32 * n * singProd n / w ^ 2 ≤ 32.539 * (N / u ^ 2 * singProd n) := by
      have hw2 : (0.99169 * u) ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by positivity) hw_ge 2
      have hs0 : 0 ≤ singProd n := by linarith
      have hnum : 32 * n * singProd n ≤ 32 * N * singProd n := by
        have := mul_le_mul_of_nonneg_right hnN hs0
        nlinarith
      have step1 : 32 * n * singProd n / w ^ 2 ≤ 32 * N * singProd n / (0.99169 * u) ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hw2
      have e : 32 * N * singProd n / (0.99169 * u) ^ 2 =
          (32 / 0.99169 ^ 2) * (N / u ^ 2 * singProd n) := by
        field_simp
      have hc : (32 / 0.99169 ^ 2 : ℝ) ≤ 32.539 := by norm_num
      have hpos : 0 ≤ N / u ^ 2 * singProd n := by positivity
      rw [e] at step1
      exact step1.trans (mul_le_mul_of_nonneg_right hc hpos)
    -- error term
    have herr : z * (1 + w) ^ 6 + 2 * (z + 1) ≤ 0.001 * (N / u ^ 2 * singProd n) := by
      have hwu : w ≤ u := by
        have : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
        linarith
      have h1 : (1 + w) ^ 6 ≤ (1 + u) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
      have h2 := pow6_le u hu
      have h3 : z * (1 + w) ^ 6 + 2 * (z + 1) ≤ z * ((1 + u) ^ 6 + 4) := by nlinarith
      have h4 : z * ((1 + u) ^ 6 + 4) ≤ z * (2 * u ^ 6) := mul_le_mul_of_nonneg_left h2 hzpos.le
      have h5 : z * (2 * u ^ 6) * u ^ 3 = 2 * N := by rw [← hz_eq]; ring
      have hu3 : (10000 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
      have h6 : z * (2 * u ^ 6) ≤ 0.001 * (N / u ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        have hX : 0 ≤ z * (2 * u ^ 6) * u ^ 2 := by positivity
        have hXu : z * (2 * u ^ 6) * u ^ 2 * u = 2 * N := by rw [← h5]; ring
        have := mul_le_mul_of_nonneg_left hu hX
        linarith
      have h7 : 0.001 * (N / u ^ 2) ≤ 0.001 * (N / u ^ 2 * singProd n) := by
        have h0 : 0 ≤ N / u ^ 2 := by positivity
        have := le_mul_of_one_le_right h0 hsp
        linarith
      linarith
    calc (r n : ℝ) ≤ 32.539 * (N / u ^ 2 * singProd n) + 0.001 * (N / u ^ 2 * singProd n) := by
          linarith
      _ = 32.54 * N / u ^ 2 * singProd n := by ring
  · have h3 : (r n : ℝ) ≤ 3 := by exact_mod_cast r_le_three_of_not hev
    have : (3 : ℝ) ≤ 32.54 * (N / u ^ 2 * singProd n) := by nlinarith
    calc (r n : ℝ) ≤ 32.54 * (N / u ^ 2 * singProd n) := by linarith
      _ = 32.54 * N / u ^ 2 * singProd n := by ring

end LeanLab.SchnirelmannGoldbach.Task63

#print axioms LeanLab.SchnirelmannGoldbach.Task63.log_le_u_8192

#print axioms LeanLab.SchnirelmannGoldbach.Task63.log_le_of_lt_12000

#print axioms LeanLab.SchnirelmannGoldbach.Task63.S1u_3254
