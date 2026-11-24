/-
Helfgott https://arxiv.org/abs/1312.7748v2 page 59 equation 7.16 and page 63,
and the book https://arxiv.org/abs/1501.05438v2 printed page 264 equation 14.17.
Scalar audit of the cited constant behind Decomp580b.star_mass_error.
Pass 3 adds a split of star_mass_error through an explicit psi bound,
BKLNW 2021 arXiv 2002.11068v2, and Abel summation, with LEAF sorries.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import LeanLab.Ternary.Decomp580b

namespace LeanLab.Ternary.Feed1122Decomp580b

/-- The v2 printed constant 1.9075e-8 is reproduced exactly when the square root
is taken of the unscaled threshold x+ equal to 4.9e26.
Helfgott 1312.7748v2 page 59 equation 7.16, with Major arcs Corollary 1.3. -/
theorem v2_eq716_constant_with_sqrt_xplus :
    (4.269e-14 : ℝ) + (380600 + 76 * Real.sqrt 300000) / Real.sqrt 4.9e26 ≤ 1.9075e-8 := by
  have h1 : Real.sqrt 300000 ≤ 547.723 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : (2.2135943e13 : ℝ) ≤ Real.sqrt 4.9e26 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hp : (0 : ℝ) < Real.sqrt 4.9e26 := by linarith
  have h3 : (380600 + 76 * Real.sqrt 300000) / Real.sqrt 4.9e26 ≤ 1.90745e-8 := by
    rw [div_le_iff₀ hp]; nlinarith
  linarith

/-- With the scaling y equal to x over kappa that the text itself names, the same
Corollary 1.3 terms at the threshold y equal to 1e25 exceed the v2 allowance.
Helfgott 1312.7748v2 page 59 equation 7.16 and line 7.15, kappa equal to 49. -/
theorem eq716_scaled_terms_exceed_v2_allowance :
    (1.9075e-8 : ℝ) < 4.269e-14 + (380600 + 76 * Real.sqrt 300000) / Real.sqrt 1e25 := by
  have h1 : (547 : ℝ) ≤ Real.sqrt 300000 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.sqrt 1e25 ≤ 3.17e12 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp : (0 : ℝ) < Real.sqrt 1e25 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (1.9075e-8 : ℝ) < (380600 + 76 * Real.sqrt 300000) / Real.sqrt 1e25 := by
    rw [lt_div_iff₀ hp]; nlinarith
  linarith

/-- The book corrects the square root to that of 1e25, but its printed value
1.33805e-8 is ten times smaller than the displayed terms, which exceed 1.338e-7.
Helfgott book 1501.05438v2 printed page 264 equation 14.17. -/
theorem book_eq1417_terms_exceed_printed :
    (1.338e-7 : ℝ) < 2.485e-19 + (381500 + 76 * Real.sqrt 300000) / Real.sqrt 1e25 := by
  have h1 : (547.72 : ℝ) ≤ Real.sqrt 300000 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h2 : Real.sqrt 1e25 ≤ 3.1623e12 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp : (0 : ℝ) < Real.sqrt 1e25 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (1.338e-7 : ℝ) < (381500 + 76 * Real.sqrt 300000) / Real.sqrt 1e25 := by
    rw [lt_div_iff₀ hp]; nlinarith
  have h4 : (0 : ℝ) ≤ 2.485e-19 := by norm_num
  linarith

/-! Pass 3. Route through an explicit psi bound instead of Major arcs Corollary 1.3. -/

open MeasureTheory

/-- LEAF: explicit psi bound, HARD for Codex. BKLNW 2021 arXiv 2002.11068v2: (A.26) from
Buthe 2018 eq 1.5 for 100 ≤ x ≤ 1e19 with 0.94; eps(19 log 10) = 1.93378e-8 for x ≥ 1e19,
Corollary 15.1 and page 25; Table 8 rows b ≥ 50 all at most 1.11990e-9 up to e^26000, and
eps = 4.60e-14 for x ≥ e^3000 by Platt and Trudgian, page 3. Pass 4 checked PDF pages 3, 24,
25, 26 as images: Table 8 bounds psi, rows valid on e^b to e^b', constants exact. -/
theorem psi_explicit_bklnw (t : ℝ) (ht : 100 < t) :
    |(∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) - t| ≤
      (if t ≤ 1e19 then 0.94 * Real.sqrt t
        else if t ≤ Real.exp 50 then 1.93378e-8 * t else 1.1199e-9 * t) := by
  sorry

/-- Finite check, kernel decide: lcm of 1 to k is at most 7 to the k for k up to 100.
Pass 4 helper for psi_small_range. -/
theorem lcmUpto_le_seven_pow : ∀ k : ℕ, k ≤ 100 → Nat.lcmUpto k ≤ 7 ^ k := by
  decide +kernel

/-- Finite range of the psi bound, PROVED in pass 4. For 0 ≤ t ≤ 100, psi of t is at
most 2t, via psi of n equal to log of lcm of 1 to n and lcm at most 7 to the n; it closes
the range below BKLNW 2021 (A.26). -/
theorem psi_small_range (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    |(∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) - t| ≤ t := by
  have hsum : (∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ))
      = Chebyshev.psi (⌊t⌋₊ : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Finset.range_eq_Ico]
    rfl
  rw [hsum]
  set k := ⌊t⌋₊ with hk
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht0
  have hk100 : k ≤ 100 := by
    have : k ≤ ⌊(100:ℝ)⌋₊ := Nat.floor_le_floor ht
    simpa using this
  have hpos : 0 ≤ Chebyshev.psi (k : ℝ) := Chebyshev.psi_nonneg _
  have hlcm : (0:ℝ) < (Nat.lcmUpto k : ℝ) := by
    have : 0 < Nat.lcmUpto k := Nat.lcmUpto_pos k
    exact_mod_cast this
  have h7 : (Nat.lcmUpto k : ℝ) ≤ (7:ℝ) ^ k := by exact_mod_cast lcmUpto_le_seven_pow k hk100
  have hlog7 : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hpsi : Chebyshev.psi (k : ℝ) ≤ 2 * k := by
    rw [Chebyshev.psi_eq_log_lcmUpto]
    calc Real.log (Nat.lcmUpto k) ≤ Real.log ((7:ℝ) ^ k) := Real.log_le_log hlcm h7
      _ = k * Real.log 7 := by rw [Real.log_pow]
      _ ≤ k * 2 := by gcongr
      _ = 2 * k := by ring
  rw [abs_le]; constructor <;> linarith

/-- LEAF: Abel summation for the smooth weight, MEDIUM for Open Math OS. The sum of
Lambda of n times eta star of n over x minus x times its integral equals minus the
integral of psi of t minus t against the derivative, so any integrable pointwise bound
on psi of t minus t bounds it. Partial summation step replacing Helfgott 1312.7748v2 eq 7.16. -/
theorem abel_star_bound (x : ℝ) (hx : 0 < x) (B : ℝ → ℝ)
    (hB : ∀ t, 0 ≤ t →
      |(∑ n ∈ Finset.range (⌊t⌋₊ + 1), (ArithmeticFunction.vonMangoldt n : ℝ)) - t| ≤ B t)
    (hint : IntegrableOn (fun t => B t * |deriv Task580.starWeight (t / x)| / x)
      (Set.Ioi 0)) :
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x)) -
      x * (∫ t in Set.Ioi (0 : ℝ), Task580.starWeight t)| ≤
      ∫ t in Set.Ioi (0 : ℝ), B t * |deriv Task580.starWeight (t / x)| / x := by
  sorry

/-- LEAF: numerics of the Abel integral, MEDIUM for Open Math OS. With the BKLNW
piecewise bound the integral against the eta star derivative is integrable and at most
1.9075e-8 x over kappa for x ≥ 4.9e26; a Python trapezoid run gives 4.57e-11 x against
3.89e-10 x at the threshold. Target Helfgott 1312.7748v2 eq 7.16. -/
theorem abel_numerics (x : ℝ) (hx : 4.9e26 ≤ x) :
    IntegrableOn (fun t => (if t ≤ 100 then t else if t ≤ 1e19 then 0.94 * Real.sqrt t
        else if t ≤ Real.exp 50 then 1.93378e-8 * t else 1.1199e-9 * t) *
        |deriv Task580.starWeight (t / x)| / x) (Set.Ioi 0) ∧
    (∫ t in Set.Ioi (0 : ℝ), (if t ≤ 100 then t else if t ≤ 1e19 then 0.94 * Real.sqrt t
        else if t ≤ Real.exp 50 then 1.93378e-8 * t else 1.1199e-9 * t) *
        |deriv Task580.starWeight (t / x)| / x) ≤
      1.9075e-8 * x / LeanLab.Helfgott2013.κ := by
  sorry

/-- star_mass_error from the leaves, the verbatim sealed statement of
Decomp580b.star_mass_error. Helfgott 1312.7748v2 page 59 eq 7.16.
CONDITIONAL ON psi_explicit_bklnw, abel_star_bound, abel_numerics; psi_small_range PROVED pass 4. -/
theorem star_mass_error_of_leaves (x : ℝ) (hx : 4.9e26 ≤ x) :
    |(∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * Task580.starWeight (n / x)) -
      x * (∫ t in Set.Ioi (0 : ℝ), Task580.starWeight t)| ≤
      1.9075e-8 * x / LeanLab.Helfgott2013.κ := by
  obtain ⟨hint, hle⟩ := abel_numerics x hx
  refine (abel_star_bound x (by linarith) _ ?_ hint).trans hle
  intro t ht
  by_cases h100 : t ≤ 100
  · rw [if_pos h100]; exact psi_small_range t ht h100
  · rw [if_neg h100]; exact psi_explicit_bklnw t (lt_of_not_ge h100)

end LeanLab.Ternary.Feed1122Decomp580b
