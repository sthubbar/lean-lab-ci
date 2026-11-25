/-
Split of three page 50 to 63 leaves of Feed1122Decomp420bP2.
Helfgott https://arxiv.org/abs/1312.7748v2, page 51 and page 63, equations 6.10, 6.11,
7.26 and the display before 7.27. The bound on E of 6.10 is split into the non prime
part, from RS62 Theorem 13 by partial summation, and the part with n at most root x,
from RS62 Theorem 12; the page 63 arithmetic 7.26 is proved. The bound on S eta star at
zero is reduced to the existing leaf Task580.star_mass_error, equation 7.16.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp420bP2
import LeanLab.Ternary.Decomp580b

open Finset

namespace LeanLab.Ternary.Task420

/-- LEAF: Helfgott 1312.7748v2 page 51, the display after Let eta plus bar, from
RS62 Theorem 13, partial summation and integration by parts, with the page 62 bounds
C eta plus 0 at most 2.3375 and C eta plus 1 at most 0.4494 of 6.11:
the sum over non-prime n of Lambda of n squared times eta plus of n over x squared is
at most 2.3375 log x plus 2 times 2.3375 plus 0.4494, times root x, HARD. -/
theorem helfgott_E_nonprime_part (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (if n.Prime then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2)) ≤
      (2.3375 * Real.log (LeanLab.Helfgott2013.xOf N) + (2 * 2.3375 + 0.4494)) * Real.sqrt (LeanLab.Helfgott2013.xOf N) := by
  sorry

/-- The page 63 arithmetic of 7.26: for x at least 4.9545e26, the bound
2.3375 plus 0.6058 times log x plus 2 times 2.3375 plus 0.4494, times root x, is at most
8.4031e-12 x. Helfgott 1312.7748v2 page 63 equation 7.26. -/
theorem E_726_arith {x : ℝ} (hx : 4.9545e26 ≤ x) :
    ((2.3375 + 0.6058) * Real.log x + (2 * 2.3375 + 0.4494)) * Real.sqrt x ≤
      8.4031e-12 * x := by
  set y := Real.sqrt x with hy
  set y0 : ℝ := 2 ^ 44 * 1.265 with hy0
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hyy : y ^ 2 = x := Real.sq_sqrt hx0
  have hy0pos : 0 < y0 := by rw [hy0]; positivity
  have hy0y : y0 ≤ y := by
    rw [hy]; apply Real.le_sqrt_of_sq_le; rw [hy0]; norm_num at hx ⊢; linarith
  have hypos : 0 < y := lt_of_lt_of_le hy0pos hy0y
  have hlogx : Real.log x = 2 * Real.log y := by
    rw [← hyy, Real.log_pow]; push_cast; ring
  have hlog2 := Real.log_two_lt_d9
  have hlogy0 : Real.log y0 ≤ 44 * 0.6931471808 + 0.265 := by
    rw [hy0, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    have h1 : Real.log (1.265 : ℝ) ≤ 1.265 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    push_cast
    nlinarith
  have hlogy : Real.log y ≤ Real.log y0 + y / y0 - 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < y / y0 by positivity)
    rw [Real.log_div hypos.ne' hy0pos.ne'] at h
    linarith
  have hyd : y / y0 * y0 = y := div_mul_cancel₀ y hy0pos.ne'
  have hkey : (2.3375 + 0.6058) * Real.log x + (2 * 2.3375 + 0.4494) ≤ 8.4031e-12 * y := by
    rw [hlogx]
    have hc : (8.4031e-12 : ℝ) * y0 - (2.3375 + 0.6058) * 2 ≥
        (2.3375 + 0.6058) * 2 * (44 * 0.6931471808 + 0.265 - 1) + (2 * 2.3375 + 0.4494) := by
      rw [hy0]; norm_num
    set k : ℝ := 8.4031e-12 - (2.3375 + 0.6058) * 2 / y0 with hkdef
    have hk : 0 ≤ k := by rw [hkdef, hy0]; norm_num
    have e1 : 8.4031e-12 * y - (2.3375 + 0.6058) * 2 * (y / y0) = k * y := by
      rw [hkdef]; ring
    have e2 : k * y0 = 8.4031e-12 * y0 - (2.3375 + 0.6058) * 2 := by
      rw [hkdef, sub_mul, div_mul_cancel₀ _ hy0pos.ne']
    have e3 : k * y0 ≤ k * y := mul_le_mul_of_nonneg_left hy0y hk
    nlinarith
  calc _ ≤ 8.4031e-12 * y * y := mul_le_mul_of_nonneg_right hkey hypos.le
    _ = 8.4031e-12 * x := by rw [← hyy]; ring

/-- x is at least 4.9545e26 for N at least 10 to the 27, using root 2 pi at least 2.5066.
Helfgott 1312.7748v2 page 59, x as a multiple of N. -/
theorem xOf_ge_4952 (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    4.9545e26 ≤ LeanLab.Helfgott2013.xOf N := by
  unfold LeanLab.Helfgott2013.xOf LeanLab.Helfgott2013.ratio
  have hs : (2.5066 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    apply Real.le_sqrt_of_sq_le; nlinarith [Real.pi_gt_d6]
  have hd : 9 / (196 * Real.sqrt (2 * Real.pi)) ≤ 9 / (196 * 2.5066) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
  have hden : 0 < 2 + 9 / (196 * Real.sqrt (2 * Real.pi)) := by positivity
  have hr : (1 : ℝ) / (2 + 9 / (196 * 2.5066)) ≤ 1 / (2 + 9 / (196 * Real.sqrt (2 * Real.pi))) :=
    one_div_le_one_div_of_le hden (by linarith)
  have hr0 : (0.49545 : ℝ) ≤ 1 / (2 + 9 / (196 * 2.5066)) := by norm_num
  have hN' : (1e27 : ℝ) ≤ N := by norm_num at hN ⊢; exact hN
  nlinarith

/-- LEAF: Rosser and Schoenfeld 1962, Theorem 12, cited on Helfgott 1312.7748v2 page 51:
psi of y is less than 1.03883 y for every positive y, HARD. -/
theorem rs62_psi_le (y : ℝ) (hy : 0 < y) : Chebyshev.psi y ≤ 1.03883 * y := by
  sorry

/-- Helfgott 1312.7748v2 page 51, the display after while, by RS62 Theorem 12: the
sum over n at most root x of Lambda of n squared times eta plus of n over x squared is
at most one half the sup of eta plus squared times log x times psi of root x. With the
lab bound 1.079955 for the sup, page 56 equation 7.3, this gives 0.6058 times root x
times log x. The page 63 value 0.60579 uses 0.51941 for 1.03883 over 2, which is
0.519415, so 0.60579 is replaced by 0.6058. CONDITIONAL ON rs62_psi_le. -/
theorem helfgott_E_small_part (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (if (n : ℝ) ≤ Real.sqrt (LeanLab.Helfgott2013.xOf N) then
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2 else 0)) ≤
      0.6058 * Real.log (LeanLab.Helfgott2013.xOf N) * Real.sqrt (LeanLab.Helfgott2013.xOf N) := by
  have hx := xOf_pos N hN
  set x := LeanLab.Helfgott2013.xOf N
  set y := Real.sqrt x with hydef
  have hy : 0 < y := Real.sqrt_pos.mpr hx
  have hlogy : Real.log y = Real.log x / 2 := by
    rw [hydef, Real.log_sqrt hx.le]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [xOf_ge_4952 N hN])
  rw [tsum_eq_sum (s := Icc 0 ⌊y⌋₊)]
  · have hterm : ∀ n ∈ Icc 0 ⌊y⌋₊, (if (n : ℝ) ≤ y then
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2 else 0) ≤
        (Real.log x / 2 * 1.079955 ^ 2) * (ArithmeticFunction.vonMangoldt n : ℝ) := by
      intro n hn
      have hny : (n : ℝ) ≤ y := by
        have := (mem_Icc.mp hn).2
        exact (Nat.cast_le.mpr this).trans (Nat.floor_le hy.le)
      rw [ite_cond_eq_true _ _ (eq_true hny)]
      have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log x / 2 := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simp; positivity
        · rw [← hlogy]
          exact ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast hpos) hny)
      have hη : LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2 ≤ 1.079955 ^ 2 := by
        have := etaPlus_abs_le (n / x)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have h2 : (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 ≤
          Real.log x / 2 * (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hΛ hΛ0
      calc _ ≤ Real.log x / 2 * (ArithmeticFunction.vonMangoldt n : ℝ) * 1.079955 ^ 2 :=
            mul_le_mul h2 hη (by positivity) (by positivity)
        _ = _ := by ring
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum, ← Chebyshev.psi_eq_sum_Icc]
    have hpsi := rs62_psi_le y hy
    have hc : (0 : ℝ) ≤ Real.log x / 2 * 1.079955 ^ 2 := by positivity
    calc _ ≤ (Real.log x / 2 * 1.079955 ^ 2) * (1.03883 * y) := mul_le_mul_of_nonneg_left hpsi hc
      _ = (1.079955 ^ 2 * 1.03883 / 2) * Real.log x * y := by ring
      _ ≤ 0.6058 * Real.log x * y := by
        apply mul_le_mul_of_nonneg_right _ hy.le
        apply mul_le_mul_of_nonneg_right _ hlx
        norm_num
  · intro n hn
    have : ¬ (n : ℝ) ≤ y := by
      intro h
      apply hn
      exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor h⟩
    rw [ite_cond_eq_false _ _ (eq_false this)]

/-- Lambda squared times eta plus squared is summable.
Helfgott 1312.7748v2 page 51, the sums in E of 6.10. -/
theorem etaPlus_sq_coefficients_summable {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
      LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2 := by
  have hs := etaPlus_coefficients_summable hx
  set a : ℕ → ℝ := fun n => ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (LeanLab.HelfgottArcs.etaPlus (n / x) : ℂ)‖ with ha
  have hle (n : ℕ) : a n ≤ ∑' m, a m := hs.le_tsum n (fun m _ => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hs.mul_left (∑' m, a m))
  intro n
  have hsq : (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
      LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2 = a n * a n := by
    simp only [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← abs_mul, abs_mul_abs_self]; ring
  rw [hsq]
  exact mul_le_mul_of_nonneg_right (hle n) (norm_nonneg _)

/-- The leaf helfgott_E_bound from the two parts of E and the 7.26 arithmetic.
Helfgott 1312.7748v2 page 51 and page 63 equation 7.26. -/
theorem helfgott_E_bound_of_leaves (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2)) ≤
      8.4031e-12 * LeanLab.Helfgott2013.xOf N := by
  have hx := xOf_pos N hN
  set x := LeanLab.Helfgott2013.xOf N with hxdef
  have hsum := etaPlus_sq_coefficients_summable hx
  have h1 := helfgott_E_nonprime_part N hN
  have h2 := helfgott_E_small_part N hN
  rw [← hxdef] at h1 h2
  have hA : Summable fun n : ℕ => (if n.Prime then 0 else
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 * LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> first | positivity | exact le_refl _) hsum
  have hB : Summable fun n : ℕ => (if (n : ℝ) ≤ Real.sqrt x then
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 * LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> first | positivity | exact le_refl _) hsum
  have hC : Summable fun n : ℕ => (if n.Prime ∧ Real.sqrt x < n then 0 else
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 * LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> first | positivity | exact le_refl _) hsum
  have hle : (∑' n : ℕ, (if n.Prime ∧ Real.sqrt x < n then 0 else
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 * LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2)) ≤
      (∑' n : ℕ, (if n.Prime then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 * LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2)) +
      ∑' n : ℕ, (if (n : ℝ) ≤ Real.sqrt x then
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 * LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2
        else 0) := by
    rw [← hA.tsum_add hB]
    apply hC.tsum_le_tsum _ (hA.add hB)
    intro n
    have h0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
        LeanLab.HelfgottArcs.etaPlus (n / x) ^ 2 := by positivity
    by_cases hp : n.Prime
    · by_cases hs : Real.sqrt x < n
      · simp only [hp, hs, and_self, ite_true]; split_ifs <;> linarith
      · have hs' : (n : ℝ) ≤ Real.sqrt x := le_of_not_gt hs
        simp only [hp, hs, hs', and_false, ite_false, ite_true]; linarith
    · simp only [hp, false_and, ite_false]; split_ifs <;> linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith [xOf_ge_4952 N hN])
  calc _ ≤ _ := hle
    _ ≤ (2.3375 * Real.log x + (2 * 2.3375 + 0.4494)) * Real.sqrt x +
        0.6058 * Real.log x * Real.sqrt x := add_le_add h1 h2
    _ = ((2.3375 + 0.6058) * Real.log x + (2 * 2.3375 + 0.4494)) * Real.sqrt x := by ring
    _ ≤ 8.4031e-12 * x := E_726_arith (xOf_ge_4952 N hN)

/-- The leaf helfgott_Sstar_zero_upper from Task580.star_mass_upper, which is
CONDITIONAL ON the existing leaf Task580.star_mass_error, equation 7.16.
Helfgott 1312.7748v2 page 63, the display before 7.27. -/
theorem helfgott_Sstar_zero_upper_of_leaves (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (n / LeanLab.Helfgott2013.xOf N))) ≤
      (Real.sqrt (Real.pi / 2) + 1.9075e-8) * LeanLab.Helfgott2013.xOf N /
        LeanLab.Helfgott2013.κ :=
  LeanLab.Ternary.Task580.star_mass_upper _
    (le_trans (by norm_num) (xOf_ge_4952 N hN))

end LeanLab.Ternary.Task420
