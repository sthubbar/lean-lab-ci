/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary bounds for Case 2 of Lemma 2.1, pages 347 to 348.
The estimates here avoid the false printed totient comparison already recorded in Arith.lean.
They do not prove the cited GRH estimate 2.9.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.TotientTail
import LeanLab.Zinoviev1997.Arith

namespace LeanLab.Zinoviev1997
open Real Finset

/-- An elementary lower bound that suffices after splitting the denominator range. -/
theorem totient_ge_six (q : ℕ) (L : ℝ) (hL : 46 ≤ L) (hq : L ^ 2 ≤ q) :
    6 * L ≤ Nat.totient q := by
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by nlinarith
    exact_mod_cast this
  have h := seventh_le_totient_eighth q hq0
  have hr : (q : ℝ) ^ 7 ≤ 2401 * (Nat.totient q : ℝ) ^ 8 := by exact_mod_cast h
  have hL6 : (2401 : ℝ) * 6 ^ 8 ≤ L ^ 6 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 46) hL 6
    norm_num at hpow ⊢
    linarith
  have hq7 : L ^ 14 ≤ (q : ℝ) ^ 7 := by
    have hh := pow_le_pow_left₀ (sq_nonneg L) hq 7
    convert hh using 1 <;> ring
  have hcomp : (2401 : ℝ) * (6 * L) ^ 8 ≤ 2401 * (Nat.totient q : ℝ) ^ 8 := by
    calc
      _ = (2401 * 6 ^ 8) * L ^ 8 := by ring
      _ ≤ L ^ 6 * L ^ 8 := mul_le_mul_of_nonneg_right hL6 (by positivity)
      _ = L ^ 14 := by ring
      _ ≤ (q : ℝ) ^ 7 := hq7
      _ ≤ _ := hr
  have hroot : (6 * L) ^ 8 ≤ (Nat.totient q : ℝ) ^ 8 := by linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _) (by norm_num : (8 : ℕ) ≠ 0)).mp hroot

/-- A sharp enough fourth power exponential comparison on the actual logarithm range. -/
theorem fourth_lt_exp (x : ℝ) (hx : 46 ≤ x) : x ^ 4 < 0.00046 * Real.exp (x / 2) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_sub_one_of_pos (show 0 < x / 46 by positivity)
  have hl' : 4 * Real.log (x / 46) ≤ (x - 46) / 2 := by nlinarith
  have hp : (x / 46) ^ 4 ≤ Real.exp ((x - 46) / 2) := by
    calc
      _ = Real.exp (4 * Real.log (x / 46)) := by
        have he4 := Real.exp_nat_mul (Real.log (x / 46)) 4
        norm_num only [Nat.cast_ofNat] at he4
        rw [Real.exp_log (by positivity)] at he4
        exact he4.symm
      _ ≤ _ := Real.exp_le_exp.mpr hl'
  have he : Real.exp ((x - 46) / 2) * Real.exp 23 = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hn : (46 : ℝ) ^ 4 < 0.00046 * Real.exp 23 := by
    have he23 : (2.7182818283 : ℝ) ^ 23 < Real.exp 23 := by
      have hh := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (23 : ℕ) ≠ 0)
      simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hh
    have hnum : (46 : ℝ) ^ 4 < 0.00046 * (2.7182818283 : ℝ) ^ 23 := by norm_num
    linarith
  have hprod : x ^ 4 * Real.exp 23 ≤ (46 : ℝ) ^ 4 * Real.exp (x / 2) := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos 23).le
    rw [he] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 46 ^ 4 by positivity)
    convert hmul using 1 <;> ring
  have hh := mul_lt_mul_of_pos_right hn (Real.exp_pos (x / 2))
  have hc : x ^ 4 * Real.exp 23 < (0.00046 * Real.exp (x / 2)) * Real.exp 23 := by
    nlinarith
  exact lt_of_mul_lt_mul_right hc (Real.exp_pos 23).le

/-- A corresponding cubic comparison for the small denominator range. -/
theorem cube_lt_exp_sharp (x : ℝ) (hx : 46 ≤ x) : x ^ 3 < 0.00001 * Real.exp (x / 2) := by
  have h := fourth_lt_exp x hx
  have hp : 0 < x ^ 3 := by positivity
  have hh := mul_le_mul_of_nonneg_right hx hp.le
  nlinarith

/-- The upper alternative in display 2.9 is sufficient on E2.
This is an elementary numerical estimate, independent of GRH. -/
theorem minor_upper_case2 (N : ℝ) (q : ℕ) (hN : 10 ^ 20 ≤ N)
    (hq : Real.log N ^ 2 ≤ q) (hqτ : (q : ℝ) ≤ 4900 * Real.log N ^ 4) :
    N / Nat.totient q + 2.75 * Real.sqrt (N * q) * Real.log N <
      0.18 * N / Real.log N := by
  let L := Real.log N
  have hn : 0 < N := by linarith
  have hl : 46 ≤ L := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have hl0 : 0 < L := by linarith
  have hs0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hn
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hn.le
  have he : Real.exp (L / 2) = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn]
    congr 1
    ring
  have hc := cube_lt_exp_sharp L hl
  have hf := fourth_lt_exp L hl
  rw [he] at hc hf
  have hφ := totient_ge_six q L hl hq
  have hφ0 : (0 : ℝ) < Nat.totient q := by linarith
  change N / Nat.totient q + 2.75 * Real.sqrt (N * q) * L < 0.18 * N / L
  rw [Real.sqrt_mul hn.le]
  by_cases hsmall : (q : ℝ) ≤ 9 * L ^ 2
  · have hsq : Real.sqrt q ≤ 3 * L := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith
    have hmain : N / Nat.totient q ≤ (1 / 6 : ℝ) * N / L := by
      have hh := div_le_div_of_nonneg_left hn.le (show 0 < 6 * L by positivity) hφ
      convert hh using 1 <;> ring
    have herr : 2.75 * (Real.sqrt N * Real.sqrt q) * L ≤ 0.0000825 * N / L := by
      rw [le_div_iff₀ hl0]
      have hh := mul_le_mul_of_nonneg_left hc.le (Real.sqrt_pos.mpr hn).le
      have hroot := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2.75 * Real.sqrt N * L ^ 2 by positivity)
      nlinarith
    have hpos : 0 < N / L := div_pos hn hl0
    simp only [div_eq_mul_inv] at hmain herr hpos ⊢
    nlinarith
  · have hφ' := totient_ge_six q (3 * L) (by linarith) (by nlinarith)
    have hsq : Real.sqrt q ≤ 70 * L ^ 2 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · change (q : ℝ) ≤ 4900 * L ^ 4 at hqτ
        nlinarith [hqτ]
    have hmain : N / Nat.totient q ≤ (1 / 18 : ℝ) * N / L := by
      have hh := div_le_div_of_nonneg_left hn.le (show 0 < 6 * (3 * L) by positivity) hφ'
      convert hh using 1 <;> ring
    have herr : 2.75 * (Real.sqrt N * Real.sqrt q) * L ≤ 0.08855 * N / L := by
      rw [le_div_iff₀ hl0]
      have hh := mul_le_mul_of_nonneg_left hf.le (Real.sqrt_pos.mpr hn).le
      have hroot := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2.75 * Real.sqrt N * L ^ 2 by positivity)
      nlinarith
    have hpos : 0 < N / L := div_pos hn hl0
    simp only [div_eq_mul_inv] at hmain herr hpos ⊢
    nlinarith

/-- The lower alternative in display 2.9 uses the large phase bound for its leading term. -/
theorem minor_lower_case2 (N : ℝ) (q : ℕ) (hN : 10 ^ 20 ≤ N)
    (hq : Real.log N ^ 2 ≤ q) :
    N / (10 * Nat.totient q) + 0.1 * N / Real.log N < 0.18 * N / Real.log N := by
  let L := Real.log N
  have hn : 0 < N := by linarith
  have hl : 46 ≤ L := le_trans log_1e20_ge (Real.log_le_log (by norm_num) hN)
  have hl0 : 0 < L := by linarith
  have hφ := totient_ge_six q L hl hq
  have hmain : N / (10 * Nat.totient q) ≤ (1 / 60 : ℝ) * N / L := by
    have hh := div_le_div_of_nonneg_left hn.le (show 0 < 60 * L by positivity)
      (show 60 * L ≤ 10 * (Nat.totient q : ℝ) by linarith)
    convert hh using 1 <;> ring
  change N / (10 * Nat.totient q) + 0.1 * N / L < 0.18 * N / L
  have hpos : 0 < N / L := div_pos hn hl0
  simp only [div_eq_mul_inv] at hmain hpos ⊢
  nlinarith

end LeanLab.Zinoviev1997
