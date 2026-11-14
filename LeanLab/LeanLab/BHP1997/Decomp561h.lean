/-
P0069 page 8, the eta tail before display 2.7.
Elementary reciprocal totient averaging and reciprocal square integration.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561a
import LeanLab.BHP1997.EnergyLogC165
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace LeanLab.BHP1997.Decomp561h
open Finset MeasureTheory

/-- P0069 page 8, the sum of q over phi q on a full modulus range.
A harmonic divisor moment supplies a sufficient logarithmic square bound. -/
theorem sum_totient_ratio_le561 (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 N, (q : ℝ) / (Nat.totient q : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) ^ 2 := by
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 N, (N : ℝ) * ((q.divisors.card : ℝ) / q) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hq1, hqN⟩ := Finset.mem_Icc.mp hq
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
      calc
        _ ≤ (q.divisors.card : ℝ) := Decomp561a.divisor_totient_ratio_le
          (Nat.mem_divisors_self q (by omega))
        _ = (q : ℝ) * ((q.divisors.card : ℝ) / q) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hqN) (by positivity)
    _ = (N : ℝ) * EnergyLogC165.harmonicDivisorMoment 1 N := by
      simp [EnergyLogC165.harmonicDivisorMoment, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      simpa using EnergyLogC165.harmonicDivisorMoment_le 1 N

/-- P0069 page 8, the same average with the actual real cutoff P. -/
theorem sum_totient_ratio_le_real561 {P : ℝ} (hP : 1 ≤ P) :
    (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, (q : ℝ) / (Nat.totient q : ℝ)) ≤
      P * (1 + Real.log P) ^ 2 := by
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hN : 1 ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP0).mpr (by simpa using hP)
  have hN0 : (0 : ℝ) < ⌊P⌋₊ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hfloor : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hP0
  have hlog : Real.log (⌊P⌋₊ : ℝ) ≤ Real.log P := Real.log_le_log hN0 hfloor
  have hlog0 : 0 ≤ Real.log (⌊P⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ (⌊P⌋₊ : ℝ) * (1 + Real.log (⌊P⌋₊ : ℝ)) ^ 2 := sum_totient_ratio_le561 _
    _ ≤ _ := by gcongr

/-- P0069 page 8, the exact reciprocal square integral in the eta tail. -/
theorem integral_inv_square561 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) = 1 / a - 1 / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, not_and]
    intro h
    linarith
  have he : (∫ t in a..b, 1 / t ^ 2) = ∫ t in a..b, t ^ (-2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 ≤ t := ha.le.trans ht.1
    change 1 / t ^ 2 = t ^ (-2 : ℝ)
    rw [Real.rpow_neg ht0, Real.rpow_two, one_div]
  rw [he, integral_rpow (Or.inr ⟨by norm_num, hz⟩)]
  norm_num [Real.rpow_neg_one]
  ring

/-- P0069 page 8, the eta tail integral is at most the reciprocal lower endpoint. -/
theorem integral_inv_square_le561 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) ≤ 1 / a := by
  rw [integral_inv_square561 ha hab]
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hb : 0 ≤ 1 / b := by positivity
  linarith


/-- P0069 page 8, the summed eta tail before display 2.7.
For P squared at most Y over 2, the printed lower eta endpoints lie below
one half. Averaging q over phi q leaves the saving one over P. -/
theorem summed_eta_tail561 {Y P : ℝ} (hY : 0 < Y) (hP : 1 ≤ P)
    (hPY : 2 * P ^ 2 ≤ Y) :
    (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, 1 / (Nat.totient q : ℝ) *
      ∫ t in (P ^ 2 / ((q : ℝ) * Y))..(1 / 2 : ℝ), 1 / t ^ 2) ≤
      Y / P * (1 + Real.log P) ^ 2 := by
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
        ((q : ℝ) / (Nat.totient q : ℝ)) * Y / P ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
      have hphi : (0 : ℝ) < Nat.totient q := by
        exact_mod_cast Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq1)
      have ha : 0 < P ^ 2 / ((q : ℝ) * Y) := by positivity
      have hab : P ^ 2 / ((q : ℝ) * Y) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ (mul_pos hq0 hY)).mpr
        have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
        nlinarith
      calc
        _ ≤ 1 / (Nat.totient q : ℝ) * (1 / (P ^ 2 / ((q : ℝ) * Y))) :=
          mul_le_mul_of_nonneg_left (integral_inv_square_le561 ha hab) (by positivity)
        _ = _ := by field_simp
    _ = (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, (q : ℝ) / (Nat.totient q : ℝ)) * Y / P ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
    _ ≤ (P * (1 + Real.log P) ^ 2) * Y / P ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sum_totient_ratio_le_real561 hP) hY.le) (sq_nonneg P)
    _ = _ := by field_simp

/-- P0069 page 8, the explicit logarithmic saving in the eta arithmetic bound.
The auxiliary factor involving log log is absorbed by two powers of log. -/
theorem eta_cutoff_log_saving561 {Y l D : ℝ} (hY : 0 ≤ Y) (hl : 1 ≤ l) (hD : 0 ≤ D) :
    Y / l ^ (2 * D) * (1 + Real.log (l ^ (2 * D))) ^ 2 ≤
      (1 + 2 * D) ^ 2 * Y * l ^ (-2 * D + 2) := by
  have hl0 : 0 < l := lt_of_lt_of_le zero_lt_one hl
  have hlog0 : 0 ≤ Real.log l := Real.log_nonneg hl
  have hlog : Real.log l ≤ l := (Real.log_le_sub_one_of_pos hl0).trans (by linarith)
  have hbase : 1 + 2 * D * Real.log l ≤ (1 + 2 * D) * l := by nlinarith
  have he : (l ^ (2 : ℝ)) / l ^ (2 * D) = l ^ (-2 * D + 2) := by
    rw [← Real.rpow_sub hl0]
    congr 1
    ring
  rw [Real.log_rpow hl0]
  calc
    _ ≤ Y / l ^ (2 * D) * ((1 + 2 * D) * l) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase 2) (by positivity)
    _ = (1 + 2 * D) ^ 2 * Y * (l ^ (2 : ℝ) / l ^ (2 * D)) := by rw [Real.rpow_two]; ring
    _ = _ := by rw [he]

end LeanLab.BHP1997.Decomp561h
