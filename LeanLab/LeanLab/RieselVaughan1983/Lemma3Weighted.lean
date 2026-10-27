import LeanLab.RieselVaughan1983.Lemma2SecondMoment

/-! Weighted sums in Lemma 3 on pages 51 and 52.
AI wrote the Lean code. Binary Goldbach is OPEN.
Lemma3ApproxP is stated and remains unproved. -/
namespace LeanLab.RieselVaughan1983.Lemma3
open Real Finset MeasureTheory
open LeanLab.RieselVaughan1983.Lemma2
open scoped ArithmeticFunction.Moebius
noncomputable section

/-- The n = 2 sum in equation 3.12. -/
def S2 (z : ℝ) : ℝ := ∑ q ∈ Icc 1 ⌊z⌋₊, sieveCoeff q / (1 + (q : ℝ) / z)

/-- Equation 3.15. -/
def M (y : ℝ) : ℝ := Real.log y ^ 2 + A3 * Real.log y + A4

/-- Equation 2.16 at lambda = 1. -/
def A6one : ℝ := 2 * A3 - 4 * Real.log 2
/-- The explicit identity for A7 at lambda = 1 on page 53. -/
def A7one : ℝ := 2 / 3 * Real.pi ^ 2 + 4 * A4 - 4 * A3 * Real.log 2
/-- Equation 2.18 at lambda = 1. -/
def A8one : ℝ := 8 * A5
/-- Equation 2.19 at lambda = 1. -/
def A9one : ℝ := 4 * A3

/-- Equation 3.14. This definition is not a proof. -/
def Lemma3ApproxP : Prop := ∀ z : ℝ, 1 ≤ z →
  |2 * Ctw * S2 z - Real.log z ^ 2 - A6one / 2 * Real.log z - A7one / 4| <
    A8one / 4 * z ^ (-(1 / 3 : ℝ)) + A9one / 4 * z ^ (-1 : ℝ)

lemma sieveCoeff_nonneg (q : ℕ) : 0 ≤ sieveCoeff q := by
  by_cases hq : q = 0
  · subst q; simp
  rw [sieveCoeff_apply q hq]
  apply mul_nonneg (sq_nonneg _)
  apply prod_nonneg
  intro p hp
  have hpprime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
  have hp2 : 2 < p := by have := hpprime.two_le; have := (mem_filter.mp hp).2; omega
  apply div_nonneg (by norm_num)
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  linarith

lemma S_nonneg (z : ℝ) : 0 ≤ S z :=
  sum_nonneg (fun q _ => sieveCoeff_nonneg q)

lemma S2_one : S2 1 = 1 / 2 := by simp [S2, sieveCoeff_one]; norm_num

lemma S2_nonneg (z : ℝ) (hz : 0 < z) : 0 ≤ S2 z := by
  apply sum_nonneg
  intro q hq
  apply div_nonneg (sieveCoeff_nonneg q)
  positivity

lemma S2_sandwich (z : ℝ) (hz : 0 < z) : S z / 2 ≤ S2 z ∧ S2 z ≤ S z := by
  have hterm (q : ℕ) (hq : q ∈ Icc 1 ⌊z⌋₊) :
      sieveCoeff q / 2 ≤ sieveCoeff q / (1 + (q : ℝ) / z) ∧
        sieveCoeff q / (1 + (q : ℝ) / z) ≤ sieveCoeff q := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hqz : (q : ℝ) ≤ z := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le hz.le)
    have hd : 0 < 1 + (q : ℝ) / z := by positivity
    have hd1 : 1 ≤ 1 + (q : ℝ) / z := by have := div_nonneg hq0 hz.le; linarith
    have hd2 : 1 + (q : ℝ) / z ≤ 2 := by have := (div_le_one hz).mpr hqz; linarith
    constructor
    · exact div_le_div_of_nonneg_left (sieveCoeff_nonneg q) hd hd2
    · exact (div_le_iff₀ hd).mpr (by nlinarith [sieveCoeff_nonneg q])
  constructor
  · rw [S, S2, sum_div]
    exact sum_le_sum (fun q hq => (hterm q hq).1)
  · exact sum_le_sum (fun q hq => (hterm q hq).2)

lemma half_polynomial_lower (z : ℝ) (hz : 1 ≤ z) :
    (M z - A5 * z ^ (-(1 / 3 : ℝ))) / 2 < 2 * Ctw * S2 z := by
  have h := (abs_lt.mp (lemma2_unconditional z hz)).1
  have hs := (S2_sandwich z (by linarith)).1
  have hC := Ctw_pos
  unfold M
  nlinarith

lemma polynomial_upper (z : ℝ) (hz : 1 ≤ z) :
    2 * Ctw * S2 z < M z + A5 * z ^ (-(1 / 3 : ℝ)) := by
  have h := (abs_lt.mp (lemma2_unconditional z hz)).2
  have hs := (S2_sandwich z (by linarith)).2
  have hC := Ctw_pos
  unfold M
  nlinarith

end
end LeanLab.RieselVaughan1983.Lemma3

#print axioms LeanLab.RieselVaughan1983.Lemma3.sieveCoeff_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma3.S_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma3.S2_one
#print axioms LeanLab.RieselVaughan1983.Lemma3.S2_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma3.S2_sandwich
#print axioms LeanLab.RieselVaughan1983.Lemma3.half_polynomial_lower
#print axioms LeanLab.RieselVaughan1983.Lemma3.polynomial_upper
