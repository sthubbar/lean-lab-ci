/-
P0083, pages 488 and 489, equations 34 and 37. The finite weighted counting error.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Counting
import LeanLab.Perelli1996.Section3
import LeanLab.Perelli1996.RootCRT

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial

/-- The factor f removes the even moduli before applying CRT at two. -/
theorem weighted_root_count_two (F : ℤ[X]) (d : ℕ) :
    arithmeticFactor d * ((Roots.rootResidues F (2 * d)).card : ℝ) =
      ((Roots.rootResidues F 2).card : ℝ) * arithmeticFactor d * (Roots.rootResidues F d).card := by
  by_cases hd : 2 ∣ d
  · simp [arithmeticFactor_even hd]
  · have hdpos : 0 < d := by
      by_contra hz
      have hd0 : d = 0 := by omega
      subst d
      exact hd (dvd_zero 2)
    have hcop : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr hd
    rw [Roots.root_count_mul F 2 d (by norm_num) hdpos hcop]
    push_cast
    ring

/-- Explicit finite counting error before extending the coefficient sum to infinity. -/
theorem finite_weighted_count_error (F : ℤ[X]) (D : ℕ) {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    |(∑ d ∈ Icc 1 D, arithmeticFactor d * ((Counting.rootWindow F (2 * d) x H).card : ℝ)) -
      ((Roots.rootResidues F 2).card : ℝ) * H / 2 *
        (∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d)| ≤
    2 * ((Roots.rootResidues F 2).card : ℝ) *
      ∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) := by
  let ρ : ℝ := (Roots.rootResidues F 2).card
  have hmain (d : ℕ) (hd : d ∈ Icc 1 D) :
      arithmeticFactor d * (((Roots.rootResidues F (2 * d)).card : ℝ) / (2 * d : ℕ) * H) =
        ρ * H / 2 * (arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d) := by
    have hd0 : (d : ℝ) ≠ 0 := by
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      exact_mod_cast Nat.ne_of_gt hdpos
    have hw := weighted_root_count_two F d
    calc arithmeticFactor d * (((Roots.rootResidues F (2 * d)).card : ℝ) / (2 * d : ℕ) * H)
        = (arithmeticFactor d * ((Roots.rootResidues F (2 * d)).card : ℝ)) * H / (2 * (d : ℝ)) := by
          push_cast
          ring
      _ = (((Roots.rootResidues F 2).card : ℝ) * arithmeticFactor d * (Roots.rootResidues F d).card) * H /
          (2 * (d : ℝ)) := by rw [hw]
      _ = _ := by dsimp [ρ]; field_simp
  have hterm (d : ℕ) (hd : d ∈ Icc 1 D) :
      |arithmeticFactor d * (((Counting.rootWindow F (2 * d) x H).card : ℝ) -
        ((Roots.rootResidues F (2 * d)).card : ℝ) / (2 * d : ℕ) * H)| ≤
      2 * ρ * (arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (arithmeticFactor_nonneg d)]
    have hdpos : 0 < 2 * d := by have := (Finset.mem_Icc.mp hd).1; omega
    have hc := Counting.root_window_error F (2 * d) hdpos hx hH
    have hmul := mul_le_mul_of_nonneg_left hc (arithmeticFactor_nonneg d)
    refine hmul.trans_eq ?_
    have hw := weighted_root_count_two F d
    dsimp [ρ]
    nlinarith [hw]
  have hsum : (∑ d ∈ Icc 1 D, arithmeticFactor d *
      (((Counting.rootWindow F (2 * d) x H).card : ℝ) -
        ((Roots.rootResidues F (2 * d)).card : ℝ) / (2 * d : ℕ) * H)) =
      (∑ d ∈ Icc 1 D, arithmeticFactor d * ((Counting.rootWindow F (2 * d) x H).card : ℝ)) -
        ρ * H / 2 * (∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl hmain
  change |(∑ d ∈ Icc 1 D, arithmeticFactor d * ((Counting.rootWindow F (2 * d) x H).card : ℝ)) -
    ρ * H / 2 * (∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d)| ≤
    2 * ρ * ∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ)
  rw [← hsum]
  calc |∑ d ∈ Icc 1 D, arithmeticFactor d * (((Counting.rootWindow F (2 * d) x H).card : ℝ) -
        ((Roots.rootResidues F (2 * d)).card : ℝ) / (2 * d : ℕ) * H)|
      ≤ ∑ d ∈ Icc 1 D, |arithmeticFactor d * (((Counting.rootWindow F (2 * d) x H).card : ℝ) -
        ((Roots.rootResidues F (2 * d)).card : ℝ) / (2 * d : ℕ) * H)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 D, 2 * ρ * (arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.mul_sum]

end LeanLab.Perelli1996.Section3
