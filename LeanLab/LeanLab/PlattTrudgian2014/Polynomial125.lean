/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 page 177 display 5.2 and pages 184 to 185.
An explicit Taylor majorant replaces the degree 19 interpolation polynomial.
-/
import LeanLab.PlattTrudgian2014.Perron125

namespace LeanLab.PlattTrudgian2014

open Finset Polynomial

noncomputable def halfCosPoly125 (x : ℝ) : ℝ :=
  ∑ j : Fin 17, (halfCoeff125 j : ℝ) * Real.cos ((j : ℝ) * x)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- The finite Taylor polynomial has the listed exact cosine expansion. -/
theorem half_taylor_cos_identity125 (x : ℝ) :
    (∑ n ∈ range 17, (((halfParameter125 : ℝ) * Real.cos x) ^ n) / n.factorial) =
      ∑ j : Fin 17, (taylorCosCoeff125 16 halfParameter125 j : ℝ) *
        Real.cos ((j : ℝ) * x) := by
  have hp (y : ℝ) :
      (∑ n ∈ range 17, (halfParameter125 : ℝ) ^ n * y ^ n / n.factorial) =
        ∑ j : Fin 17, (taylorCosCoeff125 16 halfParameter125 j : ℝ) *
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval y := by
    have hT2 := Polynomial.Chebyshev.T_add_two ℝ (0 : ℤ)
    norm_num only [Int.reduceAdd] at hT2
    have hT3 := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ)
    norm_num only [Int.reduceAdd] at hT3
    have hT4 := Polynomial.Chebyshev.T_add_two ℝ (2 : ℤ)
    norm_num only [Int.reduceAdd] at hT4
    have hT5 := Polynomial.Chebyshev.T_add_two ℝ (3 : ℤ)
    norm_num only [Int.reduceAdd] at hT5
    have hT6 := Polynomial.Chebyshev.T_add_two ℝ (4 : ℤ)
    norm_num only [Int.reduceAdd] at hT6
    have hT7 := Polynomial.Chebyshev.T_add_two ℝ (5 : ℤ)
    norm_num only [Int.reduceAdd] at hT7
    have hT8 := Polynomial.Chebyshev.T_add_two ℝ (6 : ℤ)
    norm_num only [Int.reduceAdd] at hT8
    have hT9 := Polynomial.Chebyshev.T_add_two ℝ (7 : ℤ)
    norm_num only [Int.reduceAdd] at hT9
    have hT10 := Polynomial.Chebyshev.T_add_two ℝ (8 : ℤ)
    norm_num only [Int.reduceAdd] at hT10
    have hT11 := Polynomial.Chebyshev.T_add_two ℝ (9 : ℤ)
    norm_num only [Int.reduceAdd] at hT11
    have hT12 := Polynomial.Chebyshev.T_add_two ℝ (10 : ℤ)
    norm_num only [Int.reduceAdd] at hT12
    have hT13 := Polynomial.Chebyshev.T_add_two ℝ (11 : ℤ)
    norm_num only [Int.reduceAdd] at hT13
    have hT14 := Polynomial.Chebyshev.T_add_two ℝ (12 : ℤ)
    norm_num only [Int.reduceAdd] at hT14
    have hT15 := Polynomial.Chebyshev.T_add_two ℝ (13 : ℤ)
    norm_num only [Int.reduceAdd] at hT15
    have hT16 := Polynomial.Chebyshev.T_add_two ℝ (14 : ℤ)
    norm_num only [Int.reduceAdd] at hT16
    norm_num [Fin.sum_univ_succ, Finset.sum_range_succ, taylorCosCoeff125,
      halfParameter125, Nat.choose]
    simp only [hT16, hT15, hT14, hT13, hT12, hT11, hT10, hT9, hT8, hT7, hT6, hT5, hT4, hT3, hT2,
      Polynomial.Chebyshev.T_zero, Polynomial.Chebyshev.T_one, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
    ring
  simpa only [mul_pow, Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] using hp (Real.cos x)

/-- The library Taylor remainder is bounded by twice the first omitted term unit. -/
theorem half_taylor_remainder125 (x : ℝ) (hx : |x| ≤ (halfParameter125 : ℝ)) :
    Real.exp x ≤ (∑ n ∈ range 17, x ^ n / n.factorial) +
      2 * (halfParameter125 : ℝ) ^ 17 / (17).factorial := by
  have ht : (halfParameter125 : ℝ) ≤ 1 := by norm_num [halfParameter125]
  have h := Real.exp_bound (n := 17) (hx.trans ht) (by norm_num)
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 17
  have hh : |Real.exp x - ∑ n ∈ range 17, x ^ n / n.factorial| ≤
      2 * (halfParameter125 : ℝ) ^ 17 / (17).factorial := by
    apply h.trans
    have hcoef : (18 / ((17).factorial * (17 : ℝ)) : ℝ) ≤ 2 / (17).factorial := by norm_num
    have htp : 0 ≤ (halfParameter125 : ℝ) ^ 17 :=
      pow_nonneg (by exact_mod_cast half_parameter_box125.1.le) _
    have hb := mul_le_mul hp hcoef (by norm_num) htp
    convert hb using 1 <;> ring
  have := (abs_le.mp hh).2
  linarith

set_option maxHeartbeats 2000000 in
/-- A pointwise positive cosine majorant with the certified rational coefficients. -/
theorem half_exp_majorant125 (x : ℝ) :
    Real.exp ((halfParameter125 : ℝ) * Real.cos x) ≤ halfCosPoly125 x := by
  let d (j : Fin 17) : ℝ := (halfCoeff125 j : ℝ) - taylorCosCoeff125 16 halfParameter125 j
  have hdq : ∀ j : Fin 17, 0 ≤ halfCoeff125 j - taylorCosCoeff125 16 halfParameter125 j := by
    decide +kernel
  have hd : ∀ j : Fin 17, 0 ≤ d j := by
    intro j
    dsimp [d]
    exact_mod_cast hdq j
  have hbudget : 2 * (halfParameter125 : ℝ) ^ 17 / (17).factorial +
      (∑ j : Fin 17, if j = 0 then 0 else d j) ≤ d 0 := by
    dsimp [d]
    have hb := Rat.cast_mono (K := ℝ) half_rounding_budget125
    push_cast at hb
    simpa only [apply_ite, Rat.cast_zero, Rat.cast_sub] using hb
  have hsum : d 0 ≤ (∑ j : Fin 17, d j * Real.cos ((j : ℝ) * x)) +
      ∑ j : Fin 17, if j = 0 then 0 else d j := by
    calc
      d 0 = ∑ j : Fin 17, if j = 0 then d 0 else 0 := by simp
      _ ≤ ∑ j : Fin 17, (d j * Real.cos ((j : ℝ) * x) + if j = 0 then 0 else d j) := by
        apply sum_le_sum
        intro j _
        by_cases hj : j = 0
        · subst j
          simp
        · simp only [if_neg hj]
          have hh := Real.neg_one_le_cos ((j : ℝ) * x)
          have hm := mul_nonneg (hd j) (by linarith : 0 ≤ Real.cos ((j : ℝ) * x) + 1)
          nlinarith
      _ = _ := sum_add_distrib
  have ht : (0 : ℝ) ≤ halfParameter125 := by exact_mod_cast half_parameter_box125.1.le
  have habs : |(halfParameter125 : ℝ) * Real.cos x| ≤ (halfParameter125 : ℝ) := by
    rw [abs_mul, abs_of_nonneg ht]
    simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) ht
  have hm := half_taylor_remainder125 ((halfParameter125 : ℝ) * Real.cos x) habs
  rw [half_taylor_cos_identity125] at hm
  have he : halfCosPoly125 x =
      (∑ j : Fin 17, (taylorCosCoeff125 16 halfParameter125 j : ℝ) * Real.cos ((j : ℝ) * x)) +
      ∑ j : Fin 17, d j * Real.cos ((j : ℝ) * x) := by
    rw [halfCosPoly125, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    dsimp [d]
    ring
  rw [he]
  linarith

/-- The majorant is strictly positive on the whole real line. -/
theorem halfCosPoly_pos125 (x : ℝ) : 0 < halfCosPoly125 x :=
  (Real.exp_pos _).trans_le (half_exp_majorant125 x)

#print axioms half_exp_majorant125
#print axioms halfCosPoly_pos125

#print axioms half_taylor_cos_identity125
#print axioms half_taylor_remainder125

end LeanLab.PlattTrudgian2014
