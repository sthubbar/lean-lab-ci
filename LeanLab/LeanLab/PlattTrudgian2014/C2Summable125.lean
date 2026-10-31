/-
AI wrote this Lean code. Binary Goldbach is open.
Platt and Trudgian arXiv 1404.5669v2 page 2, the weight k and the C2 series.
These are weight bounds. The sealed Mersenne series differs from the paper C2 series.
-/
import LeanLab.PlattTrudgian2014.PaperInputs

namespace LeanLab.PlattTrudgian2014

open Finset

/-- The odd squarefree weight satisfies a uniform square root bound. -/
theorem paperWeight_square_bound125 (d : ℕ) : paperWeight d ^ 2 * d ≤ 3 := by
  by_cases hd : Odd d ∧ Squarefree d
  · obtain ⟨ho, hs⟩ := hd
    have hcast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hs]
    have he : paperWeight d ^ 2 * d =
        ∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 2) ^ 2 := by
      rw [paperWeight, if_pos ⟨ho, hs⟩, hcast, ← prod_pow, ← prod_mul_distrib]
      apply prod_congr rfl
      intro p _
      rw [div_pow, one_pow]
      ring
    rw [he]
    have hb : (∏ p ∈ d.primeFactors, (p : ℝ) / ((p : ℝ) - 2) ^ 2) ≤
        ∏ p ∈ d.primeFactors, (if p = 3 then (3 : ℝ) else 1) := by
      apply prod_le_prod₀
      · intro p _
        exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      · intro p hp
        have hpr := Nat.prime_of_mem_primeFactors hp
        have hne : p ≠ 2 := by
          intro heq
          have hdiv := Nat.dvd_of_mem_primeFactors hp
          rw [heq] at hdiv
          have heven : Even d := even_iff_two_dvd.mpr hdiv
          exact (Nat.not_odd_iff_even.mpr heven) ho
        have hp3 : 3 ≤ p := by have := hpr.two_le; omega
        by_cases hp3eq : p = 3
        · subst p
          norm_num
        · simp only [if_neg hp3eq]
          have hp4 : (4 : ℝ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
          have hpos : 0 < ((p : ℝ) - 2) ^ 2 := sq_pos_of_pos (by linarith)
          rw [div_le_iff₀ hpos, one_mul]
          have hh := mul_nonneg (by linarith : 0 ≤ (p : ℝ) - 1)
            (by linarith : 0 ≤ (p : ℝ) - 4)
          nlinarith
    apply hb.trans
    by_cases h3 : 3 ∈ d.primeFactors
    · have hh : (∏ p ∈ d.primeFactors, if p = 3 then (3 : ℝ) else 1) = 3 := by
        rw [prod_eq_single 3]
        · simp
        · intro p _ hp
          simp [hp]
        · exact fun h => (h h3).elim
      rw [hh]
    · have hh : (∏ p ∈ d.primeFactors, if p = 3 then (3 : ℝ) else 1) = 1 := by
        apply prod_eq_one
        intro p hp
        have hne : p ≠ 3 := by intro heq; subst p; exact h3 hp
        simp [hne]
      rw [hh]
      norm_num
  · simp [paperWeight, hd]

/-- A convenient square root majorant for the paper's multiplicative weight. -/
theorem paperWeight_sqrt_bound125 (d : ℕ) (hd : 0 < d) :
    paperWeight d ≤ 2 / Real.sqrt d := by
  have hsq := paperWeight_square_bound125 d
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdp
  have he := Real.sq_sqrt hdp.le
  have hw := paperWeight_nonneg d
  have hp2 : (paperWeight d * Real.sqrt d) ^ 2 ≤ 3 := by
    rw [mul_pow, Real.sq_sqrt hdp.le]
    exact hsq
  have hprod : paperWeight d * Real.sqrt d ≤ 2 := by
    have hp : 0 ≤ paperWeight d * Real.sqrt d := mul_nonneg hw hs.le
    nlinarith [sq_nonneg (paperWeight d * Real.sqrt d - 2)]
  exact (le_div_iff₀ hs).mpr hprod

#print axioms paperWeight_sqrt_bound125
#print axioms paperWeight_square_bound125

end LeanLab.PlattTrudgian2014
