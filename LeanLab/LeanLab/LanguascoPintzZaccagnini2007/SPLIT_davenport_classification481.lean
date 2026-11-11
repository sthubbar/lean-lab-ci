import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
The real primitive conductor classification is cut here into the two numerical
ingredients it uses: the conductor divides eight times its odd radical, and the
conductor is never exactly twice its odd radical. The step from those two facts to
the three listed conductors is arithmetic and is discharged in the assembly below.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-- The odd radical of a modulus is positive. -/
private theorem oddRad131_pos481 (r : ℕ) : 0 < oddRad131 r := by
  unfold oddRad131
  rcases Finset.eq_empty_or_nonempty (r.primeFactors.filter (fun p => 2 < p)) with h | ⟨p, hp⟩
  · rw [h, Finset.prod_empty]
    exact Nat.zero_lt_one
  · exact Finset.prod_pos
      (fun q hq => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos)

/-- The odd radical of a modulus divides that modulus. -/
private theorem oddRad131_dvd481 (r : ℕ) : oddRad131 r ∣ r := by
  unfold oddRad131
  refine Finset.prod_primes_dvd r (fun p hp => ?_) (fun p hp => ?_)
  · exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
  · exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- LEAF. The power of two carried by the conductor of a real primitive character is at
most eight: the conductor divides eight times its odd radical. -/
theorem real_primitive_dvd_eight_odd_rad481 {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    r ∣ 8 * oddRad131 r := by
  sorry

/-- LEAF. A real primitive character never has conductor exactly twice its odd radical:
the power of two outside the odd radical is not the first power. -/
theorem real_primitive_ne_two_odd_rad481 {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (hreal : ∀ a, (χ a).im = 0) :
    r ≠ 2 * oddRad131 r := by
  sorry

/-- The conductor of a real primitive character is its odd radical, or four or eight times
that radical, obtained by writing the conductor as the odd radical times a divisor of eight
and excluding the factor two. -/
theorem davenport_classification481_split : RealPrimitiveStatement481 := by
  intro r hr χ hprim hreal
  obtain ⟨c, hc⟩ := oddRad131_dvd481 r
  have hdv : oddRad131 r * c ∣ oddRad131 r * 8 := by
    rw [Nat.mul_comm (oddRad131 r) 8, ← hc]
    exact real_primitive_dvd_eight_odd_rad481 hr χ hprim hreal
  have hc8 : c ∣ 8 := Nat.dvd_of_mul_dvd_mul_left (oddRad131_pos481 r) hdv
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hc8 (by norm_num)
  have hcle : c ≤ 8 := Nat.le_of_dvd (by norm_num) hc8
  interval_cases c
  · left; omega
  · exact absurd (by omega : r = 2 * oddRad131 r)
      (real_primitive_ne_two_odd_rad481 hr χ hprim hreal)
  · norm_num at hc8
  · right; left; omega
  · norm_num at hc8
  · norm_num at hc8
  · norm_num at hc8
  · right; right; omega

end

end LeanLab.LPZ2007
