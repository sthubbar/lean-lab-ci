import LeanLab.LanguascoPintzZaccagnini2007.GrowingWeighted481
import LeanLab.LanguascoPintzZaccagnini2007.Instances383
import LeanLab.LanguascoPintzZaccagnini2007.Singular383

/-!
A nonempty exceptional tuple example for P0045 page 6, displays 9 to 14.
The modulus is seven and the positive residual is fourteen.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter

/-- P0045 page 6, qualitative radical growth remark and displays 9 to 14.
Square root growth is admissible. At X and N equal to sixteen the modulus seven
and the exponent one give a genuine exceptional tuple with positive singular series. -/
theorem growing_exception_instance481 :
    Tendsto (fun X : ℕ => Real.sqrt (X : ℝ)) atTop atTop ∧
      ({7} : Finset ℕ).card ≤ 1 ∧
      Real.sqrt 16 ≤ (oddRad131 7 : ℝ) ∧
      16 ∈ evenJ131 16 ∧
      (fun _ : Fin 1 => (1 : ℕ)) ∈ tuples131 1 16 ∧
      ¬ Nonexceptional131 1 {7} (16 - tuplePower131 (fun _ : Fin 1 => (1 : ℕ))) ∧
      0 < Sing (16 - tuplePower131 (fun _ : Fin 1 => (1 : ℕ))) := by
  have hrad : oddRad131 7 = 7 := by
    norm_num [oddRad131, prime_7.primeFactors, Finset.filter_singleton]
  refine ⟨Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop,
    by norm_num, by rw [hrad]; norm_num,
    tuple_instance383.2.2, tuple_instance383.1, ?_, ?_⟩
  · rw [tuple_instance383.2.1]
    norm_num [Nonexceptional131]
  · rw [tuple_instance383.2.1]
    exact (singular_pos_iff_even383 (by norm_num : (16 - 2 : ℕ) ≠ 0)).2 (by decide)

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.growing_exception_instance481
