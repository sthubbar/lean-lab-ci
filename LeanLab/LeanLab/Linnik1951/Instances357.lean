/-
P0093 pages 154 and 162. Concrete instances for the supplied statements.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp357m

namespace LeanLab.Linnik1951

/-- P0093 page 162 definition before equation 7.4. The fiber at five is
nonempty and has exactly the representation three plus two to the first. -/
theorem prime_power_five357 : primePowerCount111 5 = 1 := by
  classical
  have hs : (Finset.univ.filter fun t : Fin 6 × Fin 6 =>
      t.1.val.Prime ∧ 1 ≤ t.2.val ∧ 5 = t.1.val + 2 ^ t.2.val) =
      {(⟨3, by omega⟩, ⟨1, by omega⟩)} := by
    ext t
    rcases t with ⟨p, x⟩
    fin_cases p <;> fin_cases x <;> norm_num
  unfold primePowerCount111
  rw [hs]
  simp

/-- P0093 page 154 equation 2.1. The representation count has a positive
instance at eight from the two primes three and the positive power two. -/
theorem representation_eight357 : 0 < representationCount111 1 8 := by
  apply count_pos_of_representation111
  refine ⟨3, 3, Nat.prime_three, Nat.prime_three, fun _ => 1, by simp, ?_⟩
  norm_num

/-- P0093 page 168 equation 10.6. At cutoff one the finite singular
series contains only its normalized modulus one term. -/
theorem truncated_singular_one357 (n : ℕ) : truncatedSingular357 1 n = 1 := by
  simp [truncatedSingular357, LeanLab.Perelli1996.Ramanujan103.ramanujanSum,
    LeanLab.Perelli1996.Kernel.e]

/-- P0093 page 162 equation 7.4. A single phase at negative five has
coefficient one there and zero at the positive frequency five. -/
theorem phase_five357 :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => Complex.exp ((-(2 * Real.pi * α * (5 : ℕ)) : ℝ) * Complex.I)) (-5) = 1 ∧
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun α => Complex.exp ((-(2 * Real.pi * α * (5 : ℕ)) : ℝ) * Complex.I)) 5 = 0 := by
  constructor <;> rw [negative_phase_coefficient357] <;> norm_num

end LeanLab.Linnik1951
