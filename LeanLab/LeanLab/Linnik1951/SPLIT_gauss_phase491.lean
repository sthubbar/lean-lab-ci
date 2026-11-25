/-
Split of the HARD leaf gauss_phase_product_le491 of SPLIT_mixed_pair_repair491, P0093 page 160
equation 5.5, along the argument its doc comment gives: pass to the primitive character
inducing the character, of conductor c.
* the conjugate Gauss coefficient has modulus at most the square root of c, HARD;
* the residue phase at n has modulus at most the square root of c times the cofactor q over c,
  that is at most q over the square root of c, HARD.
The product bound follows by multiplying the two, proved in SPLIT_mixed_pair_repair491.
Both leaves were checked in floating point for every character mod q, every q up to 60 and
every residue n mod q.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mixed_pair_bound491

namespace LeanLab.Linnik1951

open Finset

/-- LEAF: P0093 page 160, equation 5.5, the Gauss coefficient through the primitive character.
Class: HARD. For a character mod a positive q with conductor c, the conjugate Gauss coefficient
has modulus at most the square root of c: the Gauss sum of the character is the Moebius value
of the cofactor times the primitive character at the cofactor times the primitive Gauss sum,
whose modulus is the square root of c. -/
theorem gauss_coefficient_le_sqrt_conductor491 (q : ℕ) (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) :
    ‖conjugateGauss491 q χ‖ ≤ Real.sqrt (χ.conductor : ℝ) := by
  sorry

/-- LEAF: P0093 page 160, equation 5.5, the residue phase through the primitive character.
Class: HARD. For a character mod a positive q with conductor c and every integer n, the residue
phase at n times the square root of c is at most q: the residue phase is at most the square
root of c times the Ramanujan factor of the cofactor q over c, whose size is at most the
cofactor. -/
theorem residue_phase_mul_sqrt_conductor_le491 (q : ℕ) (hq : 1 ≤ q) (n : ℤ)
    (χ : DirichletCharacter ℂ q) :
    ‖residuePhase555 q n χ‖ * Real.sqrt (χ.conductor : ℝ) ≤ (q : ℝ) := by
  sorry

end LeanLab.Linnik1951
