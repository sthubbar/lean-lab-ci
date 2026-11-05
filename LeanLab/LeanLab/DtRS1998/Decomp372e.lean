/-
AI wrote this Lean code for CODEX task372.
P0037 Section 3 page 208, the paragraph on admissible residue classes.
These exact finite counts do not assume statistical independence.
They do not prove a Goldbach coverage estimate.
Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.DtRS1998.Decomp372e

/-- P0037 Section 3 page 208, the denominator r minus one.
There are r minus one nonzero residues modulo a positive modulus r.
This finite count also holds when r is composite. -/
theorem nonzero_residue_card (r : ℕ) [NeZero r] :
    ((Finset.univ : Finset (ZMod r)).filter (fun x => x ≠ 0)).card = r - 1 := by
  simp [Finset.filter_ne', ZMod.card]

/-- P0037 Section 3 page 208, the numerator r minus two.
For a nonzero target residue a, precisely r minus two residue classes x
make both x and a minus x nonzero. This is exact finite arithmetic.
The paper applies the count to odd primes r. -/
theorem admissible_residue_card (r : ℕ) [NeZero r] (a : ZMod r) (ha : a ≠ 0) :
    ((Finset.univ : Finset (ZMod r)).filter
      (fun x => x ≠ 0 ∧ a - x ≠ 0)).card = r - 2 := by
  have hset : ((Finset.univ : Finset (ZMod r)).filter
      (fun x => x ≠ 0 ∧ a - x ≠ 0)) = ({0, a} : Finset (ZMod r))ᶜ := by
    ext x
    simp [sub_ne_zero, ne_comm, and_comm]
  rw [hset, Finset.card_compl, ZMod.card, Finset.card_pair ha.symm]

/-- P0037 Section 3 page 208. For a prime modulus, nonzero residues
are exactly the units that describe the coprime classes in the paper. -/
theorem prime_unit_residue_card (r : ℕ) [Fact r.Prime] :
    ((Finset.univ : Finset (ZMod r)).filter IsUnit).card = r - 1 := by
  simpa only [isUnit_iff_ne_zero] using nonzero_residue_card r

/-- P0037 Section 3 page 208. For a prime modulus and nonzero target a,
there are r minus two classes with both summands coprime to r. -/
theorem admissible_prime_unit_card (r : ℕ) [Fact r.Prime]
    (a : ZMod r) (ha : a ≠ 0) :
    ((Finset.univ : Finset (ZMod r)).filter
      (fun x => IsUnit x ∧ IsUnit (a - x))).card = r - 2 := by
  simpa only [isUnit_iff_ne_zero] using admissible_residue_card r a ha

/-- P0037 Section 3 page 208, concrete cases r equals 3 and 5.
Target residue one is nonzero in both cases. -/
theorem residue_instances :
    ((Finset.univ : Finset (ZMod 3)).filter
      (fun x => x ≠ 0 ∧ 1 - x ≠ 0)).card = 1 ∧
    ((Finset.univ : Finset (ZMod 5)).filter
      (fun x => x ≠ 0 ∧ 1 - x ≠ 0)).card = 3 := by
  constructor
  · exact admissible_residue_card 3 1 (by decide)
  · exact admissible_residue_card 5 1 (by decide)

#print axioms nonzero_residue_card
#print axioms admissible_residue_card
#print axioms prime_unit_residue_card
#print axioms admissible_prime_unit_card
#print axioms residue_instances

end LeanLab.DtRS1998.Decomp372e
