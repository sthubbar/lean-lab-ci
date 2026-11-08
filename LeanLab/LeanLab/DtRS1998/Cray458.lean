/-
AI wrote this Lean code for CODEX task458.
P0037 Section 4.1 printed page 209, the OR of shifted ODD arrays.
These are exact bitmap identities, with no assertion of complete range coverage.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Shift

namespace LeanLab.DtRS1998.Cray458

/-- P0037 Section 4.1 page 209, successive OR operations.
Splitting the shift list splits its bitmap into an OR of two bitmaps. -/
theorem gmR_append (P : ℕ) (S T : List ℕ) :
    gmR P (S ++ T) = gmR P S ||| gmR P T := by
  induction S with
  | nil => simp [gmR]
  | cons s S ih => simp [gmR, ih, Nat.or_assoc]

/-- P0037 Section 4.1 page 209, the bit meaning of the shifted array.
A bit is set exactly when at least one listed shift reaches a set source bit. -/
theorem testBit_gmR_iff (P : ℕ) (S : List ℕ) (j : ℕ) :
    (gmR P S).testBit j = true ↔ ∃ s ∈ S, P.testBit (j + s) = true := by
  induction S with
  | nil => simp [gmR]
  | cons s S ih =>
    simp [gmR, Nat.testBit_or, Nat.testBit_shiftRight, ih, Nat.add_comm]

/-- P0037 Section 4.1 page 209, checking that all requested bits are one.
The exact mask equality is equivalent to a witness shift for every requested bit. -/
theorem mask_covered_iff (P M : ℕ) (S : List ℕ) :
    M &&& gmR P S = M ↔
      ∀ j : ℕ, M.testBit j = true → ∃ s ∈ S, P.testBit (j + s) = true := by
  constructor
  · intro h j hj
    apply (testBit_gmR_iff P S j).mp
    have hbit := congrArg (fun n : ℕ => n.testBit j) h
    simpa [Nat.testBit_and, hj] using hbit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    cases hj : M.testBit j with
    | false => simp
    | true => simp [(testBit_gmR_iff P S j).mpr (h j hj)]

/-- P0037 Section 4.1 page 209, supporting nonempty bitmap instance.
Source bits one and three, shifted by zero and one, cover four target bits. -/
theorem bitmap_instance : gmR 10 [0, 1] = 15 := by
  decide

/-- P0037 Section 4.1 page 209, supporting incomplete bitmap instance.
Keeping only the zero shift does not cover the four target bits. -/
theorem bitmap_prefix_incomplete : ¬ (15 &&& gmR 10 [0] = 15) := by
  decide

#print axioms gmR_append
#print axioms testBit_gmR_iff
#print axioms mask_covered_iff
#print axioms bitmap_instance
#print axioms bitmap_prefix_incomplete

end LeanLab.DtRS1998.Cray458
