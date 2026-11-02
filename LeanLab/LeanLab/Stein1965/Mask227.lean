/-
AI wrote this Lean code for CODEX task227. Goldbach is open.
Covered intervals for equation 2.2 on page 427.
-/
import LeanLab.SteinStein1965.Replay

namespace LeanLab.Stein1965.Mask227
open LeanLab.SteinStein1965

/-- The even-position mask as a geometric sum. -/
theorem gapMask_geometric (n : ℕ) : 3 * gapMask n + 1 = 4 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hor : (gapMask n <<< 2) ||| 1 = 4 * gapMask n + 1 := by
      rw [Nat.shiftLeft_eq]
      simpa [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt (i := 2) (b := 1) (by decide) (gapMask n)).symm
    rw [gapMask, hor, pow_succ]
    omega

/-- Closed form for the recursive even-position mask. -/
theorem gapMask_closed (n : ℕ) : gapMask n = (4 ^ n - 1) / 3 := by
  have h := gapMask_geometric n
  omega

/-- Closed-form gap test with no recursion over the interval length. -/
def gapCheckClosed (s : BitState) (lo n : ℕ) : Bool :=
  let mask := (4 ^ n - 1) / 3
  ((s.sums >>> lo) &&& mask) == mask

theorem gapCheckClosed_eq (s : BitState) (lo n : ℕ) :
    gapCheckClosed s lo n = gapCheck s lo n := by
  simp only [gapCheckClosed, gapCheck, gapMask_closed]

end LeanLab.Stein1965.Mask227
#print axioms LeanLab.Stein1965.Mask227.gapMask_geometric
#print axioms LeanLab.Stein1965.Mask227.gapMask_closed
#print axioms LeanLab.Stein1965.Mask227.gapCheckClosed_eq
