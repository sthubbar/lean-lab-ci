import Mathlib

/-!
P0012 page 30 display 44. Consecutive block partitions for the numerical certificate.
The rational partition theorem moves here verbatim from Decomp1530c.
The integer specialization supports smaller direct kernel checks.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.HeathBrownPuchta.Decomp1530c
open Finset

/-- Partition a rational finite sum into equal consecutive blocks. -/
theorem sum_blocks177 (f : ℕ → ℚ) (n m : ℕ) :
    (∑ r ∈ range (n*m), f r) = ∑ b ∈ range n, ∑ r ∈ range m, f (m*b+r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, sum_range_add, sum_range_succ, ih]
    congr 1
    apply sum_congr rfl
    intro r hr
    congr 1
    ring


/-- Integer specialization into sixteen consecutive blocks of eight. -/
lemma sum128_split215 (f : ℕ → ℤ) :
    (∑ r ∈ range 128, f r) = ∑ b ∈ range 16, ∑ r ∈ range 8, f (8 * b + r) := by
  exact_mod_cast sum_blocks177 (fun r => (f r : ℚ)) 16 8

end LeanLab.HeathBrownPuchta.Decomp1530c
