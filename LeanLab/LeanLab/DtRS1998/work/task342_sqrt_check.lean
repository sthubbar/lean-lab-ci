import Mathlib
#check Nat.sqrt
#check Nat.sqrt_le
#check Nat.sqrt_le_iff
#check Nat.le_sqrt
#check Nat.lt_sqrt
#check Nat.sqrt_lt
#check Nat.sqrt_lt_iff
#check Nat.sqrt_sq
#check Nat.sq_sqrt
#check Nat.sqrt_eq_iff
example (L p : ℕ) (hpL : p * p < L) : p ≤ Nat.sqrt L := by
  omega
