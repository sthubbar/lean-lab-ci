/-
AI wrote this Lean code for CODEX task302.
P0037 Table 2 page 214 and Section 5.2 page 212.
These checks certify only the printed small complements.
The large printed primes and full coverage remain OPEN.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Pock

namespace LeanLab.DtRS1998.Task302.Printed

set_option maxRecDepth 100000

/-- The small complement of the printed final prime at W is prime.
P0037 Table 2 page 214, row 10^260. Large-prime primality remains OPEN. -/
theorem complement260 :
    10 ^ 260 + 999864924 - (10 ^ 260 + 999837181) = 27743 ∧
      Nat.Prime 27743 := by
  constructor
  · omega
  · apply Big.prime_of_pockK (known := []) (by simp)
      (c := (27743, 5, [(2, 1), (11, 1), (13, 1), (97, 1)]))
    decide +kernel

#print axioms complement260

/-- The small complement of the printed final prime at W is prime.
P0037 Table 2 page 214, row 10^270. Large-prime primality remains OPEN. -/
theorem complement270 :
    10 ^ 270 + 999697006 - (10 ^ 270 + 999503997) = 193009 ∧
      Nat.Prime 193009 := by
  constructor
  · omega
  · apply Big.prime_of_pockK (known := []) (by simp)
      (c := (193009, 7, [(2, 4), (3, 1), (4021, 1)]))
    decide +kernel

#print axioms complement270

/-- The small complement of the printed final prime at W is prime.
P0037 Table 2 page 214, row 10^280. Large-prime primality remains OPEN. -/
theorem complement280 :
    10 ^ 280 + 999837064 - (10 ^ 280 + 999714813) = 122251 ∧
      Nat.Prime 122251 := by
  constructor
  · omega
  · apply Big.prime_of_pockK (known := []) (by simp)
      (c := (122251, 3, [(2, 1), (3, 1), (5, 3), (163, 1)]))
    decide +kernel

#print axioms complement280

/-- The small complement of the printed final prime at W is prime.
P0037 Table 2 page 214, row 10^290. Large-prime primality remains OPEN. -/
theorem complement290 :
    10 ^ 290 + 999872646 - (10 ^ 290 + 999819517) = 53129 ∧
      Nat.Prime 53129 := by
  constructor
  · omega
  · apply Big.prime_of_pockK (known := []) (by simp)
      (c := (53129, 3, [(2, 3), (29, 1), (229, 1)]))
    decide +kernel

#print axioms complement290

/-- The small complement of the printed final prime at W is prime.
P0037 Table 2 page 214, row 10^300. Large-prime primality remains OPEN. -/
theorem complement300 :
    10 ^ 300 + 999821434 - (10 ^ 300 + 999692157) = 129277 ∧
      Nat.Prime 129277 := by
  constructor
  · omega
  · apply Big.prime_of_pockK (known := []) (by simp)
      (c := (129277, 2, [(2, 2), (3, 5), (7, 1), (19, 1)]))
    decide +kernel

#print axioms complement300

end LeanLab.DtRS1998.Task302.Printed
