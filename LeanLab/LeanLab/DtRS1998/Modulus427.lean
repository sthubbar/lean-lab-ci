/-
AI wrote this Lean code for CODEX task427.
Cohen and Lenstra 1987 pages 104 and 106, parameters for Algorithm 1.3.
The finite parameter checks do not establish the divisor congruences.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372aData
import LeanLab.DtRS1998.Decomp372bData
import LeanLab.DtRS1998.Decomp372cData

namespace LeanLab.DtRS1998.Modulus427

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Cohen and Lenstra 1987 page 104, display 1.1a.
The explicit product of prime powers for the chosen parameter t equal to 5040
has the value used as the modulus in the three new residue decompositions. -/
theorem modulus_product :
    2 * ([2 ^ 5, 3 ^ 3, 5 ^ 2, 7 ^ 2, 11, 13, 17, 19, 29, 31, 37,
      41, 43, 61, 71, 73, 113, 127, 181, 211, 241, 281, 337, 421, 631,
      1009, 2521] : List ℕ).prod =
      15321986788854443284662612735663611380010431225771200 := by
  decide +kernel

/-- Cohen and Lenstra 1987 page 106, step f and its periodicity conclusion.
Every first batch candidate is coprime to the modulus and its 5040th power
is one modulo that modulus. This asserts no prime divisor congruence. -/
theorem parameters90 :
    (Decomp372a.qs.take 64).all (fun q => decide
      (q.Coprime 15321986788854443284662612735663611380010431225771200 ∧
        Nat.powMod q 5040 15321986788854443284662612735663611380010431225771200 = 1)) = true := by
  decide +kernel

#print axioms parameters90

/-- Cohen and Lenstra 1987 page 106, step f and its periodicity conclusion.
Every first batch candidate is coprime to the modulus and its 5040th power
is one modulo that modulus. This asserts no prime divisor congruence. -/
theorem parameters95 :
    (Decomp372b.qs.take 64).all (fun q => decide
      (q.Coprime 15321986788854443284662612735663611380010431225771200 ∧
        Nat.powMod q 5040 15321986788854443284662612735663611380010431225771200 = 1)) = true := by
  decide +kernel

#print axioms parameters95

/-- Cohen and Lenstra 1987 page 106, step f and its periodicity conclusion.
Every first batch candidate is coprime to the modulus and its 5040th power
is one modulo that modulus. This asserts no prime divisor congruence. -/
theorem parameters100 :
    (Decomp372c.qs.take 64).all (fun q => decide
      (q.Coprime 15321986788854443284662612735663611380010431225771200 ∧
        Nat.powMod q 5040 15321986788854443284662612735663611380010431225771200 = 1)) = true := by
  decide +kernel

#print axioms parameters100

#print axioms modulus_product

end LeanLab.DtRS1998.Modulus427
