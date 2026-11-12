/-
AI wrote this Lean code for CODEX task445.
P0037 page 211 and Table 1 page 213, row 10^100.
Cohen and H. W. Lenstra 1984 page 306, Theorem 6.3 and proof.
The four primary divisor orbit components remain OPEN.
Their exact assembly uses no sorry of its own.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Modulus427
import LeanLab.DtRS1998.Projections445
import LeanLab.DtRS1998.PocklingtonB7Row100

namespace LeanLab.DtRS1998.Decomp445c

open Decomp372c

set_option maxRecDepth 100000

/-- LEAF. P0037 page 211, finite primality phase, and Table 1 page 213.
Cohen and H. W. Lenstra 1984 page 306, proof of Theorem 6.3,
conditions 6.4 and 6.5 and the choice of the common exponent.
This derived finite subclaim retains only the 2 primary projection.
It asks for its own witness below 16, not a shared full orbit witness.
The missing character and p-adic certification remains OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row100.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem component2 :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 16 ∧
        p ^ 315 % 15321986788854443284662612735663611380010431225771200 = q ^ (315 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hq' := PocklingtonB7Row100.qs_prime q (List.mem_of_mem_take hq)
  obtain rfl : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
  exact ⟨1, by decide, by rw [Nat.mul_one]⟩


/-- LEAF. P0037 page 211, finite primality phase, and Table 1 page 213.
Cohen and H. W. Lenstra 1984 page 306, proof of Theorem 6.3,
conditions 6.4 and 6.5 and the choice of the common exponent.
This derived finite subclaim retains only the 3 primary projection.
It asks for its own witness below 9, not a shared full orbit witness.
The missing character and p-adic certification remains OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row100.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem component3 :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 = q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hq' := PocklingtonB7Row100.qs_prime q (List.mem_of_mem_take hq)
  obtain rfl : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
  exact ⟨1, by decide, by rw [Nat.mul_one]⟩


/-- LEAF. P0037 page 211, finite primality phase, and Table 1 page 213.
Cohen and H. W. Lenstra 1984 page 306, proof of Theorem 6.3,
conditions 6.4 and 6.5 and the choice of the common exponent.
This derived finite subclaim retains only the 5 primary projection.
It asks for its own witness below 5, not a shared full orbit witness.
The missing character and p-adic certification remains OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row100.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem component5 :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 5 ∧
        p ^ 1008 % 15321986788854443284662612735663611380010431225771200 = q ^ (1008 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hq' := PocklingtonB7Row100.qs_prime q (List.mem_of_mem_take hq)
  obtain rfl : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
  exact ⟨1, by decide, by rw [Nat.mul_one]⟩


/-- LEAF. P0037 page 211, finite primality phase, and Table 1 page 213.
Cohen and H. W. Lenstra 1984 page 306, proof of Theorem 6.3,
conditions 6.4 and 6.5 and the choice of the common exponent.
This derived finite subclaim retains only the 7 primary projection.
It asks for its own witness below 7, not a shared full orbit witness.
The missing character and p-adic certification remains OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row100.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem component7 :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hq' := PocklingtonB7Row100.qs_prime q (List.mem_of_mem_take hq)
  obtain rfl : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
  exact ⟨1, by decide, by rw [Nat.mul_one]⟩


/-- P0037 page 213, a concrete nonempty premise for every new leaf.
The first candidate belongs to the batch, is not one, and has its explicit
least prime factor as a prime divisor. No candidate primality is assumed. -/
theorem leaf_premises :
    (10 ^ 100 - 68969) ∈ qs.take 64 ∧
      (10 ^ 100 - 68969).minFac.Prime ∧
      (10 ^ 100 - 68969).minFac ∣ (10 ^ 100 - 68969) := by
  exact ⟨by decide +kernel, Nat.minFac_prime (by decide +kernel), Nat.minFac_dvd _⟩

/-- P0037 page 211 with Cohen and H. W. Lenstra 1984 page 306.
CONDITIONAL ON the four OPEN primary component leaves.
This is the exact existing Decomp427c.divisor_residues statement.
No old divisor congruence or old prime leaf is used. -/
theorem divisor_residues :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 5040 ∧
        p % 15321986788854443284662612735663611380010431225771200 = q ^ i % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hperiod := of_decide_eq_true (List.all_eq_true.mp Modulus427.parameters100 q hq)
  exact Projections445.residue_orbit_of_primary_components hperiod.2
    (component2 q hq p hp hd) (component3 q hq p hp hd)
    (component5 q hq p hp hd) (component7 q hq p hp hd)

#print axioms component2
#print axioms component3
#print axioms component5
#print axioms component7
#print axioms leaf_premises
#print axioms divisor_residues

end LeanLab.DtRS1998.Decomp445c
