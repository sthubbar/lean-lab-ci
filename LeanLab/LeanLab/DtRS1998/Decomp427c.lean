/-
AI wrote this Lean code for CODEX task427.
P0037 Section 5.1 page 211 and Table 1 page 213, row 10^100.
Cohen and Lenstra 1987 page 108, final trial division.
The prime divisor congruences remain OPEN.
The finite trial checks assert no candidate primality by themselves.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372cData
import LeanLab.DtRS1998.Primality427
import LeanLab.DtRS1998.PocklingtonB7Row100

namespace LeanLab.DtRS1998.Decomp427c

open Decomp372c

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- LEAF. P0037 page 211, finite primality phase, with Cohen and Lenstra
1987 page 108, final trial division and its preceding divisor conclusion.
Every prime divisor of a first batch candidate lies in the power residue orbit.
This asserts only the congruence ingredient, not primality or accepted trials.
The cyclotomic justification for these concrete congruences is OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row100.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem divisor_residues :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 5040 ∧
        p % 15321986788854443284662612735663611380010431225771200 = q ^ i % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hq' := PocklingtonB7Row100.qs_prime q (List.mem_of_mem_take hq)
  obtain rfl : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
  exact ⟨1, by decide, by rw [pow_one]⟩

/-- LEAF. Cohen and Lenstra 1987 page 108, the square modulus condition.
P0037 page 213, row 10^100. Every first batch candidate is at least two
and is smaller than the square of the chosen trial modulus. -/
theorem candidate_bounds :
    ∀ q ∈ qs.take 64, 2 ≤ q ∧ q < 15321986788854443284662612735663611380010431225771200 ^ 2 := by
  decide +kernel

/-- P0037 page 213 and Cohen and Lenstra 1987 page 108.
The first candidate gives an explicit inhabited batch premise. -/
theorem batch_member : (10 ^ 100 - 68969) ∈ qs.take 64 := by
  decide +kernel

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 1 through 4 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials0 :
    ([10 ^ 100 - 68969, 10 ^ 100 - 68811, 10 ^ 100 - 68603, 10 ^ 100 - 68501] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials0

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 5 through 8 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials1 :
    ([10 ^ 100 - 68111, 10 ^ 100 - 67887, 10 ^ 100 - 67773, 10 ^ 100 - 67601] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials1

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 9 through 12 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials2 :
    ([10 ^ 100 - 67397, 10 ^ 100 - 66801, 10 ^ 100 - 66533, 10 ^ 100 - 66387] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials2

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 13 through 16 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials3 :
    ([10 ^ 100 - 66377, 10 ^ 100 - 66071, 10 ^ 100 - 65823, 10 ^ 100 - 65819] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials3

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 17 through 20 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials4 :
    ([10 ^ 100 - 65457, 10 ^ 100 - 65151, 10 ^ 100 - 65039, 10 ^ 100 - 65031] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials4

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 21 through 24 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials5 :
    ([10 ^ 100 - 64233, 10 ^ 100 - 63993, 10 ^ 100 - 63083, 10 ^ 100 - 62817] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials5

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 25 through 28 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials6 :
    ([10 ^ 100 - 62643, 10 ^ 100 - 62111, 10 ^ 100 - 62009, 10 ^ 100 - 61979] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials6

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 29 through 32 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials7 :
    ([10 ^ 100 - 61959, 10 ^ 100 - 61673, 10 ^ 100 - 61451, 10 ^ 100 - 61407] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials7

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 33 through 36 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials8 :
    ([10 ^ 100 - 61343, 10 ^ 100 - 61269, 10 ^ 100 - 60903, 10 ^ 100 - 60873] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials8

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 37 through 40 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials9 :
    ([10 ^ 100 - 60863, 10 ^ 100 - 60587, 10 ^ 100 - 60551, 10 ^ 100 - 60051] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials9

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 41 through 44 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials10 :
    ([10 ^ 100 - 59871, 10 ^ 100 - 59559, 10 ^ 100 - 59481, 10 ^ 100 - 59393] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials10

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 45 through 48 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials11 :
    ([10 ^ 100 - 59337, 10 ^ 100 - 58863, 10 ^ 100 - 58319, 10 ^ 100 - 57933] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials11

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 49 through 52 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials12 :
    ([10 ^ 100 - 57497, 10 ^ 100 - 56741, 10 ^ 100 - 56237, 10 ^ 100 - 56141] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials12

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 53 through 56 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials13 :
    ([10 ^ 100 - 55593, 10 ^ 100 - 55491, 10 ^ 100 - 55401, 10 ^ 100 - 55239] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials13

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 57 through 60 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials14 :
    ([10 ^ 100 - 54567, 10 ^ 100 - 54173, 10 ^ 100 - 54167, 10 ^ 100 - 53853] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials14

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 61 through 64 of row 10^100.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials15 :
    ([10 ^ 100 - 53751, 10 ^ 100 - 53159, 10 ^ 100 - 53039, 10 ^ 100 - 52929] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials15

/-- LEAF. Cohen and Lenstra 1987 page 108, step l1 and l3.
All final trial divisions pass for this first batch. This is independent
of the OPEN prime divisor congruences and asserts no primality. -/
theorem trial_checks :
    (qs.take 64).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  change (([10 ^ 100 - 68969, 10 ^ 100 - 68811, 10 ^ 100 - 68603, 10 ^ 100 - 68501] ++ [10 ^ 100 - 68111, 10 ^ 100 - 67887, 10 ^ 100 - 67773, 10 ^ 100 - 67601] ++ [10 ^ 100 - 67397, 10 ^ 100 - 66801, 10 ^ 100 - 66533, 10 ^ 100 - 66387] ++ [10 ^ 100 - 66377, 10 ^ 100 - 66071, 10 ^ 100 - 65823, 10 ^ 100 - 65819] ++ [10 ^ 100 - 65457, 10 ^ 100 - 65151, 10 ^ 100 - 65039, 10 ^ 100 - 65031] ++ [10 ^ 100 - 64233, 10 ^ 100 - 63993, 10 ^ 100 - 63083, 10 ^ 100 - 62817] ++ [10 ^ 100 - 62643, 10 ^ 100 - 62111, 10 ^ 100 - 62009, 10 ^ 100 - 61979] ++ [10 ^ 100 - 61959, 10 ^ 100 - 61673, 10 ^ 100 - 61451, 10 ^ 100 - 61407] ++ [10 ^ 100 - 61343, 10 ^ 100 - 61269, 10 ^ 100 - 60903, 10 ^ 100 - 60873] ++ [10 ^ 100 - 60863, 10 ^ 100 - 60587, 10 ^ 100 - 60551, 10 ^ 100 - 60051] ++ [10 ^ 100 - 59871, 10 ^ 100 - 59559, 10 ^ 100 - 59481, 10 ^ 100 - 59393] ++ [10 ^ 100 - 59337, 10 ^ 100 - 58863, 10 ^ 100 - 58319, 10 ^ 100 - 57933] ++ [10 ^ 100 - 57497, 10 ^ 100 - 56741, 10 ^ 100 - 56237, 10 ^ 100 - 56141] ++ [10 ^ 100 - 55593, 10 ^ 100 - 55491, 10 ^ 100 - 55401, 10 ^ 100 - 55239] ++ [10 ^ 100 - 54567, 10 ^ 100 - 54173, 10 ^ 100 - 54167, 10 ^ 100 - 53853] ++ [10 ^ 100 - 53751, 10 ^ 100 - 53159, 10 ^ 100 - 53039, 10 ^ 100 - 52929] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true)
  simp only [List.all_append, trials0, trials1, trials2, trials3, trials4, trials5, trials6, trials7, trials8, trials9, trials10, trials11, trials12, trials13, trials14, trials15, Bool.and_self]

/-- P0037 page 211 with Cohen and Lenstra 1987 page 108.
CONDITIONAL ON the OPEN divisor_residues leaf.
This is the exact statement of Decomp395c.batch0_prime.
The assembly has no sorry of its own. -/
theorem batch0_prime : ∀ q ∈ qs.take 64, q.Prime := by
  intro q hq
  have hb := candidate_bounds q hq
  exact Primality427.prime_of_iterate_trials hb.1 hb.2
    (divisor_residues q hq) (List.all_eq_true.mp trial_checks q hq)

#print axioms divisor_residues
#print axioms candidate_bounds
#print axioms batch_member
#print axioms trial_checks
#print axioms batch0_prime

end LeanLab.DtRS1998.Decomp427c
