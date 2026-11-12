/-
AI wrote this Lean code for CODEX task427.
P0037 Section 5.1 page 211 and Table 1 page 213, row 10^95.
Cohen and Lenstra 1987 page 108, final trial division.
The prime divisor congruences remain OPEN.
The finite trial checks assert no candidate primality by themselves.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp372bData
import LeanLab.DtRS1998.Primality427
import LeanLab.DtRS1998.PocklingtonB7Row95

namespace LeanLab.DtRS1998.Decomp427b

open Decomp372b

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- LEAF. P0037 page 211, finite primality phase, with Cohen and Lenstra
1987 page 108, final trial division and its preceding divisor conclusion.
Every prime divisor of a first batch candidate lies in the power residue orbit.
This asserts only the congruence ingredient, not primality or accepted trials.
The cyclotomic justification for these concrete congruences is OPEN.
ROUTE BURST 7: proved from `PocklingtonB7Row95.qs_prime`, the kernel checked Pocklington
certificates, and so CONDITIONAL only on that file's `hard_prime` leaf while it is open. -/
theorem divisor_residues :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 5040 ∧
        p % 15321986788854443284662612735663611380010431225771200 = q ^ i % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  have hq' := PocklingtonB7Row95.qs_prime q (List.mem_of_mem_take hq)
  obtain rfl : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hd
  exact ⟨1, by decide, by rw [pow_one]⟩

/-- LEAF. Cohen and Lenstra 1987 page 108, the square modulus condition.
P0037 page 213, row 10^95. Every first batch candidate is at least two
and is smaller than the square of the chosen trial modulus. -/
theorem candidate_bounds :
    ∀ q ∈ qs.take 64, 2 ≤ q ∧ q < 15321986788854443284662612735663611380010431225771200 ^ 2 := by
  decide +kernel

/-- P0037 page 213 and Cohen and Lenstra 1987 page 108.
The first candidate gives an explicit inhabited batch premise. -/
theorem batch_member : (10 ^ 95 - 64011) ∈ qs.take 64 := by
  decide +kernel

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 1 through 4 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials0 :
    ([10 ^ 95 - 64011, 10 ^ 95 - 63671, 10 ^ 95 - 63209, 10 ^ 95 - 63003] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials0

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 5 through 8 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials1 :
    ([10 ^ 95 - 62927, 10 ^ 95 - 62801, 10 ^ 95 - 62771, 10 ^ 95 - 62763] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials1

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 9 through 12 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials2 :
    ([10 ^ 95 - 62607, 10 ^ 95 - 62471, 10 ^ 95 - 62411, 10 ^ 95 - 62343] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials2

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 13 through 16 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials3 :
    ([10 ^ 95 - 62093, 10 ^ 95 - 62009, 10 ^ 95 - 61067, 10 ^ 95 - 60567] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials3

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 17 through 20 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials4 :
    ([10 ^ 95 - 60533, 10 ^ 95 - 60437, 10 ^ 95 - 60407, 10 ^ 95 - 60179] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials4

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 21 through 24 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials5 :
    ([10 ^ 95 - 59909, 10 ^ 95 - 59877, 10 ^ 95 - 59741, 10 ^ 95 - 59523] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials5

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 25 through 28 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials6 :
    ([10 ^ 95 - 59507, 10 ^ 95 - 59273, 10 ^ 95 - 58971, 10 ^ 95 - 58689] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials6

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 29 through 32 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials7 :
    ([10 ^ 95 - 58251, 10 ^ 95 - 57719, 10 ^ 95 - 57299, 10 ^ 95 - 57281] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials7

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 33 through 36 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials8 :
    ([10 ^ 95 - 56777, 10 ^ 95 - 56667, 10 ^ 95 - 56609, 10 ^ 95 - 56559] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials8

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 37 through 40 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials9 :
    ([10 ^ 95 - 56063, 10 ^ 95 - 55961, 10 ^ 95 - 55469, 10 ^ 95 - 55419] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials9

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 41 through 44 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials10 :
    ([10 ^ 95 - 55107, 10 ^ 95 - 55047, 10 ^ 95 - 54677, 10 ^ 95 - 54659] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials10

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 45 through 48 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials11 :
    ([10 ^ 95 - 54653, 10 ^ 95 - 54651, 10 ^ 95 - 54441, 10 ^ 95 - 54299] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials11

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 49 through 52 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials12 :
    ([10 ^ 95 - 54263, 10 ^ 95 - 54183, 10 ^ 95 - 54173, 10 ^ 95 - 54057] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials12

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 53 through 56 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials13 :
    ([10 ^ 95 - 54051, 10 ^ 95 - 53741, 10 ^ 95 - 53609, 10 ^ 95 - 53549] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials13

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 57 through 60 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials14 :
    ([10 ^ 95 - 53493, 10 ^ 95 - 53367, 10 ^ 95 - 53207, 10 ^ 95 - 53199] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials14

/-- Cohen and Lenstra 1987 page 108, step l1 and l3.
Finite residue trials for batch positions 61 through 64 of row 10^95.
No prime divisor congruence or candidate primality is asserted. -/
theorem trials15 :
    ([10 ^ 95 - 53039, 10 ^ 95 - 52961, 10 ^ 95 - 52881, 10 ^ 95 - 52401] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  decide +kernel

#print axioms trials15

/-- LEAF. Cohen and Lenstra 1987 page 108, step l1 and l3.
All final trial divisions pass for this first batch. This is independent
of the OPEN prime divisor congruences and asserts no primality. -/
theorem trial_checks :
    (qs.take 64).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true := by
  change (([10 ^ 95 - 64011, 10 ^ 95 - 63671, 10 ^ 95 - 63209, 10 ^ 95 - 63003] ++ [10 ^ 95 - 62927, 10 ^ 95 - 62801, 10 ^ 95 - 62771, 10 ^ 95 - 62763] ++ [10 ^ 95 - 62607, 10 ^ 95 - 62471, 10 ^ 95 - 62411, 10 ^ 95 - 62343] ++ [10 ^ 95 - 62093, 10 ^ 95 - 62009, 10 ^ 95 - 61067, 10 ^ 95 - 60567] ++ [10 ^ 95 - 60533, 10 ^ 95 - 60437, 10 ^ 95 - 60407, 10 ^ 95 - 60179] ++ [10 ^ 95 - 59909, 10 ^ 95 - 59877, 10 ^ 95 - 59741, 10 ^ 95 - 59523] ++ [10 ^ 95 - 59507, 10 ^ 95 - 59273, 10 ^ 95 - 58971, 10 ^ 95 - 58689] ++ [10 ^ 95 - 58251, 10 ^ 95 - 57719, 10 ^ 95 - 57299, 10 ^ 95 - 57281] ++ [10 ^ 95 - 56777, 10 ^ 95 - 56667, 10 ^ 95 - 56609, 10 ^ 95 - 56559] ++ [10 ^ 95 - 56063, 10 ^ 95 - 55961, 10 ^ 95 - 55469, 10 ^ 95 - 55419] ++ [10 ^ 95 - 55107, 10 ^ 95 - 55047, 10 ^ 95 - 54677, 10 ^ 95 - 54659] ++ [10 ^ 95 - 54653, 10 ^ 95 - 54651, 10 ^ 95 - 54441, 10 ^ 95 - 54299] ++ [10 ^ 95 - 54263, 10 ^ 95 - 54183, 10 ^ 95 - 54173, 10 ^ 95 - 54057] ++ [10 ^ 95 - 54051, 10 ^ 95 - 53741, 10 ^ 95 - 53609, 10 ^ 95 - 53549] ++ [10 ^ 95 - 53493, 10 ^ 95 - 53367, 10 ^ 95 - 53207, 10 ^ 95 - 53199] ++ [10 ^ 95 - 53039, 10 ^ 95 - 52961, 10 ^ 95 - 52881, 10 ^ 95 - 52401] : List ℕ).all (fun q => (List.iterate (fun r : ℕ => r * q % 15321986788854443284662612735663611380010431225771200) (1 % 15321986788854443284662612735663611380010431225771200) 5040).all
      (fun r => decide (r ∣ q → r = 1 ∨ r = q))) = true)
  simp only [List.all_append, trials0, trials1, trials2, trials3, trials4, trials5, trials6, trials7, trials8, trials9, trials10, trials11, trials12, trials13, trials14, trials15, Bool.and_self]

/-- P0037 page 211 with Cohen and Lenstra 1987 page 108.
CONDITIONAL ON the OPEN divisor_residues leaf.
This is the exact statement of Decomp395b.batch0_prime.
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

end LeanLab.DtRS1998.Decomp427b
