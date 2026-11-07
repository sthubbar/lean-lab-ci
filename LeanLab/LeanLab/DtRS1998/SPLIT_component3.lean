/-
Split of component3 into four block-wise sub-domains of the fixed candidate
batch of the 10 ^ 90 row.

The statement asks, for every candidate q among the first 64 entries of the
fixed candidate list, and for every prime divisor p of q, for a residue i
below 9 with p ^ 560 congruent to q ^ (560 * i) modulo the sealed modulus
15321986788854443284662612735663611380010431225771200.

The proof route has two phases. Phase one is the finite primality
certification: each of the 64 candidates of this batch is a prime number.
Phase two is algebraic and costs nothing: if q is prime and p is a prime
divisor of q, then p equals q, so the witness i = 1 is immediate and no
residue computation is required. The four smaller primary components 2, 5
and 7 share this shape and are handled elsewhere.

This file therefore leaves the congruence arithmetic alone and splits the
batch by the size of the offset 10 ^ 90 - q into four consecutive blocks,

  block one    the offset is at least 60000
  block two    57000 <= offset < 60000
  block three  55000 <= offset < 57000
  block four   the offset is below 55000

and asks for the congruence for the candidates of one block at a time. The
four blocks partition the batch, all four are inhabited, and each block is a
proper sub-domain of the batch, so each leaf is strictly easier than the
whole statement and no leaf has a hypothesis that can never hold.

component3_split has no sorry of its own. The four block leaves are the only
open obligations this file adds.
-/
import LeanLab.DtRS1998.Decomp445a

namespace LeanLab.DtRS1998.Decomp445a

open Decomp372a

set_option maxRecDepth 100000

/-- LEAF. First block of the candidate batch: every candidate whose offset
10 ^ 90 - q is at least 60000, and every prime divisor of such a candidate,
with a residue witness below 9. This is the congruence step for 32 of the 64
candidates only, so it is strictly less than the whole statement. The closure
route is the finite primality phase: each candidate of this block is prime,
so a prime divisor p of q is q itself and the witness i = 1 works without any
residue computation. -/
theorem leaf_block_one :
    ∀ q ∈ qs.take 64, 60000 ≤ 10 ^ 90 - q → ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Second block of the candidate batch: every candidate whose offset
10 ^ 90 - q lies in the half-open range from 57000 to 60000, and every prime
divisor of it, with a residue witness below 9. This is the congruence step
for the 16 candidates of that range only. The closure route is again the
finite primality phase, after which the witness is i = 1. -/
theorem leaf_block_two :
    ∀ q ∈ qs.take 64, 57000 ≤ 10 ^ 90 - q → 10 ^ 90 - q < 60000 →
      ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Third block of the candidate batch: every candidate whose offset
10 ^ 90 - q lies in the half-open range from 55000 to 57000, and every prime
divisor of it, with a residue witness below 9. This is the congruence step
for the 11 candidates of that range only. The closure route is again the
finite primality phase, after which the witness is i = 1. -/
theorem leaf_block_three :
    ∀ q ∈ qs.take 64, 55000 ≤ 10 ^ 90 - q → 10 ^ 90 - q < 57000 →
      ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Fourth block of the candidate batch: every candidate whose offset
10 ^ 90 - q is below 55000, and every prime divisor of it, with a residue
witness below 9. This is the congruence step for the last 5 candidates of the
batch only, the smallest offset range of the four blocks. The closure route
is again the finite primality phase, after which the witness is i = 1. -/
theorem leaf_block_four :
    ∀ q ∈ qs.take 64, 10 ^ 90 - q < 55000 → ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- The exact component3 statement, proved from the four block leaves. The
four offset ranges partition the batch, so an arbitrary member q of the batch
falls into exactly one block and the corresponding block leaf supplies the
witness. No residue is computed here and the component3 statement itself is
not used. -/
theorem component3_split :
    ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 9 ∧
        p ^ 560 % 15321986788854443284662612735663611380010431225771200 =
          q ^ (560 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  by_cases h1 : 60000 ≤ 10 ^ 90 - q
  · exact leaf_block_one q hq h1 p hp hd
  · by_cases h2 : 57000 ≤ 10 ^ 90 - q
    · exact leaf_block_two q hq h2 (Nat.not_le.mp h1) p hp hd
    · by_cases h3 : 55000 ≤ 10 ^ 90 - q
      · exact leaf_block_three q hq h3 (Nat.not_le.mp h2) p hp hd
      · exact leaf_block_four q hq (Nat.not_le.mp h3) p hp hd

#print axioms leaf_block_one
#print axioms leaf_block_two
#print axioms leaf_block_three
#print axioms leaf_block_four
#print axioms component3_split

end LeanLab.DtRS1998.Decomp445a
