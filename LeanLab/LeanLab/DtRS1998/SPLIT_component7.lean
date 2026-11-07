/-
Split of the exponent-720 primary component of Decomp445a, `component7`.

The target is a congruence obligation on the first 64 candidates of the fixed
row 10^90 candidate list: for every candidate q in that block and every prime
p dividing q, the 720th power of p is a power of the 720th power of q modulo
the fixed modulus, with an exponent i below 7.

The eight leaves below cut the block `qs.take 64` into eight consecutive windows
of eight candidates each, and `component7_split` reassembles the block from them
by splitting the list once per window. Each leaf asserts the same congruence
obligation on eight candidates, a strictly smaller finite claim than the whole
block; none of them assumes the block statement, and the assembly has no sorry
of its own. The list-splitting identity used in the assembly is proved here.

The route that closes a window, recorded so that the next worker does not
re-walk a longer one: a window closes as soon as its eight candidates are
certified prime, because a prime divisor of a prime candidate is the candidate
itself, and then the witness is i = 1 and the congruence is reflexivity. No
character value, no p-adic input and no orbit computation is needed for this one
projection. What is missing here is the finite primality certificate for those
eight written-out 90 digit integers; none is present in this tree.

The eight leaves remain OPEN. Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp445a

namespace LeanLab.DtRS1998.Decomp445a

open Decomp372a

set_option maxRecDepth 100000

/-- A block of length `a + b` is its first `a` entries followed by the next `b`
entries. This is the only list bookkeeping the assembly needs; it is proved here
so that no existing file is touched. -/
private theorem take_add_split (l : List ℕ) (a b : ℕ) :
    l.take (a + b) = l.take a ++ (l.drop a).take b := by
  conv_lhs => rw [← List.take_append_drop a (l.take (a + b))]
  rw [List.take_take, List.take_drop]
  simp

/-- LEAF. First step of the proof of the exponent-720 component: the
congruence obligation on the first window of eight candidates of `qs.take 64`,
namely positions 1 through 8 of the fixed row 10^90 candidate list, cut by
`qs.take 8`. The finite certification for these eight candidates stays OPEN. -/
theorem component7_window0 :
    ∀ q ∈ qs.take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Second step of the proof of the exponent-720 component: the
congruence obligation on positions 9 through 16 of the candidate list, cut by
`(qs.drop 8).take 8`, the second window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window1 :
    ∀ q ∈ (qs.drop 8).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Third step of the proof of the exponent-720 component: the
congruence obligation on positions 17 through 24 of the candidate list, cut by
`(qs.drop 16).take 8`, the third window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window2 :
    ∀ q ∈ (qs.drop 16).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Fourth step of the proof of the exponent-720 component: the
congruence obligation on positions 25 through 32 of the candidate list, cut by
`(qs.drop 24).take 8`, the fourth window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window3 :
    ∀ q ∈ (qs.drop 24).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Fifth step of the proof of the exponent-720 component: the
congruence obligation on positions 33 through 40 of the candidate list, cut by
`(qs.drop 32).take 8`, the fifth window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window4 :
    ∀ q ∈ (qs.drop 32).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Sixth step of the proof of the exponent-720 component: the
congruence obligation on positions 41 through 48 of the candidate list, cut by
`(qs.drop 40).take 8`, the sixth window of the block. The finite certification
for these eight candidates stays OPEN. -/
theorem component7_window5 :
    ∀ q ∈ (qs.drop 40).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Seventh step of the proof of the exponent-720 component: the
congruence obligation on positions 49 through 56 of the candidate list, cut by
`(qs.drop 48).take 8`, the seventh window of the block. The finite
certification for these eight candidates stays OPEN. -/
theorem component7_window6 :
    ∀ q ∈ (qs.drop 48).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- LEAF. Eighth and last step of the proof of the exponent-720 component: the
congruence obligation on the final window of eight candidates, positions 57
through 64 of the fixed row 10^90 candidate list, cut by `(qs.drop 56).take 8`,
which is what remains of the block after the seven earlier windows. The finite
certification for these eight candidates stays OPEN. -/
theorem component7_window7 :
    ∀ q ∈ (qs.drop 56).take 8, ∀ p : ℕ, p.Prime → p ∣ q →
      ∃ i : ℕ, i < 7 ∧
        p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  sorry

/-- The exact statement of `component7`, proved from the eight windows above and
not from `component7` itself. Each step rewrites the remaining block
`(qs.drop (8 * k)).take (64 - 8 * k)` into its next window of eight followed by
a shorter remainder, using `take_add_split` and `List.drop_drop`. -/
theorem component7_split : ∀ q ∈ qs.take 64, ∀ p : ℕ, p.Prime → p ∣ q → ∃ i : ℕ, i < 7 ∧ p ^ 720 % 15321986788854443284662612735663611380010431225771200 = q ^ (720 * i) % 15321986788854443284662612735663611380010431225771200 := by
  intro q hq p hp hd
  rw [show (64 : ℕ) = 8 + 56 from rfl, take_add_split] at hq
  rcases List.mem_append.mp hq with h | h
  · exact component7_window0 q h p hp hd
  rw [show (56 : ℕ) = 8 + 48 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window1 q h p hp hd
  rw [List.drop_drop, show (8 : ℕ) + 8 = 16 from rfl,
    show (48 : ℕ) = 8 + 40 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window2 q h p hp hd
  rw [List.drop_drop, show (16 : ℕ) + 8 = 24 from rfl,
    show (40 : ℕ) = 8 + 32 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window3 q h p hp hd
  rw [List.drop_drop, show (24 : ℕ) + 8 = 32 from rfl,
    show (32 : ℕ) = 8 + 24 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window4 q h p hp hd
  rw [List.drop_drop, show (32 : ℕ) + 8 = 40 from rfl,
    show (24 : ℕ) = 8 + 16 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window5 q h p hp hd
  rw [List.drop_drop, show (40 : ℕ) + 8 = 48 from rfl,
    show (16 : ℕ) = 8 + 8 from rfl, take_add_split] at h
  rcases List.mem_append.mp h with h | h
  · exact component7_window6 q h p hp hd
  rw [List.drop_drop, show (48 : ℕ) + 8 = 56 from rfl] at h
  exact component7_window7 q h p hp hd

#print axioms component7_split

end LeanLab.DtRS1998.Decomp445a
