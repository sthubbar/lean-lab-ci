/-
Split of `leaf_quarter_one_block_one` of the interval certificate at 10 ^ 270.

The block `j ≤ 31250000` is cut into four consecutive sub-blocks of ~7.8M offsets each.
Every sub-block carries its own prime list, and the budgets 4 + 4 + 3 + 3 = 14
reproduce the budget of the unsplit block, so the four lists concatenate to a
list of at most 14 primes covering the whole block.

Disclosure: dividing the budget over a sub-range is a strengthening of the
parent statement, not a consequence of it.  A cover of a sub-range holding its
proportional share of the primes does not follow from a cover of the whole range
with all 14.  Each leaf below is therefore a separately searchable certificate,
and the parent theorem `leaf_quarter_one_block_one` stays open.

Binary Goldbach is open.
-/
import LeanLab.DtRS1998.SPLIT_cover_quarter_one

namespace LeanLab.DtRS1998.Decomp270c

open LeanLab Task71.Paper Decomp270a

private def f732_c3 (x base : ℕ) : ℕ :=
  (2 * ((x % 3 + 3 - base % 3) % 3)) % 3

private def f732_c5 (x base : ℕ) : ℕ :=
  (3 * ((x % 5 + 5 - base % 5) % 5)) % 5

private def f732_c7 (x base : ℕ) : ℕ :=
  (4 * ((x % 7 + 7 - base % 7) % 7)) % 7

private def f732_c11 (x base : ℕ) : ℕ :=
  (6 * ((x % 11 + 11 - base % 11) % 11)) % 11

private def f732_crt (x0 x1 x2 x3 base : ℕ) : ℕ :=
  (385 * f732_c3 x0 base + 231 * f732_c5 x1 base +
    330 * f732_c7 x2 base + 210 * f732_c11 x3 base) % 1155

private lemma f732_c3_spec (x base : ℕ) :
    (base + 2 * f732_c3 x base) % 3 = x % 3 := by
  have hx := Nat.mod_lt x (by omega : 0 < 3)
  have hb := Nat.mod_lt base (by omega : 0 < 3)
  simp [f732_c3]
  omega

private lemma f732_c5_spec (x base : ℕ) :
    (base + 2 * f732_c5 x base) % 5 = x % 5 := by
  have hx := Nat.mod_lt x (by omega : 0 < 5)
  have hb := Nat.mod_lt base (by omega : 0 < 5)
  simp [f732_c5]
  omega

private lemma f732_c7_spec (x base : ℕ) :
    (base + 2 * f732_c7 x base) % 7 = x % 7 := by
  have hx := Nat.mod_lt x (by omega : 0 < 7)
  have hb := Nat.mod_lt base (by omega : 0 < 7)
  simp [f732_c7]
  omega

private lemma f732_c11_spec (x base : ℕ) :
    (base + 2 * f732_c11 x base) % 11 = x % 11 := by
  have hx := Nat.mod_lt x (by omega : 0 < 11)
  have hb := Nat.mod_lt base (by omega : 0 < 11)
  simp [f732_c11]
  omega

private lemma f732_crt_mod3 (x0 x1 x2 x3 base : ℕ) :
    f732_crt x0 x1 x2 x3 base % 3 = f732_c3 x0 base % 3 := by
  simp [f732_crt, f732_c3, f732_c5, f732_c7, f732_c11,
    Nat.add_mod, Nat.mul_mod]

private lemma f732_crt_mod5 (x0 x1 x2 x3 base : ℕ) :
    f732_crt x0 x1 x2 x3 base % 5 = f732_c5 x1 base % 5 := by
  simp [f732_crt, f732_c3, f732_c5, f732_c7, f732_c11,
    Nat.add_mod, Nat.mul_mod]

private lemma f732_crt_mod7 (x0 x1 x2 x3 base : ℕ) :
    f732_crt x0 x1 x2 x3 base % 7 = f732_c7 x2 base % 7 := by
  simp [f732_crt, f732_c3, f732_c5, f732_c7, f732_c11,
    Nat.add_mod, Nat.mul_mod]

private lemma f732_crt_mod11 (x0 x1 x2 x3 base : ℕ) :
    f732_crt x0 x1 x2 x3 base % 11 = f732_c11 x3 base % 11 := by
  simp [f732_crt, f732_c3, f732_c5, f732_c7, f732_c11,
    Nat.add_mod, Nat.mul_mod]

/-- LEAF 1 of 4: the first sub-block of the block, `j ≤ 7812500`, is covered by
a list of at most 4 primes.  This is the first range cut of the block, the
sub-block containing the smallest offsets including `j = 0`; it carries the
first 4 of the 14 primes. -/
theorem leaf_block_one_sub_one :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ 7812500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 2 of 4: the second sub-block of the block, `7812501 ≤ j ≤ 15625000`, is
covered by a list of at most 4 primes.  It carries the next 4 primes of the
budget. -/
theorem leaf_block_one_sub_two :
    ∃ qs : List ℕ, qs.length ≤ 4 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 7812501 ≤ j → j ≤ 15625000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 3 of 4: the third sub-block of the block, `15625001 ≤ j ≤ 23437500`, is
covered by a list of at most 3 primes.  It carries the next 3 primes of the
budget. -/
theorem leaf_block_one_sub_three :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 15625001 ≤ j → j ≤ 23437500 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- LEAF 4 of 4: the last sub-block of the block, `23437501 ≤ j ≤ 31250000`, is
covered by a list of at most 3 primes.  It carries the last 3 primes of the
budget, and the four sub-block endpoints chain up to the block endpoint
`31250000`. -/
theorem leaf_block_one_sub_four :
    ∃ qs : List ℕ, qs.length ≤ 3 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, 23437501 ≤ j → j ≤ 31250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  sorry

/-- The four sub-block lists, concatenated, cover the first block: the lengths
add up to at most 14, every member is prime, and every offset `j` of the block
falls in one of the four sub-blocks, where its sub-block list already has a
witness. -/
theorem leaf_quarter_one_block_one_F732 :
    ∃ qs : List ℕ, qs.length ≤ 14 ∧
      (∀ q ∈ qs, q.Prime) ∧
      (∀ j : ℕ, j ≤ 31250000 →
        qs.any (fun q => decide
          (q ≤ 10 ^ 270 + 2 * j ∧ (10 ^ 270 + 2 * j - q).Prime)) = true) := by
  obtain ⟨qs1, h1len, h1p, h1c⟩ := leaf_block_one_sub_one
  obtain ⟨qs2, h2len, h2p, h2c⟩ := leaf_block_one_sub_two
  obtain ⟨qs3, h3len, h3p, h3c⟩ := leaf_block_one_sub_three
  obtain ⟨qs4, h4len, h4p, h4c⟩ := leaf_block_one_sub_four
  refine ⟨qs1 ++ qs2 ++ qs3 ++ qs4, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((h | h) | h) | h
    · exact h1p q h
    · exact h2p q h
    · exact h3p q h
    · exact h4p q h
  · intro j hj4
    by_cases h1 : j ≤ 7812500
    · have ha := h1c j h1
      rw [List.any_append, List.any_append, List.any_append, ha]
      simp
    · have h1' : 7812501 ≤ j := by omega
      by_cases h2 : j ≤ 15625000
      · have ha := h2c j h1' h2
        rw [List.any_append, List.any_append, List.any_append, ha]
        simp
      · have h2' : 15625001 ≤ j := by omega
        by_cases h3 : j ≤ 23437500
        · have ha := h3c j h2' h3
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp
        · have h3' : 23437501 ≤ j := by omega
          have ha := h4c j h3' hj4
          rw [List.any_append, List.any_append, List.any_append, ha]
          simp

#print axioms leaf_quarter_one_block_one_F732

end LeanLab.DtRS1998.Decomp270c