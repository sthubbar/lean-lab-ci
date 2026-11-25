/-
Next step on `KarLemma1`, Karacuba 1971 Lemma 1 page 243, Vinogradov's mean value theorem.
The only open leaf left by `SPLIT_leaf_karLemma1_mvt` and `SPLIT_leaf_mvt_threshold` is
`leaf_solution_count_deep`, the counting form of the threshold bound for `l ≥ 2`.

Vinogradov's method proves the bound by induction on `l`: the bound at `l` is passed to
`l + 1`, the exponent `b` growing by `n`, through the recursive inequality of the mean value
theorem. Here the induction is made explicit: the base `l = 1` is the proved lemma
`leaf_solution_count_at_one`, and the passage from `l` to `l + 1` is the new leaf
`leaf_solution_count_succ`. The assembly `leaf_solution_count_deep_split` has exactly the
type of `leaf_solution_count_deep`, checked by a `type_of%` twin.

AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.SPLIT_leaf_mvt_threshold

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

open Classical

/-- LEAF: Vinogradov's mean value theorem, induction step from `l` to `l + 1`, as Karacuba
cites it for Lemma 1 page 243. HARD. If the counting bound at the threshold exponent
`b = n m + [n(n+1)/4 + 1]` holds for every `P > 0`, then it holds at
`b + n = n (m + 1) + [n(n+1)/4 + 1]` for every `P > 0`, with the constant multiplied by
`(20 n)^(n(n+1)/2)` and the excess exponent multiplied by `1 - 1/n`. This is the recursive
step of Vinogradov's method, the passage from `J_b` to `J_(b+n)`. One implication. -/
theorem leaf_solution_count_succ :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m →
      (∀ P : ℕ, 0 < P →
        ∑ x : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ m) *
             (P : ℝ) ^ ((2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) →
      (∀ P : ℕ, 0 < P →
        ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) := by
  sorry

/-- Assembly: the open leaf `leaf_solution_count_deep` from the proved base case
`leaf_solution_count_at_one` and the induction step `leaf_solution_count_succ`. -/
theorem leaf_solution_count_deep_split :
    ∀ n : ℕ, 12 ≤ n → ∀ l : ℕ, 0 < l → 2 ≤ l → ∀ P : ℕ, 0 < P →
      ∑ x : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
      < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * l) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ l) *
             (P : ℝ) ^ ((2 * (n * l + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  intro n hn l hl h2 P hP
  clear h2
  induction l, hl using Nat.le_induction generalizing P with
  | base => exact leaf_solution_count_at_one n hn 1 rfl P hP
  | succ m hm ih =>
    have := leaf_solution_count_succ n hn m hm ih P hP
    simpa using this

/-- Twin: the assembly has exactly the type of the open leaf. -/
example : type_of% @leaf_solution_count_deep := leaf_solution_count_deep_split

/-- The target `KarLemma1` through the split chain, for the axiom check. -/
theorem karLemma1_next_chain : KarLemma1 := leaf_karLemma1_mvt_split

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.leaf_solution_count_deep_split
