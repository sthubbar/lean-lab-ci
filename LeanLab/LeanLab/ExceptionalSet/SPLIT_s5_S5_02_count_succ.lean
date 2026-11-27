/-
Split of `leaf_solution_count_succ` of `KarLemma1Next`, the induction step `l` to `l + 1` of
Vinogradov's mean value theorem in the counting form, as Karacuba cites it for Lemma 1 on p. 243
of Trudy Mat. Inst. Steklov 112 (1971), his reference [1], Vinogradov.

The split is by the size of `P` against the constant `(20 n)^(m+1)` of the conclusion.

* `s5_count_succ_trivial`: PROVED. For `P < (20 n)^(m+1)` the conclusion follows from the
  trivial count, the number of pairs `(x, y)` is at most `P^(2 b)`, since the excess factor
  `P^(N (1 - (1 - 1/n)^(m+1)))` with `N = n(n+1)/2` is then below `(20 n)^(N (m+1))`.
  No use of the hypothesis at `m`.
* `leaf_solution_count_succ_large`: LEAF, the range `P ≥ (20 n)^(m+1)`, where the recursive
  inequality of Vinogradov's method passing from `J_b` to `J_(b+n)` is really needed.
* `leaf_solution_count_succ_of_leaves`: the statement of `leaf_solution_count_succ` verbatim,
  proved from the two, with a `type_of%` twin.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KarLemma1Next

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

open Classical

/-- PROVED. The trivial range of the induction step: for `0 < P < (20 n)^(m+1)` the number of
pairs is at most `P^(2 b)` with `b = n (m + 1) + [n(n+1)/4 + 1]`, which is below the right side
of Karacuba's Lemma 1 at `l = m + 1`, p. 243. -/
theorem s5_count_succ_trivial (n : ℕ) (hn : 12 ≤ n) (m : ℕ) (P : ℕ) (hP : 0 < P)
    (hsmall : (P : ℝ) < (20 * n : ℝ) ^ (m + 1)) :
        ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  set k := ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hk
  set N : ℝ := ((n * (n + 1) : ℕ) : ℝ) / 2 with hN
  set D : ℝ := (1 - 1 / (n : ℝ)) ^ (m + 1) with hD
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : 0 < N := by rw [hN]; push_cast; positivity
  have hD0 : 0 < D := by
    rw [hD]; apply pow_pos
    have : 1 / (n : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hD1 : D ≤ 1 := by
    rw [hD]; apply pow_le_one₀
    · have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    · have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  -- trivial bound on the left side
  have hL : (∑ x : Fin (n * (m + 1) + k) → Fin P, ∑ y : Fin (n * (m + 1) + k) → Fin P,
      (if (∀ j : Fin n,
          ∑ i : Fin (n * (m + 1) + k), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
            = ∑ i : Fin (n * (m + 1) + k), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
        then (1 : ℝ) else 0)) ≤ (P : ℝ) ^ (((2 * (n * (m + 1) + k) : ℕ) : ℝ)) := by
    calc _ ≤ ∑ x : Fin (n * (m + 1) + k) → Fin P, ∑ y : Fin (n * (m + 1) + k) → Fin P, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
          split_ifs <;> norm_num
      _ = (P : ℝ) ^ (((2 * (n * (m + 1) + k) : ℕ) : ℝ)) := by
          rw [Real.rpow_natCast]
          simp [Finset.card_univ]
          ring
  refine lt_of_le_of_lt hL ?_
  have hexp : ((2 * (n * (m + 1) + k) : ℕ) : ℝ) = N * D + ((2 * (n * (m + 1) + k) : ℝ) - N) + (N - N * D) := by
    push_cast; ring
  rw [hexp, Real.rpow_add hP0, Real.rpow_add hP0]
  have hC : (P : ℝ) ^ (N - N * D) < (20 * n : ℝ) ^ (N * ((m + 1 : ℕ) : ℝ)) := by
    calc (P : ℝ) ^ (N - N * D) ≤ (P : ℝ) ^ N := by
          apply Real.rpow_le_rpow_of_exponent_le hPR; nlinarith
      _ < ((20 * n : ℝ) ^ (m + 1)) ^ N := Real.rpow_lt_rpow hP0.le hsmall hN0
      _ = (20 * n : ℝ) ^ (N * ((m + 1 : ℕ) : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm (((m + 1 : ℕ) : ℝ)) N]
  have hpos : 0 < (P : ℝ) ^ (N * D) * (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - N) := by positivity
  have := mul_lt_mul_of_pos_left hC hpos
  calc (P : ℝ) ^ (N * D) * (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - N) * (P : ℝ) ^ (N - N * D)
      = (P : ℝ) ^ (N * D) * (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - N) * (P : ℝ) ^ (N - N * D) := rfl
    _ < (P : ℝ) ^ (N * D) * (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - N) * (20 * n : ℝ) ^ (N * ((m + 1 : ℕ) : ℝ)) := this
    _ = _ := by ring


/-- LEAF: Vinogradov's mean value theorem, induction step from `l = m` to `l = m + 1` as
Karacuba cites it for Lemma 1 p. 243, his reference [1], in the range `P ≥ (20 n)^(m+1)` where
the trivial count does not suffice. HARD. This is the recursive inequality of Vinogradov's
method, `J_(b+n)(P)` bounded through `J_b(P_1)` with `P_1` about `P^(1 - 1/n)`, which uses the
hypothesis at the smaller length `P_1`, then the arithmetic of the exponents. The statement is
`leaf_solution_count_succ` with the conclusion restricted to `(20 n)^(m+1) ≤ P`. -/
theorem leaf_solution_count_succ_large :
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
      ∀ P : ℕ, 0 < P → (20 * n : ℝ) ^ (m + 1) ≤ (P : ℝ) →
        ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  sorry

/-- PROVED from the leaves: the statement of `leaf_solution_count_succ` verbatim. -/
theorem leaf_solution_count_succ_of_leaves :
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
  intro n hn m hm ih P hP
  by_cases hs : (P : ℝ) < (20 * n : ℝ) ^ (m + 1)
  · exact s5_count_succ_trivial n hn m P hP hs
  · exact leaf_solution_count_succ_large n hn m hm ih P hP (not_lt.1 hs)

/-- Twin: the assembly has exactly the type of the open leaf. -/
example : type_of% @leaf_solution_count_succ := leaf_solution_count_succ_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.s5_count_succ_trivial
