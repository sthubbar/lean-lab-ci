/-
Second split, of `leaf_solution_count_succ_large` of `SPLIT_s5_S5_02_count_succ`, the
induction step of the counting form of Karacuba 1971 Lemma 1 p. 243, his reference [1],
Vinogradov, in the range `P ≥ (20 n)^(m+1)`.

* `leaf_count_add_n_le`: LEAF, MEDIUM, the monotonicity `J_(b+n)(P) ≤ P^(2n) J_b(P)` of the
  number of solutions, by Cauchy Schwarz over each added pair of variables.
* `s5_02b_mid`: proved, CONDITIONAL ON that leaf, from it and the hypothesis at `m`, for `P < (20 n)^n`: the excess
  `P^(N (1-1/n)^m / n)` with `N = n(n+1)/2` is then at most `(20 n)^N`.
* `leaf_solution_count_succ_large_beyond`: LEAF, HARD, the range `P ≥ (20 n)^n`.
* `leaf_solution_count_succ_large_of_leaves`: the parent leaf verbatim, with a `type_of%` twin.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_02_count_succ

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

open Classical

/-- LEAF: the monotonicity of the number of solutions of Vinogradov's system in the number of
variables, `J_(b+n)(P) ≤ P^(2n) J_b(P)`, used throughout Vinogradov's method behind Karacuba's
Lemma 1 p. 243, his reference [1]. MEDIUM. Proof: with `r_b(v)` the number of `x` with power
sums `v`, `J_b = Σ_v r_b(v)^2` and `r_(b+1)(v) = Σ_(t ≤ P) r_b(v - s(t))`, so Cauchy Schwarz gives
`J_(b+1) ≤ P^2 J_b`; iterate `n` times. Equivalently `∫ |S|^(2b+2) ≤ P^2 ∫ |S|^(2b)`. -/
theorem leaf_count_add_n_le :
    ∀ n b P : ℕ,
      ∑ x : Fin (b + n) → Fin P, ∑ y : Fin (b + n) → Fin P,
        (if (∀ j : Fin n,
            ∑ i : Fin (b + n), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
              = ∑ i : Fin (b + n), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
          then (1 : ℝ) else 0)
      ≤ (P : ℝ) ^ (2 * n) *
        ∑ x : Fin b → Fin P, ∑ y : Fin b → Fin P,
          (if (∀ j : Fin n,
              ∑ i : Fin b, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                = ∑ i : Fin b, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
            then (1 : ℝ) else 0) := by
  sorry

/-- Proved, CONDITIONAL ON the MEDIUM LEAF `leaf_count_add_n_le`, with the hypothesis at `m`: the induction step of Lemma 1
p. 243 for `0 < P < (20 n)^n`. -/
theorem s5_02b_mid (n : ℕ) (hn : 12 ≤ n) (m : ℕ) (P : ℕ) (hP : 0 < P)
    (hmid : (P : ℝ) < (20 * n : ℝ) ^ n)
    (ih : ∑ x : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ m) *
             (P : ℝ) ^ ((2 * (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) :
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
  have hb : n * (m + 1) + k = (n * m + k) + n := by ring
  have hstep := leaf_count_add_n_le n (n * m + k) P
  rw [← hb] at hstep
  refine lt_of_le_of_lt hstep ?_
  set J := ∑ x : Fin (n * m + k) → Fin P, ∑ y : Fin (n * m + k) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * m + k), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * m + k), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0) with hJ
  set N : ℝ := ((n * (n + 1) : ℕ) : ℝ) / 2 with hN
  set D : ℝ := (1 - 1 / (n : ℝ)) ^ m with hD
  have hnR : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hN0 : 0 < N := by rw [hN]; push_cast; positivity
  have hD0 : 0 ≤ D := by
    rw [hD]; apply pow_nonneg
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
    linarith
  have hD1 : D ≤ 1 := by
    rw [hD]; apply pow_le_one₀
    · have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hn0]; linarith
      linarith
    · have : 0 ≤ 1 / (n : ℝ) := by positivity
      linarith
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  -- the needed comparison of the P powers
  have hcmp : (P : ℝ) ^ (N * D) ≤ (20 * n : ℝ) ^ N * (P : ℝ) ^ (N * (1 - 1 / (n : ℝ)) ^ (m + 1)) := by
    have hsplitP : (P : ℝ) ^ (N * D) = (P : ℝ) ^ (N * D / n) * (P : ℝ) ^ (N * (1 - 1 / (n : ℝ)) ^ (m + 1)) := by
      rw [← Real.rpow_add hP0]; congr 1; rw [hD, pow_succ]; field_simp; ring
    rw [hsplitP]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (P : ℝ) ^ (N * D / n) ≤ (P : ℝ) ^ (N / n) := by
          apply Real.rpow_le_rpow_of_exponent_le hPR
          apply div_le_div_of_nonneg_right _ hn0.le
          nlinarith
      _ ≤ ((20 * n : ℝ) ^ n) ^ (N / n) := Real.rpow_le_rpow hP0.le hmid.le (by positivity)
      _ = (20 * n : ℝ) ^ N := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1; field_simp
  have hC : (20 * n : ℝ) ^ (N * ((m + 1 : ℕ) : ℝ)) = (20 * n : ℝ) ^ (N * m) * (20 * n : ℝ) ^ N := by
    rw [← Real.rpow_add (by positivity)]; congr 1; push_cast; ring
  have hE : (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - N) = (P : ℝ) ^ (2 * n) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hP0]; congr 1; push_cast; ring
  rw [hC, hE]
  have hP2n : 0 < (P : ℝ) ^ (2 * n) := by positivity
  have h1 := mul_lt_mul_of_pos_left ih hP2n
  have hCm : 0 ≤ (20 * n : ℝ) ^ (N * m) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hcmp hCm
  calc (P : ℝ) ^ (2 * n) * J < (P : ℝ) ^ (2 * n) * ((20 * n : ℝ) ^ (N * m) * ((P : ℝ) ^ (N * D) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N))) := h1
    _ = (P : ℝ) ^ (2 * n) * (((20 * n : ℝ) ^ (N * m) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N)) * (P : ℝ) ^ (N * D)) := by ring
    _ ≤ (P : ℝ) ^ (2 * n) * (((20 * n : ℝ) ^ (N * m) * (P : ℝ) ^ ((2 * (n * m + k) : ℝ) - N)) * ((20 * n : ℝ) ^ N * (P : ℝ) ^ (N * (1 - 1 / (n : ℝ)) ^ (m + 1)))) :=
        mul_le_mul_of_nonneg_left h2 hP2n.le
    _ = _ := by ring

/-- LEAF: Vinogradov's mean value theorem, induction step from `l = m` to `l = m + 1` as
Karacuba cites it for Lemma 1 p. 243, his reference [1], in the range `P ≥ (20 n)^(m+1)` and
`P ≥ (20 n)^n`, where neither the trivial count nor the monotonicity in the number of variables
suffices. HARD. This is the recursive inequality of Vinogradov's method, `J_(b+n)(P)` bounded
through `J_b(P_1)` with `P_1` about `P^(1 - 1/n)`. The statement is
`leaf_solution_count_succ_large` with `(20 n)^n ≤ P` added. -/
theorem leaf_solution_count_succ_large_beyond :
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
      ∀ P : ℕ, 0 < P → (20 * n : ℝ) ^ (m + 1) ≤ (P : ℝ) → (20 * n : ℝ) ^ n ≤ (P : ℝ) →
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

/-- PROVED from the leaves: the statement of `leaf_solution_count_succ_large` verbatim. -/
theorem leaf_solution_count_succ_large_of_leaves :
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
  intro n hn m hm ih P hP hlarge
  by_cases hs : (P : ℝ) < (20 * n : ℝ) ^ n
  · exact s5_02b_mid n hn m P hP hs (ih P hP)
  · exact leaf_solution_count_succ_large_beyond n hn m hm ih P hP hlarge (not_lt.1 hs)

/-- Twin: the assembly has exactly the type of the open leaf. -/
example : type_of% @leaf_solution_count_succ_large := leaf_solution_count_succ_large_of_leaves

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.s5_02b_mid
