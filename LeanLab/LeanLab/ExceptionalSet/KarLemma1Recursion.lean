/-
Re-split of the leaf `leaf_solution_count_succ` of `KarLemma1Next`, the induction step of
Vinogradov's mean value theorem as Karacuba 1971 cites it for Lemma 1, p. 243.

Write `N = n(n+1)/2`, `k = [n(n+1)/4 + 1]`, `b = n m + k`, `δ_m = N (1 - 1/n)^m` and
`J_s(P)` for the number of pairs of `s`-tuples in `[1, P]` with equal power sums of orders
`1, ..., n`. The target passes `J_b(P) < (20n)^(N m) P^(δ_m) P^(2b - N)` for all `P > 0` to the
same bound at `b + n`, `m + 1`.

Pieces:
* (A) LEAF `leaf_vinogradov_recursion`: Vinogradov's recursive inequality
  `J_(b+n)(P) ≤ (20n)^N P^(2n + 2b/n - (n+1)/2) J_b(P1)`, `P1 = [P^(1 - 1/n)]`, for `P` large
  compared with `b`, namely `(20n)^(m+1) ≤ P`.
* (B) `count_le_total`: the trivial bound `J_s(P) ≤ P^(2s)`, proved.
* (C) `step_arith`: the exponent and constant arithmetic, proved; and `small_region`: the
  target bound for `P < (20n)^(m+1)` from (B), proved.
The assembly `leaf_solution_count_succ_split` has exactly the type of the leaf, by a twin.

Rounding: `P1 = [P^(1-1/n)] ≤ P^(1-1/n)`, and every exponent of `P1` is nonnegative, so the
rounding costs nothing in (C). The hypothesis `(20n)^(m+1) ≤ P` in (A) is needed: with a
fixed constant and `P` fixed, the inequality with the floor fails as `b → ∞`, since the loss
`(P^(1-1/n)/P1)^(2b)` is unbounded. Below that threshold the target bound is trivial.

AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.KarLemma1Next

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.Recursion

open LeanLab.ExceptionalSet.U1539 LeanLab.ExceptionalSet.U1539.KaracubaSplit

open Classical

/-- (B) The trivial bound: the number of pairs of `s`-tuples in `[1, P]` with equal power sums
is at most the number `P^(2s)` of all pairs. -/
theorem count_le_total (n s P : ℕ) :
    ∑ x : Fin s → Fin P, ∑ y : Fin s → Fin P,
      (if (∀ j : Fin n,
          ∑ i : Fin s, (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
            = ∑ i : Fin s, (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
        then (1 : ℝ) else 0) ≤ (P : ℝ) ^ (2 * s) := by
  calc _ ≤ ∑ _x : Fin s → Fin P, ∑ _y : Fin s → Fin P, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro y _
        split_ifs <;> norm_num
    _ = (P : ℝ) ^ (2 * s) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        push_cast; ring

/-- (C), small `P`: for `0 < P < (20n)^(m+1)` the target bound at `m + 1` follows from the
trivial bound, because then `P^N < (20n)^(N(m+1))` and `P^(δ_(m+1)) ≥ 1`. -/
theorem small_region (n m k P : ℕ) (hn : 12 ≤ n) (hP : 0 < P)
    (hsmall : (P : ℝ) < (20 * n : ℝ) ^ (m + 1)) :
    ∑ x : Fin (n * (m + 1) + k) → Fin P,
          ∑ y : Fin (n * (m + 1) + k) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + k), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + k), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            ((P : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             (P : ℝ) ^ ((2 * (n * (m + 1) + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  refine lt_of_le_of_lt (count_le_total n (n * (m + 1) + k) P) ?_
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hA : (0 : ℝ) < ((n * (n + 1) : ℕ) : ℝ) / 2 := by
    have : 0 < n * (n + 1) := Nat.mul_pos (by omega) (by omega)
    positivity
  set A : ℝ := ((n * (n + 1) : ℕ) : ℝ) / 2 with hAdef
  set e : ℝ := (2 * (n * (m + 1) + k) : ℝ) - A
  have hsplit : (P : ℝ) ^ (2 * (n * (m + 1) + k)) = (P : ℝ) ^ e * (P : ℝ) ^ A := by
    rw [← Real.rpow_add hP0, ← Real.rpow_natCast]
    congr 1; simp only [e]; push_cast; ring
  have hpow : (P : ℝ) ^ A < (20 * n : ℝ) ^ (A * ((m + 1 : ℕ) : ℝ)) := by
    rw [mul_comm A, Real.rpow_mul (by positivity), Real.rpow_natCast]
    exact Real.rpow_lt_rpow hP0.le hsmall hA
  have hone : (1 : ℝ) ≤ (P : ℝ) ^ (A * (1 - 1 / (n : ℝ)) ^ (m + 1)) := by
    apply Real.one_le_rpow hP1
    have : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      exact_mod_cast (by omega : 1 ≤ n)
    positivity
  rw [hsplit]
  have he : 0 < (P : ℝ) ^ e := Real.rpow_pos_of_pos hP0 e
  have hT : 0 < (20 * n : ℝ) ^ (A * ((m + 1 : ℕ) : ℝ)) := by
    apply Real.rpow_pos_of_pos; positivity
  calc (P : ℝ) ^ e * (P : ℝ) ^ A < (P : ℝ) ^ e * (20 * n : ℝ) ^ (A * ((m + 1 : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hpow he
    _ ≤ (P : ℝ) ^ e * (20 * n : ℝ) ^ (A * ((m + 1 : ℕ) : ℝ)) *
          (P : ℝ) ^ (A * (1 - 1 / (n : ℝ)) ^ (m + 1)) :=
        le_mul_of_one_le_right (by positivity) hone
    _ = _ := by ring

/-- (C), large `P`: the exponent and constant arithmetic. From the recursive inequality
`J ≤ (20n)^N P^(2n + 2b/n - (n+1)/2) J1` and the bound at `m` evaluated at
`P1 ≤ P^(1-1/n)`, `P1 ≥ 1`, the bound at `m + 1` follows: the constants multiply to
`(20n)^(N(m+1))`, and the exponents add to `δ_(m+1) + 2(b+n) - N`. Uses `k ≥ n(n+1)/4`, so
that `2b - N ≥ 0`. -/
theorem step_arith (n m k P1 : ℕ) (P J J1 : ℝ) (hn : 12 ≤ n)
    (hk : ((n * (n + 1) : ℕ) : ℝ) / 4 ≤ (k : ℝ)) (hP : 1 ≤ P) (hP1 : 1 ≤ P1)
    (hP1le : (P1 : ℝ) ≤ P ^ (1 - 1 / (n : ℝ)))
    (h1 : J1 < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
            ((P1 : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ m) *
             (P1 : ℝ) ^ ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)))
    (h2 : J ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
            P ^ (2 * (n : ℝ) + 2 * ((n * m + k : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2) * J1) :
    J < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) *
            (P ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * (1 - 1 / (n : ℝ)) ^ (m + 1)) *
             P ^ ((2 * (n * (m + 1) + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
  have hP0 : 0 < P := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hq : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one hn0]
    exact_mod_cast (by omega : 1 ≤ n)
  have hA : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by push_cast; ring
  set q : ℝ := 1 - 1 / (n : ℝ) with hqdef
  have hδ : (0 : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m := by positivity
  have he : (0 : ℝ) ≤ (2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2 := by
    have : (0 : ℝ) ≤ (n : ℝ) * m := by positivity
    linarith
  have hP1r : (0 : ℝ) ≤ (P1 : ℝ) := by positivity
  have e1 : (P1 : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m)
      ≤ P ^ (q * (((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m)) := by
    rw [Real.rpow_mul hP0.le]; exact Real.rpow_le_rpow hP1r hP1le hδ
  have e2 : (P1 : ℝ) ^ ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)
      ≤ P ^ (q * ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)) := by
    rw [Real.rpow_mul hP0.le]; exact Real.rpow_le_rpow hP1r hP1le he
  have hC : (0 : ℝ) ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) := by positivity
  have hJ1 : J1 < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
      (P ^ (q * (((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m)) *
       P ^ (q * ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) := by
    refine lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left ?_ hC)
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  have hKp : 0 < (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
      P ^ (2 * (n : ℝ) + 2 * ((n * m + k : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2) := by
    apply mul_pos
    · apply Real.rpow_pos_of_pos; positivity
    · exact Real.rpow_pos_of_pos hP0 _
  refine lt_of_le_of_lt h2 (lt_of_lt_of_le (mul_lt_mul_of_pos_left hJ1 hKp) (le_of_eq ?_))
  have hK : (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
      (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m)
      = (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * ((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1; push_cast; ring
  have hE : (2 * (n : ℝ) + 2 * ((n * m + k : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2)
      + q * (((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m)
      + q * ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2)
      = ((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ (m + 1)
        + ((2 * (n * (m + 1) + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2) := by
    rw [pow_succ]
    generalize q ^ m = r
    rw [hA, hqdef]
    push_cast
    field_simp
    ring
  calc (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
        P ^ (2 * (n : ℝ) + 2 * ((n * m + k : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2) *
        ((20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m) *
          (P ^ (q * (((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m)) *
           P ^ (q * ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))))
      = ((20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
          (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2 * m)) *
        (P ^ (2 * (n : ℝ) + 2 * ((n * m + k : ℕ) : ℝ) / n - ((n : ℝ) + 1) / 2) *
          P ^ (q * (((n * (n + 1) : ℕ) : ℝ) / 2 * q ^ m)) *
          P ^ (q * ((2 * (n * m + k) : ℝ) - ((n * (n + 1) : ℕ) : ℝ) / 2))) := by ring
    _ = _ := by
      rw [hK, ← Real.rpow_add hP0, ← Real.rpow_add hP0, hE, Real.rpow_add hP0]

/-- LEAF: Vinogradov's recursive inequality, the step of his mean value theorem from `J_b` to
`J_(b+n)`, as Karacuba 1971 cites it for Lemma 1, p. 243, his reference [2]. HARD.
With `N = n(n+1)/2`, `b = n m + [n(n+1)/4 + 1]` and `P1 = [P^(1-1/n)]`:
`J_(b+n)(P) ≤ (20n)^N P^(2n + 2b/n - (n+1)/2) J_b(P1)`, in the counting form of the lab,
for `P` large compared with `b`, namely `(20n)^(m+1) ≤ P`. The constant `(20n)^N` is the ratio
`D_(m+1)/D_m` of the constants `D_l = (20n)^(N l)` of `KarLemma1`. One inequality; the bound
at `m` is not part of it. -/
theorem leaf_vinogradov_recursion :
    ∀ n : ℕ, 12 ≤ n → ∀ m : ℕ, 1 ≤ m → ∀ P : ℕ, (20 * n : ℝ) ^ (m + 1) ≤ P →
      ∑ x : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
          ∑ y : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin P,
            (if (∀ j : Fin n,
                ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                  = ∑ i : Fin (n * (m + 1) + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
              then (1 : ℝ) else 0)
        ≤ (20 * n : ℝ) ^ (((n * (n + 1) : ℕ) : ℝ) / 2) *
            (P : ℝ) ^ (2 * (n : ℝ) + 2 * ((n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊) : ℕ) : ℝ) / n
              - ((n : ℝ) + 1) / 2) *
          ∑ x : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊,
            ∑ y : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)) → Fin ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊,
              (if (∀ j : Fin n,
                  ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((x i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1)
                    = ∑ i : Fin (n * m + (⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊)), (((y i).val + 1 : ℕ) : ℝ) ^ ((j : ℕ) + 1))
                then (1 : ℝ) else 0) := by
  sorry

/-- Assembly of `leaf_solution_count_succ` from the trivial bound below the threshold, the
recursive inequality above it, and the exponent arithmetic. -/
theorem leaf_solution_count_succ_split :
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
  rcases lt_or_ge (P : ℝ) ((20 * n : ℝ) ^ (m + 1)) with hsmall | hbig
  · exact small_region n m _ P hn hP hsmall
  · have hP1r : (1 : ℝ) ≤ P := by exact_mod_cast hP
    have hx : (1 : ℝ) ≤ (P : ℝ) ^ (1 - 1 / (n : ℝ)) := by
      apply Real.one_le_rpow hP1r
      rw [sub_nonneg, div_le_one (by exact_mod_cast (by omega : 0 < n))]
      exact_mod_cast (by omega : 1 ≤ n)
    have hP1pos : 1 ≤ ⌊(P : ℝ) ^ (1 - 1 / (n : ℝ))⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
    have hk : ((n * (n + 1) : ℕ) : ℝ) / 4 ≤ ((⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (((n * (n + 1) : ℕ) : ℝ) / 4 + 1)
      linarith
    exact step_arith n m _ _ (P : ℝ) _ _ hn hk hP1r hP1pos
      (Nat.floor_le (by positivity)) (ih _ hP1pos)
      (leaf_vinogradov_recursion n hn m hm P hbig)

/-- Twin: the assembly has exactly the type of the leaf `leaf_solution_count_succ`. -/
example : type_of% @leaf_solution_count_succ := leaf_solution_count_succ_split

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.Recursion

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.Recursion.leaf_solution_count_succ_split
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.Recursion.step_arith
#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.Recursion.small_region
