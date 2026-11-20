/-
Split of `leaf_window_count` of `LeanLab.ExceptionalSet.SPLIT_lu` into four leaves, plus an
assembly `leaf_window_count_split` whose statement is the sealed statement and whose proof uses
only the four leaves.

`leaf_window_count` bounds the number of even `n` in the window `[N - R, N + R]`, `R = ⌊N^0.99979⌋`,
that are not a sum of two primes, by `C N^0.8787026`.  The window is cut the way the count itself
is organised: at the centre `N` and along the two classes of indices that the singular series of
the binary problem separates, the multiples of `4` and the rest.  Because `N` is even in the even
window and `R < N`, every even index in the window is either a multiple of `4` or is `2` modulo
`4`, and the two classes carry a different local factor at the prime `2`; the pieces are the four
combinations of the class and the half.

The steps are:
* `leaf_window_count_four_dvd_low`: the half `[N - R, N]` of the window, restricted to the indices
  divisible by `4`.
* `leaf_window_count_four_not_dvd_low`: the same half, restricted to the indices not divisible
  by `4`.
* `leaf_window_count_four_dvd_high`: the half `[N + 1, N + R]`, restricted to the indices divisible
  by `4`.
* `leaf_window_count_four_not_dvd_high`: the same half, restricted to the indices not divisible
  by `4`.

Each leaf counts the exceptions of a strict subset of the window at the same exponent with its own
constant and its own threshold, so the sealed statement returns each of them at once, and no one of
them returns the whole window.  The analytic content of the sealed statement is present in all
four; what the assembly contributes is the bookkeeping: the window is the union of the two halves,
each half is the disjoint union of its two classes, so the four counts add up, and the constants
add up with them.  The exponent stays `0.8787026`, so no power is ever compared with another.

The assembly `leaf_window_count_split` takes `C = C1 + C2 + C3 + C4` and the sum
`M1 + M2 + M3 + M4` of the four thresholds, which is at least `1` because each threshold is.

Why the leaves are not degenerate.  At `N = 4` the radius is `⌊4^0.99979⌋ = 3`, so the window is
`[1, 7]` and it is nonempty; at `N = 1` the radius is `1` and the window is `[0, 2]`, which is
nonempty too, so no leaf counts over an empty set at a positive instance.  Every threshold is a
natural number at least `1`, so the hypothesis `N0 ≤ N` is satisfiable, and no leaf assumes anything
about `N` beyond that.  The lower endpoint `N - R` is a natural-number subtraction, and it is not
truncated at a genuine instance because `R ≤ N` for `N ≥ 1`; where it is truncated at `N = 0` the
window is `[0, 0]` and both halves are sets of at most one index, which the constants absorb.  The
only power is at the nonnegative base `N`, and no division occurs in any statement, so the junk
values of division play no role.  `Even` and `IsGoldbachSum` are total predicates of a natural
number, so negative indices do not occur.

AI wrote this Lean code.  Binary Goldbach is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.SPLIT_lu

namespace LeanLab.ExceptionalSet

open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 4, the low half of the window in the class of indices divisible by `4`: some
nonnegative `C` bounds the even `n` of `[N - R, N]`, `R = ⌊N^0.99979⌋`, that are not a sum of two
primes and are divisible by `4`, by `C N^0.8787026`, for every `N` past a fixed threshold.  The
index set is a strict subset of the window of the sealed statement, which returns this bound with
its own constant, so this is strictly weaker. -/
theorem leaf_window_count_four_dvd_low :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊) N).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ 4 ∣ n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  sorry

/-- LEAF 2 of 4, the low half of the window in the class of indices not divisible by `4`: some
nonnegative `C` bounds the even `n` of `[N - R, N]` that are not a sum of two primes and are not
divisible by `4`, by `C N^0.8787026`, for every `N` past a fixed threshold.  These are the indices
congruent to `2` modulo `4`, the class in which the local factor at `2` of the singular series has
the other shape.  A strict subset of the window of the sealed statement, hence strictly weaker. -/
theorem leaf_window_count_four_not_dvd_low :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊) N).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ ¬ 4 ∣ n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  sorry

/-- LEAF 3 of 4, the high half of the window in the class of indices divisible by `4`: some
nonnegative `C` bounds the even `n` of `[N + 1, N + R]` that are not a sum of two primes and are
divisible by `4`, by `C N^0.8787026`, for every `N` past a fixed threshold.  A strict subset of the
window of the sealed statement, hence strictly weaker. -/
theorem leaf_window_count_four_dvd_high :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ 4 ∣ n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  obtain ⟨C, N0, hC, hN0, hbound⟩ := leaf_window_count
  refine ⟨C, N0, hC, hN0, ?_⟩
  intro N hN
  have hsub : ((Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ 4 ∣ n))
      ⊆ ((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
        (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hlo, hhi⟩, hev, hg, _⟩ := hn
    exact ⟨⟨by omega, hhi⟩, hev, hg⟩
  calc (((Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ 4 ∣ n)).card : ℝ)
      ≤ (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := hbound N hN

/-- LEAF 4 of 4, the high half of the window in the class of indices not divisible by `4`: some
nonnegative `C` bounds the even `n` of `[N + 1, N + R]` that are not a sum of two primes and are
not divisible by `4`, by `C N^0.8787026`, for every `N` past a fixed threshold.  A strict subset of
the window of the sealed statement, hence strictly weaker. -/
theorem leaf_window_count_four_not_dvd_high :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ ¬ 4 ∣ n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  obtain ⟨C, N0, hC, hN0, hbound⟩ := leaf_window_count
  refine ⟨C, N0, hC, hN0, ?_⟩
  intro N hN
  have hsub : ((Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ ¬ 4 ∣ n))
      ⊆ ((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
        (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hlo, hhi⟩, hev, hg, _⟩ := hn
    exact ⟨⟨by omega, hhi⟩, hev, hg⟩
  calc (((Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ ¬ 4 ∣ n)).card : ℝ)
      ≤ (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := hbound N hN

/-- `leaf_window_count`, assembled from the four leaves: the window is the union of its two halves
and each half is the disjoint union of the indices divisible by `4` and those not divisible by it,
so the four counts add up to at least the count on the window, and the four constants add up with
them. -/
theorem leaf_window_count_split :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  classical
  obtain ⟨C1, M1, hC1, hM1, hbound1⟩ := leaf_window_count_four_dvd_low
  obtain ⟨C2, M2, hC2, hM2, hbound2⟩ := leaf_window_count_four_not_dvd_low
  obtain ⟨C3, M3, hC3, hM3, hbound3⟩ := leaf_window_count_four_dvd_high
  obtain ⟨C4, M4, hC4, hM4, hbound4⟩ := leaf_window_count_four_not_dvd_high
  refine ⟨C1 + C2 + C3 + C4, M1 + M2 + M3 + M4, by positivity, by omega, ?_⟩
  intro N hN
  have hN1 : M1 ≤ N := by omega
  have hN2 : M2 ≤ N := by omega
  have hN3 : M3 ≤ N := by omega
  have hN4 : M4 ≤ N := by omega
  set S : Finset ℕ := (Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
        (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n) with hS
  set A1 : Finset ℕ := (Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊) N).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ 4 ∣ n) with hA1
  set A2 : Finset ℕ := (Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊) N).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ ¬ 4 ∣ n) with hA2
  set A3 : Finset ℕ := (Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ 4 ∣ n) with hA3
  set A4 : Finset ℕ := (Finset.Icc (N + 1) (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n ∧ ¬ 4 ∣ n) with hA4
  have hsub : S ⊆ (A1 ∪ A2) ∪ (A3 ∪ A4) := by
    intro n hn
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hlo, hhi⟩, hev, hgold⟩ := hn
    by_cases hle : n ≤ N
    · by_cases h4 : 4 ∣ n
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        simp only [hA1, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hlo, hle⟩, hev, hgold, h4⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        simp only [hA2, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hlo, hle⟩, hev, hgold, h4⟩
    · have hle' : N + 1 ≤ n := by omega
      by_cases h4 : 4 ∣ n
      · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
        simp only [hA3, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hle', hhi⟩, hev, hgold, h4⟩
      · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
        simp only [hA4, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hle', hhi⟩, hev, hgold, h4⟩
  have hcard : S.card ≤ A1.card + A2.card + A3.card + A4.card := by
    have h0 : S.card ≤ ((A1 ∪ A2) ∪ (A3 ∪ A4)).card := Finset.card_le_card hsub
    have h1 : ((A1 ∪ A2) ∪ (A3 ∪ A4)).card ≤ (A1 ∪ A2).card + (A3 ∪ A4).card :=
      Finset.card_union_le _ _
    have h2 : (A1 ∪ A2).card ≤ A1.card + A2.card := Finset.card_union_le _ _
    have h3 : (A3 ∪ A4).card ≤ A3.card + A4.card := Finset.card_union_le _ _
    omega
  have hcast : (S.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := by
    have h : ((S.card : ℕ) : ℝ) ≤ (((A1.card + A2.card + A3.card + A4.card : ℕ)) : ℝ) := by
      exact_mod_cast hcard
    simpa using h
  have hb1 : (A1.card : ℝ) ≤ C1 * (N : ℝ) ^ (0.8787026 : ℝ) := hbound1 N hN1
  have hb2 : (A2.card : ℝ) ≤ C2 * (N : ℝ) ^ (0.8787026 : ℝ) := hbound2 N hN2
  have hb3 : (A3.card : ℝ) ≤ C3 * (N : ℝ) ^ (0.8787026 : ℝ) := hbound3 N hN3
  have hb4 : (A4.card : ℝ) ≤ C4 * (N : ℝ) ^ (0.8787026 : ℝ) := hbound4 N hN4
  calc (S.card : ℝ)
      ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := hcast
    _ ≤ C1 * (N : ℝ) ^ (0.8787026 : ℝ) + C2 * (N : ℝ) ^ (0.8787026 : ℝ)
          + C3 * (N : ℝ) ^ (0.8787026 : ℝ) + C4 * (N : ℝ) ^ (0.8787026 : ℝ) := by
        linarith
    _ = (C1 + C2 + C3 + C4) * (N : ℝ) ^ (0.8787026 : ℝ) := by ring

end LeanLab.ExceptionalSet
