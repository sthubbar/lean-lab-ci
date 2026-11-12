import Mathlib
import LeanLab.ExceptionalSet.State1539

/-!
Upstream supply of the elementary steps of P0082 page 362, first sentence of the proof of Lemma 7,
for `DecompJ200.leaf_major_coefficient_lower`.
Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, https://doi.org/10.5802/aif.1621.

Every declaration here is a copy of a proved declaration further down the import graph, placed
here so that `DecompJ200` can import it without an import cycle:
`evenAdjacent`, `adjacent_sum` and `bad_pair_count` copy `Adjacent446`,
`count_of_tail_and_moment` copies `Decomp371b`, and `odd_bad_count` copies `OddMoment446`.

AI wrote this Lean code. Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.CoeffSupplyJ200

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu nuOdd)

/-- Copy of `Adjacent446.evenAdjacent`: the even one of `ν_n, ν_n + 1`, P0082 pages 354 and 362. -/
noncomputable def evenAdjacent (γ : ℝ) (n : ℕ) : ℤ :=
  if Even (nu γ n) then nu γ n else nu γ n + 1

/-- Copy of `Adjacent446.adjacent_sum`, P0082 page 362: the even and the odd coefficient sum to
the two adjacent coefficients. -/
theorem adjacent_sum (f : ℤ → ℂ) (γ : ℝ) (n : ℕ) :
    f (evenAdjacent γ n) + f (nuOdd γ n) = f (nu γ n) + f (nu γ n + 1) := by
  by_cases he : Even (nu γ n)
  · have ho : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr he
    simp [evenAdjacent, nuOdd, he, ho]
  · have ho : Odd (nu γ n) := Int.not_even_iff_odd.mp he
    simp [evenAdjacent, nuOdd, he, ho, add_comm]

/-- Copy of `Adjacent446.bad_pair_count`, P0082 page 362: a small real part of the sum forces a
small first real part or a large second norm. -/
theorem bad_pair_count {ι : Type*} (s : Finset ι) (f g : ι → ℂ) (T : ℝ) :
    (s.filter (fun n => (f n + g n).re < T)).card ≤
      (s.filter (fun n => (f n).re < 2 * T)).card +
        (s.filter (fun n => T < ‖g n‖)).card := by
  classical
  have hsub : s.filter (fun n => (f n + g n).re < T) ⊆
      s.filter (fun n => (f n).re < 2 * T) ∪ s.filter (fun n => T < ‖g n‖) := by
    intro n hn
    simp only [mem_filter, mem_union] at hn ⊢
    by_cases hf : (f n).re < 2 * T
    · exact Or.inl ⟨hn.1, hf⟩
    · right
      refine ⟨hn.1, ?_⟩
      have hr := (abs_le.mp (Complex.abs_re_le_norm (g n))).1
      simp only [Complex.add_re] at hn
      by_contra hg
      have hff := le_of_not_gt hf
      have hgg := le_of_not_gt hg
      linarith
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- Copy of `Decomp371b.count_of_tail_and_moment`: Chebyshev's inequality for a second moment. -/
theorem count_of_tail_and_moment (s : Finset ℕ) (f g : ℕ → ℂ)
    (T A : ℝ) (hT : 0 < T)
    (htail : ∀ n ∈ s, ‖f n - g n‖ ≤ T / 2)
    (hmoment : (∑ n ∈ s, ‖g n‖ ^ 2) ≤ A) :
    (((s.filter (fun n => T < ‖f n‖)).card : ℝ) * (T / 2) ^ 2) ≤ A := by
  classical
  let bad := s.filter (fun n => T < ‖f n‖)
  have hlarge : ∀ n ∈ bad, (T / 2) ^ 2 ≤ ‖g n‖ ^ 2 := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hnf⟩
    have hnorm : ‖f n‖ ≤ ‖f n - g n‖ + ‖g n‖ := norm_le_norm_sub_add _ _
    have hg : T / 2 ≤ ‖g n‖ := by linarith [htail n hns]
    exact pow_le_pow_left₀ (by positivity) hg 2
  calc
    _ ≤ ∑ n ∈ bad, ‖g n‖ ^ 2 := by
      simpa only [nsmul_eq_mul] using
        Finset.card_nsmul_le_sum bad (fun n => ‖g n‖ ^ 2) ((T / 2) ^ 2) hlarge
    _ ≤ ∑ n ∈ s, ‖g n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _)
    _ ≤ A := hmoment

/-- Copy of `OddMoment446.odd_bad_count`, P0082 page 362, Lemma 6 as used in the proof of
Lemma 7: a second moment with saving `ℰ^{-1/3}` controls the odd coefficient at a fixed multiple of
the threshold `X ℰ^{-1/10}` outside `O(N ℰ^{-1/12})` indices. -/
theorem odd_bad_count (s : Finset ℕ) (f : ℕ → ℂ)
    (c B X E : ℝ) (N : ℕ) (hc : 0 < c) (hB : 0 ≤ B) (hX : 0 < X) (hE : 1 ≤ E)
    (hm : (∑ n ∈ s, ‖f n‖ ^ 2) ≤ B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) :
    ((s.filter (fun n => c / 2 * X * E ^ (-(1 / 10 : ℝ)) < ‖f n‖)).card : ℝ) ≤
      (16 * B / c ^ 2) * N * E ^ (-(1 / 12 : ℝ)) := by
  classical
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  let T := c / 2 * X * E ^ (-(1 / 10 : ℝ))
  have hT : 0 < T := by dsimp [T]; positivity
  have hh := count_of_tail_and_moment s f f T
    (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) hT
    (fun n _ => by simpa using (half_pos hT).le) hm
  have hp : E ^ (-(1 / 3 : ℝ)) ≤
      E ^ (-(1 / 12 : ℝ)) * (E ^ (-(1 / 10 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE0.le, ← Real.rpow_add hE0]
    exact Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hf : B * (N : ℝ) * X ^ 2 * E ^ (-(1 / 3 : ℝ)) ≤
      ((16 * B / c ^ 2) * N * E ^ (-(1 / 12 : ℝ))) * (T / 2) ^ 2 := by
    calc
      _ ≤ B * N * X ^ 2 * (E ^ (-(1 / 12 : ℝ)) * (E ^ (-(1 / 10 : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by
        dsimp [T]
        field_simp [hc.ne']
        <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp (hh.trans hf)

end LeanLab.ExceptionalSet.CoeffSupplyJ200
