import Mathlib
import LeanLab.LanguascoPintzZaccagnini2007.Statements
import LeanLab.LanguascoPintzZaccagnini2007.Lemma61

namespace LeanLab.LPZ2007
open Finset Real Filter Topology

/-- OFF ROUTE, U-1633 20261108T0415Z-4325: FALSE, the odd squarefree d below 7 are 1, 3 and 5 with terms 1, 1/2 and 1/12, sum 19/12 above 1.50; no file imports DecompJ1234.
Retired leaf text: small d. -/
theorem small_d_bound : ∑ d ∈ range 7, seriesTerm d ≤ 1.50 := by
  sorry

/-! ### The head sum `d < 7` is exactly `19/12`

Private helpers for `large_d_bound` below: `ξ` and `f` at `1, 3, 5`, and `seriesTerm` at the
seven arguments of `range 7`. -/

private theorem xi_eq (d μ : ℕ) (hμ : 1 ≤ μ) (h : 2 ^ μ ≡ 1 [MOD d])
    (hmin : ∀ k, 1 ≤ k → k < μ → ¬ (2 ^ k ≡ 1 [MOD d])) : xi d = μ := by
  have hmem : μ ∈ {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} := ⟨hμ, h⟩
  show sInf {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} = μ
  refine le_antisymm (Nat.sInf_le hmem) ?_
  rcases Nat.lt_or_ge (sInf {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]}) μ with hlt | hge
  · have hs : sInf {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} ∈
        {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} := Nat.sInf_mem ⟨μ, hmem⟩
    exact absurd hs.2 (hmin _ hs.1 hlt)
  · exact hge

private theorem xi_one : xi 1 = 1 := by
  refine xi_eq 1 1 le_rfl ?_ ?_
  · unfold Nat.ModEq; norm_num
  · intro k hk hlt; omega

private theorem xi_three : xi 3 = 2 := by
  refine xi_eq 3 2 (by norm_num) ?_ ?_
  · unfold Nat.ModEq; norm_num
  · intro k hk hlt
    interval_cases k
    unfold Nat.ModEq
    norm_num

private theorem xi_five : xi 5 = 4 := by
  refine xi_eq 5 4 (by norm_num) ?_ ?_
  · unfold Nat.ModEq; norm_num
  · intro k hk hlt
    interval_cases k <;> (unfold Nat.ModEq; norm_num)

private theorem fd_prime {p : ℕ} (hp : Nat.Prime p) (h2 : 2 < p) : fd p = 1 / ((p : ℝ) - 2) := by
  unfold fd
  rw [hp.primeFactors, Finset.filter_singleton, if_pos h2]
  simp

private theorem fd_one : fd 1 = 1 := by
  unfold fd
  simp

private theorem fd_three : fd 3 = 1 := by
  rw [fd_prime Nat.prime_three (by norm_num)]
  norm_num

private theorem fd_five : fd 5 = 1 / 3 := by
  rw [fd_prime Nat.prime_five (by norm_num)]
  norm_num

private theorem oddSqf_one : OddSqf 1 := ⟨by norm_num, odd_one, squarefree_one⟩

private theorem oddSqf_three : OddSqf 3 := ⟨by norm_num, ⟨1, by norm_num⟩, Nat.prime_three.squarefree⟩

private theorem oddSqf_five : OddSqf 5 := ⟨by norm_num, ⟨2, by norm_num⟩, Nat.prime_five.squarefree⟩

private theorem seriesTerm_one : seriesTerm 1 = 1 := by
  unfold seriesTerm
  rw [if_pos oddSqf_one, fd_one, xi_one]
  norm_num

private theorem seriesTerm_three : seriesTerm 3 = 1 / 2 := by
  unfold seriesTerm
  rw [if_pos oddSqf_three, fd_three, xi_three]
  norm_num

private theorem seriesTerm_five : seriesTerm 5 = 1 / 12 := by
  unfold seriesTerm
  rw [if_pos oddSqf_five, fd_five, xi_five]
  norm_num

private theorem seriesTerm_zero : seriesTerm 0 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.1 (by norm_num)

private theorem seriesTerm_two : seriesTerm 2 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.2.1 (by decide)

private theorem seriesTerm_four : seriesTerm 4 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.2.2 (by
    rw [Nat.squarefree_iff_prime_squarefree]
    push_neg
    exact ⟨2, Nat.prime_two, by norm_num⟩)

private theorem seriesTerm_six : seriesTerm 6 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.2.1 (by decide)

/-- The head of the series at `d = 7`: `1 + 1/2 + 1/12 = 19/12`. -/
private theorem sum_range_seven_eq : ∑ d ∈ range 7, seriesTerm d = 19 / 12 := by
  rw [show (7:ℕ) = 6 + 1 from rfl, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
  rw [seriesTerm_one, seriesTerm_two, seriesTerm_three, seriesTerm_four, seriesTerm_five,
    seriesTerm_six, seriesTerm_zero]
  norm_num

/-- LEAF large d. Proved from the file's own shift identity, the exact head `19/12`, and the cited
`lpz_lemma61_bound`: `1.9378 - 19/12 = 0.35446… ≤ 0.4378`. The statement is unchanged. -/
theorem large_d_bound : ∑' d, seriesTerm (d + 7) ≤ 0.4378 := by
  have hsplit : ∑' d, seriesTerm d
      = ∑ d ∈ range 7, seriesTerm d + ∑' d, seriesTerm (d + 7) :=
    (Summable.sum_add_tsum_nat_add 7 lemma61_proved).symm
  have hb : ∑' d, seriesTerm d ≤ 1.9378 := lpz_lemma61_bound
  have hsmall : ∑ d ∈ range 7, seriesTerm d = 19 / 12 := sum_range_seven_eq
  linarith

/-- LEAF shift. -/
theorem tsum_eq_sum_add_tsum_shift :
    ∑' d, seriesTerm d = ∑ d ∈ range 7, seriesTerm d + ∑' d, seriesTerm (d + 7) := by
  exact (Summable.sum_add_tsum_nat_add 7 lemma61_proved).symm

theorem lpz_lemma61_bound_assembly : Lemma61Bound := by
  rw [Lemma61Bound, tsum_eq_sum_add_tsum_shift]
  have h1 := small_d_bound
  have h2 := large_d_bound
  linarith


end LeanLab.LPZ2007
