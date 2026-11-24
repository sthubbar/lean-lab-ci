import LeanLab.LanguascoPintzZaccagnini2007.Statements

/-!
FALSIFY unit `LanguascoPintzZaccagnini2007/DecompJ1234`, CLOUD S101 burst-20261122.

The statement of `small_d_bound` in `DecompJ1234.lean` is FALSE as written. The odd squarefree
`d` below `7` are `1`, `3` and `5`, with `seriesTerm` values `1`, `1/2` and `1/12`, since
`f(1) = 1, ξ(1) = 1`, `f(3) = 1, ξ(3) = 2`, `f(5) = 1/3, ξ(5) = 4`. The head sum is `19/12`,
which exceeds `1.50`. Source: P0045 page 9, series (26) and the definitions in Statements.lean.

The helpers repeat the private helpers of `DecompJ1234.lean` under new names, since private
declarations are not visible here and this file must not import the file that holds the `sorry`.
The statement of `small_d_bound` is not changed. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007
open Finset Real

private theorem xi_eqF1234 (d μ : ℕ) (hμ : 1 ≤ μ) (h : 2 ^ μ ≡ 1 [MOD d])
    (hmin : ∀ k, 1 ≤ k → k < μ → ¬ (2 ^ k ≡ 1 [MOD d])) : xi d = μ := by
  have hmem : μ ∈ {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} := ⟨hμ, h⟩
  show sInf {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} = μ
  refine le_antisymm (Nat.sInf_le hmem) ?_
  rcases Nat.lt_or_ge (sInf {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]}) μ with hlt | hge
  · have hs : sInf {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} ∈
        {m : ℕ | 1 ≤ m ∧ 2 ^ m ≡ 1 [MOD d]} := Nat.sInf_mem ⟨μ, hmem⟩
    exact absurd hs.2 (hmin _ hs.1 hlt)
  · exact hge

private theorem xi_oneF1234 : xi 1 = 1 := by
  refine xi_eqF1234 1 1 le_rfl ?_ ?_
  · unfold Nat.ModEq; norm_num
  · intro k hk hlt; omega

private theorem xi_threeF1234 : xi 3 = 2 := by
  refine xi_eqF1234 3 2 (by norm_num) ?_ ?_
  · unfold Nat.ModEq; norm_num
  · intro k hk hlt
    interval_cases k
    unfold Nat.ModEq
    norm_num

private theorem xi_fiveF1234 : xi 5 = 4 := by
  refine xi_eqF1234 5 4 (by norm_num) ?_ ?_
  · unfold Nat.ModEq; norm_num
  · intro k hk hlt
    interval_cases k <;> (unfold Nat.ModEq; norm_num)

private theorem fd_primeF1234 {p : ℕ} (hp : Nat.Prime p) (h2 : 2 < p) : fd p = 1 / ((p : ℝ) - 2) := by
  unfold fd
  rw [hp.primeFactors, Finset.filter_singleton, if_pos h2]
  simp

private theorem fd_oneF1234 : fd 1 = 1 := by
  unfold fd
  simp

private theorem fd_threeF1234 : fd 3 = 1 := by
  rw [fd_primeF1234 Nat.prime_three (by norm_num)]
  norm_num

private theorem fd_fiveF1234 : fd 5 = 1 / 3 := by
  rw [fd_primeF1234 Nat.prime_five (by norm_num)]
  norm_num

private theorem oddSqf_oneF1234 : OddSqf 1 := ⟨by norm_num, odd_one, squarefree_one⟩

private theorem oddSqf_threeF1234 : OddSqf 3 := ⟨by norm_num, ⟨1, by norm_num⟩, Nat.prime_three.squarefree⟩

private theorem oddSqf_fiveF1234 : OddSqf 5 := ⟨by norm_num, ⟨2, by norm_num⟩, Nat.prime_five.squarefree⟩

private theorem seriesTerm_oneF1234 : seriesTerm 1 = 1 := by
  unfold seriesTerm
  rw [if_pos oddSqf_oneF1234, fd_oneF1234, xi_oneF1234]
  norm_num

private theorem seriesTerm_threeF1234 : seriesTerm 3 = 1 / 2 := by
  unfold seriesTerm
  rw [if_pos oddSqf_threeF1234, fd_threeF1234, xi_threeF1234]
  norm_num

private theorem seriesTerm_fiveF1234 : seriesTerm 5 = 1 / 12 := by
  unfold seriesTerm
  rw [if_pos oddSqf_fiveF1234, fd_fiveF1234, xi_fiveF1234]
  norm_num

private theorem seriesTerm_zeroF1234 : seriesTerm 0 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.1 (by norm_num)

private theorem seriesTerm_twoF1234 : seriesTerm 2 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.2.1 (by decide)

private theorem seriesTerm_fourF1234 : seriesTerm 4 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.2.2 (by
    rw [Nat.squarefree_iff_prime_squarefree]
    push_neg
    exact ⟨2, Nat.prime_two, by norm_num⟩)

private theorem seriesTerm_sixF1234 : seriesTerm 6 = 0 := by
  unfold seriesTerm
  rw [if_neg]
  intro h
  exact absurd h.2.1 (by decide)

private theorem sum_range_seven_eqF1234 : ∑ d ∈ range 7, seriesTerm d = 19 / 12 := by
  rw [show (7:ℕ) = 6 + 1 from rfl, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
  rw [seriesTerm_oneF1234, seriesTerm_twoF1234, seriesTerm_threeF1234, seriesTerm_fourF1234, seriesTerm_fiveF1234,
    seriesTerm_sixF1234, seriesTerm_zeroF1234]
  norm_num

/-- The head of series (26) over `d < 7` is exactly `19/12 = 1 + 1/2 + 1/12`. -/
theorem sum_range_seven_eq_1234 : ∑ d ∈ range 7, seriesTerm d = 19 / 12 :=
  sum_range_seven_eqF1234

/-- FALSE flag: the statement of `small_d_bound` of `DecompJ1234.lean`, word for word, is false,
since the head sum is `19/12 > 1.50`. -/
theorem small_d_bound_false : ¬ (∑ d ∈ range 7, seriesTerm d ≤ 1.50) := by
  rw [sum_range_seven_eq_1234]
  norm_num

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.sum_range_seven_eq_1234
#print axioms LeanLab.LPZ2007.small_d_bound_false
