import LeanLab.LanguascoPintzZaccagnini2007.Lemma61

/-!
# P0045 Audit1620: the bound 1.50 of a novelty report is false

AI wrote this Lean code, unit U-1620, run 20261105T0803Z-23816. Binary Goldbach is OPEN.
Refutes research/novelty/LanguascoPintzZaccagnini2007-20261102T1240Z.md section 6 Result 1 and Rank 2,
which say every finite sum of series (26) is below 1.50. This touches no lab statement and no paper.
It does not touch `lpz_lemma61_bound`: scripts/lpz_romanov_sum.py gives partial sum 1.9366119 to 1e7.
-/

namespace LeanLab.LPZ2007.Audit1620

open LeanLab.LPZ2007

private theorem xi_of_isLeast {d m : ℕ} (hm : 1 ≤ m) (hd : 2 ^ m ≡ 1 [MOD d])
    (hl : ∀ j, 1 ≤ j → j < m → ¬ 2 ^ j ≡ 1 [MOD d]) : xi d = m := by
  have h : IsLeast {μ : ℕ | 1 ≤ μ ∧ 2 ^ μ ≡ 1 [MOD d]} m := by
    refine ⟨⟨hm, hd⟩, ?_⟩
    rintro j ⟨hj1, hj2⟩
    by_contra hlt
    exact hl j hj1 (not_le.mp hlt) hj2
  exact h.csInf_eq

theorem term_one : seriesTerm 1 = 1 := by
  have hx : xi 1 = 1 := xi_of_isLeast le_rfl (by decide) (by intro j h1 h2; omega)
  have hs : OddSqf 1 := ⟨by norm_num, by decide, squarefree_one⟩
  simp [seriesTerm, hs, hx, fd]

theorem term_three : seriesTerm 3 = 1 / 2 := by
  have hx : xi 3 = 2 := xi_of_isLeast (by norm_num) (by decide) (by
    intro j h1 h2
    obtain rfl : j = 1 := by omega
    decide)
  have hs : OddSqf 3 := ⟨by norm_num, by decide, Nat.prime_three.prime.squarefree⟩
  have hf : fd 3 = 1 := by
    unfold fd
    rw [Nat.prime_three.primeFactors]
    norm_num [Finset.filter_singleton]
  simp [seriesTerm, hs, hx, hf]

theorem term_seven : seriesTerm 7 = 1 / 15 := by
  have h7 : Nat.Prime 7 := by norm_num
  have hx : xi 7 = 3 := xi_of_isLeast (by norm_num) (by decide) (by
    intro j h1 h2
    interval_cases j <;> decide)
  have hs : OddSqf 7 := ⟨by norm_num, by decide, h7.prime.squarefree⟩
  have hf : fd 7 = 1 / 5 := by
    unfold fd
    rw [h7.primeFactors]
    norm_num [Finset.filter_singleton]
  simp only [seriesTerm, hs, if_true, hx, hf]
  norm_num

/-- REFUTATION of the report's claim, on the set `{1, 3, 7}`: the sum is `47/30`. -/
theorem report_bound_false : ¬ ∀ S : Finset ℕ, ∑ d ∈ S, seriesTerm d < 3 / 2 := by
  intro h
  have := h {1, 3, 7}
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    term_one, term_three, term_seven] at this
  norm_num at this

end LeanLab.LPZ2007.Audit1620

#print axioms LeanLab.LPZ2007.Audit1620.report_bound_false
