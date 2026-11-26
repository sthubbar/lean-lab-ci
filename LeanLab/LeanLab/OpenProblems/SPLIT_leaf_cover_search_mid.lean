import LeanLab.OpenProblems.Erdos273

/-!
# SPLIT of `leaf_cover_search_mid`, folder OpenProblems, module SPLIT_leaf_card_lt_of_lcm_lt

AI wrote this Lean code. Goldbach is OPEN and Erdős Problem 273 is OPEN; nothing here claims
progress on either.

Target, unchanged and not restated in its own file: a covering system with distinct moduli
`p - 1`, `p ≥ 5` prime, whose lcm lies in `[1965600, 4600000)` has fewer than `100` congruences.

The moduli of such a system are divisors of its lcm `L` of the shape `p - 1`. So the target splits
into a counting step and a search step:

* counting, no covering hypothesis: for `L` in the window outside an explicit list of `33` values,
  `L` has fewer than `100` divisors of the shape, so the system has fewer than `100` congruences;
* search: for `L` in that list the congruence search itself is needed.

The list is the set of `L` in the window with at least `100` divisors `d` of `L` with `d + 1` prime,
`d ≥ 4`, and with reciprocal sum of those divisors at least `1`; it was computed by a lab Python
count over every `L` in the window, where no value fails the reciprocal sum.
The assembly `leaf_cover_search_mid_split` proves the target statement from the two LEAFs with no `sorry`.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-- LEAF: counting step of `leaf_cover_search_mid`. For `1965600 ≤ L < 4600000` outside the listed `33` lcm values,
a finite set of divisors of `L` of the shape `p - 1`, `p ≥ 5` prime, has fewer than `100` members.
Class HARD: a finite divisor count over the window with no covering in it, the same kind of
claim as `leaf_candidate_count_small` on a higher range; the listed values are exactly the ones where
the count reaches `100`. -/
theorem leaf_count_mid_window (L : ℕ) (hlo : 1965600 ≤ L) (hhi : L < 4600000)
    (hlist : L ∉ ({1965600, 2162160, 2217600, 2227680, 2494800, 2570400, 2751840, 2827440, 2882880, 2948400,
    3160080, 3276000, 3326400, 3341520, 3598560, 3603600, 3734640, 3769920, 3825360, 3855600,
    3880800, 3931200, 3991680, 4158000, 4213440, 4233600, 4241160, 4309200, 4324320, 4435200,
    4455360, 4520880, 4586400} : Finset ℕ))
    (T : Finset ℕ) (hdvd : ∀ d ∈ T, d ∣ L)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- LEAF: search step of `leaf_cover_search_mid` on the listed lcm values. A covering system with distinct
moduli `p - 1`, `p ≥ 5` prime, whose lcm is one of the `33` listed values, has fewer than `100`
congruences. Class HARD: the congruence search over the residue data for these `33` lcm values,
a proof-carrying certificate per value. -/
theorem leaf_search_mid_list {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlist : S.lcm Prod.fst ∈ ({1965600, 2162160, 2217600, 2227680, 2494800, 2570400, 2751840, 2827440, 2882880, 2948400,
    3160080, 3276000, 3326400, 3341520, 3598560, 3603600, 3734640, 3769920, 3825360, 3855600,
    3880800, 3931200, 3991680, 4158000, 4213440, 4233600, 4241160, 4309200, 4324320, 4435200,
    4455360, 4520880, 4586400} : Finset ℕ)) :
    S.card < 100 := by
  sorry

/-- The statement of `leaf_cover_search_mid`, assembled from the two LEAFs with no `sorry`. -/
theorem leaf_cover_search_mid_split {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 1965600 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 4600000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  by_cases hl : S.lcm Prod.fst ∈ ({1965600, 2162160, 2217600, 2227680, 2494800, 2570400, 2751840, 2827440, 2882880, 2948400,
    3160080, 3276000, 3326400, 3341520, 3598560, 3603600, 3734640, 3769920, 3825360, 3855600,
    3880800, 3931200, 3991680, 4158000, 4213440, 4233600, 4241160, 4309200, 4324320, 4435200,
    4455360, 4520880, 4586400} : Finset ℕ)
  · exact leaf_search_mid_list hS hi hp hl
  · have hdvd : ∀ d ∈ S.image Prod.fst, d ∣ S.lcm Prod.fst := by
      intro d hd
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.dvd_lcm (f := Prod.fst) hs
    have hform : ∀ d ∈ S.image Prod.fst, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1 := by
      intro d hd
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
      exact hp s hs
    have hlt := leaf_count_mid_window (S.lcm Prod.fst) hlo hhi hl (S.image Prod.fst) hdvd hform
    rwa [Finset.card_image_of_injOn hi] at hlt

end LeanLab.OpenProblems.Novelty1615

#print axioms LeanLab.OpenProblems.Novelty1615.leaf_cover_search_mid_split
