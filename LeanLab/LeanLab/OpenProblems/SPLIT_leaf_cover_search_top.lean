import LeanLab.OpenProblems.Erdos273

/-!
# SPLIT of `leaf_cover_search_top`, folder OpenProblems, module SPLIT_leaf_card_lt_of_lcm_lt

AI wrote this Lean code. Goldbach is OPEN and Erdős Problem 273 is OPEN; nothing here claims
progress on either.

Target, unchanged and not restated in its own file: a covering system with distinct moduli
`p - 1`, `p ≥ 5` prime, whose lcm lies in `[4600000, 8000000)`, and other than the four lcm values `5012280`, `7022400`, `7425600`, `7876440` that the reciprocal test handles, has fewer than `100` congruences.

The moduli of such a system are divisors of its lcm `L` of the shape `p - 1`. So the target splits
into a counting step and a search step:

* counting, no covering hypothesis: for `L` in the window outside an explicit list of `91` values,
  `L` has fewer than `100` divisors of the shape, so the system has fewer than `100` congruences;
* search: for `L` in that list the congruence search itself is needed.

The list is the set of `L` in the window with at least `100` divisors `d` of `L` with `d + 1` prime,
`d ≥ 4`, and with reciprocal sum of those divisors at least `1`; it was computed by a lab Python
count over every `L` in the window and the four reciprocal-test values are excluded from it.
The assembly `leaf_cover_search_top_split` proves the target statement from the two LEAFs with no `sorry`.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-- Every member of `T` is an admissible divisor for `L`.  This isolates the arithmetic
bookkeeping needed by the finite counting step. -/
private lemma top_candidate_subset (L : ℕ) (T : Finset ℕ) (hLpos : 0 < L)
    (hdvd : ∀ d ∈ T, d ∣ L)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T ⊆ (Nat.divisors L).filter (fun d => 4 ≤ d ∧ (d + 1).Prime) := by
  intro d hdT
  obtain ⟨p, hp, h5, rfl⟩ := hform d hdT
  refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd (p - 1) hdT, hLpos.ne'⟩, ?_, ?_⟩
  · omega
  · rw [Nat.sub_add_cancel h5]
    exact hp

/-- LEAF: counting step of `leaf_cover_search_top`. For `4600000 ≤ L < 8000000` outside the listed `91` lcm values, and outside the four reciprocal-test values,
a finite set of divisors of `L` of the shape `p - 1`, `p ≥ 5` prime, has fewer than `100` members.
Class HARD: a finite divisor count over the window with no covering in it, the same kind of
claim as `leaf_candidate_count_small` on a higher range; the listed values are exactly the ones where
the count reaches `100` with reciprocal sum at least `1`. -/
theorem leaf_count_top_window (L : ℕ) (hlo : 4600000 ≤ L) (hhi : L < 8000000)
    (hlist : L ∉ ({4656960, 4712400, 4717440, 4804800, 4883760, 4914000, 4979520, 4989600, 5045040, 5100480,
    5140800, 5155920, 5241600, 5250960, 5266800, 5322240, 5397840, 5405400, 5443200, 5503680,
    5544000, 5569200, 5654880, 5745600, 5765760, 5821200, 5896800, 5911920, 5987520, 5997600,
    6006000, 6027840, 6048000, 6098400, 6126120, 6153840, 6168960, 6177600, 6209280, 6224400,
    6289920, 6320160, 6350400, 6375600, 6426000, 6431040, 6486480, 6511680, 6552000, 6597360,
    6652800, 6683040, 6846840, 6854400, 6874560, 6879600, 6894720, 6955200, 6985440, 7001280,
    7030800, 7068600, 7076160, 7197120, 7207200, 7257600, 7272720, 7318080, 7338240, 7373520,
    7413120, 7454160, 7469280, 7484400, 7534800, 7539840, 7567560, 7600320, 7620480, 7650720,
    7660800, 7687680, 7711200, 7761600, 7796880, 7817040, 7862400, 7882560, 7900200, 7927920,
    7983360} : Finset ℕ))
    (hout : L ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ))
    (T : Finset ℕ) (hdvd : ∀ d ∈ T, d ∣ L)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  have hsub : T ⊆ (Nat.divisors L).filter (fun d => 4 ≤ d ∧ (d + 1).Prime) :=
    top_candidate_subset L T (by omega) hdvd hform
  have hcard : T.card ≤ ((Nat.divisors L).filter (fun d => 4 ≤ d ∧ (d + 1).Prime)).card :=
    Finset.card_le_card hsub
  sorry

/-- LEAF: search step of `leaf_cover_search_top` on the listed lcm values. A covering system with distinct
moduli `p - 1`, `p ≥ 5` prime, whose lcm is one of the `91` listed values, has fewer than `100`
congruences. Class HARD: the congruence search over the residue data for these `91` lcm values,
a proof-carrying certificate per value. -/
theorem leaf_search_top_list {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlist : S.lcm Prod.fst ∈ ({4656960, 4712400, 4717440, 4804800, 4883760, 4914000, 4979520, 4989600, 5045040, 5100480,
    5140800, 5155920, 5241600, 5250960, 5266800, 5322240, 5397840, 5405400, 5443200, 5503680,
    5544000, 5569200, 5654880, 5745600, 5765760, 5821200, 5896800, 5911920, 5987520, 5997600,
    6006000, 6027840, 6048000, 6098400, 6126120, 6153840, 6168960, 6177600, 6209280, 6224400,
    6289920, 6320160, 6350400, 6375600, 6426000, 6431040, 6486480, 6511680, 6552000, 6597360,
    6652800, 6683040, 6846840, 6854400, 6874560, 6879600, 6894720, 6955200, 6985440, 7001280,
    7030800, 7068600, 7076160, 7197120, 7207200, 7257600, 7272720, 7318080, 7338240, 7373520,
    7413120, 7454160, 7469280, 7484400, 7534800, 7539840, 7567560, 7600320, 7620480, 7650720,
    7660800, 7687680, 7711200, 7761600, 7796880, 7817040, 7862400, 7882560, 7900200, 7927920,
    7983360} : Finset ℕ)) :
    S.card < 100 := by
  sorry

/-- The statement of `leaf_cover_search_top`, assembled from the two LEAFs with no `sorry`. -/
theorem leaf_cover_search_top_split {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 4600000 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 8000000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  by_cases hl : S.lcm Prod.fst ∈ ({4656960, 4712400, 4717440, 4804800, 4883760, 4914000, 4979520, 4989600, 5045040, 5100480,
    5140800, 5155920, 5241600, 5250960, 5266800, 5322240, 5397840, 5405400, 5443200, 5503680,
    5544000, 5569200, 5654880, 5745600, 5765760, 5821200, 5896800, 5911920, 5987520, 5997600,
    6006000, 6027840, 6048000, 6098400, 6126120, 6153840, 6168960, 6177600, 6209280, 6224400,
    6289920, 6320160, 6350400, 6375600, 6426000, 6431040, 6486480, 6511680, 6552000, 6597360,
    6652800, 6683040, 6846840, 6854400, 6874560, 6879600, 6894720, 6955200, 6985440, 7001280,
    7030800, 7068600, 7076160, 7197120, 7207200, 7257600, 7272720, 7318080, 7338240, 7373520,
    7413120, 7454160, 7469280, 7484400, 7534800, 7539840, 7567560, 7600320, 7620480, 7650720,
    7660800, 7687680, 7711200, 7761600, 7796880, 7817040, 7862400, 7882560, 7900200, 7927920,
    7983360} : Finset ℕ)
  · exact leaf_search_top_list hS hi hp hl
  · have hdvd : ∀ d ∈ S.image Prod.fst, d ∣ S.lcm Prod.fst := by
      intro d hd
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.dvd_lcm (f := Prod.fst) hs
    have hform : ∀ d ∈ S.image Prod.fst, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1 := by
      intro d hd
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
      exact hp s hs
    have hlt := leaf_count_top_window (S.lcm Prod.fst) hlo hhi hl hout (S.image Prod.fst) hdvd hform
    rwa [Finset.card_image_of_injOn hi] at hlt

end LeanLab.OpenProblems.Novelty1615

#print axioms LeanLab.OpenProblems.Novelty1615.leaf_cover_search_top_split
