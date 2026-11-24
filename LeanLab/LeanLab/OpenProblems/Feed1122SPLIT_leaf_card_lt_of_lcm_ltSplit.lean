import LeanLab.OpenProblems.SPLIT_leaf_card_lt_of_lcm_lt

/-!
# Feed1122 split of `leaf_cover_search_mid` and `leaf_cover_search_top`

Parent module `LeanLab.OpenProblems.SPLIT_leaf_card_lt_of_lcm_lt`, unit Novelty1615, Erdos problem
273 setting: covering systems whose moduli are distinct numbers `p - 1`, `p ≥ 5` prime.

Each window leaf of the parent is cut, following the parent file's own method, into

* a pure counting leaf: for an lcm `L` in the window outside an explicit finite list, fewer than
  `100` divisors of `L` have the shape `p - 1`, `p ≥ 5` prime; no covering enters;
* a search leaf restricted to the explicit list, the only lcm values in the window carrying at
  least `100` such divisors with reciprocal sum at least `1`.

The lists were computed by a sieve over all `L < 8000000`, AI scratch computation, burst-20261122-S105:
`33` values in `[1965600, 4600000)` and `91` values in `[4600000, 8000000)` once the four lcm
values of the reciprocal test are removed. The assembly theorems prove the parent statements with no
`sorry`. AI wrote the Lean code.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-- The `33` lcm values in `[1965600, 4600000)` with at least `100` divisors of the shape `p - 1`,
`p ≥ 5` prime. Sieve computation recorded in the note of burst-20261122-S105. -/
def midList : Finset ℕ :=
  {1965600, 2162160, 2217600, 2227680, 2494800, 2570400, 2751840, 2827440, 2882880, 2948400,
   3160080, 3276000, 3326400, 3341520, 3598560, 3603600, 3734640, 3769920, 3825360, 3855600,
   3880800, 3931200, 3991680, 4158000, 4213440, 4233600, 4241160, 4309200, 4324320, 4435200,
   4455360, 4520880, 4586400}

/-- The `91` lcm values in `[4600000, 8000000)`, other than `5012280, 7022400, 7425600, 7876440`,
with at least `100` divisors of the shape `p - 1`, `p ≥ 5` prime. Sieve computation recorded in the
note of burst-20261122-S105. -/
def topList : Finset ℕ :=
  {4656960, 4712400, 4717440, 4804800, 4883760, 4914000, 4979520, 4989600, 5045040, 5100480,
   5140800, 5155920, 5241600, 5250960, 5266800, 5322240, 5397840, 5405400, 5443200, 5503680,
   5544000, 5569200, 5654880, 5745600, 5765760, 5821200, 5896800, 5911920, 5987520, 5997600,
   6006000, 6027840, 6048000, 6098400, 6126120, 6153840, 6168960, 6177600, 6209280, 6224400,
   6289920, 6320160, 6350400, 6375600, 6426000, 6431040, 6486480, 6511680, 6552000, 6597360,
   6652800, 6683040, 6846840, 6854400, 6874560, 6879600, 6894720, 6955200, 6985440, 7001280,
   7030800, 7068600, 7076160, 7197120, 7207200, 7257600, 7272720, 7318080, 7338240, 7373520,
   7413120, 7454160, 7469280, 7484400, 7534800, 7539840, 7567560, 7600320, 7620480, 7650720,
   7660800, 7687680, 7711200, 7761600, 7796880, 7817040, 7862400, 7882560, 7900200, 7927920,
   7983360}

/-- LEAF: counting step on the middle window of the parent split, class MEDIUM. For `L` in
`[1965600, 4600000)` outside `midList`, a set of divisors of `L` each of the shape `p - 1`,
`p ≥ 5` prime, has fewer than `100` members. Same kind of statement as
`leaf_candidate_count_small`, no covering hypothesis; a finite divisor count. -/
theorem leaf_candidate_count_mid (L : ℕ) (hlo : 1965600 ≤ L) (hhi : L < 4600000)
    (hnot : L ∉ midList) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- LEAF: congruence search on the middle window restricted to the `33` lcm values of `midList`,
class HARD. A covering system with distinct moduli `p - 1`, `p ≥ 5` prime, whose lcm is one of
these values, has fewer than `100` congruences. -/
theorem leaf_cover_search_midList {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hL : S.lcm Prod.fst ∈ midList) :
    S.card < 100 := by
  sorry

/-- LEAF: counting step on the top window of the parent split, class MEDIUM. For `L` in
`[4600000, 8000000)` outside `topList` and outside the four reciprocal test values, a set of divisors
of `L` each of the shape `p - 1`, `p ≥ 5` prime, has fewer than `100` members. No covering
hypothesis; a finite divisor count. -/
theorem leaf_candidate_count_top (L : ℕ) (hlo : 4600000 ≤ L) (hhi : L < 8000000)
    (hnot : L ∉ topList) (hout : L ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ))
    (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- LEAF: congruence search on the top window restricted to the `91` lcm values of `topList`,
class HARD. A covering system with distinct moduli `p - 1`, `p ≥ 5` prime, whose lcm is one of
these values, has fewer than `100` congruences. -/
theorem leaf_cover_search_topList {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hL : S.lcm Prod.fst ∈ topList) :
    S.card < 100 := by
  sorry

/-- Bookkeeping: the moduli of `S`, as a set, divide the lcm, have the required shape, and number
`S.card` when the moduli are distinct. -/
private lemma image_facts {S : Finset (ℕ × ℤ)} (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) :
    (∀ d ∈ S.image Prod.fst, d ∣ S.lcm Prod.fst) ∧
    (∀ d ∈ S.image Prod.fst, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) ∧
    (S.image Prod.fst).card = S.card := by
  refine ⟨?_, ?_, Finset.card_image_of_injOn hi⟩
  · intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact Finset.dvd_lcm (f := Prod.fst) hs
  · intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact hp s hs

/-- Assembly: the statement of `leaf_cover_search_mid`, proved from the two middle window leaves
with no `sorry`. -/
theorem leaf_cover_search_mid_split {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 1965600 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 4600000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  by_cases hL : S.lcm Prod.fst ∈ midList
  · exact leaf_cover_search_midList hS hi hp hL
  · obtain ⟨hdvd, hform, hcard⟩ := image_facts hi hp
    have := leaf_candidate_count_mid _ hlo hhi hL _ hdvd hform
    omega

/-- Assembly: the statement of `leaf_cover_search_top`, proved from the two top window leaves with
no `sorry`. -/
theorem leaf_cover_search_top_split {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 4600000 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 8000000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  by_cases hL : S.lcm Prod.fst ∈ topList
  · exact leaf_cover_search_topList hS hi hp hL
  · obtain ⟨hdvd, hform, hcard⟩ := image_facts hi hp
    have := leaf_candidate_count_top _ hlo hhi hL hout _ hdvd hform
    omega

end LeanLab.OpenProblems.Novelty1615
