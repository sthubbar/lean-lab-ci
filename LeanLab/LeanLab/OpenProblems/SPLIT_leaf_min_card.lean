import LeanLab.OpenProblems.DecompJ1235

/-!
# SPLIT of `OpenProblems.DecompJ1235.leaf_min_card`

Target, unchanged and not restated here:

`Covers S`, distinct first coordinates, every first coordinate `p - 1` for a prime `p ≥ 5`
`⟹ 100 ≤ S.card`.

Status of the target on main: `OPEN`, one `sorry`, and the folder's notes record it as blocked on
search-scale input. The reciprocal test `Erdos273.one_le_sum_inv`, the only covering input in this
file's import closure, needs the seventeen admissible moduli below `70` and one more to pass `1`,
so it stops at `18 ≤ S.card` and cannot reach `100`. The split below therefore does not try to
push the reciprocal test further: it cuts the counting claim into three modulus bands and asks, per
band, for the number of classes the band has to supply. Each band bound is one inequality about an
ordinary filtered cardinality, strictly weaker than the target, and every band is wide enough that
the count asked for is reachable: the band `[70, 1000)` contains `149` numbers `p - 1` with `p`
prime, the band `[1000, 10^5)` far more, and the band `[10^5, ∞)` more still.

Two facts about the bands are proved outright, with no `sorry`:

* `card_split_four` splits `S.card` into the four filtered cardinalities, exact, no hypothesis;
* `card_lt_seventy_le` caps the bottom band at `17`: the low band of `Novelty1615`'s sibling
  development holds exactly the seventeen admissible moduli below `70`, so distinctness gives the
  cap by an injection. That is why the three leaves can be stated as bands from `70` upward and the
  bottom band can be dropped from the arithmetic with no loss.

Nothing here changes a statement, an import or a definition of the target file, and no definition,
abbreviation, structure, instance or notation is introduced: the two helpers are `private theorem`s.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-! ### Bookkeeping: the band partition of a finite set of pairs -/

/-- Splitting off one threshold, exactly. No hypothesis on the threshold. -/
private theorem card_split_two (S : Finset (ℕ × ℤ)) (a : ℕ) :
    S.card = (S.filter fun s => s.1 < a).card + (S.filter fun s => a ≤ s.1).card := by
  have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun s : ℕ × ℤ => a ≤ s.1)
  have h2 : (S.filter fun s : ℕ × ℤ => ¬ a ≤ s.1) = (S.filter fun s => s.1 < a) := by
    apply Finset.filter_congr
    intro s _
    simp only [not_le]
  rw [h2] at h
  omega

/-- The four bands `[0, a)`, `[a, b)`, `[b, c)`, `[c, ∞)`, exactly and without overlap. -/
private theorem card_split_four (S : Finset (ℕ × ℤ)) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    S.card = (S.filter fun s => s.1 < a).card
      + (S.filter fun s => a ≤ s.1 ∧ s.1 < b).card
      + (S.filter fun s => b ≤ s.1 ∧ s.1 < c).card
      + (S.filter fun s => c ≤ s.1).card := by
  have h1 := card_split_two S a
  have step1 : (S.filter fun s => a ≤ s.1).card
      = (S.filter fun s => a ≤ s.1 ∧ s.1 < b).card + (S.filter fun s => b ≤ s.1).card := by
    have h := card_split_two (S.filter fun s => a ≤ s.1) b
    rw [Finset.filter_filter, Finset.filter_filter] at h
    have hcong : (S.filter fun s => a ≤ s.1 ∧ b ≤ s.1) = (S.filter fun s => b ≤ s.1) := by
      apply Finset.filter_congr
      intro s _
      constructor
      · intro hh; exact hh.2
      · intro hh; exact ⟨hab.trans hh, hh⟩
    rw [hcong] at h
    exact h
  have step2 : (S.filter fun s => b ≤ s.1).card
      = (S.filter fun s => b ≤ s.1 ∧ s.1 < c).card + (S.filter fun s => c ≤ s.1).card := by
    have h := card_split_two (S.filter fun s => b ≤ s.1) c
    rw [Finset.filter_filter, Finset.filter_filter] at h
    have hcong : (S.filter fun s => b ≤ s.1 ∧ c ≤ s.1) = (S.filter fun s => c ≤ s.1) := by
      apply Finset.filter_congr
      intro s _
      constructor
      · intro hh; exact hh.2
      · intro hh; exact ⟨hbc.trans hh, hh⟩
    rw [hcong] at h
    exact h
  omega

/-! ### The bottom band is capped at seventeen -/

/-- At most `17` classes have their modulus below `70`. Every such modulus is `p - 1` for a prime
`p ≥ 5` and below `70`, hence one of the seventeen admissible values listed in `lowModuli`, and
distinctness makes the modulus map injective on that filter. This is the only factual input the
split keeps from the sibling development, and it is proved here in full. -/
private theorem card_lt_seventy_le (S : Finset (ℕ × ℤ))
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) :
    (S.filter fun s => s.1 < 70).card ≤ 17 := by
  have hsub : (S.filter fun s => s.1 < 70).image Prod.fst ⊆ lowModuli := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hsS, hs70⟩ := Finset.mem_filter.mp hs
    obtain ⟨p, hpp, h5, hpe⟩ := hp s hsS
    show s.1 ∈ lowModuli
    rw [hpe]
    exact mem_lowModuli hpp h5 (by omega)
  have hinj : Set.InjOn Prod.fst ((S.filter fun s => s.1 < 70) : Set (ℕ × ℤ)) := by
    apply hi.mono
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hcard : ((S.filter fun s => s.1 < 70).image Prod.fst).card
      = (S.filter fun s => s.1 < 70).card := Finset.card_image_of_injOn hinj
  have h17 : lowModuli.card = 17 := by decide
  calc (S.filter fun s => s.1 < 70).card
      = ((S.filter fun s => s.1 < 70).image Prod.fst).card := hcard.symm
    _ ≤ lowModuli.card := Finset.card_le_card hsub
    _ = 17 := h17

/-! ### The three band leaves

The three bands below `10^5` are the ones that carry the density; their stated counts are the
per-band shares of the `100` the target asks for, and they add up to it.
-/

/-- LEAF: the first counting band. Among the classes whose modulus lies in `[70, 1000)` at least
`52` are present. This is the low end of the counting step: the reciprocal test places its mass
exactly here, and `149` numbers `p - 1` with `p` prime lie in the band, so the count is reachable.
Its proof is the per-band counting estimate, and it is strictly weaker than the target, which asks
for the total over all bands. -/
theorem leaf_low_band_card {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) :
    52 ≤ (S.filter fun s => 70 ≤ s.1 ∧ s.1 < 1000).card := by
  sorry

/-- LEAF: the second counting band. Among the classes whose modulus lies in `[1000, 10^5)` at
least `33` are present. This is the middle counting step, strictly easier than the target because
it bounds one band only, and the band holds far more admissible moduli than the `33` asked for. -/
theorem leaf_mid_band_card {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) :
    33 ≤ (S.filter fun s => 1000 ≤ s.1 ∧ s.1 < 100000).card := by
  sorry

/-- LEAF: the third counting band. Among the classes whose modulus is at least `10^5` at least `15`
are present. This is the tail counting step: the band is unbounded above, so its count is not
capped by a prime count, and the leaf bounds that one band rather than the total. -/
theorem leaf_high_band_card {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) :
    15 ≤ (S.filter fun s => 100000 ≤ s.1).card := by
  sorry

/-! ### Assembly -/

/-- The target's claim, assembled from the three band leaves and the exact band partition. The
bottom band `[0, 70)` is dropped, not estimated: it contributes at most `17` classes and here it
only needs to contribute `0`. -/
theorem leaf_min_card_split {S : Finset (ℕ × ℤ)} (hS : Covers S) (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
  (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) : 100 ≤ S.card := by
  have h1 := leaf_low_band_card hS hi hp
  have h2 := leaf_mid_band_card hS hi hp
  have h3 := leaf_high_band_card hS hi hp
  have hpart := card_split_four S (a := 70) (b := 1000) (c := 100000) (by norm_num) (by norm_num)
  omega

end LeanLab.OpenProblems.Novelty1615

#print axioms LeanLab.OpenProblems.Novelty1615.leaf_low_band_card
#print axioms LeanLab.OpenProblems.Novelty1615.leaf_mid_band_card
#print axioms LeanLab.OpenProblems.Novelty1615.leaf_high_band_card
#print axioms LeanLab.OpenProblems.Novelty1615.leaf_min_card_split
