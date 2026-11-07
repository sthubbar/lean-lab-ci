import LeanLab.OpenProblems.DecompJ1235

/-!
# SPLIT of `leaf_card_lt_of_lcm_lt`, folder OpenProblems, module DecompJ1235

The target bounds the number of congruences of a covering system whose moduli are the distinct
numbers `p - 1` with `p ≥ 5` prime and whose lcm stays below `8000000`. The statement is a finite
verification, not a consequence of the reciprocal test alone: the moduli of such a system are
divisors of the lcm, and for `L = 6006000` there are already `104` divisors of that shape with
reciprocal sum above `1`, so no estimate on the sum can refuse `100` congruences there. What the
split below does is cut the lcm range:

* below `1965600` no lcm has `100` divisors of the required shape, and that is pure counting, with
  no covering hypothesis at all;
* at the four lcm values `5012280`, `7022400`, `7425600`, `7876440`, which are the only ones below
  `8000000` whose required divisors number at least `100` and whose full reciprocal sum is below
  `1`, the reciprocal test refuses `100` congruences with no covering argument;
* on the two remaining windows of the lcm the claim needs the congruence search itself.

The assembly `leaf_card_lt_of_lcm_lt_split` proves the target from the leaves with no `sorry`.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-- LEAF: counting step on the low range. A finite set of numbers, each of the shape `p - 1` for a
prime `p ≥ 5`, all of them divisors of a nonzero `L` below `1965600`, has fewer than `100` members.
No covering and no residue class enters here: this is the size of the set of divisors of `L` of that
shape, and it says that `1965600` is the first lcm which can carry `100` of them. The hypothesis
`0 < L` is needed: every positive `d` divides `0`. -/
theorem leaf_candidate_count_small (L : ℕ) (hL0 : 0 < L) (hL : L < 1965600) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry

/-- LEAF: the reciprocal test at the four exceptional lcm values. For `L` one of `5012280`,
`7022400`, `7425600`, `7876440`, the sum of `1 / d` over the divisors `d` of `L` of the shape
`p - 1`, `p ≥ 5` prime, is below `1`, so every subset of them is too. These are the values below
`8000000` where the sum over all of them already fails the `1` that a covering forces. -/
theorem leaf_inv_sum_lt_of_special (L : ℕ)
    (hL : L ∈ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    ∑ d ∈ T, (1 : ℚ) / d < 1 := by
  sorry

/-- LEAF: the congruence search on the middle window of the lcm, `1965600 ≤ lcm < 4600000`. A
covering system with distinct moduli `p - 1`, `p ≥ 5` prime, and with lcm in that window, other
than at the four lcm values handled by the reciprocal test, has fewer than `100` congruences. This
is the search over the residue data for the lcm values in the window. -/
theorem leaf_cover_search_mid {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 1965600 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 4600000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  sorry

/-- LEAF: the congruence search on the top window of the lcm, `4600000 ≤ lcm < 8000000`. Same
claim as the middle window, for the residue data whose lcm lies in the upper part of the range, the
four lcm values handled by the reciprocal test again excluded. -/
theorem leaf_cover_search_top {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 4600000 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 8000000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  sorry

/-- Every modulus of `S` divides the lcm of the moduli, so the moduli are divisors of one number.
Bookkeeping for the two arithmetic leaves. -/
private lemma moduli_dvd_lcm {S : Finset (ℕ × ℤ)} {s : ℕ × ℤ} (hs : s ∈ S) :
    s.1 ∣ S.lcm Prod.fst :=
  Finset.dvd_lcm (f := Prod.fst) hs

/-- Distinctness of the moduli turns a sum over the congruences into a sum over the moduli. -/
private lemma sum_inv_eq_sum_image {S : Finset (ℕ × ℤ)}
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ))) :
    ∑ s ∈ S, (1 : ℚ) / ((s.1 : ℕ) : ℚ) = ∑ d ∈ S.image Prod.fst, (1 : ℚ) / ((d : ℕ) : ℚ) :=
  (Finset.sum_image (s := S) (g := Prod.fst) (f := fun d : ℕ => (1 : ℚ) / ((d : ℕ) : ℚ))
    hi).symm

/-- The split of `leaf_card_lt_of_lcm_lt`: the same statement, proved from the four leaves above,
with no `sorry` and without using the target theorem. -/
theorem leaf_card_lt_of_lcm_lt_split {S : Finset (ℕ × ℤ)} (hS : Covers S) (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
  (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) (hlcm : S.lcm Prod.fst < 8000000) : S.card < 100 := by
  have hdvd : ∀ d ∈ S.image Prod.fst, d ∣ S.lcm Prod.fst := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact moduli_dvd_lcm hs
  have hform : ∀ d ∈ S.image Prod.fst, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1 := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact hp s hs
  have hpos : ∀ s ∈ S, 0 < s.1 := by
    intro s hs
    obtain ⟨p, _, h5, hsp⟩ := hp s hs
    omega
  have hlcmpos : 0 < S.lcm Prod.fst := by
    rw [Nat.pos_iff_ne_zero]
    refine Finset.lcm_ne_zero_iff.mpr ?_
    intro s hs
    have h := hpos s hs
    omega
  by_cases h1 : S.lcm Prod.fst < 1965600
  · have hlt := leaf_candidate_count_small (S.lcm Prod.fst) hlcmpos h1 (S.image Prod.fst) hdvd hform
    have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_of_injOn hi
    omega
  · by_cases h2 : S.lcm Prod.fst ∈ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)
    · exfalso
      have hd := one_le_sum_inv hS hpos
      rw [sum_inv_eq_sum_image hi] at hd
      have hlt := leaf_inv_sum_lt_of_special (S.lcm Prod.fst) h2 (S.image Prod.fst) hdvd hform
      linarith
    · by_cases h3 : S.lcm Prod.fst < 4600000
      · exact leaf_cover_search_mid hS hi hp (by omega) h3 h2
      · exact leaf_cover_search_top hS hi hp (by omega) hlcm h2

end LeanLab.OpenProblems.Novelty1615

#print axioms LeanLab.OpenProblems.Novelty1615.leaf_card_lt_of_lcm_lt_split
