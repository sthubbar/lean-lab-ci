/-
Split of `leaf_short_weight_large_cutoff` in the sibling file
`SPLIT_leaf_centered_character_mean_value` into three leaves, with the sealed statement left
unchanged and the target neither imported nor used.

Where the cut is made. The sealed block asks for one density `v0` and one coefficient family `b0`
such that four properties hold together: the Buchstab ledger against the two discarded integrals,
the divisor bound of exponent `B`, the centred character mean value at level `11/20 + ε`, and the
pointwise domination of the prime indicator on the short interval. All four speak about the same
two witnesses, and the density is pinned to the family through the per-term offset
`v0 / Real.log (x ^ (11/20 + ε))`, so the block cannot be handed to a second universally
quantified step: the family `b0 = 0` together with `v0 = 1` has the divisor bound and the prime
domination, while at the principal character its centred sum is minus the number of window terms
over the logarithm, of size about `Y / Real.log Y`, which no `C * Y * (Real.log x) ^ (-A)`
dominates. A leaf transporting the mean value to an arbitrary divisor-bounded family is therefore
refutable, and the block is cut on the cutoff `ε` instead.

The cut. This leaf carries `1 < B` and the closed cutoff window `[1/10^12, 1/10^8]`. The three
leaves below split that window at `1/10^10` and at `1/10^9`. Each leaf is exactly the same block
under the same hypotheses plus one further condition on `ε`, hence strictly easier than the leaf
being split, and the assembly is a two-step case analysis with no unproved step. Every band is
inhabited: `ε = 1/10^11` lies in the first, `ε = 3/10^10` in the second, and `ε = 1/10^8` in the
third.

The three analytic leaves remain OPEN.
-/
import LeanLab.BHP1997.SPLIT_leaf_centered_character_mean_value

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 3. Step: the four-part block in the lowest cutoff band, `1/10^12 ≤ ε ≤ 1/10^10`,
with the divisor exponent fixed above one.

Strictly easier than the leaf being split: every hypothesis of that leaf is kept, and the extra
condition `ε ≤ 1/10^10` narrows the cutoff. The band is inhabited (`ε = 1/10^11`), and it does not
restate the block, which carries no upper cutoff below `1/10^8`. Degenerate readings: `ε` stays
strictly positive and at most `1/10^8`, so both discarded integrals stay inside their range; the
divisor bound is read at `B > 1`, where the divisor count of `0` is one and the right-hand side is
at least a constant. -/
theorem leaf_short_weight_near_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^12 ≤ ε)
    (hεnear : ε ≤ 1/10^10) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- LEAF 2 of 3. Step: the same four-part block in the middle cutoff band,
`1/10^10 ≤ ε ≤ 1/10^9`, with the divisor exponent fixed above one.

Strictly easier than the leaf being split on two counts: the extra lower bound `1/10^10 ≤ ε` and
the extra upper bound `ε ≤ 1/10^9` both narrow the cutoff window. The band is inhabited
(`ε = 3/10^10`), so the leaf is not vacuously true. Read at `ε = 1/10^9` the window is the widest
of the three bands and `11/20 + ε` is still within `1/10^9` of `11/20`; the positivity and upper
bounds `0 < ε ≤ 1/10^8` are inherited unchanged, so no integral is read at a degenerate cutoff. -/
theorem leaf_short_weight_mid_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^10 ≤ ε)
    (hεmid : ε ≤ 1/10^9) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- LEAF 3 of 3. Step: the same four-part block in the top cutoff band,
`1/10^9 ≤ ε ≤ 1/10^8`, with the divisor exponent fixed above one.

Strictly easier than the leaf being split: the extra condition `1/10^9 ≤ ε` narrows the cutoff
window, and the remaining hypotheses are those of the split leaf, so the band covers the top of
the window `[1/10^12, 1/10^8]` up to its endpoint `ε = 1/10^8`, where the leaf applies. The band is
inhabited and not a single point, since `1/10^9 < 1/10^8`; the cutoff stays strictly positive, so
the short interval is nonempty for large `x` and the two discarded integrals are read at a
nondegenerate cutoff. -/
theorem leaf_short_weight_top_cutoff
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hεtop : 1/10^9 ≤ ε) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  sorry

/-- The sealed block of `leaf_short_weight_large_cutoff`, assembled from the three cutoff bands
by case analysis on `ε ≤ 1/10^10` and then on `ε ≤ 1/10^9`. No sorry, and the sealed statement is
neither imported nor used. -/
theorem leaf_short_weight_large_cutoff_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : 1/10^12 ≤ ε) :
    ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
      1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
      (∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  by_cases hnear : ε ≤ 1/10^10
  · exact leaf_short_weight_near_cutoff h4 h9 hω hz hB hε hε8 hεt hnear
  · have hnear' : 1/10^10 ≤ ε := le_of_lt (not_le.mp hnear)
    by_cases hmid : ε ≤ 1/10^9
    · exact leaf_short_weight_mid_cutoff h4 h9 hω hz hB hε hε8 hnear' hmid
    · have hmid' : 1/10^9 ≤ ε := le_of_lt (not_le.mp hmid)
      exact leaf_short_weight_top_cutoff h4 h9 hω hz hB hε hε8 hmid'
