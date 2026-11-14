/-
Split of `leaf_short_weight_tiny_cutoff` in the sibling file `SPLIT_leaf_centered_character_mean_value`
into four leaves, with the sealed statement left unchanged and the target neither imported nor used.

Where the cut is made. The leaf's conclusion is a single existential block

  `∃ v0 b0, (density ledger) ∧ (divisor bound) ∧ (centred character mean value) ∧ (prime domination)`,

and all four conjuncts speak about the same two witnesses. So the block cannot be cut by handing one
conjunct to a separate step: a family that carries the divisor bound and the prime domination is not
thereby the normalised short coefficient, and the density is pinned to the family through the per-term
offset `v0 / log Y`. The cut is therefore made on the two parameters that the leaf, once `1 < B` and
`ε ≤ 1/10^12` are fixed, still leaves free: the divisor exponent `B`, cut at `2`, and the cutoff `ε`,
cut at `1/10^20`. Each leaf is the block under two strictly stronger hypotheses, hence strictly easier
than the leaf being split, and no regime is empty: the pairs `B = 3/2, ε = 1/10^30`,
`B = 3/2, ε = 1/10^15`, `B = 3, ε = 1/10^30` and `B = 3, ε = 1/10^15` each satisfy the extra
hypotheses of its leaf together with `0 < ε`, `ε ≤ 1/10^8` and `ε ≤ 1/10^12`. Since
`1/10^20 < 1/10^12`, both cutoff regimes sit inside the range the leaf already carries. The assembly
below is the matching four-way case analysis and has no unproved step.

The four analytic leaves remain OPEN. AI wrote the Lean code.
-/
import LeanLab.BHP1997.SPLIT_leaf_centered_character_mean_value

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 4. Step: the density ledger, the divisor bound, the centred character mean value and the
prime domination, in the regime where the divisor exponent is at most two and the cutoff is at most
`1/10^20`.

This is the block of `leaf_short_weight_tiny_cutoff` under the two extra hypotheses `B ≤ 2` and
`ε ≤ 1/10^20`, so it is strictly easier than what it splits and not a restatement of it: at `B = 3/2`
and `ε = 1/10^30` both extra hypotheses hold, and at `ε = 1/10^15` the leaf does not apply. The
divisor bound is the easier one here because the divisor count enters with exponent at most two. -/
theorem leaf_tiny_cutoff_exponent_le_two_tiny_epsilon
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hB2 : B ≤ 2) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hεt : ε ≤ 1/10^12) (hε20 : ε ≤ 1/10^20) :
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

/-- LEAF 2 of 4. Step: the same block in the regime where the divisor exponent is at most two and the
cutoff is at least `1/10^20`.

This is the block of `leaf_short_weight_tiny_cutoff` under the two extra hypotheses `B ≤ 2` and
`1/10^20 ≤ ε`, so it is strictly easier than what it splits and not a restatement of it: at `B = 3/2`
and `ε = 1/10^15` both extra hypotheses hold, and at `ε = 1/10^30` the leaf does not apply. Together
with leaf 1 this covers the whole regime `B ≤ 2`, since `1/10^20 ≤ ε` and `ε ≤ 1/10^20` are
complementary. -/
theorem leaf_tiny_cutoff_exponent_le_two_large_epsilon
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hB2 : B ≤ 2) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hεt : ε ≤ 1/10^12) (hε20 : 1/10^20 ≤ ε) :
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

/-- LEAF 3 of 4. Step: the same block in the regime where the divisor exponent is larger than two and
the cutoff is at most `1/10^20`.

This is the block of `leaf_short_weight_tiny_cutoff` under the two extra hypotheses `2 < B` and
`ε ≤ 1/10^20`, so it is strictly easier than what it splits and not a restatement of it: at `B = 3`
and `ε = 1/10^30` both extra hypotheses hold. This is the leaf whose divisor bound is the hardest of
the four, since the divisor count enters with an exponent above two. -/
theorem leaf_tiny_cutoff_exponent_gt_two_tiny_epsilon
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 2 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hεt : ε ≤ 1/10^12) (hε20 : ε ≤ 1/10^20) :
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

/-- LEAF 4 of 4. Step: the same block in the regime where the divisor exponent is larger than two and
the cutoff is at least `1/10^20`.

This is the block of `leaf_short_weight_tiny_cutoff` under the two extra hypotheses `2 < B` and
`1/10^20 ≤ ε`, so it is strictly easier than what it splits and not a restatement of it: at `B = 3`
and `ε = 1/10^15` both extra hypotheses hold. Together with leaf 3 this covers the whole regime
`2 < B`, since `1/10^20 ≤ ε` and `ε ≤ 1/10^20` are complementary. -/
theorem leaf_tiny_cutoff_exponent_gt_two_large_epsilon
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 2 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hεt : ε ≤ 1/10^12) (hε20 : 1/10^20 ≤ ε) :
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

theorem leaf_short_weight_tiny_cutoff_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : 1 < B) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hεt : ε ≤ 1/10^12) :
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
  by_cases hB2 : B ≤ 2
  · by_cases he : ε ≤ 1/10^20
    · exact leaf_tiny_cutoff_exponent_le_two_tiny_epsilon h4 h9 hω hz hB hB2 hε hε8 hεt he
    · have he' : 1/10^20 ≤ ε := le_of_lt (not_le.mp he)
      exact leaf_tiny_cutoff_exponent_le_two_large_epsilon h4 h9 hω hz hB hB2 hε hε8 hεt he'
  · have hB2' : 2 < B := not_le.mp hB2
    by_cases he : ε ≤ 1/10^20
    · exact leaf_tiny_cutoff_exponent_gt_two_tiny_epsilon h4 h9 hω hz hB2' hε hε8 hεt he
    · have he' : 1/10^20 ≤ ε := le_of_lt (not_le.mp he)
      exact leaf_tiny_cutoff_exponent_gt_two_large_epsilon h4 h9 hω hz hB2' hε hε8 hεt he'
