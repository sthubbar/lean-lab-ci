/-
Split of `leaf_centered_character_mean_value` in the sibling file `SPLIT_lower_short_weight_analytic`
into three leaves, with the sealed statement left unchanged and the target theorem neither
imported nor used.

Where the cut can be made. The leaf's conclusion is one existential block

  `∃ v0 b0, (density ledger) ∧ (divisor bound) ∧ (centred character mean value) ∧ (prime domination)`,

and all four properties speak about the same two witnesses. The block therefore cannot be split
by handing the family to a second, universally quantified step: a family that satisfies both the
divisor bound and the prime domination need not be the normalised short coefficient, and the
density is pinned to the family through the per-term offset `v0 / log Y`. The family `b0 = 0` with
`v0 = 1`, for example, satisfies `|b0 x k| ≤ 1 * (card of divisors of k) ^ B` and
`b0 x m ≤ primeWeight m`, while at the principal character its centred sum is minus the number of
terms over `log Y`, of size `Y / log Y`, which no `C * Y * (log x) ^ (-A)` dominates. So a leaf
that transports the mean value to an arbitrary divisor-bounded family is refutable, and the
three-way cut is made instead on the two parameters that index the block: the exponent `B` and
the cutoff `ε`. The exponent is cut at one, and the harder branch `1 < B` is cut again at a small
cutoff. Each leaf is the same block under strictly stronger hypotheses, hence strictly easier than
the leaf being split, and the assembly below is a case analysis with no sorry.

The three analytic leaves remain OPEN. AI wrote the Lean code.
-/
import LeanLab.BHP1997.SPLIT_lower_short_weight_analytic

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 3. Step: the density ledger, the divisor bound, the centred character mean value
and the prime domination, in the regime where the divisor exponent is at most one.

This is the block of `leaf_centered_character_mean_value` under the extra hypothesis `B ≤ 1`.
Restricting the exponent restricts the divisor bound `|b0 x k| ≤ C * (card of divisors of k) ^ B`
to the linear regime, so the leaf is strictly easier than the statement it splits. It is not a
restatement: it carries a hypothesis the statement does not have, and it does not produce the
weight `ω`, the exponent `B0` or the threshold `η`.

Tested at the degenerate readings: `B = 1` and `B = 0` are inside the regime and the exponent
`tau(k) ^ 0 = 1` is the constant bound; `B` negative stays inside too, and then `tau(k) ^ B ≤ 1`
since the divisor count is at least one, so the bound is the constant one. `ε` still satisfies
`0 < ε ≤ 1/10^8`, so the two discarded integrals are evaluated inside their range. Not vacuous:
the standard Buchstab weight together with the normalised short coefficient is the intended
witness, and `ε → 0` is excluded by `0 < ε`.

Where a finer cut fails: the density `v0` enters the sum only as the offset `v0 / log Y`, and no
divisor-bounded family that is merely dominated by the prime indicator carries a matching
density, so this block cannot be handed to an arbitrary family of that kind. -/
theorem leaf_short_weight_small_exponent
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hB : B ≤ 1) (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
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

/-- LEAF 2 of 3. Step: the same block in the regime `1 < B` and a very small cutoff `ε`.

Strictly easier than `leaf_centered_character_mean_value` on two counts: the exponent is
restricted to `1 < B` and the cutoff to `ε ≤ 1/10^12`. On this range the local window
`rightInterval ε x` is the narrowest one the statement ever asks about and the exponent
`11/20 + ε` is within `1/10^12` of `11/20`.

Tested at the boundary: at `ε = 1/10^12` the leaf applies, and `1/10^12 < 1/10^8`, so the range
is nonempty; `ε → 0` is excluded by `0 < ε`; `B` just above one leaves the divisor bound
essentially linear. Not vacuous for the same reason as leaf 1. -/
theorem leaf_short_weight_tiny_cutoff
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
  sorry

/-- LEAF 3 of 3. Step: the same block in the regime `1 < B` and a cutoff `ε` at least `1/10^12`.

Strictly easier than `leaf_centered_character_mean_value` on two counts: the exponent is
restricted to `1 < B` and the cutoff to `1/10^12 ≤ ε`; together with the statement's
`ε ≤ 1/10^8` that leaves the range `[1/10^12, 1/10^8]`, so the leaf is not vacuous and its
hypotheses are simultaneously satisfiable, for example at `ε = 1/10^10`.

The two leaves 2 and 3 cover the branch `1 < B` of the split and leaf 1 covers `B ≤ 1`. -/
theorem leaf_short_weight_large_cutoff
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
  sorry

/-- The sealed statement, assembled from the three leaves above with no sorry. The case
`B ≤ 1` is leaf 1; on `1 < B` the cutoff is split at `1/10^12`, which is leaf 2 and leaf 3. No
step uses the target theorem, and the statement is unchanged. -/
theorem leaf_centered_character_mean_value_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
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
  by_cases hB : B ≤ 1
  · exact leaf_short_weight_small_exponent h4 h9 hω hz hB hε hε8
  · have hB1 : 1 < B := not_le.mp hB
    by_cases hεt : ε ≤ 1/10^12
    · exact leaf_short_weight_tiny_cutoff h4 h9 hω hz hB1 hε hε8 hεt
    · have hεt1 : 1/10^12 ≤ ε := le_of_lt (not_le.mp hεt)
      exact leaf_short_weight_large_cutoff h4 h9 hω hz hB1 hε hε8 hεt1
