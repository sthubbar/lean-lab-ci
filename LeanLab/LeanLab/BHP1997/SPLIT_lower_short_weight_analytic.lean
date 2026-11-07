/-
Split of `lower_short_weight_analytic` in LeanLab.BHP1997.DecompC165d into four leaves.
The sealed statement is unchanged; the target theorem is neither imported nor used.

The statement asks for one Buchstab weight `ω`, one divisor exponent `B0`, one `ε`-threshold
`η`, and then for every admissible pair `(B, ε)` a density `v0` and a coefficient family `b0`
on the short interval, such that `v0` is at least one minus the two discarded Buchstab
integrals, the family obeys the short weight condition `RightConditions`, and the family is
pointwise dominated by the prime indicator on the short interval.

The split separates four steps. Leaf 1 supplies the Buchstab weight with its zero extension.
Leaf 2 supplies the two quantifiers and the range conversion `ε < η → ε ≤ 1/10^8`. Leaf 3 is
the construction of the normalised short coefficient together with its divisor bound, its
centred character mean value and the pointwise domination of the prime indicator; it also
carries the density ledger against the two discarded integrals. Leaf 4 is the remaining
exceptional character average, taken conditionally on the two boundedness properties of the
coefficient family that leaf 3 produces. The assembly below has no sorry.

Every leaf is OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165d

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 4. Step: choose the Buchstab weight. One function on the reals that solves the
defining Buchstab equations above one and is extended by zero below one, so that both the
density integrals and the zero extension of the statement have their argument.

Non-vacuity: the reading `ω = 0` fails the equations, but the construction of the standard
Buchstab function from a linear sieve pair gives a witness, so the leaf is not vacuous. The
leaf asserts nothing about any coefficient family on the short interval, so it is strictly
easier than the statement. -/
theorem leaf_buchstab_model_exists :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω := by
  sorry

/-- LEAF 2 of 4. Step: fix the two numeric quantifiers and convert the range restriction.
There is a divisor exponent `B0` and a threshold `η` with `0 < η`, `η ≤ 1/10^8`, such that
every admissible pair `B0 ≤ B`, `0 < ε`, `ε < η` gives `0 < ε` and `ε ≤ 1/10^8`.

The smallness of `η` is what lets the two discarded Buchstab integrals be evaluated at any
`ε` the statement allows. Non-vacuity: `B0 = 0` and `η = 1/10^8` satisfy all four conditions,
so the leaf is not vacuous. Tested at the degenerate readings `ε = η`, `ε → 0` and `B = B0`:
the conclusion is then `0 < ε` and `ε ≤ 1/10^8`, both true. -/
theorem leaf_thresholds :
    ∃ B0 η : ℝ, 0 < η ∧ η ≤ 1/10^8 ∧
      ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η → 0 < ε ∧ ε ≤ 1/10^8 := by
  sorry

/-- LEAF 3 of 4. Step: build the normalised short coefficient. For a Buchstab weight with the
zero extension, a divisor exponent `B` and a cutoff `ε` in `(0, 1/10^8]`, there are a density
`v0` and a family `b0` such that `v0` is at least one minus the two discarded integrals, the
family obeys the divisor bound at exponent `B`, it obeys the centred character mean value of
`RightConditions`, and it is pointwise dominated by the prime indicator on every short
interval from some point on.

This is the construction step that turns the functional equation into a coefficient family:
the discarded parts of the two-prime and four-prime decompositions give the density ledger,
and the normalisation of the centred sums gives the mean value. Strictly easier than the
statement, which in addition has to choose `ω`, `B0` and `η`, and which asks for the
exceptional character average as well. Non-vacuity: `ε → 0` is excluded by `0 < ε`, and at
`v0 = 0` the family `b0 = 0` satisfies the divisor bound and the mean value, so neither the
hypotheses nor the conclusion degenerate. -/
theorem leaf_centered_character_mean_value
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
  sorry

/-- LEAF 4 of 4. Step: average over characters and discard the exceptional set. For a family
`b0` that already carries the divisor bound at exponent `B` and the centred character mean
value at density `v0`, there is an exceptional set of characters per level `A` and per `x`,
whose cardinality is `O(q^(1/2) log x^(-2A))`, such that the squared centred sums over the
complement, averaged over the shifts `z` of the short interval, are
`O((q * sieveQ)^2 x^(11/20+eps) log x^(-A))`.

This is the third conjunct of `RightConditions` alone: it consumes the two boundedness
properties of the coefficient family and produces the exceptional set, so it does not restate
the statement and does not assert the pointwise domination. Non-vacuity: `b0 = 0` and
`v0 = 0` satisfy the two hypotheses, and then the empty exceptional set satisfies the
conclusion, so the leaf is neither vacuous nor refutable at that reading. Its content is the
case where `b0` is the normalised coefficient of leaf 3, which is why it is stated on the
boundedness properties only. -/
theorem leaf_exceptional_set_moment
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The sealed statement, assembled from the four leaves above with no sorry. Leaf 1 supplies
`ω` with its zero extension, leaf 2 the divisor exponent `B0` and the threshold `η` together
with the conversion `ε < η → 0 < ε ∧ ε ≤ 1/10^8`, leaf 3 the density `v0` and the coefficient
family `b0` with its density ledger, divisor bound, character mean value and prime domination,
and leaf 4 the exceptional character set that completes `RightConditions`. No step uses the
sealed theorem. -/
theorem lower_short_weight_analytic_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
          1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
          RightConditions ε B v0 b0 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  obtain ⟨ω, hω, hz⟩ := leaf_buchstab_model_exists
  obtain ⟨B0, η, hη, hη8, hrange⟩ := leaf_thresholds
  refine ⟨ω, hω, hz, B0, η, hη, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨hε0, hε8⟩ := hrange B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hbd, hchar, hsand⟩ :=
    leaf_centered_character_mean_value h4 h9 hω hz hε0 hε8
  obtain ⟨E, hE⟩ := leaf_exceptional_set_moment h4 h9 hω hz hε0 hε8 hbd hchar
  exact ⟨v0, b0, hv0, ⟨hbd, hchar, ⟨E, hE⟩⟩, hsand⟩

end LeanLab.BHP1997.DecompC165d
