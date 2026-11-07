/-
Split of `lower_mean_value_supply` in LeanLab.BHP1997.Decomp312a into leaves.
The sealed statement is unchanged; the target theorem is neither imported nor used.

The statement asks for one divisor exponent `B0`, one `ε`-threshold `η`, one density
constant `u0` in (0.9953, 1], a sifted coefficient family `c0` and an auxiliary family
`b`, such that on every window of width `2 x^(11/20+eps)` the sifted family is
pointwise dominated by the prime indicator and both families obey a divisor-count
bound, while `b` satisfies the character mean value and the reference density and
approximates the sifted family in absolute value.

The split separates three steps. Leaf 1 picks the three numeric constants. Leaf 2 is
the sieve step: it builds the sifted family with its divisor bound and the pointwise
prime domination on the window. Leaf 3 is the auxiliary step: from the divisor bound
of the sifted family alone it builds `b` with its own divisor bound, the mean value,
the reference density and the absolute approximation. Nothing else is needed, so the
assembly below has no sorry.

Every leaf is OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312a

namespace LeanLab.BHP1997.Decomp312a
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- LEAF 1 of 3. The numeric constants only: one divisor exponent at least 1, one
threshold in (0, 1/10], and one density constant in (0.9953, 1]. This is the step that
fixes the two quantifiers `B0` and `η` of the statement and the constant `u0` that the
reference density is later measured against. It asserts no estimate on any family.
Checked at the degenerate readings: `B0 = 1`, `η = 1/10`, `u0 = 1` satisfy all five
conjuncts, so the leaf is not vacuous. -/
theorem leaf_thresholds_and_density_constant :
    ∃ B0 η u0 : ℝ, 1 ≤ B0 ∧ 0 < η ∧ η ≤ 1 / 10 ∧ 0.9953 < u0 ∧ u0 ≤ 1 := by
  sorry

/-- LEAF 2 of 3. The sieve step. For a divisor exponent `B0 ≥ 1` and a fixed
`ε ∈ (0, 1/10]` it produces the sifted family `c0` together with two facts: the
divisor-count bound `|c0 x k * ψ(k)| ≤ C * (divisors k).card ^ B0` with one constant
for all `x` and `k`, and the pointwise domination of the sifted family by the prime
indicator on every window `leftInterval ε x` and all large enough `x`.

This is the step that forces a sieve with a prime-producing upper bound: the constant
`c0 = 0` already gives the divisor bound, so the two conjuncts are jointly satisfiable
and the leaf is not vacuous, and the second conjunct is the content. The step is
strictly easier than the statement, which additionally needs the mean value, the
reference density and the approximation of `c0` by `b`. -/
theorem leaf_sifted_family_supply (B0 : ℝ) (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε)
    (hε10 : ε ≤ 1 / 10) :
    ∃ c0 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∀ᶠ x : ℝ in Filter.atTop,
        ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k) := by
  sorry

/-- LEAF 3 of 3. The auxiliary step. For a divisor exponent `B0 ≥ 1`, a fixed
`ε ∈ (0, 1/10]`, a density constant `u0` in (0.9953, 1], and any sifted family `c0`
carrying the divisor-count bound of the previous leaf, it produces a family `b` with
the same kind of divisor bound, the character mean value on both heights, the
normalised reference density `u0 / log x` and the absolute approximation of the sifted
family on the window.

The only hypothesis on `c0` is its divisor bound, so the leaf does not assume the
prime domination and does not restate the statement. It is strictly easier: the
statement asks in addition that `u0` and `c0` come from the sieve step. Non-vacuity:
the hypothesis is met by `c0 = 0` with `C = 0`, and `b` is required to exist for that
reading. -/
theorem leaf_auxiliary_family_supply (B0 : ℝ) (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε)
    (hε10 : ε ≤ 1 / 10) (u0 : ℝ) (hu0 : 0.9953 < u0) (hu01 : u0 ≤ 1)
    (c0 : ℝ → ℕ → ℝ)
    (hc0 : ∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0) :
    ∃ b : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
      ShortApproximation ε (section4SiftedFamily c0) b := by
  sorry

/-- LEAF. The same statement as the sealed supply theorem, assembled from the three
leaves above with no sorry. Leaf 1 supplies `B0`, `η` and `u0`; the range check
`ε < η → ε ≤ 1/10` is what lets leaves 2 and 3 be used; leaf 2 supplies `c0` with its
divisor bound and the pointwise prime domination, converted from the eventual form to
the explicit `∃ X` by unfolding the at-top filter; leaf 3 supplies `b` with the
remaining four conjuncts. No step uses the sealed theorem. -/
theorem lower_mean_value_supply_split (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u0 : ℝ) (c0 b : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
        ShortApproximation ε (section4SiftedFamily c0) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k := by
  obtain ⟨B0, η, u0, hB01, hη0, hη10, hu0, hu01⟩ := leaf_thresholds_and_density_constant
  refine ⟨B0, η, lt_of_lt_of_le zero_lt_one hB01, hη0, ?_⟩
  intro ε hε hεη
  have hε10 : ε ≤ 1 / 10 := le_of_lt (lt_of_lt_of_le hεη hη10)
  obtain ⟨c0, hc0, hlo⟩ := leaf_sifted_family_supply B0 hB01 ε hε hε10
  obtain ⟨b, hb, hm, hd, happ⟩ :=
    leaf_auxiliary_family_supply B0 hB01 ε hε hε10 u0 hu0 hu01 c0 hc0
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hlo
  exact ⟨u0, c0, b, hu0, hu01, hc0, hb, hm, hd, happ, X, hX⟩

end LeanLab.BHP1997.Decomp312a
