/-
Split of `upper_mean_value_supply` in LeanLab.BHP1997.Decomp312b into leaves.
The sealed statement is unchanged; the target theorem is neither imported nor used.

The statement asks for one divisor exponent `B0`, one `ε`-threshold `η`, and, for every
`0 < ε < η`, one density constant `u1` in [1, 1.0001), a sifted coefficient family `c1`
and an auxiliary family `b`, such that the sifted family carries a divisor-count bound,
the prime indicator is pointwise dominated by the sifted family on the window, `b`
carries its own divisor-count bound and satisfies the character mean value and the
normalised reference density, and `b` approximates the sifted family in absolute value
on the window.

The split separates four steps. Leaf 1 fixes the numeric constants. Leaf 2 is the sieve
step: it builds the sifted family with its divisor bound and the pointwise prime
domination on the window. Leaf 3 is the mean-value step: it builds an auxiliary family
with the divisor bound and the character mean value. Leaf 4 is the smoothing step: from
an auxiliary family that already carries the mean value it produces one that keeps the
divisor bound and the mean value and adds the reference density and the absolute
approximation of the sifted family. The assembly below has no sorry.

Every leaf is OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312b

namespace LeanLab.BHP1997.Decomp312b
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- LEAF 1 of 4. The numeric constants only: one divisor exponent at least 1, one
threshold in (0, 1/10], and one density constant in [1, 1.0001). This is the step that
fixes the two quantifiers `B0` and `η` of the statement and the constant `u1` that the
reference density is later measured against. It asserts no estimate on any family.
Checked at the degenerate readings: `B0 = 1`, `η = 1/10`, `u1 = 1` satisfy all five
conjuncts, and `u1 = 1` shows the half-open range is nonempty, so the leaf is not
vacuous. -/
theorem leaf_thresholds_and_density_constant :
    ∃ B0 η u1 : ℝ, 1 ≤ B0 ∧ 0 < η ∧ η ≤ 1 / 10 ∧ 1 ≤ u1 ∧ u1 < 1.0001 := by
  sorry

/-- LEAF 2 of 4. The sieve step. For a divisor exponent `B0 ≥ 1` and a fixed
`ε ∈ (0, 1/10]` it produces the sifted family `c1` together with two facts: the
divisor-count bound `|c1 x k * ψ(k)| ≤ C * (divisors k).card ^ B0` with one constant
for all `x` and `k`, and the pointwise domination of the prime indicator by the sifted
family on every window `leftInterval ε x` for all large enough `x`. This is the step
that builds an upper sieve out of the weight conditions of the hypothesis `h4`: the
sifted indicator is 1 exactly on the integers free of small prime factors, so it is 1
on every prime of the window while the coefficient family stays divisor-bounded.
Checked at the degenerate readings: `c1 = 1` gives `C = 1`, `B0 = 1` and the domination
on the window, so the two conjuncts are jointly satisfiable and the leaf is not
vacuous. The step is strictly easier than the statement, which additionally needs the
mean value, the reference density and the approximation of `c1` by `b`. -/
theorem leaf_sifted_family_supply (h4 : Thm4.Theorem4Paper) (B0 : ℝ) (hB0 : 1 ≤ B0)
    (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ c1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∀ᶠ x : ℝ in Filter.atTop,
        ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k) := by
  sorry

/-- LEAF 3 of 4. The mean-value step. For a divisor exponent `B0 ≥ 1` and a fixed
`ε ∈ (0, 1/10]` it produces an auxiliary family `b` with its own divisor-count bound
and with the two-height character mean value on the wide window `[x/2, 2x]`. The family
is left free, so nothing here fixes a density normalisation or an approximation of the
sifted family. Non-vacuity: `b = 0` satisfies the divisor bound with `C = 0` and makes
the mean-value integral vanish, so the leaf is not vacuously true. The step is strictly
easier than the statement, which additionally pins `b` to one density constant and to
the sifted family. -/
theorem leaf_auxiliary_mean_value (B0 : ℝ) (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε)
    (hε10 : ε ≤ 1 / 10) :
    ∃ b : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b := by
  sorry

/-- LEAF 4 of 4. The smoothing step. From an auxiliary family `b` that already carries
the divisor bound and the mean value, and from any divisor exponent `B0 ≥ 1`, density
constant `u1` in [1, 1.0001) and sifted family `c1`, it produces a family `b'` that
keeps the divisor bound and the mean value and additionally realises the normalised
reference density on the short window `I1` and the absolute approximation of the sifted
family on the window `I`. The tapered weight is the mechanism: it is equal to 1 on both
windows, which leaves the local density and the mean value intact, and the discarded
tail carries the absolute difference. Only the divisor bound and the mean value of `b`
are assumed, so the leaf neither restates the statement nor assumes its conclusion.
Non-vacuity: the hypothesis set is met by `b` from the previous leaf, and the produced
`b'` must have positive reference mass since `u1 ≥ 1`, so the conclusion is not
degenerate. -/
theorem leaf_smoothed_reference_family (B0 : ℝ) (hB0 : 1 ≤ B0) (ε : ℝ) (hε : 0 < ε)
    (hε10 : ε ≤ 1 / 10) (u1 : ℝ) (hu1 : 1 ≤ u1) (hu1' : u1 < 1.0001)
    (c1 b : ℝ → ℕ → ℝ)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0)
    (hm : MeanValue41 ε b) :
    ∃ b' : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |b' x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b' ∧ ReferenceDensity u1 b' ∧
      ShortApproximation ε (section4SiftedFamily c1) b' := by
  sorry

/-- The same statement as the sealed supply theorem, assembled from the four leaves
above with no sorry. Leaf 1 supplies `B0`, `η` and `u1`; the range check `ε < η → ε ≤
1/10` is what lets leaves 2, 3 and 4 be used; leaf 2 supplies `c1` with its divisor
bound and the pointwise prime domination, converted from the eventual form to the
explicit `∃ X` by unfolding the at-top filter; leaf 3 supplies `b` with the divisor
bound and the mean value; leaf 4 replaces `b` by `b'` with the divisor bound, the mean
value, the reference density and the approximation, and `b'` is the family reported in
the conclusion. No step uses the sealed theorem. -/
theorem upper_mean_value_supply_split (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
          C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u1 b ∧
        ShortApproximation ε (section4SiftedFamily c1) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k := by
  obtain ⟨B0, η, u1, hB01, hη0, hη10, hu1, hu1'⟩ :=
    leaf_thresholds_and_density_constant
  refine ⟨B0, η, lt_of_lt_of_le zero_lt_one hB01, hη0, ?_⟩
  intro ε hε hεη
  have hε10 : ε ≤ 1 / 10 := le_of_lt (lt_of_lt_of_le hεη hη10)
  obtain ⟨c1, hc1, hdom⟩ := leaf_sifted_family_supply h4 B0 hB01 ε hε hε10
  obtain ⟨b, hb, hm⟩ := leaf_auxiliary_mean_value B0 hB01 ε hε hε10
  obtain ⟨b', hb', hm', hden, happ⟩ :=
    leaf_smoothed_reference_family B0 hB01 ε hε hε10 u1 hu1 hu1' c1 b hb hm
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hdom
  exact ⟨u1, c1, b', hu1, hu1', hc1, hb', hm', hden, happ, X, hX⟩

end LeanLab.BHP1997.Decomp312b
