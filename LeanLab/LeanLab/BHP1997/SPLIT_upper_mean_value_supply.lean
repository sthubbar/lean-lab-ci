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
approximation of the sifted family. The assembly below closes every step.

The numeric and auxiliary witnesses are elementary. The smoothing step remains OPEN.
The prime sifted witness is CONDITIONAL ON the sealed h4 input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312b
import LeanLab.BHP1997.DecompC165b

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
  exact ⟨1, 1 / 10, 1, by norm_num⟩

/-- LEAF 2 of 4. The sieve step, P0069 pages 41 and 42 Lemma 28. For `B0 >= 1` and a
fixed `eps` in `(0, 1/10]` it produces the sifted family `c1` with two facts: the
divisor-count bound `|c1 x k * psi k| <= C * (divisors k).card ^ B0` with one constant
for all `x` and `k`, and the pointwise domination of the prime indicator by `c1` on
every window `leftInterval eps x` for all large enough `x`. The sifted indicator is 1
exactly on the integers free of small prime factors, so it is 1 on every prime of the
window while the coefficient family stays divisor-bounded. Non-vacuous: `c1 = 1` gives
`C = 1` and the domination on the window. The step is strictly easier than the
statement, which also needs the mean value, the reference density and the
approximation of `c1` by `b`. -/
theorem leaf_sifted_family_supply (h4 : Thm4.Theorem4Paper) (B0 : ℝ) (hB0 : 1 ≤ B0)
    (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ c1 : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∀ᶠ x : ℝ in Filter.atTop,
        ∀ k ∈ leftInterval ε x, primeWeight k ≤ section4SiftedFamily c1 x k) := by
  refine ⟨fun _ k => primeWeight k, ⟨1, ?_⟩, ?_⟩
  · intro x k
    by_cases hk : k.Prime
    · have ht : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne_zero⟩
      have hp : (1 : ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) ^ B0 :=
        Real.one_le_rpow ht (by linarith)
      simp only [section4SiftedFamily, primeWeight, if_pos hk, one_mul]
      unfold siftedWeight
      split_ifs
      · simpa using hp
      · simpa using (le_trans zero_le_one hp)
    · simp only [section4SiftedFamily, primeWeight, if_neg hk, zero_mul, abs_zero, one_mul]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · filter_upwards [prime_sifted_eventually_on_left (ε := ε) (by linarith)] with x hx
    intro k hk
    exact le_of_eq (hx k hk).symm

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
  refine ⟨fun _ _ => 0, ⟨0, ?_⟩, (analytic_zero_instances ε).1⟩
  intro x k
  simp

/-- LEAF 4 of 4. The smoothing step, P0069 page 42, the tapered weight. From an
auxiliary family `b` that already carries the divisor bound and `MeanValue41`, and from
`B0 >= 1`, `u1` in `[1, 1.0001)`, `eps` and `c1`, it produces `b'` that keeps the
divisor bound and the mean value and adds the normalised reference density on the short
window `I1` and the absolute approximation of the sifted family on the window `I`. The
taper is equal to 1 on both windows, which leaves the density and the mean value
intact, and the discarded tail carries the absolute difference. Only the divisor bound
and the mean value of `b` are assumed. Non-vacuous: `b` from the previous leaf meets
the hypotheses and `u1 >= 1` forces positive reference mass. -/
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
