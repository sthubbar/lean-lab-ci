/-
Feed split S82 burst-20261122 of `upper_mean_value_supply` in
LeanLab.BHP1997.Decomp312b, P0069 Section 4, pages 41 and 42.

This file does not import Decomp312b, so Decomp312b can import it and close its
sorry with `upper_mean_value_supply_of_leaves`. It replaces the earlier split leaf
`leaf_smoothed_reference_family` of SPLIT_upper_mean_value_supply, which takes an
arbitrary auxiliary family and is false, by a corrected leaf: the tapered family
`b` is required to agree with the sifted family on the window I and on the reference
interval I1, which is what the page 42 taper with weight 1 on I and I1 gives. The
absolute approximation on I and the transfer of the I1 density to `b` are then
PROVED below, not assumed.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312a

namespace LeanLab.BHP1997.Decomp312bFeed1122
open Classical Complex DecompC165b Decomp312a Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- LEAF: P0069 pages 41 and 42, the numeric constants of the upper construction.
One divisor exponent at least 1 and one threshold in (0, 1/10]. Class EASY. -/
theorem leaf_constants :
    ∃ B0 η : ℝ, 1 ≤ B0 ∧ 0 < η ∧ η ≤ 1 / 10 := by
  exact ⟨1, 1 / 10, le_rfl, by norm_num, le_rfl⟩

/-- LEAF: P0069 pages 41 and 42, the upper seven-step Buchstab construction with
Lemma 28, the final density computation, and the page 42 taper. For a fixed
`ε ∈ (0, 1/10]` it supplies the density constant `u1 ∈ [1, 1.0001)`, the sifted
coefficient family `c1` with its divisor bound and the eventual domination of the
prime indicator on I, the I1 density of the sifted family, and a tapered family `b`
with its divisor bound and the mean value 4.1 that agrees with the sifted family on
I and on I1 for all large `x`. Class HARD. Unlike the false unrestricted smoothing
leaf of SPLIT_upper_mean_value_supply, the family `b` is constructed together with
`c1`, so the counterexample there does not apply. -/
theorem leaf_upper_sifted_tapered (h4 : Thm4.Theorem4Paper) (B0 : ℝ) (hB0 : 1 ≤ B0)
    (ε : ℝ) (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    ∃ (u1 : ℝ) (c1 b : ℝ → ℕ → ℝ),
      1 ≤ u1 ∧ u1 < 1.0001 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c1 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u1 (section4SiftedFamily c1) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        primeWeight k ≤ section4SiftedFamily c1 x k) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x,
        b x k = section4SiftedFamily c1 x k) ∧
      (∀ᶠ x : ℝ in atTop, ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        b x k = section4SiftedFamily c1 x k) := by
  sorry

/-- Agreement on the window I for all large `x` gives the absolute approximation
with zero error. PROVED. -/
theorem shortApproximation_of_eventually_eq {ε : ℝ} {a b : ℝ → ℕ → ℝ}
    (h : ∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x, b x k = a x k) :
    ShortApproximation ε a b := by
  intro A _
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  refine ⟨0, X, fun x hx => ?_⟩
  have hs : (∑ k ∈ leftInterval ε x, |a x k - b x k|) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hX x hx k hk, sub_self, abs_zero]
  rw [hs]
  simp

/-- Agreement on I1 for all large `x` transfers the reference density. PROVED. -/
theorem referenceDensity_of_eventually_eq {u : ℝ} {a b : ℝ → ℕ → ℝ}
    (h : ∀ᶠ x : ℝ in atTop, ∀ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
      b x k = a x k)
    (ha : ReferenceDensity u a) : ReferenceDensity u b := by
  intro A hA
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  obtain ⟨C, X', hC⟩ := ha A hA
  refine ⟨C, max X X', fun x hx q hq hqA χ => ?_⟩
  have heq : referenceAverage b x χ = referenceAverage a x χ := by
    unfold referenceAverage
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [hX x (le_trans (le_max_left _ _) hx) k hk]
  rw [heq]
  exact hC x (le_trans (le_max_right _ _) hx) q hq hqA χ

/-- The statement of `upper_mean_value_supply` in Decomp312b, assembled from the
leaves above with no sorry. CONDITIONAL ON `leaf_upper_sifted_tapered`. -/
theorem upper_mean_value_supply_of_leaves (h4 : Thm4.Theorem4Paper) :
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
  obtain ⟨B0, η, hB0, hη, hη10⟩ := leaf_constants
  refine ⟨B0, η, lt_of_lt_of_le zero_lt_one hB0, hη, ?_⟩
  intro ε hε hεη
  have hε10 : ε ≤ 1 / 10 := le_of_lt (lt_of_lt_of_le hεη hη10)
  obtain ⟨u1, c1, b, hu, hu', hc, hb, hm, hd, hdom, hI, hI1⟩ :=
    leaf_upper_sifted_tapered h4 B0 hB0 ε hε hε10
  obtain ⟨X, hX⟩ := eventually_atTop.mp hdom
  exact ⟨u1, c1, b, hu, hu', hc, hb, hm, referenceDensity_of_eventually_eq hI1 hd,
    shortApproximation_of_eventually_eq hI, X, hX⟩

end LeanLab.BHP1997.Decomp312bFeed1122
