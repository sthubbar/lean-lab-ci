/-
P0069, Section 4, pages 26 to 41. SPLIT of lower_mean_value_supply, FREE-nv-glm6 task3897.
The parent theorem lower_mean_value_supply in Decomp312a.lean is OPEN.
This file provides the SPLIT: LEAF lemmas and an assembly theorem lower_mean_value_supply_F3897.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Sifted312
import LeanLab.BHP1997.DecompC165c
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.Decomp312c

namespace LeanLab.BHP1997.DecompF3897
open Classical Complex DecompC165b Decomp312c Decomp132
open scoped BigOperators
open Filter

/-- LEAF. Establish the positive constants B0 and η that work for the construction.
The paper's Section 4 uses B0 = 1 (or any fixed positive exponent) and η small enough
that the sieve intervals and reference intervals align. This leaf isolates the existential
choice of B0 > 0 and η > 0 from the rest of the construction. -/
theorem leaf_positive_constants : ∃ (B0 η : ℝ), 0 < B0 ∧ 0 < η := by sorry

/-- LEAF. Construct the sifted coefficient family c0 with the divisor bound.
For the given B0, there exists c0 : ℝ → ℕ → ℝ such that
|section4SiftedFamily c0 x k| ≤ C * (k.divisors.card : ℝ)^B0 for all x, k.
This captures the sieve weight construction from pages 26-27, 4.7 and 4.11,
using the truncated Möbius weight truncatedMobiusWeight. -/
theorem leaf_c0_divisor_bound {B0 : ℝ} (hB0 : 0 < B0) :
    ∃ (c0 : ℝ → ℕ → ℝ), ∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0 := by sorry

/-- LEAF. Construct the auxiliary family b with divisor bound, both mean values 4.1,
and the reference interval density u0 ∈ (0.9953, 1].
This family is chosen with a smooth weight tapering at x/2 and 2x (as noted in the
Gate QUESTION) to avoid the principal character obstruction at sharp cutoffs.
Pages 32-33 and 41 cover the density calculation and the smoothing. -/
theorem leaf_b_construction {B0 η : ℝ} (hB0 : 0 < B0) (hη : 0 < η) :
    ∀ (ε : ℝ), 0 < ε → ε < η →
      ∃ (u0 b : ℝ → ℕ → ℝ), 0.9953 < u0 ∧ u0 ≤ 1 ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u0 b := by sorry

/-- LEAF. The absolute approximation on the left interval I:
ShortApproximation ε (section4SiftedFamily c0) b.
This is the analytic band-sum estimate from pages 26-27 (4.7, 4.11, 4.12)
and the fundamental lemma of sieve theory, assembled via
approximation_of_band_sum using the truncated convolution family. -/
theorem leaf_short_approximation {B0 η : ℝ} (hB0 : 0 < B0) (hη : 0 < η) :
    ∀ (ε : ℝ), 0 < ε → ε < η →
      ∀ (c0 b : ℝ → ℕ → ℝ),
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) →
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) →
        ShortApproximation ε (section4SiftedFamily c0) b := by sorry

/-- LEAF. The pointwise upper bound on the left interval I:
section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k for all sufficiently large x
and k ∈ leftInterval ε x.
This is the sieve minorant property from page 41, display 4.25, following from
the construction of c0 as a lower sieve weight. -/
theorem leaf_pointwise_minorant {B0 η : ℝ} (hB0 : 0 < B0) (hη : 0 < η) :
    ∀ (ε : ℝ), 0 < ε → ε < η →
      ∀ (c0 : ℝ → ℕ → ℝ),
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) →
        ∃ (X : ℝ), ∀ (x : ℝ), X ≤ x →
          ∀ (k : ℕ), k ∈ leftInterval ε x → section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k := by sorry

/-- Assembly theorem: lower_mean_value_supply_F3897.
This is the exact statement of lower_mean_value_supply from Decomp312a.lean,
proved from the LEAF lemmas above with NO sorry. -/
theorem lower_mean_value_supply_F3897 (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < B0 ∧ 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ (u0 : ℝ) (c0 b : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧
        (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
        MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
        ShortApproximation ε (section4SiftedFamily c0) b ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k := by
  obtain ⟨B0, η, hB0, hη⟩ := leaf_positive_constants
  refine' ⟨B0, η, hB0, hη, _⟩
  intro ε hε hεη
  have h₁ : ∃ (c0 : ℝ → ℕ → ℝ), ∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0 :=
    leaf_c0_divisor_bound hB0
  obtain ⟨c0, Cc0, hc0⟩ := h₁
  have h₂ : ∃ (u0 b : ℝ → ℕ → ℝ), 0.9953 < u0 ∧ u0 ≤ 1 ∧
    (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
    MeanValue41 ε b ∧ ReferenceDensity u0 b :=
    leaf_b_construction hB0 hη ε hε hεη
  obtain ⟨u0, b, hu0_gt, hu0_le, Cb, hb, hmv, hrd⟩ := h₂
  have h₃ : ShortApproximation ε (section4SiftedFamily c0) b :=
    leaf_short_approximation hB0 hη ε hε hεη c0 b ⟨Cc0, hc0⟩ ⟨Cb, hb⟩
  have h₄ : ∃ (X : ℝ), ∀ (x : ℝ), X ≤ x →
      ∀ (k : ℕ), k ∈ leftInterval ε x → section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k :=
    leaf_pointwise_minorant hB0 hη ε hε hεη c0 ⟨Cc0, hc0⟩
  refine' ⟨u0, c0, b, hu0_gt, hu0_le, ⟨Cc0, hc0⟩, ⟨Cb, hb⟩, hmv, hrd, h₃, h₄⟩

end LeanLab.BHP1997.DecompF3897