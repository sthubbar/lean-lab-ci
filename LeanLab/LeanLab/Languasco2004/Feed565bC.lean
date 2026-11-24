/-
Jia 1996 pages 261, 262 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp565b.model_pair_lower, the remaining regions of Lemma 28 group five.
The rough integer comparison and the prime pair summation are separate leaves.
Analytic leaves stay OPEN. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578c

namespace LeanLab.Languasco2004.Feed565bC
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Numeric565 Reserve578 Decomp578c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 285 remaining region formula with page 283 display 60: the constant lower
approximation to the reciprocal pair prime sum over the unselected pair domain.
Lemma 20 part iii gives the weight 0.5612, as for Decomp578c.pairPrimeModel. -/
def pairPrimeModelRest (Y : ℝ) (n : ℕ) : ℝ :=
  (0.5612 * (135 / 16)) *
    ∑ pq ∈ pairDomain false Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))

/-- LEAF: Jia page 283 display 60 transferred to the page 285 remaining regions, first model equality and application of Lemma 20. MEDIUM.
CONDITIONAL ON the explicit Buchstab existence, global bounds and Lemma 21 inputs.
The Buchstab argument is at least four by Geometry565.mainRest_argument.
Only the individual rough integer counts are replaced by the reciprocal prime sum. -/
theorem pair_rough_lower_rest
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        (pairPrimeModelRest Y n - η) * (Y / log Y) ≤
          pairMass true false 0 Y n (Y ^ (16 / 135 : ℝ)) := by sorry

/-- LEAF: Jia page 285 remaining region formula, the pair prime sum to double integral step behind mainRest. HARD.
Only the reciprocal pair prime sum over the unselected domain is estimated.
The untruncated integral is mainRest plus its source reserve 0.000001. -/
theorem pair_prime_sum_lower_rest :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) → mainRest + 0.000001 - η ≤ pairPrimeModelRest Y n := by sorry

/-- Page 285 support: the B pair mass has no dependence on the ambient prime location N. -/
theorem pair_model_independent_rest (N Y : ℝ) (n : ℕ) (z : ℝ) :
    pairMass true false N Y n z = pairMass true false 0 Y n z := by rfl

/-- Jia page 285 with display 60: exact type of Decomp565b.model_pair_lower.
CONDITIONAL ON the two leaves above and the Buchstab inputs of Decomp578c.
The model estimate is pointwise for large N, so its exceptional set is empty. -/
theorem model_pair_lower_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        modelPair false N (localization N ε) n < (mainRest + 0.0000004) * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := pair_rough_lower_rest buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.0000003 (by norm_num)
  obtain ⟨Y2, h2⟩ := pair_prime_sum_lower_rest 0.0000003 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      modelPair false N (localization N ε) n <
        (mainRest + 0.0000004) * scale N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_lower N (localization N ε)
      (pairPrimeModelRest (localization N ε) n - 0.0000003)
      (pairMass true false 0 (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : mainRest + 0.0000004 ≤ pairPrimeModelRest (localization N ε) n - 0.0000003 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← pair_model_independent_rest N] at hnorm
    change (pairPrimeModelRest (localization N ε) n - 0.0000003) * scale N (localization N ε) n ≤
      modelPair false N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms pairPrimeModelRest
#print axioms pair_rough_lower_rest
#print axioms pair_prime_sum_lower_rest
#print axioms pair_model_independent_rest
#print axioms model_pair_lower_from_leaves
end
end LeanLab.Languasco2004.Feed565bC
