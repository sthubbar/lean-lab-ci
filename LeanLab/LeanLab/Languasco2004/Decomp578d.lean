/-
Jia 1996 pages 261, 262 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
The Buchstab inputs, integer sieve comparison and prime summation are separate.
Analytic leaves stay OPEN. The exact supplied assemblies are CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578c

namespace LeanLab.Languasco2004.Decomp578d
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Numeric565 Reserve578
noncomputable section
attribute [local instance] Classical.propDecidable
open Decomp578c

/-- Pages 284 and 285: the weighted reciprocal triple prime sum.
Below the middle boundary Lemma 20 gives 0.5617. Above it the bound is 0.5644.
The relaxed third prime interval has the exact source half open endpoints. -/
def triplePrimeModel (Y : ℝ) (n : ℕ) : ℝ :=
  (135 / 16) * ∑ pq ∈ pairDomain true Y n,
    ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
        then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))

/-- LEAF. Jia page 284 after display 63, the model triple count to prime sum comparison.
CONDITIONAL ON the unchanged explicit solution, Lemma 20 and Lemma 21 inputs.
The global argument ranges are Geometry565.triple_four_argument and
Geometry565.triple_three_region1_argument. Only individual rough counts are replaced. -/
theorem triple_rough_upper
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        tripleMass true true 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ)) ≤
          (triplePrimeModel Y n + η) * (Y / log Y) := by sorry

/-- LEAF. Jia pages 284 and 285, the three triple prime sum integrals before display 64.
Only the weighted reciprocal prime sum is estimated. No rough integer sieve count remains.
Integral565 reduces the reciprocal inner integrals to the three Numeric565 integrals. -/
theorem triple_prime_sum_upper :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        triplePrimeModel Y n ≤ tripleOne + tripleTwo + tripleThree + η := by sorry

/-- Page 284 support: the B triple mass has no dependence on the ambient prime location N. -/
theorem triple_model_independent (N Y : ℝ) (n : ℕ) (α z : ℝ) :
    tripleMass true true N Y n α z = tripleMass true true 0 Y n α z := by rfl

/-- Jia pages 284 and 285: the exact supplied type of the sealed model_triple_upper.
CONDITIONAL ON the two proper triple inputs and the three explicit Buchstab inputs.
The eventual model estimate is pointwise, so its exceptional set is empty. -/
theorem model_triple_upper_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n < modelTriple true N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := triple_rough_upper buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.00000005 (by norm_num)
  obtain ⟨Y2, h2⟩ := triple_prime_sum_upper 0.00000005 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n <
        modelTriple true N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_upper N (localization N ε)
      (triplePrimeModel (localization N ε) n + 0.00000005)
      (tripleMass true true 0 (localization N ε) n
        ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : triplePrimeModel (localization N ε) n + 0.00000005 ≤
        tripleOne + tripleTwo + tripleThree + 0.0000001 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← triple_model_independent N] at hnorm
    change modelTriple true N (localization N ε) n ≤
      (triplePrimeModel (localization N ε) n + 0.00000005) * scale N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms triplePrimeModel
#print axioms triple_rough_upper
#print axioms triple_prime_sum_upper
#print axioms triple_model_independent
#print axioms model_triple_upper_from_parts
end
end LeanLab.Languasco2004.Decomp578d
