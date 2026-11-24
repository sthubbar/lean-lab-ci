/-
Jia 1996 pages 261, 262 and 284 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp565b.model_triple_upper, the remaining regions of Lemma 28 group five.
The rough integer comparison and the prime triple summation are separate leaves.
Analytic leaves stay OPEN. The assembly is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578c

namespace LeanLab.Languasco2004.Feed565bD
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Numeric565 Reserve578 Decomp578c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 284 and 285 remaining region formula: the weighted reciprocal triple prime sum
over the unselected pair domain. Below the middle boundary Lemma 20 gives 0.5617,
above it 0.5644, the same weights as Decomp578d.triplePrimeModel. -/
def triplePrimeModelRest (Y : ℝ) (n : ℕ) : ℝ :=
  (135 / 16) * ∑ pq ∈ pairDomain false Y n,
    ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
        then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))

/-- LEAF: Jia page 284 after display 63 transferred to the page 285 remaining regions, the model triple count to prime sum comparison. MEDIUM.
CONDITIONAL ON the explicit Buchstab existence, Lemma 20 and Lemma 21 inputs.
The argument ranges are Geometry565.triple_four_argument and
Geometry565.triple_three_remainder_argument. Only individual rough counts are replaced. -/
theorem triple_rough_upper_rest
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        tripleMass true false 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ)) ≤
          (triplePrimeModelRest Y n + η) * (Y / log Y) := by sorry

/-- LEAF: Jia page 285 remaining region formula, the triple prime sum to the three reduced logarithmic integrals restOne, restTwo and restThree. HARD.
Only the weighted reciprocal triple prime sum over the unselected domain is estimated. -/
theorem triple_prime_sum_upper_rest :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        triplePrimeModelRest Y n ≤ restOne + restTwo + restThree + η := by sorry

/-- Page 285 support: the B triple mass has no dependence on the ambient prime location N. -/
theorem triple_model_independent_rest (N Y : ℝ) (n : ℕ) (α z : ℝ) :
    tripleMass true false N Y n α z = tripleMass true false 0 Y n α z := by rfl

/-- Jia pages 284 and 285: exact type of Decomp565b.model_triple_upper.
CONDITIONAL ON the two leaves above and the Buchstab inputs of Decomp578c.
The model estimate is pointwise for large N, so its exceptional set is empty. -/
theorem model_triple_upper_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        (restOne + restTwo + restThree + 0.0000001) * scale N (localization N ε) n < modelTriple false N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := triple_rough_upper_rest buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.00000005 (by norm_num)
  obtain ⟨Y2, h2⟩ := triple_prime_sum_upper_rest 0.00000005 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      (restOne + restTwo + restThree + 0.0000001) * scale N (localization N ε) n <
        modelTriple false N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_upper N (localization N ε)
      (triplePrimeModelRest (localization N ε) n + 0.00000005)
      (tripleMass true false 0 (localization N ε) n
        ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : triplePrimeModelRest (localization N ε) n + 0.00000005 ≤
        restOne + restTwo + restThree + 0.0000001 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← triple_model_independent_rest N] at hnorm
    change modelTriple false N (localization N ε) n ≤
      (triplePrimeModelRest (localization N ε) n + 0.00000005) * scale N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms triplePrimeModelRest
#print axioms triple_rough_upper_rest
#print axioms triple_prime_sum_upper_rest
#print axioms triple_model_independent_rest
#print axioms model_triple_upper_from_leaves
end
end LeanLab.Languasco2004.Feed565bD
