/-
Jia 1996 pages 261, 262 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
The Buchstab inputs, integer sieve comparison and prime summation are separate.
Analytic leaves stay OPEN. The exact supplied assemblies are CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Reserve578
import LeanLab.Languasco2004.Buchstab578
import LeanLab.Languasco2004.Decomp578e

namespace LeanLab.Languasco2004.Decomp578c
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Numeric565 Reserve578
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 283 display 60: the constant lower approximation to the reciprocal pair prime sum.
The source finite caps and the printed p truncation are kept. -/
def pairPrimeModel (Y : ℝ) (n : ℕ) : ℝ :=
  (0.5612 * (135 / 16)) *
    ∑ pq ∈ pairDomain true Y n, 1 / ((pq.1 : ℝ) * (pq.2 : ℝ))

/-- Jia page 261 display 40 and its integrated form in display 41.
Existence of the continuous delay equation solution is isolated from every numerical bound.
No extension of the initial logarithmic segment is silently assumed. -/
theorem buchstab_solution :
    ∃ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) ∧
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) ∧
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) := by
  exact Buchstab578.buchstab_exists

/-- Jia pages 261 and 262 Lemma 20 parts ii and iii.
CONDITIONAL ON the two finite grid leaves in Decomp578e.
These are global bounds on the actual delay equation solution, not on the initial segment.
The printed grid base checks on three through four and four through five remain required. -/
theorem lemma20_global_bounds :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t) →
      (∀ u : ℝ, 3 ≤ u → w u ≤ 0.5644) ∧
      (∀ u : ℝ, 4 ≤ u → 0.5612 ≤ w u ∧ w u ≤ 0.5617) := by
  exact Decomp578e.lemma20_bounds_from_grids

/-- LEAF. Jia page 262 Lemma 21, unnumbered displayed rough integer asymptotic.
The paper refers to Lemma 5 of reference 9 and gives the prime number theorem case.
The arbitrary positive tolerance records the source sufficiently large t and z convention.
No complementary prime and no exceptional set occurs in this input. -/
theorem lemma21_rough_asymptotic :
    ∀ w : ℝ → ℝ, ContinuousOn w (Set.Ici 1) →
      (∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u) →
      (∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ s in (1 : ℝ)..(u - 1), w s) →
    ∀ η : ℝ, 0 < η → ∃ T Z : ℝ, 1 < T ∧ 1 < Z ∧
      ∀ t z : ℝ, T ≤ t → Z ≤ z → z ≤ t →
        |((Sieve565.sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
            w (log t / log z) * (t / log z)| ≤ η * (t / log z) := by sorry

/-- LEAF. Jia page 283 display 60, first model equality and application of Lemma 20.
CONDITIONAL ON the explicit Buchstab existence, global bounds and Lemma 21 inputs.
Only replace the individual rough integer counts by a constant weighted reciprocal prime sum.
The sum over prime pairs has not yet been replaced by an integral. -/
theorem pair_rough_lower
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        (pairPrimeModel Y n - η) * (Y / log Y) ≤
          pairMass true true 0 Y n (Y ^ (16 / 135 : ℝ)) := by sorry

/-- LEAF. Jia page 283 display 60, the pair prime sum to double integral step.
Only the reciprocal pair prime sum is estimated. No rough integer count remains.
The fixed truncated integral is pairCoefficient, without the source numerical reserve. -/
theorem pair_prime_sum_lower :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) → pairCoefficient - η ≤ pairPrimeModel Y n := by sorry

/-- Page 283 support: the B pair mass has no dependence on the ambient prime location N. -/
theorem pair_model_independent (N Y : ℝ) (n : ℕ) (z : ℝ) :
    pairMass true true N Y n z = pairMass true true 0 Y n z := by rfl

/-- Jia page 283 display 60: the exact supplied type of the sealed model_pair_lower.
CONDITIONAL ON the two finite Buchstab grids and the three smaller analytic inputs above.
The model estimate is pointwise for large N, so its exceptional set is empty. -/
theorem model_pair_lower_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        modelPair true N (localization N ε) n < (mainOne + 0.0000004) * scale N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := pair_rough_lower buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.00000005 (by norm_num)
  obtain ⟨Y2, h2⟩ := pair_prime_sum_lower 0.00000005 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      modelPair true N (localization N ε) n <
        (mainOne + 0.0000004) * scale N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_lower N (localization N ε)
      (pairPrimeModel (localization N ε) n - 0.00000005)
      (pairMass true true 0 (localization N ε) n ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : mainOne + 0.0000004 ≤ pairPrimeModel (localization N ε) n - 0.00000005 := by
      linarith [pair_coefficient_reserve]
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← pair_model_independent N] at hnorm
    change (pairPrimeModel (localization N ε) n - 0.00000005) * scale N (localization N ε) n ≤
      modelPair true N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms pairPrimeModel
#print axioms buchstab_solution
#print axioms lemma20_global_bounds
#print axioms lemma21_rough_asymptotic
#print axioms pair_rough_lower
#print axioms pair_prime_sum_lower
#print axioms pair_model_independent
#print axioms model_pair_lower_from_parts
end
end LeanLab.Languasco2004.Decomp578c
