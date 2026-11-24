/-
Jia 1996 pages 262 and 279, Lemma 21 and the Omega4 model after displays 53 to 56:
split of `Decomp568a.model4_asymptotic` into the uniform rough count, the weight bound
and the prime double sum against the Buchstab integral.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The three LEAF inputs remain OPEN; the assembly below is proved from them.
-/
import LeanLab.Languasco2004.Decomp568a

namespace LeanLab.Languasco2004.Feed568aModel4
open Finset Real Decomp568a BuchstabInitial316
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 262, Lemma 21, the Buchstab asymptotic for rough integers,
applied uniformly to the Omega4 pairs of page 279. HARD.
For q < p primes of the Omega4 domain, the multiples a of p q in the interval Y to 2Y
free of primes below q are m p q with m in the interval Y / p q to 2 Y / p q free of
primes below q; the exponent log of Y / p q over log q lies in 17/8 to 3, where the
explicit initial Buchstab formula holds, so the count is at least the main term
minus η times Y / p q log q for all large Y, uniformly in the pair. -/
theorem rough_count_lower :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ p q : ℕ, p.Prime → q.Prime →
      Y ^ (41 / 180 : ℝ) < (p : ℝ) → (p : ℝ) ≤ Y ^ (8 / 33 : ℝ) →
      (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) → (q : ℝ) < p →
      (buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) - η) *
          (Y / ((p : ℝ) * q * Real.log q)) ≤ (modelSifted Y (p * q) q : ℝ) := by
  sorry

/-- LEAF: Jia page 279, the error weights of Lemma 21 summed over the Omega4 pairs are
of the order Y / log Y. HARD.
Here log q is at least 211/990 log Y and the reciprocal prime sums over the dyadic
ranges of p and q are bounded by Mertens' theorem. -/
theorem pair_weight_upper :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          Y / ((p : ℝ) * q * Real.log q) ≤ K * (Y / Real.log Y) := by
  sorry

/-- LEAF: Jia page 279 after displays 53 to 56, the prime double sum of the Buchstab main
terms is at least the Omega4 integral times Y / log Y for large Y. HARD.
With t = log p / log Y and u = log q / log Y the summand is Y / log Y times
the kernel of `Kernel568.region4_kernel` divided by p q, and the prime number theorem
with partial summation turns the double reciprocal prime sum into the integral `integral4`. -/
theorem kernel_sum_lower :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (integral4 - η) * (Y / Real.log Y) ≤
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) *
            (Y / ((p : ℝ) * q * Real.log q)) := by
  sorry

/-- Jia page 279: the exact statement of `Decomp568a.model4_asymptotic`, proved from the
LEAF inputs `rough_count_lower`, `pair_weight_upper` and `kernel_sum_lower`. -/
theorem model4_asymptotic_from_leaves :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (integral4 - η) * (Y / Real.log Y) ≤ model4 Y := by
  intro η hη
  obtain ⟨K, hK, Y1, hW⟩ := pair_weight_upper
  obtain ⟨Y2, hM⟩ := kernel_sum_lower (η / 2) (by positivity)
  have hη' : 0 < η / (2 * (K + 1)) := by positivity
  obtain ⟨Y3, hR⟩ := rough_count_lower (η / (2 * (K + 1))) hη'
  refine ⟨max 1 (max Y1 (max Y2 Y3)), ?_⟩
  intro Y hY
  have hY0 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : Y1 ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hY2 : Y2 ≤ Y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hY3 : Y3 ≤ Y :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  set e := η / (2 * (K + 1)) with he
  have hpair :
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          (buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) - e) *
            (Y / ((p : ℝ) * q * Real.log q)) ≤ model4 Y := by
    unfold model4
    apply sum_le_sum
    intro p hp
    obtain ⟨_, hpP, hp1, hp2⟩ := mem_filter.mp hp
    apply sum_le_sum
    intro q hq
    obtain ⟨_, hqP, hq1, hq2⟩ := mem_filter.mp hq
    exact hR Y hY3 p q hpP hqP hp1 hp2 hq1 hq2
  have hexp :
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          (buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) - e) *
            (Y / ((p : ℝ) * q * Real.log q)) =
      ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          buchstabInitial (Real.log (Y / ((p : ℝ) * q)) / Real.log q) *
            (Y / ((p : ℝ) * q * Real.log q)) -
      e * ∑ p ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (41 / 180 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Y ^ (8 / 33 : ℝ)),
        ∑ q ∈ (range (⌊2 * Y⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧
          (p : ℝ)⁻¹ * Y ^ (41 / 90 : ℝ) < (q : ℝ) ∧ (q : ℝ) < p),
          Y / ((p : ℝ) * q * Real.log q) := by
    simp only [sub_mul, sum_sub_distrib, mul_sum]
  have hWY := hW Y hY1
  have hMY := hM Y hY2
  have hs : 0 ≤ Y / Real.log Y := div_nonneg (by linarith) (Real.log_nonneg hY0)
  have heK : e * K ≤ η / 2 := by
    rw [he, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hfin := mul_le_mul_of_nonneg_left hWY hη'.le
  have hfin2 := mul_le_mul_of_nonneg_right heK hs
  rw [hexp] at hpair
  nlinarith

#print axioms rough_count_lower
#print axioms pair_weight_upper
#print axioms kernel_sum_lower
#print axioms model4_asymptotic_from_leaves
end
end LeanLab.Languasco2004.Feed568aModel4
