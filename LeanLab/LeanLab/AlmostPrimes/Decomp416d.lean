import LeanLab.AlmostPrimes.Decomp416b

/-!
AI wrote the Lean code. Goldbach is open.
Campbell 2026 v1, https://arxiv.org/abs/2608.09488v1,
Theorem 2.1 on printed page 3 and Case 2 on printed pages 13 and 14.
The remainder input of Case2SieveX is supplied by the proved Rankin bound.
The concrete lower-sieve estimate remains an explicit hypothesis.
-/
open Real Finset
noncomputable section
namespace LeanLab.AlmostPrimes.Decomp416d
open Campbell2026 CampbellCase2 CampbellCase2X CampbellCase3 CampbellLemma43 Decomp416b

/-- LEAF. Campbell printed page 14, Case 2, first display.
The remainder estimate is uniform when z is at most the upper endpoint v. -/
theorem case2_remainder_uniform (N : ℕ) (hN : 2 ≤ N) {z v δ : ℝ}
    (hz : 0 < z) (hzv : z ≤ v) (hδ : 0 ≤ δ) :
    2 * R4A N z (z ^ (14.8 : ℝ)) ≤ (19 / 3 : ℝ) * v ^ (14.8 * δ) *
      ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ) := by
  have hb := R4A_rankin N hN z (z ^ (14.8 : ℝ)) δ (by positivity) hδ
  rw [← Real.rpow_mul hz.le] at hb
  have hp : z ^ (14.8 * δ) ≤ v ^ (14.8 * δ) :=
    Real.rpow_le_rpow hz.le hzv (mul_nonneg (by norm_num) hδ)
  have hprod : (∏ p ∈ primesBelow z, (1 + 8 / (p : ℝ) ^ δ)) ≤
      ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ (primesBelow_mono hzv)
    · intro p _; positivity
    · intro p _ _
      have : 0 ≤ 8 / (p : ℝ) ^ δ := by positivity
      linarith
  have hm := mul_le_mul hp hprod (by positivity)
    (Real.rpow_nonneg (le_trans hz.le hzv) _)
  calc 2 * R4A N z (z ^ (14.8 : ℝ)) ≤
        2 * ((19 / 6 : ℝ) * z ^ (14.8 * δ) *
          ∏ p ∈ primesBelow z, (1 + 8 / (p : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (19 / 3 : ℝ) * (z ^ (14.8 * δ) *
        ∏ p ∈ primesBelow z, (1 + 8 / (p : ℝ) ^ δ)) := by ring
    _ ≤ (19 / 3 : ℝ) * (v ^ (14.8 * δ) *
        ∏ p ∈ primesBelow v, (1 + 8 / (p : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

/-- Campbell printed pages 13 and 14, Case 2, from Theorem 2.1 on printed page 3.
CONDITIONAL ON the concrete lower-sieve estimate alone. The remainder estimate is proved. -/
theorem case2SieveX_of_lowerSieve
    (hS : ∀ N : ℕ, N0 < N → N < N1 →
      (Xcount N : ℝ) * V N (zOf N) * F 14.8 (2 + log 1.146) -
        2 * R4A N (zOf N) (zOf N ^ (14.8 : ℝ)) ≤ (siftCount N (zOf N) : ℝ)) :
    Case2SieveX := by
  intro N h0 h1 v δ hzv hδ0 _
  have hN : 2 ≤ N := by
    have : 2 ≤ N0 := by norm_num [N0]
    omega
  have hz : 0 < zOf N := by
    unfold zOf
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  have hr := case2_remainder_uniform N hN hz hzv hδ0.le
  have hs := hS N h0 h1
  linarith

example : 2 * R4A 3 5 (5 ^ (14.8 : ℝ)) ≤ (19 / 3 : ℝ) * 7 ^ (14.8 * (1 / 2 : ℝ)) *
    ∏ p ∈ primesBelow 7, (1 + 8 / (p : ℝ) ^ (1 / 2 : ℝ)) :=
  case2_remainder_uniform 3 (by decide) (by norm_num) (by norm_num) (by norm_num)
example : N0 < N0 + 1 ∧ N0 + 1 < N1 := by norm_num [N0, N1]
end LeanLab.AlmostPrimes.Decomp416d
#print axioms LeanLab.AlmostPrimes.Decomp416d.case2_remainder_uniform
#print axioms LeanLab.AlmostPrimes.Decomp416d.case2SieveX_of_lowerSieve
