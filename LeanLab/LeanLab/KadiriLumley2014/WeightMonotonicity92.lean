/-
P0059 arXiv 1407.7902v1 pages 11 to 13, Section 3.3.
Elementary monotonicity underlying the substitution m0 = 5.
AI wrote this Lean code, CODEX task92, 2026-10-26.
-/
import LeanLab.KadiriLumley2014.WeightFirstFactor
import LeanLab.KadiriLumley2014.TableRounding

namespace LeanLab.KadiriLumley2014.Task92
open Real Set MeasureTheory
open Task64

/-- The base of the paper weight lies between zero and one on its domain. -/
theorem weight_base_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ 4 * t * (1 - t) ∧ 4 * t * (1 - t) ≤ 1 := by
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) ht.1) (sub_nonneg.mpr ht.2)
  · nlinarith [sq_nonneg (2 * t - 1)]

/-- Increasing m decreases the pointwise weight on the unit interval. -/
theorem weight_antitone_m {m n : ℕ} (hmn : m ≤ n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    weight n t ≤ weight m t := by
  obtain ⟨hb0, hb1⟩ := weight_base_bounds ht
  exact pow_le_pow_of_le_one hb0 hb1 hmn

/-- Increasing m decreases the positive weight mass. -/
theorem weight_mass_antitone {m n : ℕ} (hmn : m ≤ n) :
    (∫ t in (0 : ℝ)..1, weight n t) ≤ ∫ t in (0 : ℝ)..1, weight m t := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((weight_continuous n).intervalIntegrable _ _) ((weight_continuous m).intervalIntegrable _ _)
  exact fun t ht => weight_antitone_m hmn ht

/-- Section 3.3 uses the smallest factorial ratio at the smallest m. -/
theorem lambdaZero_monotone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    lambdaZero m ≤ lambdaZero n := by
  rw [← two_div_mass_eq_lambdaZero hm,
    ← two_div_mass_eq_lambdaZero (lt_of_lt_of_le hm hmn)]
  exact div_le_div_of_nonneg_left (by norm_num) (weight_mass_pos n) (weight_mass_antitone hmn)

/-- The exact lower factorial ratio at m0 = 5 in Section 3.3. -/
theorem lambdaZero_ge_five {m : ℕ} (hm : 5 ≤ m) :
    (693 / 128 : ℝ) ≤ lambdaZero m := by
  have h := lambdaZero_monotone (by norm_num : 0 < (5 : ℕ)) hm
  have h5 : lambdaZero 5 = (693 / 128 : ℝ) := by norm_num [lambdaZero, Nat.factorial]
  rwa [h5] at h

/-- Table 2 rows with index at least 46 satisfy all three simplifying assumptions
of equation 3.6. The earlier rows do not satisfy that displayed sufficient domain. -/
theorem table_simplification_domain : ∀ r ∈ tableTwo,
    (5 ≤ r.m ∧ r.deltaQ < (2 / 10 ^ 8 : ℚ) ∧ 10 ^ 9 < r.height) ↔ 46 ≤ r.logIndex := by
  decide +kernel

end LeanLab.KadiriLumley2014.Task92
