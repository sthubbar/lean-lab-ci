/-
P0093 page 159 equation 5.3. A weaker mixed character estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Principal442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- P0093 page 159 equation 5.3, weakened to log power seven using
the elementary principal mass bound two N. The printed log power six
uses the stronger prime counting bound N over log N. CONDITIONAL on
the explicit MellinBound280 input. No additional analytic leaf is used. -/
theorem mixed_character_mass442 (hM : MellinBound280) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
              (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 (1 : DirichletCharacter ℂ q) N α‖ *
              ‖characterPrime280 χ N α‖) ≤
            C * (N : ℝ) / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 7 := by
  obtain ⟨B, hB, N0, hb⟩ := hM
  refine ⟨Real.sqrt (2 * B), Real.sqrt_pos.mpr (by positivity), max 128 (max 3 N0), ?_⟩
  intro N hN q hq hqt χ hχ
  have hN128 : 128 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN0 : N0 < N := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 1 ≤ Real.log N := by
    have hN3 : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans hN3).le
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set R := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hR
  have hRp : 0 < R := by dsimp [R]; positivity
  have hR2 : 2 ≤ R := by
    have hτ2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
      have hn : (128 : ℝ) ≤ N := by exact_mod_cast hN128.le
      have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hn (by norm_num : (0 : ℝ) ≤ 1 / 7)
      have he : (128 : ℝ) ^ (1 / 7 : ℝ) = 2 := by
        rw [show (128 : ℝ) = 2 ^ (7 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rwa [he] at hh
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    dsimp [R]
    nlinarith
  set r := 1 / R with hrdef
  have hr : 0 < r := by positivity
  have hrh : r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hR2
  have hpcont := continuous_character_prime357 (1 : DirichletCharacter ℂ q) N (by omega)
  have hncont := continuous_character_prime357 χ N (by omega)
  have hpLp : MemLp (characterPrime280 (1 : DirichletCharacter ℂ q) N) 2
      (volume.restrict (Set.Ioc (-r) r)) :=
    (memLp_two_iff_integrable_sq_norm hpcont.aestronglyMeasurable).mpr
      ((hpcont.norm.pow 2).intervalIntegrable (-r) r).1
  have hnLp : MemLp (characterPrime280 χ N) 2
      (volume.restrict (Set.Ioc (-r) r)) :=
    (memLp_two_iff_integrable_sq_norm hncont.aestronglyMeasurable).mpr
      ((hncont.norm.pow 2).intervalIntegrable (-r) r).1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Set.Ioc (-r) r))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (Filter.Eventually.of_forall (fun α => norm_nonneg (characterPrime280 (1 : DirichletCharacter ℂ q) N α)))
    (Filter.Eventually.of_forall (fun α => norm_nonneg (characterPrime280 χ N α)))
    (by norm_num; exact hpLp.norm) (by norm_num; exact hnLp.norm)
  norm_num only [Real.rpow_two] at hcs
  simp_rw [← Real.sqrt_eq_rpow] at hcs
  rw [← intervalIntegral.integral_of_le (show -r ≤ r by linarith),
    ← intervalIntegral.integral_of_le (show -r ≤ r by linarith),
    ← intervalIntegral.integral_of_le (show -r ≤ r by linarith)] at hcs
  have hp := character_local_mass442 (1 : DirichletCharacter ℂ q) N (by omega) r hr.le hrh
  have hn := hb N hN0 q hq hqt χ hχ
  change (∫ α in -r..r, ‖characterPrime280 χ N α‖ ^ 2) ≤
    B * (N : ℝ) / R * Real.log N ^ 13 at hn
  have h13 : Real.log N ^ 13 ≤ Real.log N ^ 14 := pow_le_pow_right₀ hl (by omega)
  have hprod : Real.sqrt (2 * (N : ℝ)) *
      Real.sqrt (B * (N : ℝ) / R * Real.log N ^ 13) ≤
        Real.sqrt (2 * B) * (N : ℝ) / Real.sqrt R * Real.log N ^ 7 := by
    rw [← Real.sqrt_mul (by positivity)]
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hroot := Real.sq_sqrt hRp.le
      have hBroot := Real.sq_sqrt (show 0 ≤ 2 * B by positivity)
      have he : (Real.sqrt (2 * B) * (N : ℝ) / Real.sqrt R * Real.log N ^ 7) ^ 2 =
          (2 * B) * (N : ℝ) ^ 2 / R * Real.log N ^ 14 := by
        rw [mul_pow, div_pow, mul_pow, hBroot, hroot]
        ring
      rw [he]
      have hh := mul_le_mul_of_nonneg_left h13
        (show 0 ≤ 2 * B * (N : ℝ) ^ 2 / R by positivity)
      calc
        _ = (2 * B * (N : ℝ) ^ 2 / R) * Real.log N ^ 13 := by ring
        _ ≤ _ := hh
  exact hcs.trans ((mul_le_mul (Real.sqrt_le_sqrt hp) (Real.sqrt_le_sqrt hn)
    (Real.sqrt_nonneg _) (by positivity)).trans hprod)

end LeanLab.Linnik1951
