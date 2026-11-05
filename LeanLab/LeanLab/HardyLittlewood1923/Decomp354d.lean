import LeanLab.HardyLittlewood1923.Decomp276c

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 23 equation 3.122.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354d

open Real
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

/-- P0004 page 23 before equation 3.122.
The modulus of Y is at least its positive real part. -/
theorem localY_norm_lower {n : ℕ} (hn : 0 < n) (θ : ℝ) :
    1 / (n : ℝ) ≤ ‖localY n θ‖ := by
  simpa only [localY_re, abs_of_pos (by positivity : 0 < 1 / (n : ℝ))] using
    (Complex.abs_re_le_norm (localY n θ))

/-- P0004 page 23 equation 3.122, the square root modulus factor. -/
theorem sqrt_modulus_le {n q : ℕ} (hq : q ≤ Nat.sqrt n) :
    Real.sqrt q ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hq2 : (q : ℝ) ^ 2 ≤ n := by
    exact_mod_cast (show q ^ 2 ≤ n by simpa [pow_two] using Nat.le_sqrt.mp hq)
  have hsq : (q : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).mpr hq2
  calc
    _ ≤ Real.sqrt (Real.sqrt n) := Real.sqrt_le_sqrt hsq
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
      norm_num

/-- LEAF. P0004 page 23 before equation 3.122.
If the angular displacement is at most eta then Y stays in the central wedge.
Only this geometric lower bound on the angular gap is asserted here. -/
theorem small_gap {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ : |θ| ≤ 1 / (n : ℝ)) :
    π / 4 ≤ angularGap n θ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < 1 / (n : ℝ) := by positivity
  have hy : ‖localY n θ‖ ^ 2 = (1 / (n : ℝ)) ^ 2 + θ ^ 2 := by
    rw [Complex.sq_norm]
    simp [localY, Complex.normSq_apply, pow_two, mul_inv_rev]
  have hyn : 0 < ‖localY n θ‖ := by
    have := norm_nonneg (localY n θ)
    nlinarith
  have ht2 : θ ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := by
    calc _ = |θ| ^ 2 := (sq_abs θ).symm
         _ ≤ _ := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  have hs : (2 * |θ|) ^ 2 ≤ (Real.sqrt 2 * ‖localY n θ‖) ^ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs θ]
  have hcomp : 2 * |θ| ≤ Real.sqrt 2 * ‖localY n θ‖ :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  have hr : |(-θ) / ‖localY n θ‖| ≤ Real.sqrt 2 / 2 := by
    rw [abs_div, abs_neg, abs_of_pos hyn, div_le_iff₀ hyn]
    nlinarith
  have hv : Real.arcsin (Real.sqrt 2 / 2) = π / 4 := by
    rw [← Real.sin_pi_div_four]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hu := Real.arcsin_le_arcsin (abs_le.mp hr).2
  have hl := Real.arcsin_le_arcsin (abs_le.mp hr).1
  rw [Real.arcsin_neg, hv] at hl
  rw [hv] at hu
  have hb : |Complex.arg (localY n θ)| ≤ π / 4 := by
    rw [Complex.arg_of_re_nonneg (by simp [localY]),
      show (localY n θ).im = -θ by simp [localY]]
    exact abs_le.mpr ⟨hl, hu⟩
  unfold angularGap
  linarith

/-- P0004 page 23 equation 3.122.
The small angle factor has no logarithmic loss. This elementary estimate
holds for every nonnegative Theta. -/
theorem angular_small_without_log {Θ : ℝ} (hΘ0 : 0 ≤ Θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 4 ≤ n → ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n →
      ∀ θ : ℝ, |θ| ≤ 1 / (n : ℝ) →
        angularTerm Θ n q θ ≤ D * (n : ℝ) ^ (Θ + 1 / 4) := by
  let D : ℝ := (π / 4) ^ (-Θ - 1 / 2) * Real.log (1 / (π / 4) + 2)
  have hD : 0 ≤ D := by
    dsimp [D]
    apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
    apply Real.log_nonneg
    have : 0 < π / 4 := by positivity
    have : 0 < 1 / (π / 4) := by positivity
    linarith
  refine ⟨D, hD, fun n hn q hq hqN θ hθ => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hg := small_gap hn0 hθ
  have hg0 : 0 < angularGap n θ := angularGap_pos hn0 θ
  have hy := localY_norm_lower hn0 θ
  have hp : ‖localY n θ‖ ^ (-Θ) ≤ (n : ℝ) ^ Θ := by
    calc
      _ ≤ (1 / (n : ℝ)) ^ (-Θ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hy (by linarith)
      _ = _ := by rw [one_div, ← Real.rpow_neg_eq_inv_rpow]; simp
  have hgap : (angularGap n θ) ^ (-Θ - 1 / 2) ≤ (π / 4) ^ (-Θ - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hg (by linarith)
  have hi : 1 / angularGap n θ ≤ 1 / (π / 4) := one_div_le_one_div_of_le (by positivity) hg
  have hlog : Real.log (1 / angularGap n θ + 2) ≤ Real.log (1 / (π / 4) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (1 / angularGap n θ + 2) :=
    Real.log_nonneg (by
        have : 0 < 1 / angularGap n θ := by positivity
        linarith)
  have hr : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ Θ = (n : ℝ) ^ (Θ + 1 / 4) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hb : angularTerm Θ n q θ ≤ D * (n : ℝ) ^ (Θ + 1 / 4) := by
    unfold angularTerm
    calc
      _ ≤ ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ Θ) *
          (π / 4) ^ (-Θ - 1 / 2) * Real.log (1 / (π / 4) + 2) := by
        apply mul_le_mul _ hlog hlog0 (by positivity)
        apply mul_le_mul _ hgap (by positivity) (by positivity)
        exact mul_le_mul (sqrt_modulus_le hqN) hp (by positivity) (by positivity)
      _ = _ := by rw [hr]; dsimp [D]; ring
  exact hb

/-- P0004 page 23 equation 3.122 and the sentence after equation 3.123.
The exact small angular target follows from the stronger bound without log. -/
theorem angular_small {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 4 ≤ n → ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n →
      ∀ θ : ℝ, |θ| ≤ 1 / (n : ℝ) →
        angularTerm Θ n q θ ≤ D * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
  obtain ⟨D, hD, hd⟩ := angular_small_without_log (by linarith : 0 ≤ Θ)
  refine ⟨D, hD, fun n hn q hq hqN θ hθ => ?_⟩
  exact (hd n hn q hq hqN θ hθ).trans
    (le_mul_of_one_le_right (mul_nonneg hD (by positivity))
      (U1463.one_le_log_of_three (by omega)))

#print axioms localY_norm_lower
#print axioms sqrt_modulus_le
#print axioms small_gap
#print axioms angular_small_without_log
#print axioms angular_small

end LeanLab.HardyLittlewood1923.Decomp354d
