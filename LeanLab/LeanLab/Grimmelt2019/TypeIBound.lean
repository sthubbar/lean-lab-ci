/-
AI wrote this Lean code for CODEX task51.
P0074 page 11, the finite Type I estimate in the proof of Lemma 4.1.
The harmonic estimate and beta-sieve distribution remain separate steps.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.SieveExpansion

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
open LeanLab.PNTPort.LargeSieve
attribute [local instance] Classical.propDecidable

/-- Counting at integral frequencies and the minimum geometric bound elsewhere. -/
noncomputable def geomCap (L θ : ℝ) : ℝ :=
  if dist0 θ = 0 then L + 1 else min (L + 1) (1 / (2 * dist0 θ))

/-- The cap handles both integral and nonintegral frequencies. -/
theorem shortInterval_exp_cap_le {t H θ : ℝ} (hH : 0 ≤ H) :
    ‖∑ n ∈ shortInterval t H, LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)‖ ≤ geomCap H θ := by
  unfold geomCap
  split_ifs with hz
  · have hc := (abs_le.mp (shortInterval_card_error (t := t) hH)).2
    calc
      _ ≤ ∑ n ∈ shortInterval t H, ‖LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * θ)‖ :=
        norm_sum_le _ _
      _ = ((shortInterval t H).card : ℝ) := by simp only [norm_e, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      _ ≤ H + 1 := by linarith
  · exact shortInterval_exp_min_le hH (lt_of_le_of_ne (dist0_nonneg _) (Ne.symm hz))

/-- The cap never exceeds the elementary counting bound. -/
theorem geomCap_le_length (L θ : ℝ) : geomCap L θ ≤ L + 1 := by
  unfold geomCap
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The finite Type I sum retains the sharp cap at every divisor frequency. -/
theorem divisorWeight_typeI (D : ℕ) (weights : ℕ → ℝ) (t H α : ℝ)
    (hH : 0 ≤ H) (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      ∑ d ∈ Finset.Icc 1 D, geomCap (H / d) ((d : ℝ) * α) := by
  apply (divisorWeight_fourier_le D weights t H α hw).trans
  apply Finset.sum_le_sum
  intro d hd
  exact shortInterval_exp_cap_le (div_nonneg hH (by positivity))

/-- Dropping cancellation gives the explicit coarse bound with a harmonic divisor sum. -/
theorem divisorWeight_coarse_le (D : ℕ) (weights : ℕ → ℝ) (t H α : ℝ)
    (hH : 0 ≤ H) (hw : ∀ d ∈ Finset.Icc 1 D, |weights d| ≤ 1) :
    ‖∑ n ∈ shortInterval t H, (divisorWeight D weights n : ℂ) *
      LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * α)‖ ≤
      H * (∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ)) + D := by
  apply (divisorWeight_typeI D weights t H α hH hw).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (H / (d : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      exact geomCap_le_length _ _
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [mul_one_div, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp

#print axioms shortInterval_exp_cap_le
#print axioms geomCap_le_length
#print axioms divisorWeight_typeI
#print axioms divisorWeight_coarse_le
end LeanLab.Grimmelt2019.MainTerm
