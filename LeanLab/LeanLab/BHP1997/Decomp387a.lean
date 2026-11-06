/-
BHP1997, page 52, displays 5.18, 5.22 and 5.23.
Keep the exact finite center required by page 3 condition iv.
The analytic estimates remain explicit hypotheses.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.NormalizationC165
import LeanLab.BHP1997.WindowIntegrability308

namespace LeanLab.BHP1997.Task387
open Classical Complex MeasureTheory

/-- Page 3 condition iv. The actual finite moving window. -/
noncomputable def window (S : Finset ℕ) (y z : ℝ) : Finset ℕ :=
  S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y+y*z)

/-- Page 52. The uncentered finite coefficient sum in the actual window. -/
noncomputable def windowSum (S : Finset ℕ) (c : ℕ → ℂ) (z y : ℝ) : ℂ :=
  ∑ m ∈ window S y z, c m

/-- Page 3 condition iv. Summing a constant per term multiplies it by the
window cardinality. This is not a continuous length approximation. -/
noncomputable def windowCenter (S : Finset ℕ) (u : ℂ) (z y : ℝ) : ℂ :=
  ((window S y z).card : ℂ)*u

/-- Page 3 condition iv and page 52. The exact center of a finite window
is its cardinality times the center of each summand. -/
theorem centered_window_identity (S : Finset ℕ) (c : ℕ → ℂ)
    (d u : ℂ) (y z : ℝ) :
    windowSum S (fun m => c m-d*u) z y =
      windowSum S c z y-d*windowCenter S u z y := by
  simp only [windowSum, windowCenter, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- Page 3 condition iv and page 52. The exact centered error has a genuine
square integral, including the jumps of the moving window count. -/
theorem discrete_center_sq_integrable (S : Finset ℕ) (c : ℕ → ℂ)
    (d u : ℂ) (z a b : ℝ) :
    IntervalIntegrable (fun y =>
      ‖windowSum S c z y-d*windowCenter S u z y‖^2) volume a b := by
  simp_rw [← centered_window_identity]
  exact Task308.window_sum_sq_intervalIntegrable S (fun m => c m-d*u) z a b

/-- Page 52, displays 5.18, 5.22 and 5.23. Three actual error estimates
imply the exact centered finite window estimate.
CONDITIONAL on the estimates and their explicit regularity hypotheses. -/
theorem discrete_center_three_errors {ι : Type*} (E : Finset ι)
    (S : Finset ℕ) (c : ι → ℕ → ℂ) (d : ι → ℂ)
    (u : ℂ) (W H : ℝ → ℂ) (z : ℝ) {a b R1 R2 R3 : ℝ}
    (hab : a ≤ b)
    (h1 : ∀ χ ∈ E, IntervalIntegrable
      (fun y => ‖windowSum S (c χ) z y-d χ*W y‖^2) volume a b)
    (h2 : ∀ χ ∈ E, IntervalIntegrable
      (fun y => ‖d χ*(W y-H y)‖^2) volume a b)
    (h3 : ∀ χ ∈ E, IntervalIntegrable
      (fun y => ‖d χ*(H y-windowCenter S u z y)‖^2) volume a b)
    (hR1 : (∑ χ ∈ E, ∫ y in a..b,
      ‖windowSum S (c χ) z y-d χ*W y‖^2) ≤ R1)
    (hR2 : (∑ χ ∈ E, ∫ y in a..b, ‖d χ*(W y-H y)‖^2) ≤ R2)
    (hR3 : (∑ χ ∈ E, ∫ y in a..b,
      ‖d χ*(H y-windowCenter S u z y)‖^2) ≤ R3) :
    (∑ χ ∈ E, ∫ y in a..b,
      ‖windowSum S (fun m => c χ m-d χ*u) z y‖^2) ≤ 3*(R1+R2+R3) := by
  simp_rw [centered_window_identity]
  exact NormalizationC165.integrated_three_errors E
    (fun χ => windowSum S (c χ) z) d W H (windowCenter S u z) hab
    (fun χ _ => discrete_center_sq_integrable S (c χ) (d χ) u z a b)
    h1 h2 h3 hR1 hR2 hR3

end LeanLab.BHP1997.Task387
