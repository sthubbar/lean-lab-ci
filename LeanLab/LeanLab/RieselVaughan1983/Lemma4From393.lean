import LeanLab.RieselVaughan1983.Lemma3Weighted

/-! Lemma 4 on page 53, derived from the stated Lemma 3 approximation.
AI wrote the Lean code. Binary Goldbach is OPEN.
This file does not prove Lemma3ApproxP. -/
namespace LeanLab.RieselVaughan1983.Lemma4From393
open Real
open LeanLab.RieselVaughan1983.Lemma2 LeanLab.RieselVaughan1983.Lemma3
noncomputable section

/-- Equation 2.16. -/
def A6 (lam : ℝ) : ℝ := 2 * A3 - 4 * log 2 - 2 * log lam
/-- Equation 2.17, using the page 53 explicit identity at lambda = 1. -/
def A7 (lam : ℝ) : ℝ := A7one + log lam ^ 2 - (2 * A3 - 4 * log 2) * log lam
/-- Equation 2.18. -/
def A8 (lam : ℝ) : ℝ := 8 * A5 * lam ^ (1 / 6 : ℝ)
/-- Equation 2.19. -/
def A9 (lam : ℝ) : ℝ := 4 * A3 * lam ^ (1 / 2 : ℝ)

lemma sqrt_div_rpow (x lam s : ℝ) (hx : 0 < x) (hlam : 0 < lam) :
    (sqrt (x / lam)) ^ s = lam ^ (-s / 2) * x ^ (s / 2) := by
  rw [rpow_def_of_pos (sqrt_pos.mpr (div_pos hx hlam)),
    log_sqrt (div_nonneg hx.le hlam.le), log_div hx.ne' hlam.ne',
    rpow_def_of_pos hlam, rpow_def_of_pos hx, ← exp_add]
  congr 1
  ring

/-- The change of variable in the proof of Lemma 4 on page 53. -/
lemma main_polynomial (x lam : ℝ) (hx : 0 < x) (hlam : 0 < lam) :
    4 * (log (sqrt (x / lam)) ^ 2 + A6one / 2 * log (sqrt (x / lam)) + A7one / 4) =
      log x ^ 2 + A6 lam * log x + A7 lam := by
  rw [log_sqrt (div_nonneg hx.le hlam.le), log_div hx.ne' hlam.ne']
  unfold A6 A7 A6one
  ring

/-- Lemma 4, page 53. CONDITIONAL ON the full equation 3.14 of Lemma 3. -/
theorem lemma4_of (h3 : Lemma3ApproxP) (x lam : ℝ) (hlam : 0 < lam) (hx : lam ≤ x) :
    |8 * Ctw * S2 (sqrt (x / lam)) - log x ^ 2 - A6 lam * log x - A7 lam| <
      A8 lam * x ^ (-(1 / 6 : ℝ)) + A9 lam * x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := hlam.trans_le hx
  have hz : 1 ≤ sqrt (x / lam) := one_le_sqrt.mpr ((le_div_iff₀ hlam).mpr (by linarith))
  have h := mul_lt_mul_of_pos_left (h3 _ hz) (by norm_num : (0 : ℝ) < 4)
  have hpoly := main_polynomial x lam hx0 hlam
  have heq : 8 * Ctw * S2 (sqrt (x / lam)) - log x ^ 2 - A6 lam * log x - A7 lam =
      4 * (2 * Ctw * S2 (sqrt (x / lam)) - log (sqrt (x / lam)) ^ 2 -
        A6one / 2 * log (sqrt (x / lam)) - A7one / 4) := by
    linarith
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hp1 := sqrt_div_rpow x lam (-(1 / 3 : ℝ)) hx0 hlam
  have hp2 := sqrt_div_rpow x lam (-1) hx0 hlam
  norm_num at hp1 hp2
  have hr : 4 * (A8one / 4 * (sqrt (x / lam)) ^ (-(1 / 3 : ℝ)) +
      A9one / 4 * (sqrt (x / lam)) ^ (-1 : ℝ)) =
      A8 lam * x ^ (-(1 / 6 : ℝ)) + A9 lam * x ^ (-(1 / 2 : ℝ)) := by
    rw [hp1]
    have hp2' : (sqrt (x / lam)) ^ (-1 : ℝ) = lam ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
      simpa using hp2
    rw [hp2']
    unfold A8one A9one A8 A9
    ring
  exact h.trans_eq hr

end
end LeanLab.RieselVaughan1983.Lemma4From393

#print axioms LeanLab.RieselVaughan1983.Lemma4From393.sqrt_div_rpow
#print axioms LeanLab.RieselVaughan1983.Lemma4From393.main_polynomial
#print axioms LeanLab.RieselVaughan1983.Lemma4From393.lemma4_of
