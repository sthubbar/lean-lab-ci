import LeanLab.GoldbachAverage.Decomp82
import LeanLab.GoldbachAverage.GallagherReduction124

/-!
P0051 page 9 eqs. 48 and 49, the Fourier part of Theorem 2.
The existing GallagherReduction124 supplies all H and J bounds.
The classical continuous Gallagher inequality and its spatial split remain OPEN.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Decomp287b
open MeasureTheory Set
open GallagherReduction124 I2Bound124

/-- The absolutely convergent Fourier series in P0051 page 9 before eq. 48. -/
def fourierSeries (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑' n : ℕ, a n * eAdd (α * n)

/-- The moving coefficient sum in P0051 page 9 before eq. 48. -/
def movingSum (a : ℕ → ℂ) (x h : ℝ) : ℂ :=
  ∑' n : ℕ, if x < (n : ℝ) ∧ (n : ℝ) ≤ x + h then a n else 0

/-- The weighted coefficients Lambda zero n times r to n in P0051 page 9. -/
def coefficients (N : ℕ) (n : ℕ) : ℂ :=
  cf n * (Real.exp (-(1 / (N : ℝ))) : ℂ) ^ n

/-- Absolute convergence required by the Gallagher display on P0051 page 9. -/
theorem coefficients_summable (N : ℕ) (hN : 2 ≤ N) :
    Summable (fun n => ‖coefficients N n‖) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : Real.exp (-(1 / (N : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr hN0))
  simpa [coefficients, tm, eAdd] using
    summable_norm_tm (Real.exp_pos _).le hr 0

/-- The Fourier series is exactly Psi minus I on P0051 page 9. -/
theorem fourierSeries_eq (N : ℕ) (hN : 2 ≤ N) (α : ℝ) :
    fourierSeries (coefficients N) α =
      PsiGen (Real.exp (-(1 / (N : ℝ)))) α -
        IGen (Real.exp (-(1 / (N : ℝ)))) α := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact (psi_sub_I (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr hN0))) α).symm

/-- LEAF. P0051 page 9, the Gallagher display before eq. 48.
The classical inequality is applied to an absolutely summable sequence.
The explicit constant follows from the sinc lower bound and Plancherel.
The source cites Montgomery 1971 Lemma 1.9 and Goldston Yang 2017 Section 4. -/
theorem continuous_gallagher (a : ℕ → ℂ)
    (ha : Summable (fun n => ‖a n‖)) (h : ℝ) (hh : 0 < h) :
    Integrable (fun x : ℝ => ‖movingSum a x h‖ ^ 2) ∧
      (∫ α in (0 : ℝ)..(1 / (2 * h)), ‖fourierSeries a α‖ ^ 2) ≤
        (Real.pi ^ 2 / 4) * ((∫ x : ℝ, ‖movingSum a x h‖ ^ 2) / h ^ 2) := by
  sorry

/-- LEAF. P0051 page 9 eqs. 48 and 49, split the spatial integral at zero.
The negative part is I1 after translation by h and the positive part is I2.
The zero coefficient at n equals zero removes the endpoint discrepancy. -/
theorem moving_mass_split (N : ℕ) (hN : 2 ≤ N) (h : ℝ)
    (hh : 1 ≤ h) (hhN : h ≤ N) :
    (∫ x : ℝ, ‖movingSum (coefficients N) x h‖ ^ 2) = I1 N h + I2 N h := by
  sorry

/-- The exact gallagher_19 proposition follows from the two Fourier leaves.
CONDITIONAL ON continuous_gallagher and moving_mass_split. -/
theorem gallagher_19_assembled : GSInputs.GSGallagherVarianceBound := by
  apply gallagher_of_fourier
  refine ⟨Real.pi ^ 2 / 4, by positivity, ?_⟩
  intro N hN h hh hhN
  have hb := (continuous_gallagher (coefficients N) (coefficients_summable N hN)
    h (by linarith)).2
  rw [moving_mass_split N hN h hh hhN] at hb
  simpa only [fourierSeries_eq N hN, GSInputs.W] using hb

example : type_of% Decomp82.gallagher_19 = type_of% gallagher_19_assembled := rfl

end LeanLab.GoldbachAverage.Decomp287b
