import LeanLab.HelfgottMajor.Decomp389b

/-!
The two sign energy assembly in the first Plancherel step on book Part IV page 434.
This isolates the remaining full line integral Fourier energy input.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Energy389
open Real MeasureTheory Set LeanLab.HelfgottArcs Decomp269a Decomp389b

/-- The two sign energies partition the full line integral.
CONDITIONAL ON integrability of that actual line energy. Book page 434 after display 16.26.
-/
theorem line_energy_split (δ : ℝ)
    (hi : Integrable (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2)) :
    lineEnergy δ 1 + lineEnergy δ (-1) =
      ∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2 := by
  unfold lineEnergy
  simp only [one_mul, neg_one_mul]
  rw [integral_comp_neg_Ioi 0 (fun t : ℝ =>
    ‖gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2), neg_zero, add_comm]
  exact intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn

/-- Full line Fourier Plancherel supplies the Gaussian two sign energy leaf.
CONDITIONAL ON the full line integrability and its quantitative budget.
Only the split and Cauchy Schwarz assembly on book page 434 are proved here.
-/
theorem line_energy_bound_of_full_integral (δ : ℝ)
    (hi : Integrable (fun t : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2))
    (hbudget : (∫ t : ℝ, ‖gaussianMellin δ ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      2 * π * Sec45.nTwo) :
    sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      2 * sqrt π * sqrt Sec45.nTwo := by
  have hN : 0 ≤ Sec45.nTwo := by unfold Sec45.nTwo; positivity
  have hp : 0 ≤ lineEnergy δ 1 := by unfold lineEnergy; positivity
  have hn : 0 ≤ lineEnergy δ (-1) := by unfold lineEnergy; positivity
  have hcs : sqrt (lineEnergy δ 1) + sqrt (lineEnergy δ (-1)) ≤
      sqrt (lineEnergy δ 1 + lineEnergy δ (-1)) * sqrt 2 := by
    have hh := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset (Fin 2)))
      (f := fun i : Fin 2 => if i = 0 then lineEnergy δ 1 else lineEnergy δ (-1))
      (g := fun _ : Fin 2 => (1 : ℝ))
      (fun i => by split <;> assumption) (fun _ => by norm_num)
    simpa [Fin.sum_univ_two] using hh
  have hb : lineEnergy δ 1 + lineEnergy δ (-1) ≤ 2 * π * Sec45.nTwo := by
    rwa [line_energy_split δ hi]
  calc
    _ ≤ sqrt (2 * π * Sec45.nTwo) * sqrt 2 :=
      hcs.trans (mul_le_mul_of_nonneg_right (sqrt_le_sqrt hb) (sqrt_nonneg 2))
    _ = _ := by
      rw [← sqrt_mul (by positivity),
        show 2 * π * Sec45.nTwo * 2 = 4 * (π * Sec45.nTwo) by ring,
        sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), sqrt_mul pi_pos.le]
      norm_num <;> ring

end LeanLab.HelfgottMajor.Energy389
