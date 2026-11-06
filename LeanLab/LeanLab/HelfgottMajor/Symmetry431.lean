import LeanLab.HelfgottMajor.MellinDerivative431
import LeanLab.HelfgottMajor.Decomp389b

/-!
Conjugation for the two signed Gaussian Mellin profiles on book page 434.
This supplies the analytic profile transformation for the negative sampling branch.
It asserts no conjugation theorem for zero multiplicities or quantitative zero counts.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Symmetry431
open Real MeasureTheory LeanLab.HelfgottArcs Decomp269a Decomp389b
open scoped ComplexConjugate

/-- The Mellin transform of a real weight with the opposite modulation is conjugate reflected.
Source book page 434, the separate negative sign argument after display 16.26.
-/
theorem mellin_phase_conj (w : ℝ → ℝ) (δ : ℝ) (s : ℂ) :
    mellin (fun t : ℝ => (w t : ℂ) * e (-δ * t)) (conj s) =
      conj (mellin (fun t : ℝ => (w t : ℂ) * e (δ * t)) s) := by
  unfold mellin
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hp : (t : ℂ) ^ (conj s - 1) = conj ((t : ℂ) ^ (s - 1)) := by
    have hx : (t : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg ht.le]
      exact pi_ne_zero.symm
    simpa only [map_sub, map_one, Complex.conj_ofReal] using
      Complex.cpow_conj (t : ℂ) (s - 1) hx
  have he (v : ℝ) : e (-v) = conj (e v) := by
    unfold e
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  rw [show -δ * t = -(δ * t) by ring, he, hp]
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]

/-- The Gaussian Mellin transform obeys the conjugate reflection used for the two signs.
Source book page 434 after display 16.26.
-/
theorem gaussian_mellin_conj (δ : ℝ) (s : ℂ) :
    gaussianMellin (-δ) (conj s) = conj (gaussianMellin δ s) :=
  mellin_phase_conj (fun t : ℝ => exp (-t ^ 2 / 2)) δ s

/-- Opposite modulation exchanges the positive and negative full half line energies.
Source book page 434, the two sign Plancherel argument.
-/
theorem line_energy_neg_shift (δ ε : ℝ) : lineEnergy (-δ) ε = lineEnergy δ (-ε) := by
  unfold lineEnergy
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hc : (1 / 2 : ℂ) + (ε * t : ℝ) * Complex.I =
      conj ((1 / 2 : ℂ) + ((-ε) * t : ℝ) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [hc, gaussian_mellin_conj, Complex.norm_conj]

end LeanLab.HelfgottMajor.Symmetry431
