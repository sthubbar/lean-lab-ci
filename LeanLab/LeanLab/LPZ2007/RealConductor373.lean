import LeanLab.LPZ2007.RealZeroProof

/-!
The real character case of display 10 on P0045 preprint pages 5 and 6.
The real zero estimate is combined with the proved classical region.
The primitive principal case uses the bounded height zeta region.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.RealConductor373

open Real Filter Asymptotics LeanLab.PNTPort.DirichletZF

/-- P0045 page 5, the real zero estimate before Lemma 4.1.
Solving the reciprocal square root bound gives the quadratic modulus bound. -/
theorem modulus_bound {r : ℕ} {c H u δ : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hH : 0 < H) (hu : 0 < u)
    (hlower : c * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ)
    (hupper : δ ≤ H / u) : (c / H) ^ 2 * u ^ 2 ≤ r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Real.rpow_neg hrR.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv] at hlower
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrR
  have hh := (div_le_div_iff₀ hs hu).1 (hlower.trans hupper)
  have hb : c / H * u ≤ Real.sqrt (r : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hH]
    nlinarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ c / H * u) hb
  nlinarith [Real.sq_sqrt hrR.le]

/-- P0045 page 6, classical region for nonreal zeros of real characters.
For fixed height, log B is sublinear in log X when r is at most log X squared. -/
theorem logarithmic_majorant (T : ℝ) :
    (fun u : ℝ => log (2 * (T + 3) * Z) + 2 * log u) =o[atTop]
      (fun u : ℝ => u) := by
  exact (isLittleO_const_id_atTop _).add (Real.isLittleO_log_id_atTop.const_mul_left 2)

/-- P0045 page 6, the small conductor comparison used with the classical region. -/
theorem log_Bt_le {r : ℕ} {u t T : ℝ}
    (hr : 0 < r) (hu : 0 < u) (hT : 1 ≤ T) (ht : |t| ≤ T)
    (hrsmall : (r : ℝ) ≤ u ^ 2) :
    log (Bt r t) ≤ log (2 * (T + 3) * Z) + 2 * log u := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hZ := Z_pos
  have hle : Bt r t ≤ (2 * (T + 3) * Z) * u ^ 2 := by
    unfold Bt
    nlinarith [mul_le_mul hrsmall (by linarith : |t| + 3 ≤ T + 3)
      (by positivity : 0 ≤ |t| + 3) (by positivity : 0 ≤ u ^ 2)]
  have hb : 0 < Bt r t := by unfold Bt; positivity
  have h := log_le_log hb hle
  rw [log_mul (by positivity : 2 * (T + 3) * Z ≠ 0) (by positivity : u ^ 2 ≠ 0), log_pow] at h
  exact h


end LeanLab.LPZ2007.RealConductor373

#print axioms LeanLab.LPZ2007.RealConductor373.modulus_bound
#print axioms LeanLab.LPZ2007.RealConductor373.logarithmic_majorant
#print axioms LeanLab.LPZ2007.RealConductor373.log_Bt_le
