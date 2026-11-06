import LeanLab.RamareSaouter2003.Decomp419a

/-!
Backlund p. 350, displays 21 and 25, and p. 374.
The Gamma remainder separates into the actual periodic Bernoulli integral
and elementary logarithm and arctangent terms.
Only the Euler summation identity for the continuous Gamma argument is OPEN.
The integral bound and elementary losses are proved independently.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp419c
open Real Complex MeasureTheory Set Filter Decomp359g Circle419
open scoped Topology

/-- Backlund p. 350, display 21, the imaginary part of J at one quarter plus iT/2.
The source periodic polynomial is fract u squared minus fract u.
Taking the imaginary part of its reciprocal-square kernel gives this real integral. -/
noncomputable def stirlingImag (T : ℝ) : ℝ :=
  -(T / 2) * ∫ u in Set.Ioi (0 : ℝ),
    (Int.fract u - (Int.fract u) ^ 2) * (u + 1 / 4) /
      ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2

/-- LEAF. Backlund p. 350, display 25 from displays 20 and 21.
The continuously normalized Gamma argument is linked to its actual
periodic Bernoulli integral. This leaf is an identity, not a remainder bound. -/
theorem gamma_stieltjes_expansion (T : ℝ) (hT : 1400 ≤ T) :
    gammaRemainder T = stirlingImag T +
      T / 4 * Real.log (1 + 1 / (4 * T ^ 2)) +
        (1 / 4) * Real.arctan (1 / (2 * T)) := by
  sorry

/-- LEAF. Backlund p. 350, display 21, the real positive reciprocal-square kernel.
Its primitive is minus one over twice the quadratic denominator. -/
theorem kernel_integral (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun u : ℝ => (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2)
      (Set.Ioi 0) volume ∧
    (∫ u in Set.Ioi (0 : ℝ), (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2) =
      1 / (2 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) := by
  let F : ℝ → ℝ := fun u => -1 / (2 * ((u + 1 / 4) ^ 2 + (T / 2) ^ 2))
  let K : ℝ → ℝ := fun u => (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2
  have hd (u : ℝ) : 0 < (u + 1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  have hderiv (u : ℝ) (_ : u ∈ Set.Ici (0 : ℝ)) : HasDerivAt F (K u) u := by
    have hq : HasDerivAt (fun v : ℝ => 2 * ((v + 1 / 4) ^ 2 + (T / 2) ^ 2))
        (4 * (u + 1 / 4)) u := by
      convert ((((hasDerivAt_id u).add_const (1 / 4)).pow 2).add_const ((T / 2) ^ 2)).const_mul 2 using 1
      · ext v; dsimp <;> ring
      · dsimp <;> ring
    have hh := (hq.inv (by positivity : 2 * ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ≠ 0)).neg
    convert hh using 1
    · ext v; dsimp [F]; ring
    · dsimp [K]; field_simp; ring
  have hn (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) : 0 ≤ K u := by
    have hu0 : 0 < u := hu
    dsimp [K]
    positivity
  have htop : Tendsto (fun u : ℝ => 2 * ((u + 1 / 4) ^ 2 + (T / 2) ^ 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact tendsto_atTop_add_const_right _ ((T / 2) ^ 2)
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_atTop_add_const_right _ (1 / 4 : ℝ) tendsto_id))
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F, Pi.neg_apply, Pi.inv_apply, neg_div, one_div, neg_zero] using htop.inv_tendsto_atTop.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hn hlim, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hn hlim
  change (∫ u in Set.Ioi (0 : ℝ), K u) = _
  rw [h]
  dsimp [F]
  ring

/-- LEAF. Backlund p. 374, the imaginary Stieltjes remainder estimate.
The periodic Bernoulli factor is between zero and one quarter.
An explicit positive kernel majorant supplies the displayed one over 3T bound. -/
theorem stirlingImag_bound (T : ℝ) (hT : 0 < T) : |stirlingImag T| ≤ 1 / (3 * T) := by
  let K : ℝ → ℝ := fun u => (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2
  let H : ℝ → ℝ := fun u => Int.fract u - (Int.fract u) ^ 2
  have hH (u : ℝ) : 0 ≤ H u ∧ H u ≤ (1 / 4 : ℝ) := by
    have h0 := Int.fract_nonneg u
    have h1 := Int.fract_lt_one u
    dsimp [H]
    constructor <;> nlinarith [sq_nonneg (Int.fract u - 1 / 2)]
  obtain ⟨hKi, hKeq⟩ := kernel_integral T hT
  have hKn (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) : 0 ≤ K u := by
    have hu0 : 0 < u := hu
    dsimp [K]
    positivity
  have hHi : IntegrableOn (fun u => H u * K u) (Set.Ioi 0) volume := by
    apply Integrable.bdd_mul (c := 1 / 4) hKi
    · exact (measurable_fract.sub (measurable_fract.pow_const 2)).aestronglyMeasurable
    · exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hH u).1]; exact (hH u).2)
  have hIn : 0 ≤ ∫ u in Set.Ioi (0 : ℝ), H u * K u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (hH u).1 (hKn u hu)
  have hIle : (∫ u in Set.Ioi (0 : ℝ), H u * K u) ≤
      (1 / 4) * (1 / (2 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2))) := by
    rw [← hKeq, ← integral_const_mul]
    apply integral_mono_ae hHi (hKi.const_mul (1 / 4))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_right (hH u).2 (hKn u hu)
  have hform : stirlingImag T = -(T / 2) * ∫ u in Set.Ioi (0 : ℝ), H u * K u := by
    unfold stirlingImag
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [H, K]
    ring
  rw [hform, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < T / 2), abs_of_nonneg hIn]
  apply (mul_le_mul_of_nonneg_left hIle (by positivity : 0 ≤ T / 2)).trans
  have hd : 0 < 2 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) := by positivity
  calc
    _ = T / (16 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) := by field_simp; ring
    _ ≤ 1 / (3 * T) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 16 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) (by positivity : 0 < 3 * T)]
      nlinarith [sq_nonneg T]

/-- LEAF. Backlund p. 374, the explicit logarithmic loss in display 25. -/
theorem logarithmic_loss (T : ℝ) (hT : 0 < T) :
    |T / 4 * Real.log (1 + 1 / (4 * T ^ 2))| ≤ 1 / (16 * T) := by
  have hl : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) := Real.log_nonneg (by
    have hx : (0 : ℝ) ≤ 1 / (4 * T ^ 2) := by positivity
    linarith)
  have hu := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (4 * T ^ 2))
  rw [abs_of_nonneg (mul_nonneg (by positivity) hl)]
  calc
    _ ≤ T / 4 * (1 / (4 * T ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by field_simp; ring

/-- LEAF. Backlund p. 374, the explicit arctangent loss in display 25. -/
theorem arctangent_loss (T : ℝ) (hT : 0 < T) :
    |(1 / 4 : ℝ) * Real.arctan (1 / (2 * T))| ≤ 1 / (8 * T) := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  calc
    _ ≤ (1 / 4 : ℝ) * |1 / (2 * T)| := mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs (by norm_num)
    _ = _ := by rw [abs_of_pos (by positivity : 0 < 1 / (2 * T))]; ring

/-- Backlund p. 374, exactly the original gamma_remainder_bound target.
CONDITIONAL ON the Euler summation identity gamma_stieltjes_expansion only. -/
theorem gamma_remainder_bound (T : ℝ) (hT : 1400 ≤ T) :
    |gammaRemainder T| ≤ 25 / (48 * T) := by
  have ht : 0 < T := by linarith
  rw [gamma_stieltjes_expansion T hT]
  calc
    _ ≤ |stirlingImag T| + |T / 4 * Real.log (1 + 1 / (4 * T ^ 2))| +
        |(1 / 4 : ℝ) * Real.arctan (1 / (2 * T))| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 / (3 * T) + 1 / (16 * T) + 1 / (8 * T) := by
      gcongr
      · exact stirlingImag_bound T ht
      · exact logarithmic_loss T ht
      · exact arctangent_loss T ht
    _ = _ := by ring

/-- Rosser p. 224, exactly the original circle_gamma_bound statement.
CONDITIONAL ON the two zeta envelope leaves in Decomp419a and the single
Euler summation identity in this file. The gamma integral bound is proved. -/
theorem circle_gamma_bound (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * Complex.I))‖) /
        (2 * π * Real.log (4 * 1.32 / 3) * N) +
      1 / 2 + 4 / (π * T) + |gammaRemainder T| / π ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ /
            (2 * Real.log (4 * 1.32 / 3)) := by
  have ht : 1400 ≤ T := hA.trans hT
  have hq : 0 < Real.log (4 * 1.32 / 3) := Real.log_pos (by norm_num)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < 2 * π * Real.log (4 * 1.32 / 3) := by positivity
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le
    (powered_log_integrable T ht N) ((logEnvelope_integrable T).const_mul (N : ℝ))
    (fun φ hφ => by
      obtain ⟨hp, hm⟩ := Decomp419a.zeta_circle_bound T φ ht hφ
      exact log_average_pow_le _ _ N _ (logEnvelope_nonneg T φ ht) hp hm)
  rw [intervalIntegral.integral_const_mul] at hi
  have hdiv := div_le_div_of_nonneg_right hi (mul_pos hden hNR).le
  have hcancel : ((N : ℝ) * ∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
      (2 * π * Real.log (4 * 1.32 / 3) * N) =
      (∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
        (2 * π * Real.log (4 * 1.32 / 3)) := by field_simp
  rw [hcancel] at hdiv
  have hc := center_euler_lower (5 / 4) T (by norm_num)
  norm_num only [show (2 : ℝ) * (5 / 4) = 5 / 2 by norm_num,
    Complex.ofReal_div, Complex.ofReal_ofNat] at hc
  have hcz : 0 < ‖riemannZeta (5 / 2) / riemannZeta (5 / 4)‖ := by
    apply norm_pos_iff.mpr
    exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hcz hc) (by positivity : 0 ≤ 2 * Real.log (4 * 1.32 / 3))
  have hg := div_le_div_of_nonneg_right (gamma_remainder_bound T ht) Real.pi_pos.le
  have hid : 4 / (π * T) + (25 / (48 * T)) / π = 217 / (48 * π * T) := by ring
  have hb := Decomp419a.envelope_budget T ht
  rw [← hid] at hb
  linarith


end LeanLab.RamareSaouter2003.Decomp419c

#print axioms LeanLab.RamareSaouter2003.Decomp419c.gamma_stieltjes_expansion
#print axioms LeanLab.RamareSaouter2003.Decomp419c.kernel_integral
#print axioms LeanLab.RamareSaouter2003.Decomp419c.stirlingImag_bound
#print axioms LeanLab.RamareSaouter2003.Decomp419c.logarithmic_loss
#print axioms LeanLab.RamareSaouter2003.Decomp419c.arctangent_loss
#print axioms LeanLab.RamareSaouter2003.Decomp419c.gamma_remainder_bound

#print axioms LeanLab.RamareSaouter2003.Decomp419c.circle_gamma_bound
