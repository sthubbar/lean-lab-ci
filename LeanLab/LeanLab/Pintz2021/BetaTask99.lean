import LeanLab.Pintz2021.Theorem1U1369
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
The elementary Beta bound for the Gamma factors in P0054 page 6 display 2.10.
This supplies the analytic comparison behind the named Pin2 Hyp_220 input.
No exceptional zero construction or density estimate is asserted.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.BetaTask99

open MeasureTheory

/-- Positive lower real parts give a Beta majorant independent of imaginary parts. -/
theorem beta_majorant {a : ℝ} (ha : 0 < a) {u v : ℂ}
    (hu : a ≤ u.re) (hv : a ≤ v.re) :
    ‖Complex.Gamma u * Complex.Gamma v / Complex.Gamma (u + v)‖ ≤
      (Complex.betaIntegral (a : ℂ) (a : ℂ)).re := by
  have hu0 : 0 < u.re := ha.trans_le hu
  have hv0 : 0 < v.re := ha.trans_le hv
  have hB := Complex.betaIntegral_convergent
    (u := (a : ℂ)) (v := (a : ℂ)) (by simpa using ha) (by simpa using ha)
  have hBre : IntervalIntegrable (fun x : ℝ =>
      ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)).re) volume 0 1 :=
    ⟨hB.1.re, hB.2.re⟩
  have hpt : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ ≤
        ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)).re := by
    intro x hx
    have hx1 : 0 < 1 - x := by linarith [hx.2]
    have hc : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
    rw [norm_mul, hc, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
      Complex.norm_cpow_eq_rpow_re_of_pos hx1]
    simp only [Complex.sub_re, Complex.one_re]
    have hpow : ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [hpow, ← Complex.ofReal_cpow hx.1.le,
      ← Complex.ofReal_cpow hx1.le, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.le (by linarith))
      (Real.rpow_le_rpow_of_exponent_ge hx1 (by linarith [hx.1]) (by linarith))
      (Real.rpow_nonneg hx1.le _) (Real.rpow_nonneg hx.1.le _)
  rw [← Complex.betaIntegral_eq_Gamma_mul_div u v hu0 hv0, Complex.betaIntegral]
  calc
    _ ≤ ∫ x : ℝ in 0..1,
        ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x : ℝ in 0..1,
        ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((a : ℂ) - 1)).re :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        (Complex.betaIntegral_convergent hu0 hv0).norm hBre hpt
    _ = _ := by
      have hcomm := Complex.reCLM.intervalIntegral_comp_comm hB
      simpa only [Complex.reCLM_apply, Complex.betaIntegral] using hcomm

/-- Real parts uniformly near one give the Beta bound one plus any tolerance. -/
theorem beta_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ u v : ℂ,
      1 - δ ≤ u.re → 1 - δ ≤ v.re →
      ‖Complex.Gamma u * Complex.Gamma v / Complex.Gamma (u + v)‖ ≤ 1 + ε := by
  let F : ℝ → ℝ := fun a =>
    (Complex.Gamma (a : ℂ) * Complex.Gamma (a : ℂ) /
      Complex.Gamma ((a : ℂ) + (a : ℂ))).re
  have hΓ2 : ContinuousAt Complex.Gamma ((1 : ℂ) + 1) := by
    apply Complex.continuousAt_Gamma
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hh
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hG1 : ContinuousAt (fun a : ℝ => Complex.Gamma (a : ℂ)) 1 :=
    Complex.continuousAt_Gamma_one.comp_of_eq
      (Complex.continuous_ofReal.continuousAt : ContinuousAt Complex.ofReal (1 : ℝ))
      (by simp)
  have hG2 : ContinuousAt
      (fun a : ℝ => Complex.Gamma ((a : ℂ) + (a : ℂ))) 1 :=
    hΓ2.comp_of_eq
      ((Complex.continuous_ofReal.add Complex.continuous_ofReal).continuousAt :
        ContinuousAt (fun a : ℝ => (a : ℂ) + (a : ℂ)) 1) (by simp)
  have hne : Complex.Gamma ((1 : ℂ) + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hF : ContinuousAt F 1 := by
    have hFG : ContinuousAt (fun a : ℝ =>
        Complex.Gamma (a : ℂ) * Complex.Gamma (a : ℂ) /
          Complex.Gamma ((a : ℂ) + (a : ℂ))) 1 :=
      (hG1.mul hG1).div hG2 hne
    exact Complex.continuous_re.continuousAt.comp hFG
  have hGamma2 : Complex.Gamma ((1 : ℂ) + 1) = 1 := by
    rw [Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one, one_mul]
  have hF1 : F 1 = 1 := by simp [F, Complex.Gamma_one, hGamma2]
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hF ε hε
  let δ := min (r / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have ha : 0 < 1 - δ := by linarith
  have hdist : dist (1 - δ) (1 : ℝ) < r := by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
    exact hδr
  have hFa : F (1 - δ) ≤ 1 + ε := by
    have hh := hclose hdist
    rw [Real.dist_eq, hF1] at hh
    linarith [(abs_lt.mp hh).2]
  refine ⟨δ, hδ, hδ1, fun u v hu hv => ?_⟩
  have hb := beta_majorant ha hu hv
  have hformula := Complex.betaIntegral_eq_Gamma_mul_div
    ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) (by simpa using ha) (by simpa using ha)
  rw [hformula] at hb
  exact hb.trans hFa

/-- A uniform real-part deficit bound discharges the existing Hyp_220 predicate. -/
theorem hyp220_of_deficits {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (K : ℕ) (D : TheoremAU1357.ZeroData K),
      (∀ i, Theorem1U1369.δz D i ≤ δ) → Theorem1U1369.Hyp_220 D (1 + ε) := by
  obtain ⟨δ, hδ, _hδ1, hb⟩ := beta_near_one hε
  refine ⟨δ, hδ, fun K D hD i j => ?_⟩
  apply hb (D.ρ i) (D.ρ j)
  · have hi := hD i
    unfold Theorem1U1369.δz at hi
    linarith
  · have hj := hD j
    unfold Theorem1U1369.δz at hj
    linarith

/-- The paper's H over log X region gives Hyp_220 at every sufficiently large scale. -/
theorem hyp220_of_log_deficits (H : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X0 : ℝ, 3 ≤ X0 ∧ ∀ X : ℝ, X0 < X →
      ∀ (K : ℕ) (D : TheoremAU1357.ZeroData K),
        (∀ i, Theorem1U1369.δz D i ≤ H / Real.log X) →
          Theorem1U1369.Hyp_220 D (1 + ε) := by
  obtain ⟨δ, hδ, hb⟩ := hyp220_of_deficits hε
  refine ⟨max 3 (Real.exp (H / δ)), le_max_left _ _, fun X hX K D hD => ?_⟩
  have hX3 : (3 : ℝ) < X := (le_max_left _ _).trans_lt hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hH : H / δ ≤ Real.log X :=
    (Real.le_log_iff_exp_le (by linarith : 0 < X)).mpr
      ((le_max_right _ _).trans_lt hX).le
  have hratio : H / Real.log X ≤ δ := by
    apply (div_le_iff₀ hlog).mpr
    have hh := (div_le_iff₀ hδ).mp hH
    nlinarith
  exact hb K D (fun i => (hD i).trans hratio)

end LeanLab.Pintz2021.BetaTask99

#print axioms LeanLab.Pintz2021.BetaTask99.beta_majorant

#print axioms LeanLab.Pintz2021.BetaTask99.beta_near_one

#print axioms LeanLab.Pintz2021.BetaTask99.hyp220_of_deficits

#print axioms LeanLab.Pintz2021.BetaTask99.hyp220_of_log_deficits
