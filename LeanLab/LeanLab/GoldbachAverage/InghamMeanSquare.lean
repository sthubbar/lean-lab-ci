import LeanLab.GoldbachAverage.InghamTheta

/-!
The elementary H step of the theta route recorded for P0051 page 20.
H x is the integral of the square of psi t minus t from zero to x.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.InghamTheta
open MeasureTheory Set Filter

/-- The mean square of the psi error, with lower limit zero. -/
def H (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, (Chebyshev.psi t - t) ^ 2

/-- Ingham's pointwise estimate gives a uniform bound up to x. -/
theorem ingham_uniform (theta : ℝ) (htheta : 1 / 2 ≤ theta) (htheta1 : theta < 1)
    (hzeros : ∀ ρ : LeanLab.PNTPort.ExplicitPsi1.Zall, ρ.1.re ≤ theta) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 6 ≤ x → ∀ t : ℝ, 0 ≤ t → t ≤ x →
      |Chebyshev.psi t - t| ≤ B * x ^ theta * Real.log x ^ 2 := by
  obtain ⟨C, hC⟩ := ingham_of_zero_bound theta htheta htheta1 hzeros
  set A := Chebyshev.psi 6 + 6 with hA
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨|C| + A, by positivity, fun x hx t ht htx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hxp : 1 ≤ x ^ theta := Real.one_le_rpow (by linarith) (by linarith)
  have hshape : 1 ≤ x ^ theta * Real.log x ^ 2 := by nlinarith [sq_nonneg (Real.log x - 1)]
  by_cases ht6 : 6 ≤ t
  · have ht0 : 0 < t := by linarith
    have hCt : C * t ^ theta * Real.log t ^ 2 ≤ |C| * x ^ theta * Real.log x ^ 2 := by
      have hLt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have hLtx : Real.log t ≤ Real.log x := Real.log_le_log ht0 htx
      have hpt : t ^ theta ≤ x ^ theta := Real.rpow_le_rpow ht htx (by linarith)
      calc C * t ^ theta * Real.log t ^ 2 ≤ |C| * t ^ theta * Real.log t ^ 2 := by gcongr; exact le_abs_self C
        _ ≤ |C| * x ^ theta * Real.log x ^ 2 := by gcongr
    refine (hC t ht6).trans (hCt.trans ?_)
    have hnonneg : 0 ≤ A * (x ^ theta * Real.log x ^ 2) := by positivity
    nlinarith
  · have hpsi := Chebyshev.psi_mono (show t ≤ 6 by linarith)
    have hp0 := Chebyshev.psi_nonneg t
    have hsmall : |Chebyshev.psi t - t| ≤ A := by
      rw [abs_le]
      dsimp [A]
      constructor <;> linarith
    refine hsmall.trans ?_
    have h1 : A ≤ A * (x ^ theta * Real.log x ^ 2) := le_mul_of_one_le_right hA0 hshape
    have h2 : 0 ≤ |C| * (x ^ theta * Real.log x ^ 2) := by positivity
    nlinarith

/-- Integrating a uniform bound on the psi error. -/
lemma H_le_of_uniform {x B : ℝ} (hx : 0 ≤ x)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ x → |Chebyshev.psi t - t| ≤ B) :
    H x ≤ x * B ^ 2 := by
  have hm : Measurable (fun t : ℝ => (Chebyshev.psi t - t) ^ 2) :=
    (Chebyshev.psi_mono.measurable.sub measurable_id).pow_const 2
  have hsq : ∀ t ∈ Icc (0 : ℝ) x, (Chebyshev.psi t - t) ^ 2 ≤ B ^ 2 := by
    intro t ht
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound t ht.1 ht.2) 2
  have hi : IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t - t) ^ 2) volume 0 x := by
    refine (intervalIntegrable_const (c := B ^ 2)).mono_fun' hm.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hx]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq t ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.integral_mono_on hx hi intervalIntegrable_const hsq
  simpa [H, intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- H x is O of x to the power 2 theta plus 1 times log to the fourth power. -/
theorem H_bound (theta : ℝ) (htheta : 1 / 2 ≤ theta) (htheta1 : theta < 1)
    (hzeros : ∀ ρ : LeanLab.PNTPort.ExplicitPsi1.Zall, ρ.1.re ≤ theta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 6 ≤ x →
      H x ≤ K * x ^ (2 * theta + 1) * Real.log x ^ 4 := by
  obtain ⟨B, hB, hb⟩ := ingham_uniform theta htheta htheta1 hzeros
  refine ⟨B ^ 2, sq_nonneg B, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h := H_le_of_uniform hx0.le (hb x hx)
  refine h.trans (le_of_eq ?_)
  have hp : (x ^ theta) ^ 2 = x ^ (2 * theta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    norm_num
    ring
  have he : x ^ (2 * theta + 1) = x * (x ^ theta) ^ 2 := by
    rw [hp, Real.rpow_add hx0, Real.rpow_one]
    ring
  rw [he]
  ring

/-- The H estimate at the actual supremum Theta. -/
theorem H_theta (htheta : 1 / 2 ≤ Theta) (htheta1 : Theta < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 6 ≤ x →
      H x ≤ K * x ^ (2 * Theta + 1) * Real.log x ^ 4 := by
  apply H_bound Theta htheta htheta1
  intro ρ
  have hz := (Set.ext_iff.mp LeanLab.PNTPort.ExplicitPsi1.Zall_eq (ρ : ℂ)).mp ρ.2
  exact GSCor2.re_le_Theta ⟨ρ.1, hz⟩

/-- Concrete zero length instance of the normalization of H. -/
theorem H_at_zero : H 0 = 0 := by simp [H]

/-- The H estimate specializes to theta equals one half under RH. -/
theorem H_bound_half_of_RH (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 6 ≤ x →
      H x ≤ K * x ^ (2 : ℝ) * Real.log x ^ 4 := by
  have h := H_bound (1 / 2) (by norm_num) (by norm_num)
    (fun ρ => (LeanLab.LZCesaroShort.rh_re hRH ρ.2).le)
  norm_num at h ⊢
  exact h

end LeanLab.GoldbachAverage.InghamTheta
