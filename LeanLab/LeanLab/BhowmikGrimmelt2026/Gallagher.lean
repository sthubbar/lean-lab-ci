/-
P0029 Bhowmik and Grimmelt 2026, Lemma 5.3, p. 19, as printed, is false for large `η`.
Printed: `∫_{|β|≤η} |Σ_{n≤N} α_n e(βn)|² dβ ≪ ∫_0^{2N} η |Σ_{x−η^{-1}<n≤x} α_n|² dx`.
Take `N = 1`, `α_1 = 1`: the left side is `2η`, the right side is `η · η^{-1} = 1` for `η ≥ 1`.
The standard Gallagher lemma has `η²`, the paper's own (5.3) on p. 20 uses `η²`, and for
`η ≤ 1` the printed form follows from the standard one, so this is a typo in the statement,
harmless for the paper. PRELIMINARY, for the main run's falsifier.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The left side of Lemma 5.3 at `N = 1`, `α = 1`: `2η`. -/
theorem gallagher_lhs (η : ℝ) :
    ∫ β in (-η)..η, ‖∑ n ∈ Finset.Icc 1 1, (fun _ : ℕ => (1 : ℂ)) n * ee (β * n)‖ ^ 2 = 2 * η := by
  simp only [Finset.Icc_self, Finset.sum_singleton, one_mul, Nat.cast_one, mul_one, norm_ee,
    one_pow, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The right side integrand at `N = 1`, `α = 1` is `η` on `[1, 1 + η^{-1})` and `0` elsewhere. -/
theorem gallagher_rhs_integrand (η x : ℝ) :
    η * ‖∑ n ∈ (Finset.Icc 1 1).filter (fun n : ℕ => x - η⁻¹ < n ∧ (n : ℝ) ≤ x),
        (fun _ : ℕ => (1 : ℂ)) n‖ ^ 2 =
      Set.indicator (Set.Ico 1 (1 + η⁻¹)) (fun _ => η) x := by
  simp only [Finset.Icc_self, Finset.filter_singleton, Nat.cast_one]
  by_cases h : x - η⁻¹ < 1 ∧ 1 ≤ x
  · have hx : x ∈ Set.Ico 1 (1 + η⁻¹) := ⟨h.2, by linarith [h.1]⟩
    rw [if_pos h, Set.indicator_of_mem hx]; simp
  · have hx : x ∉ Set.Ico 1 (1 + η⁻¹) := fun hx => h ⟨by linarith [hx.2], hx.1⟩
    rw [if_neg h, Set.indicator_of_notMem hx]; simp

/-- The right side integral at `N = 1`, `α = 1`, `η ≥ 1`: exactly `1`. -/
theorem gallagher_rhs {η : ℝ} (hη : 1 ≤ η) :
    ∫ x in (0 : ℝ)..(2 * (1 : ℕ)),
      η * ‖∑ n ∈ (Finset.Icc 1 1).filter (fun n : ℕ => x - η⁻¹ < n ∧ (n : ℝ) ≤ x),
        (fun _ : ℕ => (1 : ℂ)) n‖ ^ 2 = 1 := by
  simp_rw [gallagher_rhs_integrand]
  have hη0 : 0 < η := by linarith
  have hinv : η⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hη
  rw [intervalIntegral.integral_of_le (by norm_num),
    integral_indicator_const _ measurableSet_Ico, smul_eq_mul,
    Measure.real, Measure.restrict_apply measurableSet_Ico]
  have hsub : Set.Ico (1 : ℝ) (1 + η⁻¹) ∩ Set.Ioc 0 (2 * ((1 : ℕ) : ℝ)) = Set.Ico 1 (1 + η⁻¹) := by
    apply Set.inter_eq_left.mpr
    intro x hx
    exact ⟨by linarith [hx.1], by push_cast; linarith [hx.2]⟩
  rw [hsub, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith [inv_pos.mpr hη0])]
  field_simp
  ring

/-- **Lemma 5.3 as printed is false.** No constant works for all `η > 0`. -/
theorem not_gallagherPrinted : ¬ GallagherPrinted := by
  rintro ⟨C, hC⟩
  set η : ℝ := max C 1 + 1 with hηdef
  have hη1 : 1 ≤ η := by linarith [le_max_right C 1]
  have hηC : C < η := by linarith [le_max_left C 1]
  have h := hC 1 (fun _ => 1) η (by linarith)
  rw [gallagher_lhs, gallagher_rhs hη1] at h
  linarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.not_gallagherPrinted
#print axioms LeanLab.BhowmikGrimmelt2026.norm_ee
#print axioms LeanLab.BhowmikGrimmelt2026.gallagher_lhs
#print axioms LeanLab.BhowmikGrimmelt2026.gallagher_rhs_integrand
#print axioms LeanLab.BhowmikGrimmelt2026.gallagher_rhs
