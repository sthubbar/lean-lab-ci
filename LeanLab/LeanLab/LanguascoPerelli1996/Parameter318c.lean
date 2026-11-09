import LeanLab.LanguascoPerelli1996.Parameter318b
import LeanLab.LanguascoPerelli1996.Section5381b

/-!
P0071 page 360 display 25, real parameter extension at modulus one.
The printed character uniform estimate stays cited.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Parameter318c
open Real MeasureTheory intervalIntegral

/-- Pages 359 and 360, derived comparison of the reciprocal principal terms. -/
theorem principal_parameter_difference_le {N K : ℝ} (hN : 0 < N) (hNK : N ≤ K) (η : ℝ) :
    ‖1 / Section5108.laplaceParameter N η - 1 / Section5108.laplaceParameter K η‖ ≤ K - N := by
  have hK : 0 < K := hN.trans_le hNK
  have hzN := Section5108.laplaceParameter_ne_zero hN η
  have hzK := Section5108.laplaceParameter_ne_zero hK η
  have hn : N⁻¹ ≤ ‖Section5108.laplaceParameter N η‖ := by
    simpa [Section5108.laplaceParameter, abs_of_pos (inv_pos.mpr hN)] using
      Complex.abs_re_le_norm (Section5108.laplaceParameter N η)
  have hk : K⁻¹ ≤ ‖Section5108.laplaceParameter K η‖ := by
    simpa [Section5108.laplaceParameter, abs_of_pos (inv_pos.mpr hK)] using
      Complex.abs_re_le_norm (Section5108.laplaceParameter K η)
  have he : 1 / Section5108.laplaceParameter N η - 1 / Section5108.laplaceParameter K η =
      ((K⁻¹ - N⁻¹ : ℝ) : ℂ) /
        (Section5108.laplaceParameter N η * Section5108.laplaceParameter K η) := by
    field_simp
    unfold Section5108.laplaceParameter
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hN.ne', Complex.ofReal_ne_zero.mpr hK.ne'] <;> ring
  have hδ : 0 ≤ N⁻¹ - K⁻¹ := sub_nonneg.mpr (inv_anti₀ hN hNK)
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hδ, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hzN) (norm_pos_iff.mpr hzK))).2
  have hh := mul_le_mul hn hk (inv_pos.mpr hK).le (norm_nonneg _)
  have hid : N⁻¹ - K⁻¹ = (K - N) * (N⁻¹ * K⁻¹) := by field_simp <;> ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hNK)

/-- Page 360 display 25, derived adjacent parameter comparison of the damped error. -/
theorem dampedError_adjacent_le {N K : ℝ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKN : K ≤ N + 1)
    (η : ℝ) :
    ‖(Section5108.dampedSum N η (1 : DirichletCharacter ℂ 1) - 1 / Section5108.laplaceParameter N η) -
      (Section5108.dampedSum K η (1 : DirichletCharacter ℂ 1) - 1 / Section5108.laplaceParameter K η)‖ ≤
        81 * Real.sqrt N := by
  have hN0 : 0 < N := by linarith
  have hs : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have he : (Section5108.dampedSum N η (1 : DirichletCharacter ℂ 1) - 1 / Section5108.laplaceParameter N η) -
      (Section5108.dampedSum K η (1 : DirichletCharacter ℂ 1) - 1 / Section5108.laplaceParameter K η) =
      (Section5108.dampedSum N η (1 : DirichletCharacter ℂ 1) - Section5108.dampedSum K η (1 : DirichletCharacter ℂ 1)) -
        (1 / Section5108.laplaceParameter N η - 1 / Section5108.laplaceParameter K η) := by ring
  rw [he]
  have hh := norm_sub_le
    (Section5108.dampedSum N η (1 : DirichletCharacter ℂ 1) - Section5108.dampedSum K η (1 : DirichletCharacter ℂ 1))
    (1 / Section5108.laplaceParameter N η - 1 / Section5108.laplaceParameter K η)
  have h1 := Parameter318b.dampedSum_adjacent_le hN hNK hKN η (1 : DirichletCharacter ℂ 1)
  have h2 := principal_parameter_difference_le hN0 hNK η
  linarith

/-- Page 360 display 25 for modulus one and every real N at least four.
CONDITIONAL ON RiemannHypothesis alone, with a complete proof and clean axioms.
The integer result extends by the adjacent damping parameter comparison. -/
theorem estimate25_mod_one_real (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 4 ≤ N → ∀ Q : ℝ, 1 ≤ Q → Q ≤ N →
      (∫ η in (-(1 / Q))..(1 / Q),
        ‖Section5108.dampedSum N η (1 : DirichletCharacter ℂ 1) -
          1 / Section5108.laplaceParameter N η‖ ^ 2) ≤
        C * N * Real.log N ^ 2 / Q := by
  obtain ⟨C, hC, hm⟩ := Section5381b.estimate25_mod_one_all_Q hRH
  refine ⟨16 * C + 26245, by positivity, ?_⟩
  intro N hN Q hQ hQN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hQ0 : 0 < Q := by linarith
  let k := ⌈N⌉₊
  let K : ℝ := k
  have hNK : N ≤ K := Nat.le_ceil N
  have hKN : K ≤ N + 1 := (Nat.ceil_lt_add_one hN0.le).le
  have hK0 : 0 < K := hN0.trans_le hNK
  have hK4 : 4 ≤ k := by
    have hh : (4 : ℝ) ≤ (k : ℝ) := hN.trans hNK
    exact_mod_cast hh
  have hK2 : K ≤ 2 * N := by linarith
  let f := fun A η => Section5108.dampedSum A η (1 : DirichletCharacter ℂ 1) -
    1 / Section5108.laplaceParameter A η
  have hc (A : ℝ) (hA : 0 < A) : Continuous (f A) := by
    apply (Section5381b.continuous_dampedSum hA _).sub
    apply continuous_const.div
    · unfold Section5108.laplaceParameter
      fun_prop
    · exact fun η => Section5108.laplaceParameter_ne_zero hA η
  have hp (η : ℝ) : ‖f N η‖ ^ 2 ≤ 2 * ‖f K η‖ ^ 2 + 2 * (81 * Real.sqrt N) ^ 2 := by
    have hd : ‖f N η - f K η‖ ≤ 81 * Real.sqrt N := dampedError_adjacent_le hN1 hNK hKN η
    have hn : ‖f N η‖ ≤ ‖f K η‖ + ‖f N η - f K η‖ := by
      calc
        _ = ‖f K η + (f N η - f K η)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have ht : ‖f N η‖ ≤ ‖f K η‖ + 81 * Real.sqrt N := by linarith
    have hh := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg (‖f K η‖ - 81 * Real.sqrt N)]
  have hab : -(1 / Q) ≤ 1 / Q := by
    have hh : (0 : ℝ) ≤ 1 / Q := by positivity
    linarith
  have hint := integral_mono_on (μ := volume) hab
    (((hc N hN0).norm.pow 2).intervalIntegrable _ _)
    (((continuous_const.mul ((hc K hK0).norm.pow 2)).add continuous_const).intervalIntegrable _ _)
    (fun η _ => hp η)
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at hint
  have hi1 : IntervalIntegrable (fun η => 2 * ‖f K η‖ ^ 2) volume (-(1 / Q)) (1 / Q) :=
    (((hc K hK0).norm.pow 2).intervalIntegrable _ _).const_mul _
  have hi2 : IntervalIntegrable (fun _ : ℝ => 2 * (81 * Real.sqrt N) ^ 2) volume (-(1 / Q)) (1 / Q) :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hint
  have hgeom : (1 / Q - -(1 / Q)) * (2 * (81 * Real.sqrt N) ^ 2) = 26244 * N / Q := by
    rw [mul_pow, Real.sq_sqrt hN0.le]
    ring
  rw [hgeom] at hint
  have hb := hm k hK4 Q hQ (hQN.trans hNK)
  change (∫ η in (-(1 / Q))..(1 / Q), ‖f K η‖ ^ 2) ≤ C * K * Real.log K ^ 2 / Q at hb
  have hlog : 1 ≤ Real.log N := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_gt_d9]
    exact h4.trans (Real.log_le_log (by norm_num) hN)
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
  have hlogK : Real.log K ≤ 2 * Real.log N := by
    have hh := Real.log_le_log hK0 hK2
    rw [Real.log_mul (by norm_num) hN0.ne'] at hh
    linarith
  have hlogsq : Real.log K ^ 2 ≤ 4 * Real.log N ^ 2 := by
    have hh := pow_le_pow_left₀ (Real.log_nonneg (hN1.trans hNK)) hlogK 2
    nlinarith
  have hterm : K * Real.log K ^ 2 ≤ 8 * N * Real.log N ^ 2 := by
    have hh := mul_le_mul hK2 hlogsq (sq_nonneg _) (show 0 ≤ 2 * N by positivity)
    nlinarith
  have h1 : C * K * Real.log K ^ 2 / Q ≤ C * (8 * N * Real.log N ^ 2) / Q := by
    exact div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hterm hC.le]) hQ0.le
  have h2 : 26244 * N / Q ≤ 26244 * (N * Real.log N ^ 2) / Q := by
    apply div_le_div_of_nonneg_right _ hQ0.le
    nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ Real.log N ^ 2 by nlinarith) hN0.le]
  change (∫ η in (-(1 / Q))..(1 / Q), ‖f N η‖ ^ 2) ≤ _
  have hn : 0 ≤ N * Real.log N ^ 2 / Q := by positivity
  calc
    _ ≤ 2 * (∫ η in (-(1 / Q))..(1 / Q), ‖f K η‖ ^ 2) + 26244 * N / Q := hint
    _ ≤ 2 * (C * K * Real.log K ^ 2 / Q) + 26244 * N / Q := by
      exact add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ ≤ 2 * (C * (8 * N * Real.log N ^ 2) / Q) + 26244 * (N * Real.log N ^ 2) / Q :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)) h2
    _ = (16 * C + 26244) * (N * Real.log N ^ 2 / Q) := by ring
    _ ≤ (16 * C + 26245) * (N * Real.log N ^ 2 / Q) :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    _ = _ := by ring

end LeanLab.LanguascoPerelli1996.Parameter318c

#print axioms LeanLab.LanguascoPerelli1996.Parameter318c.principal_parameter_difference_le
#print axioms LeanLab.LanguascoPerelli1996.Parameter318c.dampedError_adjacent_le
#print axioms LeanLab.LanguascoPerelli1996.Parameter318c.estimate25_mod_one_real
