import LeanLab.Ternary78.BennettRounded

/-
AI wrote this Lean code. Binary Goldbach is open.
Concrete lower certificates for the conductor used by the existing 7/8 model.
The analytic input is Bennett Theorem 1.1 printed page 2 of arXiv 2005.02989.
All auxiliary decimal inequalities below have rational Taylor certificates.
-/

namespace LeanLab.Ternary78.Bennett
open Real
open scoped Classical

/-- Logarithmic bounds for the explicit height 5/2 grid point. -/
theorem grid25_log_bounds :
    (10.68 : ℝ) ≤ log (750000 / (2 * Real.pi * exp 1)) ∧
    log (1350000 / (2 * Real.pi)) ≤ 12.3 ∧ log (13.3 : ℝ) ≤ 2.6 := by
  have hsmall : exp (0.73 : ℝ) ≤ 2.0751 := by
    have h := Real.exp_bound' (x := (0.73 : ℝ)) (by norm_num) (by norm_num)
      (n := 10) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  have he : exp (11.68 : ℝ) ≤ (2.0751 : ℝ) ^ 16 := by
    have h := pow_le_pow_left₀ (exp_pos (0.73 : ℝ)).le hsmall 16
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  constructor
  · apply (Real.le_log_iff_exp_le (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi * exp 1)).mpr
    calc
      exp (10.68 : ℝ) * (2 * Real.pi * exp 1) = 2 * Real.pi * exp 11.68 := by
        rw [show (11.68 : ℝ) = 10.68 + 1 by norm_num, exp_add]
        ring
      _ ≤ 2 * 3.142 * (2.0751 : ℝ) ^ 16 := by
        gcongr
        linarith [Real.pi_lt_d4]
      _ ≤ 750000 := by norm_num
  constructor
  · have hpoint : (1.345 : ℝ) ≤ exp 0.3 := by
      have h := sum_le_exp_of_nonneg (x := (0.3 : ℝ)) (by norm_num) 3
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
      norm_num at h ⊢
      exact h
    have hpow : (2.718 : ℝ) ^ 12 ≤ exp 1 ^ 12 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 12
    have heq : exp 1 ^ 12 * exp (0.3 : ℝ) = exp 12.3 := by
      rw [← Real.exp_nat_mul, ← exp_add]
      norm_num
    have hlow : (2.718 : ℝ) ^ 12 * 1.345 ≤ exp 12.3 := by
      rw [← heq]
      exact mul_le_mul hpow hpoint (by norm_num) (by positivity)
    apply (log_le_iff_le_exp (by positivity)).mpr
    calc
      (1350000 : ℝ) / (2 * Real.pi) ≤ 1350000 / (2 * 3.1415) := by
        gcongr
        exact Real.pi_gt_d4.le
      _ ≤ (2.718 : ℝ) ^ 12 * 1.345 := by norm_num
      _ ≤ exp 12.3 := hlow
  · apply (log_le_iff_le_exp (by norm_num)).mpr
    have h := sum_le_exp_of_nonneg (x := (2.6 : ℝ)) (by norm_num) 12
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢
    linarith

#print axioms grid25_log_bounds

/-- A positive lower endpoint for every character at the target conductor.
Primitivity is needed only when the cited count theorem is later applied. -/
theorem grid25_lower_certificate (χ : DirichletCharacter ℂ 300000) :
    1.567 < log (1350000 / (2 * Real.pi)) ∧ (3 / 4 : ℝ) ≤ lowerEndpoint χ (5 / 2) := by
  have hmain := grid25_log_bounds.1
  have hell := grid25_log_bounds.2.1
  have hcomp : (750000 : ℝ) / (2 * Real.pi * exp 1) ≤ 1350000 / (2 * Real.pi) := by
    calc
      (750000 : ℝ) / (2 * Real.pi * exp 1) = (750000 / (2 * Real.pi)) / exp 1 := by ring
      _ ≤ 750000 / (2 * Real.pi) := div_le_self (by positivity) (by linarith [Real.exp_one_gt_d9])
      _ ≤ 1350000 / (2 * Real.pi) := by gcongr; norm_num
  have hlow : (10.68 : ℝ) ≤ log (1350000 / (2 * Real.pi)) :=
    hmain.trans (log_le_log (by positivity) hcomp)
  have hlog : log (1 + log (1350000 / (2 * Real.pi))) ≤ (2.6 : ℝ) :=
    (log_le_log (by linarith) (by linarith : 1 + log (1350000 / (2 * Real.pi)) ≤ 13.3)).trans
      grid25_log_bounds.2.2
  have hcoef : (2.5 : ℝ) / 3.142 ≤ 2.5 / Real.pi := by
    gcongr
    linarith [Real.pi_lt_d4]
  have hprod := mul_le_mul hcoef hmain (by norm_num : (0 : ℝ) ≤ 10.68)
    (by positivity : (0 : ℝ) ≤ 2.5 / Real.pi)
  have hpar : (χ (-1) : ℂ).re ≤ 1 :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))
  constructor
  · linarith
  · unfold lowerEndpoint
    norm_num at hmain hell hlog hprod ⊢
    linarith

#print axioms grid25_lower_certificate

/-- CONDITIONAL ON BennettThm1_1. At least one zero is counted through height 5/2. -/
theorem count_grid25_positive
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ}
    (hB : BennettThm1_1 N 300000) (χ : DirichletCharacter ℂ 300000) (hχ : χ.IsPrimitive) :
    1 ≤ N 300000 χ (5 / 2) := by
  have hc := grid25_lower_certificate χ
  have h := lowerEndpoint_le_count hB (by rfl) (by norm_num) χ hχ
    (T := 5 / 2) (by norm_num) (by have hdom := hc.1; norm_num at hdom ⊢; exact hdom)
  have hlow : (3 / 4 : ℝ) ≤ N 300000 χ (5 / 2) := hc.2.trans ((le_max_right _ _).trans h)
  by_contra hn
  have hzero : N 300000 χ (5 / 2) = 0 := by omega
  rw [hzero] at hlow
  norm_num at hlow

#print axioms count_grid25_positive

/-- CONDITIONAL ON BennettThm1_1. A concrete Gamma weight lower bound at
conductor 300000, without any asserted decimal evaluation of Gamma. -/
theorem gamma25_tsum_lower
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ}
    (hB : BennettThm1_1 N 300000) (χ : DirichletCharacter ℂ 300000) (hχ : χ.IsPrimitive)
    {ι : Type*} [DecidableEq ι] (z : Finset ι) (γ : ι → ℝ)
    (hcount : N 300000 χ (5 / 2) = (z.filter (fun a => |γ a| ≤ 5 / 2)).card) :
    ENNReal.ofReal ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + ((5 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑' a, ENNReal.ofReal ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (γ a : ℂ) * Complex.I)‖ := by
  classical
  have hc := count_grid25_positive hB χ hχ
  have hz : 0 < (z.filter (fun a => |γ a| ≤ (5 / 2 : ℝ))).card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hz
  have haT := (Finset.mem_filter.mp ha).2
  have hw := gamma_norm_antitone (by norm_num : (0 : ℝ) < 7 / 8)
    (show |γ a| ∈ Set.Ici (0 : ℝ) from abs_nonneg (γ a))
    (show (5 / 2 : ℝ) ∈ Set.Ici 0 by norm_num) haT
  dsimp only at hw
  rw [gamma_norm_abs] at hw
  exact (ENNReal.ofReal_le_ofReal hw).trans (ENNReal.le_tsum (f := fun a => ENNReal.ofReal
    ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + (γ a : ℂ) * Complex.I)‖) a)

/-- The concrete lower weight is strictly positive. -/
theorem gamma25_weight_pos :
    0 < ‖Complex.Gamma (((7 / 8 : ℝ) : ℂ) + ((5 / 2 : ℝ) : ℂ) * Complex.I)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff _).mp hz
  have hi := congrArg Complex.im hm
  norm_num at hi

#print axioms gamma25_tsum_lower
#print axioms gamma25_weight_pos

end LeanLab.Ternary78.Bennett
