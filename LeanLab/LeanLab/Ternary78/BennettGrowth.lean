import LeanLab.Ternary78.BennettCorollary

/-
AI wrote this Lean code. Binary Goldbach is open.
A coarse polynomial zero count bound derived from the printed Bennett Theorem 1.1.
This is for summability, not a replacement for the sharper printed statement.
-/

namespace LeanLab.Ternary78.Bennett
open Real

/-- A rational Taylor certificate used only to verify the large ell domain. -/
theorem exp1567_le_six : exp (1.567 : ℝ) ≤ 6 := by
  have hsmall : exp (0.567 : ℝ) ≤ 2 := by
    have h := Real.exp_bound' (x := (0.567 : ℝ)) (by norm_num) (by norm_num)
      (n := 5) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  rw [show (1.567 : ℝ) = 1 + 0.567 by norm_num, exp_add]
  nlinarith [Real.exp_one_lt_d9, exp_pos (1 : ℝ)]

/-- Every positive conductor at least two is in the large ell domain by height twenty. -/
theorem large_ell_of_twenty {q T : ℝ} (hq : 2 ≤ q) (hT : 20 ≤ T) :
    1.567 < log (q * (T + 2) / (2 * Real.pi)) := by
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
  apply exp1567_le_six.trans_lt
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
  have hmul : (44 : ℝ) ≤ q * (T + 2) :=
    (by norm_num : (44 : ℝ) = 2 * 22) ▸
      mul_le_mul hq (by linarith : (22 : ℝ) ≤ T + 2) (by norm_num) hq0.le
  linarith [Real.pi_lt_d2]

#print axioms exp1567_le_six
#print axioms large_ell_of_twenty

/-- Coarse elementary bounds for the two logarithms in the cited theorem. -/
theorem bennett_log_upper {q T : ℝ} (hq : 0 < q) (hT : 0 < T) :
    log (q * T / (2 * Real.pi * exp 1)) ≤ q + T ∧
      log (q * (T + 2) / (2 * Real.pi)) ≤ q + T + 2 := by
  constructor
  · have hden : (1 : ℝ) ≤ 2 * Real.pi * exp 1 := by
      nlinarith [Real.pi_gt_three, Real.exp_one_gt_d9]
    have harg : q * T / (2 * Real.pi * exp 1) ≤ q * T := div_le_self (by positivity) hden
    have hlog := log_le_log (by positivity) harg
    rw [log_mul (ne_of_gt hq) (ne_of_gt hT)] at hlog
    linarith [log_le_sub_one_of_pos hq, log_le_sub_one_of_pos hT]
  · have hden : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hT2 : 0 < T + 2 := by linarith
    have harg : q * (T + 2) / (2 * Real.pi) ≤ q * (T + 2) := div_le_self (by positivity) hden
    have hlog := log_le_log (by positivity) harg
    rw [log_mul (ne_of_gt hq) (ne_of_gt hT2)] at hlog
    linarith [log_le_sub_one_of_pos hq, log_le_sub_one_of_pos hT2]

#print axioms bennett_log_upper

/-- CONDITIONAL ON BennettThm1_1. A coarse quadratic count bound for summability. -/
theorem count_le_quadratic_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 20 ≤ T) :
    (N q χ T : ℝ) ≤ 20 * q * T ^ 2 := by
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq1
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  have hl := large_ell_of_twenty hqr hT
  have h := hB q hq hq1 χ hχ T (by linarith) hl
  have hN := (abs_le.mp h).2
  have hpar : -(1 : ℝ) ≤ (χ (-1) : ℂ).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (χ.norm_le_one _))).1
  have hlogs := bennett_log_upper hq0 hT0
  have hloglog : log (1 + log (q * (T + 2) / (2 * Real.pi))) ≤
      log (q * (T + 2) / (2 * Real.pi)) := by
    have hp : 0 < 1 + log (q * (T + 2) / (2 * Real.pi)) := by linarith
    have hh := log_le_sub_one_of_pos hp
    linarith
  let R : ℝ := q + T + 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hmain : T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) ≤ T * R := by
    calc
      T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) ≤ T / Real.pi * R :=
        mul_le_mul_of_nonneg_left (hlogs.1.trans (by dsimp [R]; linarith)) (by positivity)
      _ ≤ T * R := mul_le_mul_of_nonneg_right
        (div_le_self hT0.le (by linarith [Real.pi_gt_three])) hR.le
  have herror : 0.22737 * log (q * (T + 2) / (2 * Real.pi)) +
      2 * log (1 + log (q * (T + 2) / (2 * Real.pi))) - 0.5 ≤ 3 * R := by
    dsimp [R]
    nlinarith
  have hbound : (N q χ T : ℝ) ≤ 5 * T * R := by
    have hTR : R ≤ T * R := le_mul_of_one_le_left hR.le (by linarith)
    have hR1 : (1 : ℝ) ≤ R := by dsimp [R]; linarith
    linarith
  have hRupper : R ≤ (q + 3) * T := by
    dsimp [R]
    nlinarith [mul_nonneg hq0.le (show 0 ≤ T - 1 by linarith)]
  calc
    (N q χ T : ℝ) ≤ 5 * T * R := hbound
    _ ≤ 5 * T * ((q + 3) * T) := mul_le_mul_of_nonneg_left hRupper (by positivity)
    _ = (5 * q + 15) * T ^ 2 := by ring
    _ ≤ (20 * q) * T ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg T)
    _ = 20 * q * T ^ 2 := rfl

#print axioms count_le_quadratic_of_bennett

/-- CONDITIONAL ON BennettThm1_1. Finite low heights are absorbed into one constant. -/
theorem exists_quadratic_bound_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (N q χ (n + 1 : ℝ) : ℝ) ≤ C * (n + 1 : ℝ) ^ 2 := by
  let D : ℝ := ∑ i ∈ Finset.range 20, (N q χ (i + 1 : ℝ) : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨D + 20 * q, by positivity, ?_⟩
  intro n
  by_cases hn : 20 ≤ n + 1
  · have h := count_le_quadratic_of_bennett hB hq hq1 χ hχ
      (T := (n + 1 : ℝ)) (by exact_mod_cast hn)
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : (20 : ℝ) * q ≤ D + 20 * q)
      (sq_nonneg _))
  · have hmem : n ∈ Finset.range 20 := Finset.mem_range.mpr (by omega)
    have hterm : (N q χ (n + 1 : ℝ) : ℝ) ≤ D :=
      Finset.single_le_sum (f := fun (i : ℕ) => (N q χ (i + 1 : ℝ) : ℝ))
        (fun _ _ => Nat.cast_nonneg _) hmem
    have hC : 0 ≤ D + 20 * q := by positivity
    have hx : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    calc
      (N q χ (n + 1 : ℝ) : ℝ) ≤ D := hterm
      _ ≤ D + 20 * q := le_add_of_nonneg_right (by positivity)
      _ ≤ (D + 20 * q) * (n + 1 : ℝ) ^ 2 := le_mul_of_one_le_right hC hx

#print axioms exists_quadratic_bound_of_bennett

end LeanLab.Ternary78.Bennett
