import LeanLab.Ternary78.BennettLower

/-
AI wrote this Lean code. Binary Goldbach is open.
Source: https://arxiv.org/abs/2005.02989 printed page 2 Corollary 1.2.
The numerical logarithm estimates below are elementary consequences of Mathlib.
-/

namespace LeanLab.Ternary78.Bennett
open Real

/-- Rational certificates for the logarithmic tangents used by Corollary 1.2. -/
theorem cor12_log_constants :
    log (200000 / 1963 : ℝ) ≤ 4.62385 ∧
    log (200000 / 7063 : ℝ) ≤ 3.34345 ∧
    log (19 / (10 * Real.pi)) ≤ -0.5028 := by
  constructor
  · rw [log_le_iff_le_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := (4.62385 : ℝ)) (by norm_num) 25
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢
    linarith
  constructor
  · rw [log_le_iff_le_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := (3.34345 : ℝ)) (by norm_num) 22
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢
    linarith
  · have he : exp (0.5028 : ℝ) ≤ 1.65335 := by
      have h := Real.exp_bound' (x := (0.5028 : ℝ)) (by norm_num) (by norm_num)
        (n := 10) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
      norm_num at h ⊢
      linarith
    have hp : exp (0.5028 : ℝ) ≤ 10 * Real.pi / 19 := by
      have := Real.pi_gt_d4
      linarith
    have hl : (0.5028 : ℝ) ≤ log (10 * Real.pi / 19) :=
      (Real.le_log_iff_exp_le (by positivity)).mpr hp
    have hi : (19 / (10 * Real.pi) : ℝ) = (10 * Real.pi / 19)⁻¹ := by field_simp
    rw [hi, Real.log_inv]
    linarith

#print axioms cor12_log_constants

/-- The two printed affine error envelopes, including the parity cost 1/4. -/
theorem cor12_error_envelope {l L : ℝ} (hl : -1 < l) (hL : l ≤ L - 0.5028) :
    0.22737 * l + 2 * log (1 + l) - 0.5 + 1 / 4 ≤
      min (0.247 * L + 6.894) (0.298 * L + 4.358) := by
  have hpos : 0 < 1 + l := by linarith
  apply le_min
  · have h := log_le_sub_one_of_pos (div_pos hpos (show (0 : ℝ) < 200000 / 1963 by norm_num))
    rw [log_div (by positivity : (1 + l : ℝ) ≠ 0) (by norm_num)] at h
    norm_num at h
    nlinarith [cor12_log_constants.1]
  · have h := log_le_sub_one_of_pos (div_pos hpos (show (0 : ℝ) < 200000 / 7063 by norm_num))
    rw [log_div (by positivity : (1 + l : ℝ) ≠ 0) (by norm_num)] at h
    norm_num at h
    nlinarith [cor12_log_constants.2.1]

#print axioms cor12_error_envelope

/-- The height restriction gives exactly the logarithmic shift needed above. -/
theorem cor12_log_height {q T : ℝ} (hq : 0 < q) (hT : 5 / 7 ≤ T) :
    log (q * (T + 2) / (2 * Real.pi)) ≤ log (q * T) - 0.5028 := by
  have hT0 : 0 < T := by linarith
  have harg : q * (T + 2) / (2 * Real.pi) ≤ q * T * (19 / (10 * Real.pi)) := by
    calc q * (T + 2) / (2 * Real.pi) = q / (2 * Real.pi) * (T + 2) := by ring
      _ ≤ q / (2 * Real.pi) * (19 / 5 * T) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = q * T * (19 / (10 * Real.pi)) := by field_simp; ring
  calc log (q * (T + 2) / (2 * Real.pi)) ≤ log (q * T * (19 / (10 * Real.pi))) :=
      log_le_log (by positivity) harg
    _ = log (q * T) + log (19 / (10 * Real.pi)) := log_mul (by positivity) (by positivity)
    _ ≤ log (q * T) - 0.5028 := by linarith [cor12_log_constants.2.2]

#print axioms cor12_log_height

/-- CONDITIONAL ON BennettThm1_1. Corollary 1.2 on the large ell domain
covered by the existing cited input, with both printed constants unchanged. -/
theorem cor12_large_of_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1 N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {T : ℝ} (hT : 5 / 7 ≤ T)
    (hl : 1.567 < log (q * (T + 2) / (2 * Real.pi))) :
    |(N q χ T : ℝ) - T / Real.pi * log (q * T / (2 * Real.pi * exp 1))| ≤
      min (0.247 * log (q * T) + 6.894) (0.298 * log (q * T) + 4.358) := by
  have h := hB q hq hq1 χ hχ T hT hl
  have hpar : |(χ (-1) : ℂ).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
  have hpar' : |(χ (-1) : ℂ).re / 4| ≤ (1 / 4 : ℝ) := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right hpar (by norm_num)
  have htriangle := abs_add_le
    ((N q χ T : ℝ) - (T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) -
      (χ (-1) : ℂ).re / 4)) (-(χ (-1) : ℂ).re / 4)
  have hshift := cor12_log_height (q := (q : ℝ)) (by exact_mod_cast (by omega : 0 < q)) hT
  have henv := cor12_error_envelope (by linarith : (-1 : ℝ) <
    log (q * (T + 2) / (2 * Real.pi))) hshift
  have hnorm : |(N q χ T : ℝ) - T / Real.pi * log (q * T / (2 * Real.pi * exp 1))| ≤
      0.22737 * log (q * (T + 2) / (2 * Real.pi)) +
        2 * log (1 + log (q * (T + 2) / (2 * Real.pi))) - 0.5 + 1 / 4 := by
    have he : ((N q χ T : ℝ) - (T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) -
        (χ (-1) : ℂ).re / 4)) + (-(χ (-1) : ℂ).re / 4) =
        (N q χ T : ℝ) - T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) := by ring
    rw [he] at htriangle
    rw [neg_div, abs_neg] at htriangle
    linarith
  exact hnorm.trans henv

#print axioms cor12_large_of_bennett

/-- A universal lower bound for the printed main term at positive q and T. -/
theorem mainTerm_ge_neg_two_div {q T : ℝ} (hq : 0 < q) (hT : 0 < T) :
    -2 / q ≤ T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) := by
  let y := q * T / (2 * Real.pi)
  have hy : 0 < y := by dsimp [y]; positivity
  have hlog : log (q * T / (2 * Real.pi * exp 1)) = log y - 1 := by
    rw [show q * T / (2 * Real.pi * exp 1) = y / exp 1 by dsimp [y]; ring,
      log_div (ne_of_gt hy) (ne_of_gt (exp_pos 1)), log_exp]
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hy) hy.le
  have hi : y * y⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hy)
  have hbase : -1 ≤ y * (log y - 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ 2 / q by positivity)
  rw [hlog]
  convert hmul using 1 <;> (try dsimp only [y]) <;> field_simp [ne_of_gt hq, Real.pi_ne_zero]

#print axioms mainTerm_ge_neg_two_div

/-- A coarse main term bound suffices for the omitted small ell branch. -/
theorem small_mainTerm_abs_le_four {q T : ℝ} (hq : 2 ≤ q) (hT : 5 / 7 ≤ T)
    (hl : log (q * (T + 2) / (2 * Real.pi)) ≤ 1.567) :
    |T / Real.pi * log (q * T / (2 * Real.pi * exp 1))| ≤ 4 := by
  have hq0 : 0 < q := by linarith
  have hT0 : 0 < T := by linarith
  have he : exp (1.567 : ℝ) ≤ 6 := by
    have hsmall : exp (0.567 : ℝ) ≤ 2 := by
      have h := Real.exp_bound' (x := (0.567 : ℝ)) (by norm_num) (by norm_num)
        (n := 5) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
      norm_num at h
      linarith
    rw [show (1.567 : ℝ) = 1 + 0.567 by norm_num, exp_add]
    nlinarith [Real.exp_one_lt_d9, exp_pos (1 : ℝ)]
  have harg : q * (T + 2) / (2 * Real.pi) ≤ 6 :=
    ((log_le_iff_le_exp (by positivity)).mp hl).trans he
  have hheight : T / Real.pi ≤ 6 := by
    have harg' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp harg
    have hmul : 2 * (T + 2) ≤ q * (T + 2) :=
      mul_le_mul_of_nonneg_right hq (by linarith)
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith
  have hlog : log (q * T / (2 * Real.pi * exp 1)) ≤ 0.567 := by
    have hcomp : q * T / (2 * Real.pi) ≤ q * (T + 2) / (2 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have hlog' := (log_le_log (by positivity) hcomp).trans hl
    rw [show q * T / (2 * Real.pi * exp 1) = (q * T / (2 * Real.pi)) / exp 1 by ring,
      log_div (by positivity) (ne_of_gt (exp_pos 1)), log_exp]
    linarith
  have hupper : T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) ≤ 4 := by
    calc T / Real.pi * log (q * T / (2 * Real.pi * exp 1)) ≤ T / Real.pi * 0.567 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 6 * 0.567 := mul_le_mul_of_nonneg_right hheight (by norm_num)
      _ ≤ 4 := by norm_num
  have hneg : (-1 : ℝ) ≤ -2 / q := by
    apply (le_div_iff₀ hq0).mpr
    linarith
  exact abs_le.mpr ⟨by linarith [mainTerm_ge_neg_two_div hq0 hT0], hupper⟩

#print axioms small_mainTerm_abs_le_four

/-- Both printed branches of Theorem 1.1 for primitive characters of conductor q.
CITED, not proved. The existing large ell Prop is preserved as the first conjunct. -/
def BennettThm1_1Full
    (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) (Q : ℕ) : Prop :=
  BennettThm1_1 N Q ∧
    ∀ (q : ℕ) [NeZero q], q ≤ Q → 1 < q →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 5 / 7 ≤ T →
        log (q * (T + 2) / (2 * Real.pi)) ≤ 1.567 → N q χ T = 0

/-- CONDITIONAL ON the full printed Theorem 1.1. Printed Corollary 1.2
for primitive characters, with its full height domain and exact constants. -/
theorem cor12_of_full_bennett
    {N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ} {Q q : ℕ} [NeZero q]
    (hB : BennettThm1_1Full N Q) (hq : q ≤ Q) (hq1 : 1 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 5 / 7 ≤ T) :
    |(N q χ T : ℝ) - T / Real.pi * log (q * T / (2 * Real.pi * exp 1))| ≤
      min (0.247 * log (q * T) + 6.894) (0.298 * log (q * T) + 4.358) := by
  by_cases hl : 1.567 < log (q * (T + 2) / (2 * Real.pi))
  · exact cor12_large_of_bennett hB.1 hq hq1 χ hχ hT hl
  · have hl' := le_of_not_gt hl
    have hzero := hB.2 q hq hq1 χ hχ T hT hl'
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
    have hmain := small_mainTerm_abs_le_four hq2 hT hl'
    have hprod : (1 : ℝ) ≤ q * T := by nlinarith
    have hlog : 0 ≤ log (q * T) := Real.log_nonneg hprod
    rw [hzero]
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    exact hmain.trans (le_min (by linarith) (by linarith))

/-- The full cited input has an unconditional empty modulus range instance. -/
example (N : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℕ) : BennettThm1_1Full N 0 := by
  constructor
  · intro q _ hq hq1
    omega
  · intro q _ hq hq1
    omega

#print axioms cor12_of_full_bennett

end LeanLab.Ternary78.Bennett
