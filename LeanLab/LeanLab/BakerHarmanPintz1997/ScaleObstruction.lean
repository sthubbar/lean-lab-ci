/-
P0069, pages 4 and 5, short interval input audit.
A global prime number theorem error of Siegel Walfisz size exceeds every fixed sublinear power.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Real

/-- A global exponential square root log error is too large for a sublinear short interval. -/
theorem global_error_exceeds_short_power (c θ C X : ℝ) (hθ : θ < 1) :
    ∃ x : ℝ, X ≤ x ∧ 1 < x ∧
      C * x ^ θ < x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  let δ := 1 - θ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let t := max (max 1 (2 * (|c| + |C| + 1) / δ)) (|X| + 1)
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have htbound : 2 * (|c| + |C| + 1) / δ ≤ t :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have htX : |X| + 1 ≤ t := le_max_right _ _
  have htpos : 0 < t := by linarith
  have hδt : 2 * (|c| + |C| + 1) ≤ δ * t := by
    have := (div_le_iff₀ hδ).mp htbound
    nlinarith only [this]
  have hquad : |C| + θ * t ^ 2 < t ^ 2 - c * t := by
    have hmul := mul_le_mul_of_nonneg_right hδt htpos.le
    have hc := le_abs_self c
    have hct := mul_le_mul_of_nonneg_right hc htpos.le
    have hC := abs_nonneg C
    have hc0 := abs_nonneg c
    have hCt := mul_le_mul_of_nonneg_left ht1 (abs_nonneg C)
    dsimp [δ] at hmul
    nlinarith
  let x := Real.exp (t ^ 2)
  have hxpos : 0 < x := Real.exp_pos _
  have hxlarge : t ^ 2 + 1 ≤ x := Real.add_one_le_exp _
  have hxX : X ≤ x := by
    have := le_abs_self X
    nlinarith
  have hx1 : 1 < x := by nlinarith [sq_pos_of_pos htpos]
  refine ⟨x, hxX, hx1, ?_⟩
  have hlog : Real.log x = t ^ 2 := Real.log_exp _
  have hsqrt : Real.sqrt (Real.log x) = t := by rw [hlog, Real.sqrt_sq htpos.le]
  have hpow : x ^ θ = Real.exp (θ * t ^ 2) := by
    rw [Real.rpow_def_of_pos hxpos, hlog, mul_comm]
  have herr : x * Real.exp (-c * Real.sqrt (Real.log x)) = Real.exp (t ^ 2 - c * t) := by
    rw [hsqrt, ← Real.exp_add]
    congr 1
    ring
  rw [hpow, herr]
  have hCexp : C < Real.exp |C| := by
    have := Real.add_one_le_exp |C|
    have := le_abs_self C
    linarith
  calc C * Real.exp (θ * t ^ 2) < Real.exp |C| * Real.exp (θ * t ^ 2) :=
        mul_lt_mul_of_pos_right hCexp (Real.exp_pos _)
    _ = Real.exp (|C| + θ * t ^ 2) := (Real.exp_add _ _).symm
    _ < _ := Real.exp_lt_exp.mpr hquad

/-- The global error scale is not bounded by a constant times x to a sublinear power. -/
theorem global_error_not_LL (c θ : ℝ) (hθ : θ < 1) :
    ¬ LL (fun x => x * Real.exp (-c * Real.sqrt (Real.log x))) (fun x => x ^ θ) := by
  rintro ⟨K, hK, X, hX⟩
  obtain ⟨x, hxX, _, hx⟩ := global_error_exceeds_short_power c θ (1 / K) X hθ
  have hbound := hX x hxX
  have hstrict := mul_lt_mul_of_pos_left hx hK
  have heq : K * (1 / K * x ^ θ) = x ^ θ := by field_simp
  rw [heq] at hstrict
  linarith

#print axioms global_error_exceeds_short_power
#print axioms global_error_not_LL
end LeanLab.BakerHarmanPintz1997
