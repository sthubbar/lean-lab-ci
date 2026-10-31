/-
P0069, pages 1 and 24, a normalization QUESTION.
The interval I has width 2Y. The encoded equation 4.2 uses Y/y1.
This diagnostic proves a fact about that predicate. It does not assert a paper error.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.DecompBounds
open Finset
namespace LeanLab.BakerHarmanPintz1997
open LeanLab.BakerHarmanPintz1997.Decomp1518
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
/-- The constant family cannot satisfy the encoded transfer factor with the page 1 interval. -/
theorem not_holds42_constant_one {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 20) :
    ¬ Holds42 ε (fun _ _ => (1 : ℂ)) := by
  intro h
  obtain ⟨C, X0, hC⟩ := holds42_real_upper (ε := ε) (e := fun _ _ => 1) h 1 (by norm_num)
  let T : ℝ := max 216 (max X0 (4 * |C| + 1))
  let x : ℝ := Real.exp T
  have hT : 216 ≤ T := le_max_left _ _
  have hTX : X0 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTC : 4 * |C| + 1 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := Real.exp_pos _
  have hxX : X0 ≤ x := by have := Real.add_one_le_exp T; dsimp [x]; linarith
  have hlog : Real.log x = T := Real.log_exp _
  have h216 : (216 : ℝ) ^ (2 / 3 : ℝ) = 36 := by
    rw [show (216 : ℝ) = 6 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h6 : 6 ≤ T ^ (2 / 3 : ℝ) := by
    have he := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 216) hT (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [h216] at he
    linarith
  have hrootid : T ^ (1 / 3 : ℝ) * T ^ (2 / 3 : ℝ) = T := by
    rw [← Real.rpow_add hT0]; norm_num
  have hroot : 3 * T ^ (1 / 3 : ℝ) ≤ T / 2 := by
    have he := mul_le_mul_of_nonneg_left h6 (Real.rpow_nonneg hT0.le (1 / 3 : ℝ))
    nlinarith
  have hY : Yof ε x = Real.exp (T * (11 / 20 + ε)) := by
    unfold Yof theta1
    rw [Real.rpow_def_of_pos hx0, hlog]
  have hy : y1 x = Real.exp (T - 3 * T ^ (1 / 3 : ℝ)) := by
    rw [y1, hlog, show x = Real.exp T from rfl, ← Real.exp_add]
    congr 1
    ring
  have hY4 : 4 ≤ Yof ε x := by
    rw [hY]
    have := Real.add_one_le_exp (T * (11 / 20 + ε))
    have heps := mul_nonneg hT0.le hε
    nlinarith
  have hy4 : 4 ≤ y1 x := by rw [hy]; have := Real.add_one_le_exp (T - 3 * T ^ (1 / 3 : ℝ)); linarith
  have hy0 : 0 < y1 x := by linarith
  have hY0 : 0 ≤ Yof ε x := by linarith
  have hxY : 2 * Yof ε x ≤ x := by
    rw [hY]
    have he : 2 ≤ Real.exp (T * (9 / 20 - ε)) := by
      have := Real.add_one_le_exp (T * (9 / 20 - ε))
      have heps := mul_le_mul_of_nonneg_left hεsmall hT0.le
      nlinarith
    calc 2 * Real.exp (T * (11 / 20 + ε)) ≤
        Real.exp (T * (9 / 20 - ε)) * Real.exp (T * (11 / 20 + ε)) :=
          mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = x := by dsimp [x]; rw [← Real.exp_add]; congr 1; ring
  have hs := (Iset_card_bounds hY0 hxY).1
  have hlong : ((Ioc ⌊x - y1 x⌋₊ ⌊x⌋₊).card : ℝ) ≤ y1 x + 1 := by
    have hm : ⌊x - y1 x⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono (by linarith)
    rw [Nat.card_Ioc, Nat.cast_sub hm]
    linarith [Nat.floor_le hx0.le, Nat.lt_floor_add_one (x - y1 x)]
  have hratio : 0 ≤ Yof ε x / y1 x := div_nonneg hY0 hy0.le
  have hscaled := mul_le_mul_of_nonneg_left hlong hratio
  have hid : Yof ε x / y1 x * (y1 x + 1) = Yof ε x + Yof ε x / y1 x := by
    field_simp [hy0.ne']
  rw [hid] at hscaled
  have hratio4 : Yof ε x / y1 x ≤ Yof ε x / 4 := div_le_div_of_nonneg_left hY0 (by norm_num) hy4
  have hCT : C / T ≤ 1 / 4 := by
    apply (div_le_iff₀ hT0).mpr
    have := le_abs_self C
    linarith
  have herr : C * Yof ε x / L x ≤ Yof ε x / 4 := by
    rw [L, hlog]
    calc C * Yof ε x / T = (C / T) * Yof ε x := by ring
      _ ≤ (1 / 4) * Yof ε x := mul_le_mul_of_nonneg_right hCT hY0
      _ = _ := by ring
  have htransfer := hC x hxX
  simp only [sum_const, nsmul_eq_mul, mul_one, Real.rpow_one] at htransfer
  nlinarith

#print axioms not_holds42_constant_one
end LeanLab.BakerHarmanPintz1997
