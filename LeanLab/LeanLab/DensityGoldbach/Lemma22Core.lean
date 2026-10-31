/-
P0038 Shao 2012, Lemma 2.2, the real inequality (7): `U + V - W ≤ 3m² + 9`, after the
substitution `x = 16/5 a - 1` and the block summations. Each case is its own lemma.
AI-written Lean code, Claude, 2026-10-17, run 20261016T2303Z-22954, unit U-0098.
-/
import Mathlib

namespace LeanLab.DensityGoldbach

lemma prod_le_box {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 11 / 5) (hb : -1 ≤ b) (hb' : b ≤ 11 / 5) :
    a * b ≤ (11 / 5) ^ 2 := by
  rcases le_total 0 a with h | h <;> rcases le_total 0 b with h' | h' <;> nlinarith

lemma U_caseA {r s t : ℝ} (hr : -2 ≤ r) (hs : -2 ≤ s) (ht : -2 ≤ t)
    (hrs : r + s < 0) : r * s + s * t + t * r ≤ 12 := by
  have h1 : (r + s) * t ≤ -2 * (r + s) := by nlinarith
  have h2 : (r - 2) * (s - 2) ≤ 16 := by nlinarith
  nlinarith

/-- Moving one variable of `xy + yz + zx` down when the other two sum to `≤ 0` raises it. -/
lemma sym_step_down {X X' Y Z : ℝ} (hX : X' ≤ X) (hYZ : Y + Z ≤ 0) :
    X * Y + Y * Z + Z * X ≤ X' * Y + Y * Z + Z * X' := by
  have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hX) hYZ
  linear_combination this

/-- Moving one variable up when the other two sum to `≥ 0` raises it. -/
lemma sym_step_up {X X' Y Z : ℝ} (hX : X ≤ X') (hYZ : 0 ≤ Y + Z) :
    X * Y + Y * Z + Z * X ≤ X' * Y + Y * Z + Z * X' := by
  have := mul_nonneg (sub_nonneg.2 hX) hYZ
  linear_combination this

/-- Case (i), final arithmetic: with `xm, ym, zm ∈ [-1, 11/5]` and `L ≥ 4`. -/
lemma case_i_final (xm ym zm L : ℝ) (hxm : -1 ≤ xm) (hym : -1 ≤ ym) (hzm : -1 ≤ zm)
    (hxm' : xm ≤ 11 / 5) (hym' : ym ≤ 11 / 5) (hzm' : zm ≤ 11 / 5) (hL : 4 ≤ L) :
    ((11 / 5 + xm) * (11 / 5 + ym) + (11 / 5 + ym) * (11 / 5 + zm) + (11 / 5 + zm) * (11 / 5 + xm))
      + ((xm - L) * (ym - L) + (ym - L) * (zm - L) + (zm - L) * (xm - L))
      - (xm * ym + ym * zm + zm * xm) ≤ 3 * (L + 1) ^ 2 + 9 := by
  have hv1 : (xm + 1) * (ym + 1) ≤ 8 / 5 * ((xm + 1) + (ym + 1)) := by
    rcases le_total xm ym with h | h <;> nlinarith
  have hv2 : (ym + 1) * (zm + 1) ≤ 8 / 5 * ((ym + 1) + (zm + 1)) := by
    rcases le_total ym zm with h | h <;> nlinarith
  have hv3 : (zm + 1) * (xm + 1) ≤ 8 / 5 * ((zm + 1) + (xm + 1)) := by
    rcases le_total zm xm with h | h <;> nlinarith
  have hc := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L - 22 / 5 - 6 / 5)
    (by linarith : (0 : ℝ) ≤ (xm + 1) + (ym + 1) + (zm + 1))
  nlinarith

/-- Cases (ii), (iii): not all negative, some pair sum negative, all `≥ -m`: `V ≤ m²`. -/
lemma V_le_sq (X Y Z m : ℝ) (hX : -m ≤ X) (hY : -m ≤ Y) (hZ : -m ≤ Z)
    (hnot : ¬ (X < 0 ∧ Y < 0 ∧ Z < 0)) (hpair : X + Y < 0) :
    X * Y + Y * Z + Z * X ≤ m ^ 2 := by
  rcases le_total 0 Z with hZ0 | hZ0
  · have h1 : Z * (X + Y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hZ0 hpair.le
    rcases le_total 0 X with hX0 | hX0
    · have : X * Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hX0 (by linarith)
      nlinarith
    · rcases le_total 0 Y with hY0 | hY0
      · have : X * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hX0 hY0
        nlinarith
      · have := mul_le_mul (by linarith : -X ≤ m) (by linarith : -Y ≤ m) (by linarith) (by linarith)
        nlinarith
  · -- `Z ≤ 0`; not all negative, so one of `X, Y` is `≥ 0` and the other negative.
    rcases le_total 0 X with hX0 | hX0
    · have hY0 : Y < 0 := by linarith
      have h1 : Z * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hZ0 hX0
      rcases le_total 0 (X + Z) with h | h
      · have : Y * (X + Z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hY0.le h
        nlinarith
      · have := mul_le_mul (by linarith : -Y ≤ m) (by linarith : -(X + Z) ≤ m) (by linarith)
          (by linarith)
        nlinarith
    · rcases le_total 0 Y with hY0 | hY0
      · have h1 : Y * Z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hY0 hZ0
        rcases le_total 0 (Y + Z) with h | h
        · have : X * (Y + Z) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hX0 h
          nlinarith
        · have := mul_le_mul (by linarith : -X ≤ m) (by linarith : -(Y + Z) ≤ m) (by linarith)
            (by linarith)
          nlinarith
      · -- `X, Y ≤ 0`, `Z ≤ 0`, not all `< 0`: one is `0`.
        have hm : 0 ≤ m := by linarith
        by_cases hXz : X = 0
        · subst hXz
          have := mul_le_mul (by linarith : -Y ≤ m) (by linarith : -Z ≤ m) (by linarith) hm
          nlinarith
        by_cases hYz : Y = 0
        · subst hYz
          have := mul_le_mul (by linarith : -X ≤ m) (by linarith : -Z ≤ m) (by linarith) hm
          nlinarith
        have hZz : Z = 0 := by
          by_contra hZz
          exact hnot ⟨lt_of_le_of_ne hX0 hXz, lt_of_le_of_ne hY0 hYz, lt_of_le_of_ne hZ0 hZz⟩
        subst hZz
        have := mul_le_mul (by linarith : -X ≤ m) (by linarith : -Y ≤ m) (by linarith) hm
        nlinarith

/-- Case (iv-b): a pair sum of `xm, ym, zm` in `[0, 11/20)` forces `W ≤ 13/10`. -/
lemma W_small (xm ym zm : ℝ) (hzm' : zm ≤ 11 / 5) (h0 : 0 ≤ xm + ym) (h1 : xm + ym < 11 / 20) :
    xm * ym + ym * zm + zm * xm ≤ 13 / 10 := by
  have a1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 11 / 5 - zm) h0
  have a2 := sq_nonneg (xm - ym)
  have a3 := mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 11 / 20 - (xm + ym))
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Inequality (7) of Lemma 2.2.** -/
lemma lemma22_core (m x0 y0 z0 xm ym zm X1 Y1 Z1 : ℝ) (hm : 5 ≤ m)
    (hx0 : x0 ≤ 11 / 5) (hy0 : y0 ≤ 11 / 5) (hz0 : z0 ≤ 11 / 5)
    (hxm : -1 ≤ xm) (hym : -1 ≤ ym) (hzm : -1 ≤ zm)
    (hxx : xm ≤ x0) (hyy : ym ≤ y0) (hzz : zm ≤ z0)
    (hX1l : xm - (m - 1) ≤ X1) (hY1l : ym - (m - 1) ≤ Y1) (hZ1l : zm - (m - 1) ≤ Z1)
    (hX1u : X1 ≤ m * xm) (hY1u : Y1 ≤ m * ym) (hZ1u : Z1 ≤ m * zm)
    (h8 : X1 * Y1 + Y1 * Z1 + Z1 * X1 - (xm * ym + ym * zm + zm * xm) ≤ 3 * (m ^ 2 - 1))
    (h10 : xm * ym + ym * zm + zm * xm + x0 * ym + x0 * zm + y0 * xm + y0 * zm + z0 * xm
      + z0 * ym ≤ 9)
    (hW3 : xm * ym + ym * zm + zm * xm ≤ 3) :
    ((x0 + xm) * (y0 + ym) + (y0 + ym) * (z0 + zm) + (z0 + zm) * (x0 + xm))
      + (X1 * Y1 + Y1 * Z1 + Z1 * X1) - (xm * ym + ym * zm + zm * xm) ≤ 3 * m ^ 2 + 9 := by
  have hxm' : xm ≤ 11 / 5 := by linarith
  have hym' : ym ≤ 11 / 5 := by linarith
  have hzm' : zm ≤ 11 / 5 := by linarith
  have hx0' : -1 ≤ x0 := by linarith
  have hy0' : -1 ≤ y0 := by linarith
  have hz0' : -1 ≤ z0 := by linarith
  have hm0 : 0 < m := by linarith
  have hm2 : 25 ≤ m ^ 2 := by nlinarith
  have hP0 : x0 * y0 + y0 * z0 + z0 * x0 ≤ 3 * (11 / 5) ^ 2 := by
    have := prod_le_box hx0' hx0 hy0' hy0
    have := prod_le_box hy0' hy0 hz0' hz0
    have := prod_le_box hz0' hz0 hx0' hx0
    linarith
  have h11 : (x0 + xm) * (y0 + ym) + (y0 + ym) * (z0 + zm) + (z0 + zm) * (x0 + xm)
      ≤ 9 + (x0 * y0 + y0 * z0 + z0 * x0) := by linarith
  have hUW : (x0 + xm) * (y0 + ym) + (y0 + ym) * (z0 + zm) + (z0 + zm) * (x0 + xm)
      - (xm * ym + ym * zm + zm * xm) ≤ 9 * (11 / 5) ^ 2 := by
    have := prod_le_box hx0' hx0 hy0' hy0
    have := prod_le_box hx0' hx0 hym hym'
    have := prod_le_box hxm hxm' hy0' hy0
    have := prod_le_box hy0' hy0 hz0' hz0
    have := prod_le_box hy0' hy0 hzm hzm'
    have := prod_le_box hym hym' hz0' hz0
    have := prod_le_box hz0' hz0 hx0' hx0
    have := prod_le_box hz0' hz0 hxm hxm'
    have := prod_le_box hzm hzm' hx0' hx0
    linarith
  -- Case A
  by_cases hA : (x0 + xm) + (y0 + ym) < 0 ∨ (y0 + ym) + (z0 + zm) < 0 ∨ (z0 + zm) + (x0 + xm) < 0
  · have hU12 : (x0 + xm) * (y0 + ym) + (y0 + ym) * (z0 + zm) + (z0 + zm) * (x0 + xm) ≤ 12 := by
      rcases hA with h | h | h
      · exact U_caseA (by linarith) (by linarith) (by linarith) h
      · have := U_caseA (r := y0 + ym) (s := z0 + zm) (t := x0 + xm)
          (by linarith) (by linarith) (by linarith) h
        linarith
      · have := U_caseA (r := z0 + zm) (s := x0 + xm) (t := y0 + ym)
          (by linarith) (by linarith) (by linarith) h
        linarith
    linarith
  push Not at hA
  obtain ⟨hrs, hst, htr⟩ := hA
  have hXl : -m ≤ X1 := by linarith
  have hYl : -m ≤ Y1 := by linarith
  have hZl : -m ≤ Z1 := by linarith
  by_cases hneg3 : X1 < 0 ∧ Y1 < 0 ∧ Z1 < 0
  · obtain ⟨hX, hY, hZ⟩ := hneg3
    have e1 := sym_step_down (X := X1) (X' := xm - (m - 1)) (Y := Y1) (Z := Z1) hX1l (by linarith)
    have e2 := sym_step_down (X := Y1) (X' := ym - (m - 1)) (Y := Z1) (Z := xm - (m - 1))
      hY1l (by linarith)
    have e3 := sym_step_down (X := Z1) (X' := zm - (m - 1)) (Y := xm - (m - 1))
      (Z := ym - (m - 1)) hZ1l (by linarith)
    have f1 := sym_step_up (X := x0 + xm) (X' := 11 / 5 + xm) (Y := y0 + ym) (Z := z0 + zm)
      (by linarith) hst
    have f2 := sym_step_up (X := y0 + ym) (X' := 11 / 5 + ym) (Y := z0 + zm) (Z := 11 / 5 + xm)
      (by linarith) (by linarith)
    have f3 := sym_step_up (X := z0 + zm) (X' := 11 / 5 + zm) (Y := 11 / 5 + xm)
      (Z := 11 / 5 + ym) (by linarith) (by linarith)
    have fin := case_i_final xm ym zm (m - 1) hxm hym hzm hxm' hym' hzm' (by linarith)
    have e : 3 * (m - 1 + 1) ^ 2 + 9 = 3 * m ^ 2 + 9 := by ring
    linarith
  by_cases hneg2 : X1 + Y1 < 0 ∨ Y1 + Z1 < 0 ∨ Z1 + X1 < 0
  · have hVm : X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 := by
      rcases hneg2 with h | h | h
      · exact V_le_sq X1 Y1 Z1 m hXl hYl hZl hneg3 h
      · have := V_le_sq Y1 Z1 X1 m hYl hZl hXl (fun ⟨a, b, c⟩ => hneg3 ⟨c, a, b⟩) h
        linarith
      · have := V_le_sq Z1 X1 Y1 m hZl hXl hYl (fun ⟨a, b, c⟩ => hneg3 ⟨b, c, a⟩) h
        linarith
    nlinarith
  push Not at hneg2
  obtain ⟨hXY, hYZ, hZX⟩ := hneg2
  have g1 := sym_step_up (X := X1) (X' := m * xm) (Y := Y1) (Z := Z1) hX1u hYZ
  have g2 := sym_step_up (X := Y1) (X' := m * ym) (Y := Z1) (Z := m * xm) hY1u (by linarith)
  have g3 := sym_step_up (X := Z1) (X' := m * zm) (Y := m * xm) (Z := m * ym) hZ1u
    (by nlinarith)
  have hVW : X1 * Y1 + Y1 * Z1 + Z1 * X1 ≤ m ^ 2 * (xm * ym + ym * zm + zm * xm) := by
    have e : m * xm * (m * ym) + m * ym * (m * zm) + m * zm * (m * xm)
        = m ^ 2 * (xm * ym + ym * zm + zm * xm) := by ring
    linarith
  have pos : ∀ a b : ℝ, 0 ≤ m * a + m * b → 0 ≤ a + b := fun a b h => by
    by_contra hc; push Not at hc
    have := mul_neg_of_pos_of_neg hm0 hc; linarith
  have hxy : 0 ≤ xm + ym := pos xm ym (by linarith)
  have hyz : 0 ≤ ym + zm := pos ym zm (by linarith)
  have hzx : 0 ≤ zm + xm := pos zm xm (by linarith)
  set W := xm * ym + ym * zm + zm * xm with hW
  by_cases hbig : 11 / 20 ≤ xm + ym ∧ 11 / 20 ≤ ym + zm ∧ 11 / 20 ≤ zm + xm
  · obtain ⟨b1, b2, b3⟩ := hbig
    have c1 : (x0 + y0 - 8 * (xm + ym)) * (z0 - zm) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have c2 : (y0 + z0 - 8 * (ym + zm)) * (x0 - xm) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have c3 : (z0 + x0 - 8 * (zm + xm)) * (y0 - ym) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h12 : 2 * (x0 * y0 + y0 * z0 + z0 * x0) + 25 * W ≤ 81 := by rw [hW]; linarith
    have hk := mul_nonneg (by linarith : (0 : ℝ) ≤ m ^ 2 - 27 / 2) (by linarith : (0 : ℝ) ≤ 3 - W)
    nlinarith
  · have hW13 : W ≤ 13 / 10 := by
      push Not at hbig
      by_cases h1 : 11 / 20 ≤ xm + ym
      · by_cases h2 : 11 / 20 ≤ ym + zm
        · have h3 := hbig h1 h2
          have := W_small zm xm ym hym' hzx h3
          rw [hW]; linarith
        · push Not at h2
          have := W_small ym zm xm hxm' hyz h2
          rw [hW]; linarith
      · push Not at h1
        exact W_small xm ym zm hzm' hxy h1
    have hk := mul_nonneg (by linarith : (0 : ℝ) ≤ m ^ 2 - 1) (by linarith : (0 : ℝ) ≤ 13 / 10 - W)
    nlinarith

end LeanLab.DensityGoldbach
