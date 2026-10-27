/-
P0085 Alsetri 2025, arXiv 2505.09648, Lemma 2.2 (the 1/2 analogue of Shao's Lemma 2.2), the
real inequality `U + V - W ≤ 3m² + 9` after the substitution `x = 4a - 1` (values in `[-1, 3]`)
and the block summations. Follows the paper's four cases; the paper's final constant `49.5`
in Case 4 should read `58.5`, which still gives `3m² + 9`.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.Lemma22Core

namespace LeanLab.DensityGoldbach

lemma box3 {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 3) (hb : -1 ≤ b) (hb' : b ≤ 3) :
    a * b ≤ 9 := by
  rcases le_total 0 a with h | h <;> rcases le_total 0 b with h' | h' <;> nlinarith

lemma box3_lo {a b : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 3) (hb : -1 ≤ b) (hb' : b ≤ 3) :
    -3 ≤ a * b := by
  rcases le_total 0 a with h | h <;> rcases le_total 0 b with h' | h' <;> nlinarith

/-- Case 1, final arithmetic, `x ∈ [-1, 3]`, `L ≥ 4`. -/
lemma half_case_i_final (xm ym zm L : ℝ) (hxm : -1 ≤ xm) (hym : -1 ≤ ym) (hzm : -1 ≤ zm)
    (hxm' : xm ≤ 3) (hym' : ym ≤ 3) (hzm' : zm ≤ 3) (hL : 4 ≤ L) :
    ((3 + xm) * (3 + ym) + (3 + ym) * (3 + zm) + (3 + zm) * (3 + xm))
      + ((xm - L) * (ym - L) + (ym - L) * (zm - L) + (zm - L) * (xm - L))
      - (xm * ym + ym * zm + zm * xm) ≤ 3 * (L + 1) ^ 2 + 9 := by
  have hv1 : (xm + 1) * (ym + 1) ≤ 2 * ((xm + 1) + (ym + 1)) := by
    rcases le_total xm ym with h | h <;> nlinarith
  have hv2 : (ym + 1) * (zm + 1) ≤ 2 * ((ym + 1) + (zm + 1)) := by
    rcases le_total ym zm with h | h <;> nlinarith
  have hv3 : (zm + 1) * (xm + 1) ≤ 2 * ((zm + 1) + (xm + 1)) := by
    rcases le_total zm xm with h | h <;> nlinarith
  have hc := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * L - 8)
    (by linarith : (0 : ℝ) ≤ (xm + 1) + (ym + 1) + (zm + 1))
  nlinarith

/-- Case 4b: a pair sum of `xm, ym, zm` in `[0, 3/5)` forces `W ≤ 2`. -/
lemma half_W_small (xm ym zm : ℝ) (hzm' : zm ≤ 3) (h0 : 0 ≤ xm + ym) (h1 : xm + ym < 3 / 5) :
    xm * ym + ym * zm + zm * xm ≤ 2 := by
  have a1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - zm) h0
  have a2 := sq_nonneg (xm - ym)
  have a3 := mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 3 / 5 - (xm + ym))
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Inequality (7) of Alsetri's Lemma 2.2**, values in `[-1, 3]`. -/
lemma half_lemma22_core (m x0 y0 z0 xm ym zm X1 Y1 Z1 : ℝ) (hm : 5 ≤ m)
    (hx0 : x0 ≤ 3) (hy0 : y0 ≤ 3) (hz0 : z0 ≤ 3)
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
  have hxm' : xm ≤ 3 := by linarith
  have hym' : ym ≤ 3 := by linarith
  have hzm' : zm ≤ 3 := by linarith
  have hx0' : -1 ≤ x0 := by linarith
  have hy0' : -1 ≤ y0 := by linarith
  have hz0' : -1 ≤ z0 := by linarith
  have hm0 : 0 < m := by linarith
  have hm2 : 25 ≤ m ^ 2 := by nlinarith
  have hP0 : x0 * y0 + y0 * z0 + z0 * x0 ≤ 27 := by
    have := box3 hx0' hx0 hy0' hy0
    have := box3 hy0' hy0 hz0' hz0
    have := box3 hz0' hz0 hx0' hx0
    linarith
  have hWlo : -9 ≤ xm * ym + ym * zm + zm * xm := by
    have := box3_lo hxm hxm' hym hym'
    have := box3_lo hym hym' hzm hzm'
    have := box3_lo hzm hzm' hxm hxm'
    linarith
  have h11 : (x0 + xm) * (y0 + ym) + (y0 + ym) * (z0 + zm) + (z0 + zm) * (x0 + xm)
      ≤ 9 + (x0 * y0 + y0 * z0 + z0 * x0) := by linarith
  have hUW : (x0 + xm) * (y0 + ym) + (y0 + ym) * (z0 + zm) + (z0 + zm) * (x0 + xm)
      - (xm * ym + ym * zm + zm * xm) ≤ 45 := by linarith
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
    have f1 := sym_step_up (X := x0 + xm) (X' := 3 + xm) (Y := y0 + ym) (Z := z0 + zm)
      (by linarith) hst
    have f2 := sym_step_up (X := y0 + ym) (X' := 3 + ym) (Y := z0 + zm) (Z := 3 + xm)
      (by linarith) (by linarith)
    have f3 := sym_step_up (X := z0 + zm) (X' := 3 + zm) (Y := 3 + xm)
      (Z := 3 + ym) (by linarith) (by linarith)
    have fin := half_case_i_final xm ym zm (m - 1) hxm hym hzm hxm' hym' hzm' (by linarith)
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
  by_cases hbig : 3 / 5 ≤ xm + ym ∧ 3 / 5 ≤ ym + zm ∧ 3 / 5 ≤ zm + xm
  · obtain ⟨b1, b2, b3⟩ := hbig
    have c1 : (x0 + y0 - 10 * (xm + ym)) * (z0 - zm) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have c2 : (y0 + z0 - 10 * (ym + zm)) * (x0 - xm) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have c3 : (z0 + x0 - 10 * (zm + xm)) * (y0 - ym) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h12 : 2 * (x0 * y0 + y0 * z0 + z0 * x0) + 31 * W ≤ 99 := by rw [hW]; linarith
    have hk := mul_nonneg (by linarith : (0 : ℝ) ≤ m ^ 2 - 33 / 2) (by linarith : (0 : ℝ) ≤ 3 - W)
    nlinarith
  · have hW2 : W ≤ 2 := by
      push Not at hbig
      by_cases h1 : 3 / 5 ≤ xm + ym
      · by_cases h2 : 3 / 5 ≤ ym + zm
        · have h3 := hbig h1 h2
          have := half_W_small zm xm ym hym' hzx h3
          rw [hW]; linarith
        · push Not at h2
          have := half_W_small ym zm xm hxm' hyz h2
          rw [hW]; linarith
      · push Not at h1
        exact half_W_small xm ym zm hzm' hxy h1
    have hk := mul_nonneg (by linarith : (0 : ℝ) ≤ m ^ 2 - 1) (by linarith : (0 : ℝ) ≤ 2 - W)
    nlinarith

end LeanLab.DensityGoldbach
