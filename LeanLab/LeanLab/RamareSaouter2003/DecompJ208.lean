import Mathlib
import LeanLab.RamareSaouter2003.Theorem4Parts

namespace LeanLab.RamareSaouter2003.DecompJ208
open Real Chebyshev Finset LeanLab.RamareSaouter2003.Thm4Parts

/-- LEAF. p. 16. Y bound. -/
theorem lemma5_Y_bound {X δ t Y : ℝ} (hXpos : 0 < X) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 0.0001) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hYdef : Y = X * (1 + δ * t)) :
    X ≤ Y ∧ Y ≤ 1.0001 * X := by
  have hdt0 : 0 ≤ δ * t := mul_nonneg hδ0 ht0
  have hdt1 : δ * t ≤ 0.0001 := by nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- LEAF. p. 16. E bound. -/
theorem lemma5_E_bound {u E : ℝ} (hu0 : 0 < u) (hu : u ≤ 0.0001) (hEdef : E = Real.exp u - 1) :
    u ≤ E ∧ E ≤ 1.000075 * u := by
  have hE1 : u ≤ E := by
    have := Real.add_one_le_exp u
    linarith
  have hE2 : E ≤ u + 0.75 * u ^ 2 := by
    have := exp_sub_one_le hu0.le (by linarith : u ≤ 1)
    linarith
  constructor
  · exact hE1
  · nlinarith

/-- LEAF. p. 16. y lower bound. -/
theorem lemma5_y_lower {X u Y E y : ℝ} (hu0 : 0 < u) (huX : 1 < u * X) (hXpos : 0 < X) (hY1 : X ≤ Y) (hE1 : u ≤ E) (hydef : y = Y * E) :
    1 < y := by
  have hE0 : 0 ≤ E := by linarith
  have h : u * X ≤ Y * E := by
    calc u * X ≤ E * X := mul_le_mul_of_nonneg_right hE1 hXpos.le
      _ ≤ E * Y := mul_le_mul_of_nonneg_left hY1 hE0
      _ = Y * E := mul_comm _ _
  linarith

/-- LEAF. p. 16. log sum equality. -/
theorem lemma5_logYE {X u δ t Y : ℝ} (hYdef : Y = X * (1 + δ * t)) (hYpos : 0 < Y) :
    Real.log (X * Real.exp u * (1 + δ * t)) = Real.log Y + u := by
  have hYpos_exp : 0 < Y * Real.exp u := mul_pos hYpos (Real.exp_pos u)
  calc Real.log (X * Real.exp u * (1 + δ * t))
    _ = Real.log (X * (1 + δ * t) * Real.exp u) := by ring_nf
    _ = Real.log (Y * Real.exp u) := by rw [← hYdef]
    _ = Real.log Y + Real.log (Real.exp u) := Real.log_mul hYpos.ne' (Real.exp_pos u).ne'
    _ = Real.log Y + u := by rw [Real.log_exp]

/-- LEAF. p. 16. theta sub step 1. -/
theorem lemma5_step1 (hMV : MVBrunTitchmarsh) {X u δ t Y E y LY : ℝ}
    (hX : 10 ^ 12 ≤ X) (hYdef : Y = X * (1 + δ * t)) (hYpos : 0 < Y) (hEdef : E = Real.exp u - 1) (hydef : y = Y * E)
    (hy1 : 1 < y) (hLY : LY = Real.log Y) (hlogYE : Real.log (X * Real.exp u * (1 + δ * t)) = LY + u) (hu0 : 0 < u) (hδ0 : 0 ≤ δ) (ht0 : 0 ≤ t) :
    θ (X * Real.exp u * (1 + δ * t)) - θ Y ≤ 2 * y / Real.log y * (LY + u) := by
  have hcount := hMV Y y hYpos hy1
  have hth := theta_sub_le (x := Y) (z := Y + y) (by linarith) (by linarith)
  have hYy : Y + y = X * Real.exp u * (1 + δ * t) := by
    simp only [hydef, hEdef, hYdef]; ring
  rw [hYy] at hth hcount
  rw [hlogYE] at hth
  have hLYu : 0 ≤ LY + u := by
    have hl1 : 5 ≤ Real.log X := log_ge_five hX
    have hXpos : 0 < X := by linarith
    have hdt0 : 0 ≤ δ * t := mul_nonneg hδ0 ht0
    have hYpos2 : X ≤ Y := by nlinarith
    have hlog_mono : Real.log X ≤ Real.log Y := Real.log_le_log hXpos hYpos2
    linarith
  calc _ ≤ _ := hth
    _ ≤ 2 * y / Real.log y * (LY + u) := mul_le_mul_of_nonneg_right hcount.le hLYu

/-- LEAF. p. 16. step 2 algebra. -/
theorem lemma5_step2 {y L l LY E u : ℝ}
    (hlogy' : Real.log y = LY + Real.log E) (hL4 : 5 ≤ L)
    (hLuXpos : 0 < l + L) (hLYL : L ≤ LY) (hlE : l ≤ Real.log E) (hlneg : l < 0) (hu0 : 0 < u) (hy1 : 1 < y):
    2 * y / Real.log y * (LY + u) ≤ 2 * y * (L + u) / (l + L) := by
  rw [hlogy']
  have hden1 : 0 < LY + l := by linarith
  have hden2 : 0 < LY + Real.log E := by linarith
  have hy0 : 0 < y := by linarith
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hden2 hLuXpos]
  have key : (LY + u) * (l + L) ≤ (L + u) * (LY + Real.log E) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hLYL) (show 0 ≤ u - l by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left key (show 0 ≤ 2 * y by linarith)]

/-- LEAF. p. 16. step 3 bound. -/
theorem lemma5_step3 {X Y u E y L : ℝ} (hXpos : 0 < X)
    (hu0 : 0 < u) (hY1 : X ≤ Y) (hY2 : Y ≤ 1.0001 * X) (hE3 : E ≤ 1.000075 * u)
    (hydef : y = Y * E) (_hL : L = Real.log X) (hL4 : 5 ≤ L) (hu : u ≤ 0.0001) (hE1 : u ≤ E) (hy1 : 1 < y):
    2 * y * (L + u) ≤ 2.0004 * u * X * L := by
  have hEpos : 0 < E := by linarith
  have hYpos : 0 < Y := by linarith
  have h1 : y ≤ 1.0001 * X * (1.000075 * u) := by
    simp only [hydef]
    exact mul_le_mul hY2 hE3 hEpos.le (by positivity)
  have h2 : L + u ≤ 1.00002 * L := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hL0 : 0 ≤ L := by linarith
  calc 2 * y * (L + u) ≤ 2 * y * (1.00002 * L) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ ≤ 2 * (1.0001 * X * (1.000075 * u)) * (1.00002 * L) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    _ = 2.0003900220003 * (u * X * L) := by ring
    _ ≤ 2.0004 * u * X * L := by
        have : 0 ≤ u * X * L := by positivity
        linarith

/-- **Lemma 5 of Ramaré-Saouter 2003**, as printed on p. 16, plus the hypothesis `1 < u X`
which the printed statement lacks but needs. PROVED CONDITIONAL ON `MVBrunTitchmarsh`. -/
theorem lemma5 (hMV : MVBrunTitchmarsh) {X u δ t : ℝ} (hX : 10 ^ 12 ≤ X) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 0.0001) (hu0 : 0 < u) (hu : u ≤ 0.0001) (huX : 1 < u * X)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    θ (X * Real.exp u * (1 + δ * t)) - θ (X * (1 + δ * t)) ≤
      2.0004 * u * X * (Real.log X / Real.log (u * X)) := by
  set Y := X * (1 + δ * t) with hYdef
  set E := Real.exp u - 1 with hEdef
  set y := Y * E with hydef
  have hXpos : 0 < X := by linarith
  have hYbounds := lemma5_Y_bound hXpos hδ0 hδ ht0 ht1 hYdef
  have hY1 : X ≤ Y := hYbounds.1
  have hY2 : Y ≤ 1.0001 * X := hYbounds.2
  have hYpos : 0 < Y := by linarith
  have hEbounds := lemma5_E_bound hu0 hu hEdef
  have hE1 : u ≤ E := hEbounds.1
  have hE3 : E ≤ 1.000075 * u := hEbounds.2
  have hy1 : 1 < y := lemma5_y_lower hu0 huX hXpos hY1 hE1 hydef
  have hlogYE := lemma5_logYE (X := X) (u := u) (δ := δ) (t := t) (Y := Y) hYdef hYpos
  set L := Real.log X with hL
  set l := Real.log u with hl
  set LY := Real.log Y with hLY
  have hstep1 := lemma5_step1 hMV hX hYdef hYpos hEdef hydef hy1 hLY hlogYE hu0 hδ0 ht0
  have hL4 : 5 ≤ L := log_ge_five hX
  have hLuX : Real.log (u * X) = l + L := Real.log_mul hu0.ne' hXpos.ne'
  have hLuXpos : 0 < l + L := by rw [← hLuX]; exact Real.log_pos huX
  have hLYL : L ≤ LY := Real.log_le_log hXpos hY1
  have hlogy' : Real.log y = LY + Real.log E := Real.log_mul hYpos.ne' (by linarith : (0:ℝ) < E).ne'
  have hlE : l ≤ Real.log E := Real.log_le_log hu0 hE1
  have hlneg : l < 0 := Real.log_neg hu0 (by linarith)
  have hstep2 := lemma5_step2 (u := u) hlogy' hL4 hLuXpos hLYL hlE hlneg hu0 hy1
  have hstep3 := lemma5_step3 hXpos hu0 hY1 hY2 hE3 hydef hL hL4 hu hE1 hy1
  calc θ (X * Real.exp u * (1 + δ * t)) - θ (X * (1 + δ * t)) ≤ 2 * y * (L + u) / (l + L) := hstep1.trans hstep2
    _ ≤ 2.0004 * u * X * L / (l + L) := div_le_div_of_nonneg_right hstep3 hLuXpos.le
    _ = 2.0004 * u * X * (L / Real.log (u * X)) := by rw [hLuX]; ring

end LeanLab.RamareSaouter2003.DecompJ208
