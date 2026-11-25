import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left

/-!
# Feed 1122, third split of `Burst9Matrix.entry_5_0`: `leaf_sigma_left` cut into eight panels

Source: Wu 2004, arXiv 0705.1652, display 7.2, the `sigma0` term of the kernel Xi1 of
display 3.21, page 14, row 6 of Table 1. The leaf `leaf_sigma_left` bounds the integral of
`sigma0 t/(2t)` over the left half panel `[1, 8/5]` from below by `0.0021039266`, against the true
value `0.0021039356802`, a margin of `9.08e-9`. Here `[1, 8/5]` is cut into eight sub-intervals of
width `3/40`, each a LEAF with its own lower bound, and `leaf_sigma_left_split` proves the stated
bound of `leaf_sigma_left` from the eight LEAFs by additivity of the interval integral over
adjacent intervals. The margin is shared out in proportion to the plain midpoint error of five
sub-panels on each piece, so that the pieces near `t = 1`, where `sigma0` bends most, get most of
it. The eight lower bounds sum to `0.0021039266` plus `2.7e-10`.
All values are from mpmath quadrature at 30 digits. AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p3_sigma

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_left

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 0 of the left half panel: `∫ sigma0 t/(2t)` over `[1, 43/40]`. High precision
quadrature gives `0.0000065356800320`, so the stated bound leaves about `2.7e-09`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. HARD. -/
theorem leaf_sigma_p0 :
    (653296030/100000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(43/40 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 1 of the left half panel: `∫ sigma0 t/(2t)` over `[43/40, 23/20]`. High precision
quadrature gives `0.0000419604214708`, so the stated bound leaves about `2e-09`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p1 :
    (4195845371/100000000000000 : ℝ) ≤ ∫ t in (43/40 : ℝ)..(23/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 2 of the left half panel: `∫ sigma0 t/(2t)` over `[23/20, 49/40]`. High precision
quadrature gives `0.0001038462989294`, so the stated bound leaves about `1.4e-09`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p2 :
    (10384488052/100000000000000 : ℝ) ≤ ∫ t in (23/20 : ℝ)..(49/40 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 3 of the left half panel: `∫ sigma0 t/(2t)` over `[49/40, 13/10]`. High precision
quadrature gives `0.0001848200096268`, so the stated bound leaves about `1e-09`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p3 :
    (18481899648/100000000000000 : ℝ) ≤ ∫ t in (49/40 : ℝ)..(13/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 4 of the left half panel: `∫ sigma0 t/(2t)` over `[13/10, 11/8]`. High precision
quadrature gives `0.0002794385186267`, so the stated bound leaves about `7.1e-10`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p4 :
    (27943780717/100000000000000 : ℝ) ≤ ∫ t in (13/10 : ℝ)..(11/8 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 5 of the left half panel: `∫ sigma0 t/(2t)` over `[11/8, 29/20]`. High precision
quadrature gives `0.0003836411585928`, so the stated bound leaves about `4.9e-10`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p5 :
    (38364067228/100000000000000 : ℝ) ≤ ∫ t in (11/8 : ℝ)..(29/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 6 of the left half panel: `∫ sigma0 t/(2t)` over `[29/20, 61/40]`. High precision
quadrature gives `0.0004943729543928`, so the stated bound leaves about `3.1e-10`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p6 :
    (49437264369/100000000000000 : ℝ) ≤ ∫ t in (29/20 : ℝ)..(61/40 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- LEAF: Wu 2004 display 7.2, the `sigma0` term of the kernel Xi1 of display 3.21, page 14,
row 6, panel 7 of the left half panel: `∫ sigma0 t/(2t)` over `[61/40, 8/5]`. High precision
quadrature gives `0.0006093206385319`, so the stated bound leaves about `1.8e-10`. Certified midpoint
panels with the second derivative correction `sigma0_mid_panel` of the kit, at width `3/200` or
finer, are the expected route. MEDIUM. -/
theorem leaf_sigma_p7 :
    (60932045841/100000000000000 : ℝ) ≤ ∫ t in (61/40 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  sorry

/-- The stated bound of `leaf_sigma_left` from the eight panel LEAFs, by additivity of the
integral over adjacent intervals. -/
theorem leaf_sigma_left_split :
    (0.0021039266 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hi0 := sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (43/40 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi1 := sigma0_div_two_integrable_Icc (a := (43/40 : ℝ)) (b := (23/20 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi2 := sigma0_div_two_integrable_Icc (a := (23/20 : ℝ)) (b := (49/40 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi3 := sigma0_div_two_integrable_Icc (a := (49/40 : ℝ)) (b := (13/10 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi4 := sigma0_div_two_integrable_Icc (a := (13/10 : ℝ)) (b := (11/8 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi5 := sigma0_div_two_integrable_Icc (a := (11/8 : ℝ)) (b := (29/20 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi6 := sigma0_div_two_integrable_Icc (a := (29/20 : ℝ)) (b := (61/40 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have hi7 := sigma0_div_two_integrable_Icc (a := (61/40 : ℝ)) (b := (8/5 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num)
  have j1 := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have j2 := intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi1) hi2
  have j3 := intervalIntegral.integral_add_adjacent_intervals ((hi0.trans hi1).trans hi2) hi3
  have j4 := intervalIntegral.integral_add_adjacent_intervals (((hi0.trans hi1).trans hi2).trans hi3) hi4
  have j5 := intervalIntegral.integral_add_adjacent_intervals ((((hi0.trans hi1).trans hi2).trans hi3).trans hi4) hi5
  have j6 := intervalIntegral.integral_add_adjacent_intervals (((((hi0.trans hi1).trans hi2).trans hi3).trans hi4).trans hi5) hi6
  have j7 := intervalIntegral.integral_add_adjacent_intervals ((((((hi0.trans hi1).trans hi2).trans hi3).trans hi4).trans hi5).trans hi6) hi7
  have l0 := leaf_sigma_p0
  have l1 := leaf_sigma_p1
  have l2 := leaf_sigma_p2
  have l3 := leaf_sigma_p3
  have l4 := leaf_sigma_p4
  have l5 := leaf_sigma_p5
  have l6 := leaf_sigma_p6
  have l7 := leaf_sigma_p7
  linarith [j1, j2, j3, j4, j5, j6, j7, l0, l1, l2, l3, l4, l5, l6, l7]


/-- `leaf_sigma_left` holds by its split. -/
example : (0.0021039266 : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) :=
  leaf_sigma_left_split

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p3_sigma
