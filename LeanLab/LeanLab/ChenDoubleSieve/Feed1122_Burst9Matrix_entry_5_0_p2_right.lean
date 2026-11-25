import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan20
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan21
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan22
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan23
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan24
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan25
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan26
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan27
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan28
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan29
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan30
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan31
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan32
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan33
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan34
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan35
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan36
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan37
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan38
import LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan39

/-!
# Feed 1122, second split of `Burst9Matrix.entry_5_0`: the right half panel

Source: Wu 2004, arXiv 0705.1652, display 7.2, kernel Xi1 of display 3.21, page 14, row 6 of
Table 1, so `s = 27/10` and `sp = 347/100`. On the right half panel `[8/5, 11/5]` the kernel is
the `sigma0` term with weight `log (16000/4199)` plus the `(t+1)^2` window, since
`sp - 2 = 147/100 < 8/5`. The `sigma0` part reuses the twenty certified midpoint panels
`b9_pan_20` to `b9_pan_39` of `Burst9MatrixCol0`, in the verbatim copies `_p2_pan20` to `_p2_pan39`, and the window
part is the `log (t+1)` series at the midpoint `19/10` with twelve terms.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_right

open Real Set MeasureTheory intervalIntegral
open LeanLab.ChenDoubleSieve.Wu04Table LeanLab.ChenDoubleSieve.Wu04Functional

open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan20
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan21
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan22
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan23
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan24
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan25
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan26
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan27
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan28
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan29
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan30
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan31
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan32
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan33
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan34
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan35
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan36
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan37
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan38
open LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_pan39

set_option maxHeartbeats 4000000 in
/-- `∫ sigma0 t/(2t)` on `[8/5, 11/5]`, the sum of the twenty midpoint panels 20 to 39. -/
theorem r5_I_sigma_right : (909201015164161089/100000000000000000000 : ℝ) ≤ (∫ t in (8/5 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
  have e21 : (∫ t in (8/5 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(163/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (163/100 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (163/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (163/100 : ℝ)) (b := (83/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e22 : (∫ t in (8/5 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (83/50 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (83/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (83/50 : ℝ)) (b := (169/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e23 : (∫ t in (8/5 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (169/100 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (169/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (169/100 : ℝ)) (b := (43/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e24 : (∫ t in (8/5 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (43/25 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (43/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (43/25 : ℝ)) (b := (7/4 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e25 : (∫ t in (8/5 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (7/4 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (7/4 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (7/4 : ℝ)) (b := (89/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e26 : (∫ t in (8/5 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (89/50 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (89/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (89/50 : ℝ)) (b := (181/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e27 : (∫ t in (8/5 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (181/100 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (181/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (181/100 : ℝ)) (b := (46/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e28 : (∫ t in (8/5 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (46/25 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (46/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (46/25 : ℝ)) (b := (187/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e29 : (∫ t in (8/5 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (187/100 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (187/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (187/100 : ℝ)) (b := (19/10 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e30 : (∫ t in (8/5 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (19/10 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (19/10 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (19/10 : ℝ)) (b := (193/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e31 : (∫ t in (8/5 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (193/100 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (193/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (193/100 : ℝ)) (b := (49/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e32 : (∫ t in (8/5 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (49/25 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (49/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (49/25 : ℝ)) (b := (199/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e33 : (∫ t in (8/5 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (199/100 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (199/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (199/100 : ℝ)) (b := (101/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e34 : (∫ t in (8/5 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (101/50 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (101/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (101/50 : ℝ)) (b := (41/20 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e35 : (∫ t in (8/5 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (41/20 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (41/20 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (41/20 : ℝ)) (b := (52/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e36 : (∫ t in (8/5 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (52/25 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (52/25 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (52/25 : ℝ)) (b := (211/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e37 : (∫ t in (8/5 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (211/100 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (211/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (211/100 : ℝ)) (b := (107/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e38 : (∫ t in (8/5 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (107/50 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (107/50 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (107/50 : ℝ)) (b := (217/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  have e39 : (∫ t in (8/5 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) = (∫ t in (8/5 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (217/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals (sigma0_div_two_integrable_Icc (a := (8/5 : ℝ)) (b := (217/100 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (a := (217/100 : ℝ)) (b := (11/5 : ℝ)) (by norm_num) (by norm_num) (by norm_num))).symm
  linarith [b9_pan_20, b9_pan_21, b9_pan_22, b9_pan_23, b9_pan_24, b9_pan_25, b9_pan_26, b9_pan_27, b9_pan_28, b9_pan_29, b9_pan_30, b9_pan_31, b9_pan_32, b9_pan_33, b9_pan_34, b9_pan_35, b9_pan_36, b9_pan_37, b9_pan_38, b9_pan_39, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31, e32, e33, e34, e35, e36, e37, e38, e39]

/-- `log (29/20)` two-sided, `x = 9/49`, ten terms. -/
theorem r5_log_29_20 : (0.37156355643248 : ℝ) ≤ log (29/20 : ℝ) ∧ log (29/20 : ℝ) ≤ (0.37156355643249 : ℝ) := by
  have h := log_enclosure (y := (29/20 : ℝ)) (x := (9/49 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (11/8)` two-sided, `x = 3/19`, ten terms. -/
theorem r5_log_11_8 : (0.31845373111853 : ℝ) ≤ log (11/8 : ℝ) ∧ log (11/8 : ℝ) ≤ (0.31845373111854 : ℝ) := by
  have h := log_enclosure (y := (11/8 : ℝ)) (x := (3/19 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (4199/4000)` two-sided, `x = 199/8199`, five terms. -/
theorem r5_log_4199_4000 : (0.04855204058216 : ℝ) ≤ log (4199/4000 : ℝ) ∧ log (4199/4000 : ℝ) ≤ (0.04855204058217 : ℝ) := by
  have h := log_enclosure (y := (4199/4000 : ℝ)) (x := (199/8199 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 5
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log 4 = 2 log 2`. -/
theorem r5_log_four : log (4 : ℝ) = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- The weight of the `sigma0` term: `log (16000/4199) = log 4 - log (4199/4000)`. -/
theorem r5_log_c : log (16000/4199 : ℝ) = 2 * log 2 - log (4199/4000) := by
  rw [show (16000/4199 : ℝ) = 4 / (4199/4000) by norm_num, Real.log_div (by norm_num) (by norm_num),
    r5_log_four]

/-- `log (4199/1000) = log 4 + log (4199/4000)`. -/
theorem r5_log_P : log (4199/1000 : ℝ) = 2 * log 2 + log (4199/4000) := by
  rw [show (4199/1000 : ℝ) = 4 * (4199/4000) by norm_num, Real.log_mul (by norm_num) (by norm_num),
    r5_log_four]

/-- `log (29/10) = log 2 + log (29/20)`. -/
theorem r5_log_29_10 : log (29/10 : ℝ) = log 2 + log (29/20) := by
  rw [show (29/10 : ℝ) = 2 * (29/20) by norm_num, Real.log_mul (by norm_num) (by norm_num)]

set_option maxHeartbeats 2000000 in
/-- `∫_{8/5}^{11/5} log (t+1)/t`, from the `log (t+1)` series at `19/10` with twelve terms,
radius `3/29`. -/
theorem r5_L_lower :
    (0.33673812667 : ℝ) ≤ ∫ t in (8/5 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (8/5 : ℝ) (11/5), |(19/10 - t) / (19/10 + 1)| ≤ 3/29 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(19/10 : ℝ) - t| ≤ 3/10 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (19/10 : ℝ) + 1 = 29/10 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 19/10 + 1), hden]
    have h3 : |(19/10 : ℝ) - t| / (29/10) ≤ (3/10) / (29/10) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (3/10 : ℝ) / (29/10) = 3/29 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := 8/5) (b := 11/5) (c := 19/10) (r := 3/29)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 12
  simp only [Finset.sum_range_succ] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (8/5 : ℝ)..(11/5 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (8/5 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have h2lo : (0.69314718055 : ℝ) ≤ log 2 := log_two_bounds.1
  have h2hi : log 2 ≤ (0.69314718056 : ℝ) := log_two_bounds.2
  have hl := r5_log_11_8
  have h29 := r5_log_29_20
  have h2910lo : (0.69314718055 + 0.37156355643248 : ℝ) ≤ log (29/10) := by
    rw [r5_log_29_10]; linarith [h29.1]
  have hprod : ((0.69314718055 + 0.37156355643248 : ℝ) * 0.31845373111853) ≤
      log (29/10) * log (11/8) := by
    refine mul_le_mul h2910lo hl.1 (by norm_num) ?_
    linarith [h2910lo]
  linarith [h, hprod, hl.1, hl.2]

/-- The `(t+1)^2` window on `[8/5, 11/5]`, split into `log (t+1)` and `log (4199/1000)`. -/
theorem r5_J2_eq :
    (∫ t in (8/5 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (4199/1000)) / (2 * t)) =
      (∫ t in (8/5 : ℝ)..(11/5 : ℝ), log (t + 1) / t) -
        (1/2) * log (4199/1000) * log (11/8) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (8/5 : ℝ) (11/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (8/5 : ℝ) (11/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (8/5 : ℝ) (11/5),
      log ((t + 1) ^ 2 / (4199/1000)) / (2 * t) =
        log (t + 1) / t - (1/2) * log (4199/1000) * (1 / t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have hnum : ((t + 1) ^ 2 : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hnum (by norm_num : (4199/1000 : ℝ) ≠ 0), Real.log_pow]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub hI1 (hI2.const_mul (1/2 * log (4199/1000)))]
  rw [intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((11/5 : ℝ) / (8/5)) = (11/8 : ℝ) by norm_num]

/-- On `(8/5, 11/5)` the row-6 kernel is the `sigma0` term plus the `(t+1)^2` window. -/
theorem r5_xi1_right {t : ℝ} (ht : t ∈ Set.uIoo (8/5 : ℝ) (11/5)) :
    Wu04Functional.Xi1 (27/10) (347/100) t =
      log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) ^ 2 / (4199/1000)) / (2 * t) := by
  rw [Set.uIoo, min_eq_left (by norm_num : (8/5 : ℝ) ≤ 11/5),
    max_eq_right (by norm_num : (8/5 : ℝ) ≤ 11/5)] at ht
  have e1 : Wu04Functional.ind (147/100) 3 t = 1 := by
    unfold Wu04Functional.ind
    exact if_pos ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have e2 : Wu04Functional.ind (3199/2700) (147/100) t = 0 := by
    unfold Wu04Functional.ind
    exact if_neg (by rintro ⟨-, h2⟩; linarith [ht.1])
  unfold Wu04Functional.Xi1
  have hA : ((27/10 : ℝ) - 1) * (347/100 - 1) = 4199/1000 := by norm_num
  have hB : (16 : ℝ) / (4199/1000) = 16000/4199 := by norm_num
  have hC : (347/100 : ℝ) - 2 = 147/100 := by norm_num
  have hD : (347/100 : ℝ) - 347/100/(27/10) - 1 = 3199/2700 := by norm_num
  rw [hA, hB, hC, hD, e1, e2]
  ring

/-- The right half panel of `a_{6,1}` in Wu's display 7.2: the stated bound of
`Feed1122_Burst9Matrix_entry_5_0.leaf_right`. -/
theorem right_half :
    (120434785693/1000000000000 : ℝ) ≤ ∫ t in (8/5 : ℝ)..(11/5 : ℝ), tableKernel 5 t := by
  have he : (∫ t in (8/5 : ℝ)..(11/5 : ℝ), tableKernel 5 t) =
      ∫ t in (8/5 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (27/10) (347/100) t := by
    simp only [Wu04Table.tableKernel, Wu04Functional.grid, Wu04Functional.tableSp]
    norm_num
  have h1 : IntervalIntegrable (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) volume (8/5) (11/5) :=
    sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num)
  have h2 : IntervalIntegrable (fun t : ℝ => log ((t + 1) ^ 2 / (4199/1000)) / (2 * t))
      volume (8/5 : ℝ) (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_id.add continuousOn_const).pow 2 |>.div_const (4199/1000)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  rw [he, intervalIntegral.integral_congr_uIoo (f := fun t => Wu04Functional.Xi1 (27/10) (347/100) t)
    (g := fun t => log (16000/4199) * (Wu04Integral.sigma0 t / (2 * t)) +
      log ((t + 1) ^ 2 / (4199/1000)) / (2 * t))
    (fun t ht => r5_xi1_right ht)]
  rw [intervalIntegral.integral_add (h1.const_mul (log (16000/4199))) h2,
    intervalIntegral.integral_const_mul, r5_J2_eq]
  have hI := r5_I_sigma_right
  have hL := r5_L_lower
  have h2lo : (0.69314718055 : ℝ) ≤ log 2 := log_two_bounds.1
  have h2hi : log 2 ≤ (0.69314718056 : ℝ) := log_two_bounds.2
  have hq := r5_log_4199_4000
  have hl := r5_log_11_8
  have hclo : (2 * 0.69314718055 - 0.04855204058217 : ℝ) ≤ log (16000/4199) := by
    rw [r5_log_c]; linarith [hq.2]
  have hPhi : log (4199/1000) ≤ (2 * 0.69314718056 + 0.04855204058217 : ℝ) := by
    rw [r5_log_P]; linarith [hq.2]
  have hPpos : (0 : ℝ) ≤ log (4199/1000) := by
    rw [r5_log_P]; linarith [hq.1]
  have hmul : (2 * 0.69314718055 - 0.04855204058217 : ℝ) * (909201015164161089/100000000000000000000) ≤
      log (16000/4199) * (∫ t in (8/5 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    refine mul_le_mul hclo hI (by norm_num) ?_
    linarith [hclo]
  have hw : log (4199/1000) * log (11/8) ≤
      (2 * 0.69314718056 + 0.04855204058217 : ℝ) * 0.31845373111854 :=
    mul_le_mul hPhi hl.2 (le_trans (by norm_num) hl.1) (by norm_num)
  linarith [hmul, hL, hw]

end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_right

#print axioms LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_right.right_half
