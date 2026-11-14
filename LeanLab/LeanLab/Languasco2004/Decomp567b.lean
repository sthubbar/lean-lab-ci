/-
Jia 1996 pages 275 to 277, the remaining 31 integrals of Lemma 25.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Numeric567_02
import LeanLab.Languasco2004.Numeric567_03
import LeanLab.Languasco2004.Numeric567_04
import LeanLab.Languasco2004.Numeric567_05
import LeanLab.Languasco2004.Numeric567_06
import LeanLab.Languasco2004.Numeric567_07
import LeanLab.Languasco2004.Numeric567_08
import LeanLab.Languasco2004.Numeric567_09
import LeanLab.Languasco2004.Numeric567_10
import LeanLab.Languasco2004.Numeric567_11
import LeanLab.Languasco2004.Numeric567_12
import LeanLab.Languasco2004.Numeric567_13
import LeanLab.Languasco2004.Numeric567_14
import LeanLab.Languasco2004.Numeric567_15
import LeanLab.Languasco2004.Numeric567_16
import LeanLab.Languasco2004.Numeric567_17
import LeanLab.Languasco2004.Numeric567_18
import LeanLab.Languasco2004.Numeric567_19
import LeanLab.Languasco2004.Numeric567_20
import LeanLab.Languasco2004.Numeric567_21
import LeanLab.Languasco2004.Numeric567_22
import LeanLab.Languasco2004.Numeric567_23
import LeanLab.Languasco2004.Numeric567_24
import LeanLab.Languasco2004.Numeric567_25
import LeanLab.Languasco2004.Numeric567_26
import LeanLab.Languasco2004.Numeric567_27
import LeanLab.Languasco2004.Numeric567_28
import LeanLab.Languasco2004.Numeric567_29
import LeanLab.Languasco2004.Numeric567_30
import LeanLab.Languasco2004.Numeric567_31
import LeanLab.Languasco2004.Numeric567_32

namespace LeanLab.Languasco2004.Decomp567b
open Real Polynomial567
noncomputable section

/-- Pages 275 to 277: all lower integrals after the distinguished region 47. -/
def remainderIntegral : ℝ :=
  (∫ t in (34 / 81 : ℝ)..(65 / 154), ∫ u in ((17 / 12) + (-29 / 10) * t)..((25 / 72) + (-1 / 4) * t), kernel 0 t u) +
  (∫ t in (65 / 154 : ℝ)..(49 / 114), ∫ u in ((17 / 12) + (-29 / 10) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (65 / 154 : ℝ)..(49 / 114), ∫ u in ((1 / 3) + (-1 / 3) * t)..((25 / 72) + (-1 / 4) * t), kernel 0 t u) +
  (∫ t in (49 / 114 : ℝ)..(70 / 159), ∫ u in ((17 / 12) + (-29 / 10) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (49 / 114 : ℝ)..(70 / 159), ∫ u in ((1 / 3) + (-1 / 3) * t)..((4 / 21) + (1 / 7) * t), kernel 0 t u) +
  (∫ t in (70 / 159 : ℝ)..(4 / 9), ∫ u in ((17 / 12) + (-29 / 10) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (70 / 159 : ℝ)..(4 / 9), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (70 / 159 : ℝ)..(4 / 9), ∫ u in ((1 / 3) + (-1 / 3) * t)..((4 / 21) + (1 / 7) * t), kernel 0 t u) +
  (∫ t in (4 / 9 : ℝ)..(701 / 1566), ∫ u in ((17 / 12) + (-29 / 10) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (4 / 9 : ℝ)..(701 / 1566), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (4 / 9 : ℝ)..(701 / 1566), ∫ u in ((1 / 3) + (-1 / 3) * t)..((3 / 10) + (-1 / 5) * t), kernel 0 t u) +
  (∫ t in (4 / 9 : ℝ)..(701 / 1566), ∫ u in ((34 / 45) + (-6 / 5) * t)..((4 / 21) + (1 / 7) * t), kernel 0 t u) +
  (∫ t in (701 / 1566 : ℝ)..(41 / 90), ∫ u in ((16 / 135) + (0) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (701 / 1566 : ℝ)..(41 / 90), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (701 / 1566 : ℝ)..(41 / 90), ∫ u in ((1 / 3) + (-1 / 3) * t)..((3 / 10) + (-1 / 5) * t), kernel 0 t u) +
  (∫ t in (701 / 1566 : ℝ)..(41 / 90), ∫ u in ((34 / 45) + (-6 / 5) * t)..((4 / 21) + (1 / 7) * t), kernel 0 t u) +
  (∫ t in (41 / 90 : ℝ)..(17 / 36), ∫ u in ((16 / 135) + (0) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (41 / 90 : ℝ)..(17 / 36), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (41 / 90 : ℝ)..(17 / 36), ∫ u in ((1 / 3) + (-1 / 3) * t)..((4 / 21) + (1 / 7) * t), kernel 0 t u) +
  (∫ t in (17 / 36 : ℝ)..(16 / 33), ∫ u in ((16 / 135) + (0) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (17 / 36 : ℝ)..(16 / 33), ∫ u in ((1 / 4) + (-1 / 4) * t)..((1 / 3) + (-1 / 3) * t), kernel 1 t u) +
  (∫ t in (17 / 36 : ℝ)..(16 / 33), ∫ u in ((1 / 3) + (-1 / 3) * t)..((46 / 63) + (-1) * t), kernel 0 t u) +
  (∫ t in (16 / 33 : ℝ)..(307 / 630), ∫ u in ((16 / 135) + (0) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (16 / 33 : ℝ)..(307 / 630), ∫ u in ((1 / 4) + (-1 / 4) * t)..((89 / 27) + (-58 / 9) * t), kernel 1 t u) +
  (∫ t in (16 / 33 : ℝ)..(307 / 630), ∫ u in ((17 / 99) + (0) * t)..((46 / 63) + (-1) * t), kernel 0 t u) +
  (∫ t in (307 / 630 : ℝ)..(329 / 669), ∫ u in ((16 / 135) + (0) * t)..((1 / 4) + (-1 / 4) * t), kernel 2 t u) +
  (∫ t in (307 / 630 : ℝ)..(329 / 669), ∫ u in ((1 / 4) + (-1 / 4) * t)..((89 / 27) + (-58 / 9) * t), kernel 1 t u) +
  (∫ t in (329 / 669 : ℝ)..(281 / 570), ∫ u in ((16 / 135) + (0) * t)..((89 / 27) + (-58 / 9) * t), kernel 2 t u) +
  (∫ t in (307 / 630 : ℝ)..(281 / 570), ∫ u in ((17 / 99) + (0) * t)..((19 / 6) + (-6) * t), kernel 0 t u) +
  (∫ t in (281 / 570 : ℝ)..(143 / 290), ∫ u in ((16 / 135) + (0) * t)..((89 / 27) + (-58 / 9) * t), kernel 2 t u) +
  (∫ t in (143 / 290 : ℝ)..(1 / 2), ∫ u in ((17 / 99) + (0) * t)..((40 / 57) + (-1) * t), kernel 0 t u)

/-- Page 277: the full remainder coefficient has a reserve of 31 hundred millionths. -/
theorem remainder_numeric_margin : (0.34129331 : ℝ) ≤ remainderIntegral := by
  unfold remainderIntegral
  linarith [Numeric567_02.source_integral_lower,
    Numeric567_03.source_integral_lower,
    Numeric567_04.source_integral_lower,
    Numeric567_05.source_integral_lower,
    Numeric567_06.source_integral_lower,
    Numeric567_07.source_integral_lower,
    Numeric567_08.source_integral_lower,
    Numeric567_09.source_integral_lower,
    Numeric567_10.source_integral_lower,
    Numeric567_11.source_integral_lower,
    Numeric567_12.source_integral_lower,
    Numeric567_13.source_integral_lower,
    Numeric567_14.source_integral_lower,
    Numeric567_15.source_integral_lower,
    Numeric567_16.source_integral_lower,
    Numeric567_17.source_integral_lower,
    Numeric567_18.source_integral_lower,
    Numeric567_19.source_integral_lower,
    Numeric567_20.source_integral_lower,
    Numeric567_21.source_integral_lower,
    Numeric567_22.source_integral_lower,
    Numeric567_23.source_integral_lower,
    Numeric567_24.source_integral_lower,
    Numeric567_25.source_integral_lower,
    Numeric567_26.source_integral_lower,
    Numeric567_27.source_integral_lower,
    Numeric567_28.source_integral_lower,
    Numeric567_29.source_integral_lower,
    Numeric567_30.source_integral_lower,
    Numeric567_31.source_integral_lower,
    Numeric567_32.source_integral_lower]

/-- Page 277: the printed coefficient follows from the certified strict reserve. -/
theorem remainder_numeric_lower : (0.341293 : ℝ) ≤ remainderIntegral := by
  linarith [remainder_numeric_margin]

#print axioms remainder_numeric_margin
#print axioms remainder_numeric_lower
end
end LeanLab.Languasco2004.Decomp567b
