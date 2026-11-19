/-
DQ6 decisions for HelfgottMajor, design queue item DQ6, run 20261119T0802Z-29270.
Source: P0014 pages 17 to 25, displays 3.30, 3.56 and 3.59 to 3.64, and the
Riemann von Mangoldt error of book chapter 16, display 16.21.

Part A. The re-cut of `Decomp269c.book_error_le_half_exp`. As sealed it is FALSE,
see `BookErrorLeHalfExpFails.lean` and `FALSE_conductor_log_le_quarter_exp_linked.lean`:
the left side grows with the modulus q and the right side has no q. The corrected
statement adds the hypothesis that q is at most exp t, which covers q at most the
height t. Under it every leaf of the old four step split holds, and the corrected
conductor leaf and the corrected target are PROVED below with no unproved step.
The special case with q at most t is also PROVED.

Part B. The two contour bounds `Decomp639Contour.saddle_segment_bound` and
`Decomp639Contour.initial_segment_bound` are accepted as NAMED HYPOTHESES cited from
P0014 page 23 displays 3.56 and 3.57 and pages 24 to 25 displays 3.59 to 3.63.
Two match theorems check that they are exactly the sealed statements. The route
conclusion they feed, `Decomp511a.opposite_positive_contour_before_tail`, is proved
below from them as explicit hypothesis arguments. CONDITIONAL, never PROVED.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.HelfgottMajor.Decomp511a
import LeanLab.HelfgottMajor.ZeroCount1623

namespace LeanLab.HelfgottMajor.DQ6
open Real

/-! ## Part A. The re-cut of `book_error_le_half_exp` with q bounded by the height -/

/-- Corrected conductor leaf. Plain math: if q is a nonzero natural with q at most
exp t and t is at least 100, then 0.15 log q plus 3.389 is at most exp of 0.6 t over 4.
This replaces the FALSE leaf `conductor_log_le_quarter_exp`. PROVED. -/
theorem conductor_log_le_quarter_exp_of_le_exp (q : ℕ) (t : ℝ) (hq : q ≠ 0)
    (ht : 100 ≤ t) (hqt : (q : ℝ) ≤ exp t) :
    0.15 * log q + 3.389 ≤ exp (0.6 * t) / 4 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hlog : log q ≤ t := by
    have := Real.log_le_log hq' hqt
    rwa [Real.log_exp] at this
  have hx : (0 : ℝ) ≤ 0.6 * t := by linarith
  have hquad := Real.quadratic_le_exp_of_nonneg hx
  nlinarith

/-- Corrected target. Plain math: for q nonzero with q at most exp t and t at least 100,
the book error 0.15 log of q times t plus 1, plus 3.389, is at most exp of 0.6 t over 2.
This is the re-cut of the FALSE `Decomp269c.book_error_le_half_exp`. PROVED. -/
theorem book_error_le_half_exp_of_le_exp (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t)
    (hqt : (q : ℝ) ≤ exp t) :
    ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2 := by
  have hq : q ≠ 0 := NeZero.ne q
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hmul : log ((q : ℝ) * (t + 1)) = log q + log (t + 1) :=
    Real.log_mul hq' (ne_of_gt ht1)
  have hheight : log (t + 1) ≤ t + 1 := by
    have := Real.log_le_sub_one_of_pos ht1
    linarith
  have hlinear : 0.6 * t + 1 ≤ exp (0.6 * t) := Real.add_one_le_exp _
  have hcond := conductor_log_le_quarter_exp_of_le_exp q t hq ht hqt
  unfold ZeroCount1623.bookError
  rw [hmul]
  nlinarith

/-- Corrected target in the form named by the queue, q at most the height t. PROVED. -/
theorem book_error_le_half_exp_of_le_height (q : ℕ) [NeZero q] (t : ℝ) (ht : 100 ≤ t)
    (hqt : (q : ℝ) ≤ t) :
    ZeroCount1623.bookError q (t + 1) ≤ exp (0.6 * t) / 2 := by
  refine book_error_le_half_exp_of_le_exp q t ht (hqt.trans ?_)
  have := Real.add_one_le_exp t
  linarith

/-! ## Part B. The two contour bounds as named hypotheses -/

open Decomp511a Decomp639Contour SplitGaussian123

/-- Named hypothesis, the conclusion of `Decomp639Contour.saddle_segment_bound`, P0014
page 23 displays 3.56 and 3.57: the central limacon integral is bounded by the main
coefficient times the saddle exponential. CITED. -/
def SaddleSegmentBoundDQ6 : Prop :=
  ∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re ≤ 1 → 100 ≤ |s.im| → δ * s.im < 0 →
    ‖saddleIntegral δ s‖ ≤ mainCoefficient s.re |s.im| δ *
      exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|)

/-- Named hypothesis, the conclusion of `Decomp639Contour.initial_segment_bound`, P0014
pages 24 to 25 displays 3.59 to 3.63: the integral over the initial segment C1 is bounded
by the first coefficient times exp of minus 0.4798 times the height. CITED. -/
def InitialSegmentBoundDQ6 : Prop :=
  ∀ (δ : ℝ) (s : ℂ), 0 < s.re → s.re ≤ 1 → 100 ≤ |s.im| → δ * s.im < 0 →
    ‖initialIntegral δ s‖ ≤ firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|)

/-- Match check: `SaddleSegmentBoundDQ6` is exactly the sealed statement. Depends on the
sealed open leaf and only checks the match. -/
theorem saddle_named_match_dq6 : SaddleSegmentBoundDQ6 :=
  fun δ s h0 h1 ht hs => saddle_segment_bound δ s h0 h1 ht hs

/-- Match check: `InitialSegmentBoundDQ6` is exactly the sealed statement. Depends on the
sealed open leaf and only checks the match. -/
theorem initial_named_match_dq6 : InitialSegmentBoundDQ6 :=
  fun δ s h0 h1 ht hs => initial_segment_bound δ s h0 h1 ht hs

/-- The statement of `Decomp511a.opposite_positive_contour_before_tail`, CONDITIONAL on the
two named hypotheses `SaddleSegmentBoundDQ6` and `InitialSegmentBoundDQ6`. Same proof as the
sealed theorem with the two cited bounds taken as arguments. -/
theorem opposite_positive_contour_before_tail_of_named_dq6
    (hsaddle : SaddleSegmentBoundDQ6) (hinit : InitialSegmentBoundDQ6)
    (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖gaussianMellin δ s‖ ≤
      mainCoefficient s.re |s.im| δ *
        exp (-BookE.E (|s.im| / (π * δ) ^ 2) * |s.im|) +
      firstCoefficient s.re |s.im| * exp (-0.4798 * |s.im|) +
      (∫ x : ℝ in Set.Ioi (min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)),
        exp (-x ^ 2 / 2) * x ^ (s.re - 1)) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have htpos : 0 < |s.im| := by linarith
  let a := min (|s.im| / (2 * π * |δ|)) (5 / 4 * sqrt |s.im|)
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min (div_pos htpos (by positivity)) (by positivity)
  have hgeom := Decomp639Contour.realEndpoint_lower δ s.im hd htpos
  have hep : 0 < Decomp639Contour.realEndpoint δ s.im := ha.trans_le hgeom
  have htail := real_ray_tail_le_integral δ s _ hep
  have hmono : (∫ x : ℝ in Set.Ioi (Decomp639Contour.realEndpoint δ s.im),
      exp (-x ^ 2 / 2) * x ^ (s.re - 1)) ≤
      ∫ x : ℝ in Set.Ioi a, exp (-x ^ 2 / 2) * x ^ (s.re - 1) := by
    apply MeasureTheory.setIntegral_mono_set
      (gaussian_tail_bound s.re a hσ0.le (by linarith) ha).1
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : 0 < x := ha.trans hx
      positivity
    · exact Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt hgeom hx)
  have hmain := hsaddle δ s hσ0 hσ1 ht hsign
  have hfirst := hinit δ s hσ0 hσ1 ht hsign
  rw [Decomp639Contour.contour_shift δ s hσ0 hσ1 ht hsign]
  calc
    _ ≤ ‖Decomp639Contour.initialIntegral δ s‖ +
        ‖Decomp639Contour.saddleIntegral δ s‖ +
        ‖∫ x : ℝ in Set.Ioi (Decomp639Contour.realEndpoint δ s.im),
          (x : ℂ) ^ (s - 1) * ((exp (-x ^ 2 / 2) : ℂ) *
            LeanLab.HelfgottArcs.e (δ * x))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := by linarith only [hmain, hfirst, htail, hmono]

end LeanLab.HelfgottMajor.DQ6
