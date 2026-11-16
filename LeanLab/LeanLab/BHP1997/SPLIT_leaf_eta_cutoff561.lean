/-
Split of theorem leaf_eta_cutoff561 in LeanLab.BHP1997.Decomp561m: the eta
cutoff error of display 2.6 on page 8, the mean square over the even
frequencies of the difference between the truncated eta integral and the
complete period integral.
The cut separates the unit coefficient case with the explicit frequency count
from the two elementary interface estimates (count of even frequencies, sign of
the scale). The u times v scaling is bookkeeping and is proved here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp561m

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- Both principal models carry one common factor u times v in front of the
modulus sum, and nothing else in them depends on u and v. -/
private theorem principalArc_units561 (ε D x u v : ℝ) (N : ℕ) :
    principalArc512 ε D x u v N = ((u * v : ℝ) : ℂ) * principalArc512 ε D x 1 1 N := by
  unfold principalArc512
  push_cast
  ring

/-- The complete period model of the same display has the same factor. -/
private theorem completePrincipal_units561 (ε D x u v : ℝ) (N : ℕ) :
    completePrincipal561 ε D x u v N =
      ((u * v : ℝ) : ℂ) * completePrincipal561 ε D x 1 1 N := by
  unfold completePrincipal561
  push_cast
  ring

/-- The eta cutoff difference at any coefficient pair is the unit coefficient
difference multiplied by the common factor. -/
private theorem etaDiff_units561 (ε D x u v : ℝ) (N : ℕ) :
    principalArc512 ε D x u v N - completePrincipal561 ε D x u v N =
      ((u * v : ℝ) : ℂ) *
        (principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N) := by
  rw [principalArc_units561 (u := u) (v := v), completePrincipal_units561 (u := u) (v := v),
    principalArc_units561 (u := 1) (v := 1), completePrincipal_units561 (u := 1) (v := 1)]
  simp only [mul_one, Complex.ofReal_one, one_mul]
  ring

/-- The eta cutoff error is quadratic in the two coefficients. -/
private theorem etaTailError_units561 (ε D x u v : ℝ) :
    etaTailError561 ε D x u v = u ^ 2 * v ^ 2 * etaTailError561 ε D x 1 1 := by
  unfold etaTailError561
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [etaDiff_units561, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- LEAF. The eta cutoff mean square at unit coefficients, stated with the
number of even frequencies kept explicit instead of replaced by the frequency
interval length. This is the analytic step of display 2.6 on page 8: the two
removed eta tails are integrated against the reciprocal square of the distance
to the nearest integer, the modulus average over q divided by phi of q is taken
over the full modulus range, and the resulting tail is transferred into the mean
square over the even frequencies. The count factor is handed to the interface
leaves below, so this leaf is weaker than the target in the coefficient pair
(unit coefficients instead of arbitrary u and v, the quadratic scaling being
proved above) and in the right hand side, which is larger than the target scale
whenever the count exceeds the interval length. The polynomial tail reduction
and its mean square transfer are what remains open. -/
theorem leaf_eta_tail_unit_coeff561 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100)
    (A : ℝ) (hA : 0 < A) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      etaTailError561 ε D x 1 1 ≤
        C * ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2 *
          Real.log x ^ (-A - 7) := by
  sorry

/-- LEAF. The number of even frequencies in the closed interval from the
ceiling of x to the floor of x plus the interval length. The interval holds at
most the interval length plus one integers, its even part is at most half of
that, and the length is at least one, so three copies of the length cover the
count. This is the step that replaces the explicit count of the unit
coefficient leaf by the interval length factor of the target scale. -/
theorem leaf_frequencies_card561 (ε x : ℝ) (hε : 0 < ε) (hx : 3 ≤ x) :
    ((frequencies512 ε x).card : ℝ) ≤
      3 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  sorry

/-- LEAF. The target scale is nonnegative on the range: the positive power of x,
the square of the interval length and the arbitrary negative power of the
logarithm are each nonnegative. This is the step that lets a bound at the
enlarged constant be multiplied by the scale without turning the inequality
around, including at x where one of the three factors vanishes and including at
zero coefficients. -/
theorem leaf_scale_nonneg561 (ε A x : ℝ) (hx : 3 ≤ x) : 0 ≤ scale512 ε A x := by
  sorry

/-- The assembly: the target statement follows from the unit coefficient leaf,
the frequency count leaf and the sign of the scale, with the constant of the
unit coefficient leaf enlarged by the coefficient square and by the count
factor three. The eta cutoff error at general coefficients is recovered from the
unit coefficient error by the proved quadratic scaling. -/
theorem leaf_eta_cutoff561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaTailError561 ε D x u v ≤ C * scale512 ε A x := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε hε hε' u v A hA
  obtain ⟨D₀, hD₀⟩ := leaf_eta_tail_unit_coeff561 ε hε hε' A hA
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD₀ D hD
  refine ⟨max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3, fun x hx => ?_⟩
  have hCx : C₁ ≤ x := by
    have h : C₁ ≤ max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
      linarith [le_max_left C₁ (3 * (u ^ 2 * v ^ 2) * C₁),
        le_max_left (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    exact h.trans hx
  have hx3 : 3 ≤ x := by
    have h : (3 : ℝ) ≤ max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
      linarith [le_max_right (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    exact h.trans hx
  set card : ℝ := ((frequencies512 ε x).card : ℝ) with hcard_def
  set Y : ℝ := length512 ε x with hY_def
  set lg : ℝ := Real.log x ^ (-A - 7) with hlg_def
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH_def
  have huv : 0 ≤ u ^ 2 * v ^ 2 := by positivity
  have hcard0 : 0 ≤ card := by
    rw [hcard_def]
    exact Nat.cast_nonneg _
  have hY0 : 0 ≤ Y ^ 2 := by positivity
  have hlg0 : 0 ≤ lg := by
    rw [hlg_def]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hP0 : 0 ≤ card * Y ^ 2 * lg := mul_nonneg (mul_nonneg hcard0 hY0) hlg0
  have hcardH : card ≤ 3 * H := by
    rw [hcard_def, hH_def]
    exact leaf_frequencies_card561 ε x hε hx3
  have hstep : etaTailError561 ε D x 1 1 ≤ C₁ * card * Y ^ 2 * lg := by
    have h := hC₁ x hCx
    rw [hcard_def, hY_def, hlg_def]
    exact h
  have hK : etaTailError561 ε D x 1 1 ≤ max C₁ 0 * card * Y ^ 2 * lg := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left (C₁ : ℝ) 0) hP0
    calc etaTailError561 ε D x 1 1 ≤ C₁ * card * Y ^ 2 * lg := hstep
      _ = C₁ * (card * Y ^ 2 * lg) := by ring
      _ ≤ max C₁ 0 * (card * Y ^ 2 * lg) := hm
      _ = max C₁ 0 * card * Y ^ 2 * lg := by ring
  have hKH : max C₁ 0 * card * Y ^ 2 * lg ≤ max C₁ 0 * (3 * H) * Y ^ 2 * lg := by
    have h0 : 0 ≤ max C₁ 0 * (Y ^ 2 * lg) :=
      mul_nonneg (le_max_right (C₁ : ℝ) 0) (mul_nonneg hY0 hlg0)
    have hm := mul_le_mul_of_nonneg_right hcardH h0
    calc max C₁ 0 * card * Y ^ 2 * lg = card * (max C₁ 0 * (Y ^ 2 * lg)) := by ring
      _ ≤ (3 * H) * (max C₁ 0 * (Y ^ 2 * lg)) := hm
      _ = max C₁ 0 * (3 * H) * Y ^ 2 * lg := by ring
  have hmain : etaTailError561 ε D x u v ≤
      u ^ 2 * v ^ 2 * (max C₁ 0 * (3 * H) * Y ^ 2 * lg) := by
    rw [etaTailError_units561]
    exact (mul_le_mul_of_nonneg_left hK huv).trans (mul_le_mul_of_nonneg_left hKH huv)
  have hscale_eq : H * Y ^ 2 * lg = scale512 ε A x := by
    rw [hH_def, hY_def, hlg_def]
    unfold scale512
    ring
  have hscale0 : 0 ≤ H * Y ^ 2 * lg := by
    rw [hscale_eq]
    exact leaf_scale_nonneg561 ε A x hx3
  have hcoef : 3 * (u ^ 2 * v ^ 2) * max C₁ 0 ≤
      max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
    have hm : max (3 * (u ^ 2 * v ^ 2) * C₁) 0 = 3 * (u ^ 2 * v ^ 2) * max C₁ 0 := by
      rw [mul_max_of_nonneg C₁ 0 (by positivity : (0 : ℝ) ≤ 3 * (u ^ 2 * v ^ 2)), mul_zero]
    rw [← hm]
    refine max_le ?_ ?_
    · linarith [le_max_right C₁ (3 * (u ^ 2 * v ^ 2) * C₁),
        le_max_left (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    · linarith [le_max_right (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
  have hlast : u ^ 2 * v ^ 2 * (max C₁ 0 * (3 * H) * Y ^ 2 * lg)
      = (3 * (u ^ 2 * v ^ 2) * max C₁ 0) * (H * Y ^ 2 * lg) := by ring
  rw [hlast] at hmain
  calc etaTailError561 ε D x u v
      ≤ (3 * (u ^ 2 * v ^ 2) * max C₁ 0) * (H * Y ^ 2 * lg) := hmain
    _ ≤ (max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3) * (H * Y ^ 2 * lg) :=
        mul_le_mul_of_nonneg_right hcoef hscale0
    _ = (max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3) * scale512 ε A x := by
        rw [hscale_eq]

end LeanLab.BHP1997.Decomp561m
