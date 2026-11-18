import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Coefficient bound for the Selberg-type cosine majorant

`|G_h| ≤ 4 / h` for the cosine coefficients of the majorant of the arc `[-k/N, k/N]`,
`N = H + 1`. AI wrote this Lean code.
-/

namespace LeanLab.ExceptionalSet.Selberg524

open Real Finset

/-- Sum of cosines along an arithmetic progression, multiplied by `2 sin (d/2)`. -/
private lemma cos_ap_sum (a d : ℝ) (n : ℕ) :
    (∑ i ∈ range n, cos (a + (i : ℝ) * d)) * (2 * sin (d / 2)) =
      sin (a + ((n : ℝ) - 1 / 2) * d) - sin (a - d / 2) := by
  induction n with
  | zero =>
    have e : a + (((0 : ℕ) : ℝ) - 1 / 2) * d = a - d / 2 := by push_cast; ring
    rw [e]; simp
  | succ n ih =>
    rw [sum_range_succ, add_mul, ih]
    have e1 : a + (((n + 1 : ℕ) : ℝ) - 1 / 2) * d = (a + (n : ℝ) * d) + d / 2 := by
      push_cast; ring
    have e2 : a + ((n : ℝ) - 1 / 2) * d = (a + (n : ℝ) * d) - d / 2 := by ring
    rw [e1, e2, sin_add, sin_sub]
    ring

/-- Jordan-type lower bound `sin (π x) ≥ 2 x (1 - x)` on `[0, 1]`. -/
private lemma sin_pi_mul_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    2 * x * (1 - x) ≤ sin (π * x) := by
  have hpi := pi_pos
  rcases le_total x (1 / 2) with hx | hx
  · have hj := mul_le_sin (x := π * x) (by positivity) (by nlinarith)
    have e : 2 / π * (π * x) = 2 * x := by field_simp
    rw [e] at hj
    nlinarith
  · have hj := mul_le_sin (x := π * (1 - x)) (by nlinarith) (by nlinarith)
    have e : 2 / π * (π * (1 - x)) = 2 * (1 - x) := by field_simp
    have e' : π * (1 - x) = π - π * x := by ring
    rw [e, e', sin_pi_sub] at hj
    nlinarith

private lemma coeff_bound_aux (N h : ℝ) (k : ℕ) (hh : 1 ≤ h) (hN : h < N) :
    |2 * (N - h) / N ^ 2 *
          ∑ i ∈ range (2 * k + 1), cos (2 * π * (h * (((i : ℝ) - (k : ℝ)) / N))) +
        2 / (π * N) * sin (2 * π * (h * ((k : ℝ) / N)))| ≤ 4 / h := by
  have hpi := pi_pos
  have hpi3 := two_le_pi
  have hh0 : 0 < h := by linarith
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < h / N := div_pos hh0 hN0
  have hx1 : h / N < 1 := (div_lt_one hN0).2 hN
  have hsum : ∑ i ∈ range (2 * k + 1), cos (2 * π * (h * (((i : ℝ) - (k : ℝ)) / N))) =
      ∑ i ∈ range (2 * k + 1),
        cos (-(2 * π * (h * ((k : ℝ) / N))) + (i : ℝ) * (2 * π * (h / N))) :=
    sum_congr rfl (fun i _ => by congr 1; ring)
  rw [hsum]
  have hD := cos_ap_sum (-(2 * π * (h * ((k : ℝ) / N)))) (2 * π * (h / N)) (2 * k + 1)
  set D := ∑ i ∈ range (2 * k + 1),
        cos (-(2 * π * (h * ((k : ℝ) / N))) + (i : ℝ) * (2 * π * (h / N))) with hDdef
  set θ := 2 * π * (h * ((k : ℝ) / N)) + π * (h / N) with hθ
  have e1 : 2 * π * (h / N) / 2 = π * (h / N) := by ring
  have e2 : -(2 * π * (h * ((k : ℝ) / N))) + (((2 * k + 1 : ℕ) : ℝ) - 1 / 2) * (2 * π * (h / N))
      = θ := by rw [hθ]; push_cast; ring
  have e3 : -(2 * π * (h * ((k : ℝ) / N))) - π * (h / N) = -θ := by rw [hθ]; ring
  rw [e1, e2, e3, sin_neg] at hD
  have hs := sin_pi_mul_ge (h / N) hx0.le hx1.le
  have hspos : 0 < sin (π * (h / N)) := by
    have : 0 < 2 * (h / N) * (1 - h / N) := by
      have : 0 < 1 - h / N := by linarith
      positivity
    linarith
  have habs : |D| * sin (π * (h / N)) ≤ 1 := by
    have h1 : |D| * (2 * sin (π * (h / N))) = |sin θ - -sin θ| := by
      rw [← hD, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * sin (π * (h / N)))]
    have h2 : |sin θ - -sin θ| ≤ 2 := by
      have := abs_le.1 (abs_sin_le_one θ)
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    linarith
  have habs2 : |D| * (2 * (h / N) * (1 - h / N)) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hs (abs_nonneg D)) habs
  have hfirst : |2 * (N - h) / N ^ 2 * D| ≤ 1 / h := by
    have hc : 0 ≤ 2 * (N - h) / N ^ 2 := by
      have : 0 ≤ N - h := by linarith
      positivity
    rw [abs_mul, abs_of_nonneg hc, le_div_iff₀ hh0]
    have e : 2 * (N - h) / N ^ 2 * |D| * h = |D| * (2 * (h / N) * (1 - h / N)) := by
      field_simp
    rw [e]; exact habs2
  have hsecond : |2 / (π * N) * sin (2 * π * (h * ((k : ℝ) / N)))| ≤ 1 / h := by
    have hc : 0 < 2 / (π * N) := by positivity
    rw [abs_mul, abs_of_pos hc]
    have h1 : 2 / (π * N) * |sin (2 * π * (h * ((k : ℝ) / N)))| ≤ 2 / (π * N) * 1 :=
      mul_le_mul_of_nonneg_left (abs_sin_le_one _) hc.le
    have h2 : 2 / (π * N) ≤ 1 / h := by
      rw [div_le_div_iff₀ (by positivity) hh0]
      nlinarith
    linarith
  have h4 : 1 / h + 1 / h ≤ 4 / h := by
    have : 0 < 1 / h := by positivity
    have e : 4 / h = 4 * (1 / h) := by ring
    rw [e]; linarith
  exact le_trans (abs_add_le _ _) (by linarith)

/-- The cosine coefficients `G_h` of the Selberg-type majorant satisfy `|G_h| ≤ 4 / h`. -/
theorem selberg_coeff_bound524 (H k h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ H) :
    |2 * (((H : ℝ) + 1) - (h : ℝ)) / ((H : ℝ) + 1) ^ 2 *
          ∑ i ∈ range (2 * k + 1), cos (2 * π * ((h : ℝ) * (((i : ℝ) - (k : ℝ)) / ((H : ℝ) + 1)))) +
        2 / (π * ((H : ℝ) + 1)) * sin (2 * π * ((h : ℝ) * ((k : ℝ) / ((H : ℝ) + 1))))| ≤ 4 / (h : ℝ) := by
  have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
  have h2 : (h : ℝ) < (H : ℝ) + 1 := by
    have : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hhH
    linarith
  exact coeff_bound_aux ((H : ℝ) + 1) (h : ℝ) k h1 h2

end LeanLab.ExceptionalSet.Selberg524
