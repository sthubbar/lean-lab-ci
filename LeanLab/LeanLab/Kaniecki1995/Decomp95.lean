/-
P0022, Lemma 3, pages 363 and 364, displays 4 to 7.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Trivial95

namespace LeanLab.Kaniecki1995.Decomp95

open Real Complex Finset
open scoped ArithmeticFunction.vonMangoldt

/-- The real part of s in Lemma 3, page 363. -/
noncomputable def sigma (x c : ℝ) : ℝ := 1 / 2 + c / Real.log x

/-- The finite Dirichlet polynomial in display 4, page 363. -/
noncomputable def polynomial (x a c t : ℝ) : ℂ :=
  ∑ n ∈ (range ⌈x ^ a⌉₊).filter (fun n : ℕ => 0 < n ∧ (n : ℝ) < x ^ a),
    ((LamXA x a n : ℝ) : ℂ) / (n : ℂ) ^ ((sigma x c : ℂ) + t * I)

/-- The elementary remainder in display 4, page 363. -/
noncomputable def remainder (x a c t : ℝ) : ℝ :=
  1 / ((a - 1) * t ^ 2 * Real.log x) *
    (Real.exp (-(a * c)) * x ^ (a / 2) + Real.exp (-c) * x ^ (1 / 2 : ℝ) +
      1 / (x ^ sigma x c * (x ^ 2 - 1)) +
      1 / (x ^ (a * sigma x c) * (x ^ (2 * a) - 1)))

/-- The constant in display 6, page 364, in its standard exact form. -/
noncomputable def kOne : ℝ :=
  1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * π) / 2

/-- The trivial zero correction in display 5, page 363. -/
noncomputable def trivialCorrection (σ t : ℝ) : ℝ :=
  ∑' n : ℕ, (σ ^ 2 + 2 * (n + 1) * σ + t ^ 2) /
    (2 * (n + 1) * ((σ + 2 * (n + 1)) ^ 2 + t ^ 2))

/-- The zero mass of display 5, expressed by its Hadamard real part.
This definition does not assume that the Hadamard identity is proved. -/
noncomputable def zeroMass (x c t : ℝ) : ℝ :=
  Real.log x / c *
    ((logDerivZeta ((sigma x c : ℂ) + t * I)).re -
      (1 - sigma x c) / ((1 - sigma x c) ^ 2 + t ^ 2) -
      kOne - Real.log (2 * π) + 1 + trivialCorrection (sigma x c) t)

/-- Page 364, display 6. The constant part of the real identity exceeds three quarters. -/
theorem constant_lower : 3 / 4 ≤ kOne + Real.log (2 * π) - 1 := by
  have hl : 1 < Real.log π := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    exact Real.exp_one_lt_d9.trans (by linarith [Real.pi_gt_three])
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have heq : kOne + Real.log (2 * π) - 1 =
      Real.eulerMascheroniConstant / 2 + Real.log π / 2 := by
    unfold kOne
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero, h4]
    ring
  rw [heq]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- LEAF. Page 363, display 4. Selberg's formula and the pole, trivial zero,
and nontrivial zero estimates give this norm bound. The standard explicit
formulas are Lemmas 1 and 2 on page 362. Their cited sources are Prachar,
Primzahlverteilung, pages 218 and 394, and Selberg 1943, Lemma 2. -/
theorem selberg_bound (hRH : RiemannHypothesis) (x a c t : ℝ)
    (hx : 1 < x) (ha : 1 < a) (hc : 0 < c) (ht : 14 ≤ t)
    (hσ : sigma x c ≤ 3 / 4) :
    ‖logDerivZeta ((sigma x c : ℂ) + t * I)‖ ≤
      ‖polynomial x a c t‖ + remainder x a c t +
        (Real.exp (-c) + Real.exp (-(a * c))) /
          ((a - 1) * Real.log x) * zeroMass x c t := by
  sorry

/-- LEAF. Pages 363 and 364, displays 5 to 7. The Hadamard real part
and the elementary trivial zero estimate bound the zero mass.
The source of the Hadamard identity is Lemma 1 on page 362. -/
theorem zero_mass_bound (x c t : ℝ) (hx : 1 < x) (hc : 0 < c)
    (ht : 14 ≤ t) (hσ : sigma x c ≤ 3 / 4) :
    zeroMass x c t ≤ Real.log x / c *
      (‖logDerivZeta ((sigma x c : ℂ) + t * I)‖ + Real.log t / 2) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hs0 : 0 ≤ sigma x c := by unfold sigma; positivity
  have hs1 : sigma x c < 1 := by linarith
  have hb := Trivial95.correction_bound hs0 hσ ht
  have heq : trivialCorrection (sigma x c) t =
      ∑' n : ℕ, Trivial95.term (sigma x c) t (n + 1) := by
    rfl
  rw [← heq] at hb
  have hp : 0 ≤ (1 - sigma x c) / ((1 - sigma x c) ^ 2 + t ^ 2) := by positivity
  have hre := Complex.re_le_norm (logDerivZeta ((sigma x c : ℂ) + t * I))
  unfold zeroMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [constant_lower]

/-- LEAF. Page 364, the last algebraic step after display 7.
The strict guard permits absorption of the logarithmic derivative. -/
theorem absorption {z D R E A L : ℝ} (hA : 0 < A) (hE : E < A)
    (h : z ≤ D + R + E / A * (z + L / 2)) :
    z ≤ A / (A - E) * (D + E / (2 * A) * L + R) := by
  have hd : 0 < A - E := sub_pos.mpr hE
  have heq : A / (A - E) * (D + E / (2 * A) * L + R) =
      (A * (D + R) + E * L / 2) / (A - E) := by
    field_simp
    <;> ring
  rw [heq, le_div_iff₀ hd]
  have hm := mul_le_mul_of_nonneg_left h hA.le
  field_simp at hm
  nlinarith

/-- Lemma 3 exactly as stated in Statements.lean.
CONDITIONAL ON the two analytic leaves. The assembly has no sorry. -/
theorem lemma3 : Lemma3 := by
  intro hRH x a c t hx ha hc ht hσ hguard
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hA : 0 < (a - 1) * c := mul_pos (sub_pos.mpr ha) hc
  have hE : 0 ≤ Real.exp (-c) + Real.exp (-(a * c)) := by positivity
  have hfirst := selberg_bound hRH x a c t hx ha hc ht hσ
  have hsecond := zero_mass_bound x c t hx hc ht hσ
  have hcoef : 0 ≤ (Real.exp (-c) + Real.exp (-(a * c))) /
      ((a - 1) * Real.log x) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsecond hcoef
  have heq : (Real.exp (-c) + Real.exp (-(a * c))) /
      ((a - 1) * Real.log x) * (Real.log x / c) =
      (Real.exp (-c) + Real.exp (-(a * c))) / ((a - 1) * c) := by
    field_simp
  have hbound : ‖logDerivZeta ((sigma x c : ℂ) + t * I)‖ ≤
      ‖polynomial x a c t‖ + remainder x a c t +
        (Real.exp (-c) + Real.exp (-(a * c))) / ((a - 1) * c) *
          (‖logDerivZeta ((sigma x c : ℂ) + t * I)‖ + Real.log t / 2) := by
    rw [← mul_assoc, heq] at hmul
    linarith
  simpa only [sigma, polynomial, remainder, sub_add_eq_sub_sub, mul_assoc] using absorption hA hguard hbound

/-- The real hypotheses of Lemma 3 hold at x equal to exp 8,
a equal to 2, c equal to 1 and t equal to 14. This does not assert RH. -/
theorem parameter_instance :
    1 < Real.exp 8 ∧ (1 : ℝ) < 2 ∧ (0 : ℝ) < 1 ∧ (14 : ℝ) ≤ 14 ∧
      sigma (Real.exp 8) 1 ≤ 3 / 4 ∧
      Real.exp (-1) + Real.exp (-(2 * 1)) < (2 - 1 : ℝ) * 1 := by
  refine ⟨?_, by norm_num, by norm_num, le_rfl, ?_, ?_⟩
  · exact Real.one_lt_exp_iff.mpr (by norm_num)
  · norm_num [sigma, Real.log_exp]
  · have h0 := Real.exp_pos (-1)
    have h1 := Real.exp_neg_one_lt_d9
    have heq : Real.exp (-(2 * (1 : ℝ))) = Real.exp (-1) ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [heq]
    norm_num
    nlinarith

end LeanLab.Kaniecki1995.Decomp95

#print axioms LeanLab.Kaniecki1995.Decomp95.absorption
#print axioms LeanLab.Kaniecki1995.Decomp95.lemma3

#print axioms LeanLab.Kaniecki1995.Decomp95.constant_lower
#print axioms LeanLab.Kaniecki1995.Decomp95.zero_mass_bound

#print axioms LeanLab.Kaniecki1995.Decomp95.parameter_instance
