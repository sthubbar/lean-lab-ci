import LeanLab.RieselVaughan1983.Lemma3ErrorIntegral
import LeanLab.RieselVaughan1983.S143SplitBracketA6

/-! Split of the leaf `S106SplitDecomp93.lemma3_eq314`, Lemma 3 display 3.14.
Riesel and Vaughan 1983, Ark. Mat. 21, pages 52 and 53, proof of Lemma 3.
The error term, display 3.16, is already proved as `Lemma3.eq316`.
The main term is split into the paper's integration by parts, the two integrals
on page 53, the bracket of the alternating series, and the cited constant
inequality 0 < A4 < A3 - 2 from display 2.14.
The assembly `lemma3_eq314_of_leaves` has no sorry of its own.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.S143SplitLemma3
open Real MeasureTheory
open LeanLab.RieselVaughan1983.Lemma2 LeanLab.RieselVaughan1983.Lemma3
noncomputable section

/-- The alternating series of page 53, the sum over h at least 1 of
2 (-1)^(h-1) z^(-h) h^(-2). The index here is h - 1. -/
def T (z : ℝ) : ℝ := ∑' h : ℕ, 2 * (-1 : ℝ) ^ h / (z ^ (h + 1) * ((h : ℝ) + 1) ^ 2)

/-- Riesel and Vaughan 1983 page 52, integration by parts of the integral of
z M(u) / (z+u)^2 over 1 < u ≤ z, with M from display 3.15 and M(1) = A4. PROVED. -/
theorem parts_identity (z : ℝ) (hz : 1 ≤ z) :
    M z / 2 + (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) =
      z * A4 / (z + 1) + (∫ u in Set.Ioc 1 z, 2 * z * log u / (u * (z + u))) +
        (∫ u in Set.Ioc 1 z, z * A3 / (u * (z + u))) := by
  have hz0 : 0 < z := by linarith
  have hpos : ∀ u ∈ Set.uIcc 1 z, 0 < u := by
    intro u hu; rw [Set.uIcc_of_le hz] at hu; linarith [hu.1]
  have hMd : ∀ u ∈ Set.uIcc 1 z,
      HasDerivAt M (2 * log u * u⁻¹ + A3 * u⁻¹) u := by
    intro u hu
    have hu0 := hpos u hu
    have h := (((hasDerivAt_log hu0.ne').pow 2).add
      ((hasDerivAt_log hu0.ne').const_mul A3)).add_const A4
    have hfun : M = fun y => log y ^ 2 + A3 * log y + A4 := by
      funext y; rfl
    rw [hfun]
    convert h using 1
    push_cast
    ring
  have hvd : ∀ u ∈ Set.uIcc 1 z,
      HasDerivAt (fun u => -(z / (z + u))) (z / (z + u) ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le hz] at hu
    have := (kernel_hasDerivAt z u hz hu).neg
    convert this using 1
    ring
  have hc1 : ContinuousOn (fun u : ℝ => 2 * log u * u⁻¹ + A3 * u⁻¹) (Set.uIcc 1 z) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu0 := (hpos u hu).ne'
    fun_prop (disch := exact hu0)
  have hc2 : ContinuousOn (fun u : ℝ => z / (z + u) ^ 2) (Set.uIcc 1 z) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu0 : (z + u) ^ 2 ≠ 0 := by have := hpos u hu; positivity
    fun_prop (disch := exact hu0)
  have hc3 : ContinuousOn (fun u : ℝ => 2 * z * log u / (u * (z + u))) (Set.uIcc 1 z) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu1 := (hpos u hu).ne'
    have hu0 : u * (z + u) ≠ 0 := by have := hpos u hu; positivity
    fun_prop (disch := assumption)
  have hc4 : ContinuousOn (fun u : ℝ => z * A3 / (u * (z + u))) (Set.uIcc 1 z) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu0 : u * (z + u) ≠ 0 := by have := hpos u hu; positivity
    fun_prop (disch := exact hu0)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hMd hvd
    hc1.intervalIntegrable hc2.intervalIntegrable
  simp only [← intervalIntegral.integral_of_le hz]
  have e1 : (∫ u in (1 : ℝ)..z, z * M u / (z + u) ^ 2) =
      ∫ u in (1 : ℝ)..z, M u * (z / (z + u) ^ 2) := by
    congr 1; funext u; ring
  have e2 : (∫ u in (1 : ℝ)..z, (2 * log u * u⁻¹ + A3 * u⁻¹) * -(z / (z + u))) =
      -((∫ u in (1 : ℝ)..z, 2 * z * log u / (u * (z + u))) +
        ∫ u in (1 : ℝ)..z, z * A3 / (u * (z + u))) := by
    rw [← intervalIntegral.integral_add hc3.intervalIntegrable hc4.intervalIntegrable,
      ← intervalIntegral.integral_neg]
    congr 1; funext u; simp only [div_eq_mul_inv, mul_inv]; ring
  have hM1 : M 1 = A4 := by
    show log 1 ^ 2 + A3 * log 1 + A4 = A4
    simp
  have hzz : z / (z + z) = 1 / 2 := by field_simp; ring
  rw [e1, hibp, e2, hM1, hzz]
  ring

/-- Riesel and Vaughan 1983 page 53, the elementary integral of z A3 / (u (z+u))
over 1 < u ≤ z, equal to A3 times log z - log 2 + log (1 + 1/z). PROVED. -/
theorem a3_integral (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, z * A3 / (u * (z + u))) =
      A3 * (log z - log 2 + log (1 + 1 / z)) := by
  have hz0 : 0 < z := by linarith
  rw [← intervalIntegral.integral_of_le hz]
  have hcongr : Set.EqOn (fun u : ℝ => z * A3 / (u * (z + u)))
      (fun u => A3 * (u⁻¹ - (z + u)⁻¹)) (Set.uIcc 1 z) := by
    intro u hu
    rw [Set.uIcc_of_le hz] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hzu : 0 < z + u := by linarith
    simp only
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  have hi1 : IntervalIntegrable (fun u : ℝ => u⁻¹) volume 1 z := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro u hu; rw [Set.uIcc_of_le hz] at hu; linarith [hu.1]
    · exact continuousOn_id
  have hi2 : IntervalIntegrable (fun u : ℝ => (z + u)⁻¹) volume 1 z := by
    apply intervalIntegral.intervalIntegrable_inv
    · intro u hu; rw [Set.uIcc_of_le hz] at hu; linarith [hu.1]
    · exact (continuousOn_const.add continuousOn_id)
  rw [intervalIntegral.integral_sub hi1 hi2, integral_inv_of_pos one_pos hz0,
    intervalIntegral.integral_comp_add_left (fun u : ℝ => u⁻¹) z,
    integral_inv_of_pos (by linarith) (by linarith)]
  have h1 : (1 : ℝ) + 1 / z = (z + 1) / z := by field_simp
  rw [h1, div_one, log_div (by linarith) hz0.ne', log_div (by linarith) (by linarith),
    show z + z = 2 * z by ring, log_mul (by norm_num) hz0.ne']
  ring

/-- LEAF: Riesel and Vaughan 1983 page 53, the series expansion of the integral of
2 z log u / (u (z+u)) over 1 < u ≤ z, equal to
(log z)^2 - 2 (log 2) (log z) + pi^2/6 - T z. HARD. -/
theorem log_integral_series (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioc 1 z, 2 * z * log u / (u * (z + u))) =
      log z ^ 2 - 2 * log 2 * log z + π ^ 2 / 6 - T z := by
  sorry

/-- Riesel and Vaughan 1983 page 53, the alternating series T z lies between
0 and 2/z, since its terms decrease in absolute value and alternate in sign. PROVED. -/
theorem T_bracket (z : ℝ) (hz : 1 ≤ z) : 0 ≤ T z ∧ T z ≤ 2 / z := by
  have hz0 : 0 < z := by linarith
  set f : ℕ → ℝ := fun h => 2 / (z ^ (h + 1) * ((h : ℝ) + 1) ^ 2) with hf
  have hterm : (fun h : ℕ => 2 * (-1 : ℝ) ^ h / (z ^ (h + 1) * ((h : ℝ) + 1) ^ 2)) =
      fun h => (-1 : ℝ) ^ h * f h := by
    funext h; simp only [hf]; ring
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro h
    simp only [hf]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : z ^ (h + 1) ≤ z ^ (h + 1 + 1) := pow_le_pow_right₀ hz (by omega)
    have h2 : ((h : ℝ) + 1) ^ 2 ≤ (((h + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      have := (Nat.cast_nonneg h : (0:ℝ) ≤ h)
      push_cast; nlinarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hs0 : Summable (fun h : ℕ => 2 * (1 / ((h : ℝ) + 1) ^ 2)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have h2 := this.mul_left 2
    simpa [Nat.cast_add, Nat.cast_one] using h2
  have hbound : ∀ h : ℕ, ‖(-1 : ℝ) ^ h * f h‖ ≤ 2 * (1 / ((h : ℝ) + 1) ^ 2) := by
    intro h
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by simp only [hf]; positivity)]
    simp only [hf]
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : (1 : ℝ) ≤ z ^ (h + 1) := one_le_pow₀ hz
    nlinarith [sq_nonneg ((h : ℝ) + 1)]
  have hsum : Summable (fun h : ℕ => (-1 : ℝ) ^ h * f h) :=
    (hs0.of_nonneg_of_le (fun h => norm_nonneg _) hbound).of_norm
  have hlim := hsum.hasSum.tendsto_sum_nat
  have hT : T z = ∑' h : ℕ, (-1 : ℝ) ^ h * f h := by
    unfold T; rw [hterm]
  rw [hT]
  constructor
  · have := hanti.alternating_series_le_tendsto hlim 0
    simpa using this
  · have := hanti.tendsto_le_alternating_series hlim 0
    simpa [hf] using this

/-- LEAF: Riesel and Vaughan 1983 page 46 display 2.14, lower bound 1.114073 < A4. HARD, cited numerical evaluation of A0, A2, Euler's constant and the Stieltjes constant. -/
theorem a4_lower_214 : (1114073 / 1000000 : ℝ) < A4 := by
  sorry

/-- LEAF: Riesel and Vaughan 1983 page 46 display 2.14, upper bound A4 < 1.114074. HARD, cited numerical evaluation of A0, A2, Euler's constant and the Stieltjes constant. -/
theorem a4_upper_214 : A4 < (1114074 / 1000000 : ℝ) := by
  sorry

/-- Page 53, the inequalities 0 < A4 < A3 - 2 quoted from display 2.14.
CONDITIONAL ON the display 2.14 leaves `a4_lower_214`, `a4_upper_214` and
`S143SplitBracketA6.a3_lower_214`. -/
theorem a4_bounds_214 : 0 < A4 ∧ A4 < A3 - 2 := by
  have h1 := a4_lower_214
  have h2 := a4_upper_214
  have h3 := S143SplitBracketA6.a3_lower_214
  constructor <;> linarith

/-- Page 53, the closed form of the main term, from the leaves above. -/
theorem main_term_closed_form (z : ℝ) (hz : 1 ≤ z) :
    M z / 2 + (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) =
      log z ^ 2 + (A3 - 2 * log 2) * log z + A4 + π ^ 2 / 6 - A3 * log 2 - T z -
        A4 / (z + 1) + A3 * log (1 + 1 / z) := by
  have hz1 : z + 1 ≠ 0 := by linarith
  rw [parts_identity z hz, a3_integral z hz, log_integral_series z hz]
  have h : z * A4 / (z + 1) = A4 - A4 / (z + 1) := by
    field_simp
    ring
  rw [h]
  ring

/-- Page 53, the main term bound: the closed form differs from the polynomial of
display 3.14 by at most A3 / z. CONDITIONAL ON the leaves above. -/
theorem main_term_bound (z : ℝ) (hz : 1 ≤ z) :
    |M z / 2 + (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) -
      (log z ^ 2 + A6one / 2 * log z + A7one / 4)| ≤ A3 / z := by
  have hz0 : 0 < z := by linarith
  obtain ⟨hT0, hT1⟩ := T_bracket z hz
  obtain ⟨hA4, hA43⟩ := a4_bounds_214
  have hA3 : 0 ≤ A3 := by linarith
  have hzi : 0 ≤ 1 / z := by positivity
  have hl0 : 0 ≤ log (1 + 1 / z) := log_nonneg (by linarith)
  have hl1 : log (1 + 1 / z) ≤ 1 / z := by
    have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / z)
    linarith
  have hq0 : 0 ≤ A4 / (z + 1) := by positivity
  have hq1 : A4 / (z + 1) ≤ A4 / z :=
    div_le_div_of_nonneg_left hA4.le hz0 (by linarith)
  have hm1 : A3 * log (1 + 1 / z) ≤ A3 * (1 / z) := mul_le_mul_of_nonneg_left hl1 hA3
  have hm0 : 0 ≤ A3 * log (1 + 1 / z) := mul_nonneg hA3 hl0
  have hsum : 2 / z + A4 / z ≤ A3 / z := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hz0.le
  have hA3z : A3 * (1 / z) = A3 / z := by ring
  rw [main_term_closed_form z hz]
  unfold A6one A7one
  rw [abs_le]
  constructor <;> nlinarith

/-- Lemma 3, display 3.14 on page 53, assembled from display 3.16 and the
main term leaves. CONDITIONAL ON the leaves of this file. -/
theorem lemma3_eq314_of_leaves : Lemma3ApproxP := by
  intro z hz
  have hz0 : 0 < z := by linarith
  have h316 := eq316 z hz
  have hmain := main_term_bound z hz
  have hneg : z ^ (-1 : ℝ) = 1 / z := by rw [rpow_neg_one, one_div]
  have h8 : A8one / 4 * z ^ (-(1 / 3 : ℝ)) = 2 * A5 * z ^ (-(1 / 3 : ℝ)) := by
    unfold A8one; ring
  have h9 : A9one / 4 * z ^ (-1 : ℝ) = A3 / z := by
    rw [hneg]; unfold A9one; ring
  rw [h8, h9]
  calc |2 * Ctw * S2 z - log z ^ 2 - A6one / 2 * log z - A7one / 4|
      = |(2 * Ctw * S2 z - M z / 2 - (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2)) +
          (M z / 2 + (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) -
            (log z ^ 2 + A6one / 2 * log z + A7one / 4))| := by ring_nf
    _ ≤ |2 * Ctw * S2 z - M z / 2 - (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2)| +
          |M z / 2 + (∫ u in Set.Ioc 1 z, z * M u / (z + u) ^ 2) -
            (log z ^ 2 + A6one / 2 * log z + A7one / 4)| := abs_add_le _ _
    _ < 2 * A5 * z ^ (-(1 / 3 : ℝ)) + A3 / z := add_lt_add_of_lt_of_le h316 hmain

end
end LeanLab.RieselVaughan1983.S143SplitLemma3

#print axioms LeanLab.RieselVaughan1983.S143SplitLemma3.parts_identity
#print axioms LeanLab.RieselVaughan1983.S143SplitLemma3.a3_integral
#print axioms LeanLab.RieselVaughan1983.S143SplitLemma3.T_bracket
#print axioms LeanLab.RieselVaughan1983.S143SplitLemma3.main_term_closed_form
#print axioms LeanLab.RieselVaughan1983.S143SplitLemma3.main_term_bound
#print axioms LeanLab.RieselVaughan1983.S143SplitLemma3.lemma3_eq314_of_leaves
