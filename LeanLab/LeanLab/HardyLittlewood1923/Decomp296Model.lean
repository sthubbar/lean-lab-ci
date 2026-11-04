import LeanLab.HardyLittlewood1923.Decomp296Laplace
import LeanLab.HardyLittlewood1923.Decomp296Farey

/-!
AI wrote this Lean code for CODEX task296.
P0004 page 25 equations 3.151 to 3.154.
The lower bounds on the Farey widths are explicit hypotheses.
Binary Goldbach is OPEN.
-/

open Real MeasureTheory

namespace LeanLab.HardyLittlewood1923.Decomp296Model

open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp296Integral
open LeanLab.HardyLittlewood1923.Decomp296Laplace

/-- P0004 page 25 equations 3.151 to 3.154, one actual model arc after its width bounds. -/
theorem modelArc_error_of_width {n p q : ℕ} (hn : 0 < n) {K : ℝ} (hK : 0 < K)
    (hL : 1 / (2 * K) ≤ -arcLeft (Nat.sqrt n) p q)
    (hR : 1 / (2 * K) ≤ arcRight (Nat.sqrt n) p q) :
    ‖modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
      ((n : ℂ) ^ 2 / 2)‖ ≤
        (2 * Real.exp 1 / π) *
          ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3‖ * K ^ 2 := by
  let c : ℂ := ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3
  let J : ℂ := ∫ θ : ℝ, ((1 / (n : ℂ)) - Complex.I * θ) ^ (-3 : ℤ) *
    Complex.exp ((n : ℂ) * ((1 / (n : ℂ)) - Complex.I * θ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ : (1 / (2 * (π : ℂ))) * J = (n : ℂ) ^ 2 / 2 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using
      vertical_cube_integral (a := 1 / (n : ℝ)) (by positivity) hnR
  have he : modelArc n p q - c * ((n : ℂ) ^ 2 / 2) =
      (1 / (2 * (π : ℂ))) * c *
        ((∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          ((1 / (n : ℂ)) - Complex.I * θ) ^ (-3 : ℤ) *
            Complex.exp ((n : ℂ) * ((1 / (n : ℂ)) - Complex.I * θ))) - J) := by
    rw [← hJ]
    unfold modelArc c
    ring
  change ‖modelArc n p q - c * ((n : ℂ) ^ 2 / 2)‖ ≤ _
  rw [he, norm_mul, norm_mul]
  have hc : ‖(1 : ℂ) / (2 * (π : ℂ))‖ = 1 / (2 * π) := by
    simp [norm_div, norm_mul, abs_of_pos Real.pi_pos]
  rw [hc]
  calc _ ≤ (1 / (2 * π)) * ‖c‖ * (4 * Real.exp 1 * K ^ 2) :=
      mul_le_mul_of_nonneg_left (model_segment_error hn hK hL hR) (by positivity)
    _ = _ := by dsimp [c]; ring

#print axioms modelArc_error_of_width

/-- P0004 page 25 equations 3.152 to 3.154, with the actual Farey widths proved. -/
theorem modelArc_error {n p q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hqN : q ≤ Nat.sqrt n) (hp : p < q) (hpq : p.Coprime q) :
    ‖modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
      ((n : ℂ) ^ 2 / 2)‖ ≤
        (2 * Real.exp 1 / π) *
          ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3‖ *
            ((q : ℝ) * Nat.sqrt n) ^ 2 := by
  have hN : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hn)
  have hK : 0 < (q : ℝ) * Nat.sqrt n := by positivity
  obtain ⟨hL, hR⟩ := Decomp296Farey.arc_widths hN hq hqN hp hpq
  apply modelArc_error_of_width (by omega) hK
  · simpa only [mul_assoc] using hL
  · simpa only [mul_assoc] using hR

/-- P0004 page 25 equation 3.155, the arithmetic coefficient is bounded by the reciprocal totient cube. -/
theorem arithmetic_cube_norm_le (q : ℕ) :
    ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3‖ ≤
      1 / (q.totient : ℝ) ^ 3 := by
  have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  calc _ = (‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ)) ^ 3 := by simp
    _ ≤ (1 / (q.totient : ℝ)) ^ 3 := by gcongr
    _ = _ := by simp [div_pow]

#print axioms modelArc_error
#print axioms arithmetic_cube_norm_le

/-- P0004 page 25 equation 3.155, the model error summed over one denominator. -/
theorem sum_modelArc_error {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) (hqN : q ≤ Nat.sqrt n) :
    ∑ p ∈ (Finset.range q).filter (fun p => p.Coprime q),
      ‖modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
        ((n : ℂ) ^ 2 / 2)‖ ≤
      (2 * Real.exp 1 / π) * (Nat.sqrt n : ℝ) ^ 2 * ((q : ℝ) / q.totient) ^ 2 := by
  let S := (Finset.range q).filter (fun p => p.Coprime q)
  let c : ℝ := 2 * Real.exp 1 / π
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hcard : S.card = q.totient := by
    simpa only [S, Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm
  have hs : (∑ p ∈ S,
      ‖modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
        ((n : ℂ) ^ 2 / 2)‖) ≤
      ∑ _p ∈ S, c * ‖((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3‖ *
        ((q : ℝ) * Nat.sqrt n) ^ 2 := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact modelArc_error hn hq hqN (Finset.mem_range.mp hp'.1) hp'.2
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hs
  refine hs.trans ?_
  calc
    _ ≤ (q.totient : ℝ) * (c * (1 / (q.totient : ℝ) ^ 3) *
        ((q : ℝ) * Nat.sqrt n) ^ 2) := by
      gcongr
      exact arithmetic_cube_norm_le q
    _ = _ := by
      dsimp [c]
      field_simp [hphi.ne']

#print axioms sum_modelArc_error

end LeanLab.HardyLittlewood1923.Decomp296Model
