import LeanLab.HardyLittlewood1923.Decomp296Farey
import LeanLab.HardyLittlewood1923.Decomp276b
import LeanLab.HardyLittlewood1923.Decomp105b
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
AI wrote this Lean code for CODEX task296.
P0004 pages 22 to 24 equations 3.119, 3.131 and 3.141.
This is the square mean estimate for the rational main approximation.
Binary Goldbach is OPEN.
-/

open Real Finset MeasureTheory

namespace LeanLab.HardyLittlewood1923.Decomp296SquareMean

open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b

/-- P0004 page 24 equation 3.131 at r equal to three, the local rational square mean. -/
theorem localPhi_square_integral {n : ℕ} (hn : 1 ≤ n) (q : ℕ) (L R : ℝ) :
    (∫ θ in L..R, ‖localPhi n q θ‖ ^ 2) ≤
      π * n * ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he (θ : ℝ) : ‖localPhi n q θ‖ ^ 2 =
      ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ^ 2 *
        ((1 / (n : ℝ)) ^ 2 + θ ^ 2)⁻¹ := by
    have hy : ‖localY n θ‖ ^ 2 = (1 / (n : ℝ)) ^ 2 + θ ^ 2 := by
      rw [Complex.sq_norm]
      simp [localY, Complex.normSq_apply, pow_two, mul_inv_rev]
    rw [localPhi, norm_div, div_pow, hy, div_eq_mul_inv]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    integral_inv_sq_add_sq (by positivity : (1 / (n : ℝ)) ≠ 0)]
  have ha : arctan (R / (1 / (n : ℝ))) - arctan (L / (1 / (n : ℝ))) ≤ π := by
    linarith [arctan_lt_pi_div_two (R / (1 / (n : ℝ))),
      neg_pi_div_two_lt_arctan (L / (1 / (n : ℝ)))]
  simp only [one_div, inv_inv] at ha ⊢
  calc _ ≤ ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ^ 2 * ((n : ℝ) * π) := by
        gcongr
    _ = _ := by ring

#print axioms localPhi_square_integral

/-- P0004 page 24 equation 3.131, summing the square mean over one denominator. -/
theorem localPhi_denominator_square_sum {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) :
    (∑ p ∈ (range q).filter (fun p => p.Coprime q),
      ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q, ‖localPhi n q θ‖ ^ 2) ≤
        π * n / (q.totient : ℝ) := by
  let S := (range q).filter (fun p => p.Coprime q)
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hcoef : ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ^ 2 ≤
      1 / (q.totient : ℝ) ^ 2 := by
    calc _ = (‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ)) ^ 2 := by simp
      _ ≤ (1 / (q.totient : ℝ)) ^ 2 := by gcongr
      _ = _ := by simp
  have hcard : S.card = q.totient := by
    simpa only [S, Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm
  have hs : (∑ p ∈ S,
      ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q, ‖localPhi n q θ‖ ^ 2) ≤
      ∑ _p ∈ S, π * n * ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ^ 2 := by
    exact sum_le_sum (fun p _ => localPhi_square_integral hn q _ _)
  simp only [sum_const, nsmul_eq_mul, hcard] at hs
  refine hs.trans ?_
  calc
    _ ≤ (q.totient : ℝ) * (π * n * (1 / (q.totient : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoef (by positivity)) (by positivity)
    _ = _ := by field_simp [hphi.ne']

#print axioms localPhi_denominator_square_sum

/-- P0004 page 24 equations 3.131 and 3.141, the rational main approximation square mean. -/
theorem localPhi_square_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q, ‖localPhi n q θ‖ ^ 2) ≤
          C * n * Real.log n := by
  obtain ⟨D, hD, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨2 * π * D, by positivity, fun n hn => ?_⟩
  have hN : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hlog : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hlogle : Real.log (Nat.sqrt n) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < Nat.sqrt n))
      (by exact_mod_cast Nat.sqrt_le_self n)
  have hb : (∑ q ∈ Icc 1 (Nat.sqrt n), (1 : ℝ) / q.totient) ≤ D * (2 * Real.log n) :=
    (hsum (Nat.sqrt n)).trans (mul_le_mul_of_nonneg_left (by linarith) hD.le)
  calc
    _ ≤ ∑ q ∈ Icc 1 (Nat.sqrt n), π * n / (q.totient : ℝ) :=
      sum_le_sum (fun q hq => localPhi_denominator_square_sum (by omega) (mem_Icc.mp hq).1)
    _ = (π * n) * ∑ q ∈ Icc 1 (Nat.sqrt n), (1 : ℝ) / q.totient := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      ring
    _ ≤ (π * n) * (D * (2 * Real.log n)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

#print axioms localPhi_square_mean

end LeanLab.HardyLittlewood1923.Decomp296SquareMean
