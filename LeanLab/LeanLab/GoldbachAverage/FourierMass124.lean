import LeanLab.GoldbachAverage.LZTheorem1RH
import LeanLab.PNTPort.Gallagher.Basic

/-!
A coarse finite Fourier bound used to audit the sealed State1558 Lemma 3 encoding.
The encoded statement has an extra y inverse on its left side.
This file proves a weaker consequence than P0050 page 3 Lemma 3.
It does not prove that paper lemma.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.FourierMass124
open Finset MeasureTheory Filter
open LeanLab.PNTPort.LargeSieve
open scoped ArithmeticFunction.vonMangoldt

/-- A two period Parseval bound for the finite coefficient polynomial.
Source comparison: P0050 page 3 Lemma 3, with its extra encoded y inverse removed only after
cancelling it against the right side. This is a coarse lab consequence, not the paper bound. -/
theorem coarse_local_mean_square {x y : ℝ} (hx : 2 ≤ x) (hy : 1 ≤ y) :
    (∫ α in (-(1 / y))..(1 / y),
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, ((Λ n : ℂ) - 1) * eAdd (α * n)‖ ^ 2) ≤
      144 * x * Real.log x ^ 4 := by
  let M : ℕ := ⌊x⌋₊
  let c : ℕ → ℂ := fun n => if n = 0 then 0 else (Λ n : ℂ) - 1
  let R : ℝ → ℂ := fun α => ∑ n ∈ Icc 1 M, ((Λ n : ℂ) - 1) * eAdd (α * n)
  let F : ℝ → ℝ := fun α => ‖R α‖ ^ 2
  have hR (α : ℝ) : R α = ∑ n ∈ range (M + 1), c n * LeanLab.PNTPort.LargeSieve.e (n * α) := by
    calc R α = ∑ n ∈ Icc 1 M, c n * LeanLab.PNTPort.LargeSieve.e (n * α) := by
          apply sum_congr rfl
          intro n hn
          have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
          simp [c, hn0, eAdd_eq_e, mul_comm]
      _ = _ := by
        apply sum_subset
        · intro n hn; have := mem_Icc.mp hn; exact mem_range.mpr (by omega)
        · intro n hn hnot
          have hn0 : n = 0 := by
            have := mem_range.mp hn
            simp only [mem_Icc, not_and_or, not_le] at hnot
            omega
          simp [c, hn0]
  have hc : Continuous R := by
    exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul (continuous_eAdd_mul (n : ℝ))
  have hF : Continuous F := hc.norm.pow 2
  have hper : Function.Periodic F 1 := by
    intro α
    dsimp [F, R]
    simp_rw [eAdd_add_one]
  have hpars : (∫ α in (-(1 / 2 : ℝ))..(1 / 2), F α) =
      ∑ n ∈ range (M + 1), ‖c n‖ ^ 2 := by
    calc (∫ α in (-(1 / 2 : ℝ))..(1 / 2), F α) =
          ∫ α in (-(1 / 2 : ℝ))..(1 / 2),
            ‖∑ n ∈ range (M + 1), c n * LeanLab.PNTPort.LargeSieve.e (n * α)‖ ^ 2 := by
            apply intervalIntegral.integral_congr
            intro α _
            change ‖R α‖ ^ 2 = _
            rw [hR]
      _ = _ := LeanLab.PNTPort.Gallagher.parseval c (M + 1)
  have hdouble := hper.intervalIntegral_add_zsmul_eq (2 : ℤ) (-1)
    (fun a b => hF.intervalIntegrable a b)
  have hshift := hper.intervalIntegral_add_eq (-1) (-(1 / 2))
  norm_num [smul_eq_mul] at hdouble hshift
  rw [hshift, hpars] at hdouble
  have hy0 : 0 < y := by linarith
  have hw0 : 0 ≤ 1 / y := by positivity
  have hw1 : 1 / y ≤ 1 := (div_le_one hy0).mpr hy
  have hi := intervalIntegral.integral_mono_interval (μ := volume)
    (show (-1 : ℝ) ≤ -(1 / y) by linarith)
    (show -(1 / y) ≤ 1 / y by linarith) hw1
    (Eventually.of_forall fun α => sq_nonneg ‖R α‖) (hF.intervalIntegrable (-1) 1)
  have hx0 : 0 < x := by linarith
  have hlog : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hcoeff : ∀ n ∈ range (M + 1), ‖c n‖ ^ 2 ≤ (Real.log x + 1) ^ 2 := by
    intro n hn
    by_cases hn0 : n = 0
    · simpa [c, hn0] using sq_nonneg (Real.log x + 1)
    have hnM : n ≤ M := by have := mem_range.mp hn; omega
    have hnx : (n : ℝ) ≤ x := (by exact_mod_cast hnM : (n : ℝ) ≤ M).trans
      (Nat.floor_le hx0.le)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have hl := (ArithmeticFunction.vonMangoldt_le_log (n := n)).trans
      (Real.log_le_log hnpos hnx)
    have hc' : ‖c n‖ ≤ Real.log x + 1 := by
      simp only [c, if_neg hn0]
      have htri := norm_sub_le ((Λ n : ℝ) : ℂ) (1 : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_one] at htri
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) hc' 2
  have hsum := sum_le_sum hcoeff
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hM : ((M + 1 : ℕ) : ℝ) ≤ 2 * x := by
    have hm : (M : ℝ) ≤ x := Nat.floor_le hx0.le
    push_cast
    linarith
  have hL : (Real.log x + 1) ^ 2 ≤ 36 * Real.log x ^ 4 := by
    have h1 : (Real.log x + 1) ^ 2 ≤ 9 * Real.log x ^ 2 := by
      nlinarith [sq_nonneg (Real.log x - 1 / 2)]
    have h2 : (1 : ℝ) / 4 ≤ Real.log x ^ 2 := by
      nlinarith [sq_nonneg (Real.log x - 1 / 2)]
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (Real.log x))
    nlinarith
  have hs : ∑ n ∈ range (M + 1), ‖c n‖ ^ 2 ≤ 72 * x * Real.log x ^ 4 := by
    calc _ ≤ ((M + 1 : ℕ) : ℝ) * (Real.log x + 1) ^ 2 := hsum
      _ ≤ (2 * x) * (36 * Real.log x ^ 4) := by gcongr
      _ = _ := by ring
  rw [hdouble] at hi
  change (∫ α in (-(1 / y))..(1 / y), F α) ≤ _
  linarith

end LeanLab.GoldbachAverage.FourierMass124
