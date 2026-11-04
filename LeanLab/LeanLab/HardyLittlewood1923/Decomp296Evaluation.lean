import LeanLab.HardyLittlewood1923.Decomp296Model
import LeanLab.HardyLittlewood1923.Decomp105b
import LeanLab.PNTPort.Vinogradov.SingSeries

/-!
AI wrote this Lean code for CODEX task296.
P0004 page 25 equations 3.154 and 3.155.
This evaluates the summed model errors using proved arithmetic bounds.
Binary Goldbach is OPEN.
-/

open Real Finset

namespace LeanLab.HardyLittlewood1923.Decomp296Evaluation

open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp296Model
open LeanLab.HardyLittlewood1923.Decomp105
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.PNTPort.LargeSieve

/-- P0004 page 25 equation 3.155, the squared totient ratios have a logarithmic sum bound. -/
theorem totient_ratio_square_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ q ∈ Icc 1 N, ((q : ℝ) / q.totient) ^ 2 ≤ C * N * (1 + Real.log N) ^ 2 := by
  obtain ⟨C, hC, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨C ^ 2, by positivity, fun N hN => ?_⟩
  have hb {q : ℕ} (hq : q ∈ Icc 1 N) : (q : ℝ) / q.totient ≤ C * (1 + Real.log N) := by
    apply (Decomp105b.ratio_le_sum (mem_Icc.mp hq).1).trans
    apply le_trans _ (hsum N)
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans (mem_Icc.mp hq).2⟩
    · intro d _ _
      positivity
  calc
    _ ≤ ∑ _q ∈ Icc 1 N, (C * (1 + Real.log N)) ^ 2 := by
      apply sum_le_sum
      intro q hq
      exact pow_le_pow_left₀ (by positivity) (hb hq) 2
    _ = _ := by simp [sum_const, nsmul_eq_mul, Nat.card_Icc]; ring

/-- P0004 page 26 equation 3.212, in the explicit phase convention of fareyModel. -/
theorem phase_sum {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ∑ p ∈ (range q).filter (fun p => p.Coprime q),
      Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) =
        (LeanLab.HeathBrown1985.ramanujan q n : ℂ) := by
  have he (p : ℕ) : Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) =
      (starRingEnd ℂ) (LeanLab.PNTPort.LargeSieve.e ((n : ℝ) * p / q)) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp
    norm_num [map_ofNat] <;> ring
  simp_rw [he]
  rw [← map_sum, LeanLab.PNTPort.Vinogradov.ramanujan_sum hq n]
  simp

#print axioms totient_ratio_square_sum
#print axioms phase_sum

/-- P0004 page 25 equation 3.154 and page 26 equation 3.156, the exact finite main term. -/
theorem model_main_sum (n : ℕ) :
    (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
      Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
        (((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 * ((n : ℂ) ^ 2 / 2))) =
      (finiteMain n : ℂ) := by
  unfold finiteMain
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [← sum_mul, phase_sum (mem_Icc.mp hq).1 n]
  unfold singTerm
  push_cast
  ring

/-- P0004 page 25 equation 3.155, before estimating the positive error sum. -/
theorem farey_model_error_sum (n : ℕ) :
    ‖fareyModel n - (finiteMain n : ℂ)‖ ≤
      ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ‖modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
          ((n : ℂ) ^ 2 / 2)‖ := by
  have he : fareyModel n - (finiteMain n : ℂ) =
      ∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        Complex.exp (-2 * π * Complex.I * (n : ℂ) * p / q) *
          (modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
            ((n : ℂ) ^ 2 / 2)) := by
    rw [← model_main_sum n, fareyModel, ← sum_sub_distrib]
    apply sum_congr rfl
    intro q hq
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q hq
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  simp [norm_mul, Complex.norm_exp]

#print axioms model_main_sum
#print axioms farey_model_error_sum

/-- P0004 page 25 equations 3.154 and 3.155, the completed ternary model evaluation. -/
theorem farey_to_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      ‖fareyModel n - (finiteMain n : ℂ)‖ ≤
        C * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log n ^ 2 := by
  obtain ⟨C, hC, hsum⟩ := totient_ratio_square_sum
  let c : ℝ := 2 * Real.exp 1 / π
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨4 * c * C, by positivity, fun n hn => ?_⟩
  let N := Nat.sqrt n
  have hN : 1 ≤ N := Nat.le_sqrt.mpr (by omega)
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNsq : (N : ℝ) ^ 2 ≤ n := by
    have hh : (N : ℝ) * N ≤ n := by exact_mod_cast Nat.sqrt_le n
    simpa only [pow_two] using hh
  have hs : (N : ℝ) ≤ Real.sqrt n := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]
  have hs3 : (Real.sqrt n) ^ 3 = (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hN3 : (N : ℝ) ^ 3 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← hs3]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hs 3
  have hlog : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogle : Real.log N ≤ Real.log n :=
    Real.log_le_log hNR (by exact_mod_cast Nat.sqrt_le_self n)
  have hlog2 : (1 + Real.log N) ^ 2 ≤ 4 * Real.log n ^ 2 := by
    calc _ ≤ (2 * Real.log n) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ = _ := by ring
  calc
    _ ≤ ∑ q ∈ Icc 1 N, ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ‖modelArc n p q - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) ^ 3 *
          ((n : ℂ) ^ 2 / 2)‖ := farey_model_error_sum n
    _ ≤ ∑ q ∈ Icc 1 N, c * (N : ℝ) ^ 2 * ((q : ℝ) / q.totient) ^ 2 := by
      apply sum_le_sum
      intro q hq
      exact sum_modelArc_error (by omega) (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
    _ = c * (N : ℝ) ^ 2 * ∑ q ∈ Icc 1 N, ((q : ℝ) / q.totient) ^ 2 := by rw [mul_sum]
    _ ≤ c * (N : ℝ) ^ 2 * (C * N * (1 + Real.log N) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsum N hN) (by positivity)
    _ = c * C * (N : ℝ) ^ 3 * (1 + Real.log N) ^ 2 := by ring
    _ ≤ c * C * (n : ℝ) ^ (3 / 2 : ℝ) * (1 + Real.log N) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN3 (by positivity)) (by positivity)
    _ ≤ c * C * (n : ℝ) ^ (3 / 2 : ℝ) * (4 * Real.log n ^ 2) :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ = _ := by ring

#print axioms farey_to_finite_bound

end LeanLab.HardyLittlewood1923.Decomp296Evaluation
