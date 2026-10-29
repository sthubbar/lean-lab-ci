/- AI wrote the Lean code for CODEX task164.
Elementary error budget for journal Lemma 11 p. 1228.
The prime count, Robin and logarithmic integral inputs stay explicit.
Goldbach is open. -/
import LeanLab.BS2022GRH.BookkeepingC164
import LeanLab.BS2022GRH.Constants
import LeanLab.BS2022GRH.LiPV
namespace LeanLab.BS2022GRH.Lemma11C164
open Real Finset Classical
/-- The paper threshold gives a logarithm at least 22000. -/
theorem log_lower (N : ℝ) (hN : exp (exp 10) ≤ N) : 22000 ≤ log N := by
  have hN0 : 0 < N := (exp_pos _).trans_le hN
  have he : (22000 : ℝ) ≤ exp 10 := by
    have h := exp_nat_ge 10
    norm_num at h
    norm_num
    linarith
  exact he.trans ((le_log_iff_exp_le hN0).mpr hN)
/-- Above the paper threshold, square root N exceeds log N to the fourth power. -/
theorem sqrt_large (N : ℝ) (hN : exp (exp 10) ≤ N) : log N ^ 4 ≤ √N := by
  have hN0 : 0 < N := (exp_pos _).trans_le hN
  have hL := log_lower N hN
  have he := Real.pow_div_factorial_le_exp (x := log N / 2) (by linarith) 5
  have hs : exp (log N / 2) = √N := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hN0]
    congr 1
    ring
  rw [hs] at he
  norm_num [Nat.factorial] at he
  have hp : 0 ≤ log N ^ 4 := by positivity
  nlinarith
/-- The Schoenfeld and Robin errors fit into two N over log cubed N. -/
theorem error_budget (N : ℝ) (hN : exp (exp 10) ≤ N) :
    √N * log N / (8 * π) + 1.3841 * log N / log (log N) ≤ 2 * N / log N ^ 3 := by
  have hN0 : 0 < N := (exp_pos _).trans_le hN
  have hL := log_lower N hN
  have hS := sqrt_large N hN
  have hlog : 1 ≤ log (log N) := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  have hL0 : 0 < log N := by linarith
  have hS0 : 0 < √N := sqrt_pos.mpr hN0
  have h4 : (2 : ℝ) ≤ log N ^ 4 := by nlinarith [sq_nonneg (log N ^ 2 - 2)]
  have hN2 : 2 * log N ^ 4 ≤ N := by
    have hm := mul_le_mul_of_nonneg_left hS hS0.le
    have hs := sq_sqrt hN0.le
    nlinarith
  have hp : 1 ≤ 8 * π := by linarith [pi_gt_three]
  have h1 : √N * log N / (8 * π) ≤ N / log N ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hS hS0.le
    have hm2 := mul_le_mul_of_nonneg_left hp hN0.le
    nlinarith [sq_sqrt hN0.le]
  have h2 : 1.3841 * log N / log (log N) ≤ N / log N ^ 3 := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hlog hN0.le
    nlinarith
  calc _ ≤ N / log N ^ 3 + N / log N ^ 3 := add_le_add h1 h2
    _ = _ := by ring
/-- Journal Lemma 11, CONDITIONAL ON the prime count, Robin and li estimates.
All analytic inequalities used by the paper remain explicit arguments. -/
theorem cardinality_bounds (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ))
    (hpi : |(((range (n + 1)).filter Nat.Prime).card : ℝ) - liPV n| ≤
      √(n : ℝ) * log n / (8 * π))
    (homega : (n.primeFactors.card : ℝ) ≤ 1.3841 * log n / log (log n))
    (hliL : (1 + 1 / log (n : ℝ)) * n / log n ≤ liPV n)
    (hliU : liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n) :
    (n : ℝ) / log n ≤ (U7153.Aset n).card ∧
      ((U7153.Aset n).card : ℝ) ≤ (1 + 5e-5) * n / log n := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hL := log_lower n hn
  have hL0 : 0 < log (n : ℝ) := by linarith
  have hcard : ((U7153.Aset n).card : ℝ) + n.primeFactors.card =
      (((range (n + 1)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast BookkeepingC164.count_identity n hnNat
  obtain ⟨hpiL, hpiU⟩ := abs_le.mp hpi
  have herror := error_budget n hn
  have hAlo : liPV n - 2 * (n : ℝ) / log n ^ 3 ≤ (U7153.Aset n).card := by
    linarith
  have hAhi : ((U7153.Aset n).card : ℝ) ≤ liPV n + 2 * (n : ℝ) / log n ^ 3 := by
    have hω : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
    have hRobin : 0 ≤ 1.3841 * log (n : ℝ) / log (log n) := by
      have : 0 ≤ log (log (n : ℝ)) := log_nonneg (by linarith)
      positivity
    linarith
  have heq : 2 * (n : ℝ) / log n ^ 3 = ((n : ℝ) / log n) * (2 / log n ^ 2) := by
    field_simp
    <;> ring
  have hlow : 2 / log (n : ℝ) ^ 2 ≤ 1 / log n := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    nlinarith
  have hsmall : 1 / log (n : ℝ) + 5 / log n ^ 2 ≤ (5e-5 : ℝ) := by
    have h1 : 1 / log (n : ℝ) ≤ 1 / 22000 := by gcongr
    have h2 : 5 / log (n : ℝ) ^ 2 ≤ 5 / (22000 : ℝ) ^ 2 := by gcongr
    linarith
  have hNdiv : 0 ≤ (n : ℝ) / log n := by positivity
  have hmL := mul_le_mul_of_nonneg_left hlow hNdiv
  have hmU := mul_le_mul_of_nonneg_left hsmall hNdiv
  rw [heq] at hAlo hAhi
  constructor
  · linear_combination hAlo + hliL + hmL
  · linear_combination hAhi + hliU + hmU
end LeanLab.BS2022GRH.Lemma11C164
#print axioms LeanLab.BS2022GRH.Lemma11C164.log_lower
#print axioms LeanLab.BS2022GRH.Lemma11C164.sqrt_large
#print axioms LeanLab.BS2022GRH.Lemma11C164.error_budget
#print axioms LeanLab.BS2022GRH.Lemma11C164.cardinality_bounds
