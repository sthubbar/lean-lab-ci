/- AI wrote this Lean code for CODEX task169.
Quotient sieve levels in Theorem 6, journal pp. 1232 and 1233. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169b

namespace LeanLab.BS2022GRH.QuotientC169
open Real Finset Classical DecompC169b

/-- The explicit value of s_q in the proof of Theorem 6, p. 1233. -/
theorem parameter_eq (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n) (hq : 0 < q) :
    quotientParameter n q α = 8 * (1 / 2 - α - log q / log n) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : log (n : ℝ) ≠ 0 := (log_pos hn).ne'
  unfold quotientParameter quotientLevel U7153.zz
  rw [log_div (rpow_pos_of_pos hn0 _).ne' hq0.ne', log_rpow hn0, log_rpow hn0]
  field_simp
  <;> ring

/-- The quotient sieve parameter lies strictly between one and three, p. 1233. -/
theorem parameter_bounds (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hq : q ∈ qRange n) :
    1 < quotientParameter n q α ∧ quotientParameter n q α < 3 := by
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hqQ, _⟩ := mem_filter.mp hq
  obtain ⟨_, hprime, hqz, hqy⟩ := mem_filter.mp hqQ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hL : 0 < log (n : ℝ) := log_pos hn
  have hlo : (1 / 8 : ℝ) * log n ≤ log q := by
    rw [← log_rpow hn0]
    exact log_le_log (rpow_pos_of_pos hn0 _) hqz
  have hhi : log q < (1 / 3 : ℝ) * log n := by
    rw [← log_rpow hn0]
    exact log_lt_log hq0 hqy
  have hfraclo : (1 / 8 : ℝ) ≤ log q / log n := (le_div_iff₀ hL).mpr hlo
  have hfrachi : log q / log n < (1 / 3 : ℝ) := (div_lt_iff₀ hL).mpr hhi
  rw [parameter_eq n q α hn hprime.pos]
  constructor <;> linarith

/-- D_q exceeds z under the quotient sieve hypotheses, p. 1232 display 22. -/
theorem level_gt_z (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hq : q ∈ qRange n) :
    U7153.zz n < quotientLevel n q α := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hprime := (mem_filter.mp (mem_filter.mp hq).1).2.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
  have hD0 : 0 < quotientLevel n q α := div_pos (rpow_pos_of_pos hn0 _) hq0
  have hLz : 0 < log (U7153.zz n) := by
    rw [U7153.zz, log_rpow hn0]
    exact mul_pos (by norm_num) (log_pos hn)
  have hparam := (parameter_bounds n q α hn hα hα1 hq).1
  unfold quotientParameter at hparam
  have hlog := (lt_div_iff₀ hLz).mp hparam
  have hexp := exp_lt_exp.mpr (by simpa using hlog)
  simpa only [exp_log hz0, exp_log hD0] using hexp

end LeanLab.BS2022GRH.QuotientC169

#print axioms LeanLab.BS2022GRH.QuotientC169.parameter_eq
#print axioms LeanLab.BS2022GRH.QuotientC169.parameter_bounds
#print axioms LeanLab.BS2022GRH.QuotientC169.level_gt_z
