/-
AI wrote this Lean code for CODEX task105.
P0004 page 21 Lemma 10 equation 2.91.
An elementary logarithmic lower bound for Euler's totient.
Binary Goldbach is OPEN.
-/
import LeanLab.PNTPort.BV.Helpers
import LeanLab.HardyLittlewood1923.U1463ThmA

namespace LeanLab.HardyLittlewood1923.Decomp105b

open Finset Real
open LeanLab.PNTPort.BV

/-- LEAF. The ratio q over phi q is bounded by the sum of reciprocal totients up to q.
P0004 page 21 equation 2.91, an elementary divisor sum proof. -/
theorem ratio_le_sum {q : ℕ} (hq : 1 ≤ q) :
    (q : ℝ) / q.totient ≤ ∑ d ∈ Icc 1 q, (1 : ℝ) / d.totient := by
  have hq0 : q ≠ 0 := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  calc (q : ℝ) / q.totient = ∑ d ∈ q.divisors, sqfTot d := by
        calc (q : ℝ) / q.totient = (q : ℝ) * (1 / q.totient) := by ring
          _ = (q : ℝ) * ((1 / q) * ∑ d ∈ q.divisors, sqfTot d) := by rw [inv_totient_eq hq0]
          _ = _ := by field_simp
    _ ≤ ∑ d ∈ Icc 1 q, sqfTot d := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hdq, _⟩ := Nat.mem_divisors.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd (by omega) hdq⟩
      · intro d _ _
        exact sqfTot_nonneg d
    _ ≤ ∑ d ∈ Icc 1 q, (1 : ℝ) / d.totient :=
      sum_le_sum fun d _ => sqfTot_le d

/-- CITED. P0004 page 21 Lemma 10 equation 2.91, with logarithmic exponent one.
There is a positive c with phi q strictly greater than c q over log q for q at least three.
This suffices for the unspecified logarithmic power in the paper. -/
theorem lemma10 : ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 3 ≤ q →
    c * (q : ℝ) / Real.log q < q.totient := by
  obtain ⟨C, hC, hsum⟩ := sum_inv_totient_le
  refine ⟨1 / (4 * C), by positivity, fun q hq => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hlog : 1 ≤ Real.log q := U1463.one_le_log_of_three hq
  have hrat : (q : ℝ) / q.totient ≤ 2 * C * Real.log q := by
    refine ((ratio_le_sum (by omega)).trans (hsum q)).trans ?_
    nlinarith
  have hqbound : (q : ℝ) ≤ 2 * C * Real.log q * q.totient :=
    (div_le_iff₀ hphi).mp hrat
  apply (div_lt_iff₀ (by linarith : 0 < Real.log q)).mpr
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_lt_iff₀ (by positivity : 0 < 4 * C)).mpr
  nlinarith [mul_pos (mul_pos hC (by linarith : 0 < Real.log q)) hphi]

#print axioms ratio_le_sum
#print axioms lemma10

end LeanLab.HardyLittlewood1923.Decomp105b
