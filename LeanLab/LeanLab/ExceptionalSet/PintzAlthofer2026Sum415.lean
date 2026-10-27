/-
# Pintz and Althöfer 2026, (4.15), first sum, explicit form

Unit U-1127, T2 FRONTIER, idea I-0080, run 20261019T2303Z-16260.

arXiv 2610.15559v1 (4.15): uniformly for 1 ≤ n ≤ X, Σ_{q≤P} q|c_q(n)|/φ(q)² ≪_η X^η.
Here, explicitly, with an absolute C:

  Σ_{1≤q≤P} q |c_q(n)|/φ(q)² ≤ C e (1 + log P/log 2) τ(n)² (1 + log P),

from |c_q(n)| ≤ (q,n) τ((q,n)), PintzAlthofer2026Ram; q/φ(q) ≤ e(1 + ω(q)) and
ω(q) log 2 ≤ log q, HeathBrown1985/Elementary; τ((q,n)) ≤ τ(n); the gcd sum,
PintzAlthofer2026Gcd; and Σ_{m≤P} 1/φ(m) ≤ C(1 + log P), PNTPort/BV/Helpers. With
τ(n) ≤ C_k n^{1/k}, HeathBrown1985/DivisorEps, and n, P ≤ X this is ≪_η X^η.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Ram
import LeanLab.ExceptionalSet.PintzAlthofer2026Gcd
import LeanLab.HeathBrown1985.Elementary
import LeanLab.PNTPort.BV.Helpers

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Sum415

open Finset

/-- One term: `q|c_q(n)|/φ(q)² ≤ e(1 + log P/log 2) τ(n) (q,n)/φ(q)` for `1 ≤ q ≤ P`. -/
lemma term_le (n P q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) (hqP : q ≤ P) :
    (q : ℝ) * |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 ≤
      Real.exp 1 * (1 + Real.log P / Real.log 2) * (n.divisors.card : ℝ) *
        ((Nat.gcd q n : ℝ) / Nat.totient q) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- q/φ(q) bound
  have h1 := LeanLab.HeathBrown1985.div_totient_le q hq
  have h2 := LeanLab.HeathBrown1985.card_primeFactors_mul_log_two_le q hq
  have hlogq : Real.log q ≤ Real.log P :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqP)
  have hω : (q.primeFactors.card : ℝ) ≤ Real.log P / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  have hqφ : (q : ℝ) / Nat.totient q ≤ Real.exp 1 * (1 + Real.log P / Real.log 2) :=
    h1.trans (by gcongr)
  -- Ramanujan bound
  have hc := LeanLab.ExceptionalSet.PintzAlthofer2026Ram.ramanujan_abs_le_gcd_mul_tau q n
  have hg : n.gcd q = q.gcd n := Nat.gcd_comm n q
  have hτ : ((q.gcd n).divisors.card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd (by omega) (Nat.gcd_dvd_right q n))
  have hc' : |LeanLab.HeathBrown1985.ramanujan q n| ≤ (q.gcd n : ℝ) * n.divisors.card := by
    refine hc.trans ?_
    rw [hg]; push_cast
    exact mul_le_mul_of_nonneg_left hτ (Nat.cast_nonneg _)
  have hE : 0 ≤ Real.exp 1 * (1 + Real.log P / Real.log 2) := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    positivity
  calc (q : ℝ) * |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2
      = ((q : ℝ) / Nat.totient q) * (|LeanLab.HeathBrown1985.ramanujan q n| / Nat.totient q) := by
        field_simp
    _ ≤ (Real.exp 1 * (1 + Real.log P / Real.log 2)) *
          (((q.gcd n : ℝ) * n.divisors.card) / Nat.totient q) := by
        gcongr
    _ = _ := by ring

/-- **(4.15), first sum, explicit**: `Σ_{q≤P} q|c_q(n)|/φ(q)² ≤ C e (1 + log P/log 2) τ(n)² (1 + log P)`. -/
theorem sum415 : ∃ C : ℝ, 0 < C ∧ ∀ n P : ℕ, 1 ≤ n →
    ∑ q ∈ Icc 1 P, (q : ℝ) * |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2 ≤
      C * (Real.exp 1 * (1 + Real.log P / Real.log 2)) * (n.divisors.card : ℝ) ^ 2 *
        (1 + Real.log P) := by
  obtain ⟨C, hC, hsum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨C, hC, fun n P hn => ?_⟩
  have hE : 0 ≤ Real.exp 1 * (1 + Real.log P / Real.log 2) := by
    have : 0 ≤ Real.log P := Real.log_natCast_nonneg P
    have := Real.log_pos one_lt_two
    positivity
  have hτ0 : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
  calc ∑ q ∈ Icc 1 P, (q : ℝ) * |LeanLab.HeathBrown1985.ramanujan q n| / (Nat.totient q : ℝ) ^ 2
      ≤ ∑ q ∈ Icc 1 P, Real.exp 1 * (1 + Real.log P / Real.log 2) * (n.divisors.card : ℝ) *
          ((Nat.gcd q n : ℝ) / Nat.totient q) :=
        sum_le_sum fun q hq => term_le n P q hn (mem_Icc.1 hq).1 (mem_Icc.1 hq).2
    _ = Real.exp 1 * (1 + Real.log P / Real.log 2) * (n.divisors.card : ℝ) *
          ∑ q ∈ Icc 1 P, (Nat.gcd q n : ℝ) / Nat.totient q := by rw [mul_sum]
    _ ≤ Real.exp 1 * (1 + Real.log P / Real.log 2) * (n.divisors.card : ℝ) *
          ((n.divisors.card : ℝ) * (C * (1 + Real.log P))) := by
        gcongr
        exact (LeanLab.ExceptionalSet.PintzAlthofer2026Gcd.sum_gcd_div_totient_le n P hn).trans
          (mul_le_mul_of_nonneg_left (hsum P) hτ0)
    _ = _ := by ring

end LeanLab.ExceptionalSet.PintzAlthofer2026Sum415
