/-
P0041 Sinisalo 1993: the Richstein2001 log machinery with arbitrary rational bounds, for the
three-decimal columns of Sinisalo's Table 1. q2 = p(n) / (log² n log log n) by rowOKq, and
q1 = log n / (log p(n))² by q1OK. Run 20261018T1103Z-12430, unit U-0940.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Richstein2001.LogBounds

namespace LeanLab.Sinisalo1993

open LeanLab.Richstein2001

/-- Row checks with arbitrary rational bounds lo, hi.  log n lies in (k1 + f1, k2 + f2), log log n in
(j1 + g1, j2 + g2), and the printed c, times 10^-4, is the ratio to within half a unit. -/
def rowOKq (n p : ℕ) (lo hi : ℚ) (k1 : ℕ) (f1 : ℚ) (k2 : ℕ) (f2 : ℚ) (j1 : ℕ) (g1 : ℚ) (j2 : ℕ) (g2 : ℚ)
    (N : ℕ) : Bool :=
  decide (0 < N) && decide (0 ≤ f1) && decide (f1 ≤ 1) && decide (0 ≤ f2) &&
  decide (0 ≤ g1) && decide (g1 ≤ 1) && decide (0 ≤ g2) && decide (0 < (j1 : ℚ) + g1) &&
  decide (expHiQ k1 f1 N < n) && decide ((n : ℚ) < expLoQ k2 f2 N) &&
  decide (expHiQ j1 g1 N < (k1 : ℚ) + f1) && decide ((k2 : ℚ) + f2 < expLoQ j2 g2 N) &&
  decide (lo ≤ (p : ℚ) / (((k2 : ℚ) + f2) ^ 2 * ((j2 : ℚ) + g2))) &&
  decide ((p : ℚ) / (((k1 : ℚ) + f1) ^ 2 * ((j1 : ℚ) + g1)) < hi)

theorem rowOKq_sound {n p k1 k2 j1 j2 N : ℕ} {lo hi f1 f2 g1 g2 : ℚ} (hp : 0 < p)
    (h : rowOKq n p lo hi k1 f1 k2 f2 j1 g1 j2 g2 N = true) :
    ((lo : ℚ) : ℝ) ≤ ratio n p ∧ ratio n p < ((hi : ℚ) : ℝ) := by
  simp only [rowOKq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hf10⟩, hf11⟩, hf20⟩, hg10⟩, hg11⟩, hg20⟩, hM1⟩, hA⟩, hB⟩, hC⟩, hD⟩,
    hE⟩, hF⟩ := h
  -- log n bounds
  have hA' : Real.exp ((k1 : ℝ) + (f1 : ℝ)) < (n : ℝ) :=
    lt_of_le_of_lt (le_expHiQ k1 f1 N hf10 hf11 hN) (by exact_mod_cast hA)
  have hB' : (n : ℝ) < Real.exp ((k2 : ℝ) + (f2 : ℝ)) :=
    lt_of_lt_of_le (by exact_mod_cast hB) (expLoQ_le k2 f2 N hf20)
  have hn : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hA'
  have hL1 : (k1 : ℝ) + f1 < Real.log n := (Real.lt_log_iff_exp_lt hn).mpr hA'
  have hL2 : Real.log n < (k2 : ℝ) + f2 := (Real.log_lt_iff_lt_exp hn).mpr hB'
  have hC' : Real.exp ((j1 : ℝ) + (g1 : ℝ)) < (k1 : ℝ) + f1 := by
    have := lt_of_le_of_lt (le_expHiQ j1 g1 N hg10 hg11 hN)
      (show ((expHiQ j1 g1 N : ℚ) : ℝ) < ((((k1 : ℚ) + f1) : ℚ) : ℝ) by exact_mod_cast hC)
    push_cast at this; exact this
  have hD' : (k2 : ℝ) + f2 < Real.exp ((j2 : ℝ) + (g2 : ℝ)) := by
    have := lt_of_lt_of_le
      (show ((((k2 : ℚ) + f2) : ℚ) : ℝ) < ((expLoQ j2 g2 N : ℚ) : ℝ) by exact_mod_cast hD)
      (expLoQ_le j2 g2 N hg20)
    push_cast at this; exact this
  have hL1pos : (0 : ℝ) < (k1 : ℝ) + f1 := lt_trans (Real.exp_pos _) hC'
  have hlogpos : 0 < Real.log n := lt_trans hL1pos hL1
  have hM1' : (j1 : ℝ) + g1 < Real.log (Real.log n) :=
    (Real.lt_log_iff_exp_lt hlogpos).mpr (lt_trans hC' hL1)
  have hM2' : Real.log (Real.log n) < (j2 : ℝ) + g2 :=
    (Real.log_lt_iff_lt_exp hlogpos).mpr (lt_trans hL2 hD')
  have hM1pos : (0 : ℝ) < (j1 : ℝ) + g1 := by exact_mod_cast hM1
  have hllpos : 0 < Real.log (Real.log n) := lt_trans hM1pos hM1'
  -- denominators
  have hden_lo : ((k1 : ℝ) + f1) ^ 2 * ((j1 : ℝ) + g1) < Real.log n ^ 2 * Real.log (Real.log n) :=
    mul_lt_mul'' (pow_lt_pow_left₀ hL1 hL1pos.le (by norm_num)) hM1' (by positivity) hM1pos.le
  have hden_hi : Real.log n ^ 2 * Real.log (Real.log n) < ((k2 : ℝ) + f2) ^ 2 * ((j2 : ℝ) + g2) :=
    mul_lt_mul'' (pow_lt_pow_left₀ hL2 hlogpos.le (by norm_num)) hM2' (by positivity) hllpos.le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hdpos : 0 < Real.log n ^ 2 * Real.log (Real.log n) := by positivity
  unfold ratio
  constructor
  · have hE' : ((lo : ℚ) : ℝ) ≤
        (p : ℝ) / (((k2 : ℝ) + f2) ^ 2 * ((j2 : ℝ) + g2)) := by
      have := (show ((lo : ℚ) : ℝ) ≤
        ((((p : ℚ) / (((k2 : ℚ) + f2) ^ 2 * ((j2 : ℚ) + g2))) : ℚ) : ℝ) by exact_mod_cast hE)
      push_cast at this ⊢; exact this
    exact le_trans hE' (div_le_div_of_nonneg_left hpR.le hdpos hden_hi.le)
  · have hF' : (p : ℝ) / (((k1 : ℝ) + f1) ^ 2 * ((j1 : ℝ) + g1)) <
        ((hi : ℚ) : ℝ) := by
      have := (show ((((p : ℚ) / (((k1 : ℚ) + f1) ^ 2 * ((j1 : ℚ) + g1))) : ℚ) : ℝ) <
        ((hi : ℚ) : ℝ) by exact_mod_cast hF)
      push_cast at this ⊢; exact this
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left hpR.le (by positivity) hden_lo.le) hF'


/-- Table 1 first quotient, log n / (log p)². -/
noncomputable def quot1 (n p : ℕ) : ℝ := Real.log n / Real.log p ^ 2

theorem log_bracket {x : ℝ} {k1 k2 N : ℕ} {f1 f2 : ℚ} (hN : 0 < N) (hf10 : 0 ≤ f1)
    (hf11 : f1 ≤ 1) (hf20 : 0 ≤ f2) (hA : ((expHiQ k1 f1 N : ℚ) : ℝ) < x)
    (hB : x < ((expLoQ k2 f2 N : ℚ) : ℝ)) :
    (k1 : ℝ) + f1 < Real.log x ∧ Real.log x < (k2 : ℝ) + f2 := by
  have hA' : Real.exp ((k1 : ℝ) + (f1 : ℝ)) < x := lt_of_le_of_lt (le_expHiQ k1 f1 N hf10 hf11 hN) hA
  have hB' : x < Real.exp ((k2 : ℝ) + (f2 : ℝ)) := lt_of_lt_of_le hB (expLoQ_le k2 f2 N hf20)
  have hx : 0 < x := lt_trans (Real.exp_pos _) hA'
  exact ⟨(Real.lt_log_iff_exp_lt hx).mpr hA', (Real.log_lt_iff_lt_exp hx).mpr hB'⟩

def q1OK (n p : ℕ) (lo hi : ℚ) (k1 : ℕ) (f1 : ℚ) (k2 : ℕ) (f2 : ℚ) (a1 : ℕ) (e1 : ℚ) (a2 : ℕ)
    (e2 : ℚ) (N : ℕ) : Bool :=
  decide (0 < N) && decide (0 ≤ f1) && decide (f1 ≤ 1) && decide (0 ≤ f2) &&
  decide (0 ≤ e1) && decide (e1 ≤ 1) && decide (0 ≤ e2) && decide (0 < (a1 : ℚ) + e1) &&
  decide (expHiQ k1 f1 N < n) && decide ((n : ℚ) < expLoQ k2 f2 N) &&
  decide (expHiQ a1 e1 N < p) && decide ((p : ℚ) < expLoQ a2 e2 N) &&
  decide (lo ≤ ((k1 : ℚ) + f1) / ((a2 : ℚ) + e2) ^ 2) &&
  decide (((k2 : ℚ) + f2) / ((a1 : ℚ) + e1) ^ 2 < hi)

theorem q1OK_sound {n p k1 k2 a1 a2 N : ℕ} {lo hi f1 f2 e1 e2 : ℚ}
    (h : q1OK n p lo hi k1 f1 k2 f2 a1 e1 a2 e2 N = true) :
    ((lo : ℚ) : ℝ) ≤ quot1 n p ∧ quot1 n p < ((hi : ℚ) : ℝ) := by
  simp only [q1OK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hf10⟩, hf11⟩, hf20⟩, he10⟩, he11⟩, he20⟩, hP1⟩, hA⟩, hB⟩, hC⟩, hD⟩,
    hE⟩, hF⟩ := h
  obtain ⟨hL1, hL2⟩ := log_bracket (x := (n : ℝ)) hN hf10 hf11 hf20 (by exact_mod_cast hA)
    (by exact_mod_cast hB)
  obtain ⟨hP1', hP2'⟩ := log_bracket (x := (p : ℝ)) hN he10 he11 he20 (by exact_mod_cast hC)
    (by exact_mod_cast hD)
  have hP1pos : (0 : ℝ) < (a1 : ℝ) + e1 := by exact_mod_cast hP1
  have hlp : 0 < Real.log p := lt_trans hP1pos hP1'
  have hL1pos : (0 : ℝ) ≤ (k1 : ℝ) + f1 := by positivity
  have hE' : ((lo : ℚ) : ℝ) ≤ ((k1 : ℝ) + f1) / ((a2 : ℝ) + e2) ^ 2 := by
    have := (show ((lo : ℚ) : ℝ) ≤ ((((k1 : ℚ) + f1) / ((a2 : ℚ) + e2) ^ 2 : ℚ) : ℝ) by
      exact_mod_cast hE)
    push_cast at this; exact this
  have hF' : ((k2 : ℝ) + f2) / ((a1 : ℝ) + e1) ^ 2 < ((hi : ℚ) : ℝ) := by
    have := (show ((((k2 : ℚ) + f2) / ((a1 : ℚ) + e1) ^ 2 : ℚ) : ℝ) < ((hi : ℚ) : ℝ) by
      exact_mod_cast hF)
    push_cast at this; exact this
  unfold quot1
  constructor
  · refine le_trans hE' ?_
    calc ((k1 : ℝ) + f1) / ((a2 : ℝ) + e2) ^ 2 ≤ Real.log n / ((a2 : ℝ) + e2) ^ 2 :=
          div_le_div_of_nonneg_right hL1.le (by positivity)
      _ ≤ Real.log n / Real.log p ^ 2 := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          exact pow_le_pow_left₀ hlp.le hP2'.le 2
  · refine lt_of_le_of_lt ?_ hF'
    calc Real.log n / Real.log p ^ 2 ≤ ((k2 : ℝ) + f2) / Real.log p ^ 2 :=
          div_le_div_of_nonneg_right hL2.le (by positivity)
      _ ≤ ((k2 : ℝ) + f2) / ((a1 : ℝ) + e1) ^ 2 := by
          apply div_le_div_of_nonneg_left (by linarith) (by positivity)
          exact pow_le_pow_left₀ hP1pos.le hP1'.le 2

end LeanLab.Sinisalo1993
