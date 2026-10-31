/-
P0017 Richstein 2001: machinery for the third column of Table 1, p(n) / (log² n log log n).
Rational upper and lower bounds for exp from e between 2.7182818283 and 2.7182818286 and the
Taylor series with Mathlib's remainder bound; then one Boolean check per row whose truth
places the printed four decimals. Run 20261018T1103Z-12430, unit U-0937.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Richstein2001

/-- Partial Taylor sum of exp, ∑_{i < N} f^i / i!. -/
def tsum (f : ℚ) : ℕ → ℚ
  | 0 => 0
  | N + 1 => tsum f N + f ^ N / (N.factorial : ℚ)

theorem tsum_cast (f : ℚ) (N : ℕ) :
    ((tsum f N : ℚ) : ℝ) = ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) := by
  induction N with
  | zero => simp [tsum]
  | succ N ih => rw [tsum, Finset.sum_range_succ, ← ih]; push_cast; ring

def eLo : ℚ := 27182818283 / 10 ^ 10
def eHi : ℚ := 27182818286 / 10 ^ 10

/-- Lower bound for exp (k + f). -/
def expLoQ (k : ℕ) (f : ℚ) (N : ℕ) : ℚ := eLo ^ k * tsum f N

/-- Upper bound for exp (k + f), 0 ≤ f ≤ 1. -/
def expHiQ (k : ℕ) (f : ℚ) (N : ℕ) : ℚ :=
  eHi ^ k * (tsum f N + f ^ N * ((N + 1 : ℕ) : ℚ) / ((N.factorial : ℚ) * (N : ℚ)))

theorem exp_split (k : ℕ) (f : ℝ) : Real.exp (k + f) = Real.exp 1 ^ k * Real.exp f := by
  rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]

theorem expLoQ_le (k : ℕ) (f : ℚ) (N : ℕ) (h0 : 0 ≤ f) :
    ((expLoQ k f N : ℚ) : ℝ) ≤ Real.exp (k + f) := by
  rw [exp_split]
  unfold expLoQ
  push_cast
  rw [tsum_cast]
  have hf : (0 : ℝ) ≤ f := by exact_mod_cast h0
  have h1 : ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) ≤ Real.exp f :=
    Real.sum_le_exp_of_nonneg hf N
  have he : ((eLo : ℚ) : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    unfold eLo; push_cast; linarith
  have hs : 0 ≤ ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hk : ((eLo : ℚ) : ℝ) ^ k ≤ Real.exp 1 ^ k :=
    pow_le_pow_left₀ (by unfold eLo; norm_num) he k
  calc ((eLo : ℚ) : ℝ) ^ k * ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ)
      ≤ Real.exp 1 ^ k * ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right hk hs
    _ ≤ Real.exp 1 ^ k * Real.exp f :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (Real.exp_pos 1).le k)

theorem le_expHiQ (k : ℕ) (f : ℚ) (N : ℕ) (h0 : 0 ≤ f) (h1 : f ≤ 1) (hN : 0 < N) :
    Real.exp (k + f) ≤ ((expHiQ k f N : ℚ) : ℝ) := by
  rw [exp_split]
  unfold expHiQ
  push_cast
  rw [tsum_cast]
  have hf0 : (0 : ℝ) ≤ f := by exact_mod_cast h0
  have hf1 : (f : ℝ) ≤ 1 := by exact_mod_cast h1
  have hb := Real.exp_bound (x := (f : ℝ)) (by rw [abs_of_nonneg hf0]; exact hf1) hN
  rw [abs_of_nonneg hf0] at hb
  have hx : Real.exp f ≤ ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) +
      (f : ℝ) ^ N * ((N + 1 : ℝ) / ((N.factorial : ℝ) * (N : ℝ))) := by
    have := (abs_le.mp hb).2
    push_cast [Nat.succ_eq_add_one] at this
    linarith
  have he : Real.exp 1 ≤ ((eHi : ℚ) : ℝ) := by
    have := Real.exp_one_lt_d9
    unfold eHi; push_cast; linarith
  have hk : Real.exp 1 ^ k ≤ ((eHi : ℚ) : ℝ) ^ k :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he k
  have hpos : 0 ≤ ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) +
      (f : ℝ) ^ N * ((N + 1 : ℝ) / ((N.factorial : ℝ) * (N : ℝ))) := by
    have : 0 ≤ ∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    positivity
  calc Real.exp 1 ^ k * Real.exp f
      ≤ Real.exp 1 ^ k * (∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) +
          (f : ℝ) ^ N * ((N + 1 : ℝ) / ((N.factorial : ℝ) * (N : ℝ)))) :=
        mul_le_mul_of_nonneg_left hx (pow_nonneg (Real.exp_pos 1).le k)
    _ ≤ ((eHi : ℚ) : ℝ) ^ k * (∑ i ∈ Finset.range N, (f : ℝ) ^ i / (i.factorial : ℝ) +
          (f : ℝ) ^ N * ((N + 1 : ℝ) / ((N.factorial : ℝ) * (N : ℝ)))) :=
        mul_le_mul_of_nonneg_right hk hpos
    _ = _ := by ring

/-- The quantity in Table 1's third column. -/
noncomputable def ratio (n p : ℕ) : ℝ := (p : ℝ) / (Real.log n ^ 2 * Real.log (Real.log n))

/-- All rational checks for one row. log n lies in (k1 + f1, k2 + f2), log log n in
(j1 + g1, j2 + g2), and the printed c, times 10^-4, is the ratio to within half a unit. -/
def rowOK (n p c : ℕ) (k1 : ℕ) (f1 : ℚ) (k2 : ℕ) (f2 : ℚ) (j1 : ℕ) (g1 : ℚ) (j2 : ℕ) (g2 : ℚ)
    (N : ℕ) : Bool :=
  decide (0 < N) && decide (0 ≤ f1) && decide (f1 ≤ 1) && decide (0 ≤ f2) &&
  decide (0 ≤ g1) && decide (g1 ≤ 1) && decide (0 ≤ g2) && decide (0 < (j1 : ℚ) + g1) &&
  decide (expHiQ k1 f1 N < n) && decide ((n : ℚ) < expLoQ k2 f2 N) &&
  decide (expHiQ j1 g1 N < (k1 : ℚ) + f1) && decide ((k2 : ℚ) + f2 < expLoQ j2 g2 N) &&
  decide (((2 * c - 1 : ℕ) : ℚ) / (2 * 10 ^ 4) ≤ (p : ℚ) / (((k2 : ℚ) + f2) ^ 2 * ((j2 : ℚ) + g2))) &&
  decide ((p : ℚ) / (((k1 : ℚ) + f1) ^ 2 * ((j1 : ℚ) + g1)) < ((2 * c + 1 : ℕ) : ℚ) / (2 * 10 ^ 4))

theorem rowOK_sound {n p c k1 k2 j1 j2 N : ℕ} {f1 f2 g1 g2 : ℚ} (hc : 1 ≤ c) (hp : 0 < p)
    (h : rowOK n p c k1 f1 k2 f2 j1 g1 j2 g2 N = true) :
    ((2 * c - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio n p ∧
    ratio n p < ((2 * c + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
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
  · have hE' : ((2 * c - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤
        (p : ℝ) / (((k2 : ℝ) + f2) ^ 2 * ((j2 : ℝ) + g2)) := by
      have := (show ((((2 * c - 1 : ℕ) : ℚ) / (2 * 10 ^ 4) : ℚ) : ℝ) ≤
        ((((p : ℚ) / (((k2 : ℚ) + f2) ^ 2 * ((j2 : ℚ) + g2))) : ℚ) : ℝ) by exact_mod_cast hE)
      push_cast at this ⊢; exact this
    exact le_trans hE' (div_le_div_of_nonneg_left hpR.le hdpos hden_hi.le)
  · have hF' : (p : ℝ) / (((k1 : ℝ) + f1) ^ 2 * ((j1 : ℝ) + g1)) <
        ((2 * c + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) := by
      have := (show ((((p : ℚ) / (((k1 : ℚ) + f1) ^ 2 * ((j1 : ℚ) + g1))) : ℚ) : ℝ) <
        ((((2 * c + 1 : ℕ) : ℚ) / (2 * 10 ^ 4) : ℚ) : ℝ) by exact_mod_cast hF)
      push_cast at this ⊢; exact this
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left hpR.le (by positivity) hden_lo.le) hF'

end LeanLab.Richstein2001
