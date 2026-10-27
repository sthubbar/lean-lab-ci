/-
P0080 Hathi 2021, the constant `c_{4,P}` of page 5, a lower bound: **`c₄ ≥ 0.97422`**, so with
C4.lean `0.97422 ≤ c₄ ≤ 0.97428`; true value 0.9742428.
Unit U-6155, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
Head: a rounded-down chain over primes `5 < p < 20001`, last value 974238391930888054 at 10¹⁸.
Tail: factors at `p ≡ 1 mod 4` exceed 1; at `p ≡ 3 mod 4` the log of the factor is at least
`-y/(1 - y)` with `y = (p + 1)²/(p - 1)⁴`, and `y/(1 - y) ≤ (1001/1000)/((p - 1)(p + 3))`, which
telescopes along `p ≡ 3 mod 4`. KNOWN mathematics.
-/
import LeanLab.Hathi2021.C4

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace LeanLab.Hathi2021.C4
open Real Finset

/-- The least `m ≥ n` with `m ≡ 3 mod 4`. -/
def mH3 (n : ℕ) : ℕ := n + (7 - n % 4) % 4

/-- The telescoping minorant scale `T₃(n) = (1001/4000)/(m₃(n) - 1)`. -/
noncomputable def TL (n : ℕ) : ℝ := (1001 / 4000) / ((mH3 n : ℝ) - 1)

lemma TL_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ TL n := by
  unfold TL
  have : (2 : ℝ) ≤ (mH3 n : ℝ) := by unfold mH3; exact_mod_cast (by omega)
  apply div_nonneg (by norm_num); linarith

/-- **The lower tail step.** For `n ≥ 20001`, `-(T₃(n) - T₃(n + 1)) ≤ lH n`. -/
lemma lH_ge_step {n : ℕ} (hn : 20001 ≤ n) : -(TL n - TL (n + 1)) ≤ lH n := by
  have hR : (20001 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases h3 : n % 4 = 3
  · have hm0 : mH3 n = n := by unfold mH3; omega
    have hm1 : mH3 (n + 1) = n + 4 := by unfold mH3; omega
    have hstep : TL n - TL (n + 1) = (1001 / 1000) / (((n : ℝ) - 1) * ((n : ℝ) + 3)) := by
      unfold TL; rw [hm0, hm1]; push_cast
      have h1 : (n : ℝ) - 1 ≠ 0 := by intro h; linarith
      have h2 : (n : ℝ) + 4 - 1 ≠ 0 := by intro h; linarith
      have h3 : (n : ℝ) + 3 ≠ 0 := by intro h; linarith
      field_simp; ring
    rw [hstep]
    have hd1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hS : 0 ≤ (1001 / 1000) / (((n : ℝ) - 1) * ((n : ℝ) + 3)) := by positivity
    unfold lH
    split_ifs with hp
    · have hn5 : 5 < n := by omega
      have hpos := gH_pos hn5
      set y := ((n : ℝ) + 1) ^ 2 / ((n : ℝ) - 1) ^ 4 with hy
      have hg : gH n = 1 - y := by
        unfold gH aH; rw [if_pos h3, hy, neg_div]; ring
      have hd4 : (0 : ℝ) < ((n : ℝ) - 1) ^ 4 := by positivity
      have hy0 : 0 ≤ y := by positivity
      have hy1 : y < 1 := by rw [hg] at hpos; linarith
      have hlo : 1 - (1 - y)⁻¹ ≤ Real.log (1 - y) := Real.one_sub_inv_le_log_of_pos (by linarith)
      have hinv : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
      have hkey : y / (1 - y) ≤ (1001 / 1000) / (((n : ℝ) - 1) * ((n : ℝ) + 3)) := by
        have hden : 0 < ((n : ℝ) - 1) ^ 4 - ((n : ℝ) + 1) ^ 2 := by
          have : y * ((n : ℝ) - 1) ^ 4 = ((n : ℝ) + 1) ^ 2 := by rw [hy]; field_simp
          nlinarith
        have hyq : y / (1 - y) = ((n : ℝ) + 1) ^ 2 / (((n : ℝ) - 1) ^ 4 - ((n : ℝ) + 1) ^ 2) := by
          rw [hy]; field_simp
        rw [hyq, div_le_div_iff₀ hden (by positivity)]
        have ht : (0 : ℝ) ≤ (n : ℝ) - 20001 := by linarith
        have hpoly : (1001 / 1000) * (((n : ℝ) - 1) ^ 4 - ((n : ℝ) + 1) ^ 2) -
            ((n : ℝ) + 1) ^ 2 * (((n : ℝ) - 1) * ((n : ℝ) + 3)) =
            (((n : ℝ) - 20001) ^ 4 + 72000 * ((n : ℝ) - 20001) ^ 3 +
              1919978999 * ((n : ℝ) - 20001) ^ 2 + 22399159939996 * ((n : ℝ) - 20001) +
              95991599199915996) / 1000 := by ring
        have : 0 ≤ (((n : ℝ) - 20001) ^ 4 + 72000 * ((n : ℝ) - 20001) ^ 3 +
              1919978999 * ((n : ℝ) - 20001) ^ 2 + 22399159939996 * ((n : ℝ) - 20001) +
              95991599199915996) / 1000 := by positivity
        linarith
      rw [hg]; linarith
    · linarith
  · have hm : mH3 (n + 1) = mH3 n := by unfold mH3; omega
    rw [show TL (n + 1) = TL n by unfold TL; rw [hm], sub_self, neg_zero]
    unfold lH
    split_ifs with hp
    · have h1 : n % 4 = 1 := by
        rcases hp.1.eq_two_or_odd with h | h <;> omega
      apply Real.log_nonneg
      unfold gH aH; rw [if_neg (by omega)]
      have : (0 : ℝ) ≤ (3 * (n : ℝ) + 1) * ((n : ℝ) - 1) / ((n : ℝ) - 1) ^ 4 := by
        apply div_nonneg _ (by positivity)
        apply mul_nonneg <;> linarith
      linarith
    · exact le_refl 0

/-- **The lower tail.** `∑_{n ≥ 20001} lH n ≥ -(1001/4000)/20002`. -/
lemma tail_ge : -((1001 / 4000) / 20002) ≤ ∑' k, lH (k + 20001) := by
  have hs : Summable (fun k => lH (k + 20001)) := (summable_nat_add_iff 20001).mpr summable_lH
  have hn : ∑' k, -lH (k + 20001) ≤ (1001 / 4000) / 20002 := by
    refine hs.neg.tsum_le_of_sum_range_le fun K => ?_
    calc ∑ k ∈ range K, -lH (k + 20001) ≤ ∑ k ∈ range K, (TL (k + 20001) - TL (k + 1 + 20001)) := by
          apply sum_le_sum; intro k _
          have := lH_ge_step (n := k + 20001) (by omega)
          rw [show k + 20001 + 1 = k + 1 + 20001 by ring] at this
          linarith
      _ = TL (0 + 20001) - TL (K + 20001) := sum_range_sub' (fun k => TL (k + 20001)) K
      _ ≤ TL 20001 := by have := TL_nonneg (n := K + 20001) (by omega); simp; linarith
      _ = (1001 / 4000) / 20002 := by
          unfold TL; rw [show mH3 20001 = 20003 by unfold mH3; norm_num]; norm_num
  rw [tsum_neg] at hn
  linarith

/-- One rounded-down step. -/
def stepD (a n : ℕ) : ℕ := if primeB n && decide (5 < n) then a * numN n / denN n else a

/-- The rounded-down chain. -/
def chainD : ℕ → ℕ
  | 0 => 10 ^ 18
  | n + 1 => stepD (chainD n) n

lemma stepD_le {a n : ℕ} (hn : 5 < n) : ((a * numN n / denN n : ℕ) : ℝ) ≤ (a : ℝ) * gH n := by
  have hq1 : 0 < denN n := by unfold denN; exact pow_pos (by omega) 4
  have hdiv : a * numN n / denN n * denN n ≤ a * numN n := Nat.div_mul_le_self _ _
  rw [gH_eq hn]
  have hqpos : (0 : ℝ) < denN n := by exact_mod_cast hq1
  rw [mul_div_assoc', le_div_iff₀ hqpos]
  exact_mod_cast hdiv

theorem chainD_bound (n : ℕ) :
    (chainD n : ℝ) ≤ ((10 ^ 18 : ℕ) : ℝ) * ∏ k ∈ (range n).filter (fun k => k.Prime ∧ 5 < k), gH k := by
  induction n with
  | zero => simp [chainD]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : n.Prime ∧ 5 < n
    · rw [if_pos h, Finset.prod_insert (by simp)]
      have hstep : stepD (chainD n) n = chainD n * numN n / denN n := by
        unfold stepD; rw [if_pos (by simp [(primeB_iff n).mpr h.1, h.2])]
      simp only [chainD, hstep]
      calc ((chainD n * numN n / denN n : ℕ) : ℝ) ≤ (chainD n : ℝ) * gH n := stepD_le h.2
        _ ≤ (((10 ^ 18 : ℕ) : ℝ) * ∏ k ∈ (range n).filter (fun k => k.Prime ∧ 5 < k), gH k) * gH n :=
            mul_le_mul_of_nonneg_right ih (gH_pos h.2).le
        _ = _ := by ring
    · rw [if_neg h]
      have hstep : stepD (chainD n) n = chainD n := by
        unfold stepD; rw [if_neg]; intro hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        exact h ⟨(primeB_iff n).mp hb.1, hb.2⟩
      simp only [chainD, hstep]
      exact ih

theorem chainD_last : chainD 20001 = 974238391930888054 := by decide +kernel

/-- **`c₄ ≥ 0.97422`.** Zero sorry. With `c4_le_97428`, `0.97422 ≤ c₄ ≤ 0.97428`. -/
theorem c4_ge_97422 : (97422 / 100000 : ℝ) ≤ c4 := by
  rw [c4_eq_exp, ← summable_lH.sum_add_tsum_nat_add 20001, Real.exp_add, exp_head]
  set P := ∏ n ∈ (range 20001).filter (fun n => n.Prime ∧ 5 < n), gH n with hP
  have hc := chainD_bound 20001
  rw [chainD_last, ← hP] at hc
  have hPge : (974238391930888054 : ℝ) / 10 ^ 18 ≤ P := by
    rw [div_le_iff₀ (by positivity), mul_comm]; push_cast at hc; linarith
  have he : 1 - (1001 / 4000) / 20002 ≤ Real.exp (∑' k, lH (k + 20001)) := by
    have := Real.add_one_le_exp (∑' k, lH (k + 20001))
    have := tail_ge
    linarith
  calc (97422 / 100000 : ℝ) ≤ (974238391930888054 : ℝ) / 10 ^ 18 * (1 - (1001 / 4000) / 20002) := by
        norm_num
    _ ≤ P * Real.exp (∑' k, lH (k + 20001)) :=
        mul_le_mul hPge he (by norm_num) (le_trans (by norm_num) hPge)

end LeanLab.Hathi2021.C4
