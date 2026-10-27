/-
AI-written Lean code, Claude, 2026-10-21, run 20261021T0103Z-19411, unit U-1313.
Correctly labelled Rosser-Schoenfeld 1962 inputs for P0048 Dudek-Dunn.
Source: J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime
numbers, Illinois J. Math. 6 (1962), Theorem 5, p. 70, with B = 0.26149 72128 47643, their (2.10):
* (3.18)  `Σ_{p ≤ x} 1/p < log log x + B + 1/(2 log² x)`  for `286 ≤ x`;
* (3.20)  `Σ_{p ≤ x} 1/p < log log x + B + 1/log² x`      for `1 < x`.
VERIFY U-1309 found that `RSRecipRed.RS320` has the form of (3.18), not (3.20). This file does
not touch RSRecip.lean; it adds `RS318` and `RS320true` and re-derives the chain from them.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.RSRecip

open Real Finset
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDMain

noncomputable section
namespace LeanLab.AlmostPrimes.RS1962

/-- The prime reciprocal sum `Σ_{p ≤ x} 1/p`. -/
def primeRecipSum (x : ℝ) : ℝ := ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p

/-- **Rosser-Schoenfeld 1962, Theorem 5, eq (3.20), p. 70.**
Plain math: for every real `x > 1`, `Σ_{p ≤ x} 1/p < log log x + B + 1/log² x`.
Here `B` is a parameter; the published statement is `RS320true B₀` with `B₀ = 0.2614972128...`,
and every theorem below assumes only `B < 0.2614973`. Cited. -/
def RS320true (B : ℝ) : Prop := ∀ x : ℝ, 1 < x →
  primeRecipSum x < log (log x) + B + 1 / log x ^ 2

/-- **Rosser-Schoenfeld 1962, Theorem 5, eq (3.18), p. 70.**
Plain math: for every real `x ≥ 286`, `Σ_{p ≤ x} 1/p < log log x + B + 1/(2 log² x)`. Cited. -/
def RS318 (B : ℝ) : Prop := ∀ x : ℝ, 286 ≤ x →
  primeRecipSum x < log (log x) + B + 1 / (2 * log x ^ 2)

/-- `log 10 > 2.3024`, from `2^10 = 1024 = 1000 · 1.024`, `log 2 > 0.6931471803` and
`log 1.024 ≤ 0.024`. -/
theorem log_ten_gt : (2.3024 : ℝ) < log 10 := by
  have h1 : log (1024 : ℝ) = 10 * log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have h2 : log (1000 : ℝ) = 3 * log 10 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h3 : log (1024 : ℝ) = log 1000 + log 1.024 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h4 : log (1.024 : ℝ) ≤ 1.024 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h5 := Real.log_two_gt_d9
  linarith

/-- `log z > 23.02` for `z ≥ 10^10`. -/
theorem log_gt_2302 {z : ℝ} (hz : 10 ^ 10 ≤ z) : (23.02 : ℝ) < log z := by
  have hmono : log ((10 : ℝ) ^ 10) ≤ log z := Real.log_le_log (by positivity) hz
  rw [Real.log_pow] at hmono
  have := log_ten_gt
  push_cast at hmono
  linarith

/-- `1/log² z < 0.00189` for `z ≥ 10^10`. -/
theorem inv_log_sq_lt {z : ℝ} (hz : 10 ^ 10 ≤ z) : 1 / log z ^ 2 < 0.00189 := by
  have hL := log_gt_2302 hz
  have hL2 : (529.92 : ℝ) < log z ^ 2 := by nlinarith
  have : 1 / log z ^ 2 < 1 / 529.92 := one_div_lt_one_div_of_lt (by norm_num) hL2
  have h' : (1 : ℝ) / 529.92 < 0.00189 := by norm_num
  linarith

/-- **(3.18) implies the lab's `RS320`**, PROVED for any `B < 0.2614973`. -/
theorem RS320_of_RS318 {B : ℝ} (hB : B < 0.2614973) (h : RS318 B) : RSRecipRed.RS320 := by
  intro x hx
  have := h x (by linarith)
  unfold primeRecipSum at this
  linarith

/-- **(3.20) implies Dudek-Dunn's `RSRecip`**: `Σ_{p < z} 1/p < log log z + 0.2634`,
`z ≥ 10^10`, since `0.2614973 + 0.00189 < 0.2634`. PROVED for any `B < 0.2614973`. -/
theorem RSRecip_of_RS320true {B : ℝ} (hB : B < 0.2614973) (h : RS320true B) : RSRecip := by
  intro z hz
  have hle : ∑ p ∈ primesIn 2 z, (1 : ℝ) / p ≤ primeRecipSum z :=
    sum_le_sum_of_subset_of_nonneg (RSRecipRed.primesIn_subset z) (fun p _ _ => by positivity)
  have hRS := h z (by linarith)
  have hs := inv_log_sq_lt hz
  linarith

/-- **(3.18) implies `RSRecip`**, through the lab's `RS320`. -/
theorem RSRecip_of_RS318 {B : ℝ} (hB : B < 0.2614973) (h : RS318 B) : RSRecip :=
  RSRecipRed.RSRecip_of_RS320 (RS320_of_RS318 hB h)

/-- **Theorem 3.3 for `N ≥ 10^200`**, Dudek-Dunn. CONDITIONAL ON `RSHyp`, `RS320true B` with
`B < 0.2614973`, `SelbergThm13`. -/
theorem theorem3_3_large_of_RS3 (hRS : DDLemma21All.RSHyp) {B : ℝ} (hB : B < 0.2614973)
    (h320 : RS320true B) (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  DDNathanson.theorem3_3_large_of_RS hRS (RSRecip_of_RS320true hB h320) hSel N hN

/-- **Theorem 1.2**, Dudek-Dunn. CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RSHyp`,
`RS320true B` with `B < 0.2614973`, `SelbergThm13`. -/
theorem theorem1_2_of_RS3 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) {B : ℝ} (hB : B < 0.2614973) (h320 : RS320true B)
    (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N :=
  DDNathanson.theorem1_2_of_RS hG hV hRS (RSRecip_of_RS320true hB h320) hSel

/-! ### Vacuity -/

/-- `Σ_{p ≤ 2} 1/p = 1/2`. -/
theorem primeRecipSum_two : primeRecipSum 2 = 1 / 2 := by
  have hf : ⌊(2 : ℝ)⌋₊ = 2 := by simp
  have hs : (range (2 + 1)).filter Nat.Prime = {2} := by decide
  unfold primeRecipSum
  rw [hf, hs]
  norm_num

/-- **Vacuity of (3.20)**: at `x = 2` the hypothesis `1 < x` holds and the conclusion holds
with `B = 0.2614972`, since `1/2 < log log 2 + B + 1/log² 2 ≈ 1.976`, using
`log log 2 ≥ 1 - 1/log 2` and `0.6931471803 < log 2 < 0.6931471808`. -/
theorem rs320true_instance_two :
    (1 : ℝ) < 2 ∧ primeRecipSum 2 < log (log 2) + 0.2614972 + 1 / log 2 ^ 2 := by
  refine ⟨by norm_num, ?_⟩
  rw [primeRecipSum_two]
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hpos : (0 : ℝ) < log 2 := by linarith
  have hll : 1 - (log 2)⁻¹ ≤ log (log 2) := Real.one_sub_inv_le_log_of_pos hpos
  set t := (log 2)⁻¹ with ht
  have htl : (1 : ℝ) < t := by
    rw [ht]; exact (one_lt_inv₀ hpos).2 (by linarith)
  have hsq : 1 / log 2 ^ 2 = t ^ 2 := by rw [ht]; field_simp
  rw [hsq]
  nlinarith

/-- The parameter `B = 0.2614972` meets the side condition `B < 0.2614973`. -/
theorem B_side : (0.2614972 : ℝ) < 0.2614973 := by norm_num

end LeanLab.AlmostPrimes.RS1962

end

#print axioms LeanLab.AlmostPrimes.RS1962.log_ten_gt
#print axioms LeanLab.AlmostPrimes.RS1962.log_gt_2302
#print axioms LeanLab.AlmostPrimes.RS1962.inv_log_sq_lt
#print axioms LeanLab.AlmostPrimes.RS1962.RS320_of_RS318
#print axioms LeanLab.AlmostPrimes.RS1962.RSRecip_of_RS320true
#print axioms LeanLab.AlmostPrimes.RS1962.RSRecip_of_RS318
#print axioms LeanLab.AlmostPrimes.RS1962.theorem3_3_large_of_RS3
#print axioms LeanLab.AlmostPrimes.RS1962.theorem1_2_of_RS3
#print axioms LeanLab.AlmostPrimes.RS1962.primeRecipSum_two
#print axioms LeanLab.AlmostPrimes.RS1962.rs320true_instance_two
