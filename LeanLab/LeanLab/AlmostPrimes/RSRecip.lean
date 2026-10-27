/-
AI-written Lean code, Claude, 2026-10-21, run 20261020T2303Z-14596, unit U-1307.
P0048 Dudek-Dunn cite Rosser-Schoenfeld 1962 (3.20) in the derived form `RSRecip`,
`Σ_{p < z} 1/p < log log z + 0.2634` for `z ≥ 10^10`, see DDMain.lean.
This file reduces `RSRecip` to `RS320`, the published inequality (3.20) itself,
`Σ_{p ≤ x} 1/p < log log x + B + 1/(2 log² x)`, with the Meissel-Mertens constant
`B = 0.2614972128...` replaced by the larger `0.26150`, stated only for `x ≥ 10^10`.
So `RS320` is weaker than the paper's statement for all `x > 1`. Cited as a Prop.
At `z ≥ 10^10`, `log z ≥ 17 > 16.23`, so `0.26150 + 1/(2 log² z) < 0.2634`; the true margin
at `10^10` is `0.000957`.
No full proof is attempted: an explicit Mertens second theorem with the constant `B` to five
digits needs the value of `B` itself, which no explicit θ bound for `x ≥ x₀` gives without
the sum over all primes below `x₀`, and neither the lab nor Mathlib has an explicit Mertens
theorem. KNOWN mathematics. Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.DDNathanson

open Real Finset
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDMain

noncomputable section
namespace LeanLab.AlmostPrimes.RSRecipRed

/-- Rosser-Schoenfeld 1962 (3.20), `Σ_{p ≤ x} 1/p < log log x + B + 1/(2 log² x)`, with
`B = 0.26149 72128...` replaced by `0.26150`, for `x ≥ 10^10` only. Cited. -/
def RS320 : Prop := ∀ x : ℝ, 10 ^ 10 ≤ x →
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p <
    log (log x) + 0.26150 + 1 / (2 * log x ^ 2)

/-- `log z ≥ 17` for `z ≥ 10^10`, from `e < 2.7182818286` and `2.7182818286^17 < 10^10`. -/
theorem seventeen_le_log {z : ℝ} (hz : 10 ^ 10 ≤ z) : 17 ≤ log z := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h : Real.exp 1 ^ 17 ≤ (2.7182818286 : ℝ) ^ 17 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 17
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  have h2 : (2.7182818286 : ℝ) ^ 17 ≤ 10 ^ 10 := by norm_num
  linarith

/-- The primes `2 ≤ p < z` are among the primes `p ≤ ⌊z⌋`. -/
theorem primesIn_subset (z : ℝ) :
    primesIn 2 z ⊆ (range (⌊z⌋₊ + 1)).filter Nat.Prime := by
  intro p hp
  simp only [primesIn, mem_filter, mem_range] at hp ⊢
  refine ⟨?_, hp.2.1⟩
  have : p ≤ ⌊z⌋₊ := Nat.le_floor hp.2.2.2.le
  omega

/-- **`RSRecip` from Rosser-Schoenfeld (3.20)**. CONDITIONAL ON `RS320` only. -/
theorem RSRecip_of_RS320 (h : RS320) : RSRecip := by
  intro z hz
  have hsub := primesIn_subset z
  have hle : ∑ p ∈ primesIn 2 z, (1 : ℝ) / p ≤
      ∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hRS := h z hz
  have hL := seventeen_le_log hz
  have hL2 : (289 : ℝ) ≤ log z ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 2 * log z ^ 2 := by positivity
  have hsmall : 1 / (2 * log z ^ 2) ≤ 1 / 578 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have : (0.26150 : ℝ) + 1 / 578 < 0.2634 := by norm_num
  linarith

/-- **Theorem 3.3 for `N ≥ 10^200`**: `N = a + b` with `Ω(ab) ≤ 39` for even `N`, `≤ 40` for
odd `N`. CONDITIONAL ON `RSHyp`, `RS320`, `SelbergThm13` only. -/
theorem theorem3_3_large_of_RS2 (hRS : DDLemma21All.RSHyp) (h320 : RS320)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  DDNathanson.theorem3_3_large_of_RS hRS (RSRecip_of_RS320 h320) hSel N hN

/-- **Theorem 1.2**. CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RSHyp`, `RS320`,
`SelbergThm13`. -/
theorem theorem1_2_of_RS2 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (h320 : RS320) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N :=
  DDNathanson.theorem1_2_of_RS hG hV hRS (RSRecip_of_RS320 h320) hSel

end LeanLab.AlmostPrimes.RSRecipRed

end

#print axioms LeanLab.AlmostPrimes.RSRecipRed.seventeen_le_log
#print axioms LeanLab.AlmostPrimes.RSRecipRed.primesIn_subset
#print axioms LeanLab.AlmostPrimes.RSRecipRed.RSRecip_of_RS320
#print axioms LeanLab.AlmostPrimes.RSRecipRed.theorem3_3_large_of_RS2
#print axioms LeanLab.AlmostPrimes.RSRecipRed.theorem1_2_of_RS2
