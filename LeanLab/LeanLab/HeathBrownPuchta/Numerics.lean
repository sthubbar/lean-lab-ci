/-
AI-written Lean code, Claude, 2026-10-17, run 20261017T2104Z-19452, unit U-0377.
P0012 D. R. Heath-Brown, J.-C. Puchta, Integers represented as a sum of primes and powers of
two, arXiv math/0201299, Sections 4 and 6: the numerical criterion behind K = 13 and, on GRH, K = 7.

Section 6: the K-th integral is positive when `13.968 λ^{K-2} < 2.7895`, with Lemma 1's
`λ = 0.863665` unconditionally and `λ = 0.722428` on GRH. The constants:
`2.7895 ≤ 2 + (2/3)(1 - 2^{-6}) + (2/15)(1 - 4^{-6})` from Section 4, and
`13.968 ≥ (C₁ - 2) C₂ + log 2 / C₀` with `C₁ = 7.8342`, `C₂ ≤ 2.2141`, `C₀ ≥ 0.66`.
PROVED here, all by exact rational arithmetic, except the one `log 2` bound from Mathlib.
The analytic inputs, Lemma 1's λ and the major and minor arc estimates, are NOT formalized.
Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.HeathBrownPuchta

/-- Section 6 criterion: `13.968 λ^{K-2} < 2.7895`. -/
def Admissible (lam : ℝ) (K : ℕ) : Prop := 13968 / 1000 * lam ^ (K - 2) < 27895 / 10000

theorem admissible_13 : Admissible (863665 / 1000000) 13 := by unfold Admissible; norm_num

/-- The criterion fails at `K = 12`, so `13` is the least `K` this route gives. -/
theorem not_admissible_12 : ¬ Admissible (863665 / 1000000) 12 := by unfold Admissible; norm_num

theorem admissible_7_GRH : Admissible (722428 / 1000000) 7 := by unfold Admissible; norm_num

theorem not_admissible_6_GRH : ¬ Admissible (722428 / 1000000) 6 := by unfold Admissible; norm_num

/-- A larger `K` keeps the criterion, for `0 ≤ λ ≤ 1`. -/
theorem admissible_mono {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {K K' : ℕ} (hK : K ≤ K')
    (h : Admissible lam K) : Admissible lam K' := by
  unfold Admissible at *
  have : lam ^ (K' - 2) ≤ lam ^ (K - 2) := pow_le_pow_of_le_one h0 h1 (by omega)
  linarith

/-- The printed GRH threshold: the paper says any `K > 6.995`; the criterion at the real
exponent `4.96` already holds, so the true threshold is below `6.96`; our Python gives
`6.9545`. Stated with `K - 2 = 4.96` as a real power. -/
theorem grh_threshold_below : 13968 / 1000 * (722428 / 1000000 : ℝ) ^ ((496 : ℝ) / 100) <
    27895 / 10000 := by
  have hl0 : (0 : ℝ) < 722428 / 1000000 := by norm_num
  have key : ((722428 / 1000000 : ℝ) ^ ((496 : ℝ) / 100)) ^ (25 : ℕ) = (722428 / 1000000 : ℝ) ^ (124 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have hpos : 0 < (722428 / 1000000 : ℝ) ^ ((496 : ℝ) / 100) := Real.rpow_pos_of_pos hl0 _
  by_contra hc
  push Not at hc
  have h1 : (27895 / 10000 / (13968 / 1000) : ℝ) ≤ (722428 / 1000000 : ℝ) ^ ((496 : ℝ) / 100) := by
    rw [div_le_iff₀ (by norm_num)]; linarith
  have h2 := pow_le_pow_left₀ (by norm_num) h1 25
  rw [key] at h2
  norm_num at h2

/-- Section 4: `2 + (2/3)(1 - 2^{-6}) + (2/15)(1 - 4^{-6}) ≥ 2.7895`. -/
theorem major_const : (27895 / 10000 : ℝ) ≤ 2 + 2 / 3 * (1 - 1 / 2 ^ 6) + 2 / 15 * (1 - 1 / 4 ^ 6) := by
  norm_num

/-- Section 6, Lemma 10: `(C₁ - 2) C₂ + log 2 / C₀ ≤ 13.968` for `C₁ = 7.8342`, `C₂ ≤ 2.2141`,
`C₀ ≥ 0.66`. -/
theorem minor_const (C2 C0 : ℝ) (hC2 : C2 ≤ 22141 / 10000) (hC0 : 66 / 100 ≤ C0) :
    (78342 / 10000 - 2) * C2 + Real.log 2 / C0 ≤ 13968 / 1000 := by
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  norm_num at l2 l2'
  have hC0p : 0 < C0 := by linarith
  have h1 : Real.log 2 / C0 ≤ Real.log 2 / (66 / 100) :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hC0
  have h2 : Real.log 2 / (66 / 100) ≤ 108304247 / 156250000 / (66 / 100) :=
    div_le_div_of_nonneg_right l2.le (by norm_num)
  nlinarith

end LeanLab.HeathBrownPuchta
