/-
BS2022GRH, P0021, idea I-0088, F-0075, unit U-1611, run 20261103T0803Z-22341.
The 13.375 threshold rerouted through the repaired sieve input, `LinearSieveT4` no longer an argument.

`Thm5R`, `Thm6R`, `Thm7R`, OPEN leaves: the printed brackets at the I-0088 parameters, from GRH,
Lemma 7 and the κ sieve at row 1/39500. Their proofs repeat pp. 1229, 1232 to 1234, 1236 to 1241, with
s* in the main terms and κ on the remainders; the numeric slack is kappa_check.py of U-1611.
`chenThreshold13375_of_fixedKappa`: CONDITIONAL ON those, clean axioms.
`chenThreshold13375_of_allLevels`: the same from `LinearSieveAllLevels`, carrying the named sorry
`fixedKappa_of_allLevels`. No sealed statement is changed.

AI wrote this Lean code, Claude, unit U-1611. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SieveAllLevels1611
import LeanLab.BS2022GRH.Cert1575Closed

namespace LeanLab.BS2022GRH.Chain1611
open Real Finset Classical
open LeanLab.BS2022GRH LeanLab.BS2022GRH.ChenThresholdGRH LeanLab.BS2022GRH.SieveAllLevels1611

/-- The repaired sieve at the I-0088 point: fixed level ε = 1/8349 of Lemma 7, row 1/39500. -/
abbrev SieveK : Prop := LinearSieveFixedKappa (1 / 8349) (1 / 39500) 111 113

/-- **Theorem 5 from the κ sieve**, OPEN, p. 1228 with the proof of p. 1229: the printed bracket at
α = 0.00256, A = 10, ε = 1/8349, C₂ = 114. Repaired minus printed main term is +0.0011 at log log X₂ =
13.375, the κ remainder is about 4·10⁻⁴⁸. -/
def Thm5R : Prop :=
  Lemma7J → GRH → SieveK → ∀ n : ℕ, Even n → exp (exp 13.375) ≤ (n : ℝ) →
    8 * (UNfull n * n / log n ^ 2) * B5J 0.00256 10 (1 / 8349) 114 (exp (exp 13.375)) n
      < (U7153.SA n : ℝ)

/-- **Theorem 6 from the κ sieve**, OPEN, pp. 1231-1234: the printed bracket with C₁ = 112. The slack
in l₁ is 0.0102, the κ remainder about 10⁻⁴². -/
def Thm6R : Prop :=
  Lemma7J → GRH → SieveK → ∀ n : ℕ, Even n → exp (exp 13.375) ≤ (n : ℝ) →
    ∑ q ∈ (U7153.Qset n).filter (fun q => ¬ q ∣ n), (U7153.SAq n q : ℝ)
      ≤ 8 * (UNfull n * n / log n ^ 2) * B6J 0.00256 10 (1 / 8349) 112 (exp (exp 13.375)) n

/-- **Theorem 7 from the κ sieve**, OPEN, pp. 1234-1241: the printed bracket with C₁ = 112, ε₁ = 10⁻²⁰.
The main term slack is 0.0112, the κ remainder about 4·10⁻¹⁵. -/
def Thm7R : Prop :=
  Lemma7J → GRH → SieveK → ∀ n : ℕ, Even n → exp (exp 13.375) ≤ (n : ℝ) →
    (U7153.SB n : ℝ)
      ≤ UNfull n * n / log n ^ 2 * B7J 0.00256 10 (1 / 8349) 112 (exp (exp 13.375)) 1e-20

/-- **The I-0088 threshold through the repaired input, CONDITIONAL** ON Lemma 7, the κ sieve and the
three leaves. Same proof as `chenThreshold13375_of_leaves`; `LinearSieveT4` does not appear. -/
theorem chenThreshold13375_of_fixedKappa (hL : Lemma7J) (hK : SieveK)
    (h5 : Thm5R) (h6 : Thm6R) (h7 : Thm7R) : ChenThreshold13375 := by
  intro hG n hev hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (exp_pos _) hn
  have hL13 : exp 13.375 ≤ log (n : ℝ) := by
    rw [← log_exp (exp 13.375)]; exact log_le_log (exp_pos _) hn
  have hX := X2_ranges
  have h24 : (2 : ℝ) ^ 24 ≤ n := by
    have : (2 : ℝ) ^ 24 ≤ 4e18 := by norm_num
    linarith [hX.1]
  have H5 := h5 hL hG hK n hev hn
  have H6 := h6 hL hG hK n hev hn
  have H7 := h7 hL hG hK n hev hn
  rw [sum_Qset_filter] at H6
  have H9 := U7153.lemma10 n h24
  have HB := Cert1567.bracket13375_holds n hn
  have hK3 := Journal.theorem3_positive_main
  have hU := two_fifths_le_UNfull n
  have hE := error_13375 hn0 hL13
  have h55 := section55_step n
  set c := UNfull n * n / log (n : ℝ) ^ 2 with hc
  set q := (n : ℝ) / log (n : ℝ) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hcq : 2 / 5 * q ≤ c := by
    rw [hc, hq, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hU hq0
  have hc0 : 0 ≤ c := by linarith
  have HBc := mul_le_mul_of_nonneg_left HB hc0
  have hKc := mul_le_mul_of_nonneg_left hK3.le hc0
  have hpos : (0 : ℝ) < pi2' n := by nlinarith
  exact rep_of_pi2' (by exact_mod_cast hpos)

/-- The same from the cited all levels sieve at row 1/39500, C₁ = 111, C₂ = 113, carrying the named
sorry `fixedKappa_of_allLevels`. -/
theorem chenThreshold13375_of_allLevels (hL : Lemma7J)
    (hA : LinearSieveAllLevels (1 / 39500) 111 113)
    (h5 : Thm5R) (h6 : Thm6R) (h7 : Thm7R) : ChenThreshold13375 :=
  chenThreshold13375_of_fixedKappa hL (fixedKappa_of_allLevels hA) h5 h6 h7

/-- Vacuity of the leaves' ranges: the N they speak about exist. -/
theorem leaves_nonvacuous : ∃ n : ℕ, Even n ∧ exp (exp 13.375) ≤ (n : ℝ) := threshold_nonvacuous

end LeanLab.BS2022GRH.Chain1611

#print axioms LeanLab.BS2022GRH.Chain1611.chenThreshold13375_of_fixedKappa
#print axioms LeanLab.BS2022GRH.Chain1611.chenThreshold13375_of_allLevels
#print axioms LeanLab.BS2022GRH.Chain1611.leaves_nonvacuous
