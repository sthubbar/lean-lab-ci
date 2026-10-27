/-
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Copy: papers/P0099.pdf, Lemma 1 on p. 14.

Unit U-6744, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Lemma 1 of the paper, N(T) = (T/2π) log(T/2π) - T/2π + 7/8 + O*(0.67 log(T/2π)) for T ≥ 10^3,
is said to follow easily from Theorem 19 of Rosser 1941. Here it is PROVED from that input:
* `RosserN NT`: |N(T) - F(T)| ≤ 0.137 log T + 0.443 log log T + 1.588 + 0.2/T for T ≥ 10^3,
  F(T) = (T/2π) log(T/2π) - T/2π + 7/8, Rosser's constants as quoted by Brent, Platt and
  Trudgian, JNT 238 (2022) Lemma 1, for T ≥ 2πe; the extra 0.2/T only weakens the input.
  `RosserNUpper` is its upper half.
* `rosser_err_le`: 0.137 log T + 0.443 log log T + 1.588 + 0.2/T ≤ 0.67 log(T/2π) for T ≥ 10^3.
  PROVED. The margin at T = 10^3 is about 0.006, so the paper's 0.67 is close to sharp there.
* `lemma1Upper_of_rosser`, `lemma1_of_rosser`: Lemma 1, upper half and two-sided. PROVED
  CONDITIONAL ON `RosserNUpper`, resp. `RosserN`.
* `theorem2At1e20_of_rosser`, `theorem2_row59_of_rosser`, `theorem3_of_rosser`: Table 1 rows
  one and 59 and Theorem 3 CONDITIONAL ON `Theorem4Fm` with T0 = 3.3e9, `RosserNUpper`, and for
  Theorem 3 the Section 7 `ChainCert`.
-/
import Mathlib
import LeanLab.RamareSaouter2003.MuStar55Cert

namespace LeanLab.RamareSaouter2003.Lemma1Rosser
open Real LeanLab.RamareSaouter2003.Smooth

/-- Rosser 1941 Theorem 19, upper half, with the 0.2/T of BPT 2022 Lemma 1, for T ≥ 10^3. Cited. -/
def RosserNUpper (NT : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 1000 ≤ T → NT T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8) ≤
    0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + 0.2 / T

/-- Rosser 1941 Theorem 19, two-sided, with the 0.2/T of BPT 2022 Lemma 1, for T ≥ 10^3. Cited. -/
def RosserN (NT : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 1000 ≤ T → |NT T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
    0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + 0.2 / T

/-- log(2π) ≤ 1.838, from 2π = 2^7 e^-3 z with z close to 1. PROVED. -/
theorem log_two_pi_le : Real.log (2 * π) ≤ 1.838 := by
  have p2 := Real.pi_lt_d6
  have e2 := Real.exp_one_lt_d9
  have l2 := Real.log_two_lt_d9
  have hE3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hz0 : 0 < 2 * π * Real.exp 3 / 2 ^ 7 := by positivity
  have hsplit : Real.log (2 * π) = 7 * Real.log 2 - 3 + Real.log (2 * π * Real.exp 3 / 2 ^ 7) := by
    have h : Real.log (2 * π * Real.exp 3 / 2 ^ 7) = Real.log (2 * π) + 3 - 7 * Real.log 2 := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (x := 2 * π) (by positivity) (by positivity), Real.log_exp, Real.log_pow]
      push_cast; ring
    rw [h]; ring
  have h1 := Real.log_le_sub_one_of_pos hz0
  have h3 : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by
    gcongr
  have hz : 2 * π * Real.exp 3 / 2 ^ 7 ≤ 2 * 3.141593 * (2.7182818286 : ℝ) ^ 3 / 2 ^ 7 := by
    rw [hE3]; gcongr
  have hn : 2 * 3.141593 * (2.7182818286 : ℝ) ^ 3 / 2 ^ 7 ≤ 0.98595 := by norm_num
  linarith

/-- log 1000 ≥ 6.9074, from 1000 = 2^10 (1000/1024). PROVED. -/
theorem log_thousand_ge : 6.9074 ≤ Real.log 1000 := by
  have l1 := Real.log_two_gt_d9
  have hsplit : Real.log 1000 = 10 * Real.log 2 + Real.log (1000 / 2 ^ 10) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1000 / 2 ^ 10 by norm_num)
  have : (1 : ℝ) - (1000 / 2 ^ 10)⁻¹ = -0.024 := by norm_num
  linarith

/-- The numerical heart of Lemma 1: Rosser's error is at most 0.67 log(T/2π) for T ≥ 10^3. PROVED. -/
theorem rosser_err_le (T : ℝ) (hT : 1000 ≤ T) :
    0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + 0.2 / T ≤
      0.67 * Real.log (T / (2 * π)) := by
  have hT0 : 0 < T := by linarith
  set x := Real.log T with hx
  have hx0 : 6.9074 ≤ x := le_trans log_thousand_ge (Real.log_le_log (by norm_num) hT)
  have hxpos : 0 < x := by linarith
  -- log x ≤ 1 + x / e^2
  have he2 : (7.389 : ℝ) ≤ Real.exp 2 := by
    have e1 := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith
  have hE : 0 < Real.exp 2 := Real.exp_pos _
  have hlx : Real.log x ≤ 1 + x / 7.389 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hxpos hE)
    rw [Real.log_div hxpos.ne' hE.ne', Real.log_exp] at h1
    have : x / Real.exp 2 ≤ x / 7.389 := by gcongr
    linarith
  have hlog : Real.log (T / (2 * π)) = x - Real.log (2 * π) := by
    rw [Real.log_div hT0.ne' (by positivity)]
  have h2π := log_two_pi_le
  have hTinv : 0.2 / T ≤ 0.0002 := by
    rw [div_le_iff₀ hT0]; nlinarith
  rw [hlog]
  norm_num at hx0 hlx h2π hTinv ⊢
  linarith

/-- Lemma 1, upper half, CONDITIONAL ON `RosserNUpper`. PROVED. -/
theorem lemma1Upper_of_rosser {NT : ℝ → ℝ} (h : RosserNUpper NT) :
    LeanLab.RamareSaouter2003.Row1.Lemma1Upper NT := by
  intro T hT
  have h1 := h T hT
  have h2 := rosser_err_le T hT
  linarith

/-- Lemma 1 as printed, two-sided, CONDITIONAL ON `RosserN`. PROVED. -/
theorem lemma1_of_rosser {NT : ℝ → ℝ} (h : RosserN NT) : ∀ T : ℝ, 1000 ≤ T →
    |NT T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
      0.67 * Real.log (T / (2 * π)) :=
  fun T hT => (h T hT).trans (rosser_err_le T hT)

theorem rosserNUpper_of {NT : ℝ → ℝ} (h : RosserN NT) : RosserNUpper NT :=
  fun T hT => (le_abs_self _).trans (h T hT)

/-- Table 1 row one, CONDITIONAL ON `Theorem4Fm` with T0 = 3.3e9 and `RosserNUpper`. -/
theorem theorem2At1e20_of_rosser {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hR : RosserNUpper NT) : Theorem2At1e20 :=
  MuStar55Cert.theorem2At1e20_of_thm4 h4 (lemma1Upper_of_rosser hR)

/-- Table 1 row 59, CONDITIONAL ON `Theorem4Fm` with T0 = 3.3e9 and `RosserNUpper`. -/
theorem theorem2_row59_of_rosser {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hR : RosserNUpper NT) : ∀ x : ℝ, Real.exp 59 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x :=
  MuStar55Cert.theorem2_row59_of_thm4 h4 (lemma1Upper_of_rosser hR)

/-- Theorem 3, CONDITIONAL ON `Theorem4Fm`, `RosserNUpper` and the Section 7 `ChainCert`. -/
theorem theorem3_of_rosser {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hR : RosserNUpper NT) (hc : ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000) :
    ∀ x : ℝ, 10726905041 < x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x :=
  MuStar55Cert.theorem3_of_thm4 h4 (lemma1Upper_of_rosser hR) hc

end LeanLab.RamareSaouter2003.Lemma1Rosser

#print axioms LeanLab.RamareSaouter2003.Lemma1Rosser.rosser_err_le
#print axioms LeanLab.RamareSaouter2003.Lemma1Rosser.lemma1Upper_of_rosser
#print axioms LeanLab.RamareSaouter2003.Lemma1Rosser.lemma1_of_rosser
#print axioms LeanLab.RamareSaouter2003.Lemma1Rosser.theorem2At1e20_of_rosser
#print axioms LeanLab.RamareSaouter2003.Lemma1Rosser.theorem2_row59_of_rosser
#print axioms LeanLab.RamareSaouter2003.Lemma1Rosser.theorem3_of_rosser
