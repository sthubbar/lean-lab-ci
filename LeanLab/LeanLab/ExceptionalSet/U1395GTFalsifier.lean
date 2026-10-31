/-
U-1395, PC run 20261021T1003Z-20044, independent VERIFY and falsifier of CLOUD cloud56 U-6807,
P0039 Grimmelt and Teräväinen, arXiv 2508.16400v2, F-5046 and F-5047.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.GrimmeltTeravainen2025Chain

namespace LeanLab.ExceptionalSet.GT2025.U1395

/-- Vacuity of the F-5046 witness at r = 2, the least value of r_{N^{1/10}} on rough n:
(3.11) right side is 0, printed (3.12) right side is 1/2 > 0 = Λ₂(n). -/
theorem f5046_at_two : rhs311 2 1 1 0 0 = 0 ∧ (0 : ℝ) < rhs312printed 2 1 1 0 0 :=
  eq312printed_fails_B1 (by norm_num)

/-- The exact printed right side at a B₁ point: r/2 - 1/2. -/
theorem printed_B1_value (r : ℝ) : rhs312printed r 1 1 0 0 = r / 2 - 1 / 2 := by
  unfold rhs312printed; ring

/-- F-5047 at a prime: if Ω_M is normalised only by ∏_{[P₁,N^{1/10})}, the p.16 majorant at a
prime p gives log N · κ with κ < 1, below Λ(p) = log p once log p > κ log N. -/
theorem f5047_prime_majorant_fails {L κ lp : ℝ} (hκ : κ < 1) (hL : 0 < L)
    (hlp : κ * L < lp) : ¬ (lp ≤ L * κ) := by
  intro h; linarith [mul_comm L κ]

end LeanLab.ExceptionalSet.GT2025.U1395

open LeanLab.ExceptionalSet.GT2025 in
#print axioms eq312printed_fails_B1
open LeanLab.ExceptionalSet.GT2025 in
#print axioms eq312printed_fails_B2
open LeanLab.ExceptionalSet.GT2025 in
#print axioms rhs312corrected_eq
open LeanLab.ExceptionalSet.GT2025 in
#print axioms rhs312printed_ge
open LeanLab.ExceptionalSet.GT2025 in
#print axioms two_le_rz
open LeanLab.ExceptionalSet.GT2025 in
#print axioms switch_bound
open LeanLab.ExceptionalSet.GT2025 in
#print axioms switch_bound_printed
open LeanLab.ExceptionalSet.GT2025 in
#print axioms lemma83_c1
open LeanLab.ExceptionalSet.GT2025 in
#print axioms final_chain
open LeanLab.ExceptionalSet.GT2025 in
#print axioms final_chain_vacuity
open LeanLab.ExceptionalSet.GT2025 in
#print axioms final_chain_needs_eps
#print axioms LeanLab.ExceptionalSet.GT2025.U1395.f5046_at_two
#print axioms LeanLab.ExceptionalSet.GT2025.U1395.printed_B1_value
#print axioms LeanLab.ExceptionalSet.GT2025.U1395.f5047_prime_majorant_fails
