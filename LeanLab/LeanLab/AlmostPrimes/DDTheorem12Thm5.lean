/-
AI-written Lean code, Claude, 2026-10-21, run 20261021T1103Z-29422, unit U-1404.
P0048 A. Dudek, L. Dunn, An Explicit Result for the Sum of Two Almost Primes, arXiv 2602.22720.

Theorem 1.2 and Theorem 3.3 for every `N ≥ 2` with the Rosser-Schoenfeld inputs reduced to
Rosser-Schoenfeld 1962 Theorem 5, eqs (3.17) and (3.18), p. 70, with one parameter `B` and
`B < 0.2614973`; the published value is `B = 0.26149 72128 47643`, their (2.10).
`RSHyp` comes from `RSHypFrom318.RSHyp_of_RS317_RS318`, `RSRecip` from `RS1962.RSRecip_of_RS318`,
`NathansonRd` is PROVED in `DDNathanson`.
Remaining cited inputs: `GapTable1476`, `VerifySScript`, `RS317 B`, `RS318 B`, `SelbergThm13`.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.RSHypFrom318

open Real
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDMain
open LeanLab.AlmostPrimes.RS1962 LeanLab.AlmostPrimes.RSHypFrom318

noncomputable section
namespace LeanLab.AlmostPrimes.DDTheorem12Thm5

/-- **Dudek-Dunn Theorem 3.3 for every `N ≥ 2`**: `N = a + b`, `a, b > 0`, `Ω(ab) ≤ 39` for even
`N`, `≤ 40` always. CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RS317 B`, `RS318 B` with
`B < 0.2614973`, and `SelbergThm13`. -/
theorem theorem3_3_of_thm5 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    {B : ℝ} (hB : B < 0.2614973) (h317 : RS317 B) (h318 : RS318 B) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  DDNathanson.theorem3_3_of_RS hG hV (RSHyp_of_RS317_RS318 h317 h318)
    (RSRecip_of_RS318 hB h318) hSel

/-- **Dudek-Dunn Theorem 1.2**: every `N ≥ 2` is a sum of two positive integers each with at
most 40 prime factors counted with multiplicity, in the lab's `TwoAlmostPrimes 40 N` form.
CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RS317 B`, `RS318 B` with `B < 0.2614973`,
and `SelbergThm13`. -/
theorem theorem1_2_of_thm5 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    {B : ℝ} (hB : B < 0.2614973) (h317 : RS317 B) (h318 : RS318 B) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N :=
  DDNathanson.theorem1_2_of_RS hG hV (RSHyp_of_RS317_RS318 h317 h318)
    (RSRecip_of_RS318 hB h318) hSel

/-! ### Vacuity of the Rosser-Schoenfeld side -/

/-- At `B = 0.2614972` the side condition holds and both cited (3.17), (3.18) can hold at a
point: (3.17) at `x = 2` is `RSHypFrom318.rs317_instance_two`, PROVED; the side condition is
`RS1962.B_side`. -/
theorem thm5_side_instance :
    (0.2614972 : ℝ) < 0.2614973 ∧
      log (log 2) + 0.2614972 - 1 / (2 * log 2 ^ 2) < primeRecipSum 2 :=
  ⟨B_side, rs317_instance_two.2⟩

end LeanLab.AlmostPrimes.DDTheorem12Thm5

end
