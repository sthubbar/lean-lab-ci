import Mathlib
import LeanLab.AlmostPrimes.DDCase3
import LeanLab.AlmostPrimes.DDMain
import LeanLab.AlmostPrimes.Statements
import LeanLab.AlmostPrimes.DudekDunn2026

open Real
open LeanLab.AlmostPrimes
open LeanLab.AlmostPrimes.DDMain
open LeanLab.AlmostPrimes.DDCase3

namespace LeanLab.AlmostPrimes.DDMain

/-- LEAF. The sieve premise holds. -/
theorem leaf_premise_fires : 2 * (2 + log 3) + 3 ≤ (18.4 : ℝ) := by
  exact DDConst.case3_s_cond

/-- LEAF. N^0.92 = exp(0.92 L). -/
theorem leaf_case3_Nr (N : ℝ) (hN0 : 0 < N) :
    N ^ (0.92 : ℝ) = exp (0.92 * log N) := by
  rw [rpow_def_of_pos hN0, mul_comm]

/-- LEAF. Dudek-Dunn Theorem 3.3, Case 3, the final display, for every N ≥ 10^200:
4(N - 1)/log² N - (1.182/20^8) N^{0.92} log^8 N > 0. -/
theorem leaf_case3_all (N : ℝ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    0 < 4 * (N - 1) / (log N) ^ 2 - (1.182 / 20 ^ 8) * N ^ (0.92 : ℝ) * (log N) ^ 8 := by
  exact DDCase3.case3_all N hN

/-- LEAF. Dudek-Dunn Theorem 3.3, Case 3, Theorem 1.3 at s = 18.4, K = 3. -/
theorem leaf_sifted_large (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    Campbell2026.SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ))) := by
  exact sifted_large hRS hRec hNat hSel N hN

/-- LEAF. **Theorem 3.3 for `N ≥ 10^200`**, no gap table and no script: `N = a + b` with
`Ω(ab) ≤ 39` for even `N`, `≤ 40` for odd `N`. CONDITIONAL ON `RSHyp`, `RSRecip`,
`NathansonRd`, `SelbergThm13`. -/
theorem leaf_theorem3_3_large (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 := by
  exact theorem3_3_large hRS hRec hNat hSel N hN

/-- LEAF. `S(A, N^{1/20}) > 0` for every `N > 4 · 10^18`: the `hS` input of
`DudekDunn2026.theorem3_3_of`, from the script below `10^200` and Case 3 above. -/
theorem leaf_sifted_all (hV : VerifySScript) (hRS : DDLemma21All.RSHyp) (hRec : RSRecip)
    (hNat : NathansonRd) (hSel : SelbergThm13) :
    ∀ N : ℕ, 4 * 10 ^ 18 < N → Campbell2026.SiftedExists N ((N : ℝ) ^ (1 / (20 : ℝ))) := by
  exact sifted_all hV hRS hRec hNat hSel

/-- LEAF. **Dudek-Dunn Theorem 3.3**: every `N ≥ 2` is `a + b`, positive, with `Ω(ab) ≤ 39` for even
`N` and `≤ 40` for odd `N`. CONDITIONAL ON `GapTable1476`, `VerifySScript`, `RSHyp`, `RSRecip`,
`NathansonRd`, `SelbergThm13`. -/
theorem leaf_theorem3_3 (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 := by
  exact theorem3_3 hG hV hRS hRec hNat hSel


/-- P0048 Dudek, Dunn: every N ≥ 2 is a + b, positive, with Ω of ab at most 40 -/
theorem my_assembly (hG : DudekDunn2026.GapTable1476) (hV : VerifySScript)
    (hRS : DDLemma21All.RSHyp) (hRec : RSRecip) (hNat : NathansonRd) (hSel : SelbergThm13) :
    ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 40 N := by
  intro N h2
  obtain ⟨a, b, ha, hb, hab, -, h40⟩ := leaf_theorem3_3 hG hV hRS hRec hNat hSel N h2
  exact ⟨a, b, ha, hb, hab, h40⟩

end LeanLab.AlmostPrimes.DDMain
