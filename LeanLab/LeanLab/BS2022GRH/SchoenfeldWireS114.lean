/-
ROUTE BURST S114 burst-20261122, unit li2657_wire. Schoenfeld 1976, Math. Comp. 30, p. 340:
"A direct calculation shows that (6.18) holds for 2,657 <= x < 2,659". The proof is the one of
`SchoenfeldFiniteS70.direct_2657_of_leaf`, with its LEAF `liPV_2657_encl` replaced by
`SchoenfeldLiS76.liPV_2657_encl_S76`, the same enclosure `399.59 <= li 2657 <= 399.61`, PROVED in S114.
AI wrote this Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SchoenfeldLiS76

namespace LeanLab.BS2022GRH.SchoenfeldWireS114
open Real MeasureTheory intervalIntegral Set
open LeanLab.BS2022GRH.PaperInputs148 LeanLab.BS2022GRH.SchoenfeldFiniteS70

/-- PROVED: Schoenfeld 1976 p. 340, (6.18) holds for `2657 <= x < 2659`, from the PROVED
enclosure `SchoenfeldLiS76.liPV_2657_encl_S76`. Same statement as `direct_2657_of_leaf`. -/
theorem direct_2657_S114 : ∀ x : ℝ, 2657 ≤ x → x < 2659 →
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  intro x h1 h2
  obtain ⟨lo, hi⟩ := SchoenfeldLiS76.liPV_2657_encl_S76
  have hpc := primeCount_eq_384 x h1 h2
  have hmono := BrentRangeS63.liPV_mono 2657 x (by norm_num) h1
  have hinc := liPV_incr x h1
  have hl := log_ge_787 h1
  have hs : 51.5 ≤ √x := by
    rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have hpi : π < 3.1416 := pi_lt_d4
  have hpi0 : 0 < π := pi_pos
  rw [hpc, abs_sub_comm, abs_of_pos (by linarith), lt_div_iff₀ (by positivity)]
  have hprod : 51.5 * 7.87 ≤ √x * log x := by nlinarith
  have hd : liPV x - 384 ≤ 15.87 := by
    have : (x - 2657) / 7.87 ≤ 2 / 7.87 := by gcongr; linarith
    have : (2 : ℝ) / 7.87 ≤ 0.26 := by norm_num
    linarith
  have hd0 : 0 ≤ liPV x - 384 := by linarith
  nlinarith

end LeanLab.BS2022GRH.SchoenfeldWireS114
