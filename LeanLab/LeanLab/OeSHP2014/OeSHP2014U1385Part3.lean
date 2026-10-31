/-
U-1385, run PC 20261021T0803Z-19426. Part 3 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
Holds one window of the original, up to the bound named in its docstring.
Same checks as the original, verbatim; only the file layout changed so that each kernel
sieve check runs in its own module, elaborated sequentially.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.OeSHP2014.OeSHP2014U1385Part1

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem take_le_22 : ∀ q ∈ P10k.take 129, q ≤ 727 := by
  have h : (P10k.take 129).all (fun q => decide (q ≤ 727)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_22 : em 4 3807402 &&& gm (pm 3807403) (P10k.take 129) = em 4 3807402 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 3807402 has minGB m ≤ 727. -/
theorem seg_22 : SmallGBUpTo 727 3807402 := small_of_check (by norm_num) take_le_22 check_22

end LeanLab.OeSHP2014.U1385
