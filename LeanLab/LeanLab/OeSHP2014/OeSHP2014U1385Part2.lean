/-
U-1385, run PC 20261021T0803Z-19426. Part 2 of a memory split of OeSHP2014U6818Exact1e7.lean
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

theorem take_le_21 : ∀ q ∈ P10k.take 110, q ≤ 601 := by
  have h : (P10k.take 110).all (fun q => decide (q ≤ 601)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

theorem check_21 : em 4 3526956 &&& gm (pm 3526957) (P10k.take 110) = em 4 3526956 := by
  decide +kernel

/-- Every even m with 4 ≤ m ≤ 3526956 has minGB m ≤ 601. -/
theorem seg_21 : SmallGBUpTo 601 3526956 := small_of_check (by norm_num) take_le_21 check_21

end LeanLab.OeSHP2014.U1385
