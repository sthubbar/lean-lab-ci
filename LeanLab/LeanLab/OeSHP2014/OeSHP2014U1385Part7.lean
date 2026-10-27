/-
U-1385, run PC 20261021T0803Z-19426. Part 7 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
The 10^7 sieve check of the original ran out of memory in one piece, so row 23 is split
into kernel windows on [3807404, 10000000] with the BitSieve2 machinery, two per module.
This part holds windows 7.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.OeSHP2014.OeSHP2014U1385Part1

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- Window 7 of row 23: every even n in [9115352, 10000000] is p + q, q among the first 133 primes. -/
theorem window23_7 : wem 9114592 9115352 10000000 &&& gm (wpm2 9114592 885408) (P10k.take 133) =
    wem 9114592 9115352 10000000 := by
  decide +kernel

end LeanLab.OeSHP2014.U1385
