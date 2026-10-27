/-
U-1385, run PC 20261021T0803Z-19426. Part 6 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
The 10^7 sieve check of the original ran out of memory in one piece, so row 23 is split
into kernel windows on [3807404, 10000000] with the BitSieve2 machinery, two per module.
This part holds windows 5, 6.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.OeSHP2014.OeSHP2014U1385Part1

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- Window 5 of row 23: every even n in [7346036, 8230692] is p + q, q among the first 133 primes. -/
theorem window23_5 : wem 7345276 7346036 8230692 &&& gm (wpm2 7345276 885416) (P10k.take 133) =
    wem 7345276 7346036 8230692 := by
  decide +kernel

/-- Window 6 of row 23: every even n in [8230694, 9115350] is p + q, q among the first 133 primes. -/
theorem window23_6 : wem 8229934 8230694 9115350 &&& gm (wpm2 8229934 885416) (P10k.take 133) =
    wem 8229934 8230694 9115350 := by
  decide +kernel

end LeanLab.OeSHP2014.U1385
