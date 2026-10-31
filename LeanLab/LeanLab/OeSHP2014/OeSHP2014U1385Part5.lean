/-
U-1385, run PC 20261021T0803Z-19426. Part 5 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
The 10^7 sieve check of the original ran out of memory in one piece, so row 23 is split
into kernel windows on [3807404, 10000000] with the BitSieve2 machinery, two per module.
This part holds windows 3, 4.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.OeSHP2014.OeSHP2014U1385Part1

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

/-- Window 3 of row 23: every even n in [5576720, 6461376] is p + q, q among the first 133 primes. -/
theorem window23_3 : wem 5575960 5576720 6461376 &&& gm (wpm2 5575960 885416) (P10k.take 133) =
    wem 5575960 5576720 6461376 := by
  decide +kernel

/-- Window 4 of row 23: every even n in [6461378, 7346034] is p + q, q among the first 133 primes. -/
theorem window23_4 : wem 6460618 6461378 7346034 &&& gm (wpm2 6460618 885416) (P10k.take 133) =
    wem 6460618 6461378 7346034 := by
  decide +kernel

end LeanLab.OeSHP2014.U1385
