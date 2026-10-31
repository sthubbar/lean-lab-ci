/-
U-1385, run PC 20261021T0803Z-19426. Part 4 of a memory split of OeSHP2014U6818Exact1e7.lean
by cloud57, unit U-6818: Oliveira e Silva, Herzog, Pardi 2014, Table 4 exact on [6, 10000000].
The 10^7 sieve check of the original ran out of memory in one piece, so row 23 is split
into kernel windows on [3807404, 10000000] with the BitSieve2 machinery, two per module.
This part holds windows 1, 2.
AI-written Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import LeanLab.OeSHP2014.OeSHP2014U1385Part1

set_option Elab.async false

namespace LeanLab.OeSHP2014.U1385

open LeanLab.Verifications LeanLab.Verifications.Top50 LeanLab.Verifications.Top50.Bits

theorem take_le_23 : ∀ q ∈ P10k.take 133, q ≤ 751 := by
  have h : (P10k.take 133).all (fun q => decide (q ≤ 751)) = true := by decide +kernel
  intro q hq
  simpa using List.all_eq_true.mp h q hq

/-- Window 1 of row 23: every even n in [3807404, 4692060] is p + q, q among the first 133 primes. -/
theorem window23_1 : wem 3806644 3807404 4692060 &&& gm (wpm2 3806644 885416) (P10k.take 133) =
    wem 3806644 3807404 4692060 := by
  decide +kernel

/-- Window 2 of row 23: every even n in [4692062, 5576718] is p + q, q among the first 133 primes. -/
theorem window23_2 : wem 4691302 4692062 5576718 &&& gm (wpm2 4691302 885416) (P10k.take 133) =
    wem 4691302 4692062 5576718 := by
  decide +kernel

end LeanLab.OeSHP2014.U1385
