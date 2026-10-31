/-
Kernel Goldbach windows V561 to V570, width 990000, covering even n in [878140002, 888040000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V561: every even n in [878140002, 879130000] is p + q, q among the first 280 primes. -/
theorem window_v561 : wem 878138190 878140002 879130000 &&& gm (wpm2 878138190 991810) (P10k.take 280) =
    wem 878138190 878140002 879130000 := by
  decide +kernel

/-- Window V562: every even n in [879130002, 880120000] is p + q, q among the first 280 primes. -/
theorem window_v562 : wem 879128190 879130002 880120000 &&& gm (wpm2 879128190 991810) (P10k.take 280) =
    wem 879128190 879130002 880120000 := by
  decide +kernel

/-- Window V563: every even n in [880120002, 881110000] is p + q, q among the first 280 primes. -/
theorem window_v563 : wem 880118190 880120002 881110000 &&& gm (wpm2 880118190 991810) (P10k.take 280) =
    wem 880118190 880120002 881110000 := by
  decide +kernel

/-- Window V564: every even n in [881110002, 882100000] is p + q, q among the first 280 primes. -/
theorem window_v564 : wem 881108190 881110002 882100000 &&& gm (wpm2 881108190 991810) (P10k.take 280) =
    wem 881108190 881110002 882100000 := by
  decide +kernel

/-- Window V565: every even n in [882100002, 883090000] is p + q, q among the first 280 primes. -/
theorem window_v565 : wem 882098190 882100002 883090000 &&& gm (wpm2 882098190 991810) (P10k.take 280) =
    wem 882098190 882100002 883090000 := by
  decide +kernel

/-- Window V566: every even n in [883090002, 884080000] is p + q, q among the first 280 primes. -/
theorem window_v566 : wem 883088190 883090002 884080000 &&& gm (wpm2 883088190 991810) (P10k.take 280) =
    wem 883088190 883090002 884080000 := by
  decide +kernel

/-- Window V567: every even n in [884080002, 885070000] is p + q, q among the first 280 primes. -/
theorem window_v567 : wem 884078190 884080002 885070000 &&& gm (wpm2 884078190 991810) (P10k.take 280) =
    wem 884078190 884080002 885070000 := by
  decide +kernel

/-- Window V568: every even n in [885070002, 886060000] is p + q, q among the first 280 primes. -/
theorem window_v568 : wem 885068190 885070002 886060000 &&& gm (wpm2 885068190 991810) (P10k.take 280) =
    wem 885068190 885070002 886060000 := by
  decide +kernel

/-- Window V569: every even n in [886060002, 887050000] is p + q, q among the first 280 primes. -/
theorem window_v569 : wem 886058190 886060002 887050000 &&& gm (wpm2 886058190 991810) (P10k.take 280) =
    wem 886058190 886060002 887050000 := by
  decide +kernel

/-- Window V570: every even n in [887050002, 888040000] is p + q, q among the first 280 primes. -/
theorem window_v570 : wem 887048190 887050002 888040000 &&& gm (wpm2 887048190 991810) (P10k.take 280) =
    wem 887048190 887050002 888040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
