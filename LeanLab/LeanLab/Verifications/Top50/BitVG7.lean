/-
Kernel Goldbach windows V61 to V70, width 990000, covering even n in [383140002, 393040000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V61: every even n in [383140002, 384130000] is p + q, q among the first 280 primes. -/
theorem window_v61 : wem 383138190 383140002 384130000 &&& gm (wpm2 383138190 991810) (P10k.take 280) =
    wem 383138190 383140002 384130000 := by
  decide +kernel

/-- Window V62: every even n in [384130002, 385120000] is p + q, q among the first 280 primes. -/
theorem window_v62 : wem 384128190 384130002 385120000 &&& gm (wpm2 384128190 991810) (P10k.take 280) =
    wem 384128190 384130002 385120000 := by
  decide +kernel

/-- Window V63: every even n in [385120002, 386110000] is p + q, q among the first 280 primes. -/
theorem window_v63 : wem 385118190 385120002 386110000 &&& gm (wpm2 385118190 991810) (P10k.take 280) =
    wem 385118190 385120002 386110000 := by
  decide +kernel

/-- Window V64: every even n in [386110002, 387100000] is p + q, q among the first 280 primes. -/
theorem window_v64 : wem 386108190 386110002 387100000 &&& gm (wpm2 386108190 991810) (P10k.take 280) =
    wem 386108190 386110002 387100000 := by
  decide +kernel

/-- Window V65: every even n in [387100002, 388090000] is p + q, q among the first 280 primes. -/
theorem window_v65 : wem 387098190 387100002 388090000 &&& gm (wpm2 387098190 991810) (P10k.take 280) =
    wem 387098190 387100002 388090000 := by
  decide +kernel

/-- Window V66: every even n in [388090002, 389080000] is p + q, q among the first 280 primes. -/
theorem window_v66 : wem 388088190 388090002 389080000 &&& gm (wpm2 388088190 991810) (P10k.take 280) =
    wem 388088190 388090002 389080000 := by
  decide +kernel

/-- Window V67: every even n in [389080002, 390070000] is p + q, q among the first 280 primes. -/
theorem window_v67 : wem 389078190 389080002 390070000 &&& gm (wpm2 389078190 991810) (P10k.take 280) =
    wem 389078190 389080002 390070000 := by
  decide +kernel

/-- Window V68: every even n in [390070002, 391060000] is p + q, q among the first 280 primes. -/
theorem window_v68 : wem 390068190 390070002 391060000 &&& gm (wpm2 390068190 991810) (P10k.take 280) =
    wem 390068190 390070002 391060000 := by
  decide +kernel

/-- Window V69: every even n in [391060002, 392050000] is p + q, q among the first 280 primes. -/
theorem window_v69 : wem 391058190 391060002 392050000 &&& gm (wpm2 391058190 991810) (P10k.take 280) =
    wem 391058190 391060002 392050000 := by
  decide +kernel

/-- Window V70: every even n in [392050002, 393040000] is p + q, q among the first 280 primes. -/
theorem window_v70 : wem 392048190 392050002 393040000 &&& gm (wpm2 392048190 991810) (P10k.take 280) =
    wem 392048190 392050002 393040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
