/-
Kernel Goldbach windows V251 to V260, width 990000, covering even n in [571240002, 581140000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V251: every even n in [571240002, 572230000] is p + q, q among the first 280 primes. -/
theorem window_v251 : wem 571238190 571240002 572230000 &&& gm (wpm2 571238190 991810) (P10k.take 280) =
    wem 571238190 571240002 572230000 := by
  decide +kernel

/-- Window V252: every even n in [572230002, 573220000] is p + q, q among the first 280 primes. -/
theorem window_v252 : wem 572228190 572230002 573220000 &&& gm (wpm2 572228190 991810) (P10k.take 280) =
    wem 572228190 572230002 573220000 := by
  decide +kernel

/-- Window V253: every even n in [573220002, 574210000] is p + q, q among the first 280 primes. -/
theorem window_v253 : wem 573218190 573220002 574210000 &&& gm (wpm2 573218190 991810) (P10k.take 280) =
    wem 573218190 573220002 574210000 := by
  decide +kernel

/-- Window V254: every even n in [574210002, 575200000] is p + q, q among the first 280 primes. -/
theorem window_v254 : wem 574208190 574210002 575200000 &&& gm (wpm2 574208190 991810) (P10k.take 280) =
    wem 574208190 574210002 575200000 := by
  decide +kernel

/-- Window V255: every even n in [575200002, 576190000] is p + q, q among the first 280 primes. -/
theorem window_v255 : wem 575198190 575200002 576190000 &&& gm (wpm2 575198190 991810) (P10k.take 280) =
    wem 575198190 575200002 576190000 := by
  decide +kernel

/-- Window V256: every even n in [576190002, 577180000] is p + q, q among the first 280 primes. -/
theorem window_v256 : wem 576188190 576190002 577180000 &&& gm (wpm2 576188190 991810) (P10k.take 280) =
    wem 576188190 576190002 577180000 := by
  decide +kernel

/-- Window V257: every even n in [577180002, 578170000] is p + q, q among the first 280 primes. -/
theorem window_v257 : wem 577178190 577180002 578170000 &&& gm (wpm2 577178190 991810) (P10k.take 280) =
    wem 577178190 577180002 578170000 := by
  decide +kernel

/-- Window V258: every even n in [578170002, 579160000] is p + q, q among the first 280 primes. -/
theorem window_v258 : wem 578168190 578170002 579160000 &&& gm (wpm2 578168190 991810) (P10k.take 280) =
    wem 578168190 578170002 579160000 := by
  decide +kernel

/-- Window V259: every even n in [579160002, 580150000] is p + q, q among the first 280 primes. -/
theorem window_v259 : wem 579158190 579160002 580150000 &&& gm (wpm2 579158190 991810) (P10k.take 280) =
    wem 579158190 579160002 580150000 := by
  decide +kernel

/-- Window V260: every even n in [580150002, 581140000] is p + q, q among the first 280 primes. -/
theorem window_v260 : wem 580148190 580150002 581140000 &&& gm (wpm2 580148190 991810) (P10k.take 280) =
    wem 580148190 580150002 581140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
