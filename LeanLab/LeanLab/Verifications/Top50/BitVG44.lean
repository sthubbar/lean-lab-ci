/-
Kernel Goldbach windows V431 to V440, width 990000, covering even n in [749440002, 759340000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V431: every even n in [749440002, 750430000] is p + q, q among the first 280 primes. -/
theorem window_v431 : wem 749438190 749440002 750430000 &&& gm (wpm2 749438190 991810) (P10k.take 280) =
    wem 749438190 749440002 750430000 := by
  decide +kernel

/-- Window V432: every even n in [750430002, 751420000] is p + q, q among the first 280 primes. -/
theorem window_v432 : wem 750428190 750430002 751420000 &&& gm (wpm2 750428190 991810) (P10k.take 280) =
    wem 750428190 750430002 751420000 := by
  decide +kernel

/-- Window V433: every even n in [751420002, 752410000] is p + q, q among the first 280 primes. -/
theorem window_v433 : wem 751418190 751420002 752410000 &&& gm (wpm2 751418190 991810) (P10k.take 280) =
    wem 751418190 751420002 752410000 := by
  decide +kernel

/-- Window V434: every even n in [752410002, 753400000] is p + q, q among the first 280 primes. -/
theorem window_v434 : wem 752408190 752410002 753400000 &&& gm (wpm2 752408190 991810) (P10k.take 280) =
    wem 752408190 752410002 753400000 := by
  decide +kernel

/-- Window V435: every even n in [753400002, 754390000] is p + q, q among the first 280 primes. -/
theorem window_v435 : wem 753398190 753400002 754390000 &&& gm (wpm2 753398190 991810) (P10k.take 280) =
    wem 753398190 753400002 754390000 := by
  decide +kernel

/-- Window V436: every even n in [754390002, 755380000] is p + q, q among the first 280 primes. -/
theorem window_v436 : wem 754388190 754390002 755380000 &&& gm (wpm2 754388190 991810) (P10k.take 280) =
    wem 754388190 754390002 755380000 := by
  decide +kernel

/-- Window V437: every even n in [755380002, 756370000] is p + q, q among the first 280 primes. -/
theorem window_v437 : wem 755378190 755380002 756370000 &&& gm (wpm2 755378190 991810) (P10k.take 280) =
    wem 755378190 755380002 756370000 := by
  decide +kernel

/-- Window V438: every even n in [756370002, 757360000] is p + q, q among the first 280 primes. -/
theorem window_v438 : wem 756368190 756370002 757360000 &&& gm (wpm2 756368190 991810) (P10k.take 280) =
    wem 756368190 756370002 757360000 := by
  decide +kernel

/-- Window V439: every even n in [757360002, 758350000] is p + q, q among the first 280 primes. -/
theorem window_v439 : wem 757358190 757360002 758350000 &&& gm (wpm2 757358190 991810) (P10k.take 280) =
    wem 757358190 757360002 758350000 := by
  decide +kernel

/-- Window V440: every even n in [758350002, 759340000] is p + q, q among the first 280 primes. -/
theorem window_v440 : wem 758348190 758350002 759340000 &&& gm (wpm2 758348190 991810) (P10k.take 280) =
    wem 758348190 758350002 759340000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
