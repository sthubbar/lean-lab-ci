/-
Kernel Goldbach windows V171 to V180, width 990000, covering even n in [492040002, 501940000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V171: every even n in [492040002, 493030000] is p + q, q among the first 280 primes. -/
theorem window_v171 : wem 492038190 492040002 493030000 &&& gm (wpm2 492038190 991810) (P10k.take 280) =
    wem 492038190 492040002 493030000 := by
  decide +kernel

/-- Window V172: every even n in [493030002, 494020000] is p + q, q among the first 280 primes. -/
theorem window_v172 : wem 493028190 493030002 494020000 &&& gm (wpm2 493028190 991810) (P10k.take 280) =
    wem 493028190 493030002 494020000 := by
  decide +kernel

/-- Window V173: every even n in [494020002, 495010000] is p + q, q among the first 280 primes. -/
theorem window_v173 : wem 494018190 494020002 495010000 &&& gm (wpm2 494018190 991810) (P10k.take 280) =
    wem 494018190 494020002 495010000 := by
  decide +kernel

/-- Window V174: every even n in [495010002, 496000000] is p + q, q among the first 280 primes. -/
theorem window_v174 : wem 495008190 495010002 496000000 &&& gm (wpm2 495008190 991810) (P10k.take 280) =
    wem 495008190 495010002 496000000 := by
  decide +kernel

/-- Window V175: every even n in [496000002, 496990000] is p + q, q among the first 280 primes. -/
theorem window_v175 : wem 495998190 496000002 496990000 &&& gm (wpm2 495998190 991810) (P10k.take 280) =
    wem 495998190 496000002 496990000 := by
  decide +kernel

/-- Window V176: every even n in [496990002, 497980000] is p + q, q among the first 280 primes. -/
theorem window_v176 : wem 496988190 496990002 497980000 &&& gm (wpm2 496988190 991810) (P10k.take 280) =
    wem 496988190 496990002 497980000 := by
  decide +kernel

/-- Window V177: every even n in [497980002, 498970000] is p + q, q among the first 280 primes. -/
theorem window_v177 : wem 497978190 497980002 498970000 &&& gm (wpm2 497978190 991810) (P10k.take 280) =
    wem 497978190 497980002 498970000 := by
  decide +kernel

/-- Window V178: every even n in [498970002, 499960000] is p + q, q among the first 280 primes. -/
theorem window_v178 : wem 498968190 498970002 499960000 &&& gm (wpm2 498968190 991810) (P10k.take 280) =
    wem 498968190 498970002 499960000 := by
  decide +kernel

/-- Window V179: every even n in [499960002, 500950000] is p + q, q among the first 280 primes. -/
theorem window_v179 : wem 499958190 499960002 500950000 &&& gm (wpm2 499958190 991810) (P10k.take 280) =
    wem 499958190 499960002 500950000 := by
  decide +kernel

/-- Window V180: every even n in [500950002, 501940000] is p + q, q among the first 280 primes. -/
theorem window_v180 : wem 500948190 500950002 501940000 &&& gm (wpm2 500948190 991810) (P10k.take 280) =
    wem 500948190 500950002 501940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
