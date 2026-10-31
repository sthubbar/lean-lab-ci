/-
Kernel Goldbach windows U251 to V260, width 990000, covering even n in [248500002, 258400000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U251: every even n in [248500002, 249490000] is p + q, q among the first 280 primes. -/
theorem window_u251 : wem 248498190 248500002 249490000 &&& gm (wpm2 248498190 991810) (P10k.take 280) =
    wem 248498190 248500002 249490000 := by
  decide +kernel

/-- Window U252: every even n in [249490002, 250480000] is p + q, q among the first 280 primes. -/
theorem window_u252 : wem 249488190 249490002 250480000 &&& gm (wpm2 249488190 991810) (P10k.take 280) =
    wem 249488190 249490002 250480000 := by
  decide +kernel

/-- Window U253: every even n in [250480002, 251470000] is p + q, q among the first 280 primes. -/
theorem window_u253 : wem 250478190 250480002 251470000 &&& gm (wpm2 250478190 991810) (P10k.take 280) =
    wem 250478190 250480002 251470000 := by
  decide +kernel

/-- Window U254: every even n in [251470002, 252460000] is p + q, q among the first 280 primes. -/
theorem window_u254 : wem 251468190 251470002 252460000 &&& gm (wpm2 251468190 991810) (P10k.take 280) =
    wem 251468190 251470002 252460000 := by
  decide +kernel

/-- Window U255: every even n in [252460002, 253450000] is p + q, q among the first 280 primes. -/
theorem window_u255 : wem 252458190 252460002 253450000 &&& gm (wpm2 252458190 991810) (P10k.take 280) =
    wem 252458190 252460002 253450000 := by
  decide +kernel

/-- Window U256: every even n in [253450002, 254440000] is p + q, q among the first 280 primes. -/
theorem window_u256 : wem 253448190 253450002 254440000 &&& gm (wpm2 253448190 991810) (P10k.take 280) =
    wem 253448190 253450002 254440000 := by
  decide +kernel

/-- Window U257: every even n in [254440002, 255430000] is p + q, q among the first 280 primes. -/
theorem window_u257 : wem 254438190 254440002 255430000 &&& gm (wpm2 254438190 991810) (P10k.take 280) =
    wem 254438190 254440002 255430000 := by
  decide +kernel

/-- Window U258: every even n in [255430002, 256420000] is p + q, q among the first 280 primes. -/
theorem window_u258 : wem 255428190 255430002 256420000 &&& gm (wpm2 255428190 991810) (P10k.take 280) =
    wem 255428190 255430002 256420000 := by
  decide +kernel

/-- Window U259: every even n in [256420002, 257410000] is p + q, q among the first 280 primes. -/
theorem window_u259 : wem 256418190 256420002 257410000 &&& gm (wpm2 256418190 991810) (P10k.take 280) =
    wem 256418190 256420002 257410000 := by
  decide +kernel

/-- Window U260: every even n in [257410002, 258400000] is p + q, q among the first 280 primes. -/
theorem window_u260 : wem 257408190 257410002 258400000 &&& gm (wpm2 257408190 991810) (P10k.take 280) =
    wem 257408190 257410002 258400000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
