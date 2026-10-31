/-
Kernel Goldbach windows V381 to V390, width 990000, covering even n in [699940002, 709840000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V381: every even n in [699940002, 700930000] is p + q, q among the first 280 primes. -/
theorem window_v381 : wem 699938190 699940002 700930000 &&& gm (wpm2 699938190 991810) (P10k.take 280) =
    wem 699938190 699940002 700930000 := by
  decide +kernel

/-- Window V382: every even n in [700930002, 701920000] is p + q, q among the first 280 primes. -/
theorem window_v382 : wem 700928190 700930002 701920000 &&& gm (wpm2 700928190 991810) (P10k.take 280) =
    wem 700928190 700930002 701920000 := by
  decide +kernel

/-- Window V383: every even n in [701920002, 702910000] is p + q, q among the first 280 primes. -/
theorem window_v383 : wem 701918190 701920002 702910000 &&& gm (wpm2 701918190 991810) (P10k.take 280) =
    wem 701918190 701920002 702910000 := by
  decide +kernel

/-- Window V384: every even n in [702910002, 703900000] is p + q, q among the first 280 primes. -/
theorem window_v384 : wem 702908190 702910002 703900000 &&& gm (wpm2 702908190 991810) (P10k.take 280) =
    wem 702908190 702910002 703900000 := by
  decide +kernel

/-- Window V385: every even n in [703900002, 704890000] is p + q, q among the first 280 primes. -/
theorem window_v385 : wem 703898190 703900002 704890000 &&& gm (wpm2 703898190 991810) (P10k.take 280) =
    wem 703898190 703900002 704890000 := by
  decide +kernel

/-- Window V386: every even n in [704890002, 705880000] is p + q, q among the first 280 primes. -/
theorem window_v386 : wem 704888190 704890002 705880000 &&& gm (wpm2 704888190 991810) (P10k.take 280) =
    wem 704888190 704890002 705880000 := by
  decide +kernel

/-- Window V387: every even n in [705880002, 706870000] is p + q, q among the first 280 primes. -/
theorem window_v387 : wem 705878190 705880002 706870000 &&& gm (wpm2 705878190 991810) (P10k.take 280) =
    wem 705878190 705880002 706870000 := by
  decide +kernel

/-- Window V388: every even n in [706870002, 707860000] is p + q, q among the first 280 primes. -/
theorem window_v388 : wem 706868190 706870002 707860000 &&& gm (wpm2 706868190 991810) (P10k.take 280) =
    wem 706868190 706870002 707860000 := by
  decide +kernel

/-- Window V389: every even n in [707860002, 708850000] is p + q, q among the first 280 primes. -/
theorem window_v389 : wem 707858190 707860002 708850000 &&& gm (wpm2 707858190 991810) (P10k.take 280) =
    wem 707858190 707860002 708850000 := by
  decide +kernel

/-- Window V390: every even n in [708850002, 709840000] is p + q, q among the first 280 primes. -/
theorem window_v390 : wem 708848190 708850002 709840000 &&& gm (wpm2 708848190 991810) (P10k.take 280) =
    wem 708848190 708850002 709840000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
