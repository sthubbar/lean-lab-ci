/-
Kernel Goldbach windows V601 to V610, width 990000, covering even n in [917740002, 927640000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V601: every even n in [917740002, 918730000] is p + q, q among the first 280 primes. -/
theorem window_v601 : wem 917738190 917740002 918730000 &&& gm (wpm2 917738190 991810) (P10k.take 280) =
    wem 917738190 917740002 918730000 := by
  decide +kernel

/-- Window V602: every even n in [918730002, 919720000] is p + q, q among the first 280 primes. -/
theorem window_v602 : wem 918728190 918730002 919720000 &&& gm (wpm2 918728190 991810) (P10k.take 280) =
    wem 918728190 918730002 919720000 := by
  decide +kernel

/-- Window V603: every even n in [919720002, 920710000] is p + q, q among the first 280 primes. -/
theorem window_v603 : wem 919718190 919720002 920710000 &&& gm (wpm2 919718190 991810) (P10k.take 280) =
    wem 919718190 919720002 920710000 := by
  decide +kernel

/-- Window V604: every even n in [920710002, 921700000] is p + q, q among the first 280 primes. -/
theorem window_v604 : wem 920708190 920710002 921700000 &&& gm (wpm2 920708190 991810) (P10k.take 280) =
    wem 920708190 920710002 921700000 := by
  decide +kernel

/-- Window V605: every even n in [921700002, 922690000] is p + q, q among the first 280 primes. -/
theorem window_v605 : wem 921698190 921700002 922690000 &&& gm (wpm2 921698190 991810) (P10k.take 280) =
    wem 921698190 921700002 922690000 := by
  decide +kernel

/-- Window V606: every even n in [922690002, 923680000] is p + q, q among the first 280 primes. -/
theorem window_v606 : wem 922688190 922690002 923680000 &&& gm (wpm2 922688190 991810) (P10k.take 280) =
    wem 922688190 922690002 923680000 := by
  decide +kernel

/-- Window V607: every even n in [923680002, 924670000] is p + q, q among the first 280 primes. -/
theorem window_v607 : wem 923678190 923680002 924670000 &&& gm (wpm2 923678190 991810) (P10k.take 280) =
    wem 923678190 923680002 924670000 := by
  decide +kernel

/-- Window V608: every even n in [924670002, 925660000] is p + q, q among the first 280 primes. -/
theorem window_v608 : wem 924668190 924670002 925660000 &&& gm (wpm2 924668190 991810) (P10k.take 280) =
    wem 924668190 924670002 925660000 := by
  decide +kernel

/-- Window V609: every even n in [925660002, 926650000] is p + q, q among the first 280 primes. -/
theorem window_v609 : wem 925658190 925660002 926650000 &&& gm (wpm2 925658190 991810) (P10k.take 280) =
    wem 925658190 925660002 926650000 := by
  decide +kernel

/-- Window V610: every even n in [926650002, 927640000] is p + q, q among the first 280 primes. -/
theorem window_v610 : wem 926648190 926650002 927640000 &&& gm (wpm2 926648190 991810) (P10k.take 280) =
    wem 926648190 926650002 927640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
