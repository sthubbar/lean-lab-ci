/-
Kernel Goldbach windows U111 to V120, width 990000, covering even n in [109900002, 119800000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U111: every even n in [109900002, 110890000] is p + q, q among the first 280 primes. -/
theorem window_u111 : wem 109898190 109900002 110890000 &&& gm (wpm2 109898190 991810) (P10k.take 280) =
    wem 109898190 109900002 110890000 := by
  decide +kernel

/-- Window U112: every even n in [110890002, 111880000] is p + q, q among the first 280 primes. -/
theorem window_u112 : wem 110888190 110890002 111880000 &&& gm (wpm2 110888190 991810) (P10k.take 280) =
    wem 110888190 110890002 111880000 := by
  decide +kernel

/-- Window U113: every even n in [111880002, 112870000] is p + q, q among the first 280 primes. -/
theorem window_u113 : wem 111878190 111880002 112870000 &&& gm (wpm2 111878190 991810) (P10k.take 280) =
    wem 111878190 111880002 112870000 := by
  decide +kernel

/-- Window U114: every even n in [112870002, 113860000] is p + q, q among the first 280 primes. -/
theorem window_u114 : wem 112868190 112870002 113860000 &&& gm (wpm2 112868190 991810) (P10k.take 280) =
    wem 112868190 112870002 113860000 := by
  decide +kernel

/-- Window U115: every even n in [113860002, 114850000] is p + q, q among the first 280 primes. -/
theorem window_u115 : wem 113858190 113860002 114850000 &&& gm (wpm2 113858190 991810) (P10k.take 280) =
    wem 113858190 113860002 114850000 := by
  decide +kernel

/-- Window U116: every even n in [114850002, 115840000] is p + q, q among the first 280 primes. -/
theorem window_u116 : wem 114848190 114850002 115840000 &&& gm (wpm2 114848190 991810) (P10k.take 280) =
    wem 114848190 114850002 115840000 := by
  decide +kernel

/-- Window U117: every even n in [115840002, 116830000] is p + q, q among the first 280 primes. -/
theorem window_u117 : wem 115838190 115840002 116830000 &&& gm (wpm2 115838190 991810) (P10k.take 280) =
    wem 115838190 115840002 116830000 := by
  decide +kernel

/-- Window U118: every even n in [116830002, 117820000] is p + q, q among the first 280 primes. -/
theorem window_u118 : wem 116828190 116830002 117820000 &&& gm (wpm2 116828190 991810) (P10k.take 280) =
    wem 116828190 116830002 117820000 := by
  decide +kernel

/-- Window U119: every even n in [117820002, 118810000] is p + q, q among the first 280 primes. -/
theorem window_u119 : wem 117818190 117820002 118810000 &&& gm (wpm2 117818190 991810) (P10k.take 280) =
    wem 117818190 117820002 118810000 := by
  decide +kernel

/-- Window U120: every even n in [118810002, 119800000] is p + q, q among the first 280 primes. -/
theorem window_u120 : wem 118808190 118810002 119800000 &&& gm (wpm2 118808190 991810) (P10k.take 280) =
    wem 118808190 118810002 119800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
