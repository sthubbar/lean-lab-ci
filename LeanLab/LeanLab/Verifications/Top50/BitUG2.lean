/-
Kernel Goldbach windows U11 to V20, width 990000, covering even n in [10900002, 20800000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U11: every even n in [10900002, 11890000] is p + q, q among the first 280 primes. -/
theorem window_u11 : wem 10898190 10900002 11890000 &&& gm (wpm2 10898190 991810) (P10k.take 280) =
    wem 10898190 10900002 11890000 := by
  decide +kernel

/-- Window U12: every even n in [11890002, 12880000] is p + q, q among the first 280 primes. -/
theorem window_u12 : wem 11888190 11890002 12880000 &&& gm (wpm2 11888190 991810) (P10k.take 280) =
    wem 11888190 11890002 12880000 := by
  decide +kernel

/-- Window U13: every even n in [12880002, 13870000] is p + q, q among the first 280 primes. -/
theorem window_u13 : wem 12878190 12880002 13870000 &&& gm (wpm2 12878190 991810) (P10k.take 280) =
    wem 12878190 12880002 13870000 := by
  decide +kernel

/-- Window U14: every even n in [13870002, 14860000] is p + q, q among the first 280 primes. -/
theorem window_u14 : wem 13868190 13870002 14860000 &&& gm (wpm2 13868190 991810) (P10k.take 280) =
    wem 13868190 13870002 14860000 := by
  decide +kernel

/-- Window U15: every even n in [14860002, 15850000] is p + q, q among the first 280 primes. -/
theorem window_u15 : wem 14858190 14860002 15850000 &&& gm (wpm2 14858190 991810) (P10k.take 280) =
    wem 14858190 14860002 15850000 := by
  decide +kernel

/-- Window U16: every even n in [15850002, 16840000] is p + q, q among the first 280 primes. -/
theorem window_u16 : wem 15848190 15850002 16840000 &&& gm (wpm2 15848190 991810) (P10k.take 280) =
    wem 15848190 15850002 16840000 := by
  decide +kernel

/-- Window U17: every even n in [16840002, 17830000] is p + q, q among the first 280 primes. -/
theorem window_u17 : wem 16838190 16840002 17830000 &&& gm (wpm2 16838190 991810) (P10k.take 280) =
    wem 16838190 16840002 17830000 := by
  decide +kernel

/-- Window U18: every even n in [17830002, 18820000] is p + q, q among the first 280 primes. -/
theorem window_u18 : wem 17828190 17830002 18820000 &&& gm (wpm2 17828190 991810) (P10k.take 280) =
    wem 17828190 17830002 18820000 := by
  decide +kernel

/-- Window U19: every even n in [18820002, 19810000] is p + q, q among the first 280 primes. -/
theorem window_u19 : wem 18818190 18820002 19810000 &&& gm (wpm2 18818190 991810) (P10k.take 280) =
    wem 18818190 18820002 19810000 := by
  decide +kernel

/-- Window U20: every even n in [19810002, 20800000] is p + q, q among the first 280 primes. -/
theorem window_u20 : wem 19808190 19810002 20800000 &&& gm (wpm2 19808190 991810) (P10k.take 280) =
    wem 19808190 19810002 20800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
