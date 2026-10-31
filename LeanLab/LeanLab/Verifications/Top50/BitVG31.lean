/-
Kernel Goldbach windows V301 to V310, width 990000, covering even n in [620740002, 630640000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V301: every even n in [620740002, 621730000] is p + q, q among the first 280 primes. -/
theorem window_v301 : wem 620738190 620740002 621730000 &&& gm (wpm2 620738190 991810) (P10k.take 280) =
    wem 620738190 620740002 621730000 := by
  decide +kernel

/-- Window V302: every even n in [621730002, 622720000] is p + q, q among the first 280 primes. -/
theorem window_v302 : wem 621728190 621730002 622720000 &&& gm (wpm2 621728190 991810) (P10k.take 280) =
    wem 621728190 621730002 622720000 := by
  decide +kernel

/-- Window V303: every even n in [622720002, 623710000] is p + q, q among the first 280 primes. -/
theorem window_v303 : wem 622718190 622720002 623710000 &&& gm (wpm2 622718190 991810) (P10k.take 280) =
    wem 622718190 622720002 623710000 := by
  decide +kernel

/-- Window V304: every even n in [623710002, 624700000] is p + q, q among the first 280 primes. -/
theorem window_v304 : wem 623708190 623710002 624700000 &&& gm (wpm2 623708190 991810) (P10k.take 280) =
    wem 623708190 623710002 624700000 := by
  decide +kernel

/-- Window V305: every even n in [624700002, 625690000] is p + q, q among the first 280 primes. -/
theorem window_v305 : wem 624698190 624700002 625690000 &&& gm (wpm2 624698190 991810) (P10k.take 280) =
    wem 624698190 624700002 625690000 := by
  decide +kernel

/-- Window V306: every even n in [625690002, 626680000] is p + q, q among the first 280 primes. -/
theorem window_v306 : wem 625688190 625690002 626680000 &&& gm (wpm2 625688190 991810) (P10k.take 280) =
    wem 625688190 625690002 626680000 := by
  decide +kernel

/-- Window V307: every even n in [626680002, 627670000] is p + q, q among the first 280 primes. -/
theorem window_v307 : wem 626678190 626680002 627670000 &&& gm (wpm2 626678190 991810) (P10k.take 280) =
    wem 626678190 626680002 627670000 := by
  decide +kernel

/-- Window V308: every even n in [627670002, 628660000] is p + q, q among the first 280 primes. -/
theorem window_v308 : wem 627668190 627670002 628660000 &&& gm (wpm2 627668190 991810) (P10k.take 280) =
    wem 627668190 627670002 628660000 := by
  decide +kernel

/-- Window V309: every even n in [628660002, 629650000] is p + q, q among the first 280 primes. -/
theorem window_v309 : wem 628658190 628660002 629650000 &&& gm (wpm2 628658190 991810) (P10k.take 280) =
    wem 628658190 628660002 629650000 := by
  decide +kernel

/-- Window V310: every even n in [629650002, 630640000] is p + q, q among the first 280 primes. -/
theorem window_v310 : wem 629648190 629650002 630640000 &&& gm (wpm2 629648190 991810) (P10k.take 280) =
    wem 629648190 629650002 630640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
