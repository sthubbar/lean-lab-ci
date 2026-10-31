/-
Kernel Goldbach windows V511 to V520, width 990000, covering even n in [828640002, 838540000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V511: every even n in [828640002, 829630000] is p + q, q among the first 280 primes. -/
theorem window_v511 : wem 828638190 828640002 829630000 &&& gm (wpm2 828638190 991810) (P10k.take 280) =
    wem 828638190 828640002 829630000 := by
  decide +kernel

/-- Window V512: every even n in [829630002, 830620000] is p + q, q among the first 280 primes. -/
theorem window_v512 : wem 829628190 829630002 830620000 &&& gm (wpm2 829628190 991810) (P10k.take 280) =
    wem 829628190 829630002 830620000 := by
  decide +kernel

/-- Window V513: every even n in [830620002, 831610000] is p + q, q among the first 280 primes. -/
theorem window_v513 : wem 830618190 830620002 831610000 &&& gm (wpm2 830618190 991810) (P10k.take 280) =
    wem 830618190 830620002 831610000 := by
  decide +kernel

/-- Window V514: every even n in [831610002, 832600000] is p + q, q among the first 280 primes. -/
theorem window_v514 : wem 831608190 831610002 832600000 &&& gm (wpm2 831608190 991810) (P10k.take 280) =
    wem 831608190 831610002 832600000 := by
  decide +kernel

/-- Window V515: every even n in [832600002, 833590000] is p + q, q among the first 280 primes. -/
theorem window_v515 : wem 832598190 832600002 833590000 &&& gm (wpm2 832598190 991810) (P10k.take 280) =
    wem 832598190 832600002 833590000 := by
  decide +kernel

/-- Window V516: every even n in [833590002, 834580000] is p + q, q among the first 280 primes. -/
theorem window_v516 : wem 833588190 833590002 834580000 &&& gm (wpm2 833588190 991810) (P10k.take 280) =
    wem 833588190 833590002 834580000 := by
  decide +kernel

/-- Window V517: every even n in [834580002, 835570000] is p + q, q among the first 280 primes. -/
theorem window_v517 : wem 834578190 834580002 835570000 &&& gm (wpm2 834578190 991810) (P10k.take 280) =
    wem 834578190 834580002 835570000 := by
  decide +kernel

/-- Window V518: every even n in [835570002, 836560000] is p + q, q among the first 280 primes. -/
theorem window_v518 : wem 835568190 835570002 836560000 &&& gm (wpm2 835568190 991810) (P10k.take 280) =
    wem 835568190 835570002 836560000 := by
  decide +kernel

/-- Window V519: every even n in [836560002, 837550000] is p + q, q among the first 280 primes. -/
theorem window_v519 : wem 836558190 836560002 837550000 &&& gm (wpm2 836558190 991810) (P10k.take 280) =
    wem 836558190 836560002 837550000 := by
  decide +kernel

/-- Window V520: every even n in [837550002, 838540000] is p + q, q among the first 280 primes. -/
theorem window_v520 : wem 837548190 837550002 838540000 &&& gm (wpm2 837548190 991810) (P10k.take 280) =
    wem 837548190 837550002 838540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
