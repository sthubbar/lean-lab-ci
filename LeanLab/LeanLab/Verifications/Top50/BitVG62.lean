/-
Kernel Goldbach windows V611 to V620, width 990000, covering even n in [927640002, 937540000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V611: every even n in [927640002, 928630000] is p + q, q among the first 280 primes. -/
theorem window_v611 : wem 927638190 927640002 928630000 &&& gm (wpm2 927638190 991810) (P10k.take 280) =
    wem 927638190 927640002 928630000 := by
  decide +kernel

/-- Window V612: every even n in [928630002, 929620000] is p + q, q among the first 280 primes. -/
theorem window_v612 : wem 928628190 928630002 929620000 &&& gm (wpm2 928628190 991810) (P10k.take 280) =
    wem 928628190 928630002 929620000 := by
  decide +kernel

/-- Window V613: every even n in [929620002, 930610000] is p + q, q among the first 280 primes. -/
theorem window_v613 : wem 929618190 929620002 930610000 &&& gm (wpm2 929618190 991810) (P10k.take 280) =
    wem 929618190 929620002 930610000 := by
  decide +kernel

/-- Window V614: every even n in [930610002, 931600000] is p + q, q among the first 280 primes. -/
theorem window_v614 : wem 930608190 930610002 931600000 &&& gm (wpm2 930608190 991810) (P10k.take 280) =
    wem 930608190 930610002 931600000 := by
  decide +kernel

/-- Window V615: every even n in [931600002, 932590000] is p + q, q among the first 280 primes. -/
theorem window_v615 : wem 931598190 931600002 932590000 &&& gm (wpm2 931598190 991810) (P10k.take 280) =
    wem 931598190 931600002 932590000 := by
  decide +kernel

/-- Window V616: every even n in [932590002, 933580000] is p + q, q among the first 280 primes. -/
theorem window_v616 : wem 932588190 932590002 933580000 &&& gm (wpm2 932588190 991810) (P10k.take 280) =
    wem 932588190 932590002 933580000 := by
  decide +kernel

/-- Window V617: every even n in [933580002, 934570000] is p + q, q among the first 280 primes. -/
theorem window_v617 : wem 933578190 933580002 934570000 &&& gm (wpm2 933578190 991810) (P10k.take 280) =
    wem 933578190 933580002 934570000 := by
  decide +kernel

/-- Window V618: every even n in [934570002, 935560000] is p + q, q among the first 280 primes. -/
theorem window_v618 : wem 934568190 934570002 935560000 &&& gm (wpm2 934568190 991810) (P10k.take 280) =
    wem 934568190 934570002 935560000 := by
  decide +kernel

/-- Window V619: every even n in [935560002, 936550000] is p + q, q among the first 280 primes. -/
theorem window_v619 : wem 935558190 935560002 936550000 &&& gm (wpm2 935558190 991810) (P10k.take 280) =
    wem 935558190 935560002 936550000 := by
  decide +kernel

/-- Window V620: every even n in [936550002, 937540000] is p + q, q among the first 280 primes. -/
theorem window_v620 : wem 936548190 936550002 937540000 &&& gm (wpm2 936548190 991810) (P10k.take 280) =
    wem 936548190 936550002 937540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
