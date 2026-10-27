/-
Kernel Goldbach windows MV621 to MV630, width 990000, even n in [937540002, 947440000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV621: every even n in [937540002, 938530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v621 : wem 937538190 937540002 938530000 &&& gm (wpm2 937538190 991810) (P10k.take 278) =
    wem 937538190 937540002 938530000 := by
  decide +kernel

/-- Window MV622: every even n in [938530002, 939520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v622 : wem 938528190 938530002 939520000 &&& gm (wpm2 938528190 991810) (P10k.take 278) =
    wem 938528190 938530002 939520000 := by
  decide +kernel

/-- Window MV623: every even n in [939520002, 940510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v623 : wem 939518190 939520002 940510000 &&& gm (wpm2 939518190 991810) (P10k.take 278) =
    wem 939518190 939520002 940510000 := by
  decide +kernel

/-- Window MV624: every even n in [940510002, 941500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v624 : wem 940508190 940510002 941500000 &&& gm (wpm2 940508190 991810) (P10k.take 278) =
    wem 940508190 940510002 941500000 := by
  decide +kernel

/-- Window MV625: every even n in [941500002, 942490000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v625 : wem 941498190 941500002 942490000 &&& gm (wpm2 941498190 991810) (P10k.take 278) =
    wem 941498190 941500002 942490000 := by
  decide +kernel

/-- Window MV626: every even n in [942490002, 943480000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v626 : wem 942488190 942490002 943480000 &&& gm (wpm2 942488190 991810) (P10k.take 278) =
    wem 942488190 942490002 943480000 := by
  decide +kernel

/-- Window MV627: every even n in [943480002, 944470000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v627 : wem 943478190 943480002 944470000 &&& gm (wpm2 943478190 991810) (P10k.take 278) =
    wem 943478190 943480002 944470000 := by
  decide +kernel

/-- Window MV628: every even n in [944470002, 945460000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v628 : wem 944468190 944470002 945460000 &&& gm (wpm2 944468190 991810) (P10k.take 278) =
    wem 944468190 944470002 945460000 := by
  decide +kernel

/-- Window MV629: every even n in [945460002, 946450000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v629 : wem 945458190 945460002 946450000 &&& gm (wpm2 945458190 991810) (P10k.take 278) =
    wem 945458190 945460002 946450000 := by
  decide +kernel

/-- Window MV630: every even n in [946450002, 947440000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v630 : wem 946448190 946450002 947440000 &&& gm (wpm2 946448190 991810) (P10k.take 278) =
    wem 946448190 946450002 947440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
