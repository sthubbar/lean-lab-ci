/-
Kernel Goldbach windows MU41 to MU50, width 990000, even n in [40600002, 50500000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU41: every even n in [40600002, 41590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u41 : wem 40598190 40600002 41590000 &&& gm (wpm2 40598190 991810) (P10k.take 278) =
    wem 40598190 40600002 41590000 := by
  decide +kernel

/-- Window MU42: every even n in [41590002, 42580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u42 : wem 41588190 41590002 42580000 &&& gm (wpm2 41588190 991810) (P10k.take 278) =
    wem 41588190 41590002 42580000 := by
  decide +kernel

/-- Window MU43: every even n in [42580002, 43570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u43 : wem 42578190 42580002 43570000 &&& gm (wpm2 42578190 991810) (P10k.take 278) =
    wem 42578190 42580002 43570000 := by
  decide +kernel

/-- Window MU44: every even n in [43570002, 44560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u44 : wem 43568190 43570002 44560000 &&& gm (wpm2 43568190 991810) (P10k.take 278) =
    wem 43568190 43570002 44560000 := by
  decide +kernel

/-- Window MU45: every even n in [44560002, 45550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u45 : wem 44558190 44560002 45550000 &&& gm (wpm2 44558190 991810) (P10k.take 278) =
    wem 44558190 44560002 45550000 := by
  decide +kernel

/-- Window MU46: every even n in [45550002, 46540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u46 : wem 45548190 45550002 46540000 &&& gm (wpm2 45548190 991810) (P10k.take 278) =
    wem 45548190 45550002 46540000 := by
  decide +kernel

/-- Window MU47: every even n in [46540002, 47530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u47 : wem 46538190 46540002 47530000 &&& gm (wpm2 46538190 991810) (P10k.take 278) =
    wem 46538190 46540002 47530000 := by
  decide +kernel

/-- Window MU48: every even n in [47530002, 48520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u48 : wem 47528190 47530002 48520000 &&& gm (wpm2 47528190 991810) (P10k.take 278) =
    wem 47528190 47530002 48520000 := by
  decide +kernel

/-- Window MU49: every even n in [48520002, 49510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u49 : wem 48518190 48520002 49510000 &&& gm (wpm2 48518190 991810) (P10k.take 278) =
    wem 48518190 48520002 49510000 := by
  decide +kernel

/-- Window MU50: every even n in [49510002, 50500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u50 : wem 49508190 49510002 50500000 &&& gm (wpm2 49508190 991810) (P10k.take 278) =
    wem 49508190 49510002 50500000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
