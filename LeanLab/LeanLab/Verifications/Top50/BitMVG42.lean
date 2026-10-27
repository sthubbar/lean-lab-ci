/-
Kernel Goldbach windows MV411 to MV420, width 990000, even n in [729640002, 739540000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV411: every even n in [729640002, 730630000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v411 : wem 729638190 729640002 730630000 &&& gm (wpm2 729638190 991810) (P10k.take 278) =
    wem 729638190 729640002 730630000 := by
  decide +kernel

/-- Window MV412: every even n in [730630002, 731620000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v412 : wem 730628190 730630002 731620000 &&& gm (wpm2 730628190 991810) (P10k.take 278) =
    wem 730628190 730630002 731620000 := by
  decide +kernel

/-- Window MV413: every even n in [731620002, 732610000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v413 : wem 731618190 731620002 732610000 &&& gm (wpm2 731618190 991810) (P10k.take 278) =
    wem 731618190 731620002 732610000 := by
  decide +kernel

/-- Window MV414: every even n in [732610002, 733600000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v414 : wem 732608190 732610002 733600000 &&& gm (wpm2 732608190 991810) (P10k.take 278) =
    wem 732608190 732610002 733600000 := by
  decide +kernel

/-- Window MV415: every even n in [733600002, 734590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v415 : wem 733598190 733600002 734590000 &&& gm (wpm2 733598190 991810) (P10k.take 278) =
    wem 733598190 733600002 734590000 := by
  decide +kernel

/-- Window MV416: every even n in [734590002, 735580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v416 : wem 734588190 734590002 735580000 &&& gm (wpm2 734588190 991810) (P10k.take 278) =
    wem 734588190 734590002 735580000 := by
  decide +kernel

/-- Window MV417: every even n in [735580002, 736570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v417 : wem 735578190 735580002 736570000 &&& gm (wpm2 735578190 991810) (P10k.take 278) =
    wem 735578190 735580002 736570000 := by
  decide +kernel

/-- Window MV418: every even n in [736570002, 737560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v418 : wem 736568190 736570002 737560000 &&& gm (wpm2 736568190 991810) (P10k.take 278) =
    wem 736568190 736570002 737560000 := by
  decide +kernel

/-- Window MV419: every even n in [737560002, 738550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v419 : wem 737558190 737560002 738550000 &&& gm (wpm2 737558190 991810) (P10k.take 278) =
    wem 737558190 737560002 738550000 := by
  decide +kernel

/-- Window MV420: every even n in [738550002, 739540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v420 : wem 738548190 738550002 739540000 &&& gm (wpm2 738548190 991810) (P10k.take 278) =
    wem 738548190 738550002 739540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
