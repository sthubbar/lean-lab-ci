/-
Kernel Goldbach windows V411 to V420, width 990000, covering even n in [729640002, 739540000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V411: every even n in [729640002, 730630000] is p + q, q among the first 280 primes. -/
theorem window_v411 : wem 729638190 729640002 730630000 &&& gm (wpm2 729638190 991810) (P10k.take 280) =
    wem 729638190 729640002 730630000 := by
  decide +kernel

/-- Window V412: every even n in [730630002, 731620000] is p + q, q among the first 280 primes. -/
theorem window_v412 : wem 730628190 730630002 731620000 &&& gm (wpm2 730628190 991810) (P10k.take 280) =
    wem 730628190 730630002 731620000 := by
  decide +kernel

/-- Window V413: every even n in [731620002, 732610000] is p + q, q among the first 280 primes. -/
theorem window_v413 : wem 731618190 731620002 732610000 &&& gm (wpm2 731618190 991810) (P10k.take 280) =
    wem 731618190 731620002 732610000 := by
  decide +kernel

/-- Window V414: every even n in [732610002, 733600000] is p + q, q among the first 280 primes. -/
theorem window_v414 : wem 732608190 732610002 733600000 &&& gm (wpm2 732608190 991810) (P10k.take 280) =
    wem 732608190 732610002 733600000 := by
  decide +kernel

/-- Window V415: every even n in [733600002, 734590000] is p + q, q among the first 280 primes. -/
theorem window_v415 : wem 733598190 733600002 734590000 &&& gm (wpm2 733598190 991810) (P10k.take 280) =
    wem 733598190 733600002 734590000 := by
  decide +kernel

/-- Window V416: every even n in [734590002, 735580000] is p + q, q among the first 280 primes. -/
theorem window_v416 : wem 734588190 734590002 735580000 &&& gm (wpm2 734588190 991810) (P10k.take 280) =
    wem 734588190 734590002 735580000 := by
  decide +kernel

/-- Window V417: every even n in [735580002, 736570000] is p + q, q among the first 280 primes. -/
theorem window_v417 : wem 735578190 735580002 736570000 &&& gm (wpm2 735578190 991810) (P10k.take 280) =
    wem 735578190 735580002 736570000 := by
  decide +kernel

/-- Window V418: every even n in [736570002, 737560000] is p + q, q among the first 280 primes. -/
theorem window_v418 : wem 736568190 736570002 737560000 &&& gm (wpm2 736568190 991810) (P10k.take 280) =
    wem 736568190 736570002 737560000 := by
  decide +kernel

/-- Window V419: every even n in [737560002, 738550000] is p + q, q among the first 280 primes. -/
theorem window_v419 : wem 737558190 737560002 738550000 &&& gm (wpm2 737558190 991810) (P10k.take 280) =
    wem 737558190 737560002 738550000 := by
  decide +kernel

/-- Window V420: every even n in [738550002, 739540000] is p + q, q among the first 280 primes. -/
theorem window_v420 : wem 738548190 738550002 739540000 &&& gm (wpm2 738548190 991810) (P10k.take 280) =
    wem 738548190 738550002 739540000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
