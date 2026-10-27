/-
Kernel Goldbach windows MU241 to MU250, width 990000, even n in [238600002, 248500000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU241: every even n in [238600002, 239590000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u241 : wem 238598190 238600002 239590000 &&& gm (wpm2 238598190 991810) (P10k.take 278) =
    wem 238598190 238600002 239590000 := by
  decide +kernel

/-- Window MU242: every even n in [239590002, 240580000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u242 : wem 239588190 239590002 240580000 &&& gm (wpm2 239588190 991810) (P10k.take 278) =
    wem 239588190 239590002 240580000 := by
  decide +kernel

/-- Window MU243: every even n in [240580002, 241570000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u243 : wem 240578190 240580002 241570000 &&& gm (wpm2 240578190 991810) (P10k.take 278) =
    wem 240578190 240580002 241570000 := by
  decide +kernel

/-- Window MU244: every even n in [241570002, 242560000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u244 : wem 241568190 241570002 242560000 &&& gm (wpm2 241568190 991810) (P10k.take 278) =
    wem 241568190 241570002 242560000 := by
  decide +kernel

/-- Window MU245: every even n in [242560002, 243550000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u245 : wem 242558190 242560002 243550000 &&& gm (wpm2 242558190 991810) (P10k.take 278) =
    wem 242558190 242560002 243550000 := by
  decide +kernel

/-- Window MU246: every even n in [243550002, 244540000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u246 : wem 243548190 243550002 244540000 &&& gm (wpm2 243548190 991810) (P10k.take 278) =
    wem 243548190 243550002 244540000 := by
  decide +kernel

/-- Window MU247: every even n in [244540002, 245530000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u247 : wem 244538190 244540002 245530000 &&& gm (wpm2 244538190 991810) (P10k.take 278) =
    wem 244538190 244540002 245530000 := by
  decide +kernel

/-- Window MU248: every even n in [245530002, 246520000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u248 : wem 245528190 245530002 246520000 &&& gm (wpm2 245528190 991810) (P10k.take 278) =
    wem 245528190 245530002 246520000 := by
  decide +kernel

/-- Window MU249: every even n in [246520002, 247510000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u249 : wem 246518190 246520002 247510000 &&& gm (wpm2 246518190 991810) (P10k.take 278) =
    wem 246518190 246520002 247510000 := by
  decide +kernel

/-- Window MU250: every even n in [247510002, 248500000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u250 : wem 247508190 247510002 248500000 &&& gm (wpm2 247508190 991810) (P10k.take 278) =
    wem 247508190 247510002 248500000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
