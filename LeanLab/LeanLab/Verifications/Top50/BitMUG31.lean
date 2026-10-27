/-
Kernel Goldbach windows MU301 to MU310, width 990000, even n in [298000002, 307900000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU301: every even n in [298000002, 298990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u301 : wem 297998190 298000002 298990000 &&& gm (wpm2 297998190 991810) (P10k.take 278) =
    wem 297998190 298000002 298990000 := by
  decide +kernel

/-- Window MU302: every even n in [298990002, 299980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u302 : wem 298988190 298990002 299980000 &&& gm (wpm2 298988190 991810) (P10k.take 278) =
    wem 298988190 298990002 299980000 := by
  decide +kernel

/-- Window MU303: every even n in [299980002, 300970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u303 : wem 299978190 299980002 300970000 &&& gm (wpm2 299978190 991810) (P10k.take 278) =
    wem 299978190 299980002 300970000 := by
  decide +kernel

/-- Window MU304: every even n in [300970002, 301960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u304 : wem 300968190 300970002 301960000 &&& gm (wpm2 300968190 991810) (P10k.take 278) =
    wem 300968190 300970002 301960000 := by
  decide +kernel

/-- Window MU305: every even n in [301960002, 302950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u305 : wem 301958190 301960002 302950000 &&& gm (wpm2 301958190 991810) (P10k.take 278) =
    wem 301958190 301960002 302950000 := by
  decide +kernel

/-- Window MU306: every even n in [302950002, 303940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u306 : wem 302948190 302950002 303940000 &&& gm (wpm2 302948190 991810) (P10k.take 278) =
    wem 302948190 302950002 303940000 := by
  decide +kernel

/-- Window MU307: every even n in [303940002, 304930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u307 : wem 303938190 303940002 304930000 &&& gm (wpm2 303938190 991810) (P10k.take 278) =
    wem 303938190 303940002 304930000 := by
  decide +kernel

/-- Window MU308: every even n in [304930002, 305920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u308 : wem 304928190 304930002 305920000 &&& gm (wpm2 304928190 991810) (P10k.take 278) =
    wem 304928190 304930002 305920000 := by
  decide +kernel

/-- Window MU309: every even n in [305920002, 306910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u309 : wem 305918190 305920002 306910000 &&& gm (wpm2 305918190 991810) (P10k.take 278) =
    wem 305918190 305920002 306910000 := by
  decide +kernel

/-- Window MU310: every even n in [306910002, 307900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u310 : wem 306908190 306910002 307900000 &&& gm (wpm2 306908190 991810) (P10k.take 278) =
    wem 306908190 306910002 307900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
