/-
Kernel Goldbach windows MV351 to MV360, width 990000, even n in [670240002, 680140000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV351: every even n in [670240002, 671230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v351 : wem 670238190 670240002 671230000 &&& gm (wpm2 670238190 991810) (P10k.take 278) =
    wem 670238190 670240002 671230000 := by
  decide +kernel

/-- Window MV352: every even n in [671230002, 672220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v352 : wem 671228190 671230002 672220000 &&& gm (wpm2 671228190 991810) (P10k.take 278) =
    wem 671228190 671230002 672220000 := by
  decide +kernel

/-- Window MV353: every even n in [672220002, 673210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v353 : wem 672218190 672220002 673210000 &&& gm (wpm2 672218190 991810) (P10k.take 278) =
    wem 672218190 672220002 673210000 := by
  decide +kernel

/-- Window MV354: every even n in [673210002, 674200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v354 : wem 673208190 673210002 674200000 &&& gm (wpm2 673208190 991810) (P10k.take 278) =
    wem 673208190 673210002 674200000 := by
  decide +kernel

/-- Window MV355: every even n in [674200002, 675190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v355 : wem 674198190 674200002 675190000 &&& gm (wpm2 674198190 991810) (P10k.take 278) =
    wem 674198190 674200002 675190000 := by
  decide +kernel

/-- Window MV356: every even n in [675190002, 676180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v356 : wem 675188190 675190002 676180000 &&& gm (wpm2 675188190 991810) (P10k.take 278) =
    wem 675188190 675190002 676180000 := by
  decide +kernel

/-- Window MV357: every even n in [676180002, 677170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v357 : wem 676178190 676180002 677170000 &&& gm (wpm2 676178190 991810) (P10k.take 278) =
    wem 676178190 676180002 677170000 := by
  decide +kernel

/-- Window MV358: every even n in [677170002, 678160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v358 : wem 677168190 677170002 678160000 &&& gm (wpm2 677168190 991810) (P10k.take 278) =
    wem 677168190 677170002 678160000 := by
  decide +kernel

/-- Window MV359: every even n in [678160002, 679150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v359 : wem 678158190 678160002 679150000 &&& gm (wpm2 678158190 991810) (P10k.take 278) =
    wem 678158190 678160002 679150000 := by
  decide +kernel

/-- Window MV360: every even n in [679150002, 680140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v360 : wem 679148190 679150002 680140000 &&& gm (wpm2 679148190 991810) (P10k.take 278) =
    wem 679148190 679150002 680140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
