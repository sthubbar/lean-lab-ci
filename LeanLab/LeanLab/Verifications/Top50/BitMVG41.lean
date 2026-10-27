/-
Kernel Goldbach windows MV401 to MV410, width 990000, even n in [719740002, 729640000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV401: every even n in [719740002, 720730000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v401 : wem 719738190 719740002 720730000 &&& gm (wpm2 719738190 991810) (P10k.take 278) =
    wem 719738190 719740002 720730000 := by
  decide +kernel

/-- Window MV402: every even n in [720730002, 721720000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v402 : wem 720728190 720730002 721720000 &&& gm (wpm2 720728190 991810) (P10k.take 278) =
    wem 720728190 720730002 721720000 := by
  decide +kernel

/-- Window MV403: every even n in [721720002, 722710000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v403 : wem 721718190 721720002 722710000 &&& gm (wpm2 721718190 991810) (P10k.take 278) =
    wem 721718190 721720002 722710000 := by
  decide +kernel

/-- Window MV404: every even n in [722710002, 723700000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v404 : wem 722708190 722710002 723700000 &&& gm (wpm2 722708190 991810) (P10k.take 278) =
    wem 722708190 722710002 723700000 := by
  decide +kernel

/-- Window MV405: every even n in [723700002, 724690000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v405 : wem 723698190 723700002 724690000 &&& gm (wpm2 723698190 991810) (P10k.take 278) =
    wem 723698190 723700002 724690000 := by
  decide +kernel

/-- Window MV406: every even n in [724690002, 725680000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v406 : wem 724688190 724690002 725680000 &&& gm (wpm2 724688190 991810) (P10k.take 278) =
    wem 724688190 724690002 725680000 := by
  decide +kernel

/-- Window MV407: every even n in [725680002, 726670000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v407 : wem 725678190 725680002 726670000 &&& gm (wpm2 725678190 991810) (P10k.take 278) =
    wem 725678190 725680002 726670000 := by
  decide +kernel

/-- Window MV408: every even n in [726670002, 727660000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v408 : wem 726668190 726670002 727660000 &&& gm (wpm2 726668190 991810) (P10k.take 278) =
    wem 726668190 726670002 727660000 := by
  decide +kernel

/-- Window MV409: every even n in [727660002, 728650000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v409 : wem 727658190 727660002 728650000 &&& gm (wpm2 727658190 991810) (P10k.take 278) =
    wem 727658190 727660002 728650000 := by
  decide +kernel

/-- Window MV410: every even n in [728650002, 729640000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v410 : wem 728648190 728650002 729640000 &&& gm (wpm2 728648190 991810) (P10k.take 278) =
    wem 728648190 728650002 729640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
