/-
Kernel Goldbach windows MV451 to MV460, width 990000, even n in [769240002, 779140000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV451: every even n in [769240002, 770230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v451 : wem 769238190 769240002 770230000 &&& gm (wpm2 769238190 991810) (P10k.take 278) =
    wem 769238190 769240002 770230000 := by
  decide +kernel

/-- Window MV452: every even n in [770230002, 771220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v452 : wem 770228190 770230002 771220000 &&& gm (wpm2 770228190 991810) (P10k.take 278) =
    wem 770228190 770230002 771220000 := by
  decide +kernel

/-- Window MV453: every even n in [771220002, 772210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v453 : wem 771218190 771220002 772210000 &&& gm (wpm2 771218190 991810) (P10k.take 278) =
    wem 771218190 771220002 772210000 := by
  decide +kernel

/-- Window MV454: every even n in [772210002, 773200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v454 : wem 772208190 772210002 773200000 &&& gm (wpm2 772208190 991810) (P10k.take 278) =
    wem 772208190 772210002 773200000 := by
  decide +kernel

/-- Window MV455: every even n in [773200002, 774190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v455 : wem 773198190 773200002 774190000 &&& gm (wpm2 773198190 991810) (P10k.take 278) =
    wem 773198190 773200002 774190000 := by
  decide +kernel

/-- Window MV456: every even n in [774190002, 775180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v456 : wem 774188190 774190002 775180000 &&& gm (wpm2 774188190 991810) (P10k.take 278) =
    wem 774188190 774190002 775180000 := by
  decide +kernel

/-- Window MV457: every even n in [775180002, 776170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v457 : wem 775178190 775180002 776170000 &&& gm (wpm2 775178190 991810) (P10k.take 278) =
    wem 775178190 775180002 776170000 := by
  decide +kernel

/-- Window MV458: every even n in [776170002, 777160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v458 : wem 776168190 776170002 777160000 &&& gm (wpm2 776168190 991810) (P10k.take 278) =
    wem 776168190 776170002 777160000 := by
  decide +kernel

/-- Window MV459: every even n in [777160002, 778150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v459 : wem 777158190 777160002 778150000 &&& gm (wpm2 777158190 991810) (P10k.take 278) =
    wem 777158190 777160002 778150000 := by
  decide +kernel

/-- Window MV460: every even n in [778150002, 779140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v460 : wem 778148190 778150002 779140000 &&& gm (wpm2 778148190 991810) (P10k.take 278) =
    wem 778148190 778150002 779140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
