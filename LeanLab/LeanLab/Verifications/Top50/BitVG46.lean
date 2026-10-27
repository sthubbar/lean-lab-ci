/-
Kernel Goldbach windows V451 to V460, width 990000, covering even n in [769240002, 779140000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V451: every even n in [769240002, 770230000] is p + q, q among the first 280 primes. -/
theorem window_v451 : wem 769238190 769240002 770230000 &&& gm (wpm2 769238190 991810) (P10k.take 280) =
    wem 769238190 769240002 770230000 := by
  decide +kernel

/-- Window V452: every even n in [770230002, 771220000] is p + q, q among the first 280 primes. -/
theorem window_v452 : wem 770228190 770230002 771220000 &&& gm (wpm2 770228190 991810) (P10k.take 280) =
    wem 770228190 770230002 771220000 := by
  decide +kernel

/-- Window V453: every even n in [771220002, 772210000] is p + q, q among the first 280 primes. -/
theorem window_v453 : wem 771218190 771220002 772210000 &&& gm (wpm2 771218190 991810) (P10k.take 280) =
    wem 771218190 771220002 772210000 := by
  decide +kernel

/-- Window V454: every even n in [772210002, 773200000] is p + q, q among the first 280 primes. -/
theorem window_v454 : wem 772208190 772210002 773200000 &&& gm (wpm2 772208190 991810) (P10k.take 280) =
    wem 772208190 772210002 773200000 := by
  decide +kernel

/-- Window V455: every even n in [773200002, 774190000] is p + q, q among the first 280 primes. -/
theorem window_v455 : wem 773198190 773200002 774190000 &&& gm (wpm2 773198190 991810) (P10k.take 280) =
    wem 773198190 773200002 774190000 := by
  decide +kernel

/-- Window V456: every even n in [774190002, 775180000] is p + q, q among the first 280 primes. -/
theorem window_v456 : wem 774188190 774190002 775180000 &&& gm (wpm2 774188190 991810) (P10k.take 280) =
    wem 774188190 774190002 775180000 := by
  decide +kernel

/-- Window V457: every even n in [775180002, 776170000] is p + q, q among the first 280 primes. -/
theorem window_v457 : wem 775178190 775180002 776170000 &&& gm (wpm2 775178190 991810) (P10k.take 280) =
    wem 775178190 775180002 776170000 := by
  decide +kernel

/-- Window V458: every even n in [776170002, 777160000] is p + q, q among the first 280 primes. -/
theorem window_v458 : wem 776168190 776170002 777160000 &&& gm (wpm2 776168190 991810) (P10k.take 280) =
    wem 776168190 776170002 777160000 := by
  decide +kernel

/-- Window V459: every even n in [777160002, 778150000] is p + q, q among the first 280 primes. -/
theorem window_v459 : wem 777158190 777160002 778150000 &&& gm (wpm2 777158190 991810) (P10k.take 280) =
    wem 777158190 777160002 778150000 := by
  decide +kernel

/-- Window V460: every even n in [778150002, 779140000] is p + q, q among the first 280 primes. -/
theorem window_v460 : wem 778148190 778150002 779140000 &&& gm (wpm2 778148190 991810) (P10k.take 280) =
    wem 778148190 778150002 779140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
