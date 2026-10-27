/-
Kernel Goldbach windows MV151 to MV160, width 990000, even n in [472240002, 482140000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV151: every even n in [472240002, 473230000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v151 : wem 472238190 472240002 473230000 &&& gm (wpm2 472238190 991810) (P10k.take 278) =
    wem 472238190 472240002 473230000 := by
  decide +kernel

/-- Window MV152: every even n in [473230002, 474220000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v152 : wem 473228190 473230002 474220000 &&& gm (wpm2 473228190 991810) (P10k.take 278) =
    wem 473228190 473230002 474220000 := by
  decide +kernel

/-- Window MV153: every even n in [474220002, 475210000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v153 : wem 474218190 474220002 475210000 &&& gm (wpm2 474218190 991810) (P10k.take 278) =
    wem 474218190 474220002 475210000 := by
  decide +kernel

/-- Window MV154: every even n in [475210002, 476200000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v154 : wem 475208190 475210002 476200000 &&& gm (wpm2 475208190 991810) (P10k.take 278) =
    wem 475208190 475210002 476200000 := by
  decide +kernel

/-- Window MV155: every even n in [476200002, 477190000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v155 : wem 476198190 476200002 477190000 &&& gm (wpm2 476198190 991810) (P10k.take 278) =
    wem 476198190 476200002 477190000 := by
  decide +kernel

/-- Window MV156: every even n in [477190002, 478180000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v156 : wem 477188190 477190002 478180000 &&& gm (wpm2 477188190 991810) (P10k.take 278) =
    wem 477188190 477190002 478180000 := by
  decide +kernel

/-- Window MV157: every even n in [478180002, 479170000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v157 : wem 478178190 478180002 479170000 &&& gm (wpm2 478178190 991810) (P10k.take 278) =
    wem 478178190 478180002 479170000 := by
  decide +kernel

/-- Window MV158: every even n in [479170002, 480160000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v158 : wem 479168190 479170002 480160000 &&& gm (wpm2 479168190 991810) (P10k.take 278) =
    wem 479168190 479170002 480160000 := by
  decide +kernel

/-- Window MV159: every even n in [480160002, 481150000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v159 : wem 480158190 480160002 481150000 &&& gm (wpm2 480158190 991810) (P10k.take 278) =
    wem 480158190 480160002 481150000 := by
  decide +kernel

/-- Window MV160: every even n in [481150002, 482140000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v160 : wem 481148190 481150002 482140000 &&& gm (wpm2 481148190 991810) (P10k.take 278) =
    wem 481148190 481150002 482140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
