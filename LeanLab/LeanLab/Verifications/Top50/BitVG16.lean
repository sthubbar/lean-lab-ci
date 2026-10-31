/-
Kernel Goldbach windows V151 to V160, width 990000, covering even n in [472240002, 482140000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V151: every even n in [472240002, 473230000] is p + q, q among the first 280 primes. -/
theorem window_v151 : wem 472238190 472240002 473230000 &&& gm (wpm2 472238190 991810) (P10k.take 280) =
    wem 472238190 472240002 473230000 := by
  decide +kernel

/-- Window V152: every even n in [473230002, 474220000] is p + q, q among the first 280 primes. -/
theorem window_v152 : wem 473228190 473230002 474220000 &&& gm (wpm2 473228190 991810) (P10k.take 280) =
    wem 473228190 473230002 474220000 := by
  decide +kernel

/-- Window V153: every even n in [474220002, 475210000] is p + q, q among the first 280 primes. -/
theorem window_v153 : wem 474218190 474220002 475210000 &&& gm (wpm2 474218190 991810) (P10k.take 280) =
    wem 474218190 474220002 475210000 := by
  decide +kernel

/-- Window V154: every even n in [475210002, 476200000] is p + q, q among the first 280 primes. -/
theorem window_v154 : wem 475208190 475210002 476200000 &&& gm (wpm2 475208190 991810) (P10k.take 280) =
    wem 475208190 475210002 476200000 := by
  decide +kernel

/-- Window V155: every even n in [476200002, 477190000] is p + q, q among the first 280 primes. -/
theorem window_v155 : wem 476198190 476200002 477190000 &&& gm (wpm2 476198190 991810) (P10k.take 280) =
    wem 476198190 476200002 477190000 := by
  decide +kernel

/-- Window V156: every even n in [477190002, 478180000] is p + q, q among the first 280 primes. -/
theorem window_v156 : wem 477188190 477190002 478180000 &&& gm (wpm2 477188190 991810) (P10k.take 280) =
    wem 477188190 477190002 478180000 := by
  decide +kernel

/-- Window V157: every even n in [478180002, 479170000] is p + q, q among the first 280 primes. -/
theorem window_v157 : wem 478178190 478180002 479170000 &&& gm (wpm2 478178190 991810) (P10k.take 280) =
    wem 478178190 478180002 479170000 := by
  decide +kernel

/-- Window V158: every even n in [479170002, 480160000] is p + q, q among the first 280 primes. -/
theorem window_v158 : wem 479168190 479170002 480160000 &&& gm (wpm2 479168190 991810) (P10k.take 280) =
    wem 479168190 479170002 480160000 := by
  decide +kernel

/-- Window V159: every even n in [480160002, 481150000] is p + q, q among the first 280 primes. -/
theorem window_v159 : wem 480158190 480160002 481150000 &&& gm (wpm2 480158190 991810) (P10k.take 280) =
    wem 480158190 480160002 481150000 := by
  decide +kernel

/-- Window V160: every even n in [481150002, 482140000] is p + q, q among the first 280 primes. -/
theorem window_v160 : wem 481148190 481150002 482140000 &&& gm (wpm2 481148190 991810) (P10k.take 280) =
    wem 481148190 481150002 482140000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
