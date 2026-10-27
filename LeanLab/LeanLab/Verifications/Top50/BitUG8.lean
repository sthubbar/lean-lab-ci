/-
Kernel Goldbach windows U71 to V80, width 990000, covering even n in [70300002, 80200000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U71: every even n in [70300002, 71290000] is p + q, q among the first 280 primes. -/
theorem window_u71 : wem 70298190 70300002 71290000 &&& gm (wpm2 70298190 991810) (P10k.take 280) =
    wem 70298190 70300002 71290000 := by
  decide +kernel

/-- Window U72: every even n in [71290002, 72280000] is p + q, q among the first 280 primes. -/
theorem window_u72 : wem 71288190 71290002 72280000 &&& gm (wpm2 71288190 991810) (P10k.take 280) =
    wem 71288190 71290002 72280000 := by
  decide +kernel

/-- Window U73: every even n in [72280002, 73270000] is p + q, q among the first 280 primes. -/
theorem window_u73 : wem 72278190 72280002 73270000 &&& gm (wpm2 72278190 991810) (P10k.take 280) =
    wem 72278190 72280002 73270000 := by
  decide +kernel

/-- Window U74: every even n in [73270002, 74260000] is p + q, q among the first 280 primes. -/
theorem window_u74 : wem 73268190 73270002 74260000 &&& gm (wpm2 73268190 991810) (P10k.take 280) =
    wem 73268190 73270002 74260000 := by
  decide +kernel

/-- Window U75: every even n in [74260002, 75250000] is p + q, q among the first 280 primes. -/
theorem window_u75 : wem 74258190 74260002 75250000 &&& gm (wpm2 74258190 991810) (P10k.take 280) =
    wem 74258190 74260002 75250000 := by
  decide +kernel

/-- Window U76: every even n in [75250002, 76240000] is p + q, q among the first 280 primes. -/
theorem window_u76 : wem 75248190 75250002 76240000 &&& gm (wpm2 75248190 991810) (P10k.take 280) =
    wem 75248190 75250002 76240000 := by
  decide +kernel

/-- Window U77: every even n in [76240002, 77230000] is p + q, q among the first 280 primes. -/
theorem window_u77 : wem 76238190 76240002 77230000 &&& gm (wpm2 76238190 991810) (P10k.take 280) =
    wem 76238190 76240002 77230000 := by
  decide +kernel

/-- Window U78: every even n in [77230002, 78220000] is p + q, q among the first 280 primes. -/
theorem window_u78 : wem 77228190 77230002 78220000 &&& gm (wpm2 77228190 991810) (P10k.take 280) =
    wem 77228190 77230002 78220000 := by
  decide +kernel

/-- Window U79: every even n in [78220002, 79210000] is p + q, q among the first 280 primes. -/
theorem window_u79 : wem 78218190 78220002 79210000 &&& gm (wpm2 78218190 991810) (P10k.take 280) =
    wem 78218190 78220002 79210000 := by
  decide +kernel

/-- Window U80: every even n in [79210002, 80200000] is p + q, q among the first 280 primes. -/
theorem window_u80 : wem 79208190 79210002 80200000 &&& gm (wpm2 79208190 991810) (P10k.take 280) =
    wem 79208190 79210002 80200000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
