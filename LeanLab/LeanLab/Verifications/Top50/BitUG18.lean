/-
Kernel Goldbach windows U171 to V180, width 990000, covering even n in [169300002, 179200000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U171: every even n in [169300002, 170290000] is p + q, q among the first 280 primes. -/
theorem window_u171 : wem 169298190 169300002 170290000 &&& gm (wpm2 169298190 991810) (P10k.take 280) =
    wem 169298190 169300002 170290000 := by
  decide +kernel

/-- Window U172: every even n in [170290002, 171280000] is p + q, q among the first 280 primes. -/
theorem window_u172 : wem 170288190 170290002 171280000 &&& gm (wpm2 170288190 991810) (P10k.take 280) =
    wem 170288190 170290002 171280000 := by
  decide +kernel

/-- Window U173: every even n in [171280002, 172270000] is p + q, q among the first 280 primes. -/
theorem window_u173 : wem 171278190 171280002 172270000 &&& gm (wpm2 171278190 991810) (P10k.take 280) =
    wem 171278190 171280002 172270000 := by
  decide +kernel

/-- Window U174: every even n in [172270002, 173260000] is p + q, q among the first 280 primes. -/
theorem window_u174 : wem 172268190 172270002 173260000 &&& gm (wpm2 172268190 991810) (P10k.take 280) =
    wem 172268190 172270002 173260000 := by
  decide +kernel

/-- Window U175: every even n in [173260002, 174250000] is p + q, q among the first 280 primes. -/
theorem window_u175 : wem 173258190 173260002 174250000 &&& gm (wpm2 173258190 991810) (P10k.take 280) =
    wem 173258190 173260002 174250000 := by
  decide +kernel

/-- Window U176: every even n in [174250002, 175240000] is p + q, q among the first 280 primes. -/
theorem window_u176 : wem 174248190 174250002 175240000 &&& gm (wpm2 174248190 991810) (P10k.take 280) =
    wem 174248190 174250002 175240000 := by
  decide +kernel

/-- Window U177: every even n in [175240002, 176230000] is p + q, q among the first 280 primes. -/
theorem window_u177 : wem 175238190 175240002 176230000 &&& gm (wpm2 175238190 991810) (P10k.take 280) =
    wem 175238190 175240002 176230000 := by
  decide +kernel

/-- Window U178: every even n in [176230002, 177220000] is p + q, q among the first 280 primes. -/
theorem window_u178 : wem 176228190 176230002 177220000 &&& gm (wpm2 176228190 991810) (P10k.take 280) =
    wem 176228190 176230002 177220000 := by
  decide +kernel

/-- Window U179: every even n in [177220002, 178210000] is p + q, q among the first 280 primes. -/
theorem window_u179 : wem 177218190 177220002 178210000 &&& gm (wpm2 177218190 991810) (P10k.take 280) =
    wem 177218190 177220002 178210000 := by
  decide +kernel

/-- Window U180: every even n in [178210002, 179200000] is p + q, q among the first 280 primes. -/
theorem window_u180 : wem 178208190 178210002 179200000 &&& gm (wpm2 178208190 991810) (P10k.take 280) =
    wem 178208190 178210002 179200000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
