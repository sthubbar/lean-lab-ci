/-
Kernel Goldbach windows U151 to V160, width 990000, covering even n in [149500002, 159400000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U151: every even n in [149500002, 150490000] is p + q, q among the first 280 primes. -/
theorem window_u151 : wem 149498190 149500002 150490000 &&& gm (wpm2 149498190 991810) (P10k.take 280) =
    wem 149498190 149500002 150490000 := by
  decide +kernel

/-- Window U152: every even n in [150490002, 151480000] is p + q, q among the first 280 primes. -/
theorem window_u152 : wem 150488190 150490002 151480000 &&& gm (wpm2 150488190 991810) (P10k.take 280) =
    wem 150488190 150490002 151480000 := by
  decide +kernel

/-- Window U153: every even n in [151480002, 152470000] is p + q, q among the first 280 primes. -/
theorem window_u153 : wem 151478190 151480002 152470000 &&& gm (wpm2 151478190 991810) (P10k.take 280) =
    wem 151478190 151480002 152470000 := by
  decide +kernel

/-- Window U154: every even n in [152470002, 153460000] is p + q, q among the first 280 primes. -/
theorem window_u154 : wem 152468190 152470002 153460000 &&& gm (wpm2 152468190 991810) (P10k.take 280) =
    wem 152468190 152470002 153460000 := by
  decide +kernel

/-- Window U155: every even n in [153460002, 154450000] is p + q, q among the first 280 primes. -/
theorem window_u155 : wem 153458190 153460002 154450000 &&& gm (wpm2 153458190 991810) (P10k.take 280) =
    wem 153458190 153460002 154450000 := by
  decide +kernel

/-- Window U156: every even n in [154450002, 155440000] is p + q, q among the first 280 primes. -/
theorem window_u156 : wem 154448190 154450002 155440000 &&& gm (wpm2 154448190 991810) (P10k.take 280) =
    wem 154448190 154450002 155440000 := by
  decide +kernel

/-- Window U157: every even n in [155440002, 156430000] is p + q, q among the first 280 primes. -/
theorem window_u157 : wem 155438190 155440002 156430000 &&& gm (wpm2 155438190 991810) (P10k.take 280) =
    wem 155438190 155440002 156430000 := by
  decide +kernel

/-- Window U158: every even n in [156430002, 157420000] is p + q, q among the first 280 primes. -/
theorem window_u158 : wem 156428190 156430002 157420000 &&& gm (wpm2 156428190 991810) (P10k.take 280) =
    wem 156428190 156430002 157420000 := by
  decide +kernel

/-- Window U159: every even n in [157420002, 158410000] is p + q, q among the first 280 primes. -/
theorem window_u159 : wem 157418190 157420002 158410000 &&& gm (wpm2 157418190 991810) (P10k.take 280) =
    wem 157418190 157420002 158410000 := by
  decide +kernel

/-- Window U160: every even n in [158410002, 159400000] is p + q, q among the first 280 primes. -/
theorem window_u160 : wem 158408190 158410002 159400000 &&& gm (wpm2 158408190 991810) (P10k.take 280) =
    wem 158408190 158410002 159400000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
