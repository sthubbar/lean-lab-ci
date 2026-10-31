/-
Kernel Goldbach windows U301 to V310, width 990000, covering even n in [298000002, 307900000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U301: every even n in [298000002, 298990000] is p + q, q among the first 280 primes. -/
theorem window_u301 : wem 297998190 298000002 298990000 &&& gm (wpm2 297998190 991810) (P10k.take 280) =
    wem 297998190 298000002 298990000 := by
  decide +kernel

/-- Window U302: every even n in [298990002, 299980000] is p + q, q among the first 280 primes. -/
theorem window_u302 : wem 298988190 298990002 299980000 &&& gm (wpm2 298988190 991810) (P10k.take 280) =
    wem 298988190 298990002 299980000 := by
  decide +kernel

/-- Window U303: every even n in [299980002, 300970000] is p + q, q among the first 280 primes. -/
theorem window_u303 : wem 299978190 299980002 300970000 &&& gm (wpm2 299978190 991810) (P10k.take 280) =
    wem 299978190 299980002 300970000 := by
  decide +kernel

/-- Window U304: every even n in [300970002, 301960000] is p + q, q among the first 280 primes. -/
theorem window_u304 : wem 300968190 300970002 301960000 &&& gm (wpm2 300968190 991810) (P10k.take 280) =
    wem 300968190 300970002 301960000 := by
  decide +kernel

/-- Window U305: every even n in [301960002, 302950000] is p + q, q among the first 280 primes. -/
theorem window_u305 : wem 301958190 301960002 302950000 &&& gm (wpm2 301958190 991810) (P10k.take 280) =
    wem 301958190 301960002 302950000 := by
  decide +kernel

/-- Window U306: every even n in [302950002, 303940000] is p + q, q among the first 280 primes. -/
theorem window_u306 : wem 302948190 302950002 303940000 &&& gm (wpm2 302948190 991810) (P10k.take 280) =
    wem 302948190 302950002 303940000 := by
  decide +kernel

/-- Window U307: every even n in [303940002, 304930000] is p + q, q among the first 280 primes. -/
theorem window_u307 : wem 303938190 303940002 304930000 &&& gm (wpm2 303938190 991810) (P10k.take 280) =
    wem 303938190 303940002 304930000 := by
  decide +kernel

/-- Window U308: every even n in [304930002, 305920000] is p + q, q among the first 280 primes. -/
theorem window_u308 : wem 304928190 304930002 305920000 &&& gm (wpm2 304928190 991810) (P10k.take 280) =
    wem 304928190 304930002 305920000 := by
  decide +kernel

/-- Window U309: every even n in [305920002, 306910000] is p + q, q among the first 280 primes. -/
theorem window_u309 : wem 305918190 305920002 306910000 &&& gm (wpm2 305918190 991810) (P10k.take 280) =
    wem 305918190 305920002 306910000 := by
  decide +kernel

/-- Window U310: every even n in [306910002, 307900000] is p + q, q among the first 280 primes. -/
theorem window_u310 : wem 306908190 306910002 307900000 &&& gm (wpm2 306908190 991810) (P10k.take 280) =
    wem 306908190 306910002 307900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
