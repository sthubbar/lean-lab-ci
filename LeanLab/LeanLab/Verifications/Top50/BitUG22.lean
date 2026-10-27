/-
Kernel Goldbach windows U211 to V220, width 990000, covering even n in [208900002, 218800000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window U211: every even n in [208900002, 209890000] is p + q, q among the first 280 primes. -/
theorem window_u211 : wem 208898190 208900002 209890000 &&& gm (wpm2 208898190 991810) (P10k.take 280) =
    wem 208898190 208900002 209890000 := by
  decide +kernel

/-- Window U212: every even n in [209890002, 210880000] is p + q, q among the first 280 primes. -/
theorem window_u212 : wem 209888190 209890002 210880000 &&& gm (wpm2 209888190 991810) (P10k.take 280) =
    wem 209888190 209890002 210880000 := by
  decide +kernel

/-- Window U213: every even n in [210880002, 211870000] is p + q, q among the first 280 primes. -/
theorem window_u213 : wem 210878190 210880002 211870000 &&& gm (wpm2 210878190 991810) (P10k.take 280) =
    wem 210878190 210880002 211870000 := by
  decide +kernel

/-- Window U214: every even n in [211870002, 212860000] is p + q, q among the first 280 primes. -/
theorem window_u214 : wem 211868190 211870002 212860000 &&& gm (wpm2 211868190 991810) (P10k.take 280) =
    wem 211868190 211870002 212860000 := by
  decide +kernel

/-- Window U215: every even n in [212860002, 213850000] is p + q, q among the first 280 primes. -/
theorem window_u215 : wem 212858190 212860002 213850000 &&& gm (wpm2 212858190 991810) (P10k.take 280) =
    wem 212858190 212860002 213850000 := by
  decide +kernel

/-- Window U216: every even n in [213850002, 214840000] is p + q, q among the first 280 primes. -/
theorem window_u216 : wem 213848190 213850002 214840000 &&& gm (wpm2 213848190 991810) (P10k.take 280) =
    wem 213848190 213850002 214840000 := by
  decide +kernel

/-- Window U217: every even n in [214840002, 215830000] is p + q, q among the first 280 primes. -/
theorem window_u217 : wem 214838190 214840002 215830000 &&& gm (wpm2 214838190 991810) (P10k.take 280) =
    wem 214838190 214840002 215830000 := by
  decide +kernel

/-- Window U218: every even n in [215830002, 216820000] is p + q, q among the first 280 primes. -/
theorem window_u218 : wem 215828190 215830002 216820000 &&& gm (wpm2 215828190 991810) (P10k.take 280) =
    wem 215828190 215830002 216820000 := by
  decide +kernel

/-- Window U219: every even n in [216820002, 217810000] is p + q, q among the first 280 primes. -/
theorem window_u219 : wem 216818190 216820002 217810000 &&& gm (wpm2 216818190 991810) (P10k.take 280) =
    wem 216818190 216820002 217810000 := by
  decide +kernel

/-- Window U220: every even n in [217810002, 218800000] is p + q, q among the first 280 primes. -/
theorem window_u220 : wem 217808190 217810002 218800000 &&& gm (wpm2 217808190 991810) (P10k.take 280) =
    wem 217808190 217810002 218800000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
