/-
Kernel Goldbach windows V101 to V110, width 990000, covering even n in [422740002, 432640000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V101: every even n in [422740002, 423730000] is p + q, q among the first 280 primes. -/
theorem window_v101 : wem 422738190 422740002 423730000 &&& gm (wpm2 422738190 991810) (P10k.take 280) =
    wem 422738190 422740002 423730000 := by
  decide +kernel

/-- Window V102: every even n in [423730002, 424720000] is p + q, q among the first 280 primes. -/
theorem window_v102 : wem 423728190 423730002 424720000 &&& gm (wpm2 423728190 991810) (P10k.take 280) =
    wem 423728190 423730002 424720000 := by
  decide +kernel

/-- Window V103: every even n in [424720002, 425710000] is p + q, q among the first 280 primes. -/
theorem window_v103 : wem 424718190 424720002 425710000 &&& gm (wpm2 424718190 991810) (P10k.take 280) =
    wem 424718190 424720002 425710000 := by
  decide +kernel

/-- Window V104: every even n in [425710002, 426700000] is p + q, q among the first 280 primes. -/
theorem window_v104 : wem 425708190 425710002 426700000 &&& gm (wpm2 425708190 991810) (P10k.take 280) =
    wem 425708190 425710002 426700000 := by
  decide +kernel

/-- Window V105: every even n in [426700002, 427690000] is p + q, q among the first 280 primes. -/
theorem window_v105 : wem 426698190 426700002 427690000 &&& gm (wpm2 426698190 991810) (P10k.take 280) =
    wem 426698190 426700002 427690000 := by
  decide +kernel

/-- Window V106: every even n in [427690002, 428680000] is p + q, q among the first 280 primes. -/
theorem window_v106 : wem 427688190 427690002 428680000 &&& gm (wpm2 427688190 991810) (P10k.take 280) =
    wem 427688190 427690002 428680000 := by
  decide +kernel

/-- Window V107: every even n in [428680002, 429670000] is p + q, q among the first 280 primes. -/
theorem window_v107 : wem 428678190 428680002 429670000 &&& gm (wpm2 428678190 991810) (P10k.take 280) =
    wem 428678190 428680002 429670000 := by
  decide +kernel

/-- Window V108: every even n in [429670002, 430660000] is p + q, q among the first 280 primes. -/
theorem window_v108 : wem 429668190 429670002 430660000 &&& gm (wpm2 429668190 991810) (P10k.take 280) =
    wem 429668190 429670002 430660000 := by
  decide +kernel

/-- Window V109: every even n in [430660002, 431650000] is p + q, q among the first 280 primes. -/
theorem window_v109 : wem 430658190 430660002 431650000 &&& gm (wpm2 430658190 991810) (P10k.take 280) =
    wem 430658190 430660002 431650000 := by
  decide +kernel

/-- Window V110: every even n in [431650002, 432640000] is p + q, q among the first 280 primes. -/
theorem window_v110 : wem 431648190 431650002 432640000 &&& gm (wpm2 431648190 991810) (P10k.take 280) =
    wem 431648190 431650002 432640000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
