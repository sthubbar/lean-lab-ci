/-
Kernel Goldbach windows V421 to V430, width 990000, covering even n in [739540002, 749440000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V421: every even n in [739540002, 740530000] is p + q, q among the first 280 primes. -/
theorem window_v421 : wem 739538190 739540002 740530000 &&& gm (wpm2 739538190 991810) (P10k.take 280) =
    wem 739538190 739540002 740530000 := by
  decide +kernel

/-- Window V422: every even n in [740530002, 741520000] is p + q, q among the first 280 primes. -/
theorem window_v422 : wem 740528190 740530002 741520000 &&& gm (wpm2 740528190 991810) (P10k.take 280) =
    wem 740528190 740530002 741520000 := by
  decide +kernel

/-- Window V423: every even n in [741520002, 742510000] is p + q, q among the first 280 primes. -/
theorem window_v423 : wem 741518190 741520002 742510000 &&& gm (wpm2 741518190 991810) (P10k.take 280) =
    wem 741518190 741520002 742510000 := by
  decide +kernel

/-- Window V424: every even n in [742510002, 743500000] is p + q, q among the first 280 primes. -/
theorem window_v424 : wem 742508190 742510002 743500000 &&& gm (wpm2 742508190 991810) (P10k.take 280) =
    wem 742508190 742510002 743500000 := by
  decide +kernel

/-- Window V425: every even n in [743500002, 744490000] is p + q, q among the first 280 primes. -/
theorem window_v425 : wem 743498190 743500002 744490000 &&& gm (wpm2 743498190 991810) (P10k.take 280) =
    wem 743498190 743500002 744490000 := by
  decide +kernel

/-- Window V426: every even n in [744490002, 745480000] is p + q, q among the first 280 primes. -/
theorem window_v426 : wem 744488190 744490002 745480000 &&& gm (wpm2 744488190 991810) (P10k.take 280) =
    wem 744488190 744490002 745480000 := by
  decide +kernel

/-- Window V427: every even n in [745480002, 746470000] is p + q, q among the first 280 primes. -/
theorem window_v427 : wem 745478190 745480002 746470000 &&& gm (wpm2 745478190 991810) (P10k.take 280) =
    wem 745478190 745480002 746470000 := by
  decide +kernel

/-- Window V428: every even n in [746470002, 747460000] is p + q, q among the first 280 primes. -/
theorem window_v428 : wem 746468190 746470002 747460000 &&& gm (wpm2 746468190 991810) (P10k.take 280) =
    wem 746468190 746470002 747460000 := by
  decide +kernel

/-- Window V429: every even n in [747460002, 748450000] is p + q, q among the first 280 primes. -/
theorem window_v429 : wem 747458190 747460002 748450000 &&& gm (wpm2 747458190 991810) (P10k.take 280) =
    wem 747458190 747460002 748450000 := by
  decide +kernel

/-- Window V430: every even n in [748450002, 749440000] is p + q, q among the first 280 primes. -/
theorem window_v430 : wem 748448190 748450002 749440000 &&& gm (wpm2 748448190 991810) (P10k.take 280) =
    wem 748448190 748450002 749440000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
