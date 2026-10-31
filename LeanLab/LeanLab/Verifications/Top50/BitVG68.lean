/-
Kernel Goldbach windows V671 to V680, width 990000, covering even n in [987040002, 996940000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V671: every even n in [987040002, 988030000] is p + q, q among the first 280 primes. -/
theorem window_v671 : wem 987038190 987040002 988030000 &&& gm (wpm2 987038190 991810) (P10k.take 280) =
    wem 987038190 987040002 988030000 := by
  decide +kernel

/-- Window V672: every even n in [988030002, 989020000] is p + q, q among the first 280 primes. -/
theorem window_v672 : wem 988028190 988030002 989020000 &&& gm (wpm2 988028190 991810) (P10k.take 280) =
    wem 988028190 988030002 989020000 := by
  decide +kernel

/-- Window V673: every even n in [989020002, 990010000] is p + q, q among the first 280 primes. -/
theorem window_v673 : wem 989018190 989020002 990010000 &&& gm (wpm2 989018190 991810) (P10k.take 280) =
    wem 989018190 989020002 990010000 := by
  decide +kernel

/-- Window V674: every even n in [990010002, 991000000] is p + q, q among the first 280 primes. -/
theorem window_v674 : wem 990008190 990010002 991000000 &&& gm (wpm2 990008190 991810) (P10k.take 280) =
    wem 990008190 990010002 991000000 := by
  decide +kernel

/-- Window V675: every even n in [991000002, 991990000] is p + q, q among the first 280 primes. -/
theorem window_v675 : wem 990998190 991000002 991990000 &&& gm (wpm2 990998190 991810) (P10k.take 280) =
    wem 990998190 991000002 991990000 := by
  decide +kernel

/-- Window V676: every even n in [991990002, 992980000] is p + q, q among the first 280 primes. -/
theorem window_v676 : wem 991988190 991990002 992980000 &&& gm (wpm2 991988190 991810) (P10k.take 280) =
    wem 991988190 991990002 992980000 := by
  decide +kernel

/-- Window V677: every even n in [992980002, 993970000] is p + q, q among the first 280 primes. -/
theorem window_v677 : wem 992978190 992980002 993970000 &&& gm (wpm2 992978190 991810) (P10k.take 280) =
    wem 992978190 992980002 993970000 := by
  decide +kernel

/-- Window V678: every even n in [993970002, 994960000] is p + q, q among the first 280 primes. -/
theorem window_v678 : wem 993968190 993970002 994960000 &&& gm (wpm2 993968190 991810) (P10k.take 280) =
    wem 993968190 993970002 994960000 := by
  decide +kernel

/-- Window V679: every even n in [994960002, 995950000] is p + q, q among the first 280 primes. -/
theorem window_v679 : wem 994958190 994960002 995950000 &&& gm (wpm2 994958190 991810) (P10k.take 280) =
    wem 994958190 994960002 995950000 := by
  decide +kernel

/-- Window V680: every even n in [995950002, 996940000] is p + q, q among the first 280 primes. -/
theorem window_v680 : wem 995948190 995950002 996940000 &&& gm (wpm2 995948190 991810) (P10k.take 280) =
    wem 995948190 995950002 996940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
