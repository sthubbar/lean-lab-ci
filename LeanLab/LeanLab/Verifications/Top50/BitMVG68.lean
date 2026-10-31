/-
Kernel Goldbach windows MV671 to MV680, width 990000, even n in [987040002, 996940000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MV671: every even n in [987040002, 988030000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v671 : wem 987038190 987040002 988030000 &&& gm (wpm2 987038190 991810) (P10k.take 278) =
    wem 987038190 987040002 988030000 := by
  decide +kernel

/-- Window MV672: every even n in [988030002, 989020000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v672 : wem 988028190 988030002 989020000 &&& gm (wpm2 988028190 991810) (P10k.take 278) =
    wem 988028190 988030002 989020000 := by
  decide +kernel

/-- Window MV673: every even n in [989020002, 990010000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v673 : wem 989018190 989020002 990010000 &&& gm (wpm2 989018190 991810) (P10k.take 278) =
    wem 989018190 989020002 990010000 := by
  decide +kernel

/-- Window MV674: every even n in [990010002, 991000000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v674 : wem 990008190 990010002 991000000 &&& gm (wpm2 990008190 991810) (P10k.take 278) =
    wem 990008190 990010002 991000000 := by
  decide +kernel

/-- Window MV675: every even n in [991000002, 991990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v675 : wem 990998190 991000002 991990000 &&& gm (wpm2 990998190 991810) (P10k.take 278) =
    wem 990998190 991000002 991990000 := by
  decide +kernel

/-- Window MV676: every even n in [991990002, 992980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v676 : wem 991988190 991990002 992980000 &&& gm (wpm2 991988190 991810) (P10k.take 278) =
    wem 991988190 991990002 992980000 := by
  decide +kernel

/-- Window MV677: every even n in [992980002, 993970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v677 : wem 992978190 992980002 993970000 &&& gm (wpm2 992978190 991810) (P10k.take 278) =
    wem 992978190 992980002 993970000 := by
  decide +kernel

/-- Window MV678: every even n in [993970002, 994960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v678 : wem 993968190 993970002 994960000 &&& gm (wpm2 993968190 991810) (P10k.take 278) =
    wem 993968190 993970002 994960000 := by
  decide +kernel

/-- Window MV679: every even n in [994960002, 995950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v679 : wem 994958190 994960002 995950000 &&& gm (wpm2 994958190 991810) (P10k.take 278) =
    wem 994958190 994960002 995950000 := by
  decide +kernel

/-- Window MV680: every even n in [995950002, 996940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_v680 : wem 995948190 995950002 996940000 &&& gm (wpm2 995948190 991810) (P10k.take 278) =
    wem 995948190 995950002 996940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
