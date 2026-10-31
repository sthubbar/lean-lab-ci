/-
Kernel Goldbach windows V571 to V580, width 990000, covering even n in [888040002, 897940000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V571: every even n in [888040002, 889030000] is p + q, q among the first 280 primes. -/
theorem window_v571 : wem 888038190 888040002 889030000 &&& gm (wpm2 888038190 991810) (P10k.take 280) =
    wem 888038190 888040002 889030000 := by
  decide +kernel

/-- Window V572: every even n in [889030002, 890020000] is p + q, q among the first 280 primes. -/
theorem window_v572 : wem 889028190 889030002 890020000 &&& gm (wpm2 889028190 991810) (P10k.take 280) =
    wem 889028190 889030002 890020000 := by
  decide +kernel

/-- Window V573: every even n in [890020002, 891010000] is p + q, q among the first 280 primes. -/
theorem window_v573 : wem 890018190 890020002 891010000 &&& gm (wpm2 890018190 991810) (P10k.take 280) =
    wem 890018190 890020002 891010000 := by
  decide +kernel

/-- Window V574: every even n in [891010002, 892000000] is p + q, q among the first 280 primes. -/
theorem window_v574 : wem 891008190 891010002 892000000 &&& gm (wpm2 891008190 991810) (P10k.take 280) =
    wem 891008190 891010002 892000000 := by
  decide +kernel

/-- Window V575: every even n in [892000002, 892990000] is p + q, q among the first 280 primes. -/
theorem window_v575 : wem 891998190 892000002 892990000 &&& gm (wpm2 891998190 991810) (P10k.take 280) =
    wem 891998190 892000002 892990000 := by
  decide +kernel

/-- Window V576: every even n in [892990002, 893980000] is p + q, q among the first 280 primes. -/
theorem window_v576 : wem 892988190 892990002 893980000 &&& gm (wpm2 892988190 991810) (P10k.take 280) =
    wem 892988190 892990002 893980000 := by
  decide +kernel

/-- Window V577: every even n in [893980002, 894970000] is p + q, q among the first 280 primes. -/
theorem window_v577 : wem 893978190 893980002 894970000 &&& gm (wpm2 893978190 991810) (P10k.take 280) =
    wem 893978190 893980002 894970000 := by
  decide +kernel

/-- Window V578: every even n in [894970002, 895960000] is p + q, q among the first 280 primes. -/
theorem window_v578 : wem 894968190 894970002 895960000 &&& gm (wpm2 894968190 991810) (P10k.take 280) =
    wem 894968190 894970002 895960000 := by
  decide +kernel

/-- Window V579: every even n in [895960002, 896950000] is p + q, q among the first 280 primes. -/
theorem window_v579 : wem 895958190 895960002 896950000 &&& gm (wpm2 895958190 991810) (P10k.take 280) =
    wem 895958190 895960002 896950000 := by
  decide +kernel

/-- Window V580: every even n in [896950002, 897940000] is p + q, q among the first 280 primes. -/
theorem window_v580 : wem 896948190 896950002 897940000 &&& gm (wpm2 896948190 991810) (P10k.take 280) =
    wem 896948190 896950002 897940000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
