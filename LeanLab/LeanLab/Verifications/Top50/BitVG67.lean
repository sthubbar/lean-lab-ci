/-
Kernel Goldbach windows V661 to V670, width 990000, covering even n in [977140002, 987040000].
AI-written Lean code, Claude, 2026-10-17, run 20261017T2203Z-23036. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window V661: every even n in [977140002, 978130000] is p + q, q among the first 280 primes. -/
theorem window_v661 : wem 977138190 977140002 978130000 &&& gm (wpm2 977138190 991810) (P10k.take 280) =
    wem 977138190 977140002 978130000 := by
  decide +kernel

/-- Window V662: every even n in [978130002, 979120000] is p + q, q among the first 280 primes. -/
theorem window_v662 : wem 978128190 978130002 979120000 &&& gm (wpm2 978128190 991810) (P10k.take 280) =
    wem 978128190 978130002 979120000 := by
  decide +kernel

/-- Window V663: every even n in [979120002, 980110000] is p + q, q among the first 280 primes. -/
theorem window_v663 : wem 979118190 979120002 980110000 &&& gm (wpm2 979118190 991810) (P10k.take 280) =
    wem 979118190 979120002 980110000 := by
  decide +kernel

/-- Window V664: every even n in [980110002, 981100000] is p + q, q among the first 280 primes. -/
theorem window_v664 : wem 980108190 980110002 981100000 &&& gm (wpm2 980108190 991810) (P10k.take 280) =
    wem 980108190 980110002 981100000 := by
  decide +kernel

/-- Window V665: every even n in [981100002, 982090000] is p + q, q among the first 280 primes. -/
theorem window_v665 : wem 981098190 981100002 982090000 &&& gm (wpm2 981098190 991810) (P10k.take 280) =
    wem 981098190 981100002 982090000 := by
  decide +kernel

/-- Window V666: every even n in [982090002, 983080000] is p + q, q among the first 280 primes. -/
theorem window_v666 : wem 982088190 982090002 983080000 &&& gm (wpm2 982088190 991810) (P10k.take 280) =
    wem 982088190 982090002 983080000 := by
  decide +kernel

/-- Window V667: every even n in [983080002, 984070000] is p + q, q among the first 280 primes. -/
theorem window_v667 : wem 983078190 983080002 984070000 &&& gm (wpm2 983078190 991810) (P10k.take 280) =
    wem 983078190 983080002 984070000 := by
  decide +kernel

/-- Window V668: every even n in [984070002, 985060000] is p + q, q among the first 280 primes. -/
theorem window_v668 : wem 984068190 984070002 985060000 &&& gm (wpm2 984068190 991810) (P10k.take 280) =
    wem 984068190 984070002 985060000 := by
  decide +kernel

/-- Window V669: every even n in [985060002, 986050000] is p + q, q among the first 280 primes. -/
theorem window_v669 : wem 985058190 985060002 986050000 &&& gm (wpm2 985058190 991810) (P10k.take 280) =
    wem 985058190 985060002 986050000 := by
  decide +kernel

/-- Window V670: every even n in [986050002, 987040000] is p + q, q among the first 280 primes. -/
theorem window_v670 : wem 986048190 986050002 987040000 &&& gm (wpm2 986048190 991810) (P10k.take 280) =
    wem 986048190 986050002 987040000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
