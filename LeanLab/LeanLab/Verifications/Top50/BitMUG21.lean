/-
Kernel Goldbach windows MU201 to MU210, width 990000, even n in [199000002, 208900000], q ≤ 1789.
AI-written Lean code, Claude, 2026-10-18, run 20261018T0304Z-29941. Binary Goldbach is OPEN.
-/
import LeanLab.Verifications.Top50.BitSieve2

set_option Elab.async false

namespace LeanLab.Verifications.Top50.Bits

/-- Window MU201: every even n in [199000002, 199990000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u201 : wem 198998190 199000002 199990000 &&& gm (wpm2 198998190 991810) (P10k.take 278) =
    wem 198998190 199000002 199990000 := by
  decide +kernel

/-- Window MU202: every even n in [199990002, 200980000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u202 : wem 199988190 199990002 200980000 &&& gm (wpm2 199988190 991810) (P10k.take 278) =
    wem 199988190 199990002 200980000 := by
  decide +kernel

/-- Window MU203: every even n in [200980002, 201970000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u203 : wem 200978190 200980002 201970000 &&& gm (wpm2 200978190 991810) (P10k.take 278) =
    wem 200978190 200980002 201970000 := by
  decide +kernel

/-- Window MU204: every even n in [201970002, 202960000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u204 : wem 201968190 201970002 202960000 &&& gm (wpm2 201968190 991810) (P10k.take 278) =
    wem 201968190 201970002 202960000 := by
  decide +kernel

/-- Window MU205: every even n in [202960002, 203950000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u205 : wem 202958190 202960002 203950000 &&& gm (wpm2 202958190 991810) (P10k.take 278) =
    wem 202958190 202960002 203950000 := by
  decide +kernel

/-- Window MU206: every even n in [203950002, 204940000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u206 : wem 203948190 203950002 204940000 &&& gm (wpm2 203948190 991810) (P10k.take 278) =
    wem 203948190 203950002 204940000 := by
  decide +kernel

/-- Window MU207: every even n in [204940002, 205930000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u207 : wem 204938190 204940002 205930000 &&& gm (wpm2 204938190 991810) (P10k.take 278) =
    wem 204938190 204940002 205930000 := by
  decide +kernel

/-- Window MU208: every even n in [205930002, 206920000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u208 : wem 205928190 205930002 206920000 &&& gm (wpm2 205928190 991810) (P10k.take 278) =
    wem 205928190 205930002 206920000 := by
  decide +kernel

/-- Window MU209: every even n in [206920002, 207910000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u209 : wem 206918190 206920002 207910000 &&& gm (wpm2 206918190 991810) (P10k.take 278) =
    wem 206918190 206920002 207910000 := by
  decide +kernel

/-- Window MU210: every even n in [207910002, 208900000] is p + q, q among the first 278 primes, q ≤ 1789. -/
theorem mwindow_u210 : wem 207908190 207910002 208900000 &&& gm (wpm2 207908190 991810) (P10k.take 278) =
    wem 207908190 207910002 208900000 := by
  decide +kernel

end LeanLab.Verifications.Top50.Bits
