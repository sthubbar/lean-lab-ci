import Mathlib
import LeanLab.HelfgottMajor.PVOddTrunc1122
import LeanLab.HelfgottMajor.PVOddSmall1122

/-!
Route burst S68, burst-20261122, tag pv-odd-wire.
Wiring of the odd case of Pomerance 2011 Theorem 1, Frolenkov arXiv 1107.0381 displays 12 to 22.
`PVCases1122` cannot be edited, so its proof of `pomerance_odd_case` is repeated here with the
LEAF `odd_truncated` replaced by its S68 assembly `PVOddTrunc1122.odd_truncated`, which rests only
on the HARD LEAF `PVOddTrunc1122.odd_truncated_large` for q above 1000, and the LEAF `odd_small`
replaced by its PROVED twin `PVOddSmall1122.odd_small`. No new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddWire1122

open Real Finset

/-- Assembly: exactly `PV420Split1122.pomerance_odd_case`, P0014 page 36 display 4.20 odd case,
from `PVCases1122.odd_from_truncated`, the S68 assembly of `odd_truncated` for q at least 7, and
the PROVED `odd_small` below 7. Rests only on `PVOddTrunc1122.odd_truncated_large`. -/
theorem pomerance_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) - ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q :=
  if h7 : 7 ≤ q then
    LeanLab.HelfgottMajor.PVCases1122.odd_from_truncated χ hS4
      (LeanLab.HelfgottMajor.PVOddTrunc1122.odd_truncated χ hχ h7 hodd) M N
  else LeanLab.HelfgottMajor.PVOddSmall1122.odd_small χ hχ hq (by omega) hodd M N

example : type_of% @pomerance_odd_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_odd_case := rfl

end LeanLab.HelfgottMajor.PVOddWire1122

#print axioms LeanLab.HelfgottMajor.PVOddWire1122.pomerance_odd_case
