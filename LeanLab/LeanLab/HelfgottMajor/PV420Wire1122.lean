import Mathlib
import LeanLab.HelfgottMajor.PVLemmasWire1122
import LeanLab.HelfgottMajor.PVEvenWire1122
import LeanLab.HelfgottMajor.PVOddChainWire1122

/-!
Route burst S68, burst-20261122, tag pv420-wire.
P0014 page 36 display 4.20, the Polya Vinogradov bound of Pomerance 2011 Theorem 1, assembled
from the S68 wired pieces: Lemma 3 and Section 4 PROVED in `PVLemmasWire1122`, the even case in
`PVEvenWire1122` and the odd case in `PVOddChainWire1122`. The proof is that of
`PV420Split1122.polya_vinogradov_4_20` with these pieces. It rests only on the two HARD LEAFs
`PVEvenTrunc1122.cot_tail` and `PVOddTrunc1122.odd_truncated_large`, the truncation error of
Pomerance's Polya expansion, even case and odd case for q above 1000. No new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PV420Wire1122

open Real Finset

/-- P0014 page 36 display 4.20, exactly the sealed `PolyaVinogradov123.polya_vinogradov_4_20`,
resting only on `PVEvenTrunc1122.cot_tail` and `PVOddTrunc1122.odd_truncated_large`. -/
theorem polya_vinogradov_4_20 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  refine ciSup_le fun n => ?_
  split_ifs with h
  · exact LeanLab.HelfgottMajor.PVEvenWire1122.pomerance_even_case χ hχ hq
      LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_lemma3
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h 1 n
  · exact LeanLab.HelfgottMajor.PVOddChainWire1122.pomerance_odd_case χ hχ hq
      LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_sec4
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_odd hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h 1 n

example : type_of% @polya_vinogradov_4_20 =
    type_of% @LeanLab.HelfgottMajor.PolyaVinogradov123.polya_vinogradov_4_20 := rfl

end LeanLab.HelfgottMajor.PV420Wire1122

#print axioms LeanLab.HelfgottMajor.PV420Wire1122.polya_vinogradov_4_20
