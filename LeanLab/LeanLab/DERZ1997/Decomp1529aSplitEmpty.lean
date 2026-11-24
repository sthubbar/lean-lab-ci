/-
Burst 20261122, session S88. SPLIT of `zetaZeros_eq_empty` in Decomp1529a.
P0011, Deshouillers, Effinger, te Riele, Zinoviev 1997, GRH input: no non-trivial zero
of zeta below height 14. The proved glue uses the helpers of Decomp1529a for heights
through four and for the critical line through fourteen, and the functional equation
reflection rho to 1 - rho to move an off-line zero to the right half of the strip.
One LEAF remains: the right half strip band, a certified numerical verification.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.DERZ1997.Decomp1529a

namespace LeanLab.DERZ1997.Decomp1529aSplitEmpty
open Complex LeanLab.DERZ1997.Decomp1529a

/-- LEAF: Rosser 1941 Ann. of Math. 42 Theorem 19 and its table of zeros, Davenport
Multiplicative Number Theory chapter 15, as used on P0011 page 101: zeta has no zero
with `1/2 < Re ρ < 1` and `4 < |Im ρ| < 14`. Any certified argument principle count of
zeros in the rectangle `[1/2, 1] x [4, 14]`, or the RH verifications of Backlund 1914 and
later Platt and Trudgian 2021, suffices. Class HARD. -/
theorem zeta_right_band_ne_zero {ρ : ℂ} (hre : 1/2 < ρ.re) (hre1 : ρ.re < 1)
    (hlo : 4 < |ρ.im|) (hhi : |ρ.im| < 14) : riemannZeta ρ ≠ 0 := by
  sorry

/-- The parent `zetaZeros_eq_empty`, proved from the single LEAF and the proved helpers.
CONDITIONAL ON the LEAF `zeta_right_band_ne_zero`. -/
theorem zetaZeros_eq_empty_of_leaves {T : ℝ} (hT : T < 14) : zetaZeros T = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  obtain ⟨hz, h0, h1, hT'⟩ := hρ
  by_cases hlow : |ρ.im| ≤ 4
  · have hzfour : ρ ∈ zetaZeros 4 := ⟨hz, h0, h1, hlow⟩
    rw [zetaZeros_four_eq_empty193] at hzfour
    exact hzfour
  · have hlo : 4 < |ρ.im| := lt_of_not_ge hlow
    have hhi : |ρ.im| < 14 := lt_of_le_of_lt hT' hT
    rcases lt_trichotomy ρ.re (1/2) with hlt | heq | hgt
    · have hz' : riemannZeta (1 - ρ) = 0 :=
        LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero h0 h1 hz
      have hre : (1 - ρ).re = 1 - ρ.re := by simp
      have him : (1 - ρ).im = -ρ.im := by simp
      refine zeta_right_band_ne_zero (ρ := 1 - ρ) ?_ ?_ ?_ ?_ hz'
      · rw [hre]; linarith
      · rw [hre]; linarith
      · rw [him, abs_neg]; exact hlo
      · rw [him, abs_neg]; exact hhi
    · exact zeta_critical_height_fourteen193 heq hhi.le hz
    · exact zeta_right_band_ne_zero hgt h1 hlo hhi hz

end LeanLab.DERZ1997.Decomp1529aSplitEmpty
