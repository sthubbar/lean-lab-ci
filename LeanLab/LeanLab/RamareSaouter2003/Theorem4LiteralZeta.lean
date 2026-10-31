import Mathlib
import LeanLab.RamareSaouter2003.Theorem4Literal
import LeanLab.RamareSaouter2003.Lemma3Zeta

/-!
# Ramaré-Saouter 2003, Theorem 4 on the literal (15) with the true zero sum of ζ

P0099, unit U-1346, run 20261021T0203Z-29730. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Fixes the U-1333 vacuity note: with abstract `Zs`, `Zs = 0` satisfies `Lemma3Bound`. Here `Zs`
is `ZsF gZ bZ`, the sum over the nontrivial zeros of ζ with multiplicity, and `Lemma3Bound`
is discharged by `L3Zeta.lemma3_zeta` from `RHUpTo T0` and `Lemma1Count gZ`.
-/

namespace LeanLab.RamareSaouter2003.Thm4LiteralZeta

open LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.Thm4Parts
  LeanLab.RamareSaouter2003.Thm4Literal LeanLab.RamareSaouter2003.L3Zeta
  LeanLab.RamareSaouter2003.L3Zeros

/-- **Theorem 4 for `f_m`**, literal (15) with the true zero sum. PROVED CONDITIONAL ON
`MVBrunTitchmarsh`, `SchoenfeldPT 0.998697 1.001093`, `JLower15Lit NT (ZsF gZ bZ) T0`,
`RHUpTo T0` and `Lemma1Count gZ`. -/
theorem theorem4Fm_of_zeta_lit (hMV : MVBrunTitchmarsh) (hS : SchoenfeldPT 0.998697 1.001093)
    {NT : ℝ → ℝ} {T0 : ℝ} (h15 : JLower15Lit NT (ZsF gZ bZ) T0) (hRH : RHUpTo T0)
    (hN : Lemma1Count gZ) : Theorem4Fm NT T0 :=
  theorem4Fm_of_split_lit hMV hS h15 (lemma3_zeta hRH hN)

/-- **Table 1 row one**, literal (15) with the true zero sum. PROVED CONDITIONAL ON
`MVBrunTitchmarsh`, `SchoenfeldPT`, `JLower15Lit NT (ZsF gZ bZ) 3.3e9`, `RHUpTo 3.3e9`,
`Lemma1Count gZ` and `Lemma1Upper NT`. -/
theorem theorem2At1e20_of_zeta_lit (hMV : MVBrunTitchmarsh)
    (hS : SchoenfeldPT 0.998697 1.001093) {NT : ℝ → ℝ}
    (h15 : JLower15Lit NT (ZsF gZ bZ) 3300000000) (hRH : RHUpTo 3300000000)
    (hN : Lemma1Count gZ) (hU : Row1.Lemma1Upper NT) : Theorem2At1e20 :=
  theorem2At1e20_of_split_lit hMV hS h15 (lemma3_zeta hRH hN) hU

end LeanLab.RamareSaouter2003.Thm4LiteralZeta

#print axioms LeanLab.RamareSaouter2003.Thm4LiteralZeta.theorem4Fm_of_zeta_lit
#print axioms LeanLab.RamareSaouter2003.Thm4LiteralZeta.theorem2At1e20_of_zeta_lit
