import LeanLab.ExceptionalSet.Prep1121SingSeries
import LeanLab.ExceptionalSet.RealZeroLower672

/-!
Burst 2026-11-22 session S29, unit P1122-0122, wiring only.

P0082, Brüdern and Perelli, Ann. Inst. Fourier 48 (1998), page 363 case ii a uses two
inputs beyond the paper's own Lemma 3: the singular series lower bound of display 11, proved
in `Prep1121SingSeries.singSeriesLowerHyp_split`, and the left inequality of page 358
display 10, `1 - β ≫ r^{-1/2} (log r)^{-2}`, Davenport chapter 14, which is the named
`DQLeafCoprimeSelected.LandauRealZeroHyp`. Display 10 is proved on main by
`Task672.landauRealZeroHyp_proved672` from the lab Siegel theorem, with an ineffective
constant, which is all the paper needs there.

This file only plugs that proof into `Prep1121SingSeries.leaf_coprime_selected_of_two_hyps`,
so the coprime selected leaf of `Decomp559b` is CONDITIONAL ON the cited `BPLemma3CoprimeHyp`
alone. No new statement, no sorry, no axiom. AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Wire1122CoprimeLemma3Only

/-- P0082 page 363 case ii a, the exact type of `Decomp559b.leaf_coprime_selected`,
CONDITIONAL ON the cited `BPLemma3CoprimeHyp` only, P0082 page 358 Lemma 3. Display 10 is
discharged by `Task672.landauRealZeroHyp_proved672`. -/
theorem leaf_coprime_selected_of_lemma3_only
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected :=
  LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.leaf_coprime_selected_of_two_hyps hL3
    LeanLab.ExceptionalSet.Task672.landauRealZeroHyp_proved672

#print axioms leaf_coprime_selected_of_lemma3_only
#print axioms LeanLab.ExceptionalSet.Task672.landauRealZeroHyp_proved672

end LeanLab.ExceptionalSet.UpJ200.Wire1122CoprimeLemma3Only
