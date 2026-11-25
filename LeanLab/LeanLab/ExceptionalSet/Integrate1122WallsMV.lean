import LeanLab.ExceptionalSet.Integrate1122Walls4
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma2MVWalls

/-!
Burst burst-20261122, session S67, branch claude/ExceptionalSet-wire5mv, stacked on
claude/ExceptionalSet-wire4walls and claude/ExceptionalSet-rem66_lemma55.
Source P0082, J. Brüdern and A. Perelli, Ann. Inst. Fourier 48 (1998), Theorem 1 page 354, with
Lemma 2 page 357 taken apart along its source P0015, Montgomery and Vaughan 1975, sections 4 to 7.

`Integrate1122Walls4.theorem1_of_four_walls` keeps P0082 Lemma 2 as the wall `Lemma2NoExcBP`.
Here case i of Lemma 7, page 362, runs instead through the twin `Lemma2NoExcSmallDelta` of
`UpJ200/Lemma2MVSplit.lean`, which `Lemma2MVWalls.lemma2NoExcSmallDelta_of_walls` proves from two
printed displays of P0015: Lemma 5.5, display 5.4 page 360, `rem66_lemma55`, and Lemma 4.3,
pages 357 and 358, `mv_gallagher_lemma43`. No new definition, no sorry, no statement changed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Integrate1122WallsMV

open LeanLab.ExceptionalSet.BrudernPerelli1998 (Theorem1)

/-- P0082 page 362 case i, the exact type of `Decomp559b.leaf_absent_selected`, CONDITIONAL ON
P0015 Lemma 5.5 display 5.4 and P0015 Lemma 4.3 only. Display 11 is the proved
`Prep1121SingSeries.singularSeriesEvenLowerBP_split`. -/
theorem leaf_absent_selected_of_mv
    (hL55 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_lemma55)
    (hG43 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_gallagher_lemma43) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected :=
  LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.leaf_absent_selected_of_small
    (LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lemma2NoExcSmallDelta_of_walls hL55 hG43)
    LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.singularSeriesEvenLowerBP_split

/-- P0082 page 354 Theorem 1, CONDITIONAL ON five named inputs, each a printed result:
`KarLemma1` and `KarLemma2`, Karacuba 1971 pages 243 and 244; `rem66_lemma55`, P0015 Lemma 5.5
display 5.4; `mv_gallagher_lemma43`, P0015 Lemma 4.3; `BPLemma3Hyp`, P0082 Lemma 3. -/
theorem theorem1_of_mv_walls
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2)
    (hL55 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.rem66_lemma55)
    (hG43 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_gallagher_lemma43)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.BPLemma3Hyp) :
    Theorem1 :=
  LeanLab.ExceptionalSet.Integrate1122.theorem1_of_karacuba_and_leaves
    (LeanLab.ExceptionalSet.U1539.KaracubaSplit.karacubaThm1Named_of_vinogradov hK1 hK2)
    (leaf_absent_selected_of_mv hL55 hG43)
    (LeanLab.ExceptionalSet.UpJ200.CaseIIaFromLemma3.leaf_coprime_selected_of_lemma3 hL3)
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_prime_product_selected_wired
      (LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.prime_product_selected_of_lemma3 hL3))
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_near_zero_selected_wired
      (LeanLab.ExceptionalSet.UpJ200.CaseIIdFromLemma3.caseIIdMajorLowerHyp_of_lemma3 hL3))

end LeanLab.ExceptionalSet.Integrate1122WallsMV

#print axioms LeanLab.ExceptionalSet.Integrate1122WallsMV.leaf_absent_selected_of_mv
#print axioms LeanLab.ExceptionalSet.Integrate1122WallsMV.theorem1_of_mv_walls
