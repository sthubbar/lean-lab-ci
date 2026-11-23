import LeanLab.ExceptionalSet.Integrate1122WallsMV
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Termwise
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55KSum
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Pi12

/-!
# Wiring: P0015 Lemma 5.5 proved, P0082 Theorem 1 on four named inputs

Burst burst-20261122, Claude cloud session S74, branch claude/ExceptionalSet-wire_lemma55,
stacked on claude/ExceptionalSet-lem55_termwise, -lem55_ksum and -lem55_pi12.

P0015, Montgomery and Vaughan 1975, Lemma 5.5, display 5.4 page 360, the leaf `rem66_lemma55`,
is now PROVED from the four steps of its proof on pages 360 and 361, each proved:
`lem55_termwise_split`, `Lemma2MVKSum.lem55_ksum_proved`, `lem55_pi12_proof` and
`lem55_prod_combine`, through the existing assembly `lemma55_of_leaves`.

Hence `Integrate1122WallsMV.theorem1_of_mv_walls` loses its input `rem66_lemma55`: P0082
Theorem 1 page 354 is PROVED CONDITIONAL ON four printed results, `KarLemma1`, `KarLemma2`,
P0015 Lemma 4.3 `mv_gallagher_lemma43` and P0082 Lemma 3 `BPLemma3Hyp`. Compared with
`Integrate1122Walls4.theorem1_of_four_walls`, P0082 Lemma 2 is replaced by the single
Gallagher input of Montgomery and Vaughan.

No new definition, no sorry, no statement changed. AI wrote the Lean code. Binary Goldbach is
open.
-/

namespace LeanLab.ExceptionalSet.Wire1122Lemma55

open LeanLab.ExceptionalSet.BrudernPerelli1998 (Theorem1)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (rem66_lemma55 lemma55_of_leaves
  lem55_termwise_split lem55_pi12_proof lem55_prod_combine)

/-- P0015 Lemma 5.5, display 5.4 page 360, the exact type of the leaf `rem66_lemma55`, PROVED
from the four proved steps of its proof on pages 360 and 361. -/
theorem rem66_lemma55_proved : type_of% @rem66_lemma55 :=
  lemma55_of_leaves lem55_termwise_split
    LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum.lem55_ksum_proved
    lem55_pi12_proof lem55_prod_combine

/-- P0082 Lemma 2 for small `δ`, `Lemma2NoExcSmallDelta`, CONDITIONAL ON P0015 Lemma 4.3 alone. -/
theorem lemma2NoExcSmallDelta_of_lemma43
    (hG43 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_gallagher_lemma43) :
    LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.Lemma2NoExcSmallDelta :=
  LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lemma2NoExcSmallDelta_of_walls
    rem66_lemma55_proved hG43

/-- P0082 page 354 Theorem 1, CONDITIONAL ON four named printed inputs: `KarLemma1` and
`KarLemma2`, Karacuba 1971 pages 243 and 244; `mv_gallagher_lemma43`, P0015 Lemma 4.3 pages
357 and 358, Gallagher's Theorem 7; `BPLemma3Hyp`, P0082 Lemma 3 page 358. -/
theorem theorem1_of_four_inputs
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2)
    (hG43 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_gallagher_lemma43)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.BPLemma3Hyp) :
    Theorem1 :=
  LeanLab.ExceptionalSet.Integrate1122WallsMV.theorem1_of_mv_walls hK1 hK2
    rem66_lemma55_proved hG43 hL3

end LeanLab.ExceptionalSet.Wire1122Lemma55

#print axioms LeanLab.ExceptionalSet.Wire1122Lemma55.rem66_lemma55_proved
#print axioms LeanLab.ExceptionalSet.Wire1122Lemma55.lemma2NoExcSmallDelta_of_lemma43
#print axioms LeanLab.ExceptionalSet.Wire1122Lemma55.theorem1_of_four_inputs
