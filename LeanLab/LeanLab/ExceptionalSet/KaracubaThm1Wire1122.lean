/-
Wiring audit for `KaracubaThm1Named` of DQLemma10Decisions, burst-20261122 unit P1122-0112.

`KaracubaThm1Named` is Theorem 1 of A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971)
241-255, chapter I section 2, p. 244, lab copy `papers/Karacuba1971-TrudyMIAN112.pdf`.
By `karacubaThm1Named_iff` it is `KaracubaSplit.KaracubaTheorem1` by `Iff.rfl`.

KaracubaSplit assembles Theorem 1 from its two cases, p. 245 `n ≥ n0` and p. 248
`2 ≤ n < n0`, but it feeds that assembly with its own shallow leaves `leaf_W_bound` and
`leaf_small_case`. Both have since been split, in SPLIT_leaf_W_bound and SPLIT_leaf_small_case,
and nothing joined the W split back to the named hypothesis. This file does that join.

`karacubaThm1Named_of_lemmas` takes Karacuba's two cited inputs, Lemma 1 p. 243, Vinogradov's
mean value theorem, and Lemma 2 p. 243-244, Vinogradov's Weyl sum estimate, as hypotheses.
Lemma 3 is PROVED in Decomp538a and Lemma 4 is PROVED in KaracubaSplit. The admitted steps that
remain under it, through the imported split files, are exactly:
* `leaf_karW_taylor_sum_bound` of SPLIT_leaf_W_bound, the analytic core of p. 245-248;
* `leaf_small_case` of KaracubaSplit, the case `2 ≤ n < n0`, p. 248.
The small case is NOT taken through `leaf_small_case_split`: that split rests on
`leaf_small_block_sum_bound`, which burst-20261122 S24 found FALSE as stated, kernel checked in
`Refute_leaf_polynomial_block_sum` on branch claude/ExceptionalSet-polynomial_block_sum: a block
far shorter than `P^{c2}` has no saving. The shallow `leaf_small_case` is not affected.
So `#print axioms` shows `sorryAx` here: this is a CONDITIONAL wiring, not a proof.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.DQLemma10Decisions
import LeanLab.ExceptionalSet.SPLIT_leaf_W_bound
import LeanLab.ExceptionalSet.SPLIT_leaf_small_case
import LeanLab.ExceptionalSet.SPLIT_leaf_karLemma1_mvt

namespace LeanLab.ExceptionalSet.U1539.KaracubaThm1Wire1122

open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.U1539.KaracubaSplit
open LeanLab.ExceptionalSet.U1539.DQLemma10

/-- Karacuba's Theorem 1, p. 244, from his cited Lemmas 1 and 2, p. 243-244, through the
split assembly `leaf_W_bound_split` and the shallow leaf `leaf_small_case`, with Lemma 3 from
`leaf_karLemma3` and Lemma 4 from `karLemma4`. CONDITIONAL on the open leaves named in the
module doc, which enter through the imports. -/
theorem karacubaThm1Named_of_lemmas (h1 : KarLemma1) (h2 : KarLemma2) :
    KaracubaThm1Named :=
  karacubaThm1Named_iff.mpr <|
    karacubaTheorem1_of_cases
      (fun c0 c1 c2 c3 c4 h0 h1' h2' h3 h4 h01 h11 h241 =>
        largeCase_of_W h11
          (leaf_W_bound_split h1 leaf_karLemma3 karLemma4 c0 c1 c2 c3 c4
            h0 h1' h2' h3 h4 h01 h11 h241))
      (leaf_small_case h2)

/-- The same with Lemma 1 from its split `leaf_karLemma1_mvt_split`, so only Lemma 2 is left
as a hypothesis; Lemma 1 then rests on the open leaf `leaf_mvt_threshold` of
SPLIT_leaf_karLemma1_mvt, split further in SPLIT_leaf_mvt_threshold down to
`leaf_solution_count_deep`. CONDITIONAL. -/
theorem karacubaThm1Named_of_lemma2 (h2 : KarLemma2) : KaracubaThm1Named :=
  karacubaThm1Named_of_lemmas leaf_karLemma1_mvt_split h2

end LeanLab.ExceptionalSet.U1539.KaracubaThm1Wire1122
