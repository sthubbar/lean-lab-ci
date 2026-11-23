import LeanLab.Zhan1991.Integrate1122c
import LeanLab.Zhan1991.SingTailProof1122d
import LeanLab.Zhan1991.SingIdentityProof1122d
import LeanLab.Zhan1991.SingIntTailProof1122d
import LeanLab.Zhan1991.WeightedTriples1122d
import LeanLab.Zhan1991.Lemma1Proof1122d
import LeanLab.Zhan1991.WellKnownProof1122d
import LeanLab.Zhan1991.SPLIT_eq31_1122d
import LeanLab.Zhan1991.SPLIT_eq311_1122d
import LeanLab.Zhan1991.SPLIT_eq312_1122d
import LeanLab.Zhan1991.Eq38Proof1122d
import LeanLab.Zhan1991.SPLIT_majorAssembly_1122d
import LeanLab.Zhan1991.SPLIT_lemma6_1122d
import LeanLab.Zhan1991.LineShift1122d
import LeanLab.Zhan1991.PerronTrunc1122d
import LeanLab.Zhan1991.DyadicSplit1122d
import LeanLab.Zhan1991.PartialSum1122d

/-!
P0068 Zhan 1991, Theorem 1, integration of burst-20261122, session S109.
Wires the proofs of session S109 in place of the LEAFs they close: the singular series identity
and tail, the singular integral tail and weighted triple count of page 271, Lemma 1 of page 261,
the well known approach display of page 263, step 2 of the major arcs and (3.8) from (3.11) and
(3.12); and the splits of (3.1) from (3.8), of (3.11), of (3.12) and of Lemma 6.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section

/-- Page 271, step 4, the truncated singular series, PROVED from the series identity and the
tail bound, both proved in session S109. -/
theorem singTruncEval_proof : SingTruncEval :=
  singTruncEval_of_parts singSeriesIdentity_proof singSeriesTail_proof

/-- Page 271, step 3, the singular integral `3U² L⁻³ + O(U² L⁻⁴)`, PROVED from the full period
identity, the weighted triple count and the tail. -/
theorem singIntEval_proof : SingIntEval :=
  singIntEval_of_parts fullPeriodIdentity_proof weightedTriplesEval_proof singIntTail_proof

/-- Page 271, the major arc display after (3.21), PROVED from step 2 alone: steps 3, 4 and 5
are now proved. -/
theorem majorEval_of_assembly (hA : MajorAssembly) : MajorEval110 :=
  majorEval_of_steps hA singIntEval_proof singTruncEval_proof singBounded_proof

/-- Theorem 1, pages 269 to 271, CONDITIONAL ON Theorem 2, Theorem 3 of page 260 and step 2 of
the major arcs, the assembly of the arcs from the major arc approximation. PROVED. -/
theorem theorem1_of_assembly (h2 : Theorem2) (h3 : Theorem3) (hA : MajorAssembly) :
    Theorem1 :=
  theorem1_of_inputs h2 h3 (majorEval_of_assembly hA)

/-- Page 271, the major arc display after (3.21), CONDITIONAL ON the major arc approximation of
step 1 alone, the short interval Siegel Walfisz input of reference 2. PROVED. -/
theorem majorEval_of_approx (h1 : MajorArcApprox) : MajorEval110 :=
  majorEval_of_assembly (majorAssembly_of_approx_split h1)

/-- Theorem 1, pages 269 to 271, CONDITIONAL ON exactly three named inputs: Theorem 2 and
Theorem 3 of page 260 and the major arc approximation `MajorArcApprox` of page 271 step 1.
Every other step of the major arcs is PROVED. This replaces the paper's whole major arc
display `MajorEval110` by its one analytic input. -/
theorem theorem1_of_approx (h2 : Theorem2) (h3 : Theorem3) (h1 : MajorArcApprox) :
    Theorem1 :=
  theorem1_of_inputs h2 h3 (majorEval_of_approx h1)

/-- The first assertion of Theorem 1, solvability of (1.1), CONDITIONAL ON the same three named
inputs. PROVED. -/
theorem solvable_of_approx (h2 : Theorem2) (h3 : Theorem3) (h1 : MajorArcApprox) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      Solvable N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) :=
  solvable_of_theorem1 (theorem1_of_approx h2 h3 h1) singGtHalf

/-- Theorem 1 CONDITIONAL ON Theorem 2, the four cited inputs of the page 269 proof of Theorem 3,
and the major arc approximation. PROVED. -/
theorem theorem1_of_thm3_cited_approx (h2 : Theorem2) (h6 : PanPanLemma6) (h23 : Lemma4Eq23)
    (h24 : Lemma4Eq24) (h5 : Lemma5NoExc) (h1 : MajorArcApprox) : Theorem1 :=
  theorem1_of_approx h2 (theorem3_of_cited h6 h23 h24 h5) h1

/-- Display (3.8) CONDITIONAL ON the three Propositions for (3.11) and the three for (3.12).
PROVED from the S109 proofs of pages 265 to 269. -/
theorem eq38_of_props (p1 : Prop1_311_1122d) (p2 : Prop2_311_1122d) (p3 : Prop3_311_1122d)
    (r1 : Prop1_312) (r2 : Prop2_312) (r3 : Prop3_312) : Eq38 :=
  eq38_of_eq311_eq312_proof (eq311_of_props p1 p2 p3) (eq312_of_props r1 r2 r3)

/-- Lemma 6 of page 262 through its split, the Montgomery Vaughan LEAF. Shows `sorryAx`. -/
theorem lemma6_1122d : Lemma6 := zhan_lemma6_split

/-- Theorem 2 CONDITIONAL ON (3.1) and the middle range reduction of pages 262 and 263: the well
known approach display and the large range are proved. PROVED. -/
theorem theorem2_of_eq31_middle (h31 : Eq31) (hr : MiddleReduction) : Theorem2 :=
  theorem2_of_ranges (smallRange_of_wellKnown_eq31 wellKnown_proof h31) hr
    largeRange_of_vinogradov

/-- Display (3.1) through the deepest current splits: (3.8) from (3.11) and (3.12), (3.11) from
Propositions 1 to 3, and the four steps from (3.8) to (3.1) with Lemma 1 proved. Shows `sorryAx`
through the remaining LEAFs. -/
theorem eq31_deep_1122d : Eq31 :=
  eq31_of_parts (eq38_of_eq311_eq312_proof eq311_split eq312_split) dyadic_split_leaf
    perron_trunc_leaf line_shift_leaf (partialSum_lemma1_leaf zhan_lemma1_proof) tChoice_proved

/-- Theorem 2 through the deepest current splits. Shows `sorryAx` through the remaining LEAFs. -/
theorem theorem2_deep_1122d : Theorem2 :=
  theorem2_of_eq31_middle eq31_deep_1122d middle_reduction_leaf

/-- Theorem 1 through the deepest current splits of sessions S80 and S109. Shows `sorryAx` through
the remaining LEAFs. -/
theorem theorem1_deepest_1122d : Theorem1 :=
  theorem1_of_inputs theorem2_deep_1122d zhan_theorem3_cited_only
    (majorEval_of_approx majorArcApprox_cited)


/-! ### Round 2: the four steps of the (3.1) split, through their S109 files.
Each file copies the target Prop under a suffix, since SPLIT_eq31_1122d was not built there; the
bridges below check by type that each copy is the original Prop. -/

/-- Page 264, the line shift to `Re s = 1/2`, PROVED in LineShift1122d.lean. -/
theorem lineShift_proof : LineShift := lineShift_proof_ls

/-- Page 263 display (3.3), Perron's formula, through its split in PerronTrunc1122d.lean. Shows
`sorryAx` through two LEAFs. -/
theorem perronTrunc_1122d : PerronTrunc := perronTrunc_split_pt

/-- Page 264 top, the dyadic split, through DyadicSplit1122d.lean. Shows `sorryAx` through two
LEAFs. -/
theorem dyadicSplit_1122d : DyadicSplit := dyadicSplit_split_dy

/-- Pages 264 and 265, partial summation with Lemma 1, through PartialSum1122d.lean. Shows
`sorryAx` through three LEAFs. -/
theorem partialSum_1122d (h1 : Lemma1) : PartialSumLemma1 := partialSum_lemma1_ps h1

/-- Display (3.1) from (3.8) CONDITIONAL ON the dyadic split, Perron's formula and the partial
summation step; the line shift, Lemma 1 and the choice of `T` are PROVED. -/
theorem eq31_of_eq38_inputs (h38 : Eq38) (hD : DyadicSplit) (hP : PerronTrunc)
    (hH : PartialSumLemma1) : Eq31 :=
  eq31_of_parts h38 hD hP lineShift_proof hH tChoice_proved

/-- Display (3.1) through the deepest splits of round 2. Shows `sorryAx` through the LEAFs. -/
theorem eq31_deep2_1122d : Eq31 :=
  eq31_of_eq38_inputs (eq38_of_eq311_eq312_proof eq311_split eq312_split) dyadicSplit_1122d
    perronTrunc_1122d (partialSum_1122d zhan_lemma1_proof)

/-- Theorem 1 through the deepest splits of round 2. Shows `sorryAx` through the LEAFs. -/
theorem theorem1_deepest2_1122d : Theorem1 :=
  theorem1_of_inputs (theorem2_of_eq31_middle eq31_deep2_1122d middle_reduction_leaf)
    zhan_theorem3_cited_only (majorEval_of_approx majorArcApprox_cited)

end

end LeanLab.Zhan1991
