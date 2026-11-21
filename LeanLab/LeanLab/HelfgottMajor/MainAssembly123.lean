import LeanLab.HelfgottMajor.MainAssemblyParts123
import LeanLab.HelfgottMajor.MainA33Chain123
import LeanLab.HelfgottMajor.MainPV123
import LeanLab.HelfgottMajor.MainBook123
import LeanLab.HelfgottMajor.MainTail123

/-!
HELFGOTT MAIN THEOREM burst, session CLOUD-burst20261120c, 2026-11-21. P0014, Helfgott,
Major arcs for Goldbach's problem, arXiv 1305.2897v4, Theorem 1.1, page 3.

The conditional twin of `Decomp123.theorem_1_1`. It feeds the branch twins of this burst into
`MainAssemblyParts123.theorem_1_1_of_parts`:
- `MainA33Chain123.corollary_3_2_k0_of_A33`, from the named hypothesis HelfgottA33, P0014 page
  67 display A.33, a cited computation
- `MainPV123.residue_main_conj_bound_of_zeros_of_PV`, from the named hypothesis
  PolyaVinogradov420, P0014 page 36 display 4.20, Pomerance 2011 Theorem 1
- `MainBook123.low_zero_bound_slack_of_book`, from the named hypothesis BookZeroCount, P0014
  page 38 display 4.26 in the one-sided form of the book, page 431 display 16.21
- `MainTail123.tail_mass_summable_of_book`, from BookZeroCount
Two steps that Helfgott proves himself are NOT yet proved and enter as explicit arguments,
each with the exact type of a LEAF, so that nothing here is hidden:
- `htl`, the type of `MainTail123.tail_mass_bound_leaf`, the bound half of P0014 Lemma 4.5,
  page 41, displays 4.33 to 4.35, a QUESTION since display 4.35 is false as printed
- `h41`, the type of `Lemma41Leaf123.lemma_4_1_gaussian_corrected`, P0014 Lemma 4.1, page 31,
  in the lab's corrected form
These two arguments are open steps of the paper, NOT named citations.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.MainAssembly123
open Real LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123

/-- P0014 Lemma 4.5, page 41, the sealed statement of `tail_mass_of_corollary`, from
BookZeroCount and the open bound step `htl`. -/
theorem tail_mass_of_corollary_of_book_and_leaf (hB : MainHyps123.BookZeroCount)
    (htl : type_of% @MainTail123.tail_mass_bound_leaf) :
    type_of% @SplitGaussian123.tail_mass_of_corollary :=
  fun q _ χ hχ δ T hT hzeros hcor =>
    ⟨MainTail123.tail_mass_summable_of_book hB q χ hχ δ T hT hcor,
      htl hB q χ hχ δ T hT hzeros hcor⟩

/-- CONDITIONAL twin of `Decomp123.theorem_1_1`, P0014 Theorem 1.1, page 3, proof on pages 56
and 57. Named hypotheses, each a cited input: `hA` HelfgottA33, P0014 page 67 display A.33;
`hPV` PolyaVinogradov420, P0014 page 36 display 4.20, Pomerance 2011 Theorem 1; `hB`
BookZeroCount, P0014 page 38 display 4.26, book page 431 display 16.21. Open steps of the
paper, given as arguments of LEAF type: `htl`, Lemma 4.5 bound, and `h41`, Lemma 4.1 corrected.
The input HelfgottInput, P0014 page 56, is part of the statement `Theorem11` itself. -/
theorem theorem_1_1_of_named
    (hA : DQInitialSegmentBound.HelfgottA33)
    (hPV : MainHyps123.PolyaVinogradov420)
    (hB : MainHyps123.BookZeroCount)
    (htl : type_of% @MainTail123.tail_mass_bound_leaf)
    (h41 : type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected) :
    Decomp123.Theorem11 :=
  MainAssemblyParts123.theorem_1_1_of_parts
    (fun δ s h0 h1 hτ => MainA33Chain123.corollary_3_2_k0_of_A33 hA δ s h0 h1 hτ)
    (tail_mass_of_corollary_of_book_and_leaf hB htl)
    h41
    (fun χ hχ hz => MainPV123.residue_main_conj_bound_of_zeros_of_PV hPV χ hχ hz)
    (fun x hx q _ χ hχ δ T hT hz =>
      MainBook123.low_zero_bound_slack_of_book hB x hx q χ hχ δ T hT hz)

end LeanLab.HelfgottMajor.MainAssembly123

#print axioms LeanLab.HelfgottMajor.MainAssembly123.theorem_1_1_of_named
#print axioms LeanLab.HelfgottMajor.MainAssembly123.tail_mass_of_corollary_of_book_and_leaf
