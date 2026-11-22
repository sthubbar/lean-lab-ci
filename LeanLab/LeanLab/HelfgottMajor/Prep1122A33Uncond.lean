import LeanLab.HelfgottMajor.Prep1121A33Reduce
import LeanLab.HelfgottMajor.MainAssemblyLeaves123

/-!
ROUTE BURST S4, burst-20261122, unit P1122-0035, REPAIR audit of the HelfgottA33 label.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 67, display A.33.
The named hypothesis `DQInitialSegmentBound.HelfgottA33` is now proved,
`Prep1121A33Reduce.helfgottA33_holds`. The results of `MainA33Chain123`, `MainAssembly123` and
`MainAssemblyLeaves123` that take it as an argument `hA` are therefore no longer CONDITIONAL ON
HelfgottA33. Their statements are left unchanged; this file gives each of the top results a
twin with `hA` discharged, so that the downstream labels can drop HelfgottA33.
No new statement content, no sorry. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1122A33Uncond
open Real LeanLab.HelfgottMajor.SplitGaussian123

/-- P0014 Corollary 3.2, page 10, display 3.4 at k = 0 with c0 = 4.226, the sealed statement
`SplitGaussian123.corollary_3_2_k0`, no longer conditional on HelfgottA33. -/
theorem corollary_3_2_k0 : type_of% @SplitGaussian123.corollary_3_2_k0 :=
  MainA33Chain123.corollary_3_2_k0_of_A33_match Prep1121A33Reduce.helfgottA33_holds

/-- The named initial bound of DQ6, P0014 pages 24 and 25, no longer conditional on
HelfgottA33. -/
theorem initial_named_dq6 : DQ6.InitialSegmentBoundDQ6 :=
  MainA33Chain123.initial_named_dq6_of_A33 Prep1121A33Reduce.helfgottA33_holds

/-- P0014 Theorem 1.1, page 3, `MainAssembly123.theorem_1_1_of_named` with HelfgottA33
discharged. CONDITIONAL ON PolyaVinogradov420 and BookZeroCount, and on the two open step
arguments `htl` and `h41`, exactly as before. -/
theorem theorem_1_1_of_named
    (hPV : MainHyps123.PolyaVinogradov420)
    (hB : MainHyps123.BookZeroCount)
    (htl : type_of% @MainTail123.tail_mass_bound_leaf)
    (h41 : type_of% @Lemma41Leaf123.lemma_4_1_gaussian_corrected) :
    Decomp123.Theorem11 :=
  MainAssembly123.theorem_1_1_of_named Prep1121A33Reduce.helfgottA33_holds hPV hB htl h41

/-- P0014 Theorem 1.1, `MainAssemblyLeaves123.theorem_1_1_of_named_and_leaves` with
HelfgottA33 discharged. CONDITIONAL ON PolyaVinogradov420 and BookZeroCount, and resting on the
open LEAFs listed in `MainAssemblyLeaves123`. -/
theorem theorem_1_1_of_named_and_leaves
    (hPV : MainHyps123.PolyaVinogradov420)
    (hB : MainHyps123.BookZeroCount) :
    Decomp123.Theorem11 :=
  MainAssemblyLeaves123.theorem_1_1_of_named_and_leaves
    Prep1121A33Reduce.helfgottA33_holds hPV hB

end LeanLab.HelfgottMajor.Prep1122A33Uncond

#print axioms LeanLab.HelfgottMajor.Prep1122A33Uncond.corollary_3_2_k0
#print axioms LeanLab.HelfgottMajor.Prep1122A33Uncond.initial_named_dq6
#print axioms LeanLab.HelfgottMajor.Prep1122A33Uncond.theorem_1_1_of_named
#print axioms LeanLab.HelfgottMajor.Prep1122A33Uncond.theorem_1_1_of_named_and_leaves
