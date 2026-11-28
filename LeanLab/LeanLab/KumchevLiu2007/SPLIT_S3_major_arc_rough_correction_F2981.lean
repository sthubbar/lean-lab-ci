/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 5 hypothesis (A2.2) and page 15.
burst-20261127 S3-27. SPLIT of `F2981.major_arc_rough_correction_F2981`, whose statement
is the cited named hypothesis `Prep1121KLMajor.A22Corr`.

Page 15 explains the main term f2 of (A2.2) for lambda0, the z0 rough indicator: the
first term accounts for the primes in the support of lambda0 and the second for the
products p1 p2 with z0 < p1 <= p2; for the primes it points to [14, Lemma 5.1] and to
Mikawa and Peneva [19, Lemma 2]. The reduction `Split1122KLA22Parts.A22Corr_of_parts`
is PROVED: on the square window every z0 rough m is a prime or such a product.

This file states the two parts as LEAF theorems and proves the exact statement of the
target from them. Both leaves are CITED walls, the Huxley type zero density input of
page 15. No new definition.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc
import LeanLab.KumchevLiu2007.Split1122KLA22Parts

namespace LeanLab.KumchevLiu2007.F2981.S3RoughCorr

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open LeanLab.KumchevLiu2007.Prep1121KLMajor LeanLab.KumchevLiu2007.Split1122KLA22Parts
open scoped BigOperators Topology

/-- LEAF: P0088 page 15, hypothesis (A2.2) of page 5 for the primes part of lambda0,
main term 1/log m, cited there to [14, Lemma 5.1] and to Mikawa and Peneva [19,
Lemma 2], a short interval Siegel Walfisz estimate in mean square for primes p with
p^2 in (t, t + delta t], moduli up to a power of log X. Class HARD, CITATION WALL:
needs a zero density estimate of Huxley strength and Siegel's theorem. -/
theorem leaf_a22_prime_corr : A22PrimeCorr := by
  sorry

/-- LEAF: P0088 page 15, hypothesis (A2.2) of page 5 for the part of lambda0 on the
products p1 p2 of primes with z0 <= p1 <= p2, main term the second term of f2,
asserted on page 15 by the same Huxley type methods. Class HARD, CITATION WALL. -/
theorem leaf_a22_p2_corr : A22P2Corr := by
  sorry

/-- Assembly: the exact statement of `F2981.major_arc_rough_correction_F2981`, the
named hypothesis A22Corr, from the two part leaves through the PROVED reduction
`Split1122KLA22Parts.A22Corr_of_parts`. -/
theorem major_arc_rough_correction_of_leaves : Prep1121KLMajor.A22Corr :=
  A22Corr_of_parts leaf_a22_prime_corr leaf_a22_p2_corr

end LeanLab.KumchevLiu2007.F2981.S3RoughCorr

#print axioms LeanLab.KumchevLiu2007.F2981.S3RoughCorr.major_arc_rough_correction_of_leaves
