/-
Public statements of Brudern and Perelli 1998.
Task264 moves the unchanged data to State1539Data264 to let the proved
section 8 leaves discharge the original derivative statements.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.Decomp1539a
import LeanLab.ExceptionalSet.KaracubaCore

namespace LeanLab.ExceptionalSet.U1539

/-! ### Sealed statements -/

/-- CITED. Theorem 2 of J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998) 353-378, p. 354, proved there in §8 from Karacuba's estimate.
Decomp1539a splits that proof into leaves. -/
theorem theorem2 : Theorem2 := by sorry

/-- CITED. Lemma 10 of Brüdern-Perelli 1998, p. 370-371, which is Theorem 1 of
A. A. Karacuba, Estimates for trigonometric sums by Vinogradov's method, and some
applications, Proc. Steklov Inst. Math. 112 (1973) 251-265, in Brüdern-Perelli's notation.
Wired 2026-11-12, coordinator decision 5, to `KaracubaCore.lemma10_of_karacuba`, so it is now
CONDITIONAL ON the leaves of KaracubaCore: the CITED Lemmas 1 and 2 of Karacuba,
the LEAF `leaf_W_bound`, which reduces to `KaracubaWSplit.leafW1_bound`; `leaf_karLemma3` and
`leaf_T_bound` are PROVED, the latter from the CITED Lemma 2, and the QUESTION leaf `leaf_s1_case` for the case `S = {1}`, which Karacuba's Theorem 1
does not cover; a falsifier found it TRUE-LOOKING, see the burst 4 note. Theorem 2 avoids that leaf
through `Theorem2Kar.theorem2_via_karacuba_kar`. -/
theorem lemma10 : Lemma10 := KaracubaCore.lemma10_of_karacuba

/-- Lemma 1 of the paper, p. 355-356, a Poisson summation identity. Open statement. -/
theorem lemma1 : Lemma1 := by sorry

/-- Lemma 4 of the paper, p. 359, from Theorem 2 with `c = 1/2` by Vinogradov's
equidistribution argument. Open statement. -/
theorem lemma4 : Lemma4 := by sorry

/-- Lemma 6 of the paper, p. 362, proved in its §6. Open statement. -/
theorem lemma6 : Lemma6 := by sorry

/-- Lemma 7 of the paper, p. 362-364. Open statement. -/
theorem lemma7 : Lemma7 := by sorry

/-- Lemma 8 of the paper, p. 364-365. Open statement. -/
theorem lemma8 : Lemma8 := by sorry

/-- Lemma 9 of the paper, p. 368, proved in its §7. Open statement. -/
theorem lemma9 : Lemma9 := by sorry

/-- Lemma 11 of the paper, p. 372. Open statement; Decomp1539a splits it. -/
theorem lemma11 : Lemma11 := by
  exact section8_derivative_inputs.1

/-- Lemma 12 of the paper, p. 373, with `s^{2t+j}`. Open statement; Decomp1539a splits it. -/
theorem lemma12 : Lemma12 := by
  exact section8_derivative_inputs.2.1

/-- Lemma 13 of the paper, p. 375. Open statement; Decomp1539a splits it. -/
theorem lemma13 : Lemma13 := by
  exact section8_derivative_inputs.2.2.1

/-- Lemma 14 of the paper, p. 375. Open statement; Decomp1539a splits it. -/
theorem lemma14 : Lemma14 := by
  exact section8_derivative_inputs.2.2.2.1

/-- Lemma 15 of the paper, p. 375-376. Open statement; Decomp1539a splits it. -/
theorem lemma15 : Lemma15 := by
  exact section8_derivative_inputs.2.2.2.2.1

/-- Lemma 16 (a) of the paper, p. 376. Open statement; Decomp1539a splits it. -/
theorem lemma16a : Lemma16a := by
  exact section8_derivative_inputs.2.2.2.2.2.1

/-- Lemma 16 (b) of the paper, p. 376. Open statement; Decomp1539a splits it. -/
theorem lemma16b : Lemma16b := by
  exact section8_derivative_inputs.2.2.2.2.2.2


/-- Theorem 2 from the CITED `lemma10` of State1539 and the leaves. -/
theorem theorem2_via_karacuba : Theorem2 := theorem2_of_all_leaves lemma10

end LeanLab.ExceptionalSet.U1539
