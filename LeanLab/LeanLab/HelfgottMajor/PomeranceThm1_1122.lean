import Mathlib
import LeanLab.HelfgottMajor.PVTailWire1122

/-!
Route burst S75, burst-20261122, tag pomerance-thm1.
Pomerance 2011, Remarks on the Polya-Vinogradov inequality, Integers 11A, Article 19, Theorem 1 on
page 3, checked against the rendered page image of papers/Pomerance2011-Integers11A-A19.pdf: for χ
a primitive character to the modulus q > 1, the sum of χ(a) over any interval M ≤ a ≤ N is at most
(2/π²) q^(1/2) log q + (4/π²) q^(1/2) log log q + (3/2) q^(1/2) for χ even, and
(1/(2π)) q^(1/2) log q + (1/π) q^(1/2) log log q + q^(1/2) for χ odd.

Assembled from the wired cases `PVTailWire1122.pomerance_even_case` and
`PVTailWire1122.pomerance_odd_case`, with their inputs Lemma 3 and the Section 4 bound PROVED in
`PVLemmasWire1122` and display 10 and |τ(χ)| = √q PROVED in `PV420Split1122`. Intervals of
natural numbers cover every interval of integers up to a shift by a multiple of q.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PomeranceThm1_1122

open Real Finset

/-- Pomerance 2011 Theorem 1, page 3, for every interval [M, N] of natural numbers. PROVED. -/
theorem pomerance_theorem_1 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 1 < q) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  split_ifs with h
  · exact LeanLab.HelfgottMajor.PVTailWire1122.pomerance_even_case χ hχ (by omega)
      LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_lemma3
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h M N
  · exact LeanLab.HelfgottMajor.PVTailWire1122.pomerance_odd_case χ hχ (by omega)
      LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_sec4
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_odd hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h M N

end LeanLab.HelfgottMajor.PomeranceThm1_1122

#print axioms LeanLab.HelfgottMajor.PomeranceThm1_1122.pomerance_theorem_1
