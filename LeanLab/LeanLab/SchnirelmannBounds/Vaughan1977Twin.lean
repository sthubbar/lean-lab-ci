/-
P0066 Vaughan 1977, the constant C of (2.5), p. 95. Unit U-6850, CLOUD MANUAL-M1, 2026-10-21, T1.

(2.5) C = Π_{p>2} p(p-2)/(p-1)², and p(p-2)/(p-1)² = 1 - 1/(p-1)², so C is the lab's
`ChenExplicit.twinC`. Its upper bound in (2.10), C < 0.6602, follows from the lab's PROVED
`twinC_le_066017`. Lemma 10 and the Theorem are restated with Lemma 8 at the paper's own C.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma10
import LeanLab.ChenExplicit.TwinCUpper

namespace LeanLab.SchnirelmannBounds.Vaughan1977Twin
open LeanLab.RieselVaughan1983 LeanLab.SchnirelmannBounds.Vaughan1977
  LeanLab.SchnirelmannBounds.Vaughan1977Sec6 LeanLab.SchnirelmannBounds.Vaughan1977Lemma10

/-- (2.5)'s factor is the lab's: `p(p-2)/(p-1)² = 1 - 1/(p-1)²` for `p > 2`. -/
theorem factor_eq (p : ℝ) (hp : 2 < p) : p * (p - 2) / (p - 1) ^ 2 = 1 - 1 / (p - 1) ^ 2 := by
  have h1 : p - 1 ≠ 0 := by linarith
  field_simp; ring

/-- (2.10), upper half: `C < 0.6602`, PROVED, from `twinC ≤ 0.66017`. -/
theorem C_lt : LeanLab.ChenExplicit.twinC < 0.6602 :=
  lt_of_le_of_lt LeanLab.ChenExplicit.TwinCUpper.twinC_le_066017 (by norm_num)

/-- **Lemma 10, CONDITIONAL ON Lemma 8 with the paper's C and on (2.14)**. -/
theorem lemma10_of_twin (h8 : Lemma8 LeanLab.ChenExplicit.twinC) (hRS : RS33) : Lemma10 :=
  lemma10_of (by linarith [LeanLab.ChenExplicit.twinC_bounds.1]) C_lt.le h8 hRS

/-- **The Theorem, CONDITIONAL ON (2.14), Lemma 8 with the paper's C, and Lemma 12**. -/
theorem statement27_of_twin (hRS : RS33) (h8 : Lemma8 LeanLab.ChenExplicit.twinC)
    (h12 : Lemma12) : Statement27 :=
  statement27_of_RS hRS (lemma10_of_twin h8 hRS) h12

end LeanLab.SchnirelmannBounds.Vaughan1977Twin

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Twin.factor_eq
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Twin.C_lt
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Twin.lemma10_of_twin
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Twin.statement27_of_twin
