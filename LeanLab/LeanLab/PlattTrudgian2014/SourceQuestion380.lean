/-
AI wrote this Lean code. Binary Goldbach is open.
QUESTION about the literal three term formula in P0026 page 179 Lemma 6.
The sealed matrix follows the two sums of Lemma 5 on page 178.
-/
import LeanLab.PlattTrudgian2014.Perron125

namespace LeanLab.PlattTrudgian2014

/-- P0026 page 179 Lemma 6, a literal zero column comparison.
QUESTION only. This does not refute either numerical corollary. -/
theorem half_transfer_zero_column_question380 :
    halfTransfer125 0 0 ≠
      (halfCoeffInt125 (2 * 0 - 0) + halfCoeffInt125 (2 * 0 + 0) +
        halfCoeffInt125 (0 - 2 * 0)) / 2 := by
  norm_num [halfTransfer125, halfCoeffInt125, halfCoeff125]

#print axioms half_transfer_zero_column_question380

end LeanLab.PlattTrudgian2014
