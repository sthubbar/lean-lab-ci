/-
Jia 1996 Lemma 27, pages 281 and 282, certified remainder coefficients.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
The subtotal bounds are CONDITIONAL ON eight OPEN computational integral leaves.
The eight constant kernel certificates remain clean. No exceptional prime estimate is asserted.
-/
import LeanLab.Languasco2004.Integral564
import LeanLab.Languasco2004.Polynomial564a
import LeanLab.Languasco2004.Polynomial564s

namespace LeanLab.Languasco2004.Numeric564
open Real Finset RemainderData564 Integral564 Polynomial564a Polynomial564s Short564
noncomputable section
set_option maxHeartbeats 0

/-- Pages 281 and 282: all sixteen complete source lower integrals have certified enclosures.
These enclosures certify the required subtotals directly. CONDITIONAL ON the eight OPEN short_integral inputs. -/
theorem certified_row_lower (i : Fin 16) : (rowTarget i : ℝ) ≤ sourceIntegral i := by
  fin_cases i
  · exact (short_integral_2).trans (short_integral_le ⟨0, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_3).trans (polynomial_integral_le ⟨1, by decide⟩)
  · exact (short_integral_4).trans (short_integral_le ⟨2, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_5).trans (polynomial_integral_le ⟨3, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_6).trans (polynomial_integral_le ⟨4, by decide⟩)
  · exact (short_integral_7).trans (short_integral_le ⟨5, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_8).trans (polynomial_integral_le ⟨6, by decide⟩)
  · exact (short_integral_9).trans (short_integral_le ⟨7, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_10).trans (polynomial_integral_le ⟨8, by decide⟩)
  · exact (short_integral_11).trans (short_integral_le ⟨9, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_12).trans (polynomial_integral_le ⟨10, by decide⟩)
  · exact (short_integral_13).trans (short_integral_le ⟨11, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_14).trans (polynomial_integral_le ⟨12, by decide⟩)
  · exact (short_integral_15).trans (short_integral_le ⟨13, by decide⟩)
  · simpa [rowTarget, isLog] using (polynomial_integral_16).trans (polynomial_integral_le ⟨14, by decide⟩)
  · exact (short_integral_17).trans (short_integral_le ⟨15, by decide⟩)

/-- Page 281: the complete Lemma 11 remainder integral has a positive reserve. CONDITIONAL ON the eight OPEN short_integral inputs. -/
theorem integral11_lower : (0.0148871 : ℝ) ≤ integral11 := by
  calc
    _ ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => i.val < 9)), (rowTarget i : ℝ) := by
      norm_num [sum_filter, Fin.sum_univ_succ, numericData, rowTarget, isLog]
    _ ≤ integral11 := sum_le_sum fun i _ => certified_row_lower i

/-- Pages 281 and 282: the complete Lemma 12 integral has a positive reserve. CONDITIONAL ON the eight OPEN short_integral inputs. -/
theorem integral12_lower : (0.0093921 : ℝ) ≤ integral12 := by
  calc
    _ ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin 16 => ¬ i.val < 9)), (rowTarget i : ℝ) := by
      norm_num [sum_filter, Fin.sum_univ_succ, numericData, rowTarget, isLog]
    _ ≤ integral12 := sum_le_sum fun i _ => certified_row_lower i

/-- Pages 281 and 282: the two mean value families partition the full lower integral. -/
theorem integral_split : integral11 + integral12 = remainderIntegral := by
  exact sum_filter_add_sum_filter_not _ _ _

/-- Page 282: all sixteen remaining terms exceed the required subtotal with reserve. CONDITIONAL ON the eight OPEN short_integral inputs. -/
theorem remainder_numeric_margin : (0.0242792 : ℝ) ≤ remainderIntegral := by
  rw [← integral_split]
  linarith [integral11_lower, integral12_lower]

/-- Pages 281 and 282: the two proper source families have the stated printed subtotals. -/
theorem printed_family_coefficient_sums :
    (0.000244 : ℝ)+0.000282+0.000276+0.008036+0.000393+0.001843+
      0.000369+0.000357+0.003087 = 0.014887 ∧
    (0.001545 : ℝ)+0.000679+0.000634+0.002319+0.002910+0.000330+0.000975 = 0.009392 := by
  norm_num

/-- Page 282: the seventeen printed decimal coefficients have the claimed total. -/
theorem printed_coefficient_sum :
    (0.000303 : ℝ) + (0.000244 + 0.000282 + 0.000276 + 0.008036 +
      0.000393 + 0.001843 + 0.000369 + 0.000357 + 0.003087 + 0.001545 +
      0.000679 + 0.000634 + 0.002319 + 0.002910 + 0.000330 + 0.000975) = 0.024582 := by
  norm_num

#print axioms certified_row_lower
#print axioms integral11_lower
#print axioms integral12_lower
#print axioms integral_split
#print axioms remainder_numeric_margin
#print axioms printed_family_coefficient_sums
#print axioms printed_coefficient_sum
end
end LeanLab.Languasco2004.Numeric564
