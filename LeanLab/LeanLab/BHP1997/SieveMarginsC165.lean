/-
P0069, pages 2, 41 and 51. Elementary discard budgets and the
quantitative positive margin. The actual discarded integral estimates
remain inputs. AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.Statements

namespace LeanLab.BHP1997.SieveMarginsC165

/-- Page 41, the five numerical discard bounds imply u0 above 0.9953.
This is CONDITIONAL on the actual discarded integral bounds. -/
theorem lower_discard_budget {d2 d3 d4 g s u0 : ℝ}
    (h2 : d2 < 0.0003) (h3 : d3 < 0.002) (h4 : d4 < 0.002)
    (hg : g < 0.0003) (hs : s < 0.0001)
    (hu : 1 - (d2 + d3 + d4 + g + s) ≤ u0) :
    0.9953 < u0 := by linarith

/-- Page 51, subtracting the two discarded Buchstab integrals from 1
leaves density above 0.05 when their total is below 0.95.
This is CONDITIONAL on the actual integral bound and density identity. -/
theorem short_lower_discard_budget {e2 e4 v0 : ℝ}
    (hE : e2 + e4 < 0.95) (hv : 1 - e2 - e4 ≤ v0) :
    0.05 < v0 := by linarith

/-- Pages 2, 41 and 42, the sharper long-weight constants give a
positive signed correlation margin above 0.039445. This statement is
an elementary inequality for constants in the paper's ranges. -/
theorem sharp_correlation_margin {u0 u1 v0 v1 : ℝ}
    (hu0 : 0.9953 < u0) (hu1 : u1 < 1.0001)
    (hv0 : 0.05 < v0) (hv : v0 ≤ v1) (hv1 : v1 < 2.2) :
    0.039445 < u0 * v1 + u1 * v0 - u1 * v1 := by
  have hvpos : 0 < v1 := by linarith
  have hlow := mul_lt_mul_of_pos_right hu0 hvpos
  have hup := mul_le_mul_of_nonpos_right hu1.le (sub_nonpos.mpr hv)
  nlinarith

end LeanLab.BHP1997.SieveMarginsC165
