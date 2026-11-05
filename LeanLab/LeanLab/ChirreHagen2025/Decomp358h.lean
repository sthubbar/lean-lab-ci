import LeanLab.ChirreHagen2025.Decomp358f
import LeanLab.ChirreHagen2025.Decomp358g
import LeanLab.ChirreHagen2025.SeriesBounds297
import LeanLab.ChirreHagen2025.Decomp122

/-!
P0075 pages 5 to 6, Lemma 2.4. The Taylor identities and scalar series
comparisons are proved. Only the positive Laurent coefficient estimates remain.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp358h
open Decomp272a

/-- P0075 pages 5 to 6, Lemma 2.4.
CONDITIONAL ON the positive Laurent coefficient estimates from Berndt.
The constant coefficient, both analytic identities and both scalar comparisons
have proved replacements in the lab. -/
theorem lemma2_4_of_positive_coefficients
    (hcoeff : ∀ n : ℕ, 1 ≤ n → ‖laurentCoeff n‖ ≤
      (if Even n then 4 else 2) / ((n : ℝ) * Real.pi ^ n)) : lemma2_4 := by
  intro t ht htop
  have hz := (SeriesBounds297.laurent_log_majorant laurentCoeff _ t ht htop
    (Decomp358e.laurent_series t ht htop) Decomp358f.laurentCoeff_zero_bound hcoeff).trans
    Decomp272a.log_majorant_numeric
  have hd := (SeriesBounds297.differentiated_laurent_majorant laurentCoeff _ t ht htop
    (Decomp358g.differentiated_laurent_series t ht htop) hcoeff).trans
    Decomp272b.derivative_majorant_numeric
  exact Decomp122.quotient_bound t ht htop _ _ hz hd

/-- P0075 pages 5 to 6. Exact target type of Decomp122.lemma2_4_assembled.
CONDITIONAL ON the inherited positive coefficient leaf only. The new Taylor
proofs remove the two analytic series identities from this dependency chain. -/
theorem lemma2_4_assembled : lemma2_4 := by
  exact lemma2_4_of_positive_coefficients Decomp272a.laurent_coefficient_bounds.2

end LeanLab.ChirreHagen2025.Decomp358h
