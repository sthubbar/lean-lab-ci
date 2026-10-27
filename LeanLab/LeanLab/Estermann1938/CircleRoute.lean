import LeanLab.Estermann1938.Main
import LeanLab.ExceptionalSet.MVMajorFinal

/-!
# Estermann 1938, p. 307, by his own circle method route

Unit U-6255, CLOUD 20261020T0917Z-cloud39. AI wrote the Lean code. KNOWN mathematics.
Binary Goldbach is OPEN.

`main_circle`: the printed main result, `Q(n) = O(n log^{-a} n)` for every `a > 0`, from
`LeanLab.ExceptionalSet.MVMajor.estermann_circle_method`, the circle method with Vinogradov's
minor arcs and the major arc count, in place of `main`'s route through Heath-Brown.
-/

namespace LeanLab.Estermann1938

/-- Estermann 1938, p. 307, by the circle method: PROVED unconditional. -/
theorem main_circle : theorem_stmt :=
  theorem_of_logPowerSaving LeanLab.ExceptionalSet.MVMajor.estermann_circle_method

end LeanLab.Estermann1938
