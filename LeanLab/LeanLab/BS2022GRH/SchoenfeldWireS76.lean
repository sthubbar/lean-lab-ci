/-
ROUTE BURST S76 burst-20261122, unit thm10_63_wire. Schoenfeld 1976 Theorem 10, display
(6.3), assembled exactly as in `SchoenfeldThm10S70.thm10_63_S70`, with the former LEAF
`rosser_walker_599`, Schoenfeld p. 339 after (6.16), replaced by its S76 proof
`SchoenfeldRW599S76.rosser_walker_599_S76`, a kernel checked computation.
AI wrote this Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.SchoenfeldThm10S70
import LeanLab.BS2022GRH.SchoenfeldRW599S76

namespace LeanLab.BS2022GRH.SchoenfeldWireS76
open Real LeanLab.BS2022GRH.SchoenfeldThm10S70
noncomputable section

/-- Schoenfeld 1976 (6.16) for `599 ≤ x < e¹⁶`, the proof of
`SchoenfeldThm10S70.display_6_16` with the Rosser-Walker range now proved. -/
theorem display_6_16_S76 (x : ℝ) (h1 : 599 ≤ x) (h2 : x < exp 16) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x := by
  have hx0 : 0 < x := by linarith
  have hs : 0 < √x := sqrt_pos.mpr hx0
  have hpi : 0 < π := pi_pos
  have hpi4 : π < 3.1416 := pi_lt_d4
  have hx8 : x ≤ 10 ^ 8 := by linarith [exp16_lt]
  by_cases h1400 : 1400 ≤ x
  · have hL := log_ge_72 h1400
    have h18 := (rs62_thm18 x hx0 hx8).1
    have hk : 2.05282 * (8 * π) < log x ^ 2 := by nlinarith
    have : 2.05282 * √x < √x * log x ^ 2 / (8 * π) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  by_cases h1200 : 1200 ≤ x
  · have hL := log_ge_709 h1200
    have h19 := rs62_thm19 x (Or.inl ⟨hx0, by linarith⟩)
    have hk : 2 * (8 * π) < log x ^ 2 := by nlinarith
    have : 2 * √x < √x * log x ^ 2 / (8 * π) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    linarith
  exact SchoenfeldRW599S76.rosser_walker_599_S76 x h1 (by linarith)

/-- Schoenfeld 1976 Theorem 10, display (6.3): under RH, `|θ(x) - x| < √x log² x / (8π)`
for `x ≥ 599`. CONDITIONAL ON the remaining cited leaves of `SchoenfeldThm10S70`:
`display_6_11`, `rs62_3_39`, `rs62_thm18`, `rs62_thm19`. -/
theorem thm10_63_S76 : RiemannHypothesis → ∀ x : ℝ, 599 ≤ x →
    |Chebyshev.theta x - x| < √x * log x ^ 2 / (8 * π) := by
  intro hRH x hx
  by_cases h16 : exp 16 ≤ x
  · exact range_e16 hRH x h16
  rw [not_le] at h16
  have hx0 : 0 < x := by linarith
  have hpos : 0 < √x * log x ^ 2 / (8 * π) := by
    have : 0 < log x := log_pos (by linarith)
    have : 0 < √x := sqrt_pos.mpr hx0
    have := pi_pos
    positivity
  have hup := (rs62_thm18 x hx0 (by linarith [exp16_lt])).2
  have hlo := display_6_16_S76 x hx h16
  rw [abs_lt]; constructor <;> linarith

end

end LeanLab.BS2022GRH.SchoenfeldWireS76

#print axioms LeanLab.BS2022GRH.SchoenfeldWireS76.thm10_63_S76
