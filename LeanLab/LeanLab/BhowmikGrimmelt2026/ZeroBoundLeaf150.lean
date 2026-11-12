/-
Leaf of `zeroBound_lower150`: P0029 Section 3, page 12, the remark after the display
`q^{1/2} N^{Θ+ε}`, "in the best case we could hope for Θ = 1/2".  The lower limit one half rests
on Hardy 1914, Sur les zeros de la fonction zeta de Riemann: the Riemann zeta function has a zero
on the critical line.  The survey cites it and gives no proof.

Moved here from `Decomp150a.lean` by the REPAIR pass 20261112 so that an existing file carries no
newly added sorry.  The statement is unchanged, and `zeroBound_lower150` there still derives the
lower bound from this leaf exactly as before.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF: P0029 Section 3, page 12, the remark after the display `q^{1/2} N^{Θ+ε}`,
"in the best case we could hope for Θ = 1/2".  The lower limit one half rests on Hardy 1914,
Sur les zeros de la fonction zeta de Riemann: the Riemann zeta function has a zero on the
critical line.  The survey cites it and gives no proof, so this is CITED and OPEN.
AI wrote the Lean code. Goldbach is open. -/
theorem hardy_critical_line_zero150 :
    ∃ t : ℝ, riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  sorry

end LeanLab.BhowmikGrimmelt2026
