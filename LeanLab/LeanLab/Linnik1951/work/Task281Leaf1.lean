import Mathlib
import LeanLab.DERZ1997.Statements

namespace LeanLab.Linnik1951

noncomputable def testLine1622 (N : ℕ) (t : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log N : ℝ) : ℂ) + (t : ℂ) * Complex.I

example (hG : LeanLab.DERZ1997.GRH) :
    ∀ N : ℕ, 1 < N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ t : ℝ, DirichletCharacter.LFunction χ (testLine1622 N t) ≠ 0 := by
  intro N hN q _ χ hχ t hzero
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hre : (testLine1622 N t).re = 1 / 2 + 1 / Real.log (N : ℝ) := by
    simp only [testLine1622, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hgt : 1 / 2 < (testLine1622 N t).re := by
    rw [hre]
    have hone : 0 < 1 / Real.log (N : ℝ) := one_div_pos.mpr hlog
    linarith
  rcases lt_or_ge (testLine1622 N t).re 1 with hlt | hge
  · have hhalf := hG q χ (testLine1622 N t) hzero (by linarith) hlt
    linarith [hgt]
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge hzero

end LeanLab.Linnik1951
