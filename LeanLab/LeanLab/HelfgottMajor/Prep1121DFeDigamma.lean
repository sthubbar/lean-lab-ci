import LeanLab.HelfgottMajor.Prep1121VIPointwiseA
import LeanLab.Linnik.ExplicitFormula.LeftHalf

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 33, display 4.8,
from IK04 Thm. 4.15, on the line s = -1/2 + iτ with the gamma factor written through the
digamma function. The parent leaf `Prep1121VIPointwiseA.fe_digamma` is proved here with its
exact statement from the lab's `LeanLab.Linnik.ExplicitFormula.logDeriv_fe_left`, the lab's
`logDeriv_Gammaℝ`, and the pieces below.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DFeDigamma
open Complex

/-- P0014 page 33, display 4.8: χ and its inverse χ bar have the same parity κ, since
χ⁻¹(-1) = χ(-1)⁻¹. -/
theorem inv_parity {q : ℕ} {χ : DirichletCharacter ℂ q} (κ : ℕ)
    (hκ : (χ.Even ∧ κ = 0) ∨ (χ.Odd ∧ κ = 1)) :
    (χ⁻¹.Even ∧ κ = 0) ∨ (χ⁻¹.Odd ∧ κ = 1) := by
  rcases hκ with ⟨h, h0⟩ | ⟨h, h1⟩
  · left
    refine ⟨?_, h0⟩
    show χ⁻¹ (-1) = 1
    rw [MulChar.inv_apply_eq_inv', h]; simp
  · right
    refine ⟨?_, h1⟩
    show χ⁻¹ (-1) = -1
    rw [MulChar.inv_apply_eq_inv', h]; simp

/-- P0014 page 33, display 4.8, the gamma factor of parity κ through ψ:
Γℝ'/Γℝ(w + κ) = -(log π)/2 + ψ((w+κ)/2)/2 away from the poles, Davenport ch. 10.
PROVED here: unfold `DirichletCharacter.gammaFactor` with `Even.gammaFactor_def` and
`Odd.gammaFactor_def`, `deriv_comp_add_const`, and the lab lemma
`LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ`. -/
theorem logDeriv_gammaFactor_eq {q : ℕ} {χ : DirichletCharacter ℂ q} (κ : ℕ)
    (hκ : (χ.Even ∧ κ = 0) ∨ (χ.Odd ∧ κ = 1)) (w : ℂ) (hw : ∀ m : ℕ, (w + κ) / 2 ≠ -m) :
    logDeriv (DirichletCharacter.gammaFactor χ) w =
      -(Complex.log (Real.pi : ℂ)) / 2 + digamma ((w + κ) / 2) / 2 := by
  rcases hκ with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · have hf : DirichletCharacter.gammaFactor χ = Gammaℝ :=
      funext (DirichletCharacter.Even.gammaFactor_def h)
    rw [hf]
    simp only [Nat.cast_zero, add_zero] at hw ⊢
    exact LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ hw
  · have hf : DirichletCharacter.gammaFactor χ = fun s => Gammaℝ (s + 1) :=
      funext (DirichletCharacter.Odd.gammaFactor_def h)
    rw [hf, logDeriv_apply, deriv_comp_add_const, ← logDeriv_apply]
    push_cast at hw ⊢
    exact LeanLab.Linnik.ExplicitFormula.logDeriv_Gammaℝ hw

/-- Pole avoidance on the two lines: if re w = -1/2 or re w = 3/2 then (w + κ)/2 is not a
nonpositive integer for κ ∈ {0, 1}, since its real part is -1/4, 1/4, 3/4 or 5/4. -/
theorem no_pole (w : ℂ) (κ : ℕ) (hκ : κ = 0 ∨ κ = 1) (hw : w.re = -1 / 2 ∨ w.re = 3 / 2) :
    ∀ m : ℕ, (w + κ) / 2 ≠ -m := by
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.div_re, Complex.add_re, Complex.natCast_re, Complex.neg_re] at hr
  norm_num at hr
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  rcases hκ with rfl | rfl <;> rcases hw with hw | hw <;> rw [hw] at hr <;> norm_num at hr
  all_goals
    first
    | linarith
    | (have h1 : (m : ℝ) < 1 := by linarith
       have h2 : (0 : ℝ) < m := by linarith
       have h3 : m < 1 := by exact_mod_cast h1
       have h4 : 0 < m := by exact_mod_cast h2
       omega)

/-- P0014 page 33, display 4.8: exact statement of the parent leaf
`Prep1121VIPointwiseA.fe_digamma`. -/
theorem fe_digamma {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    (τ : ℝ) (κ : ℕ) (hκ : (χ.Even ∧ κ = 0) ∨ (χ.Odd ∧ κ = 1)) :
    deriv χ.LFunction ((-1 / 2 : ℂ) + τ * I) / χ.LFunction ((-1 / 2 : ℂ) + τ * I) =
      ((Real.log (Real.pi / q) : ℝ) : ℂ)
        - (1 / 2 : ℂ) * (digamma (((-1 / 2 : ℂ) + τ * I + κ) / 2) +
            digamma ((1 - ((-1 / 2 : ℂ) + τ * I) + κ) / 2))
        - logDeriv (χ⁻¹).LFunction (1 - ((-1 / 2 : ℂ) + τ * I)) := by
  have hκ' : κ = 0 ∨ κ = 1 := by rcases hκ with h | h <;> simp [h.2]
  have h1s : (3 / 2 : ℂ) + ((-τ : ℝ) : ℂ) * I = 1 - ((-1 / 2 : ℂ) + τ * I) := by
    push_cast; ring
  have hfe := LeanLab.Linnik.ExplicitFormula.logDeriv_fe_left hχ τ
  rw [h1s] at hfe
  rw [hfe, logDeriv_gammaFactor_eq κ (inv_parity κ hκ) _
      (no_pole _ κ hκ' (Or.inr (by simp; norm_num))),
    logDeriv_gammaFactor_eq κ hκ _ (no_pole _ κ hκ' (Or.inl (by simp)))]
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [Real.log_div Real.pi_pos.ne' hq.ne', Complex.ofReal_sub,
    ← Complex.ofReal_log Real.pi_pos.le]
  ring

end LeanLab.HelfgottMajor.Prep1121DFeDigamma
