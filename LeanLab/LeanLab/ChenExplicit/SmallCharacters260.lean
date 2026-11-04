/-
AI wrote the Lean code. Codex task260, 2026-11-04.
Yamada, arXiv 1306.5322v4, page 2 Theorem 1.1 eq 1 and page 21 Table 5.
This is the nonexceptional specialization at alpha1 = 10, alpha2 = 8,
Y0 = 11.7 and C = 0.000012. The table prints the scaled label 117. The stronger zero exclusion is explicit.
It does not choose the exceptional modulus needed by Lemma 7.2.
Binary Goldbach is OPEN.
-/
import LeanLab.PNTPort.BV.Characters

open Finset Real
open scoped Classical

noncomputable section
namespace LeanLab.ChenExplicit.SmallCharacters260

/-- LEAF. Cited. Yamada 1306.5322v4 page 2 Theorem 1.1 eq 1,
with Table 5 row 10, 8, 117, 0.000012 and no exceptional zero.
The author linked prim0003pari.txt uses exp of the table label divided by ten.
Thus the label 117 means log log X0 equal to 11.7, as cited in the Chen paper.
The real zero exclusion is stronger than nonexceptionality. -/
theorem yamada_nonexceptional_psi_scaled (q : ℕ) [NeZero q] (x : ℝ)
    (hx : exp (exp (117 / 10)) ≤ x) (hq : (q : ℝ) ≤ log x ^ 10)
    (hfree : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      1 / 2 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    -1 + (1 / x) * ∑ χ : DirichletCharacter ℂ q, ‖LeanLab.PNTPort.BV.psiChi x χ‖ <
      (12 / 1000000 : ℝ) / log x ^ 8 := by
  sorry

/-- The conservative unscaled cutoff follows from the scaled paper input.
CONDITIONAL ON yamada_nonexceptional_psi_scaled. -/
theorem yamada_nonexceptional_psi (q : ℕ) [NeZero q] (x : ℝ)
    (hx : exp (exp 117) ≤ x) (hq : (q : ℝ) ≤ log x ^ 10)
    (hfree : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      1 / 2 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) :
    -1 + (1 / x) * ∑ χ : DirichletCharacter ℂ q, ‖LeanLab.PNTPort.BV.psiChi x χ‖ <
      (12 / 1000000 : ℝ) / log x ^ 8 := by
  exact yamada_nonexceptional_psi_scaled q x
    ((exp_le_exp.mpr (exp_le_exp.mpr (by norm_num : (117 : ℝ) / 10 ≤ 117))).trans hx) hq hfree

/-- A principal character lower bound extracts the nonprincipal character sum.
CONDITIONAL ON yamada_nonexceptional_psi_scaled and the displayed principal lower bound. -/
theorem nonprincipal_psi_scaled (q : ℕ) [NeZero q] (x δ : ℝ)
    (hx : exp (exp (117 / 10)) ≤ x) (hq : (q : ℝ) ≤ log x ^ 10)
    (hfree : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      1 / 2 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0)
    (hprincipal : x - δ ≤ ‖LeanLab.PNTPort.BV.psiChi x (1 : DirichletCharacter ℂ q)‖) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖LeanLab.PNTPort.BV.psiChi x χ‖ < (12 / 1000000 : ℝ) * x / log x ^ 8 + δ := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have h := yamada_nonexceptional_psi_scaled q x hx hq hfree
  have he := add_sum_erase (univ : Finset (DirichletCharacter ℂ q))
    (fun χ => ‖LeanLab.PNTPort.BV.psiChi x χ‖) (mem_univ (1 : DirichletCharacter ℂ q))
  have hn : (∑ χ : DirichletCharacter ℂ q, ‖LeanLab.PNTPort.BV.psiChi x χ‖) / x <
      1 + (12 / 1000000 : ℝ) / log x ^ 8 := by
    rw [one_div_mul_eq_div] at h
    linarith
  have ht := (div_lt_iff₀ hx0).mp hn
  have hid : (1 + (12 / 1000000 : ℝ) / log x ^ 8) * x =
      x + (12 / 1000000 : ℝ) * x / log x ^ 8 := by ring
  rw [hid] at ht
  linarith

/-- A principal character lower bound extracts the nonprincipal character sum.
CONDITIONAL ON yamada_nonexceptional_psi and the displayed principal lower bound. -/
theorem nonprincipal_psi_of_principal_lower (q : ℕ) [NeZero q] (x δ : ℝ)
    (hx : exp (exp 117) ≤ x) (hq : (q : ℝ) ≤ log x ^ 10)
    (hfree : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      1 / 2 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0)
    (hprincipal : x - δ ≤ ‖LeanLab.PNTPort.BV.psiChi x (1 : DirichletCharacter ℂ q)‖) :
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      ‖LeanLab.PNTPort.BV.psiChi x χ‖ < (12 / 1000000 : ℝ) * x / log x ^ 8 + δ := by
  exact nonprincipal_psi_scaled q x δ
    ((exp_le_exp.mpr (exp_le_exp.mpr (by norm_num : (117 : ℝ) / 10 ≤ 117))).trans hx)
    hq hfree hprincipal

/-- The triangle bound XY exceeds the target bilinear error budget.
This records the loss from ignoring character cancellation in Yamada page 23 eq 99. -/
theorem triangle_budget_too_large (X Y : ℝ) (hX : 0 < X) (hY : exp 1 ≤ Y) :
    exp (-144) * X * Y / log Y ^ 4 < X * Y := by
  have hY0 : 0 < Y := (exp_pos _).trans_le hY
  have hlog : 1 ≤ log Y := by simpa using log_le_log (exp_pos 1) hY
  have he : exp (-144 : ℝ) < 1 := by rw [exp_lt_one_iff]; norm_num
  have hl4 : 1 ≤ log Y ^ 4 := one_le_pow₀ hlog
  have hb : exp (-144) * X * Y / log Y ^ 4 ≤ exp (-144) * X * Y :=
    div_le_self (by positivity) hl4
  exact hb.trans_lt (by nlinarith [mul_pos hX hY0])

/-- Reading the scaled integer label 117 as an unscaled cutoff loses the Chen range.
The author linked computation resolves the scaling. This compares the two readings. -/
theorem small_character_cutoff_gap : exp (exp 37 / 8) < exp (exp 117) := by
  apply exp_lt_exp.mpr
  have h := exp_lt_exp.mpr (by norm_num : (37 : ℝ) < 117)
  linarith [exp_pos (37 : ℝ)]

/-- The correctly scaled character cutoff lies below the Chen prime endpoint. -/
theorem chen_scale_above_character_cutoff :
    exp (exp (117 / 10 : ℝ)) < exp (exp 36 / 8) := by
  apply exp_lt_exp.mpr
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  have he : (8 : ℝ) < exp (243 / 10) := by linarith [add_one_le_exp (243 / 10 : ℝ)]
  calc
    exp (117 / 10) * 8 < exp (117 / 10) * exp (243 / 10) :=
      mul_lt_mul_of_pos_left he (exp_pos _)
    _ = exp 36 := by rw [← exp_add]; norm_num

end LeanLab.ChenExplicit.SmallCharacters260
