import Mathlib
import LeanLab.Pintz2018.Section9

/-!
# Pintz 2018, certificate targets for the paper's own numerics

Two SEALED TARGET statements recording numerical claims of arXiv 1804.09084v2:
Lemma 5, display (6.25) p. 29, which is Condition 2 (4.26)-(4.27) p. 15 for `G` of (4.19) p. 14
with `A0 = 13`, `B0 = 1.25`; and the Case 1 extremal bound of Section 9, displays (9.7)-(9.13)
pp. 39-40, with `λ0 = 0.68`, `x = 0.7`, `ϕ = 1/3`, `Λ0 = 1.311`.
These are TARGET certificates of the paper's numerics, not original results.
AI wrote the Lean code.
-/

namespace LeanLab.Pintz2018

open Finset

/-- `g(u) = (2-u)^3 (4+6u+u^2)/30`, display (4.18) p. 14. -/
noncomputable def gP (u : ℝ) : ℝ := (2 - u) ^ 3 * (4 + 6 * u + u ^ 2) / 30

/-- `G(z) = ∫_0^2 e^{-zu} g(u) du`, display (4.19) p. 14, complex argument. -/
noncomputable def Gc (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..2, Complex.exp (-z * u) * (gP u : ℂ)

/-- `G` of (4.19) on the real line, as a real integral. -/
noncomputable def GR (y : ℝ) : ℝ := ∫ u in (0 : ℝ)..2, Real.exp (-y * u) * gP u

/-- Case 1 constants of (9.7)-(9.9) p. 39-40: `G(-λ0/x)` with `λ0 = 0.68`, `x = 0.7`. -/
noncomputable def Gm1 : ℝ := GR (-(0.68 / 0.7))
/-- `G((Λ0-λ0)/x)` with `Λ0 = 1.311`. -/
noncomputable def GL1 : ℝ := GR ((1.311 - 0.68) / 0.7)
/-- `ξ = f(0)ϕ/(2F(-λ0))`, (4.31) p. 16, with `f(0) = 16x/15` (4.25) and `ϕ = 1/3` p. 39. -/
noncomputable def xi1 : ℝ := (16 * 0.7 / 15) * (1 / 3) / (2 * Gm1)
/-- `ψ = F(Λ0-λ0)/F(-λ0)`, (4.31) p. 16. -/
noncomputable def psi1 : ℝ := GL1 / Gm1
/-- `Δ = ψ - ξ`, (4.31) p. 16. -/
noncomputable def Delta1 : ℝ := psi1 - xi1
/-- `D0 = F(-λ0)(1-ξ)/(2Δ)`, the bound on `∑ (G((λj-λ0)/x) - G((Λ0-λ0)/x))` obtained from
Theorem J (4.36) p. 17 as in (9.9) p. 40; the paper prints `D0 ≤ 2.4438`. -/
noncomputable def D01 : ℝ := Gm1 * (1 - xi1) / (2 * Delta1)

/-- SEALED TARGET certificate of Condition 2 for `G`, Lemma 5, arXiv 1804.09084v2 p.29
display 6.25; numerically tested min margin 0 at the corner a = b = 0 only, slopes at least
0.0075 in b and 0.024 in a on the box pi/2 < |t| < 8 -/
theorem G_condition2 (a b t : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 13) (hb0 : 0 ≤ b) (hb : b ≤ 5 / 4) :
    (Gc ((-b : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-b : ℂ)).re
      ≤ (Gc ((a : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (a : ℂ)).re := by
  sorry

/-- Vacuity instance for `G_condition2`: the hypotheses hold at `a = b = 0`, and there the
inequality is an equality. -/
theorem G_condition2_vacuity (t : ℝ) :
    (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 13 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 5 / 4 ∧
    (Gc ((-(0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / (Gc (-(0 : ℝ) : ℂ)).re
      ≤ (Gc (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re / (Gc ((0 : ℝ) : ℂ)).re := by
  refine ⟨le_rfl, by norm_num, le_rfl, by norm_num, ?_⟩
  simp

/-- SEALED TARGET certificate of the Case 1 bound `S' < 0.612`, arXiv 1804.09084v2 p.40
display 9.13, with the constraints of (9.11) from Theorems E and F; numerically tested
maximum 0.6105899 by the Theorem K greedy and by direct optimisation over N up to 20 -/
theorem pintz_section9_certificate {ι : Type*} (s : Finset ι) (l : ι → ℝ)
    (hlo : ∀ j ∈ s, 0.68 ≤ l j) (hhi : ∀ j ∈ s, l j ≤ 1.311)
    (htwo : (s.filter fun j => l j < 0.702).card ≤ 2)
    (hD : ∑ j ∈ s, (GR ((l j - 0.68) / 0.7) - GL1) ≤ D01) :
    ∑ j ∈ s, (E (l j) - E 1.311) < 0.612 := by
  sorry

/-! ### Vacuity for `pintz_section9_certificate` -/

theorem gP_nonneg (u : ℝ) (h0 : 0 ≤ u) (h2 : u ≤ 2) : 0 ≤ gP u := by
  unfold gP
  have : 0 ≤ 2 - u := by linarith
  positivity

theorem gP_cont : Continuous gP := by
  unfold gP; fun_prop

attribute [fun_prop] gP_cont

theorem gP_integral : ∫ u in (0 : ℝ)..2, gP u = 8 / 9 := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) 2,
      HasDerivAt (fun u : ℝ => (32 * u - 40 / 3 * u ^ 3 + 5 * u ^ 4 - 1 / 6 * u ^ 6) / 30)
        (gP x) x := by
    intro x _
    have h := (((((hasDerivAt_id x).const_mul 32).sub ((hasDerivAt_pow 3 x).const_mul (40 / 3))).add
      ((hasDerivAt_pow 4 x).const_mul 5)).sub ((hasDerivAt_pow 6 x).const_mul (1 / 6))).div_const 30
    convert h using 1
    · funext y; simp
    · unfold gP; simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (gP_cont.intervalIntegrable _ _)]
  norm_num

theorem GR_lower_neg (y : ℝ) (hy : y ≤ 0) : 8 / 9 ≤ GR y := by
  rw [← gP_integral]
  unfold GR
  apply intervalIntegral.integral_mono_on (by norm_num) (gP_cont.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u => Real.exp (-y * u) * gP u).intervalIntegrable _ _)
  intro u hu
  have h1 : 1 ≤ Real.exp (-y * u) := Real.one_le_exp (by nlinarith [hu.1])
  nlinarith [gP_nonneg u hu.1 hu.2]

theorem GR_lower_pos (y : ℝ) (hy : 0 ≤ y) : Real.exp (-(2 * y)) * (8 / 9) ≤ GR y := by
  rw [← gP_integral, ← intervalIntegral.integral_const_mul]
  unfold GR
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous fun u => Real.exp (-(2 * y)) * gP u).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u => Real.exp (-y * u) * gP u).intervalIntegrable _ _)
  intro u hu
  have h1 : Real.exp (-(2 * y)) ≤ Real.exp (-y * u) :=
    Real.exp_le_exp.mpr (by nlinarith [hu.2])
  exact mul_le_mul_of_nonneg_right h1 (gP_nonneg u hu.1 hu.2)

theorem D01_nonneg : 0 ≤ D01 := by
  have hm : 8 / 9 ≤ Gm1 := GR_lower_neg _ (by norm_num)
  have hL0 := GR_lower_pos ((1.311 - 0.68) / 0.7) (by norm_num)
  have he := expneg_lower (2 * ((1.311 - 0.68) / 0.7)) (by norm_num) (by norm_num)
  simp only [T15, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at he
  norm_num at he hL0
  have hL : (16 * 0.7 / 15) * (1 / 3) / 2 ≤ GL1 := by
    unfold GL1; norm_num; nlinarith
  have hmpos : 0 < Gm1 := by linarith
  have hxi : xi1 ≤ 1 := by
    unfold xi1
    rw [div_le_one (by positivity)]
    norm_num; linarith
  have hDel : 0 ≤ Delta1 := by
    unfold Delta1 psi1 xi1
    rw [sub_nonneg, div_le_div_iff₀ (by positivity) hmpos]
    norm_num at hL ⊢; nlinarith
  unfold D01
  apply div_nonneg _ (by positivity)
  exact mul_nonneg hmpos.le (by linarith)

/-- Vacuity instance for `pintz_section9_certificate`: the one-point family `λ1 = Λ0 = 1.311`
satisfies every hypothesis. -/
theorem pintz_section9_certificate_vacuity :
    (∀ j ∈ ({0} : Finset ℕ), (0.68 : ℝ) ≤ (fun _ => (1.311 : ℝ)) j) ∧
    (∀ j ∈ ({0} : Finset ℕ), (fun _ => (1.311 : ℝ)) j ≤ 1.311) ∧
    (({0} : Finset ℕ).filter fun j => (fun _ => (1.311 : ℝ)) j < 0.702).card ≤ 2 ∧
    ∑ j ∈ ({0} : Finset ℕ), (GR (((fun _ => (1.311 : ℝ)) j - 0.68) / 0.7) - GL1) ≤ D01 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
  · simp only [Finset.sum_singleton]
    unfold GL1
    simpa using D01_nonneg

end LeanLab.Pintz2018
