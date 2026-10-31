/-
Audit of six leaf statements found false on main, run 20261031T2235Z-16111, architect,
ONE-TIME STATEMENT FIX set by Steve live 2026-10-31. Each `*_old` Prop is the leaf statement
as it stood on main at e8b544e8, word for word, quantified over its variables. Each
`*_old_false` proves its negation by the counterexample named. The repaired leaves live in
Common/DecompJ210.lean and Saouter1998/DecompJ345.lean. Vacuity instances for the repaired
hypotheses are at the end.
AI wrote this Lean code. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Common.FalseLeafAudit20261031

open Real

/-- 1 < log 10, used for the counterexample x = -10. -/
theorem one_lt_log_ten : 1 < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

theorem one_lt_log_neg_ten : 1 < Real.log (-10) := by
  rw [Real.log_neg_eq_log]; exact one_lt_log_ten

/-- DecompJ210 `leaf1_dusart` as on main at e8b544e8. -/
def leaf1_dusart_old : Prop := ∀ x : ℝ, 1 < Real.log x →
    let L := Real.log x; let y := x * (1 + 1 / (40 * L ^ 2)); x ≤ y

/-- DecompJ210 `leaf3_dusart` as on main at e8b544e8. -/
def leaf3_dusart_old : Prop := ∀ x : ℝ, 1 < Real.log x →
    let L := Real.log x; let y := x * (1 + 1 / (40 * L ^ 2));
    0.01 * y / Real.log y ^ 2 ≤ 0.01 * y / L ^ 2

/-- DecompJ210 `leaf4_dusart` as on main at e8b544e8. -/
def leaf4_dusart_old : Prop := ∀ x : ℝ, 1 < Real.log x →
    let L := Real.log x; let y := x * (1 + 1 / (40 * L ^ 2));
    0.01 * x / L ^ 2 + 0.01 * y / L ^ 2 < y - x

theorem leaf1_dusart_old_false : ¬ leaf1_dusart_old := by
  intro h
  have h1 := h (-10) one_lt_log_neg_ten
  simp only at h1
  set L := Real.log (-10)
  have hL : 1 < L := one_lt_log_neg_ten
  have hc : 0 < 1 / (40 * L ^ 2) := by positivity
  nlinarith

theorem leaf4_dusart_old_false : ¬ leaf4_dusart_old := by
  intro h
  have h1 := h (-10) one_lt_log_neg_ten
  simp only at h1
  set L := Real.log (-10)
  have hL : 1 < L := one_lt_log_neg_ten
  have hL2 : 0 < L ^ 2 := by positivity
  have hL21 : 1 < L ^ 2 := by nlinarith
  set c := 1 / (40 * L ^ 2) with hc
  have hcL : c * L ^ 2 = 1 / 40 := by rw [hc]; field_simp
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 / 40 := by
    by_contra hh; push_neg at hh; nlinarith
  have e1 : 0.01 * (-10) / L ^ 2 + 0.01 * (-10 * (1 + c)) / L ^ 2
      = (-0.1 * (2 + c)) / L ^ 2 := by ring
  have e2 : -10 * (1 + c) - -10 = (-0.25) / L ^ 2 := by
    have : c = (1 / 40) / L ^ 2 := by rw [hc, div_div]
    rw [this]; ring
  rw [e1, e2] at h1
  have := (div_lt_div_iff_of_pos_right hL2).mp h1
  linarith

theorem leaf3_dusart_old_false : ¬ leaf3_dusart_old := by
  intro h
  have h1 := h (-10) one_lt_log_neg_ten
  simp only at h1
  set L := Real.log (-10)
  have hL : 1 < L := one_lt_log_neg_ten
  have hL2 : 0 < L ^ 2 := by positivity
  set c := 1 / (40 * L ^ 2) with hc
  have hc0 : 0 < c := by positivity
  set y := -10 * (1 + c) with hy
  have hyneg : y < 0 := by rw [hy]; nlinarith
  have hLy : L < Real.log y := by
    have : Real.log y = Real.log (10 * (1 + c)) := by
      rw [← Real.log_neg_eq_log y]; congr 1; rw [hy]; ring
    rw [this, show L = Real.log 10 from Real.log_neg_eq_log 10]
    exact Real.log_lt_log (by norm_num) (by nlinarith)
  have hLy2 : L ^ 2 < Real.log y ^ 2 := by nlinarith
  have hly2pos : 0 < Real.log y ^ 2 := by linarith
  -- y / log y ^ 2 > y / L ^ 2 since y < 0 and log y ^ 2 > L ^ 2
  have key : 0.01 * y / L ^ 2 < 0.01 * y / Real.log y ^ 2 := by
    rw [div_lt_div_iff₀ hL2 hly2pos]
    nlinarith
  linarith

/-- Saouter1998/DecompJ345 `leaf_F_zero` as on main at e8b544e8. -/
def leaf_F_zero_old : Prop := ∀ R : ℕ,
    ((R * 0 + 1).Prime ↔
      R / (2 * 0) = 0 ∨ ¬ IsSquare (((R % (2 * 0) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * 0) : ℕ) : ℤ)))

/-- Saouter1998/DecompJ345 `leaf_comp_factors` as on main at e8b544e8. -/
def leaf_comp_factors_old : Prop := ∀ F R : ℕ, 0 < F → R * F + 1 < 2 * F ^ 3 →
    (∀ p : ℕ, p.Prime → p ∣ R * F + 1 → ∃ k : ℕ, p = k * F + 1) →
    ¬ (R * F + 1).Prime →
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ R * F + 1 = (a * F + 1) * (b * F + 1)

/-- Saouter1998/DecompJ345 `leaf_comp_cond_from_factors` as on main at e8b544e8. -/
def leaf_comp_cond_from_factors_old : Prop := ∀ F R a b : ℕ, 0 < F →
    R * F + 1 = (a * F + 1) * (b * F + 1) → 1 ≤ a → 1 ≤ b →
    ¬ (R / (2 * F) = 0 ∨ ¬ IsSquare (((R % (2 * F) : ℕ) : ℤ) ^ 2 - 8 * ((R / (2 * F) : ℕ) : ℤ)))

/-- Counterexample R = 0: N = 1 is not prime, yet R / 0 = 0. False at every R in fact. -/
theorem leaf_F_zero_old_false : ¬ leaf_F_zero_old := by
  intro h
  have := (h 0).mpr (Or.inl (by simp))
  norm_num at this

/-- Counterexample R = 0, F = 1: N = 1 has no prime factor and no factorization. -/
theorem leaf_comp_factors_old_false : ¬ leaf_comp_factors_old := by
  intro h
  obtain ⟨a, b, ha, hb, hab⟩ := h 1 0 (by norm_num) (by norm_num)
    (by intro p hp hd; simp at hd; exact absurd hd hp.one_lt.ne') (by norm_num)
  nlinarith

/-- Counterexample R = 5, F = 3, a = b = 1: 16 = 4 · 4 and 5 / 6 = 0. -/
theorem leaf_comp_cond_from_factors_old_false : ¬ leaf_comp_cond_from_factors_old := by
  intro h
  exact h 3 5 1 1 (by norm_num) (by norm_num) le_rfl le_rfl (Or.inl (by norm_num))

/-- Vacuity, repaired Dusart leaves: x = 7713133853 meets 0 < x and 1 < log x. -/
theorem dusart_hyps_hold : (0 : ℝ) < 7713133853 ∧ 1 < Real.log 7713133853 := by
  refine ⟨by norm_num, ?_⟩
  exact lt_of_lt_of_le one_lt_log_ten (Real.log_le_log (by norm_num) (by norm_num))

/-- Vacuity, repaired Saouter leaves: F = 2, R = 7, a = 1, b = 2, N = 15 = 3 · 5 meets every
hypothesis of the repaired `leaf_comp_factors` and `leaf_comp_cond_from_factors`, and the
repaired conclusion holds there: 7 / 4 = 1, 7 % 4 = 3, 9 - 8 = 1 = 1². -/
theorem saouter_hyps_hold :
    0 < 2 ∧ 0 < 7 ∧ 7 * 2 + 1 < 2 * 2 ^ 3 ∧ Even 2 ∧ Nat.Coprime 7 2 ∧
    7 * 2 + 1 = (1 * 2 + 1) * (2 * 2 + 1) ∧ ¬ (7 * 2 + 1).Prime ∧
    ¬ ((7 : ℕ) / (2 * 2) = 0 ∨
      ¬ IsSquare ((((7 : ℕ) % (2 * 2) : ℕ) : ℤ) ^ 2 - 8 * (((7 : ℕ) / (2 * 2) : ℕ) : ℤ))) := by
  refine ⟨by norm_num, by norm_num, by norm_num, even_two, by norm_num, by norm_num,
    by norm_num, ?_⟩
  push_neg
  refine ⟨by norm_num, ⟨1, by norm_num⟩⟩

end LeanLab.Common.FalseLeafAudit20261031
