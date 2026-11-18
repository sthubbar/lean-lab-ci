import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
Trigonometric closed forms for the Selberg-type cosine majorant: arithmetic progression
cosine sums, the Fejér kernel closed form, the conjugate kernel closed form, and the
grid partition of unity. AI wrote this Lean code.
-/

namespace LeanLab.ExceptionalSet.Selberg524

open Real Finset

theorem cos_ap_sum524 (a d : ℝ) (n : ℕ) :
    (∑ i ∈ range n, cos (a + (i : ℝ) * d)) * (2 * sin (d / 2)) =
      sin (a + ((n : ℝ) - 1 / 2) * d) - sin (a - d / 2) := by
  induction n with
  | zero =>
    have h : a + (((0 : ℕ) : ℝ) - 1 / 2) * d = a - d / 2 := by push_cast; ring
    rw [h]; simp
  | succ n ih =>
    have h1 : a + (((n + 1 : ℕ) : ℝ) - 1 / 2) * d = (a + (n : ℝ) * d) + d / 2 := by
      push_cast; ring
    have h2 : a + ((n : ℝ) - 1 / 2) * d = (a + (n : ℝ) * d) - d / 2 := by ring
    rw [sum_range_succ, add_mul, ih, h1, h2, sin_add, sin_sub]
    ring

private lemma sin_mul_sin_aux524 (B P : ℝ) :
    sin (B + P) * sin (P - B) = sin P ^ 2 - sin B ^ 2 := by
  have hB := sin_sq_add_cos_sq B
  have hP := sin_sq_add_cos_sq P
  rw [sin_add, sin_sub]
  linear_combination (sin P) ^ 2 * hB - (sin B) ^ 2 * hP

private lemma conj_step_aux524 (B P : ℝ) :
    sin (P - B) * ((sin (2 * B) + sin (2 * P)) / 2) =
      (sin P ^ 2 - sin B ^ 2) * cos (P - B) := by
  have hB := sin_sq_add_cos_sq B
  have hP := sin_sq_add_cos_sq P
  rw [sin_two_mul, sin_two_mul, sin_sub, cos_sub]
  linear_combination sin P * sin B * hB - sin P * sin B * hP

private lemma dirichlet_aux524 (H : ℕ) (u : ℝ) :
    sin u * (1 + 2 * ∑ h ∈ Icc 1 H, cos (2 * ((h : ℝ) * u))) =
      sin ((2 * (H : ℝ) + 1) * u) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h1 : (2 * ((H + 1 : ℕ) : ℝ) + 1) * u = 2 * (((H + 1 : ℕ) : ℝ) * u) + u := by ring
    have h2 : (2 * (H : ℝ) + 1) * u = 2 * (((H + 1 : ℕ) : ℝ) * u) - u := by
      push_cast; ring
    rw [h2] at ih
    rw [h1, sin_add]
    rw [sin_sub] at ih
    linear_combination ih

private lemma fejer_aux524 (H : ℕ) (u : ℝ) :
    sin u ^ 2 * (((H : ℝ) + 1) +
        2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * ((h : ℝ) * u))) =
      sin (((H : ℝ) + 1) * u) ^ 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    have key : ∑ h ∈ Icc 1 (H + 1),
          ((((H + 1 : ℕ) : ℝ) + 1) - (h : ℝ)) * cos (2 * ((h : ℝ) * u)) =
        ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * ((h : ℝ) * u)) +
          ∑ h ∈ Icc 1 (H + 1), cos (2 * ((h : ℝ) * u)) := by
      have e : ∀ h ∈ Icc 1 (H + 1),
          ((((H + 1 : ℕ) : ℝ) + 1) - (h : ℝ)) * cos (2 * ((h : ℝ) * u)) =
            (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * ((h : ℝ) * u)) +
              cos (2 * ((h : ℝ) * u)) := by
        intro h _; push_cast; ring
      rw [sum_congr rfl e, sum_add_distrib]
      congr 1
      rw [sum_Icc_succ_top (by omega)]
      push_cast; ring
    have D := dirichlet_aux524 (H + 1) u
    have hP := sin_mul_sin_aux524 (((H : ℝ) + 1) * u) ((((H + 1 : ℕ) : ℝ) + 1) * u)
    rw [show ((H : ℝ) + 1) * u + (((H + 1 : ℕ) : ℝ) + 1) * u
          = (2 * ((H + 1 : ℕ) : ℝ) + 1) * u by push_cast; ring,
      show (((H + 1 : ℕ) : ℝ) + 1) * u - ((H : ℝ) + 1) * u = u by push_cast; ring] at hP
    rw [key]
    have c : (((H + 1 : ℕ) : ℝ) + 1) = ((H : ℝ) + 1) + 1 := by push_cast; ring
    linear_combination ih + sin u * D + hP + sin u ^ 2 * c

private lemma conj_aux524 (H : ℕ) (u : ℝ) :
    sin u * (∑ h ∈ Icc 1 H, sin (2 * ((h : ℝ) * u)) + sin (2 * (((H : ℝ) + 1) * u)) / 2) =
      sin (((H : ℝ) + 1) * u) ^ 2 * cos u := by
  induction H with
  | zero =>
    simp only [zero_lt_one, Icc_eq_empty_of_lt, sum_empty, Nat.cast_zero,
      zero_add, one_mul]
    rw [sin_two_mul]; ring
  | succ H ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hc := conj_step_aux524 (((H : ℝ) + 1) * u) ((((H + 1 : ℕ) : ℝ) + 1) * u)
    rw [show (((H + 1 : ℕ) : ℝ) + 1) * u - ((H : ℝ) + 1) * u = u by push_cast; ring] at hc
    have e : (((H + 1 : ℕ) : ℝ)) * u = ((H : ℝ) + 1) * u := by push_cast; ring
    rw [e]
    linear_combination ih + hc

theorem fejer_closed524 (H : ℕ) (x : ℝ) :
    sin (π * x) ^ 2 * (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * ((h : ℝ) * x))) =
      sin (π * (((H : ℝ) + 1) * x)) ^ 2 := by
  have e1 : ∀ t : ℝ, 2 * π * (t * x) = 2 * (t * (π * x)) := fun t => by ring
  have e2 : π * (((H : ℝ) + 1) * x) = ((H : ℝ) + 1) * (π * x) := by ring
  rw [e2]
  simp_rw [e1]
  exact fejer_aux524 H (π * x)

theorem conj_closed524 (H : ℕ) (x : ℝ) :
    sin (π * x) * (∑ h ∈ Icc 1 H, sin (2 * π * ((h : ℝ) * x)) + sin (2 * π * (((H : ℝ) + 1) * x)) / 2) =
      sin (π * (((H : ℝ) + 1) * x)) ^ 2 * cos (π * x) := by
  have e1 : ∀ t : ℝ, 2 * π * (t * x) = 2 * (t * (π * x)) := fun t => by ring
  have e2 : π * (((H : ℝ) + 1) * x) = ((H : ℝ) + 1) * (π * x) := by ring
  rw [e2]
  simp_rw [e1]
  exact conj_aux524 H (π * x)

theorem grid_cos_sum_zero524 (H h : ℕ) (hh1 : 1 ≤ h) (hhH : h ≤ H) (a : ℝ) :
    ∑ i ∈ range (H + 1), cos (a + (i : ℝ) * (2 * π * (h : ℝ) / ((H : ℝ) + 1))) = 0 := by
  have hN : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hh1' : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
  have hhH' : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hhH
  have key := cos_ap_sum524 a (2 * π * (h : ℝ) / ((H : ℝ) + 1)) (H + 1)
  have e : a + (((H + 1 : ℕ) : ℝ) - 1 / 2) * (2 * π * (h : ℝ) / ((H : ℝ) + 1)) =
      (a - 2 * π * (h : ℝ) / ((H : ℝ) + 1) / 2) + (h : ℝ) * (2 * π) := by
    push_cast; field_simp; ring
  rw [e, sin_add_nat_mul_two_pi, sub_self] at key
  have hpos : 0 < sin (2 * π * (h : ℝ) / ((H : ℝ) + 1) / 2) := by
    apply sin_pos_of_pos_of_lt_pi
    · have := pi_pos; positivity
    · have e3 : 2 * π * (h : ℝ) / ((H : ℝ) + 1) / 2 = π * ((h : ℝ) / ((H : ℝ) + 1)) := by
        field_simp
      rw [e3]
      have hlt : (h : ℝ) / ((H : ℝ) + 1) < 1 := by
        rw [div_lt_one hN]; linarith
      nlinarith [pi_pos]
  rcases mul_eq_zero.mp key with h0 | h0
  · exact h0
  · exfalso
    have : sin (2 * π * (h : ℝ) / ((H : ℝ) + 1) / 2) = 0 := by linarith
    linarith

theorem fejer_grid_sum524 (H : ℕ) (y : ℝ) :
    ∑ i ∈ range (H + 1), (((H : ℝ) + 1) + 2 * ∑ h ∈ Icc 1 H, (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * ((h : ℝ) * (y - (i : ℝ) / ((H : ℝ) + 1))))) =
      ((H : ℝ) + 1) ^ 2 := by
  have hz : ∀ h ∈ Icc 1 H, ∑ i ∈ range (H + 1),
      (((H : ℝ) + 1) - (h : ℝ)) * cos (2 * π * ((h : ℝ) * (y - (i : ℝ) / ((H : ℝ) + 1)))) = 0 := by
    intro h hh
    rw [mem_Icc] at hh
    rw [← mul_sum]
    have e : ∑ i ∈ range (H + 1), cos (2 * π * ((h : ℝ) * (y - (i : ℝ) / ((H : ℝ) + 1)))) =
        ∑ i ∈ range (H + 1),
          cos (-(2 * π * ((h : ℝ) * y)) + (i : ℝ) * (2 * π * (h : ℝ) / ((H : ℝ) + 1))) := by
      refine sum_congr rfl fun i _ => ?_
      rw [← cos_neg]; congr 1; ring
    rw [e, grid_cos_sum_zero524 H h hh.1 hh.2, mul_zero]
  rw [sum_add_distrib, ← mul_sum, sum_comm, sum_eq_zero hz]
  simp only [sum_const, card_range, nsmul_eq_mul]
  push_cast; ring

end LeanLab.ExceptionalSet.Selberg524
