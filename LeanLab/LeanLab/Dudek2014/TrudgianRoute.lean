/-
P0100, A. W. Dudek, On the Riemann hypothesis and the difference between primes, arXiv 1402.6417v2.
PC run 20261020T2203Z-17931, unit U-1297, T1, 2026-10-20.

The paper's own `N(T)` input, page 5, equation (6), quoted from Corollary 1 of Trudgian,
Math. Comp. 81 (2012) 1053-1061: `N(T) < T log T / (2π)` for all `T > 15`, where `N(T)` counts the
zeros `ρ = β + iγ` with `0 < β < 1` and `0 < γ < T`. Page 8 uses it again, with Ingham's Theorem A,
to estimate the sum over `0 < γ < αx/h` in Section 2.3.

The lab conditions Theorems 1 and 3 and the abstract's `c = 3 + ε` on `SigmaH.HSWN70 gZ` instead,
the Hasanalizade-Shen-Wong bound, arXiv 2107.06506 Corollary 1.2. This file compares the two.

* `TrudgianEq6 γ`: equation (6) in the lab's count form, ordinates of both signs, `|γ| ≤ T`:
  at most `T log T / π`, which is `2 · T log T / (2π)`, for `T > 15`.
* `hsw_imp_eq6` PROVED unconditional: `HSWN70 γ` implies (6) for every `T ≥ 70`, for any family.
* `eq6_not_imp_hsw` PROVED unconditional: (6) for all `T > 15` does NOT imply `HSWN70`; eighty
  ordinates at height `70` satisfy (6) and break the first clause of `HSWN70` at `T = 70`.
  (6) is an upper bound only, while `HSWN70` carries the main term `T/(2π) log(T/(2πe))` with an
  explicit `O(log T)` error, which is needed for the block counts `T < |γ| ≤ t` of Section 2.3.
* `hsw_empty`, vacuity: `HSWN70` holds for the empty family, so the hypothesis is satisfiable.

So the honest direction is HSW implies the paper's (6), on `T ≥ 70`. The lab's input is logically
stronger than (6) alone; it is a published theorem, and its two sided form is what the paper's
page 8 step, (6) plus Ingham's Theorem A, needs in substance. AI wrote this Lean code.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Dudek2014.SigmaHSW
import LeanLab.PNTPort.ExplicitPsi1.DudekTrudgian

namespace LeanLab.Dudek2014.TrudgianRoute
open Real
open LeanLab.ChirreHagen2025.Lemma26H (Mt Rt)
open LeanLab.Dudek2014.SigmaH (HSWN70 Mt_eq Rt_le Rt_nonneg)
open LeanLab.Dudek2014.SigmaT (log_ge_four log_70)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ)

variable {ι : Type*}

/-- Dudek 2014 page 5 equation (6), Trudgian 2012 Corollary 1, `N(T) < T log T / (2π)` for
`T > 15`, as counts over any finite set of the ordinates, both signs, `|γ| ≤ T`. -/
def TrudgianEq6 (γ : ι → ℝ) : Prop :=
  ∀ T : ℝ, 15 < T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ T * log T / π

/-- Equation (6) restricted to `T ≥ T₀`. -/
def TrudgianEq6From (T₀ : ℝ) (γ : ι → ℝ) : Prop :=
  ∀ T : ℝ, T₀ ≤ T → ∀ s : Finset ι,
    ((s.filter (fun i => |γ i| ≤ T)).card : ℝ) ≤ T * log T / π

lemma eq6From_of_eq6 {γ : ι → ℝ} (h : TrudgianEq6 γ) : TrudgianEq6From 70 γ :=
  fun T hT s => h T (by linarith) s

lemma one_le_log_two_pi : 1 ≤ log (2 * π) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have := Real.pi_gt_d2
  linarith

lemma log_two_pi_le_three : log (2 * π) ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h1 := Real.exp_one_gt_d9
  have e : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (2.7182818283 : ℝ) ^ 3 ≤ exp 1 ^ 3 := by gcongr
  have := Real.pi_lt_d2
  nlinarith

/-- The HSW upper count is below Trudgian's (6) from `T = 70` on. -/
lemma two_MR_le {T : ℝ} (hT : 70 ≤ T) : 2 * (Mt T + Rt T) ≤ T * log T / π := by
  have hT0 : 0 < T := by linarith
  rw [Mt_eq hT0]
  have hR := Rt_le hT
  have hl := SigmaT.log_le_half hT0
  have hl2 := one_le_log_two_pi
  have hpi := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hpos : 0 < π := Real.pi_pos
  have e : 2 * (T * (log T - log (2 * π) - 1) / (2 * π) + 7 / 8 + Rt T)
      = T * log T / π - T * (log (2 * π) + 1) / π + 7 / 4 + 2 * Rt T := by
    field_simp; ring
  rw [e]
  have h2 : 2 * T / π ≤ T * (log (2 * π) + 1) / π := by
    apply div_le_div_of_nonneg_right _ hpos.le; nlinarith
  have h3 : 0.63 * T ≤ 2 * T / π := by
    rw [le_div_iff₀ hpos]; nlinarith
  linarith

/-- PROVED unconditional: for any family of ordinates, `HSWN70` implies the paper's (6) for
every `T ≥ 70`. -/
theorem hsw_imp_eq6 {γ : ι → ℝ} (h : HSWN70 γ) : TrudgianEq6From 70 γ :=
  fun T hT s => (h.1 T hT s).trans (two_MR_le hT)

/-- For the true zeros: (6) for `T ≥ 70` holds CONDITIONAL ON `HSWN70 gZ`, the lab's input. -/
theorem eq6_gZ_of_hsw (h : HSWN70 gZ) : TrudgianEq6From 70 gZ := hsw_imp_eq6 h

/-- The model family: eighty ordinates, all at height `70`. -/
def bunch : Fin 80 → ℝ := fun _ => 70

lemma bunch_eq6 : TrudgianEq6 bunch := by
  intro T hT s
  have hpos : 0 < π := Real.pi_pos
  by_cases h70 : 70 ≤ T
  · have hc : ((s.filter (fun i => |bunch i| ≤ T)).card : ℝ) ≤ 80 := by
      have := (Finset.card_filter_le s (fun i => |bunch i| ≤ T)).trans (Finset.card_le_univ s)
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hl := log_ge_four h70
    have hpi2 := Real.pi_lt_d2
    rw [le_div_iff₀ hpos]
    nlinarith
  · have he : s.filter (fun i => |bunch i| ≤ T) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i _
      simp only [bunch]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 70)]
      linarith
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : 0 < log T := Real.log_pos (by linarith)
    positivity

lemma MR_70_lt : 2 * (Mt 70 + Rt 70) < 80 := by
  rw [Mt_eq (by norm_num)]
  have hR := Rt_le (le_refl (70 : ℝ))
  have h70 := log_70
  have hl2 := one_le_log_two_pi
  have hpi := Real.pi_gt_d2
  have hpos : 0 < π := Real.pi_pos
  have h1 : 70 * (log 70 - log (2 * π) - 1) / (2 * π) ≤ 70 * 2.3 / (2 * π) := by
    apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
  have h2 : 70 * 2.3 / (2 * π) ≤ 70 * 2.3 / (2 * 3.14) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at h1 h2 hR ⊢
  linarith

/-- PROVED unconditional: equation (6) does not imply `HSWN70`, even in the abstract count form. -/
theorem eq6_not_imp_hsw : ¬ (∀ γ : Fin 80 → ℝ, TrudgianEq6 γ → HSWN70 γ) := by
  intro H
  have h := (H bunch bunch_eq6).1 70 (le_refl _) Finset.univ
  have hc : (Finset.univ.filter (fun i => |bunch i| ≤ 70)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    simp [bunch]
  rw [hc, Finset.card_univ, Fintype.card_fin] at h
  have := MR_70_lt
  push_cast at h
  linarith

lemma Mt_nonneg_mono {T t : ℝ} (hT : 70 ≤ T) (hTt : T ≤ t) : 0 ≤ Mt T ∧ Mt T ≤ Mt t := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  rw [Mt_eq hT0, Mt_eq ht0]
  have hl := log_ge_four hT
  have hlt : log T ≤ log t := Real.log_le_log hT0 hTt
  have h3 := log_two_pi_le_three
  have hpos : 0 < 2 * π := by positivity
  have ha : 0 ≤ log T - log (2 * π) - 1 := by linarith
  constructor
  · have : 0 ≤ T * (log T - log (2 * π) - 1) / (2 * π) := by positivity
    linarith
  · have : T * (log T - log (2 * π) - 1) ≤ t * (log t - log (2 * π) - 1) := by
      apply mul_le_mul hTt (by linarith) ha ht0.le
    have := div_le_div_of_nonneg_right this hpos.le
    linarith

/-- Vacuity check: `HSWN70` is satisfiable, it holds for the empty family. -/
theorem hsw_empty : HSWN70 (Empty.elim : Empty → ℝ) := by
  constructor
  · intro T hT s
    rw [Finset.eq_empty_of_isEmpty s]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    have := (Mt_nonneg_mono hT le_rfl).1
    have := Rt_nonneg hT
    linarith
  · intro T t hT hTt s
    rw [Finset.eq_empty_of_isEmpty s]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    have := (Mt_nonneg_mono hT hTt).2
    have := Rt_nonneg hT
    have := Rt_nonneg (hT.trans hTt)
    linarith

end LeanLab.Dudek2014.TrudgianRoute
