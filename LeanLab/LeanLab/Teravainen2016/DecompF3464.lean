/-
Decomposition of the restriction input into the small-delta and large-delta
level-set estimates, followed by dyadic summation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.LevelSetSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF Step for small delta bounds the number of exceptional frequencies by Parseval and the pointwise growth bound. -/
theorem f3464_small_delta_level_set (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c →
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ → δ ≤ (M : ℝ) ^ (-c) →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ A (ε * c) * δ ^ (-(2 + ε)) := by
  sorry

/-- LEAF Step for large delta bounds the number of exceptional frequencies by a constant times delta to the power minus two minus epsilon, using the rational Fourier expansion and its decay. -/
theorem f3464_large_delta_level_set (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ → (M : ℝ) ^ (-c) < δ →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ K * δ ^ (-(2 + ε)) := by
  sorry

/-- The restriction estimate follows from the two level-set steps and the proved dyadic summation. -/
theorem paper_enveloping_restriction_input_F3464 (A D : ℝ → ℝ) (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) : ∀ r : ℝ, 2 < r → ∃ C : ℝ, 0 < C ∧ ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M → EnvelopingFourierBounds w (WW J w) b M A D → Restriction42 M (restrictionBeta w (WW J w) b M) r C := by
  intro r hr
  have hε : 0 < (r - 2) / 2 := by linarith
  obtain ⟨c, hc, K1, hK1, Hlarge⟩ :=
    f3464_large_delta_level_set A D hAD ((r - 2) / 2) hε
  have hA := (hAD ((r - 2) / 2 * c) (mul_pos hε hc)).1
  set K : ℝ := K1 + A ((r - 2) / 2 * c) with hKdef
  have hK : 0 < K := by dsimp [K]; linarith
  have hlevel : ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
      0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
        EnvelopingFourierBounds w (WW J w) b M A D →
        ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ →
          (((range M).filter (fun ξ =>
            δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
              ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
            ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
              : ℝ) ≤ K * δ ^ (-(2 + (r - 2) / 2)) := by
    intro J w hJ hw b hb hbW hamen M hM hB a δ hδ
    have hpow : 0 ≤ δ ^ (-(2 + (r - 2) / 2)) := Real.rpow_nonneg hδ.le _
    rcases le_or_gt δ ((M : ℝ) ^ (-c)) with hsmall | hlarge
    · refine (f3464_small_delta_level_set A D hAD ((r - 2) / 2) hε c hc
        J w hJ hw b hb hbW hamen M hM hB a δ hδ hsmall).trans ?_
      have hK1pow : K1 * δ ^ (-(2 + (r - 2) / 2)) ≤ K * δ ^ (-(2 + (r - 2) / 2)) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [K]; linarith
        · exact hpow
      exact add_le_add hK1pow (le_of_eq (mul_one hpow))
    · refine (Hlarge J w hJ hw b hb hbW hamen M hM hB a δ hδ hlarge).trans ?_
      have hApow : A ((r - 2) / 2 * c) * δ ^ (-(2 + (r - 2) / 2)) ≤
          K * δ ^ (-(2 + (r - 2) / 2)) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [K]; linarith
        · exact hpow
      exact add_le_add (le_of_eq (mul_one hpow)) hApow
  have hq : 0 < 2 + (r - 2) / 2 := by linarith
  have hqr : 2 + (r - 2) / 2 < r := by linarith
  have hr0 : 0 < r := by linarith
  set Cst : ℝ := K * ((2 * K) ^ (1 / q)) ^ r * ((2 * K) ^ (1 / q)) ^ (-q) *
      (1 / 2 : ℝ) ^ (-q) * (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ with hCst
  have hx1 : (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q) < 1 := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hCpos : 0 < Cst := by
    have : 0 < (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ := inv_pos.mpr (by linarith)
    positivity
  refine ⟨Cst ^ (1 / r), Real.rpow_pos_of_pos hCpos _, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM hB a
  set E : ℝ := ((M : ℝ)⁻¹ * ∑ n ∈ range M,
      ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) with hEdef
  have hE : 0 ≤ E := by
    apply Real.rpow_nonneg
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun n _ => mul_nonneg (by positivity)
      (restrictionBeta_nonneg w (WW J w) b M n))
  have hmom := dyadic_level_moment (range M)
    (fun ξ => ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)
    (fun _ => norm_nonneg _) hE hK hq hqr
    (hlevel J w hJ hw b hb hbW hamen M hM hB a)
  have hsum : 0 ≤ ∑ ξ ∈ range M,
      ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖ ^ r :=
    sum_nonneg (fun ξ _ => Real.rpow_nonneg (norm_nonneg _) r)
  have hroot := Real.rpow_le_rpow hsum hmom (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hE r), ← Real.rpow_mul hE,
    mul_one_div_cancel hr0.ne', Real.rpow_one] at hroot
  exact hroot

end LeanLab.Teravainen2016
