/-
Feed 1122 split of `leaf_rphi_major` of `SPLIT_prop75.lean`.

Bhowmik and Grimmelt 2026, Proposition 7.5, (7.17), p. 28: the first step of its proof is
Lemma 7.3, (7.8), p. 26, applied with `R = X ^ ϑ`, `η = R ^ (-1/4)` and `T_q = η X q / R`.
With this `η` the three error terms of (7.8) become `R ^ (-1) + X ^ (-2/5) + η ^ 4`, that is
`2 X ^ (-ϑ) + X ^ (-2/5)`, and times `X ^ 3` they give `X ^ (3 - ϑ) + X ^ (13/5)`.
Lemma 7.3 needs `10 R ^ 2 ≤ η X`, which is `10 X ^ (2 ϑ) ≤ X ^ (1 - ϑ/4)`, true for large `X`
exactly because `ϑ < 4/9`; the finitely many small `X` are absorbed in the constant.

Inputs: `lemma73` of `Statements.lean`, the lab statement of Lemma 7.3, used as is and
still OPEN there, so `leaf_rphi_major_of_leaves` is CONDITIONAL ON Lemma 7.3 only. The
admissibility of `η` and the small `X` absorption are both proved here, so this file has no
sorry of its own.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

/-- Proved here. Proof of Proposition 7.5, p. 28, the admissibility of `η = R ^ (-1/4)` in Lemma 7.3:
for `0 < ϑ < 4/9` there is `X₀` with `10 R ^ 2 ≤ η X` for all `X ≥ X₀`, where `R = X ^ ϑ`.
This is `2 ϑ < 1 - ϑ / 4`, the source of the bound `ϑ < 4/9`. -/
theorem leaf_eta_admissible (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X := by
  set δ : ℝ := 1 - 9 / 4 * ϑ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨max 1 ⌈(10 : ℝ) ^ (1 / δ)⌉₊, ?_⟩
  intro X hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_left _ _) hX
  have hx : (0 : ℝ) < X := by linarith
  have hc : (10 : ℝ) ^ (1 / δ) ≤ X := by
    have h1 : (10 : ℝ) ^ (1 / δ) ≤ (⌈(10 : ℝ) ^ (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(10 : ℝ) ^ (1 / δ)⌉₊ : ℝ) ≤ X := by
      exact_mod_cast le_trans (le_max_right _ _) hX
    linarith
  have h10 : (10 : ℝ) ≤ (X : ℝ) ^ δ := by
    have := Real.rpow_le_rpow (by positivity) hc hδ0.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ0.ne', Real.rpow_one] at this
  have e1 : ((X : ℝ) ^ ϑ) ^ 2 = (X : ℝ) ^ (2 * ϑ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; ring_nf
  have e2 : ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X = (X : ℝ) ^ (2 * ϑ) * (X : ℝ) ^ δ := by
    rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
    have : ((X : ℝ) ^ (ϑ * -(1 / 4) : ℝ)) * X = (X : ℝ) ^ (ϑ * -(1 / 4) : ℝ) * (X : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one]
    rw [this, ← Real.rpow_add hx]
    congr 1; rw [hδ]; ring
  rw [e1, e2]
  have hp : 0 < (X : ℝ) ^ (2 * ϑ) := Real.rpow_pos_of_pos hx _
  nlinarith

/-- Finitely many `X` are absorbed in a constant: proved, no paper input. -/
theorem small_X_absorb (F g : ℕ → ℝ) (X₀ : ℕ) (hg : ∀ X : ℕ, 2 ≤ X → 0 < g X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → X < X₀ → F X ≤ C * g X := by
  classical
  let t : ℕ → ℝ := fun X => if 2 ≤ X then |F X| / g X else 0
  have ht : ∀ X, 0 ≤ t X := by
    intro X; simp only [t]; split_ifs with h
    · exact div_nonneg (abs_nonneg _) (hg X h).le
    · exact le_rfl
  refine ⟨∑ X ∈ Finset.range X₀, t X, Finset.sum_nonneg (fun X _ => ht X), ?_⟩
  intro X h2 hX
  have hle : t X ≤ ∑ X ∈ Finset.range X₀, t X :=
    Finset.single_le_sum (fun Y _ => ht Y) (Finset.mem_range.2 hX)
  have hgx := hg X h2
  have hval : t X * g X = |F X| := by
    simp only [t, if_pos h2]; field_simp
  calc F X ≤ |F X| := le_abs_self _
    _ = t X * g X := hval.symm
    _ ≤ (∑ X ∈ Finset.range X₀, t X) * g X := mul_le_mul_of_nonneg_right hle hgx.le

/-- `leaf_rphi_major` of `SPLIT_prop75.lean`, exactly, from Lemma 7.3 and the leaf above. -/
theorem leaf_rphi_major_of_leaves (ϕ G : ℝ → ℝ) (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 4 / 9) :
    ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) -
          ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))‖ ^ 2 ≤
        C * ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
  obtain ⟨C₇, h₇⟩ := lemma73 ϕ G hϕ hG ϑ hϑ0 (by linarith)
  obtain ⟨X₀, hX₀⟩ := leaf_eta_admissible ϑ hϑ0 hϑ
  set F : ℕ → ℝ := fun X => ∑ N ∈ Finset.Icc 1 X,
        ‖(rphi ϕ N : ℂ) -
          ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ)
              (fun q => ((X : ℝ) ^ ϑ) ^ (-(1 / 4) : ℝ) * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))‖ ^ 2 with hF
  set g : ℕ → ℝ := fun X => ((X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5
    with hgdef
  have hgpos : ∀ X : ℕ, 2 ≤ X → 0 < g X := by
    intro X hX
    have hx : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hl : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    simp only [g]; positivity
  obtain ⟨Cs, hCs0, hCs⟩ := small_X_absorb F g X₀ hgpos
  refine ⟨Cs + 2 * max C₇ 0, ?_⟩
  intro X hX
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hx : (0 : ℝ) < X := by linarith
  have hgX := hgpos X hX
  suffices key : F X ≤ (Cs + 2 * max C₇ 0) * g X by rw [mul_assoc]; exact key
  by_cases hsmall : X < X₀
  · have := hCs X hX hsmall
    nlinarith [le_max_right C₇ 0]
  · push_neg at hsmall
    have hr1 : (1 : ℝ) ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hx1 hϑ0.le
    have hr : (0 : ℝ) < (X : ℝ) ^ ϑ := by linarith
    set r := (X : ℝ) ^ ϑ with hrdef
    set η := r ^ (-(1 / 4) : ℝ) with hηdef
    have hη0 : 0 < η := Real.rpow_pos_of_pos hr _
    have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
    have h := h₇ X hX η hη0 hη1 (hX₀ X hsmall)
    have hη4 : η ^ 4 = r⁻¹ := by
      rw [hηdef, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num [Real.rpow_neg_one]
    have he1 : r⁻¹ * (X : ℝ) ^ 3 = (X : ℝ) ^ (3 - ϑ) := by
      rw [Real.rpow_sub hx, hrdef]
      norm_num [div_eq_inv_mul]
    have he2 : (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 = (X : ℝ) ^ (13 / 5 : ℝ) := by
      rw [show (13 / 5 : ℝ) = -(2 / 5) + (3 : ℕ) by norm_num, Real.rpow_add hx,
        Real.rpow_natCast]
    have hrhs : C₇ * (r⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) + η ^ 4) * (X : ℝ) ^ 3 *
        Real.log X ^ 5 =
        C₇ * (2 * (X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
      rw [hη4, ← he1, ← he2]; ring
    have hl : 0 ≤ Real.log X := Real.log_nonneg hx1
    have hp1 : 0 ≤ (X : ℝ) ^ (3 - ϑ) := (Real.rpow_pos_of_pos hx _).le
    have hp2 : 0 ≤ (X : ℝ) ^ (13 / 5 : ℝ) := (Real.rpow_pos_of_pos hx _).le
    have hL5 : 0 ≤ Real.log X ^ 5 := pow_nonneg hl 5
    have hstep : C₇ * (2 * (X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 ≤
        2 * max C₇ 0 * g X := by
      simp only [g]
      have hA : 0 ≤ (2 * (X : ℝ) ^ (3 - ϑ) + (X : ℝ) ^ (13 / 5 : ℝ)) * Real.log X ^ 5 := by
        positivity
      have hm := le_max_left C₇ 0
      have hm0 := le_max_right C₇ 0
      nlinarith [mul_le_mul_of_nonneg_right hm hA, mul_nonneg hm0 (mul_nonneg hp2 hL5)]
    have hFX : F X ≤ C₇ * (r⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) + η ^ 4) * (X : ℝ) ^ 3 *
        Real.log X ^ 5 := by
      simp only [F]; exact h
    nlinarith [mul_nonneg hCs0 hgX.le]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_rphi_major_of_leaves
