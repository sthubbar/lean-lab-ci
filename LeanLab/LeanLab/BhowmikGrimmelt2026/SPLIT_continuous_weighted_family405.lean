/-
Split of the weighted minor coefficient family estimate stated on its exact integral form.
The weighted coefficient is the minor arc integral of the smoothed square against the
continuous rational model. That model is the discrete rational weight plus the alias
remainder, so the family mean square separates into two family estimates with the same
power budget, and the assembly below adds them with the factor two of the square.

Two leaves are left open. The assembly is unconditional in those two leaves and does not
use `continuous_weighted_family405`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp405b

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory

/-- LEAF. Discrete weight part of the weighted minor family mean square. On the minor arc
set the integral of the smoothed square against the discrete rational weight `bRhat` is
estimated over the whole family `N ≤ X` by the printed power budget with logarithm power
five. This is the harder of the two summands: it keeps the discrete transform rather than
its continuous model, and it carries the whole saving of the family. -/
theorem leaf_bRhat_minor_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) α‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- LEAF. Alias remainder part of the weighted minor family mean square. On the minor arc
set the integral of the smoothed square against the continuous rational model minus its
discrete weight is estimated over the whole family `N ≤ X` by the same power budget. This
is the smaller of the two summands: the remainder is uniformly of order `η ^ 2` on the
scale of the statement, so no power of `X` has to be recovered here. -/
theorem leaf_alias_remainder_family405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, hf⟩ := alias_on_family405 hϕ hG ϑ hϑ (1 / 5) (by norm_num)
  refine ⟨C, hC, fun X hX η hη hη1 hscale => ?_⟩
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  -- the scale hypothesis with `η ≤ 1` forces `X ≥ 10`, hence `log X ≥ 1`
  have hR1 : (1 : ℝ) ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hsq : (1 : ℝ) ≤ ((X : ℝ) ^ ϑ) ^ 2 := by nlinarith
  have h10 : (10 : ℝ) ≤ (X : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hη1 hXp.le]
  have hexp : Real.exp 1 ≤ (X : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := (Real.le_log_iff_exp_le hXp).mpr hexp
  have hlog0 : (0 : ℝ) ≤ Real.log (X : ℝ) := le_trans (by norm_num) hlog1
  have hlog5 : Real.log (X : ℝ) ≤ Real.log (X : ℝ) ^ 5 :=
    le_self_pow₀ hlog1 (by norm_num)
  -- the leaf integrand is `aliasOn405` on the minor arc set
  have hsum : (∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α‖ ^ 2) =
      ∑ N ∈ Finset.Icc 1 X,
        ‖aliasOn405 ϕ G X N ϑ η {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro N _
    simp only [aliasOn405]
  rw [hsum]
  have h := hf X hX η hη hscale {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}
    (measurableSet_majorArc84 X ((X : ℝ) ^ ϑ)).compl
  have hpow : ((X : ℝ) ^ (-(1 / 5) : ℝ)) ^ 2 = (X : ℝ) ^ (-(2 / 5) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
    norm_num
  rw [hpow] at h
  have hinv : (0 : ℝ) ≤ ((X : ℝ) ^ ϑ)⁻¹ := (inv_pos.mpr (Real.rpow_pos_of_pos hXp ϑ)).le
  have hleA : (X : ℝ) ^ (-(2 / 5) : ℝ) ≤ ((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ) :=
    le_add_of_nonneg_left hinv
  have hX3 : (0 : ℝ) ≤ (X : ℝ) ^ 3 := by positivity
  have hnn : (0 : ℝ) ≤ C * (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 := by positivity
  have step1 : C * (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 * Real.log (X : ℝ) ≤
      C * (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 * Real.log (X : ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_left hlog5 hnn
  have step2 : C * (X : ℝ) ^ (-(2 / 5) : ℝ) * (X : ℝ) ^ 3 * Real.log (X : ℝ) ^ 5 ≤
      C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 *
        Real.log (X : ℝ) ^ 5 := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlog0 5)
    apply mul_le_mul_of_nonneg_right _ hX3
    exact mul_le_mul_of_nonneg_left hleA hC
  exact h.trans (step1.trans step2)

/-- The weighted minor family estimate, assembled from the two leaves: the discrete weight
part and its alias remainder are the two summands of the exact integral form, and the
square of a sum is at most twice the sum of the squares. -/
theorem continuous_weighted_family405_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ)
    (hG : IsMajorWeight G) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖continuousWeighted405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
          (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := leaf_bRhat_minor_family405 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := leaf_alias_remainder_family405 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * C₁ + 2 * C₂, by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hb := h₁ X hX η hη hη1 hscale
  have ha := h₂ X hX η hη hη1 hscale
  -- the exact integral form of one coefficient, split into the two leaf summands
  have hdec : ∀ N : ℕ, continuousWeighted405 ϕ G X N ϑ η =
      -(∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) α) -
      (∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α) := by
    intro N
    unfold continuousWeighted405 aliasOn405
    rw [minorWeighted_eq_integral328 hG ϕ hX N ϑ hη]
  -- one term: the norm of the difference of the two parts, and the square of a sum
  have hterm : ∀ N : ℕ, ‖continuousWeighted405 ϕ G X N ϑ η‖ ^ 2 ≤
      2 * ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) α‖ ^ 2 +
      2 * ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α‖ ^ 2 := by
    intro N
    set P : ℂ := (∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
            ee (-(N * α))) α) with hP
    set Q : ℂ := (∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
            ee (-(N * α))) α) with hQ
    have hdecN : continuousWeighted405 ϕ G X N ϑ η = -P - Q := by
      rw [hP, hQ]
      exact hdec N
    have htri : ‖continuousWeighted405 ϕ G X N ϑ η‖ ≤ ‖P‖ + ‖Q‖ := by
      rw [hdecN]
      have h := norm_add_le (-P) (-Q)
      rw [norm_neg, norm_neg] at h
      simpa only [sub_eq_add_neg] using h
    have hu : (0 : ℝ) ≤ ‖continuousWeighted405 ϕ G X N ϑ η‖ := norm_nonneg _
    have hp : (0 : ℝ) ≤ ‖P‖ := norm_nonneg P
    have hq : (0 : ℝ) ≤ ‖Q‖ := norm_nonneg Q
    have key : 0 ≤ (‖P‖ + ‖Q‖ - ‖continuousWeighted405 ϕ G X N ϑ η‖) *
        (‖P‖ + ‖Q‖ + ‖continuousWeighted405 ϕ G X N ϑ η‖) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [key, sq_nonneg (‖P‖ - ‖Q‖), hu, hp, hq]
  have hsum : (∑ N ∈ Finset.Icc 1 X, (
        2 * ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
            (fun α => Sphi ϕ N α ^ 2 *
              bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
              ee (-(N * α))) α‖ ^ 2 +
        2 * ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
                bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
              ee (-(N * α))) α‖ ^ 2)) =
      2 * (∑ N ∈ Finset.Icc 1 X,
            ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
              (fun α => Sphi ϕ N α ^ 2 *
                bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
                ee (-(N * α))) α‖ ^ 2) +
        2 * (∑ N ∈ Finset.Icc 1 X,
            ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
              (fun α => Sphi ϕ N α ^ 2 *
                (continuousModel405 G ((X : ℝ) ^ ϑ)
                    (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
                  bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
                ee (-(N * α))) α‖ ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hkey :
      2 * (∑ N ∈ Finset.Icc 1 X,
            ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
              (fun α => Sphi ϕ N α ^ 2 *
                bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α *
                ee (-(N * α))) α‖ ^ 2) +
        2 * (∑ N ∈ Finset.Icc 1 X,
            ‖∫ α in (0 : ℝ)..1, {α | ¬ MajorArc X ((X : ℝ) ^ ϑ) α}.indicator
              (fun α => Sphi ϕ N α ^ 2 *
                (continuousModel405 G ((X : ℝ) ^ ϑ)
                    (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
                  bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) *
                ee (-(N * α))) α‖ ^ 2) ≤
      (2 * C₁ + 2 * C₂) * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log X ^ 5 := by
    have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hlog0 : (0 : ℝ) ≤ Real.log X :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
    have hP : (0 : ℝ) ≤ (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) *
        (X : ℝ) ^ 3 * Real.log X ^ 5 := by
      have h1 : (0 : ℝ) < (X : ℝ) ^ ϑ := Real.rpow_pos_of_pos hX0 ϑ
      have h2 : (0 : ℝ) < (X : ℝ) ^ (-(2 / 5) : ℝ) := Real.rpow_pos_of_pos hX0 _
      have h3 : (0 : ℝ) ≤ (X : ℝ) ^ 3 := by positivity
      have h4 : (0 : ℝ) ≤ Real.log X ^ 5 := pow_nonneg hlog0 5
      have h5 : (0 : ℝ) ≤ ((X : ℝ) ^ ϑ)⁻¹ := (inv_pos.mpr h1).le
      exact mul_nonneg (mul_nonneg (add_nonneg h5 h2.le) h3) h4
    have e1 := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
    have e2 := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [e1, e2, mul_nonneg hC₁ hP, mul_nonneg hC₂ hP]
  refine (Finset.sum_le_sum (fun N _ => hterm N)).trans ?_
  rw [hsum]
  exact hkey

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.continuous_weighted_family405_split
