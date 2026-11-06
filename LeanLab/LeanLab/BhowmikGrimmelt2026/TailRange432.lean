/-
A derived range for the major tail in P0029 page 27 display 7.8.
The threshold is a sufficient derived condition and is not a printed paper constant.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp328a
import LeanLab.BhowmikGrimmelt2026.ArcFamily261

namespace LeanLab.BhowmikGrimmelt2026

/-- Above X to theta minus one half, a fixed decay power absorbs the rational remainder.
Derived from the explicit error in page 26 display 7.5. -/
theorem tail_absorption_large_eta432 {x ϑ η : ℝ} (hx : 1 ≤ x)
    (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) (hη : 0 < η)
    (hlarge : x ^ (ϑ - 1 / 2) ≤ η)
    (hscale : 10 * (x ^ ϑ) ^ 2 ≤ η * x) :
    (x ^ ϑ) ^ 2 * (η * x / (x ^ ϑ) ^ 2) ^ (-((2 * ϑ + 2) / (1 / 2 - ϑ))) ≤ η ^ 2 := by
  have hxp : 0 < x := by linarith
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  let d : ℝ := 1 / 2 - ϑ
  let A : ℝ := (2 * ϑ + 2) / d
  have hd : 0 < d := by dsimp [d]; linarith
  have hA : 0 < A := div_pos (by positivity) hd
  have hR : (x ^ ϑ) ^ 2 = x ^ (2 * ϑ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]
    congr 1
    ring
  have hK : x ^ d ≤ η * x / (x ^ ϑ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hRp)).mpr
    calc
      _ = x ^ (ϑ - 1 / 2) * x := by
        rw [hR, ← Real.rpow_add hxp]
        calc
          x ^ (d + 2 * ϑ) = x ^ ((ϑ - 1 / 2) + 1) := by
            congr 1
            dsimp [d]
            ring
          _ = x ^ (ϑ - 1 / 2) * x := by rw [Real.rpow_add hxp, Real.rpow_one]
      _ ≤ η * x := mul_le_mul_of_nonneg_right hlarge hxp.le
  have hpower : (x ^ ϑ) ^ 2 * (x ^ d) ^ (-A) = x ^ (-2 : ℝ) := by
    rw [hR, ← Real.rpow_mul hxp.le, ← Real.rpow_add hxp]
    congr 1
    dsimp [A]
    field_simp
    <;> ring
  have hinv : 1 / x ≤ η := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith [Real.one_le_rpow hx hϑ.le, sq_nonneg (x ^ ϑ - 1)]
  calc
    _ ≤ (x ^ ϑ) ^ 2 * (x ^ d) ^ (-A) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hxp d) hK (by linarith))
        (sq_nonneg _)
    _ = x ^ (-2 : ℝ) := hpower
    _ = (1 / x) ^ 2 := by rw [Real.rpow_neg hxp.le, Real.rpow_two]; simp [one_div, inv_pow]
    _ ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hinv 2

/-- The exact major tail has logarithm power one on the derived large eta range.
This supplies a nonoptimized interval of eta values, not only one chosen eta. -/
theorem major_tail_large_eta432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      (X : ℝ) ^ (ϑ - 1 / 2) ≤ η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  let A : ℝ := (2 * ϑ + 2) / (1 / 2 - ϑ)
  have hA : 0 < A := div_pos (by positivity) (by linarith)
  obtain ⟨C₁, hC₁, h₁⟩ := major_family_of_tail261 hϕ hG A hA
  obtain ⟨C₂, hC₂, h₂⟩ := major_core_log1_328 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hlarge hscale
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 := Real.one_le_rpow hx1 hϑ.le
  have ht := tail_absorption_large_eta432 hx1 hϑ hϑ' hη hlarge hscale
  have hmajor := h₁ X hX ((X : ℝ) ^ ϑ) η hR1 hη hη1 hscale ht
  change (∑ N ∈ Finset.Icc 1 X, ‖majorError150 ϕ G X N ϑ η‖ ^ 2) ≤ _ at hmajor
  have hcore := h₂ X hX η hη hη1 hscale
  have hs := coefficient_split328 (Finset.Icc 1 X)
    (fun N => majorTail328 ϕ G X N ϑ η) (fun N => majorError150 ϕ G X N ϑ η)
  have heq (N : ℕ) : majorTail328 ϕ G X N ϑ η - majorError150 ϕ G X N ϑ η =
      -majorCore328 ϕ G X N ϑ η := by unfold majorTail328; ring
  simp_rw [heq, norm_neg] at hs
  nlinarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.tail_absorption_large_eta432
#print axioms LeanLab.BhowmikGrimmelt2026.major_tail_large_eta432
