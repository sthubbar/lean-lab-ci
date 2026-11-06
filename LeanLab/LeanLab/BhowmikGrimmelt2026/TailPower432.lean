/-
A power margin above the minimal eta scale absorbs the rational remainder.
Source: P0029 page 26 display 7.5 and page 27 major contribution.
The auxiliary delta is a derived parameter and is not a paper constant.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.TailRange432

namespace LeanLab.BhowmikGrimmelt2026

/-- Any fixed power margin over the minimal eta power suffices.
The decay exponent depends on theta and the chosen nonnegative power delta. -/
theorem tail_absorption_power432 {x ϑ δ η : ℝ} (hx : 0 < x)
    (hϑ : 0 < ϑ) (hδ : 0 ≤ δ) (hgap : δ < 1 - 2 * ϑ)
    (hlarge : x ^ (-δ) ≤ η) :
    (x ^ ϑ) ^ 2 * (η * x / (x ^ ϑ) ^ 2) ^
      (-((2 * ϑ + 2 * δ) / (1 - 2 * ϑ - δ))) ≤ η ^ 2 := by
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hx ϑ
  let d : ℝ := 1 - 2 * ϑ - δ
  let A : ℝ := (2 * ϑ + 2 * δ) / d
  have hd : 0 < d := by dsimp [d]; linarith
  have hA : 0 < A := div_pos (by positivity) hd
  have hR : (x ^ ϑ) ^ 2 = x ^ (2 * ϑ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    ring
  have hK : x ^ d ≤ η * x / (x ^ ϑ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hRp)).mpr
    calc
      _ = x ^ (-δ) * x := by
        rw [hR, ← Real.rpow_add hx]
        calc
          x ^ (d + 2 * ϑ) = x ^ (-δ + 1) := by
            congr 1
            dsimp [d]
            ring
          _ = x ^ (-δ) * x := by rw [Real.rpow_add hx, Real.rpow_one]
      _ ≤ η * x := mul_le_mul_of_nonneg_right hlarge hx.le
  have hpower : (x ^ ϑ) ^ 2 * (x ^ d) ^ (-A) = (x ^ (-δ)) ^ 2 := by
    rw [hR, ← Real.rpow_mul hx.le, ← Real.rpow_add hx,
      ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    dsimp [A]
    field_simp
    <;> ring
  calc
    _ ≤ (x ^ ϑ) ^ 2 * (x ^ d) ^ (-A) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx d) hK (by linarith))
        (sq_nonneg _)
    _ = (x ^ (-δ)) ^ 2 := hpower
    _ ≤ η ^ 2 := pow_le_pow_left₀ (Real.rpow_pos_of_pos hx (-δ)).le hlarge 2

/-- The exact major tail has logarithm power one throughout every fixed power margin.
For delta below one minus two theta, all eta at least X to negative delta are covered. -/
theorem major_tail_power_eta432 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2)
    (δ : ℝ) (hδ : 0 ≤ δ) (hgap : δ < 1 - 2 * ϑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      (X : ℝ) ^ (-δ) ≤ η →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖majorTail328 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by
  let A : ℝ := (2 * ϑ + 2 * δ) / (1 - 2 * ϑ - δ)
  have hA : 0 < A := div_pos (by positivity) (by linarith)
  obtain ⟨C₁, hC₁, h₁⟩ := major_family_of_tail261 hϕ hG A hA
  obtain ⟨C₂, hC₂, h₂⟩ := major_core_log1_328 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hlarge hscale
  have hxp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR1 := Real.one_le_rpow hx1 hϑ.le
  have ht := tail_absorption_power432 hxp hϑ hδ hgap hlarge
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

#print axioms LeanLab.BhowmikGrimmelt2026.tail_absorption_power432
#print axioms LeanLab.BhowmikGrimmelt2026.major_tail_power_eta432
