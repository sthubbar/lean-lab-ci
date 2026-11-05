/-
P0079 page 10, the rectangle inside the continuous tent integral.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ArcGeometry353

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, the written rectangle argument before display 37.
Write q for absolute lambda2. The permitted v band lies in the integration box.
For every v in that band, the centered t interval has length eta over lambda1,
lies in the box, and has tent value at least eta over two. -/
theorem tent_rectangle375 (l q ε X η u v : ℝ)
    (hl : 1 < l) (hq : 1 < q) (hql : q ≤ l)
    (hε : 0 < ε) (hX : 0 < X) (hη : 0 < η)
    (hηsmall : η ≤ 2 * ε * (l - 1) * X) (hu : |u| ≤ ε * X)
    (hv : v ∈ Set.Icc (2 * ε * l * X / q) ((1 - ε * l) * X / q)) :
    let c := (q * v - u) / l
    let r := η / (2 * l)
    (Set.Icc (2 * ε * l * X / q) ((1 - ε * l) * X / q) ⊆ Set.Icc (ε * X) X) ∧
    (Set.Icc (c - r) (c + r) ⊆ Set.Icc (ε * X) X) ∧
    ∀ t ∈ Set.Icc (c - r) (c + r), η / 2 ≤ max 0 (η - |l * t - q * v + u|) := by
  dsimp only
  have hl0 : 0 < l := by linarith only [hl]
  have hq0 : 0 < q := by linarith only [hq]
  have hcenter : l * ((q * v - u) / l) = q * v - u := by field_simp
  have hradius : l * (η / (2 * l)) = η / 2 := by field_simp
  obtain ⟨hul, huu⟩ := abs_le.mp hu
  have hvl : 2 * ε * l * X ≤ q * v := by
    have H := (div_le_iff₀ hq0).mp hv.1
    nlinarith only [H]
  have hvu : q * v ≤ (1 - ε * l) * X := by
    have H := (le_div_iff₀ hq0).mp hv.2
    nlinarith only [H]
  have hleft : ε * X ≤ (q * v - u) / l - η / (2 * l) := by
    apply (mul_le_mul_iff_right₀ hl0).mp
    nlinarith only [hcenter, hradius, hvl, huu, hηsmall]
  have hright : (q * v - u) / l + η / (2 * l) ≤ X := by
    apply (mul_le_mul_iff_right₀ hl0).mp
    have hxl : X ≤ l * X := by nlinarith only [hl, hX]
    nlinarith only [hcenter, hradius, hvu, hul, hηsmall, hxl]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hlow : ε * X ≤ 2 * ε * l * X / q := by
      apply (le_div_iff₀ hq0).mpr
      have H := mul_le_mul_of_nonneg_right hql (mul_nonneg hε.le hX.le)
      have Hpos : 0 ≤ ε * l * X := by positivity
      nlinarith only [H, Hpos]
    have hupp : (1 - ε * l) * X / q ≤ X := by
      apply (div_le_iff₀ hq0).mpr
      have H := mul_le_mul_of_nonneg_right hq.le hX.le
      have Hpos : 0 ≤ ε * l * X := by positivity
      nlinarith only [H, Hpos]
    exact ⟨hlow.trans hw.1, hw.2.trans hupp⟩
  · intro t ht
    exact ⟨hleft.trans ht.1, ht.2.trans hright⟩
  · intro t ht
    have htl := mul_le_mul_of_nonneg_left ht.1 hl0.le
    have htu := mul_le_mul_of_nonneg_left ht.2 hl0.le
    have htent : |l * t - q * v + u| ≤ η / 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith only [htl, htu, hcenter, hradius]
    exact (show η / 2 ≤ η - |l * t - q * v + u| by linarith only [htent]).trans
      (le_max_right _ _)

end LeanLab.LZPowersOfTwo
