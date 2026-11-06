/-
P0079 page 10, the completed full continuous geometric model.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ModelExpansion396
import LeanLab.LZPowersOfTwo.Decomp375e
import LeanLab.LZPowersOfTwo.Decomp375h

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, displays 36 and 37. The exact major_full_lower375
statement follows from the finite transform, rectangle bound and floor margin.
No OPEN analytic estimate is used. -/
theorem major_full_lower396 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hμ : ∀ i, μ i ≠ 0) (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ᶠ X : ℝ in atTop,
      (1 - (13 / 4 : ℝ) * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X *
        (cutoff293 s μ ε X) ^ s ≤
          (∫ α : ℝ, majorModel353 s l1 l2 μ γ η ε X α).re := by
  classical
  have hl1 : 0 < l1 := by linarith
  have hl2 : l2 < 0 := by linarith
  have hq : 0 < -l2 := by linarith
  have hql : -l2 ≤ l1 := by
    rw [abs_div, abs_of_pos hl1, abs_of_neg hl2] at hr
    have H := (le_div_iff₀ hq).mp hr
    linarith
  have habs : |l1 * l2| = l1 * (-l2) := by
    rw [abs_mul, abs_of_pos hl1, abs_of_neg hl2]
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε hl1]
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  filter_upwards [model_floor_margin375 s μ ε l1 hM hε h1 hε',
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * |γ| / ε),
    eventually_ge_atTop (η / (2 * ε * (l1 - 1)))] with X hfloor hL hX hγX hηX
  have hX0 : 0 < X := by linarith
  have hbox : ε * X ≤ X := by nlinarith
  have hγ : 2 * |γ| ≤ ε * X := by
    have H := (div_le_iff₀ hε).mp hγX
    nlinarith only [H]
  have hηsmall : η ≤ 2 * ε * (l1 - 1) * X := by
    have H := (div_le_iff₀ (by positivity : 0 < 2 * ε * (l1 - 1))).mp hηX
    nlinarith only [H]
  rw [full_model_transform396 s l1 l2 μ γ η ε X hbox hη]
  let T := Fintype.piFinset (fun _ : Fin s => Icc 1 ⌊cutoff293 s μ ε X⌋₊)
  have hterm (m : Fin s → ℕ) (hm : m ∈ T) :
      (1 - 3 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X ≤
        ∫ v in Set.Icc (ε * X) X, ∫ t in Set.Icc (ε * X) X,
          max 0 (η - |l1 * t + l2 * v + ((∑ i : Fin s, μ i * 2 ^ m i) + γ)|) := by
    have hm' : ∀ i : Fin s, (m i : ℝ) ≤ cutoff293 s μ ε X := by
      intro i
      have H := (Fintype.mem_piFinset.mp hm i)
      exact (by exact_mod_cast (mem_Icc.mp H).2 :
        (m i : ℝ) ≤ ⌊cutoff293 s μ ε X⌋₊).trans (Nat.floor_le (by linarith))
    have hu := power_shift_bound375 s μ ε X γ m hM hε hX0 hm' hγ
    have H := tent_box_lower375 l1 (-l2) ε X η ((∑ i : Fin s, μ i * 2 ^ m i) + γ)
      h1 (by linarith) hql hε hε' hX0 hη hηsmall hu
    simpa only [habs, sub_eq_add_neg, neg_mul, neg_neg] using H
  calc
    _ = ((1 - (13 / 4 : ℝ) * l1 * ε) * (cutoff293 s μ ε X) ^ s) *
        (η ^ 2 * X / (2 * |l1 * l2|)) := by ring
    _ ≤ ((1 - 3 * l1 * ε) * (⌊cutoff293 s μ ε X⌋₊ : ℝ) ^ s) *
        (η ^ 2 * X / (2 * |l1 * l2|)) := mul_le_mul_of_nonneg_right hfloor (by positivity)
    _ = ∑ m ∈ T, (1 - 3 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 * X := by
      rw [sum_const, nsmul_eq_mul]
      dsimp only [T]
      rw [power_tuple_count375]
      push_cast
      ring
    _ ≤ _ := sum_le_sum hterm

end LeanLab.LZPowersOfTwo
