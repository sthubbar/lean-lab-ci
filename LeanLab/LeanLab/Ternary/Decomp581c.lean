/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 equation 5.1.
Reindex the finite correction before applying the independent analytic split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp581b

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory

/-- Every factor of a positive divisible triple product is at most the dividend.
Derived finite support check for MMS page 11 equation 5.1. -/
theorem triple_factors_le {n : ℕ} (hn : 0 < n) {p : ℕ × ℕ × ℕ}
    (hd : tripleProduct p ∣ n) : p.1 ≤ n ∧ p.2.1 ≤ n ∧ p.2.2 ≤ n := by
  have h₁ : p.1 ∣ tripleProduct p := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have h₂ : p.2.1 ∣ tripleProduct p := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have h₃ : p.2.2 ∣ tripleProduct p := dvd_mul_left _ _
  exact ⟨Nat.le_of_dvd hn (h₁.trans hd), Nat.le_of_dvd hn (h₂.trans hd),
    Nat.le_of_dvd hn (h₃.trans hd)⟩

/-- The original n dependent prime ranges equal the fixed ordered triple set.
MMS page 11 equation 5.1. No analytic estimate is used. -/
theorem harman_correction_reindex (x : ℝ) {n : ℕ} (hn : 0 < n) :
    Task361.harmanMajorant x n - Task361.roughIndicator n (x ^ (1 / 4 : ℝ)) =
      ∑ p ∈ primeTriples x,
        if tripleProduct p ∣ n then Task361.roughIndicator (n / tripleProduct p) p.1 else 0 := by
  classical
  unfold Task361.harmanMajorant
  rw [add_sub_cancel_left]
  let S := (range (n + 1)).product ((range (n + 1)).product (range (n + 1)))
  let f : (ℕ × ℕ × ℕ) → ℝ := fun p =>
    if p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ x ^ (1 / 10 : ℝ) < p.1 ∧
      p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧ (p.2.2 : ℝ) < x ^ (1 / 4 : ℝ) ∧
      tripleProduct p ∣ n then Task361.roughIndicator (n / tripleProduct p) p.1 else 0
  have hs : (∑ p ∈ S, f p) =
      ∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
        f (p₁, p₂, p₃) := by
    change (∑ p ∈ range (n + 1) ×ˢ (range (n + 1) ×ˢ range (n + 1)), f p) = _
    simp only [Finset.sum_product]
  change (∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
    f (p₁, p₂, p₃)) = _
  rw [← hs]
  apply sum_congr_of_eq_on_inter
  · intro p hp hnot
    dsimp [f]
    split_ifs with h
    · exfalso
      apply hnot
      apply mem_filter.mpr
      refine ⟨?_, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩
      have hbound (a : ℕ) (ha : (a : ℝ) < x ^ (1 / 4 : ℝ)) :
          a ∈ range (⌊x ^ (1 / 4 : ℝ)⌋₊ + 1) := by
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ha.le))
      have hab : (p.1 : ℝ) < p.2.1 := by exact_mod_cast h.2.2.2.2.1
      have hbc : (p.2.1 : ℝ) < p.2.2 := by exact_mod_cast h.2.2.2.2.2.1
      have h₃ := hbound p.2.2 h.2.2.2.2.2.2.1
      have h₂ := hbound p.2.1 (hbc.trans h.2.2.2.2.2.2.1)
      have h₁ := hbound p.1 ((hab.trans hbc).trans h.2.2.2.2.2.2.1)
      exact mem_product.mpr ⟨h₁, mem_product.mpr ⟨h₂, h₃⟩⟩
    · rfl
  · intro p hp hnot
    split_ifs with hd
    · exfalso
      apply hnot
      have hb := triple_factors_le hn hd
      exact mem_product.mpr ⟨mem_range.mpr (by omega),
        mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩⟩
    · rfl
  · intro p hp hp'
    have h := (mem_filter.mp hp').2
    dsimp [f]
    by_cases hd : tripleProduct p ∣ n
    · rw [if_pos ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2, hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd h.2.2.2.2.2.2.2), if_neg hd]

/-- The exact normalized correction is the sum of its cofactor means.
MMS page 11 equation 5.1 followed by its weighted bottom display. -/
theorem weighted_correction_reindex {x : ℝ} (hx : 1 ≤ x) :
    Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n *
        (Task361.harmanMajorant x n - Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
        (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
      ∑ p ∈ primeTriples x, cofactorMean x p := by
  classical
  have hs : (∑ n ∈ ints x (x + Task379.referenceLength x),
      Task379.referenceWeight x n *
        (Task361.harmanMajorant x n - Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) =
      ∑ p ∈ primeTriples x, ∑ n ∈ ints x (x + Task379.referenceLength x),
        if tripleProduct p ∣ n then Task379.referenceWeight x n *
          Task361.roughIndicator (n / tripleProduct p) p.1 else 0 := by
    calc
      _ = ∑ n ∈ ints x (x + Task379.referenceLength x), ∑ p ∈ primeTriples x,
          if tripleProduct p ∣ n then Task379.referenceWeight x n *
            Task361.roughIndicator (n / tripleProduct p) p.1 else 0 := by
        apply sum_congr rfl
        intro n hn
        have hxn : x ≤ n :=
          (Nat.le_ceil x).trans (by exact_mod_cast (mem_Icc.mp hn).1)
        have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
        rw [harman_correction_reindex x hn0, mul_sum]
        apply sum_congr rfl
        intro p hp
        split_ifs <;> simp
      _ = _ := sum_comm
  rw [hs, mul_sum, sum_div]
  rfl

/-- The exact sealed correction mean limit follows from the independent split.
MMS page 11 bottom Buchstab display, continued on page 12.
CONDITIONAL ON cofactorMean_uniform and cofactorModel_sum_limit.
The finite reindexing and mass bound use no cited input. -/
theorem correctionReferenceMean_limit_supply :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
        Task379.referenceWeight x n *
          (Task361.harmanMajorant x n - Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
          (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) -
            Task571.profileIntegral Task571.buchstabModel| ≤ δ := by
  intro δ hδ
  obtain ⟨X, hX⟩ := cofactor_sum_limit δ hδ
  refine ⟨max 1 X, fun x hx => ?_⟩
  rw [weighted_correction_reindex ((le_max_left _ _).trans hx)]
  exact hX x ((le_max_right _ _).trans hx)

end LeanLab.Ternary.MMS.Task581
