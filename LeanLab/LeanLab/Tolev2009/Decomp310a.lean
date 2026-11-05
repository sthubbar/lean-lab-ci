/-
AI wrote this Lean code. Codex task310.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98.
Adapted to https://arxiv.org/abs/0902.2669 page 4 display 12.
All analytic leaves remain OPEN. Assemblies are CONDITIONAL.
-/
import LeanLab.Tolev2009.Decomp286b

open Finset Real

namespace LeanLab.Tolev2009.Decomp310a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b

/-- The inner row after removing a m, Tolev 1999 page 86 display 64.
The product truncation and fixed residue are those of the sealed bilinear block. -/
noncomputable def row (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ)
    (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      b l * ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
    else 0

/-- Removing the first coefficient gives the row form of display 64. -/
theorem bilinear_eq_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) :
    bilinear lam l₃ K N α x M M₁ H H₁ a b =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m := by
  unfold bilinear row
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  split_ifs <;> ring

/-- The coefficient free majorant in display 64. No minor arc input is used. -/
theorem bilinear_norm_le_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) :
    ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ≤
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        ((tau5 m : ℝ) * Real.log N) * ‖row lam l₃ K N α x H H₁ b m‖ := by
  rw [bilinear_eq_rows]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro m hm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha m) (norm_nonneg _)

/-- The exact discrete Abel identity behind Tolev 1999 page 86 display 66.
It reduces each logarithmic row to constant rows with truncated upper endpoints.
No minor arc assumption or analytic row bound is used. -/
theorem logarithmic_row_by_parts (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ) (m : ℕ)
    (hHH : ⌊H⌋₊ < ⌊H₁⌋₊) :
    row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m =
      (Real.log ⌊H₁⌋₊ : ℂ) * row lam l₃ K N α x H H₁ (fun _ => 1) m -
      ∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          row lam l₃ K N α x H (l : ℝ) (fun _ => 1) m := by
  let c : ℕ → ℂ := fun l =>
    if ⌊H⌋₊ < l then
      if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
        ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
      else 0
    else 0
  have hG : ∀ t : ℕ, ∑ l ∈ range (t + 1), c l =
      row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m := by
    intro t
    have hs : (range (t + 1)).filter (fun l => ⌊H⌋₊ < l) = Ioc ⌊H⌋₊ t := by
      ext l
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    simp only [c]
    rw [← sum_filter, hs]
    simp only [row, Nat.floor_natCast, one_mul]
  have hG0 : ∑ l ∈ range (⌊H⌋₊ + 1), c l = 0 := by
    rw [hG]
    simp only [row, Nat.floor_natCast, Ioc_self, sum_empty]
  have hh := sum_Ioc_by_parts (fun l : ℕ => (Real.log l : ℂ)) c hHH
  rw [hG0, smul_zero, sub_zero] at hh
  simp only [smul_eq_mul] at hh
  have hlhs : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (Real.log l : ℂ) * c l) =
      row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m := by
    unfold row
    apply sum_congr rfl
    intro l hl
    simp only [c, ite_eq_left (mem_Ioc.mp hl).1]
    split_ifs <;> ring
  rw [hlhs] at hh
  simp_rw [hG] at hh
  simpa only [row, Nat.floor_natCast] using hh

/-- The geometric progression step of Tolev 1999 page 86 display 64 and page 72 Lemma 6.
The denominator is kept as the exact complex distance from one.
No torus distance comparison or averaged Diophantine estimate is asserted. -/
theorem progression_phase_bound (β θ : ℝ) (J : ℕ) (hθ : ee θ ≠ 1) :
    ‖∑ j ∈ range J, ee (β + (j : ℝ) * θ)‖ ≤
      min (J : ℝ) (2 / ‖ee θ - 1‖) := by
  have he : ∀ j : ℕ, ee (β + (j : ℝ) * θ) = ee β * ee θ ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [show β + ((j : ℝ) * θ + θ) = (β + (j : ℝ) * θ) + θ by ring, ee_add, ih, pow_succ]
      ring
  apply le_min
  · apply (norm_sum_le _ _).trans_eq
    simp only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have hs : (∑ j ∈ range J, ee (β + (j : ℝ) * θ)) = ee β * ∑ j ∈ range J, ee θ ^ j := by
      rw [mul_sum]
      exact sum_congr rfl (fun j hj => he j)
    rw [hs, norm_mul, norm_ee, one_mul, geom_sum_eq hθ J, norm_div]
    have hn : ‖ee θ ^ J - 1‖ ≤ 2 := by
      simpa only [norm_pow, norm_ee, one_pow, norm_one, one_add_one_eq_two] using
        norm_sub_le (ee θ ^ J) 1
    exact div_le_div_of_nonneg_right hn (norm_nonneg _)

open LeanLab.HeathBrown1985

/-- The reciprocal divisor moment used in Tolev 1999 page 72 Lemma 8 part iii.
At r equal to twelve it supplies the Cauchy factor in page 86 display 65. -/
theorem divisor_power_reciprocal (r N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤ Hn N ^ (2 ^ r) := by
  induction r generalizing N with
  | zero => simp [Hn]
  | succ r ih =>
    have hh := LeanLab.Tolev2009.DivisorMoment.reciprocal_step N r (2 ^ r) (fun M hM => ih M)
    simpa only [pow_succ, Nat.mul_comm] using hh

/-- LEAF. Tolev 1999 page 86 display 65, the unweighted inner progression sum.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. OPEN. -/
theorem constant_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  sorry

/-- LEAF. Tolev 1999 page 86 display 66, the Abel summation variant.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. OPEN. -/
theorem logarithmic_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  sorry

/-- The exact sealed Type I statement follows from the two row majorants.
CONDITIONAL ON constant_rows and logarithmic_rows. -/
theorem typeI_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ))) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := constant_rows A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := logarithmic_rows A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize a b ha hb
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  apply (bilinear_norm_le_rows lam l₃ _ N α x M M₁ H H₁ a b ha).trans
  rcases hb with rfl | rfl
  · apply (h₁ N hodd hN₁ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · apply (h₂ N hodd hN₂ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)

end LeanLab.Tolev2009.Decomp310a
