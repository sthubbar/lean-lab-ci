import Mathlib
import LeanLab.Tolev2009.Statements
import LeanLab.Tolev2009.Faithful
import LeanLab.Tolev2009.Displays14to16

open Finset
open LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Displays14to16

namespace LeanLab.Tolev2009.Triad02

theorem sum_union_le_real {α : Type*} [DecidableEq α] {s₁ s₂ : Finset α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x := by
  have H : s₁ ∪ s₂ = s₁ ∪ (s₂ \ s₁) := by ext a; by_cases ha : a ∈ s₁ <;> simp [ha]
  rw [H, sum_union disjoint_sdiff]
  exact add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => hf _))

theorem sum_biUnion_le_real {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset α} {t : α → Finset β}
    {f : β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [biUnion_insert, sum_insert ha]
    calc ∑ x ∈ t a ∪ s.biUnion t, f x
        ≤ ∑ x ∈ t a, f x + ∑ x ∈ s.biUnion t, f x := sum_union_le_real hf
      _ ≤ ∑ x ∈ t a, f x + ∑ i ∈ s, ∑ x ∈ t i, f x := add_le_add le_rfl ih

theorem Ioc_subset_biUnion_Ioc_nat (X : ℕ) :
    Ioc 1 X ⊆ (range (Nat.log 2 X + 1)).biUnion (fun j => Ioc (2 ^ j) (2 ^ (j + 1))) := by
  intro k hk
  rw [mem_Ioc] at hk
  rw [mem_biUnion]
  set j := Nat.log 2 (k - 1)
  have h1 : 2 ^ j ≤ k - 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : k - 1 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by decide) _
  refine ⟨j, ?_, ?_⟩
  · rw [mem_range]
    have : k - 1 ≤ X := by omega
    have : j ≤ Nat.log 2 X := Nat.log_mono_right (by omega)
    omega
  · rw [mem_Ioc]
    have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    omega

theorem sum_Ioc_le_sum_biUnion {X : ℕ} {F : ℕ → ℝ} (hF : ∀ k, 0 ≤ F k) :
    ∑ k ∈ Ioc 1 X, F k ≤ ∑ j ∈ range (Nat.log 2 X + 1), ∑ k ∈ Ioc (2 ^ j) (2 * 2 ^ j), F k := by
  have H : Ioc 1 X ⊆ (range (Nat.log 2 X + 1)).biUnion (fun j => Ioc (2 ^ j) (2 * 2 ^ j)) := by
    intro a ha
    have H2 : a ∈ (range (Nat.log 2 X + 1)).biUnion (fun j => Ioc (2 ^ j) (2 ^ (j + 1))) := Ioc_subset_biUnion_Ioc_nat X ha
    rw [mem_biUnion] at H2 ⊢
    obtain ⟨j, hj1, hj2⟩ := H2
    refine ⟨j, hj1, ?_⟩
    rw [mem_Ioc] at hj2 ⊢
    have h : 2 * 2 ^ j = 2 ^ (j + 1) := by ring
    omega
  calc ∑ k ∈ Ioc 1 X, F k ≤ ∑ k ∈ (range (Nat.log 2 X + 1)).biUnion (fun j => Ioc (2 ^ j) (2 * 2 ^ j)), F k :=
        sum_le_sum_of_subset_of_nonneg H (fun _ _ _ => hF _)
    _ ≤ ∑ j ∈ range (Nat.log 2 X + 1), ∑ k ∈ Ioc (2 ^ j) (2 * 2 ^ j), F k :=
        sum_biUnion_le_real hF

theorem sum_sum_Ioc_le_max_Vblk {X : ℕ} {V : ℕ → ℕ → ℝ} {F : ℕ → ℕ → ℝ}
    (hV : ∀ K₁ K₂, ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂), F k₁ k₂ ≤ V K₁ K₂)
    (hF : ∀ k₁ k₂, 0 ≤ F k₁ k₂) :
    ∃ K₁ K₂, K₁ ∈ (range (Nat.log 2 X + 1)).image (fun j => 2 ^ j) ∧
             K₂ ∈ (range (Nat.log 2 X + 1)).image (fun j => 2 ^ j) ∧
      ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ ≤
        ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 2 * V K₁ K₂ := by
  set M := Nat.log 2 X + 1
  have h1 : ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ ≤
      ∑ j₁ ∈ range M, ∑ k₁ ∈ Ioc (2 ^ j₁) (2 * 2 ^ j₁), ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ :=
    sum_Ioc_le_sum_biUnion (fun k₁ => sum_nonneg (fun k₂ _ => hF k₁ k₂))
  have h2 : ∀ k₁, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ ≤
      ∑ j₂ ∈ range M, ∑ k₂ ∈ Ioc (2 ^ j₂) (2 * 2 ^ j₂), F k₁ k₂ :=
    fun k₁ => sum_Ioc_le_sum_biUnion (fun k₂ => hF k₁ k₂)
  have h3 : ∑ j₁ ∈ range M, ∑ k₁ ∈ Ioc (2 ^ j₁) (2 * 2 ^ j₁), ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ ≤
      ∑ j₁ ∈ range M, ∑ k₁ ∈ Ioc (2 ^ j₁) (2 * 2 ^ j₁), ∑ j₂ ∈ range M, ∑ k₂ ∈ Ioc (2 ^ j₂) (2 * 2 ^ j₂), F k₁ k₂ :=
    sum_le_sum (fun j₁ _ => sum_le_sum (fun k₁ _ => h2 k₁))
  have h4 : ∑ j₁ ∈ range M, ∑ k₁ ∈ Ioc (2 ^ j₁) (2 * 2 ^ j₁), ∑ j₂ ∈ range M, ∑ k₂ ∈ Ioc (2 ^ j₂) (2 * 2 ^ j₂), F k₁ k₂ =
      ∑ j₁ ∈ range M, ∑ j₂ ∈ range M, ∑ k₁ ∈ Ioc (2 ^ j₁) (2 * 2 ^ j₁), ∑ k₂ ∈ Ioc (2 ^ j₂) (2 * 2 ^ j₂), F k₁ k₂ := by
    apply sum_congr rfl
    intro j₁ _
    exact sum_comm
  have h5 : ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ ≤
      ∑ p ∈ (range M) ×ˢ (range M), V (2 ^ p.1) (2 ^ p.2) := by
    calc ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ ≤ _ := h1
      _ ≤ _ := h3
      _ = _ := h4
      _ ≤ ∑ j₁ ∈ range M, ∑ j₂ ∈ range M, V (2 ^ j₁) (2 ^ j₂) := by
        apply sum_le_sum; intro j₁ _
        apply sum_le_sum; intro j₂ _
        exact hV (2 ^ j₁) (2 ^ j₂)
      _ = ∑ p ∈ (range M) ×ˢ (range M), V (2 ^ p.1) (2 ^ p.2) := by
        rw [sum_product]
  have h6 : ∃ p ∈ (range M) ×ˢ (range M),
      ∑ p ∈ (range M) ×ˢ (range M), V (2 ^ p.1) (2 ^ p.2) ≤ (M : ℝ) ^ 2 * V (2 ^ p.1) (2 ^ p.2) := by
    have h_card : (((range M) ×ˢ (range M)).card : ℝ) = (M : ℝ) ^ 2 := by
      rw [card_product, card_range]
      push_cast
      ring
    have hM : 0 < M := Nat.succ_pos _
    have hp : ((range M) ×ˢ (range M)).Nonempty := by
      rw [Finset.Nonempty]
      exact ⟨(0, 0), by simp [hM]⟩
    obtain ⟨pm, hpm, hmax⟩ := exists_max_image ((range M) ×ˢ (range M)) (fun p => V (2 ^ p.1) (2 ^ p.2)) hp
    refine ⟨pm, hpm, ?_⟩
    calc ∑ p ∈ (range M) ×ˢ (range M), V (2 ^ p.1) (2 ^ p.2)
      ≤ ∑ p ∈ (range M) ×ˢ (range M), V (2 ^ pm.1) (2 ^ pm.2) := sum_le_sum hmax
      _ = (((range M) ×ˢ (range M)).card : ℝ) * V (2 ^ pm.1) (2 ^ pm.2) := by simp
      _ = (M : ℝ) ^ 2 * V (2 ^ pm.1) (2 ^ pm.2) := by rw [h_card]
  obtain ⟨p, hp1, hp2⟩ := h6
  refine ⟨2 ^ p.1, 2 ^ p.2, ?_, ?_, ?_⟩
  · rw [mem_image]
    exact ⟨p.1, (mem_product.mp hp1).1, rfl⟩
  · rw [mem_image]
    exact ⟨p.2, (mem_product.mp hp1).2, rfl⟩
  · exact h5.trans hp2

theorem Icc_eq_insert_Ioc (X : ℕ) (h : 1 ≤ X) : Icc 1 X = insert 1 (Ioc 1 X) := by
  ext a
  simp only [mem_Icc, mem_insert, mem_Ioc]
  omega

theorem sum_Icc_eq_add_sum_Ioc {F : ℕ → ℝ} {X : ℕ} (hX : 1 ≤ X) :
    ∑ k ∈ Icc 1 X, F k = F 1 + ∑ k ∈ Ioc 1 X, F k := by
  rw [Icc_eq_insert_Ioc X hX, sum_insert]
  simp

theorem sum_sum_Icc_le_Ioc_add {F : ℕ → ℕ → ℝ} {X : ℕ} (hF : ∀ k₁ k₂, 0 ≤ F k₁ k₂) :
    ∑ k₁ ∈ Icc 1 X, ∑ k₂ ∈ Icc 1 X, F k₁ k₂ ≤
      (∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂) +
      (∑ k₁ ∈ Icc 1 X, F k₁ 1) +
      (∑ k₂ ∈ Icc 1 X, F 1 k₂) := by
  by_cases hX : 1 ≤ X
  · have h1 : ∑ k₁ ∈ Icc 1 X, ∑ k₂ ∈ Icc 1 X, F k₁ k₂ = F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂ + ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Icc 1 X, F k₁ k₂ := by
      rw [sum_Icc_eq_add_sum_Ioc hX]
      have : ∑ k₂ ∈ Icc 1 X, F 1 k₂ = F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂ := sum_Icc_eq_add_sum_Ioc hX
      rw [this]
    have h2 : ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Icc 1 X, F k₁ k₂ = ∑ k₁ ∈ Ioc 1 X, F k₁ 1 + ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ := by
      have : ∀ k₁, ∑ k₂ ∈ Icc 1 X, F k₁ k₂ = F k₁ 1 + ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ := fun _ => sum_Icc_eq_add_sum_Ioc hX
      simp_rw [this, sum_add_distrib]
    have h3 : F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂ + (∑ k₁ ∈ Ioc 1 X, F k₁ 1 + ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂) ≤
        ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ + (F 1 1 + ∑ k₁ ∈ Ioc 1 X, F k₁ 1) + (F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂) := by
      linarith [hF 1 1]
    have h4 : F 1 1 + ∑ k₁ ∈ Ioc 1 X, F k₁ 1 = ∑ k₁ ∈ Icc 1 X, F k₁ 1 := by rw [sum_Icc_eq_add_sum_Ioc hX]
    have h5 : F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂ = ∑ k₂ ∈ Icc 1 X, F 1 k₂ := by rw [sum_Icc_eq_add_sum_Ioc hX]
    rw [h1, h2]
    calc F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂ + (∑ k₁ ∈ Ioc 1 X, F k₁ 1 + ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂)
      ≤ ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ + (F 1 1 + ∑ k₁ ∈ Ioc 1 X, F k₁ 1) + (F 1 1 + ∑ k₂ ∈ Ioc 1 X, F 1 k₂) := h3
      _ = ∑ k₁ ∈ Ioc 1 X, ∑ k₂ ∈ Ioc 1 X, F k₁ k₂ + ∑ k₁ ∈ Icc 1 X, F k₁ 1 + ∑ k₂ ∈ Icc 1 X, F 1 k₂ := by rw [h4, h5]
  · have hX0 : X = 0 := by omega
    subst hX0
    simp

theorem triad02_main (lam : ℕ → ℝ) (l₃ : ℕ) (A : ℝ) (N : ℕ) :
    let L := Real.log N
    let K₁₂ := ⌊Real.sqrt N * L ^ (-(10 ^ 4 * A))⌋₊
    let K₃ := ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * L ^ (-(10 ^ 4 * A))⌋₊
    let M := Nat.log 2 K₁₂ + 1
    let F := fun k₁ k₂ => innerF (fun k l => Rm (Qof A N) (τof A N) k l N) lam l₃ K₃ k₁ k₂
    ∃ K₁ K₂, K₁ ∈ (range M).image (fun j => 2 ^ j) ∧
             K₂ ∈ (range M).image (fun j => 2 ^ j) ∧
      E2 lam l₃ A N ≤ ((M : ℝ) ^ 2 * Vblk (Qof A N) (τof A N) lam l₃ K₃ N K₁ K₂) +
        (∑ k₁ ∈ Icc 1 K₁₂, F k₁ 1) + (∑ k₂ ∈ Icc 1 K₁₂, F 1 k₂) := by
  intro L K₁₂ K₃ M F
  have hV : ∀ K₁ K₂, ∑ k₁ ∈ Ioc K₁ (2 * K₁), ∑ k₂ ∈ Ioc K₂ (2 * K₂),
      F k₁ k₂ ≤ Vblk (Qof A N) (τof A N) lam l₃ K₃ N K₁ K₂ := by
    intro K₁ K₂
    exact le_rfl
  have hF : ∀ k₁ k₂, 0 ≤ F k₁ k₂ := by
    intro k₁ k₂
    exact innerF_nonneg _ _ _ _ _ _
  obtain ⟨K₁, K₂, hK1, hK2, hBound⟩ := sum_sum_Ioc_le_max_Vblk hV hF
  refine ⟨K₁, K₂, hK1, hK2, ?_⟩
  have hE2 : E2 lam l₃ A N = ∑ k₁ ∈ Icc 1 K₁₂, ∑ k₂ ∈ Icc 1 K₁₂, F k₁ k₂ := by
    unfold E2 EF
    rfl
  rw [hE2]
  calc ∑ k₁ ∈ Icc 1 K₁₂, ∑ k₂ ∈ Icc 1 K₁₂, F k₁ k₂
    ≤ (∑ k₁ ∈ Ioc 1 K₁₂, ∑ k₂ ∈ Ioc 1 K₁₂, F k₁ k₂) + (∑ k₁ ∈ Icc 1 K₁₂, F k₁ 1) + (∑ k₂ ∈ Icc 1 K₁₂, F 1 k₂) := sum_sum_Icc_le_Ioc_add hF
    _ ≤ ((M : ℝ) ^ 2 * Vblk (Qof A N) (τof A N) lam l₃ K₃ N K₁ K₂) + (∑ k₁ ∈ Icc 1 K₁₂, F k₁ 1) + (∑ k₂ ∈ Icc 1 K₁₂, F 1 k₂) := by
      gcongr

theorem triad02_instance :
    let L := Real.log 16
    let K₁₂ := ⌊Real.sqrt 16 * L ^ (-(10 ^ 4 * (1:ℝ)))⌋₊
    let K₃ := ⌊(16 : ℝ) ^ ((1 : ℝ) / 3) * L ^ (-(10 ^ 4 * (1:ℝ)))⌋₊
    let M := Nat.log 2 K₁₂ + 1
    let F := fun k₁ k₂ => innerF (fun k l => Rm (Qof 1 16) (τof 1 16) k l 16) (fun _ => 0) 1 K₃ k₁ k₂
    ∃ K₁ K₂, K₁ ∈ (range M).image (fun j => 2 ^ j) ∧
             K₂ ∈ (range M).image (fun j => 2 ^ j) ∧
      E2 (fun _ => 0) 1 1 16 ≤ ((M : ℝ) ^ 2 * Vblk (Qof 1 16) (τof 1 16) (fun _ => 0) 1 K₃ 16 K₁ K₂) +
        (∑ k₁ ∈ Icc 1 K₁₂, F k₁ 1) + (∑ k₂ ∈ Icc 1 K₁₂, F 1 k₂) :=
  triad02_main (fun _ => 0) 1 1 16

end LeanLab.Tolev2009.Triad02
