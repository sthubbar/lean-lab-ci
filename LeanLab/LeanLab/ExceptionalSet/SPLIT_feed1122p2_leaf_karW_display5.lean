import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_karW_display8

/-!
Split of `leaf_karW_display5` of `LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_karW_display8`,
burst-20261122 wave 13, session S132. A. A. Karacuba, Trudy Mat. Inst. Steklov 112 (1971), p. 246,
display (5).

Pieces, with `a_y = |Σ_{z ≤ M} e(c + Σ_j B_j (yz)^j)|`.
* `karW_holder_y`, Lemma 4 a for the power `2k` over `y`: `(Σ_y a_y)^{2k} ≤ (M+1)^{2k-1} Σ_y a_y^{2k}`,
  proved from Mathlib's power mean inequality.
* `leaf_karW_display5_inner`, the rest of p. 246: the expansion of `a_y^{2k}` through `J_k(λ)`,
  Lemma 4 b with weights `J_k(λ)`, `Σ_λ J_k(λ) = (M+1)^{2k}`, `J_k(λ) ≤ J_k(0)` and the second
  expansion, giving `(Σ_y a_y^{2k})^{2k} ≤ (M+1)^{4k²-2k} J_k(0)² ∏_s 𝔖_s`. LEAF, HARD.
* `leaf_karW_display5_of_leaves`, the exact statement of `leaf_karW_display5`, proved.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- Lemma 4 a of Karacuba p. 243 for the power `2k` over `0 ≤ y ≤ M`, the power mean inequality. -/
theorem karW_holder_y (M k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ha : ∀ y, 0 ≤ a y) :
    (∑ y ∈ Finset.range (M + 1), a y) ^ (2 * k)
      ≤ ((M : ℝ) + 1) ^ (2 * k - 1) * ∑ y ∈ Finset.range (M + 1), a y ^ (2 * k) := by
  have h := _root_.pow_sum_div_card_le_sum_pow (s := Finset.range (M + 1)) (f := a)
    (fun y _ => ha y) (2 * k - 1)
  have e : 2 * k - 1 + 1 = 2 * k := by omega
  rw [e, Finset.card_range] at h
  have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) ^ (2 * k - 1) := by positivity
  rw [div_le_iff₀ hM] at h
  push_cast at h
  linarith

/-- LEAF: the rest of display (5) of Karacuba p. 246, class HARD. With
`a_y = |Σ_{z ≤ M} e(c + Σ_j B_j (yz)^j)|` and `J_k(0) = ∫_{[0,1]^n} |Σ_{y ≤ M} e(α_1 y + ... + α_n y^n)|^{2k}`:
`(Σ_y a_y^{2k})^{2k} ≤ (M+1)^{4k²-2k} J_k(0)² ∏_{s=1}^n Σ_{|μ| ≤ kM^s} |Σ_{|λ| ≤ kM^s} e(B_s λ μ)|`.
Steps: `a_y^{2k} = |Σ_λ J_k(λ) e(Σ_j B_j y^j λ_j)|`; Lemma 4 b with weights `J_k(λ)` and
`Σ_λ J_k(λ) = (M+1)^{2k}`; `J_k(λ) ≤ J_k(0)`; the second expansion over `μ` and `|λ_s| ≤ kM^s`. -/
theorem leaf_karW_display5_inner (n k M : ℕ) (hk : 1 ≤ k) (c : ℝ) (B : ℕ → ℝ) :
    (∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)) ^ (2 * k)
      ≤ ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) *
        (∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)) ^ 2 *
        ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ := by
  sorry

/-- The exact statement of `leaf_karW_display5`, from the pieces. -/
theorem leaf_karW_display5_of_leaves (n k M : ℕ) (hk : 1 ≤ k) (c : ℝ) (B : ℕ → ℝ) :
    ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (4 * k ^ 2)
      ≤ ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) *
        (∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)) ^ 2 *
        ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ := by
  set a : ℕ → ℝ := fun y => ‖∑ z ∈ Finset.range (M + 1),
      eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ with ha
  set R : ℝ := (∫ α in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
          ‖∑ y ∈ Finset.range (M + 1), eC (∑ j : Fin n, α j * (y : ℝ) ^ ((j : ℕ) + 1))‖ ^ (2 * k)) ^ 2 *
        ∏ s ∈ Finset.Icc 1 n, ∑ μ ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
          ‖∑ t ∈ Finset.Icc (-((k * M ^ s : ℕ) : ℤ)) ((k * M ^ s : ℕ) : ℤ),
            eC (B s * (t : ℝ) * (μ : ℝ))‖ with hR
  have hinner : (∑ y ∈ Finset.range (M + 1), a y ^ (2 * k)) ^ (2 * k)
      ≤ ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) * R := by
    have := leaf_karW_display5_inner n k M hk c B
    simpa only [ha, hR, mul_assoc] using this
  have hW : ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖
      ≤ ∑ y ∈ Finset.range (M + 1), a y := norm_sum_le _ _
  have hm1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [M.cast_nonneg (α := ℝ)]
  have hW2 : ‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)
      ≤ ((M : ℝ) + 1) ^ (2 * k - 1) * ∑ y ∈ Finset.range (M + 1), a y ^ (2 * k) :=
    (pow_le_pow_left₀ (norm_nonneg _) hW _).trans
      (karW_holder_y M k hk a (fun y => norm_nonneg _))
  have he : 4 * k ^ 2 = 2 * k * (2 * k) := by ring
  rw [he, pow_mul]
  have hS0 : 0 ≤ ∑ y ∈ Finset.range (M + 1), a y ^ (2 * k) :=
    Finset.sum_nonneg (fun y _ => pow_nonneg (norm_nonneg _) _)
  calc (‖∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)) ^ (2 * k)
      ≤ (((M : ℝ) + 1) ^ (2 * k - 1) * ∑ y ∈ Finset.range (M + 1), a y ^ (2 * k)) ^ (2 * k) :=
        pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) hW2 _
    _ = ((M : ℝ) + 1) ^ ((2 * k - 1) * (2 * k)) *
          (∑ y ∈ Finset.range (M + 1), a y ^ (2 * k)) ^ (2 * k) := by
        rw [mul_pow, ← pow_mul]
    _ ≤ ((M : ℝ) + 1) ^ ((2 * k - 1) * (2 * k)) * (((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) * R) := by
        gcongr
    _ = ((M : ℝ) + 1) ^ (8 * k ^ 2 - 4 * k) * R := by
        rw [← mul_assoc, ← pow_add]
        congr 2
        have h1 : 2 * k - 1 + 1 = 2 * k := by omega
        zify [show 1 ≤ 2 * k by omega, show 2 * k ≤ 4 * k ^ 2 by nlinarith,
          show 4 * k ≤ 8 * k ^ 2 by nlinarith]
        ring
    _ = _ := by rw [hR]; ring

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
