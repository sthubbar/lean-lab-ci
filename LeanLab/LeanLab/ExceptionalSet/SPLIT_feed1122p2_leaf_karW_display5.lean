import LeanLab.ExceptionalSet.SPLIT_feed1122_leaf_karW_display8
import LeanLab.ExceptionalSet.KaracubaJIntegral

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

private theorem karW_sum_range_eq_fin (P : ℕ) {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) : ∑ i ∈ Finset.range P, f i = ∑ x : Fin P, f x.val := by
  rw [Finset.sum_range, Fin.sum_univ_eq_sum_range f P]

private theorem karW_group_sum (n k M : ℕ) (F : (Fin n → ℤ) → ℝ) :
    (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        F (karPowVec n k M u - karPowVec n k M v)) =
      ∑ lam ∈ karBox n k M,
        (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          if karPowVec n k M u - karPowVec n k M v = lam then (1 : ℝ) else 0) * F lam := by
  classical
  set A := karPowVec n k M with hA
  have hpt : ∀ u v, F (A u - A v) =
      ∑ lam ∈ karBox n k M,
        (if A u - A v = lam then (1 : ℝ) else 0) * F lam := by
    intro u v
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, if_pos (karPowVec_sub_mem_box n k M u v)]
  calc
    ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1), F (A u - A v)
        = ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
            ∑ lam ∈ karBox n k M, (if A u - A v = lam then (1 : ℝ) else 0) * F lam := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          exact hpt u v
    _ = ∑ u : Fin k → Fin (M + 1), ∑ lam ∈ karBox n k M,
            ∑ v : Fin k → Fin (M + 1), (if A u - A v = lam then (1 : ℝ) else 0) * F lam := by
          apply Finset.sum_congr rfl
          intro u _
          rw [Finset.sum_comm]
    _ = ∑ lam ∈ karBox n k M, ∑ u : Fin k → Fin (M + 1),
            ∑ v : Fin k → Fin (M + 1), (if A u - A v = lam then (1 : ℝ) else 0) * F lam := by
          rw [Finset.sum_comm]
    _ = ∑ lam ∈ karBox n k M,
          (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
            if A u - A v = lam then (1 : ℝ) else 0) * F lam := by
          refine Finset.sum_congr rfl fun lam _ => ?_
          simp only [Finset.sum_mul]

private theorem karW_count_sum (n k M : ℕ) :
    (∑ lam ∈ karBox n k M,
      (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        if karPowVec n k M u - karPowVec n k M v = lam then (1 : ℝ) else 0))
      = ((M : ℝ) + 1) ^ (2 * k) := by
  have hg := karW_group_sum n k M (fun _ => (1 : ℝ))
  calc
    (∑ lam ∈ karBox n k M,
      (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
        if karPowVec n k M u - karPowVec n k M v = lam then (1 : ℝ) else 0))
      = ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1), (1 : ℝ) := by
        simpa using hg.symm
    _ = ((M : ℝ) + 1) ^ (2 * k) := by
        simp [Fintype.card_fun, Fintype.card_fin]
        push_cast
        rw [← pow_add]
        congr 1
        omega

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
  classical
  set cnt : (Fin n → ℤ) → ℝ := fun lam =>
    ∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
      if karPowVec n k M u - karPowVec n k M v = lam then (1 : ℝ) else 0 with hcnt
  have hcnt0 : ∀ lam, 0 ≤ cnt lam := by
    intro lam
    unfold cnt
    refine Finset.sum_nonneg fun u _ => ?_
    refine Finset.sum_nonneg fun v _ => ?_
    split_ifs <;> norm_num
  have hphase : ∀ (y : ℕ) (u v : Fin k → Fin (M + 1)),
      (∑ j ∈ Finset.Icc 1 n, B j * y ^ j *
        ((∑ i : Fin k, ((u i : ℕ) : ℝ) ^ j) -
          (∑ i : Fin k, ((v i : ℕ) : ℝ) ^ j))) =
        ∑ j : Fin n, B ((j : ℕ) + 1) * (y : ℝ) ^ ((j : ℕ) + 1) *
          ((karPowVec n k M u - karPowVec n k M v) j : ℝ) := by
    intro y u v
    simp only [karPowVec, Pi.sub_apply, karW_sum_Icc_fin]
    push_cast
    simp only [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
  set T : ℕ → (Fin n → ℤ) → ℂ := fun y lam =>
    eC (∑ j : Fin n, B ((j : ℕ) + 1) * (y : ℝ) ^ ((j : ℕ) + 1) * (lam j : ℝ)) with hT
  have hTsum : ∀ lam, (∑ y ∈ Finset.range (M + 1), T y lam) = karSy n M B lam := by
    intro lam
    rw [karW_sum_range_eq_fin]
    unfold karSy
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hz (y : ℕ) :
      (∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))) =
        ∑ z : Fin (M + 1),
          eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y : ℝ) * (z : ℕ)) ^ j)) := by
    rw [karW_sum_range_eq_fin]
    apply Finset.sum_congr rfl
    intro z _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have hrowgrp (y : ℕ) :
      ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k) =
        (∑ lam ∈ karBox n k M, cnt lam * T y lam).re := by
    rw [hz y]
    have hrow := leafW_polynomial_row_moment n M k y c B
    rw [hrow]
    have huv : ∀ u v : Fin k → Fin (M + 1),
        eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j *
          ((∑ i : Fin k, ((u i : ℕ) : ℝ) ^ j) -
            (∑ i : Fin k, ((v i : ℕ) : ℝ) ^ j))) = T y (karPowVec n k M u - karPowVec n k M v) := by
      intro u v
      unfold T
      congr 1
      exact hphase y u v
    have hg := karW_group_sum n k M (fun lam => T y lam)
    calc
      (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
          eC (∑ j ∈ Finset.Icc 1 n, B j * (y : ℝ) ^ j *
            ((∑ i : Fin k, ((u i : ℕ) : ℝ) ^ j) -
              (∑ i : Fin k, ((v i : ℕ) : ℝ) ^ j)))).re
          = (∑ u : Fin k → Fin (M + 1), ∑ v : Fin k → Fin (M + 1),
              T y (karPowVec n k M u - karPowVec n k M v)).re := by
            congr 1
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro v _
            exact huv u v
      _ = (∑ lam ∈ karBox n k M, cnt lam * T y lam).re := by rw [hg]
  have hrowle (y : ℕ) :
      ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)
        ≤ ∑ lam ∈ karBox n k M, cnt lam * ‖T y lam‖ := by
    rw [hrowgrp y]
    calc
      (∑ lam ∈ karBox n k M, cnt lam * T y lam).re
          ≤ ‖∑ lam ∈ karBox n k M, cnt lam * T y lam‖ := Complex.re_le_norm _
      _ ≤ ∑ lam ∈ karBox n k M, ‖cnt lam * T y lam‖ := norm_sum_le _ _
      _ = ∑ lam ∈ karBox n k M, cnt lam * ‖T y lam‖ := by
            apply Finset.sum_congr rfl
            intro lam _
            rw [norm_mul, abs_of_nonneg (hcnt0 lam)]
  have hS :
      (∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
        eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k))
        ≤ ∑ lam ∈ karBox n k M, cnt lam * ‖∑ y ∈ Finset.range (M + 1), T y lam‖ := by
    calc
      (∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
          eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k))
          ≤ ∑ y ∈ Finset.range (M + 1), ∑ lam ∈ karBox n k M, cnt lam * ‖T y lam‖ :=
            Finset.sum_le_sum fun y _ => hrowle y
      _ = ∑ lam ∈ karBox n k M, cnt lam * (∑ y ∈ Finset.range (M + 1), ‖T y lam‖) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro lam _
            rw [Finset.mul_sum]
      _ ≤ ∑ lam ∈ karBox n k M, cnt lam * ‖∑ y ∈ Finset.range (M + 1), T y lam‖ := by
            refine Finset.sum_le_sum fun lam _ => ?_
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hcnt0 lam)
  have hholder := holder_weighted (s := karBox n k M) (k := 2 * k) (by omega)
    (u := cnt) (v := fun lam => ‖∑ y ∈ Finset.range (M + 1), T y lam‖)
    hcnt0 (fun _ => norm_nonneg _)
  have hcount := karW_count_sum n k M
  have hS0 : 0 ≤ ∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
      eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k) :=
    Finset.sum_nonneg fun y _ => positivity
  have hmain : (∑ y ∈ Finset.range (M + 1), ‖∑ z ∈ Finset.range (M + 1),
      eC (c + ∑ j ∈ Finset.Icc 1 n, B j * (((y * z : ℕ) : ℝ) ^ j))‖ ^ (2 * k)) ^ (2 * k)
      ≤ ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) *
        (∑ lam ∈ karBox n k M, cnt lam * ‖∑ y ∈ Finset.range (M + 1), T y lam‖ ^ (2 * k)) := by
    calc
      _ ^ (2 * k) ≤ (∑ lam ∈ karBox n k M, cnt lam * ‖∑ y ∈ Finset.range (M + 1), T y lam‖) ^ (2 * k) :=
        pow_le_pow_left₀ hS0 hS _
      _ ≤ (∑ lam ∈ karBox n k M, cnt lam) ^ (2 * k - 1) *
          ∑ lam ∈ karBox n k M, cnt lam * ‖∑ y ∈ Finset.range (M + 1), T y lam‖ ^ (2 * k) :=
        hholder
      _ = ((M : ℝ) + 1) ^ (4 * k ^ 2 - 2 * k) *
          (∑ lam ∈ karBox n k M, cnt lam * ‖∑ y ∈ Finset.range (M + 1), T y lam‖ ^ (2 * k)) := by
        rw [hcount]
        rw [← pow_mul]
        congr 1
        omega
  trace_state
  nlinarith

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
