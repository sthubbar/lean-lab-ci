/-
P0068 Zhan 1991, page 268 second and third lines of the proof of Proposition 3, read for (3.12)
by page 269: the LEAF `mv_FJ_312_leaf_S9` of SPLIT_prop3_312_S9.lean split into the cited
Lemma 6, already the LEAF `zhan_lemma6_leaf` of SPLIT_theorem2_1122.lean, and one new LEAF for
the Dirichlet polynomial `F_J` and the divisor moment bounds (3.13). Burst 20261124, session S9,
unit C-extra-3. Source: papers/P0068.pdf, journal pages 262, 266 and 268, pdf pages 4, 8 and 10.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.Cauchy312Proof_S9

namespace LeanLab.Zhan1991
open Finset Real MeasureTheory

noncomputable section

/-- Each factor `fj` is a finite Dirichlet polynomial with support in `(N_j, 2N_j]` and
coefficients bounded by `log N`. -/
theorem fj_single_poly_S9 :
    ∃ c1 N₀ : ℝ, 0 ≤ c1 ∧ ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (j : Fin 20),
      N₀ ≤ N → Cond35 N Nv →
      ∃ (Mj Nj : ℕ) (a : ℕ → ℂ),
        (∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ),
          fj (j.val + 1) (Nv j) χ s =
            ∑ n ∈ Finset.Icc (Mj + 1) (Mj + Nj), a n * χ n * (n : ℂ) ^ (-s)) ∧
        (∀ n, ‖a n‖ ≤ Real.log N ^ c1) ∧
        (Nj : ℝ) ≤ Nv j ∧ ((Mj + Nj : ℝ) ≤ 2 * Nv j) := by
  sorry

/-- Product of the single-factor polynomials: the product over `j ∈ J` of `fj` is a
Dirichlet polynomial with coefficients bounded by a power of the divisor function. -/
theorem prod_fj_poly_S9 :
    ∃ c1 N₀ : ℝ, 0 ≤ c1 ∧ ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)),
      N₀ ≤ N → Cond35 N Nv →
      ∃ (M Nn : ℕ) (b : ℕ → ℂ),
        (∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ),
          ∏ j ∈ J, fj (j.val + 1) (Nv j) χ s =
            ∑ n ∈ Finset.Icc (M + 1) (M + Nn), b n * χ n * (n : ℂ) ^ (-s)) ∧
        (∀ n, ‖b n‖ ≤ (Real.log N ^ c1) * (((Nat.divisors n).card : ℝ) ^ J.card)) ∧
        ((M + Nn : ℝ) ≤ (2 : ℝ) ^ J.card * ∏ j ∈ J, Nv j) := by
  sorry

/-- Divisor moment bound sufficient for k ≤ 20. -/
theorem divisor_moment_S9 (k : ℕ) (hk : k ≤ 20) :
    ∃ c K N₀ : ℝ, 0 ≤ c ∧ ∀ (q : ℕ) (T X : ℝ), 1 ≤ T → N₀ ≤ X →
      ∑ n ∈ Finset.Icc 1 (Nat.floor X),
        ((q : ℝ) * T + n) * (((Nat.divisors n).card : ℝ) ^ (2 * k)) *
          (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
      ≤ K * ((q : ℝ) * T + X) * Real.log X ^ c := by
  sorry

/-- LEAF: page 268 second line with page 266 display (3.13): `F_J = Π_{j ∈ J} f_j` is a
Dirichlet polynomial `Σ_{M < n ≤ M + N'} b(n) χ(n) n^{-s}`, `b(n) = Σ_{n = Π n_j, n_j ∈ I_j}
Π a_j(n_j)`, so `|b(n)| ≤ d_{|J|}(n) L`, `n ≤ 2^{|J|} Π_{j ∈ J} N_j`; and (3.13) gives
`Σ (qT + n) |b(n)|² n⁻¹ ≪ (qT + Π_{j ∈ J} N_j) L^{c₀}` for `T ≥ 1`. The exponent `c₀` of the
paper is named `c7`. Class MEDIUM. -/
theorem FJ_dirpoly_312_leaf_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)), N₀ ≤ N → Cond35 N Nv →
    ∃ (M Nn : ℕ) (b : ℕ → ℂ),
      (∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ),
        ∏ j ∈ J, fj (j.val + 1) (Nv j) χ s
          = ∑ n ∈ Finset.Icc (M + 1) (M + Nn), b n * χ n * (n : ℂ) ^ (-s)) ∧
      ∀ (q : ℕ) (T : ℝ), 1 ≤ T →
        ∑ n ∈ Finset.Icc (M + 1) (M + Nn), ((q : ℝ) * T + n) * ‖b n‖ ^ 2 *
            (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
          ≤ K * ((q : ℝ) * T + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  sorry

/-- PROVED: `(T₂, 2T₂]` as an interval of length `|T₂|` starting at `min(T₂, 2T₂)`. -/
theorem uIoc_eq_312_S9 (T2 : ℝ) :
    Set.uIoc T2 (2 * T2) = Set.Ioc (min T2 (2 * T2)) (min T2 (2 * T2) + |T2|) := by
  rcases le_total 0 T2 with h | h
  · rw [Set.uIoc_of_le (by linarith), abs_of_nonneg h, min_eq_left (by linarith)]
    congr 1; ring
  · rw [Set.uIoc_of_ge (by linarith), abs_of_nonpos h, min_eq_right (by linarith)]
    congr 1; ring

/-- PROVED from Lemma 6, `zhan_lemma6_leaf`, and `FJ_dirpoly_312_leaf_S9`: the statement of
the LEAF `mv_FJ_312_leaf_S9`, page 268, over `[T₂, 2T₂]`. Same statement. -/
theorem mv_FJ_312_of_lemma6_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (T2 : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 ≤ |T2| →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖∏ j ∈ J, fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * ((q : ℝ) * |T2| + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  obtain ⟨K6, h6⟩ := zhan_lemma6_leaf
  obtain ⟨c7, hc7, K, N0, hD⟩ := FJ_dirpoly_312_leaf_S9
  refine ⟨c7, hc7, max K6 0 * K, N0, ?_⟩
  intro N q _ Nv J T2 hN hC hT
  obtain ⟨M, Nn, b, hrep, hb⟩ := hD N Nv J hN hC
  set U := min T2 (2 * T2) with hU
  have hL6 := h6 q M Nn b |T2| U (1 / 2) hT
  set g : DirichletCharacter ℂ q → ℝ → ℝ := fun χ t =>
    ‖∏ j ∈ J, fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2 with hg
  have hgc : ∀ χ, Continuous (g χ) := fun χ => (prodFJ_continuous_312_S9 Nv J χ).norm.pow 2
  have hg0 : ∀ χ t, 0 ≤ g χ t := fun χ t => by positivity
  have hgr : ∀ χ t, g χ t = ‖∑ n ∈ Finset.Icc (M + 1) (M + Nn), b n * χ n *
      (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * Complex.I))‖ ^ 2 := by
    intro χ t
    simp only [hg]
    rw [hrep q χ]
    push_cast
    rfl
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc (M + 1) (M + Nn), ((q : ℝ) * |T2| + n) * ‖b n‖ ^ 2 *
      (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  have hle : ∀ χ, ∫ t in Set.uIoc T2 (2 * T2), g χ t = ∫ t in U..(U + |T2|), g χ t := by
    intro χ
    rw [intervalIntegral.integral_of_le (by linarith [abs_nonneg T2]), uIoc_eq_312_S9]
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2), g χ t
        = ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in U..(U + |T2|), g χ t := Finset.sum_congr rfl (fun χ _ => hle χ)
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ∫ t in U..(U + |T2|), g χ t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun χ _ _ => intervalIntegral.integral_nonneg (by linarith [abs_nonneg T2])
            (fun t _ => hg0 χ t))
    _ = ∫ t in U..(U + |T2|), ∑ χ : DirichletCharacter ℂ q, g χ t :=
        (intervalIntegral.integral_finset_sum
          (fun χ _ => (hgc χ).intervalIntegrable _ _)).symm
    _ = ∫ t in U..(U + |T2|), ∑ χ : DirichletCharacter ℂ q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + Nn), b n * χ n *
            (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * Complex.I))‖ ^ 2 := by
        congr 1; funext t; exact Finset.sum_congr rfl (fun χ _ => hgr χ t)
    _ ≤ K6 * ∑ n ∈ Finset.Icc (M + 1) (M + Nn), ((q : ℝ) * |T2| + n) * ‖b n‖ ^ 2 *
          (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) := hL6
    _ ≤ max K6 0 * ∑ n ∈ Finset.Icc (M + 1) (M + Nn), ((q : ℝ) * |T2| + n) * ‖b n‖ ^ 2 *
          (n : ℝ) ^ (-2 * (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    _ ≤ max K6 0 * (K * ((q : ℝ) * |T2| + ∏ j ∈ J, Nv j) * Real.log N ^ c7) :=
        mul_le_mul_of_nonneg_left (hb q |T2| hT) (le_max_right _ _)
    _ = _ := by ring

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.uIoc_eq_312_S9
#print axioms LeanLab.Zhan1991.mv_FJ_312_of_lemma6_S9