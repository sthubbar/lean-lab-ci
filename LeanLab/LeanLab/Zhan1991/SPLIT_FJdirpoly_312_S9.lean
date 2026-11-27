/-
P0068 Zhan 1991, page 268 second line with page 266 display (3.13), read for (3.12) by page 269:
the LEAF `FJ_dirpoly_312_leaf_S9` of SPLIT_mvFJ_312_S9.lean split into the algebraic expansion
of `F_J = Π_{j ∈ J} f_j` as a Dirichlet polynomial, PROVED, and one new LEAF, the coefficient
moment bound from (3.13). Burst 20261124, session S9, unit C-extra-4. Source: papers/P0068.pdf,
journal pages 266 and 268, pdf pages 8 and 10. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_mvFJ_312_S9

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- The coefficient `b(m) = Σ_{m = Π n_j, n_j ∈ I_j} Π_{j ∈ J} a_j(n_j)` of
`F_J = Π_{j ∈ J} f_j`, page 268 second line with (3.6) of page 264; `Nv j` is `N_{j+1}`. -/
def bFJ312 (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (m : ℕ) : ℂ :=
  ∑ p ∈ (J.pi (fun j => dyad (Nv j))).filter (fun p => ∏ x ∈ J.attach, p x x.2 = m),
    ∏ x ∈ J.attach, aj (x.val.val + 1) (p x x.2)

/-- LEAF: page 268 second and third lines with page 266 display (3.13): `|b(n)| ≤ d_{|J|}(n) L`,
`b(n) = 0` unless `n ≤ Π_{j ∈ J} 2N_j`, and the divisor moment bounds (3.13) give
`Σ_{n ≤ Π ⌊2N_j⌋} (qT + n) |b(n)|² n⁻¹ ≪ (qT + Π_{j ∈ J} N_j) L^{c₀}` for `T ≥ 1`.
The exponent `c₀` of the paper is named `c7`. Class MEDIUM. -/
theorem coeff313_312_leaf_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)), N₀ ≤ N → Cond35 N Nv →
      ∀ (q : ℕ) (T : ℝ), 1 ≤ T →
        ∑ n ∈ Finset.Icc 1 (∏ j ∈ J, ⌊2 * Nv j⌋₊), ((q : ℝ) * T + n) * ‖bFJ312 Nv J n‖ ^ 2 *
            (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
          ≤ K * ((q : ℝ) * T + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  sorry

/-- PROVED: `(Π f_i)^z = Π f_i^z` for natural numbers `f_i`. -/
theorem natCast_prod_cpow_S9 {ι : Type*} (s : Finset ι) (f : ι → ℕ) (z : ℂ) :
    ((∏ i ∈ s, f i : ℕ) : ℂ) ^ z = ∏ i ∈ s, ((f i : ℕ) : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

/-- PROVED: a product of finite Dirichlet series with character `χ` over positive integers
`n ≤ B_i` is the Dirichlet series over `1 ≤ m ≤ Π B_i` with the convolved coefficients. -/
theorem prod_dirpoly_S9 {ι : Type*} [DecidableEq ι] {q : ℕ} (s : Finset ι) (t : ι → Finset ℕ)
    (B : ι → ℕ) (ht : ∀ i, ∀ n ∈ t i, 1 ≤ n ∧ n ≤ B i) (c : ι → ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (z : ℂ) :
    ∏ i ∈ s, ∑ n ∈ t i, c i n * χ n * (n : ℂ) ^ (-z)
      = ∑ m ∈ Finset.Icc 1 (∏ i ∈ s, B i),
          (∑ p ∈ (s.pi t).filter (fun p => ∏ x ∈ s.attach, p x x.2 = m),
            ∏ x ∈ s.attach, c x (p x x.2)) * χ m * (m : ℂ) ^ (-z) := by
  rw [Finset.prod_sum]
  have hmap : ∀ p ∈ s.pi t, (∏ x ∈ s.attach, p x x.2) ∈ Finset.Icc 1 (∏ i ∈ s, B i) := by
    intro p hp
    rw [Finset.mem_pi] at hp
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.one_le_prod' (fun x _ => (ht x (p x x.2) (hp x x.2)).1)
    · rw [← Finset.prod_attach s B]
      exact Finset.prod_le_prod' (fun x _ => (ht x (p x x.2) (hp x x.2)).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpm := (Finset.mem_filter.mp hp).2
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hpm, natCast_prod_cpow_S9,
    Nat.cast_prod, map_prod]

/-- PROVED: the members of `I_j = (N_j, 2N_j]` are `1 ≤ n ≤ ⌊2N_j⌋`. -/
theorem mem_dyad_bounds_S9 {x : ℝ} {n : ℕ} (h : n ∈ dyad x) : 1 ≤ n ∧ n ≤ ⌊2 * x⌋₊ := by
  simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at h
  exact h.1

/-- PROVED from `coeff313_312_leaf_S9`: the statement of the LEAF `FJ_dirpoly_312_leaf_S9`,
with `M = 0`, `N' = Π_{j ∈ J} ⌊2N_j⌋` and `b = bFJ312`. Same statement. -/
theorem FJ_dirpoly_312_of_coeff_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)), N₀ ≤ N → Cond35 N Nv →
    ∃ (M Nn : ℕ) (b : ℕ → ℂ),
      (∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ),
        ∏ j ∈ J, fj (j.val + 1) (Nv j) χ s
          = ∑ n ∈ Finset.Icc (M + 1) (M + Nn), b n * χ n * (n : ℂ) ^ (-s)) ∧
      ∀ (q : ℕ) (T : ℝ), 1 ≤ T →
        ∑ n ∈ Finset.Icc (M + 1) (M + Nn), ((q : ℝ) * T + n) * ‖b n‖ ^ 2 *
            (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
          ≤ K * ((q : ℝ) * T + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  obtain ⟨c7, hc7, K, N0, hB⟩ := coeff313_312_leaf_S9
  refine ⟨c7, hc7, K, N0, fun N Nv J hN hC =>
    ⟨0, ∏ j ∈ J, ⌊2 * Nv j⌋₊, bFJ312 Nv J, ?_, ?_⟩⟩
  · intro q χ s
    rw [zero_add, zero_add]
    unfold fj
    exact prod_dirpoly_S9 J (fun j => dyad (Nv j)) (fun j => ⌊2 * Nv j⌋₊)
      (fun j n hn => mem_dyad_bounds_S9 hn) (fun j n => aj (j.val + 1) n) χ s
  · intro q T hT
    rw [zero_add, zero_add]
    exact hB N Nv J hN hC q T hT

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.natCast_prod_cpow_S9
#print axioms LeanLab.Zhan1991.prod_dirpoly_S9
#print axioms LeanLab.Zhan1991.mem_dyad_bounds_S9
#print axioms LeanLab.Zhan1991.FJ_dirpoly_312_of_coeff_S9
