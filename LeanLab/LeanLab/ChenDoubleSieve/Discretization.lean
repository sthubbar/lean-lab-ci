import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# The rigorous partition step in Wu 2004 Section 7

Source: https://arxiv.org/pdf/0705.1652, page 30, equations 7.1 and 7.2.
The analytic functional inequalities, positivity and integrability are explicit inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Finset Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Discretization

/-- A decreasing correction is bounded below by its right endpoint on each panel. -/
theorem panel_lower {H K : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hH : ∀ t ∈ Set.Icc a b, H b ≤ H t) (hK : ∀ t ∈ Set.Icc a b, 0 ≤ K t)
    (hKi : IntervalIntegrable K volume a b)
    (hHKi : IntervalIntegrable (fun t => H t * K t) volume a b) :
    H b * (∫ t in a..b, K t) ≤ ∫ t in a..b, H t * K t := by
  rw [← intervalIntegral.integral_const_mul]
  exact integral_mono_on hab (hKi.const_mul _) hHKi
    (fun t ht => mul_le_mul_of_nonneg_right (hH t ht) (hK t ht))

/-- Summing panels gives the discrete lower bound for the functional integral. -/
theorem partition_lower (H K : ℝ → ℝ) (x : ℕ → ℝ) (m : ℕ)
    (hx : ∀ j < m, x j ≤ x (j + 1))
    (hH : ∀ j < m, ∀ t ∈ Set.Icc (x j) (x (j + 1)), H (x (j + 1)) ≤ H t)
    (hK : ∀ j < m, ∀ t ∈ Set.Icc (x j) (x (j + 1)), 0 ≤ K t)
    (hKi : ∀ j < m, IntervalIntegrable K volume (x j) (x (j + 1)))
    (hHKi : ∀ j < m, IntervalIntegrable (fun t => H t * K t) volume (x j) (x (j + 1))) :
    (∑ j ∈ range m, H (x (j + 1)) * (∫ t in x j..x (j + 1), K t)) ≤
      ∫ t in x 0..x m, H t * K t := by
  rw [← sum_integral_adjacent_intervals hHKi]
  exact sum_le_sum fun j hj => panel_lower (hx j (mem_range.mp hj))
    (hH j (mem_range.mp hj)) (hK j (mem_range.mp hj))
    (hKi j (mem_range.mp hj)) (hHKi j (mem_range.mp hj))

/-- Natural index form of the paper's grid, including both endpoints. -/
def node (j : ℕ) : ℝ := if j = 0 then 1 else 2 + (j + 1) / 10

/-- The nine cells are increasing and all lie in the interval one to three. -/
theorem node_bounds {j : ℕ} (hj : j < 9) :
    1 ≤ node j ∧ node j ≤ node (j + 1) ∧ node (j + 1) ≤ 3 := by
  have hj8 : (j : ℝ) ≤ 8 := by exact_mod_cast (show j ≤ 8 by omega)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_cases h0 : j = 0
  · subst j; norm_num [node]
  · simp only [node, if_neg h0, if_neg (show j + 1 ≠ 0 by omega)]
    push_cast
    constructor
    · linarith
    · constructor <;> linarith

/-- The natural and finite index grids agree. -/
theorem node_eq_grid (j : Fin 10) : node j.val = Wu04Functional.grid j := by
  simp only [node, Wu04Functional.grid]
  have he : j.val = 0 ↔ j = 0 := by simp
  simp only [he]

/-- Apply the partition argument directly to the nine printed cells. -/
theorem table_partition_lower (H K : ℝ → ℝ)
    (hH : AntitoneOn H (Set.Icc 1 3)) (hK : ∀ t ∈ Set.Icc 1 3, 0 ≤ K t)
    (hKi : IntervalIntegrable K volume 1 3)
    (hHKi : IntervalIntegrable (fun t => H t * K t) volume 1 3) :
    (∑ j : Fin 9, H (Wu04Functional.grid ⟨j.val + 1, by omega⟩) *
      (∫ t in Wu04Functional.grid ⟨j.val, by omega⟩..
        Wu04Functional.grid ⟨j.val + 1, by omega⟩, K t)) ≤
      ∫ t in (1 : ℝ)..3, H t * K t := by
  have hsub (j : ℕ) (hj : j < 9) : Set.uIcc (node j) (node (j + 1)) ⊆ Set.uIcc (1 : ℝ) 3 := by
    obtain ⟨hlo, hle, hhi⟩ := node_bounds hj
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Set.Icc_subset_Icc hlo hhi
  have hp := partition_lower H K node 9 (fun j hj => (node_bounds hj).2.1)
    (fun j hj t ht => hH ⟨ht.1.trans' (node_bounds hj).1, ht.2.trans (node_bounds hj).2.2⟩
      ⟨(node_bounds hj).1.trans (node_bounds hj).2.1, (node_bounds hj).2.2⟩ ht.2)
    (fun j hj t ht => hK t (by
      obtain ⟨hlo, hle, hhi⟩ := node_bounds hj
      exact ⟨hlo.trans ht.1, ht.2.trans hhi⟩))
    (fun j hj => hKi.mono_set (hsub j hj))
    (fun j hj => hHKi.mono_set (hsub j hj))
  have hsum : (∑ j ∈ range 9, H (node (j + 1)) * (∫ t in node j..node (j + 1), K t)) =
      ∑ j : Fin 9, H (Wu04Functional.grid ⟨j.val + 1, by omega⟩) *
        (∫ t in Wu04Functional.grid ⟨j.val, by omega⟩..Wu04Functional.grid ⟨j.val + 1, by omega⟩, K t) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro j hj
    rw [node_eq_grid ⟨j.val + 1, by omega⟩, node_eq_grid ⟨j.val, by omega⟩]
  rw [hsum] at hp
  norm_num [node] at hp
  exact hp

/-- The full analytic inputs needed for the finite Section 7 argument. -/
structure TableInputs (H : ℝ → ℝ) : Prop where
  nonnegative : ∀ t ∈ Set.Icc 1 3, 0 ≤ H t
  decreasing : AntitoneOn H (Set.Icc 1 3)
  kernel_nonnegative : ∀ i : Fin 9, ∀ t ∈ Set.Icc 1 3, 0 ≤ Wu04Table.tableKernel i t
  kernel_integrable : ∀ i : Fin 9, IntervalIntegrable (Wu04Table.tableKernel i) volume 1 3
  product_integrable : ∀ i : Fin 9,
    IntervalIntegrable (fun t => H t * Wu04Table.tableKernel i t) volume 1 3
  functional : ∀ i : Fin 9, (Wu04Table.printedBQ i : ℝ) +
    (∫ t in (1 : ℝ)..3, H t * Wu04Table.tableKernel i t) ≤
      H (Wu04Functional.grid ⟨i.val + 1, by omega⟩)

/-- The complete passage from functional inequalities and integral certificates to the correction.
CONDITIONAL ON TableInputs and IntegralMatrixBound. -/
theorem correction_of_functional (H : ℝ → ℝ) (h : TableInputs H)
    (hM : Wu04Table.IntegralMatrixBound) : (223938 / 10000000 : ℝ) ≤ H (2.2 : ℝ) := by
  let v : Fin 9 → ℝ := fun j => H (Wu04Functional.grid ⟨j.val + 1, by omega⟩)
  have hnode (j : Fin 9) : Wu04Functional.grid ⟨j.val + 1, by omega⟩ ∈ Set.Icc (1 : ℝ) 3 := by
    rw [← node_eq_grid ⟨j.val + 1, by omega⟩]
    exact ⟨(node_bounds j.isLt).1.trans (node_bounds j.isLt).2.1, (node_bounds j.isLt).2.2⟩
  have hv (j : Fin 9) : 0 ≤ v j := h.nonnegative _ (hnode j)
  have hrow (i : Fin 9) : (Wu04Table.printedBQ i : ℝ) +
      ∑ j, Wu04Table.integralMatrix i j * v j ≤ v i := by
    have hp := table_partition_lower H (Wu04Table.tableKernel i) h.decreasing
      (h.kernel_nonnegative i) (h.kernel_integrable i) (h.product_integrable i)
    have he : (∑ j : Fin 9, Wu04Table.integralMatrix i j * v j) =
        ∑ j : Fin 9, H (Wu04Functional.grid ⟨j.val + 1, by omega⟩) *
          (∫ t in Wu04Functional.grid ⟨j.val, by omega⟩..Wu04Functional.grid ⟨j.val + 1, by omega⟩,
            Wu04Table.tableKernel i t) := by
      apply sum_congr rfl
      intro j hj
      exact mul_comm _ _
    rw [he]
    exact (add_le_add le_rfl hp).trans (h.functional i)
  have hl := Wu04Table.discrete_of_entrywise Wu04Table.integralMatrix
    (fun i j => (Wu04Table.candidateMatrixQ i j : ℝ))
    (fun i => (Wu04Table.printedBQ i : ℝ)) v hv hM hrow
  have hc := Wu04Table.correction_of_discrete v hv hl
  norm_num [v, Wu04Functional.grid] at hc
  convert hc using 1 <;> norm_num

end LeanLab.ChenDoubleSieve.Wu04Discretization

#print axioms LeanLab.ChenDoubleSieve.Wu04Discretization.panel_lower
#print axioms LeanLab.ChenDoubleSieve.Wu04Discretization.partition_lower
#print axioms LeanLab.ChenDoubleSieve.Wu04Discretization.node_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Discretization.node_eq_grid
#print axioms LeanLab.ChenDoubleSieve.Wu04Discretization.table_partition_lower
#print axioms LeanLab.ChenDoubleSieve.Wu04Discretization.correction_of_functional
