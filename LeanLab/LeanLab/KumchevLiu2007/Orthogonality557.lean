/-
The centered character maximum in Davenport chapter 28 page 162.
Source https://doi.org/10.1007/978-1-4757-5927-3_28
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp557a

namespace LeanLab.KumchevLiu2007.Task557o

open scoped BigOperators

/-- Davenport chapter 28 page 162, the modified psi sum after display 2.
Subtract x for the principal character and zero for every other character. -/
noncomputable def centeredPsi {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact LeanLab.PNTPort.BV.psiChi x χ - if χ = 1 then (x : ℂ) else 0

/-- Davenport chapter 28 page 162, the endpoint maximum of modified psi. -/
noncomputable def centeredMax {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ T ∧ v = ‖centeredPsi x χ‖})

/-- Davenport chapter 28 page 162, the modified character norm set is bounded. -/
theorem centeredMax_bddAbove {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) :
    BddAbove (insert 0 {v : ℝ | ∃ x : ℝ, 0 ≤ x ∧ x ≤ T ∧ v = ‖centeredPsi x χ‖}) := by
  classical
  refine ⟨Task557a.primitiveMax T χ + max T 0, ?_⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact add_nonneg (Task557a.primitiveMax_nonneg T χ) (le_max_right _ _)
  · obtain ⟨x, hx, hxT, rfl⟩ := hv
    unfold centeredPsi
    apply (norm_sub_le _ _).trans
    apply add_le_add (Task557a.primitiveMax_majorizes T x χ hx hxT)
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      exact hxT.trans (le_max_left _ _)
    · simp

#print axioms centeredMax_bddAbove

/-- Davenport chapter 28 page 162, the modified maximal norm is nonnegative. -/
theorem centeredMax_nonneg {q : ℕ} (T : ℝ) (χ : DirichletCharacter ℂ q) :
    0 ≤ centeredMax T χ :=
  le_csSup (centeredMax_bddAbove T χ) (Set.mem_insert 0 _)

#print axioms centeredMax_nonneg

/-- Davenport chapter 28 page 162, every modified endpoint norm is majorized. -/
theorem centeredMax_majorizes {q : ℕ} (T x : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 ≤ x) (hxT : x ≤ T) : ‖centeredPsi x χ‖ ≤ centeredMax T χ := by
  apply le_csSup (centeredMax_bddAbove T χ)
  exact Set.mem_insert_of_mem 0 ⟨x, hx, hxT, rfl⟩

#print axioms centeredMax_majorizes

/-- Davenport chapter 28 page 162, the last inequality after display 2.
Orthogonality bounds every reduced residue discrepancy by the sum of modified
character maxima divided by phi q. Both the principal subtraction and the
endpoint maximum are retained. -/
theorem maximal_orthogonality {q : ℕ} [NeZero q] (T x : ℝ) (a : ℕ)
    (hx : 0 ≤ x) (hxT : x ≤ T) (ha : Nat.Coprime a q) :
    |LeanLab.HeathBrown1985.psi x q a - x / q.totient| ≤
      (∑ χ : DirichletCharacter ℂ q, centeredMax T χ) / q.totient := by
  classical
  have hφ : (0 : ℝ) ≤ q.totient := by positivity
  calc
    _ ≤ (‖LeanLab.PNTPort.BV.psiChi x (1 : DirichletCharacter ℂ q) - x‖ +
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖LeanLab.PNTPort.BV.psiChi x χ‖) / q.totient :=
      LeanLab.PNTPort.BV.abs_psi_sub_le x ha
    _ ≤ (centeredMax T (1 : DirichletCharacter ℂ q) +
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
          centeredMax T χ) / q.totient := by
      apply div_le_div_of_nonneg_right _ hφ
      apply add_le_add
      · simpa [centeredPsi] using centeredMax_majorizes T x (1 : DirichletCharacter ℂ q) hx hxT
      · apply Finset.sum_le_sum
        intro χ hχ
        have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        simpa [centeredPsi, hne] using centeredMax_majorizes T x χ hx hxT
    _ = _ := by rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]

#print axioms maximal_orthogonality

/-- Davenport chapter 28 page 162, the finite weight normalization in the
conductor reduction. A cutoff R times the reciprocal totient sum is below
the q over phi q weighted sum. This is a deterministic inequality. -/
theorem conductor_block (Q : ℕ) (R : ℝ) (F : ℕ → ℝ) (hF : ∀ q, 0 ≤ F q) :
    R * (∑ k ∈ (Finset.range Q).filter (fun k => R ≤ ((k + 1 : ℕ) : ℝ)),
      F (k + 1) / (k + 1).totient) ≤
      ∑ k ∈ Finset.range Q, ((k + 1 : ℕ) : ℝ) / (k + 1).totient * F (k + 1) := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ (Finset.range Q).filter (fun k => R ≤ ((k + 1 : ℕ) : ℝ)),
        ((k + 1 : ℕ) : ℝ) / (k + 1).totient * F (k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hk).2
        (div_nonneg (hF (k + 1)) (by positivity : (0 : ℝ) ≤ (k + 1).totient))
      convert hh using 1 <;> ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => mul_nonneg (by positivity) (hF (k + 1)))

#print axioms conductor_block

end LeanLab.KumchevLiu2007.Task557o
