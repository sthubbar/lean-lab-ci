import LeanLab.ChenDoubleSieve.FunctionalStatements

/-!
# The degenerate integral row of Wu 2004 Table 1

Source: https://arxiv.org/pdf/0705.1652, page 22, Lemma 5.1 and page 30, Table 1 row 9.
This row has s = s prime = 3. Every integration interval degenerates.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Wu04Functional

/-- An ordered box with every endpoint a is the singleton constant tuple. -/
theorem domain_diagonal (n : ℕ) (a : ℝ) :
    domain (fun _ : Fin (n + 2) => a) (fun _ => a) = {fun _ => a} := by
  ext x
  simp only [domain, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hm, hx⟩
    funext j
    exact le_antisymm (hx j).2 (hx j).1
  · rintro rfl
    exact ⟨fun i j hij => le_rfl, fun j => ⟨le_rfl, le_rfl⟩⟩

/-- The Buchstab integral over that diagonal vanishes for every phi. -/
theorem buchstabIntegral_diagonal (ω : ℝ → ℝ) (n : ℕ) (a φ : ℝ) :
    buchstabIntegral ω n (fun _ => a) (fun _ => a) φ = 0 := by
  rw [buchstabIntegral, domain_diagonal]
  simp

/-- Its supremum is zero, with phi two as a witness. -/
theorem buchstabSup_diagonal (ω : ℝ → ℝ) (n : ℕ) (a : ℝ) :
    buchstabSup ω n (fun _ => a) (fun _ => a) = 0 := by
  unfold buchstabSup
  have hs : {v : ℝ | ∃ φ : ℝ, 2 ≤ φ ∧ v = buchstabIntegral ω n (fun _ => a) (fun _ => a) φ} = {0} := by
    ext v
    simp only [buchstabIntegral_diagonal, mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨φ, hφ, hv⟩; exact hv
    · intro hv; exact ⟨2, le_rfl, hv⟩
  rw [hs, csSup_singleton]

/-- I1 vanishes when its two parameters agree. -/
theorem I1_diagonal (ω : ℝ → ℝ) (s : ℝ) : I1 ω s s = 0 :=
  buchstabSup_diagonal ω 1 (1 / s)

/-- Psi1 vanishes at the last printed parameter row. -/
theorem Psi1_three (ω : ℝ → ℝ) : Psi1 ω 3 3 = 0 := by
  rw [Psi1, I1_diagonal]
  norm_num [J, K]

/-- The final Table 1 lower bound is certified exactly. -/
theorem table1_last_Psi1_bound (ω : ℝ → ℝ) :
    tablePsi 8 ≤ Psi1 ω (grid 9) (tableSp 4) := by
  norm_num [tablePsi, grid, tableSp, Psi1_three]

end LeanLab.ChenDoubleSieve.Wu04Functional

#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.domain_diagonal
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.buchstabIntegral_diagonal
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.buchstabSup_diagonal
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.I1_diagonal
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.Psi1_three
#print axioms LeanLab.ChenDoubleSieve.Wu04Functional.table1_last_Psi1_bound
