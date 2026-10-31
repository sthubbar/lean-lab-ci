import Mathlib

/-!
The cited Theorem 1.2 includes both hypotheses of display 1.9.
Character clusters are pairwise disjoint. Every product in one cluster has conductor at most inverse c0.
The provider must represent the complete scaled zero multiset of each character.
No identification with actual Dirichlet L zeros is proved here.
Natural index zero represents paper index one.
Source: Zhao 2025, displays 1.7 to 1.10, pages 2 and 3.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56

/-- The inner multiset sum in display 1.10 preserves zero multiplicities. -/
noncomputable def clusterWeight (z : Multiset ℝ) : ℝ :=
  (z.map fun l => Real.exp (-(10 / 3 * l))).sum

/-- Collect the supplied zero multisets over a finite character cluster. -/
noncomputable def clusterZeroMultiset
    (Z : (q : ℕ) → DirichletCharacter ℂ q → ℝ → Multiset ℝ)
    (q : ℕ) (H : ℝ) (K : Finset (DirichletCharacter ℂ q)) : Multiset ℝ :=
  K.val.bind (fun chi => Z q chi H)

/-- The two structural cluster hypotheses of Theorem 1.2 and display 1.9. -/
def ConductorClusters {q : ℕ} (c0 : ℝ) (K : ℕ → Finset (DirichletCharacter ℂ q)) : Prop :=
  Pairwise (fun i j => Disjoint (K i) (K j)) ∧
    ∀ i : ℕ, ∀ chi ∈ K i, ∀ chi' ∈ K i,
      (DirichletCharacter.conductor (chi * chi') : ℝ) ≤ c0⁻¹

/-- STATED and cited. The threshold is uniform over all admissible cluster families. -/
def PaperTheorem12
    (Z : (q : ℕ) → DirichletCharacter ℂ q → ℝ → Multiset ℝ) : Prop :=
  ∀ c0 : ℝ, 0 < c0 → ∃ c1 : ℝ, 0 < c1 ∧
    ∀ H : ℝ, 1 ≤ H → ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
      ∀ K : ℕ → Finset (DirichletCharacter ℂ q), ConductorClusters c0 K →
      (∀ i : ℕ, ∀ l ∈ clusterZeroMultiset Z q H (K i), c0 ≤ l) →
      Summable (fun i : ℕ => clusterWeight (clusterZeroMultiset Z q H (K i)) ^ 2) ∧
      ∑' i : ℕ, clusterWeight (clusterZeroMultiset Z q H (K i)) ^ 2 ≤ 1 - c1

/-- Empty abstract zero data satisfy the full source specification for every admissible cluster. -/
theorem theorem12_empty : PaperTheorem12 (fun _ _ _ => 0) := by
  intro c0 hc0
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro H hH
  refine ⟨1, ?_⟩
  intro q hq hq1 K hK hmin
  simp [clusterZeroMultiset, clusterWeight]
  norm_num

#print axioms theorem12_empty
end LeanLab.Zhao2025.Task56
