import LeanLab.ChenDoubleSieve.FunctionalStatements

/-!
A fixed parameter specialization of Wu 2004 Lemma 2.10 page 9.
Source https://arxiv.org/abs/0705.1652.
The displayed rough integer asymptotic is stored as a cited Prop.
It is unproved and unused by the completed certificate proofs.
Claude review is required before merge.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
namespace LeanLab.ChenDoubleSieve.Task665
open Wu04Functional

/-- STATED. The page 9 rough integer asymptotic for each fixed u at least two.
Constants are chosen separately for each fixed u and Buchstab function.
This states no uniform estimate as u varies. CONDITIONAL when used. -/
def Wu2004RoughIntegerAsymptotic : Prop := by
  classical
  exact ∀ {ω : ℝ → ℝ}, IsBuchstab ω → ∀ {u : ℝ}, 2 ≤ u →
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 2 ≤ X ∧ ∀ x : ℝ, X ≤ x →
      |((((Finset.Icc 1 ⌊x⌋₊).filter fun n =>
          ∀ p : ℕ, p.Prime → p ∣ n → x ^ (1 / u) ≤ (p : ℝ)).card : ℕ) : ℝ) -
        x / Real.log (x ^ (1 / u)) * ω u| ≤
          C * x / Real.log (x ^ (1 / u)) ^ 2

end LeanLab.ChenDoubleSieve.Task665
#print axioms LeanLab.ChenDoubleSieve.Task665.Wu2004RoughIntegerAsymptotic
