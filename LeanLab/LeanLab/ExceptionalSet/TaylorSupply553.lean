import LeanLab.ExceptionalSet.KaracubaSplit

/-!
Karacuba 1971 page245 display4. Exact companion for the sealed Taylor leaf.
The existing Decomp538a Taylor theorem supplies the whole statement.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.TaylorSupply553
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.U1539.KaracubaSplit

/-- Karacuba 1971 page245 display4, exact Taylor reduction supply.
The constant is two pi and the original endpoint condition is preserved. -/
theorem leaf_karW_taylor_reduction_supplied :
    ∃ C : ℝ, 0 < C ∧ ∀ (c1 : ℝ) (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ),
      0 < P → 2 ≤ n →
      (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (N + P) ⊆ U ∧ ContDiffOn ℝ (n + 1) f U) →
      (∀ x ∈ Set.Icc (N : ℝ) (N + P),
        |iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℝ)|
          ≤ (P : ℝ) ^ (-(c1 * ((n + 1 : ℕ) : ℝ)))) →
      N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
      ‖karW f (karP2 c1 n P) a -
        ∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
          eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
            iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
        ≤ C * ((karP2 c1 n P : ℝ) + 1) ^ 2 * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro c1 N P n f T a hP hn hsm hD ha haP
  exact LeanLab.ExceptionalSet.Decomp538a.karacuba_taylor_error c1 f n N P a (karP2 c1 n P)
    (by omega) hP rfl hsm hD ha haP

end LeanLab.ExceptionalSet.TaylorSupply553
