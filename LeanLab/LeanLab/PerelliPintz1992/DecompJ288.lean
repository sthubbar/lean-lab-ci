import LeanLab.PerelliPintz1992.Decomp97
import Mathlib

namespace LeanLab.PerelliPintz1992.DecompJ288
open Real ArithmeticFunction MeasureTheory Set Filter Topology Decomp97

/-- LEAF. Page 364, the Farey sequence partition of the minor arcs. DECISION U-1614: `4 ≤ N` added,
for `N < 4` the Farey range `q ≤ ⌊Q⌋` is empty, `Audit1614.old_farey_cover_false`. -/
theorem farey_cover (N : ℕ) (ε A : ℝ) (_hN : 4 ≤ N) :
    minorArcs N A ⊆ ⋃ q ∈ Finset.Icc 1 ⌊Q N⌋₊, ⋃ (a : ℕ) (_ : a ≤ q ∧ a.Coprime q),
      Ioo ((a : ℝ) / q - 1 / (q * Q N)) ((a : ℝ) / q + 1 / (q * Q N)) := by
  sorry

/-- REFUTED, `Audit1614.old_gallagher_comparison_false`: one modulus block `M` cannot bound the whole
integral, the paper sums over dyadic `M` and loses a power of `L`. Do not prove this. The correct form
is `Decomp97.reduction27`, display 27 on p. 364. Unused by the assembly. Kept as text of record.
LEAF. Page 364, the Gallagher lemma application comparing discrete and continuous mean squares. -/
theorem gallagher_comparison (N : ℕ) (ε ξ A : ℝ) (M : ℕ) (hM1 : 1 ≤ M) (hM2 : (M : ℝ) ≤ Q N) :
    (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A, ‖S N α‖ ^ 2)
      ≤ 2 * (energy N ε ξ M) := by
  sorry

/-- Assembly theorem for reduction27 from the Farey cover and Gallagher comparison.
CONDITIONAL ON farey_cover and gallagher_comparison. -/
theorem reduction27_assembly :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ,
        0 ≤ ξ → ξ ≤ 1 → ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energy N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27
  exact ⟨ε₁, hε₁, hred⟩

end LeanLab.PerelliPintz1992.DecompJ288
