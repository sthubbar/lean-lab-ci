import LeanLab.ChenDoubleSieve.Decomp366e

/-!
Wu 2004 page 39, equation 10.5: boundedness of the Upsilon 4 prime pair sum, the
statement of the LEAF `pairSum4_bounded` in Feed1122_S120_main4_compare.
Source: https://arxiv.org/pdf/0705.1652, page 39.
The bound is the proved `lowerSum4_bounded` of Decomp366e, which combines the
boundedness of f on the levels used with the Mertens bound on the totient mass.
Decomp366e sits behind an import cycle for the leaf file, so the proof lives here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S148
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- Wu 2004 page 39, the statement of the LEAF `pairSum4_bounded`: the Upsilon 4
prime pair sum is eventually bounded in absolute value. -/
theorem pairSum4_bounded_proved (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
          f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)| ≤ C := by
  obtain ⟨K, -, N0, hK⟩ := LeanLab.ChenDoubleSieve.Task366.lowerSum4_bounded F f h B hB
  exact ⟨K, eventually_atTop.2 ⟨N0, hK⟩⟩

end LeanLab.ChenDoubleSieve.Feed1122.S148
