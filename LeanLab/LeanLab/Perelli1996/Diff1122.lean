/-
P0083 Perelli 1996, page 482, equation 6 of the proof of the named Lemma.
ROUTE BURST S79 burst-20261122 split of Decomp103b.leaf_differencing.
The K-th root and the heavy and light partition are proved in Decomp103b;
only the Weyl differencing display 6 itself stays a LEAF here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.VaughanInput

namespace LeanLab.Perelli1996.Diff1122
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- LEAF: Page 482 equation 6, Weyl differencing as in Vaughan 1981 Lemma 2.4.
Class HARD. With K equal to two to the k minus one,
|K(F,α)|^K is at most a constant times H^(K-k) times
H^(k-1) plus the sum over 1 ≤ h ≤ c₃ H^(k-1) of τ_k(h) |∑_{n ∈ I} e(nαh)|.
The paper's suitable interval I inside [N^(1/k), N^(1/k)+H] is rendered as one
block of at most H+1 consecutive integers for each h, start h through
start h plus len h minus one. Here τ_k is divisorCount k. -/
theorem leaf_weyl_differencing (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∃ start len : ℕ → ℕ, (∀ h, (len h : ℝ) ≤ H + 1) ∧
        ‖polynomialKernel F N H α‖ ^ weylExponent F ≤
          C * H ^ (weylExponent F - F.natDegree) *
            (H ^ (F.natDegree - 1) +
              ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
                (divisorCount F.natDegree h : ℝ) * ‖Kernel.T (start h) (len h) (α * h)‖) := by
  sorry

end
end LeanLab.Perelli1996.Diff1122
