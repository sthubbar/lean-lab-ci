/-
P0083 Perelli 1996, page 482, equation 6 of the proof of the named Lemma.
ROUTE BURST S79 burst-20261122 split of Diff1122.leaf_weyl_differencing.
The k-1 fold Weyl differencing and the count of difference tuples by τ_k are LEAFs;
grouping the tuples by the frequency m and choosing one interval per m is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.VaughanInput

namespace LeanLab.Perelli1996.Weyl1122
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- The difference tuples (h_1, ..., h_(k-1)) with 1 ≤ |h_i| ≤ R. -/
abbrev tuples (k R : ℕ) : Finset (Fin (k - 1) → ℤ) :=
  Fintype.piFinset fun _ => (Icc (-(R : ℤ)) R).filter (· ≠ 0)

/-- The frequency k! a_k |h_1 ⋯ h_(k-1)| of the linear (k-1)-th difference, page 482. -/
abbrev freq (k a : ℕ) (h : Fin (k - 1) → ℤ) : ℕ := k.factorial * a * (∏ i, h i).natAbs

/-- LEAF: Page 482 equation 6, first half, as in Vaughan 1981 Lemma 2.4 with j = k-1:
|K(F,α)|^K ≪ H^(K-k) (H^(k-1) + ∑_h |∑_{n ∈ I_h} e(α k! a_k h_1⋯h_(k-1) n)|), the sum over
tuples with 1 ≤ |h_i| ≤ H, the tuples with some h_i = 0 contributing H^(k-1), and I_h an
interval of at most H+1 consecutive integers. The constant term of the linear difference
and the sign of the product do not change the modulus. Class MEDIUM. -/

/-- Helper: the number of k-tuples of positive integers with product m equals divisorCount k m = (ζ ^ k) m.
Proof by induction on k using (ζ * f) n = ∑ i ∣ n, f i. -/
lemma divisorCount_card_tuples {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    (Fintype.piFinset (fun _ : Fin k => Icc 1 m)).filter (fun d => (∏ i : Fin k, d i) = m).card = divisorCount k m := by
  sorry

/-- Helper: divisorCount (k-1) n ≤ divisorCount k m when n ∣ m, k ≥ 2.
Proof: (ζ ^ k) m = ∑_{i ∣ m} (ζ ^ (k-1)) i ≥ (ζ ^ (k-1)) n since n ∣ m and all terms are ≥ 0. -/
lemma divisorCount_le_dvd {k n m : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (hm : 0 < m) (h : n ∣ m) :
    divisorCount (k - 1) n ≤ divisorCount k m := by
  sorry

theorem leaf_iterated_differencing (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∃ start len : (Fin (F.natDegree - 1) → ℤ) → ℕ, (∀ h, (len h : ℝ) ≤ H + 1) ∧
        ‖polynomialKernel F N H α‖ ^ weylExponent F ≤
          C * H ^ (weylExponent F - F.natDegree) *
            (H ^ (F.natDegree - 1) +
              ∑ h ∈ tuples F.natDegree ⌊H⌋₊,
                ‖Kernel.T (start h) (len h) (α * (freq F.natDegree F.leadingCoeff.natAbs h : ℕ))‖) := by
  sorry

/-- LEAF: Page 482 equation 6, second half: the number of tuples with
k! a |h_1⋯h_(k-1)| = m is at most 2^(k-1) τ_(k-1)(m/(k! a)) ≤ 2^(k-1) τ_k(m).
Class EASY. -/
theorem leaf_tuple_count (k a R m : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) :
    (((tuples k R).filter (fun h => freq k a h = m)).card : ℝ) ≤
      2 ^ (k - 1) * (divisorCount k m : ℝ) := by
  sorry

end
end LeanLab.Perelli1996.Weyl1122
