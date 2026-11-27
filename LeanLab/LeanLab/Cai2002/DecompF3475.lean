/-
Decomposition of `leaf306_T_odd_bound` for the odd-indexed Rosser bound.

The assembly keeps the target statement exactly. It splits the estimate into the finite
odd main-term sum and the remaining error budget. The second leaf is the analytic
estimate still to be discharged.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: Step one of the odd Rosser bound. For every finite cutoff and every scale at
least one, the sum of the odd finite-sieve main terms is at most the linear-sieve value
`F s - 1`. -/
theorem leaf306_F3475_main_sum (F f : ℝ → ℝ)
    (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (N : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    ∑ n ∈ (Finset.Icc 1 N).filter Odd, bjsF306 n s ≤ F s - 1 := by
  rw [Finset.sum_filter]
  refine sum_le_hasSum _ (fun n _ => ?_) (leaf306_display13 F f hF s hs)
  split_ifs with ho
  · exact leaf306_fn_nonneg n s (Or.inl ⟨ho, hs⟩)
  · exact le_refl 0

/-- LEAF: Step two of the odd Rosser bound. The odd Rosser terms are at most their
finite main terms plus the table error budget `ε C₁ e² h(s)`. -/
theorem leaf306_F3475_error_budget
    (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ))
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative)
    (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
          (∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
            bjsF306 n (log D / log z)) +
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  sorry

/-- The odd-indexed Rosser bound, assembled from the finite main-term estimate and the
error-budget estimate. -/
theorem leaf306_T_odd_bound_F3475 (F f : ℝ → ℝ) (hF : LeanLab.ChenExplicit.IsLinearSieveFns F f)
    (k C₁ C₂ : ℕ) (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1)
    (ε : ℝ) (hε : 0 < ε) (hεk : ε ≤ 1 / (k : ℝ))
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) (hz : 2 ≤ z)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (K : ℝ) (hK1 : 1 < K) (hKε : K < 1 + ε)
    (h29 : ∀ u : ℝ, 1 < u → u < z →
      ∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - g p)⁻¹ ≤ K * (log z / log u))
    (D : ℝ) (hD : z ≤ D) :
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
      (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
        (F (log D / log z) - 1 +
          ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  have hlogz : 0 < log z := log_pos (by linarith)
  have hs : 1 ≤ log D / log z := by
    rw [le_div_iff₀ hlogz, one_mul]
    exact log_le_log (by linarith) hD
  have hmain := leaf306_F3475_main_sum F f hF
    (LeanLab.ChenExplicit.primesBelowIn P z).card (log D / log z) hs
  have herr := leaf306_F3475_error_budget F f hF k C₁ C₂ hrow ε hε hεk P hP z hz
    g hg hgp K hK1 hKε h29 D hD
  have hV : 0 ≤ ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) :=
    V_nonneg306 P z g hgp
  calc
    ∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
        rosserT306 P g z D n ≤
        (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
            (∑ n ∈ (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd,
              bjsF306 n (log D / log z)) +
          (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
            (ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := herr
    _ ≤ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
            (F (log D / log z) - 1) +
          (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)) *
            (ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain hV) (le_refl _)
    _ = _ := by ring

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf306_T_odd_bound_F3475
