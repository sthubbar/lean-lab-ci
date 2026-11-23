/-
Split of `leaf306_T_odd_bound` from `Split306Theorem6.lean`.

The odd Rosser terms are exposed as a finite sum of termwise main and error
contributions.  The finite summation algebra and the elementary positivity
facts are proved here.  The termwise decomposition remains one open LEAF.
The assembly has no `sorry` of its own.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: the sieve product used by the odd Rosser terms is nonnegative.
Every factor is one minus a number in the closed interval from zero to one.
This is the positivity needed when the termwise main and error contributions
are summed. -/
theorem leaf306_odd_V_nonneg_F2567 {P : Set ℕ} (hP : ∀ p ∈ P, p.Prime) (z : ℝ)
    (g : ArithmeticFunction ℝ) (hgp : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    0 ≤ ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p) := by
  apply Finset.prod_nonneg
  intro p hp
  obtain ⟨hpP, _⟩ := Finset.mem_filter.mp hp
  have hg := hgp p hpP
  linarith

/-- LEAF: the explicit sieve error function is nonnegative at every real
argument.  This is the positivity needed for the error part of the finite
Rosser sum. -/
theorem leaf306_odd_hSieve_nonneg_F2567 (s : ℝ) :
    0 ≤ LeanLab.ChenExplicit.hSieve s := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs <;> positivity

/-- LEAF: the first constant in a Table 1 row is nonnegative.  The finite
list of rows supplies this positivity for every permitted first constant. -/
theorem leaf306_odd_C1_nonneg_F2567 (k C₁ C₂ : ℕ)
    (hrow : (k, C₁, C₂) ∈ LeanLab.ChenExplicit.table1) : 0 ≤ (C₁ : ℝ) := by
  simp only [LeanLab.ChenExplicit.table1, List.mem_cons, List.mem_nil] at hrow
  omega

/-- LEAF: the logarithmic sieve parameter is at least one when the level is
at least the cutoff.  This is the range used by the odd Rosser estimate. -/
theorem leaf306_odd_ratio_ge_one_F2567 (z D : ℝ) (hz : 2 ≤ z) (hD : z ≤ D) :
    1 ≤ log D / log z := by
  have hzlog : 0 < log z := Real.log_pos (by linarith)
  have hDlog : 0 < log D := Real.log_pos (by linarith)
  have hle : log z ≤ log D := Real.log_le_log hzlog hD
  exact (div_le_iff₀ hzlog).2 hle

/-- LEAF: the odd Rosser terms admit a termwise main and error decomposition.
There are nonnegative sequences on the odd index range.  The main sequence has
sum `F (s) - 1`, the error sequence has sum at most `C₁`, and every odd Rosser
term is at most the product of the sieve product with the main contribution
plus the explicit error contribution.  This is the termwise form of the bound
on the odd Rosser terms before the finite sum is taken. -/
theorem leaf306_odd_term_decomposition_F2567
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
    let S : Finset ℕ := (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd
    let V : ℝ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)
    let s : ℝ := log D / log z
    ∃ a b : ℕ → ℝ,
      (∀ n ∈ S, 0 ≤ a n) ∧
      (∀ n ∈ S, 0 ≤ b n) ∧
      (∑ n ∈ S, a n = F s - 1) ∧
      (∑ n ∈ S, b n ≤ (C₁ : ℝ)) ∧
      (∀ n ∈ S, rosserT306 P g z D n ≤
        V * a n + ε * exp 2 * LeanLab.ChenExplicit.hSieve s * b n) := by
  sorry

/-- LEAF: finite summation of the termwise main and error contributions.
Nonnegative coefficients and the two budget identities give the summed odd
Rosser estimate.  This leaf is only the finite algebra of the summation. -/
theorem leaf306_odd_finite_sum_F2567
    (S : Finset ℕ) (T : ℕ → ℝ) (V E C A : ℝ) (a b : ℕ → ℝ)
    (hV : 0 ≤ V) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (ha : ∀ n ∈ S, 0 ≤ a n) (hb : ∀ n ∈ S, 0 ≤ b n)
    (hterm : ∀ n ∈ S, T n ≤ V * a n + E * b n)
    (hsa : ∑ n ∈ S, a n = A) (hsb : ∑ n ∈ S, b n ≤ C) :
    ∑ n ∈ S, T n ≤ V * (A + E * C) := by
  calc
    ∑ n ∈ S, T n ≤ ∑ n ∈ S, (V * a n + E * b n) := Finset.sum_le_sum hterm
    _ = V * (∑ n ∈ S, a n) + E * (∑ n ∈ S, b n) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ V * A + E * C := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsa hV)
        (mul_le_mul_of_nonneg_left hsb hE)
    _ = V * (A + E * C) := by ring

/-- The odd Rosser bound, assembled from the termwise decomposition and the
finite summation algebra.  The statement is the sealed target statement. -/
theorem leaf306_T_odd_bound_F2567
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
        (F (log D / log z) - 1 +
          ε * C₁ * exp 2 * LeanLab.ChenExplicit.hSieve (log D / log z)) := by
  let S : Finset ℕ := (Finset.Icc 1 (LeanLab.ChenExplicit.primesBelowIn P z).card).filter Odd
  let V : ℝ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, (1 - g p)
  let s : ℝ := log D / log z
  have hV : 0 ≤ V := by
    dsimp [V]
    exact leaf306_odd_V_nonneg_F2567 hP z g hgp
  have hE : 0 ≤ ε * exp 2 * LeanLab.ChenExplicit.hSieve s := by
    positivity
  have hC : 0 ≤ (C₁ : ℝ) := leaf306_odd_C1_nonneg_F2567 k C₁ C₂ hrow
  obtain ⟨a, b, ha, hb, hsa, hsb, hterm⟩ :=
    leaf306_odd_term_decomposition_F2567 F f hF k C₁ C₂ hrow ε hε hεk P hP z hz
      g hg hgp K hK1 hKε h29 D hD
  have hsum := leaf306_odd_finite_sum_F2567 S (rosserT306 P g z D) V
    (ε * exp 2 * LeanLab.ChenExplicit.hSieve s) (C₁ : ℝ) (F s - 1) a b
    hV hE hC ha hb
    (by
      intro n hn
      simpa [S, V, s] using hterm n hn)
    (by simpa [S] using hsa)
    (by simpa [S] using hsb)
  simpa [S, V, s] using hsum

#print axioms leaf306_odd_V_nonneg_F2567
#print axioms leaf306_odd_hSieve_nonneg_F2567
#print axioms leaf306_odd_C1_nonneg_F2567
#print axioms leaf306_odd_ratio_ge_one_F2567
#print axioms leaf306_odd_finite_sum_F2567
#print axioms leaf306_T_odd_bound_F2567

end LeanLab.Cai2002
