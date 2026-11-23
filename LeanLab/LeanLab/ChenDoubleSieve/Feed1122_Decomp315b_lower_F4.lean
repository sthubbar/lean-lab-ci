import LeanLab.ChenDoubleSieve.Feed1122_Decomp315b_lower_F0

/-!
Feed split of `lower_F4` in `Decomp315b`, Wu 2004 Section 10, page 39, equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
For each pair `p < q` the set `A_{pq}` is sifted by the linear sieve at level
`N^{1/2}/(pq)` with `s = (1/2 - t - u)/κ₁`, `p = N^t`, `q = N^u`; summing gives the
sieve leaf, and the prime sum is turned into the double integral by the prime number
theorem in the form of Mertens. The Mertens main term is shared with `lower_F0`.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122F0
open Task275
open Wu41 (S PS)
open Wu08Sum (P2 P4)
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- Pointwise algebra for a product main term. -/
theorem alg_prod (x m s θ c J e e2 e3 : ℝ) (hθ : 0 ≤ θ) (hc : 0 ≤ c) (he2 : 0 ≤ e2)
    (hA : m * s - e * θ ≤ x) (hM : |m - c * θ| ≤ e2 * θ) (hS : |s - J| ≤ e3) :
    c * J * θ - e * θ - e2 * θ * (|J| + e3) - c * e3 * θ ≤ x := by
  have hs : |s| ≤ |J| + e3 := by
    have := abs_sub_abs_le_abs_sub s J
    linarith
  have h1 : |(m - c * θ) * s| ≤ e2 * θ * (|J| + e3) := by
    rw [abs_mul]
    exact mul_le_mul hM hs (abs_nonneg _) (by positivity)
  have h2 : |c * θ * (s - J)| ≤ c * θ * e3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ c * θ)]
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have h1' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).1
  have : m * s - c * J * θ = (m - c * θ) * s + c * θ * (s - J) := by ring
  nlinarith

/-- Eventual form of `alg_prod`, used for the pair and quadruple sums. -/
theorem eventual_prod (x M s : ℕ → ℝ) (c J : ℝ) (hc : 0 ≤ c)
    (hA : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      M N * s N - e * Θ N ≤ x N)
    (hM : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |M N - c * Θ N| ≤ e * Θ N)
    (hS : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N → |s N - J| ≤ e) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (c * J - ε) * Θ N ≤ x N := by
  intro ε hε
  set e3 := min 1 (ε / (3 * (c + 1)))
  set e2 := ε / (3 * (|J| + 2))
  have he3 : 0 < e3 := lt_min one_pos (by positivity)
  have he2 : 0 < e2 := by positivity
  obtain ⟨N1, h1⟩ := hA (ε / 3) (by positivity)
  obtain ⟨N2, h2⟩ := hM e2 he2
  obtain ⟨N3, h3⟩ := hS e3 he3
  refine ⟨max N1 (max N2 N3), fun N hN hle => ?_⟩
  have k := alg_prod (x N) (M N) (s N) (Θ N) c J (ε / 3) e2 e3 (Θ_nonneg N) hc he2.le
    (h1 N hN (by omega)) (h2 N hN (by omega)) (h3 N hN (by omega))
  have hθ := Θ_nonneg N
  have he3le : e3 ≤ 1 := min_le_left _ _
  have he3le' : e3 ≤ ε / (3 * (c + 1)) := min_le_right _ _
  have q1 : e2 * (|J| + e3) ≤ ε / 3 := by
    have hJ := abs_nonneg J
    have : e2 * (|J| + e3) ≤ e2 * (|J| + 2) := by nlinarith
    have : e2 * (|J| + 2) = ε / 3 := by unfold e2; field_simp
    linarith
  have q2 : c * e3 ≤ ε / 3 := by
    have : c * e3 ≤ c * (ε / (3 * (c + 1))) := mul_le_mul_of_nonneg_left he3le' hc
    have : c * (ε / (3 * (c + 1))) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have e1 : e2 * Θ N * (|J| + e3) ≤ ε / 3 * Θ N := by nlinarith
  have e4 : c * e3 * Θ N ≤ ε / 3 * Θ N := by nlinarith
  nlinarith

/-- The sifting main term `X V(N^{κ₁})` of Section 10. -/
def mainXV (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) * ∏ p ∈ PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))

/-- The pair weight sum `∑ f(s_{pq}) / ((p - 1)(q - 1))` of equation 10.5,
`s_{pq} = (1/2 - log p / log N - log q / log N) / κ₁`. -/
def pairSum4 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
    f ((1 / 2 - Real.log q.1 / Real.log N - Real.log q.2 / Real.log N) / kappa1) /
      (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))

/-- LEAF: Wu 2004 page 39, proof of equation 10.5, the linear sieve lower bound applied to each
`A_{pq}` at level `N^{1/2}/(pq)` and sifting limit `N^{κ₁}`, `|A_{pq}| ≈ X/((p-1)(q-1))`,
summed over the pairs with the remainders bounded by Bombieri Vinogradov. Class HARD. -/
theorem sieve_lower4 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      mainXV N * pairSum4 f N - e * Θ N ≤ sieveTerms N 4 := by
  sorry

/-- LEAF: Wu 2004 page 39, equation 10.5 main term, the prime pair sum tends to the double
integral `∫_{κ₁}^{κ₂} ∫_t^{κ₂} f((1/2 - t - u)/κ₁) du/u dt/t`, by the prime number theorem
with partial summation and continuity of `f`. Class MEDIUM. -/
theorem pair_sum4_limit (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |pairSum4 f N - ∫ t in kappa1..kappa2,
        (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t| ≤ e := by
  sorry

theorem lower_F4_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 := by
  have hI : integralTerms F f ω 4 = 2 / (kappa1 * exp eulerMascheroniConstant) *
      ∫ t in kappa1..kappa2, (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t := rfl
  rw [hI]
  exact eventual_prod (fun N => sieveTerms N 4) mainXV (pairSum4 f) _ _
    (by unfold kappa1; positivity) (sieve_lower4 F f ω h hω) mertens_main_term
    (pair_sum4_limit F f h)

end LeanLab.ChenDoubleSieve.Task315.Feed1122F0
