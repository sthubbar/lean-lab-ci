import LeanLab.ChenDoubleSieve.Decomp275b

/-!
Feed split of `lower_F0` in `Decomp315b`, Wu 2004 Section 10, page 38, equation 10.2.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
The lower bound for `S(A; P, N^{κ₁})` is the Jurkat Richert linear sieve lower bound
at level `N^{1/2}` with sifting parameter `s = 6`, fed by Bombieri Vinogradov,
times the Mertens product asymptotic for the sifting density `V(z)`.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122F0
open Task275
open Wu41 (S PS)
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 38, proof of equation 10.2, linear sieve lower bound
`S(A; P, z) ≥ X V(z) (f(s) - ε)` with `X = N / log N`, `z = N^{κ₁}`, level `D = N^{1/2}`,
`s = log D / log z = 1/(2κ₁) = 6`, the remainder controlled by Bombieri Vinogradov,
Wu 2004 Lemma 2.1 and the sieve lemma of Section 2. Class HARD. -/
theorem linear_sieve_lower (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (f (1 / (2 * kappa1)) - ε) * (((N : ℝ) / Real.log N) *
        ∏ p ∈ PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) ≤
      (S (primeSequence N) 1 N ((N : ℝ) ^ kappa1) : ℝ) := by
  sorry

/-- LEAF: Wu 2004 page 38, main term of equation 10.2, Mertens product:
`X V(N^{κ₁}) = (2 / (κ₁ e^γ) + o(1)) Θ(N)` for even `N`, since
`∏_{2<p<z, p∤N} (1 - 1/(p-1)) ~ 2 e^{-γ} C_N / log z`. Class MEDIUM. -/
theorem mertens_main_term : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      |((N : ℝ) / Real.log N) *
        ∏ p ∈ PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1)) -
        2 / (kappa1 * exp eulerMascheroniConstant) * Θ N| ≤ ε * Θ N := by
  sorry

theorem Θ_nonneg (N : ℕ) : 0 ≤ Θ N := by
  unfold Θ CN oddFactor
  have h1 : 0 ≤ ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    apply Finset.prod_nonneg
    intro p hp
    simp only [Finset.mem_filter] at hp
    have : (2 : ℝ) < p := by exact_mod_cast hp.2
    apply div_nonneg <;> linarith
  have h2 := LeanLab.ChenExplicit.twinC_pos
  positivity

/-- Pure algebra combining the two leaves. -/
theorem combine (x m θ a c e1 e2 : ℝ) (he1 : 0 ≤ e1)
    (hx : (a - e1) * m ≤ x) (hm : |m - c * θ| ≤ e2 * θ) :
    (a * c - e1 * (c + e2) - |a| * e2) * θ ≤ x := by
  have hm' := abs_le.mp hm
  have h3 : |a * m - a * (c * θ)| ≤ |a| * (e2 * θ) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hm (abs_nonneg a)
  have h4 := (abs_le.mp h3).1
  have h5 : e1 * m ≤ e1 * ((c + e2) * θ) := mul_le_mul_of_nonneg_left (by linarith) he1
  nlinarith

theorem lower_F0_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 := by
  intro ε hε
  set a := f (1 / (2 * kappa1))
  set c := 2 / (kappa1 * exp eulerMascheroniConstant)
  have hc : 0 < c := by unfold c kappa1; positivity
  set e1 := ε / (2 * (c + 1))
  set e2 := min 1 (ε / (2 * (|a| + 1)))
  have he1 : 0 < e1 := by positivity
  have he2 : 0 < e2 := lt_min one_pos (by positivity)
  obtain ⟨N1, h1⟩ := linear_sieve_lower F f ω h hω e1 he1
  obtain ⟨N2, h2⟩ := mertens_main_term e2 he2
  refine ⟨max N1 N2, fun N hN hle => ?_⟩
  have k := combine _ _ _ a c e1 e2 he1.le (h1 N hN (le_of_max_le_left hle))
    (h2 N hN (le_of_max_le_right hle))
  have hI : integralTerms F f ω 0 = a * c := by
    simp only [integralTerms, a, c]
    simp
    ring
  have hS : sieveTerms N 0 = (S (primeSequence N) 1 N ((N : ℝ) ^ kappa1) : ℝ) := by
    simp [sieveTerms]
  rw [hI, hS]
  have hθ := Θ_nonneg N
  have he2le : e2 ≤ 1 := min_le_left _ _
  have he2le' : e2 ≤ ε / (2 * (|a| + 1)) := min_le_right _ _
  have q1 : e1 * (c + e2) ≤ ε / 2 := by
    have : e1 * (c + e2) ≤ e1 * (c + 1) := by nlinarith
    have : e1 * (c + 1) = ε / 2 := by unfold e1; field_simp
    linarith
  have q2 : |a| * e2 ≤ ε / 2 := by
    have ha := abs_nonneg a
    have : |a| * e2 ≤ |a| * (ε / (2 * (|a| + 1))) := mul_le_mul_of_nonneg_left he2le' ha
    have : |a| * (ε / (2 * (|a| + 1))) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have : (a * c - ε) * Θ N ≤ (a * c - e1 * (c + e2) - |a| * e2) * Θ N :=
    mul_le_mul_of_nonneg_right (by linarith) hθ
  linarith

end LeanLab.ChenDoubleSieve.Task315.Feed1122F0
