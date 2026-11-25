import LeanLab.ChenDoubleSieve.Decomp348a

/-!
Feed split of `main4_compare` in Feed1122_Decomp348b_main4_lower, Wu 2004 page 39.
Source: https://arxiv.org/pdf/0705.1652, page 39, the passage from the sieve main term
with pi of N to the main term with N over log N in equation 10.5.
The comparison is assembled here from two cited inputs: the prime number theorem
for `Nat.primeCounting`, and the boundedness of the Upsilon 4 prime pair sum, which
follows from the continuity of f on the range of levels used and Mertens' theorem.
The normalisation uses `scaledDensity_tendsto` from Decomp348a, which is proved.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S120
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 39, the prime number theorem pi of N asymptotic to N over log N,
used to replace the total size pi of N of the sequence N minus p. It follows from the
lab's Chebyshev psi form of the prime number theorem in PNTPort by partial summation.
Class MEDIUM. -/
theorem primeCounting_pnt :
    Tendsto (fun N : ℕ => (Nat.primeCounting N : ℝ) * log N / N) atTop (𝓝 1) := by
  sorry

/-- LEAF: Wu 2004 page 39, boundedness of the Upsilon 4 prime pair sum in equation 10.5.
For N large every level `lowerLevel B N (p q)` with p q below N to the 2 kappa2 lies in
a fixed compact subinterval of the positive reals, so f, continuous there by the linear
sieve specification, is bounded, and the sum of 1 over phi of p q is at most the square
of the sum of 1 over p minus 1 over N to the kappa1 at most p at most N to the kappa2,
which is bounded by Mertens' theorem. Class MEDIUM. -/
theorem pairSum4_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      |∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
          f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)| ≤ C := by
  sorry

/-- The algebraic identity behind the comparison: the difference of the two main terms
is the prime number theorem error times the normalised density times the pair sum times
the normaliser Theta of N. -/
theorem compare_identity (S : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) / log N * lowerDensity N * S - (Nat.primeCounting N : ℝ) * lowerDensity N * S
      = (1 - (Nat.primeCounting N : ℝ) * log N / N) * scaledDensity N * S * Θ N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold scaledDensity Θ
  field_simp [(CN_pos N).ne', hlog.ne', hpos.ne']

/-- Wu 2004 page 39, the comparison of the two Upsilon 4 main terms, assembled from the
prime number theorem, the pair sum bound and `scaledDensity_tendsto`. -/
theorem main4_compare_of_leaves (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        |(N : ℝ) / log N * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))
          - (Nat.primeCounting N : ℝ) * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))| ≤ η * Θ N := by
  intro η hη B hB
  obtain ⟨C, hC⟩ := pairSum4_bounded F f h B hB
  set L : ℝ := 2 / (kappa1 * exp eulerMascheroniConstant)
  set K : ℝ := |L| + 1 with hK
  have hKpos : 0 < K := by positivity
  set C' : ℝ := |C| + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  have hεpos : 0 < η / (K * C') := by positivity
  have hsd : ∀ᶠ N in evenAtTop, |scaledDensity N| ≤ K := by
    have hlt : ∀ᶠ N in evenAtTop, scaledDensity N ∈ Metric.ball L 1 :=
      scaledDensity_tendsto (Metric.ball_mem_nhds L one_pos)
    filter_upwards [hlt] with N hN
    rw [Metric.mem_ball, Real.dist_eq] at hN
    have := abs_sub_abs_le_abs_sub (scaledDensity N) L
    linarith
  have hpnt : ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting N : ℝ) * log N / N ∈ Metric.ball (1 : ℝ) (η / (K * C')) :=
    primeCounting_pnt (Metric.ball_mem_nhds 1 hεpos)
  have hle : evenAtTop ≤ atTop := inf_le_left
  have hall : ∀ᶠ N in evenAtTop, Even N ∧ 2 ≤ N ∧ |scaledDensity N| ≤ K ∧
      (Nat.primeCounting N : ℝ) * log N / N ∈ Metric.ball (1 : ℝ) (η / (K * C')) ∧
      |∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
          f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)| ≤ C := by
    have hev : ∀ᶠ N in evenAtTop, Even N := mem_inf_of_right (mem_principal_self _)
    filter_upwards [hev, hle (eventually_ge_atTop 2), hsd, hle hpnt, hle hC] with N h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  have hall' := (eventually_inf_principal.1 hall)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hall'
  refine ⟨N0, fun N hE hN => ?_⟩
  obtain ⟨-, h2, h3, h4, h5⟩ := hN0 N hN hE
  rw [compare_identity _ h2]
  rw [Metric.mem_ball, Real.dist_eq] at h4
  have hΘ := Θ_nonneg N
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hΘ]
  have e1 : |1 - (Nat.primeCounting N : ℝ) * log N / N| ≤ η / (K * C') := by
    rw [abs_sub_comm]; exact h4.le
  have e3 : |∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
          f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)| ≤ C' := by
    have := le_abs_self C; linarith
  have hprod : |1 - (Nat.primeCounting N : ℝ) * log N / N| * |scaledDensity N| *
      |∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < (N : ℝ) ^ kappa2),
          f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ)| ≤
      η / (K * C') * K * C' := by
    apply mul_le_mul (mul_le_mul e1 h3 (abs_nonneg _) hεpos.le) e3 (abs_nonneg _)
    positivity
  have heq : η / (K * C') * K * C' = η := by field_simp
  rw [heq] at hprod
  exact mul_le_mul_of_nonneg_right hprod hΘ

end LeanLab.ChenDoubleSieve.Feed1122.S120
