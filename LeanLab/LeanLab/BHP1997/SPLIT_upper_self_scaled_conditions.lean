/-
Split of the OPEN target `upper_self_scaled_conditions` of Upper312RouteSelfScaled into three
leaves, with an assembly that has the target's statement verbatim and uses no sorry.

The target asks for conditions iii and iv of page 3 for the self scaled upper coefficient: the
short-interval character distribution clause at the density v1 plus the deleted integral, and the
short-interval mean square clause at that same density. Conditions iii and iv are the two halves of
the page 53 argument, and condition iii itself separates into the principal character and the
non-principal characters, exactly as in the lower lane of this folder.

Leaf 1: condition iii for the principal character, that is the density statement, with no
character sum to estimate; only the size of the filter `(1 : DirichletCharacter ℂ q) (m : ZMod q)`
factor stays in the summand so that the assembly is a substitution.
Leaf 2: condition iii for the non-principal characters, that is the uniform character sum estimate
on every short initial segment; here the density term is absent because the delta factor is zero.
Leaf 3: condition iii implies condition iv for this coefficient, using the divisor bound to bound
the square sum over a moving window.

This file adds no definition, changes no existing file, and leaves the sealed statement untouched.
The assembly declares neither the target nor any leaf as a hypothesis.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Upper312RouteSelfScaled

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: condition iii, principal character. The short interval sums of the self scaled upper
coefficient against the trivial character obey the paper density statement, at the frozen level
constant plus the deleted integral, with every power of the logarithm saved. There is no mean
square clause and no non-principal character, so this is strictly easier than the target. The
factor `(1 : DirichletCharacter ℂ q) (m : ZMod q)` is kept in the summand so that the assembly is
a substitution. Non-vacuity: the index set is empty at `t = 0`, and `b1` is pinned by `hb`. -/
theorem upper_self_scaled_principal_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
            ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
              upperDeletedIntegral ω ε : ℝ) : ℂ) /
              Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: condition iii, non-principal characters. The delta factor vanishes off the principal
character, so the claim is only that the short character sums of the self scaled coefficient at
level `x ^ (11/20 + eps)` save any power of the logarithm, uniformly in `q` up to `log x ^ A` and in
`chi` other than the trivial character. No mean square clause and no principal character, so this
is strictly easier than the target. Non-vacuity: at `t = 0` the index set is empty and the sum is
zero, and `q` and `chi` are arbitrary. -/
theorem upper_self_scaled_nonprincipal_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b1 x m : ℂ) * χ (m : ZMod q))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: condition iii yields condition iv. Given the divisor bound for `b1` at exponent two and
the short interval distribution clause at the paper density, the averaged square of the centred
short character sums over the complement of an exceptional set obeys the short interval mean square
clause at the same density, the exceptional characters being the ones whose windowed sum is
atypically large. The distribution clause is a hypothesis here and the mean square clause is not,
so this is strictly easier than the target. Non-vacuity: the divisor bound holds for the `b1`
fixed by `hb`, so both hypotheses are satisfiable. -/
theorem upper_self_scaled_mean_square_of_distribution
    {ω : ℝ → ℝ} {ε : ℝ} {b1 : ℝ → ℕ → ℝ}
    (hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ))
    (hdist : Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1) :
    Task308.ShortMeanSquare ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1 := by
  refine ⟨fun _ _ _ => ∀, ?_⟩
  intro A hA
  obtain ⟨C, hC⟩ := hdist A hA
  refine ⟨max C 1, ?_⟩
  intro x hx q hq hqQ
  constructor
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · intro z hz1 hz2
    have hx1 : 1 ≤ x := by
      have : 1 ≤ max C 1 := le_max_right _ _
      exact this.trans hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hY : 0 ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_nonneg (by linarith) _
    have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      mul_nonneg hY (Real.rpow_nonneg hlog _)
    refine le_trans (hC x (by
      have : C ≤ max C 1 := le_max_left _ _
      exact this.trans hx) q hq (by
        exact le_trans (by
          have : (1 : ∜) ≤ Real.log x := by linarith
          exact Real.one_le_rpow this hA) hqA) (fun _ => hz2)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hscale

/-- The target `upper_self_scaled_conditions` of Upper312RouteSelfScaled, verbatim, assembled from
the three leaves. For each power of the logarithm the two character leaves give the two constants;
the maximum of them and one is the constant of the distribution clause, whose principal case is the
first leaf after evaluating the delta factor and whose non-principal case is the second leaf after
evaluating the delta factor to zero. The divisor bound of the target's coefficient, proved in the
imported file, and the distribution clause just obtained feed the third leaf, which returns the
mean square clause at the same density. No step uses the sealed target. -/
theorem upper_self_scaled_conditions_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) b1 := by
  have hdiv : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (2 : ℝ) :=
    upper_self_scaled_divisor_bound (B := 2) (by norm_num) hε8 hb
  have hdist : Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε) b1 := by
    intro A hA
    obtain ⟨C1, hC1⟩ :=
      upper_self_scaled_principal_distribution h4 h9 hω hz hε hε8 hb A hA
    obtain ⟨C2, hC2⟩ :=
      upper_self_scaled_nonprincipal_distribution h4 h9 hω hz hε hε8 hb A hA
    refine ⟨max (max C1 C2) 1, fun x hx q hq hqA χ t ht => ?_⟩
    have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (Real.log_nonneg hxone) _)
    by_cases hχ : χ = 1
    · subst hχ
      have hd : Thm2.delta (1 : DirichletCharacter ℂ q) = 1 := by simp [Thm2.delta]
      rw [hd, one_mul]
      calc _ ≤ C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hC1 x hx1 q hq hqA t ht
        _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (le_trans (le_max_left _ _) (le_max_left _ _)) hscale
    · have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
      rw [hd, zero_mul, zero_div]
      simp only [sub_zero]
      calc _ ≤ C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hC2 x hx2 q hq hqA χ hχ t ht
        _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (le_trans (le_max_right _ _) (le_max_left _ _)) hscale
  exact ⟨hdist, upper_self_scaled_mean_square_of_distribution hdiv hdist⟩

end LeanLab.BHP1997.Upper312Route
