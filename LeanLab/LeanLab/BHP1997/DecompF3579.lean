/- P0069 Baker Harman Pintz 1997, Section 5, page 53. Split of the OPEN leaf
`upper_normalized_raw_conditions_slack` of UpperShortC165Leaves.

The argument follows the paper's own route for b1: the raw page 53 weight has a local
density profile D over log Y (the prime number theorem with Buchstab integrals), and the
rescaling lam = (v1 + delta) / D turns the local density into the constant slack density
v1 + delta on J. The assembly below chains four leaves:

  leaf_local_density     (sorry)  produces D, c, K and the density profile
  leaf_lam_properties    (proved) builds lam = v / D, bounded and eventually at least one
  leaf_short_distribution (sorry) ShortDistribution for upperNormCoeff ε lam at v1 + delta
  leaf_short_mean_square  (sorry) ShortMeanSquare for upperNormCoeff ε lam at v1 + delta

No existing .lean file is edited. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF: P0069 page 53. The local density profile D of the raw page 53 weight over `log Y`.
`D` is bounded below by `c > 0`, varies by at most `K / Y` per unit step on `J`, tends to
`v1 = ω(1/c4)/c4 + upperDeletedIntegral ω ε` uniformly on `J`, and the prefix sums of the raw
weight minus `D / log Y` over `J` are `O(Y L^-A)` for every `A`. Also outputs `v = v1 + δ`
and `0 < v`. This is the prime number theorem with error term; a citation wall in the paper.
STEP: local density estimate for the raw weight. -/
theorem leaf_local_density
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (D : ℝ → ℕ → ℝ) (c K v : ℝ),
      0 < c ∧ 0 < v ∧
      (∀ x m, c ≤ D x m) ∧
      (∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
        |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) ∧
      (∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
        D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + η) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
      (v = ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε + δ) := by
  sorry

/-- LEAF: P0069 page 53. The rescaling step only. Given the local density profile `D` bounded
below by `c > 0` and converging to `v1` uniformly on `J`, set `v = v1 + δ` and `lam = v / D`.
Then `lam` is bounded by `v / c` everywhere and is at least one on `J` eventually, since
`D ≤ v1 + η < v` eventually for `η = δ / 2`. STEP: bounded slowly varying rescaling with
`lam ≥ 1` eventually. -/
theorem leaf_lam_properties
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {D : ℝ → ℕ → ℝ} {c v : ℝ}
    (hc : 0 < c) (hv : 0 < v) (hDc : ∀ x m, c ≤ D x m)
    (hDconv : ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x,
      D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε + η)
    (hv_def : v = ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
      upperDeletedIntegral ω ε + δ) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) := by
  have hΛ : 0 < v / c := by positivity
  refine ⟨fun x m => v / D x m, v / c, ?_, ?_⟩
  · -- |lam x m| = v / D x m ≤ v / c since v > 0, c > 0, D x m ≥ c
    intro x m
    have h₁ : 0 < D x m := by linarith
    have h₂ : 0 < v := hv
    have h₃ : 0 < c := hc
    calc |(v / D x m : ℝ)| = v / D x m := by
      rw [abs_of_nonneg (by
        -- v / D x m > 0 since v > 0 and D x m > 0
        exact div_pos h₂ (by linarith)
      )]
    _ ≤ v / c := by
      -- v / D x m ≤ v / c since D x m ≥ c and v > 0
      have h₄ : 0 < D x m := by linarith
      have h₅ : c ≤ D x m := hDc x m
      have h₆ : 0 < v := hv
      have h₇ : 0 < c := hc
      have h₈ : 0 < D x m := by linarith
      calc v / D x m ≤ v / c := by
        -- v / D ≤ v / c since D ≥ c and v > 0
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      _ = v / c := by rfl
  · -- eventually 1 ≤ lam x m = v / D x m, since D x m ≤ v1 + δ/2 < v eventually
    obtain ⟨X, hX⟩ := hDconv (δ / 2) (by linarith)
    refine ⟨X, fun x hx m hm => ?_⟩
    have h₁ : D x m ≤ ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
      upperDeletedIntegral ω ε + δ / 2 := hX x hx m hm
    have h₂ : v = ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
      upperDeletedIntegral ω ε + δ := hv_def
    have h₃ : D x m < v := by
      linarith
    have h₄ : 0 < D x m := by linarith
    have h₅ : 0 < v := hv
    -- v / D x m ≥ 1 since v ≥ D x m and both are positive
    have h₆ : 1 ≤ v / D x m := by
      rw [ge_iff_le_div (by positivity)]
      nlinarith
    exact h₆

/-- LEAF: P0069 page 53. Short distribution condition for the normalized coefficient
`upperNormCoeff ε lam` with `lam = v / D`, at the slack density `v1 + delta`. Once the local
density `D` of the raw weight is known, partial summation against the bounded slowly varying
factor `v / D` reduces the twisted character sums to the prefix sums of the raw weight, which
are `O(Y L^-A)` by the prime number theorem with error term. STEP: condition (iii) of page 3
for the rescaled coefficient at the slack density. -/
theorem leaf_short_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {D : ℝ → ℕ → ℝ} {c K v : ℝ}
    (hc : 0 < c) (hv : 0 < v) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hDpre : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (hv_def : v = ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
      upperDeletedIntegral ω ε + δ) :
    Task308.ShortDistribution ε v (upperNormCoeff ε (fun x m => v / D x m)) := by
  sorry

/-- LEAF: P0069 page 53. Short mean square condition for the normalized coefficient
`upperNormCoeff ε lam` with `lam = v / D`, at the slack density `v1 + delta`. The second moment
over the non-exceptional characters follows from Lemma 29 applied to the four-term identity,
with the principal character handled separately. STEP: condition (iv) of page 3 for the
rescaled coefficient at the slack density. -/
theorem leaf_short_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {D : ℝ → ℕ → ℝ} {c K v : ℝ}
    (hc : 0 < c) (hv : 0 < v) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hDpre : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (upperRawWeight ε (x ^ (11 / 20 + ε)) m - D x m / Real.log (x ^ (11 / 20 + ε)))| ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (hv_def : v = ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
      upperDeletedIntegral ω ε + δ) :
    Task308.ShortMeanSquare ε v (upperNormCoeff ε (fun x m => v / D x m)) := by
  sorry

/-- P0069 page 53, assembly of `upper_normalized_raw_conditions_slack` from the four leaves.
Take the local density profile `D` of the raw weight from `leaf_local_density`, set
`v = v1 + delta` and `lam = v / D`. By `leaf_lam_properties`, `lam` is bounded and at least one
on `J` eventually. By `leaf_short_distribution` and `leaf_short_mean_square`, the normalized
coefficient satisfies both short conditions at the slack density `v`. The assembly itself has
no sorry; every analytic step is delegated to a LEAF. -/
theorem upper_normalized_raw_conditions_slack_F3579
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  obtain ⟨D, c, K, v, hc, hv, hDc, hDLip, hDconv, hDpre, hv_def⟩ :=
    leaf_local_density h4 h9 hω hz hε hε8 hδ
  obtain ⟨lam, Λ, hlam, hlamge⟩ :=
    leaf_lam_properties h4 h9 hω hz hε hε8 hδ D c v hc hv hDc hDconv hv_def
  have hdist :=
    leaf_short_distribution h4 h9 hω hz hε hε8 hδ D c K v hc hv hDc hDLip hDpre hv_def
  have hmean :=
    leaf_short_mean_square h4 h9 hω hz hε hε8 hδ D c K v hc hv hDc hDLip hDpre hv_def
  refine ⟨lam, Λ, hlam, hlamge, hdist, hmean⟩

end LeanLab.BHP1997.DecompC165d
