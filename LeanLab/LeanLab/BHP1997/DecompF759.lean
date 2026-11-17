/-
Split of the OPEN leaf `upper_slack_split_slack_distribution` of
SPLIT_upper_slack_split_rescaled_short_distribution into smaller leaves. The new file imports only
LeanLab.BHP1997.SPLIT_upper_slack_split_rescaled_short_distribution, adds no definition, and
leaves every sealed statement untouched. The assembly
`upper_slack_split_slack_distribution_F759` has the statement of the target verbatim and is
proved from the leaves with no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_slack_split_rescaled_short_distribution

namespace LeanLab.BHP1997.DecompF759
open Classical Complex Decomp132 DecompC165b

/-- LEAF: the simplification step. For large enough x where `2 ≤ x^(11/20+ε)` and for m in the
right interval, the normalized coefficient equals lam times the raw weight. This is the part of
the target that rewrites the coefficient; it asks for no character sum at all, so it is strictly
weaker than the target. -/
theorem leaf_upperNormCoeff_eq_on_interval {ε : ℝ} (hε : 0 < ε) {lam : ℝ → ℕ → ℝ} {x : ℝ}
    (hx : 2 ≤ x ^ (11 / 20 + ε)) {m : ℕ} (hm : m ∈ rightInterval ε x) :
    upperNormCoeff ε lam x m = lam x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m := by
  unfold upperNormCoeff
  simp [hx, hm]

/-- LEAF: the raw weight short distribution. The raw weight `upperRawWeight` without any lam
factor satisfies the short distribution condition at the slack density
`ω(c)/c + upperDeletedIntegral ω ε + δ`. This is the analytic core of the argument: the
prime number estimate in short intervals with Buchstab integrals and the mean square estimate
via Lemma 9, Theorem 4 and Lemma 29 supply this bound. This leaf asks for no lam factor, so
it is strictly weaker than the target. -/
theorem leaf_raw_weight_short_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ) :
    Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε + δ)
      (fun x m => upperRawWeight ε (x ^ (11 / 20 + ε)) m) := by
  sorry

/-- LEAF: the bounded rescaling step. If a coefficient `b` satisfies the short distribution at
density `v`, then `lam x m * b x m` (with `|lam| ≤ Λ`) also satisfies it at the same density,
with the constant multiplied by `Λ`. This is strictly weaker than the target because it asks
for no density shift and no existence of lam; lam is given as an argument. -/
theorem leaf_bounded_rescaling_preserves_distribution {ε v : ℝ} {lam : ℝ → ℕ → ℝ} {Λ : ℝ}
    (hb : ∀ x m, |lam x m| ≤ Λ)
    (hdist : Task308.ShortDistribution ε v (fun x m => upperRawWeight ε (x ^ (11 / 20 + ε)) m)) :
    Task308.ShortDistribution ε v (upperNormCoeff ε lam) := by
  sorry

/-- The target `upper_slack_split_slack_distribution` of
SPLIT_upper_slack_split_rescaled_short_distribution, verbatim, assembled from the leaves.
Take the raw weight short distribution from the second leaf, and get the short distribution
for the normalized coefficient from the third leaf applied to that raw distribution and the
uniform bound on lam. No other input is used and the target declaration is not used. -/
theorem upper_slack_split_slack_distribution_F759
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hb : ∀ x m, |lam x m| ≤ Λ)
    (hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) :
    Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  have hraw := leaf_raw_weight_short_distribution h4 h9 hω hz hε hε8 hδ
  exact leaf_bounded_rescaling_preserves_distribution hb hraw

end LeanLab.BHP1997.DecompF759
