/-
Split of the OPEN target `upper_normalized_raw_conditions_slack` of UpperShortC165Leaves into two
leaves: the bounded slowly varying rescaling of the raw short weight together with the short
distribution condition for the normalized coefficient at the slack density, and the transfer from
that distribution condition to the short mean square condition for the same rescaling and the same
slack density. The new file imports only LeanLab.BHP1997.UpperShortC165Leaves, adds no definition,
and leaves the sealed statement untouched. The assembly
`upper_normalized_raw_conditions_slack_split` has the statement of the target verbatim and is proved
from the two leaves with no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: P0069 page 53 with display 5.17 on page 51, the rescaling step only. There are `lam` and
`Lambda` with `|lam x m| <= Lambda` for all `x` and `m`, with `lam` at least one on `rightInterval eps
x` from some `X` on, and the short distribution condition at the slack density, that is the
reciprocal-log main term plus the deleted integral plus the slack delta. The raw weight follows the
reciprocal of the logarithm of the local size while the condition asks for a constant density, so the
factor carries the ratio and the uniform short character sum estimate supplies the saving that
absorbs the slack. No second moment clause is asked, which is what makes this leaf weaker than the
target. -/
theorem upper_slack_split_rescaled_short_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  sorry

/-- LEAF: the short mean square condition follows from the short distribution condition for the
normalized coefficient, with the same rescaling, the same density and the same slack delta. Once the
centered short character sums over every window of the right interval are uniformly small, the
second moment over the second-moment-exceptional characters is bounded by the same quantity, those
exceptional characters being the ones where a windowed sum is atypically large, and their number is
then bounded by a saving in the modulus. This leaf keeps the rescaling fixed by taking it as an
argument, so it asks for the transfer only and never for the existence of the rescaling, which is
what makes it weaker than the target. -/
theorem upper_slack_split_mean_square_transfer
    {ω : ℝ → ℝ} {ε δ : ℝ} (hδ : 0 < δ) (lam : ℝ → ℕ → ℝ)
    (hdist : Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam)) :
    Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  sorry

/-- The target `upper_normalized_raw_conditions_slack` of UpperShortC165Leaves, verbatim,
assembled from the two leaves. Take the rescaling, its bound, its eventual lower bound on the right
interval and the short distribution condition at the slack density from the first leaf, and get the
short mean square condition for that same rescaling and the same slack density from the transfer
leaf applied to that distribution condition. No other input is used and the target declaration is
not used. -/
theorem upper_normalized_raw_conditions_slack_split
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
  obtain ⟨lam, Λ, hb, hX, hdist⟩ :=
    upper_slack_split_rescaled_short_distribution h4 h9 hω hz hε hε8 hδ
  exact ⟨lam, Λ, hb, hX, hdist, upper_slack_split_mean_square_transfer hδ lam hdist⟩

end LeanLab.BHP1997.DecompC165d
