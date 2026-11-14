/-
Split of the OPEN target `upper_normalized_raw_conditions` of UpperShortC165Leaves into two
leaves: the bounded rescaling of the raw short weight together with the short distribution
condition for it, and the transfer from the short distribution condition to the short mean
square condition for that same coefficient. The new file imports only
LeanLab.BHP1997.UpperShortC165Leaves, adds no definition, and leaves the sealed statement
untouched. The assembly `upper_normalized_raw_conditions_split` has the statement of the target
verbatim and is proved from the two leaves with no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: the slowly varying rescaling of the raw short weight exists, is bounded, is at least one
on J eventually, and makes the normalized coefficient meet the short distribution condition with
the density given by the reciprocal-log main term plus the deleted integral. This is the analytic
step: the raw weight follows 1/log m on J whereas the condition asks for the constant density of
1/log Y, so the factor lam carries the ratio, at least one on J, and the uniform short sum
estimate with the Buchstab integrals supplies the saving. Nothing else is asked: the boundedness
and the eventual lower bound are the two admissibility clauses of the target, and the mean square
condition is not part of this leaf. -/
theorem upper_split_rescaled_short_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam) := by
  sorry

/-- LEAF: the short mean square condition follows from the short distribution condition for the
normalized coefficient, with the same rescaling and the same density. Once the centered short
sums over any window of J are uniformly small, the second moment over the non-exceptional
characters is bounded by the same quantity, the exceptional sets being those characters where the
windowed sum is atypically large; their number is then bounded by a saving in the modulus. This
leaf keeps lam fixed by the argument, so it uses the distribution condition as a hypothesis
instead of asserting existence. -/
theorem upper_split_mean_square_transfer
    {ω : ℝ → ℝ} {ε : ℝ} (lam : ℝ → ℕ → ℝ)
    (hdist : Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam)) :
    Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam) := by
  sorry

/-- The target `upper_normalized_raw_conditions` of UpperShortC165Leaves, verbatim, assembled from
the two leaves. Take the rescaling and its bound from the distribution leaf, and get the mean
square condition for that same rescaling from the transfer leaf applied to the distribution
condition. No other input is used and the target theorem is not used. -/
theorem upper_normalized_raw_conditions_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) ∧
      Task308.ShortDistribution ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam) ∧
      Task308.ShortMeanSquare ε
        (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
          upperDeletedIntegral ω ε) (upperNormCoeff ε lam) := by
  obtain ⟨lam, Λ, hb, hX, hdist⟩ :=
    upper_split_rescaled_short_distribution h4 h9 hω hz hε hε8
  exact ⟨lam, Λ, hb, hX, hdist, upper_split_mean_square_transfer lam hdist⟩

end LeanLab.BHP1997.DecompC165d
