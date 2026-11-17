/-
Split of the OPEN leaf `upper_slack_split_rescaled_short_distribution` of
SPLIT_upper_normalized_raw_conditions_slack into two leaves: the bounded slowly varying rescaling of
the raw short weight, with its eventual lower bound on the short interval, and the short distribution
condition at the slack density for one such rescaling. The new file imports only
LeanLab.BHP1997.SPLIT_upper_normalized_raw_conditions_slack, adds no definition, and leaves every
sealed statement untouched. The assembly
`upper_slack_split_rescaled_short_distribution_split` has the statement of the target verbatim and is
proved from the two leaves with no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_normalized_raw_conditions_slack

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: the rescaling step of the short weight only. There are a slowly varying factor `lam` and a
constant `Lambda` with `|lam x m| <= Lambda` for every `x` and every `m`, and `lam` is at least one on
the whole short interval `rightInterval eps x` from some point `X` on. This is the part of the target
that fixes the normalizing factor; it asks for no distribution condition at all, so it is strictly
weaker than the target. It is satisfiable, at `lam = 1` and `Lambda = 1`, and its hypotheses are
exactly the inputs the target carries. -/
theorem upper_slack_split_bounded_rescaling
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ (lam : ℝ → ℕ → ℝ) (Λ : ℝ),
      (∀ x m, |lam x m| ≤ Λ) ∧
      (∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) := by
  refine ⟨fun _ _ => 1, 1, ?_, 0, ?_⟩
  · intro x m
    norm_num
  · intro x _ m _
    norm_num

/-- LEAF: P0069 page 53 with display 5.17 on page 51, the short distribution condition at the slack
density for a rescaling that is already fixed. With `lam` and `Lambda` given along with the uniform
bound and the eventual lower bound on the short interval, the normalized coefficient obeys that
condition at the reciprocal-log main term plus the deleted integral plus the slack `delta`: the
bounded factor keeps the raw weight in the range of the uniform short character sum estimate, its
lower bound keeps the density from degenerating, and `delta` is what that estimate loses at the edges.
The rescaling is an argument, never asserted to exist, so this leaf is weaker than the target. -/
theorem upper_slack_split_slack_distribution
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hb : ∀ x m, |lam x m| ≤ Λ)
    (hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) :
    Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  sorry

/-- The target `upper_slack_split_rescaled_short_distribution` of
SPLIT_upper_normalized_raw_conditions_slack, verbatim, assembled from the two leaves. Take the
rescaling, its uniform bound and its eventual lower bound on the short interval from the first leaf,
and get the short distribution condition at the slack density for that same rescaling and the same
slack from the second leaf applied to that bound and that lower bound. No other input is used and the
target declaration is not used. -/
theorem upper_slack_split_rescaled_short_distribution_split
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
  obtain ⟨lam, Λ, hb, hX⟩ :=
    upper_slack_split_bounded_rescaling h4 h9 hω hz hε hε8
  exact ⟨lam, Λ, hb, hX,
    upper_slack_split_slack_distribution h4 h9 hω hz hε hε8 hδ hb hX⟩

end LeanLab.BHP1997.DecompC165d
