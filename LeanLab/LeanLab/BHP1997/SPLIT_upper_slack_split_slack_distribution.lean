/-
Split of the OPEN leaf `upper_slack_split_slack_distribution` of
SPLIT_upper_slack_split_rescaled_short_distribution into three leaves: the short character sum for a
non-principal character, where the density term vanishes and only the twisted coefficient sum is
asked for; the principal character with a short prefix, where the range of summation is empty and the
sum is zero; and the principal character with a long prefix, which carries the arithmetic content.
The new file imports only LeanLab.BHP1997.SPLIT_upper_slack_split_rescaled_short_distribution, adds no
definition, and leaves every sealed statement untouched. The assembly
`upper_slack_split_slack_distribution_split` has the statement of the target verbatim and is proved
from the three leaves with no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_upper_slack_split_rescaled_short_distribution

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b

/-- LEAF: the non-principal half of the short distribution condition. For a character that is not
the principal one the density carries the factor zero, so the condition reduces to a uniform bound
for the twisted coefficient sum over a prefix of the right interval, with nothing subtracted. Only
the character sums are asked for, never the principal case, which makes this strictly weaker than
the target. It is not vacuous: at `lam = 1`, `Λ = 1` the hypotheses hold, and the summand is the
normalized weight times a character value. -/
theorem upper_slack_split_nonprincipal_twisted
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hb : ∀ x m, |lam x m| ≤ Λ)
    (hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε lam x m : ℂ) * χ (m : ZMod q))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the boundary case of the principal character. At `χ = 1` the summand is the normalized
weight minus the density, and on a prefix `t ≤ x ^ (11/20+eps)` that prefix meets no element of the
right interval at all, since every `m` there exceeds the left end, which is the floor of
`x ^ (11/20+eps)`. The sum is therefore empty, the norm is zero, and any nonnegative constant
serves. This is the trivial short-prefix half of the principal case, strictly weaker than the
target, and its hypotheses are the target's own. -/
theorem upper_slack_split_principal_short_prefix
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hb : ∀ x m, |lam x m| ≤ Λ)
    (hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ t : ℝ, t ≤ x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε lam x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ *
              ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
                upperDeletedIntegral ω ε + δ : ℝ)) /
              Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  refine ⟨4, ?_⟩
  intro x hx q hq hqx χ hχ t ht
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hY0 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  -- Every element of the right interval exceeds `x^(11/20+eps)`, hence the prefix is empty.
  have hempty : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro m hm
    rw [rightInterval] at hm
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hm
    have h1' : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      have h2 : (⌊x ^ (11 / 20 + ε)⌋₊ + 1 : ℕ) ≤ m := Nat.succ_le_of_lt h1
      exact_mod_cast h2
    have hlt : x ^ (11 / 20 + ε) < ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    intro hmt
    linarith
  rw [hempty]
  simp only [Finset.sum_empty, norm_zero]
  exact mul_nonneg (mul_nonneg (by norm_num) hY0) (Real.rpow_nonneg (Real.log_nonneg hx1) _)

/-- LEAF: the long-prefix half of the principal character, where the density is actually met. On
`x ^ (11/20+eps) ≤ t ≤ 2 * x ^ (11/20+eps)` the prefix is the whole right interval and the main term
of the coefficient is cancelled against the density, the slack `delta` paying for the edges, so the
short character sum is small at the reciprocal-log density. The non-principal characters are removed
and the prefix is restricted to the upper half, so this is strictly weaker than the target. -/
theorem upper_slack_split_principal_long_prefix
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hb : ∀ x m, |lam x m| ≤ Λ)
    (hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m)
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ = 1 → ∀ t : ℝ,
        x ^ (11 / 20 + ε) ≤ t → t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε lam x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ *
              ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
                upperDeletedIntegral ω ε + δ : ℝ)) /
              Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The target `upper_slack_split_slack_distribution` of
SPLIT_upper_slack_split_rescaled_short_distribution, verbatim, assembled from the three leaves. Fix
the exponent `A` and take the three constants, then the largest of them and four, so that `x >= 4`
and both `x ^ (11/20+eps)` and `Real.log x ^ (-A)` are nonnegative and every leaf constant is below
the assembled one. A character is either the principal one or not; when it is not, the density term
carries the factor zero and the non-principal leaf gives the bound; when it is, split the prefix at
`x ^ (11/20+eps)`, the short side being empty by the second leaf and the long side the third. No
other input is used and the target declaration is not used. -/
theorem upper_slack_split_slack_distribution_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {δ : ℝ} (hδ : 0 < δ)
    {lam : ℝ → ℕ → ℝ} {Λ : ℝ} (hb : ∀ x m, |lam x m| ≤ Λ)
    (hX : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ m ∈ rightInterval ε x, 1 ≤ lam x m) :
    Task308.ShortDistribution ε
      (ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
        upperDeletedIntegral ω ε + δ) (upperNormCoeff ε lam) := by
  intro A hA
  obtain ⟨Cn, hn⟩ :=
    upper_slack_split_nonprincipal_twisted h4 h9 hω hz hε hε8 hδ hb hX hA
  obtain ⟨Cs, hs⟩ :=
    upper_slack_split_principal_short_prefix h4 h9 hω hz hε hε8 hδ hb hX hA
  obtain ⟨Cl, hl⟩ :=
    upper_slack_split_principal_long_prefix h4 h9 hω hz hε hε8 hδ hb hX hA
  refine ⟨max (max (max Cn Cs) Cl) 4, ?_⟩
  intro x hx q hq hqx χ t ht
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hxn : Cn ≤ x :=
    le_trans (le_trans (le_trans (le_max_left Cn Cs) (le_max_left _ Cl)) (le_max_left _ 4)) hx
  have hxs : Cs ≤ x :=
    le_trans (le_trans (le_trans (le_max_right Cn Cs) (le_max_left _ Cl)) (le_max_left _ 4)) hx
  have hxl : Cl ≤ x :=
    le_trans (le_trans (le_max_right (max Cn Cs) Cl) (le_max_left _ 4)) hx
  have hXnn : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hLnn : (0 : ℝ) ≤ Real.log x ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hCnC : Cn ≤ max (max (max Cn Cs) Cl) 4 :=
    le_trans (le_trans (le_max_left Cn Cs) (le_max_left _ Cl)) (le_max_left _ 4)
  have hCsC : Cs ≤ max (max (max Cn Cs) Cl) 4 :=
    le_trans (le_trans (le_max_right Cn Cs) (le_max_left _ Cl)) (le_max_left _ 4)
  have hClC : Cl ≤ max (max (max Cn Cs) Cl) 4 :=
    le_trans (le_max_right (max Cn Cs) Cl) (le_max_left _ 4)
  have hmono : ∀ {c : ℝ}, c ≤ max (max (max Cn Cs) Cl) 4 →
      c * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        max (max (max Cn Cs) Cl) 4 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    intro c hc
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hXnn) hLnn
  by_cases hχ : χ = 1
  · by_cases hts : t ≤ x ^ (11 / 20 + ε)
    · have h1 := hs x hxs q hq hqx χ hχ t hts
      exact le_trans h1 (hmono hCsC)
    · have h1 := hl x hxl q hq hqx χ hχ t (le_of_lt (lt_of_not_ge hts)) ht
      exact le_trans h1 (hmono hClC)
  · have hd : Thm2.delta χ = 0 := by
      simp [Thm2.delta, hχ]
    have h1 : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε lam x m : ℂ) * χ (m : ZMod q))‖ ≤
        Cn * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hn x hxn q hq hqx χ hχ t ht
    have h2 : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((upperNormCoeff ε lam x m : ℂ) * χ (m : ZMod q))‖ ≤
        max (max (max Cn Cs) Cl) 4 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
      le_trans h1 (hmono hCnC)
    simpa only [hd, zero_mul, zero_div, sub_zero] using h2

end LeanLab.BHP1997.DecompC165d
