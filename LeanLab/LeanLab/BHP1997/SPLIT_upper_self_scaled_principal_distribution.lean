/-
Split of the OPEN leaf `upper_self_scaled_principal_distribution` of
SPLIT_upper_self_scaled_conditions into three smaller leaves, with an assembly that carries that
same statement, proved from them and using no sorry.

The leaf asks for the principal character case of condition iii for the self scaled upper
coefficient: at the density v1 every initial segment of the short interval, truncated at any t up to
twice the level, carries that density to within any power of the logarithm, at every modulus q up to
a power of log x. The character at hand is the trivial one, so the character factor in the summand is
the constant one, and what is left is the discrepancy between the mass of the coefficient on an
initial segment and the density times the number of its elements.

Leaf 1: the trivial character takes the value one, so the character factor disappears.
Leaf 2: below the level the initial segment is empty, so its centred sum is zero there.
Leaf 3: the centred prefix bound with no character present, on segments from the level to twice it.

The assembly splits the truncation at the level, uses leaf 2 below it and leaf 3 above it, and
removes the character factor with leaf 1. This file adds no definition, edits no existing file and
leaves the sealed statement of the imported file untouched. AI wrote the Lean code.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_conditions

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: the trivial character takes the value one. First step of the principal character case: at
every modulus q and every index m the trivial character sends m to 1, so the character factor in the
summand is the constant one, and the character sum reduces to the plain sum of the
coefficient minus its density. -/
theorem upper_self_scaled_principal_trivial_character (q m : ℕ) :
    (1 : DirichletCharacter ℂ q) (m : ZMod q) = 1 := by
  simp [DirichletCharacter.one_apply]

/-- LEAF: the initial segment is empty below the level. Second step, the easy end of the truncation:
rightInterval is the interval from the floor of the level Y to the floor of 2Y, so every index in it
exceeds Y, and when t is at most Y no index survives the filter. The segment is then empty whatever
the coefficient is, and the centred sum over it is zero. Non-vacuity: at t = 0 and x = 4 the
hypotheses hold and the segment is empty. -/
theorem upper_self_scaled_principal_empty_prefix {ε t x : ℝ} (hε : 0 < ε)
    (ht : t ≤ x ^ (11 / 20 + ε)) :
    (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro m hmem hle
  rw [rightInterval, Finset.mem_Ioc] at hmem
  -- every index of `rightInterval` exceeds the level, by the floor gap
  have hfloor : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
    exact_mod_cast hmem.1
  have hgap := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
  have hmY : x ^ (11 / 20 + ε) < (m : ℝ) := by linarith
  exact absurd hle (not_le.mpr (lt_of_le_of_lt ht hmY))

/-- LEAF: the centred prefix bound at the weight scale, with no character present. This is the
analytic content that the leaf carries: for every A the mass of the coefficient on an initial
segment differs from the density per element by at most C times the level times log x to the minus A,
for every t from the level up to twice the level. Neither the character nor the modulus q of the
summation occurs, and the segment begins at the level, so this is strictly easier than the
principal character case of the target. Non-vacuity: at t equal to twice the level the segment is the
whole interval, and the hypotheses on the coefficient are the ones of the imported file. -/
theorem upper_self_scaled_principal_centred_prefix_bound
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then
      Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) - ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

set_option maxHeartbeats 400000 in
/-- The sealed statement of `upper_self_scaled_principal_distribution` of the imported file,
verbatim, assembled from the three leaves. For each power of the logarithm the third leaf gives the
constant of the centred prefix bound; the truncation is split at the level, where the segment is
empty by the second leaf and the inequality is the trivial non-negative bound, and above the level,
where the third leaf applies and the first leaf replaces the character factor by one. No step uses
the sealed statement of the imported file. -/
theorem upper_self_scaled_principal_distribution_split
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
  intro A hA
  obtain ⟨C0, hC0⟩ :=
    upper_self_scaled_principal_centred_prefix_bound h4 h9 hω hz hε hε8 hb A hA
  refine ⟨max (max C0 4) 1, fun x hx q hq hqA t ht => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_max_right C0 4) (le_trans (le_max_left (max C0 4) 1) hx)
  have hx0 : C0 ≤ x := le_trans (le_max_left C0 4) (le_trans (le_max_left (max C0 4) 1) hx)
  have hC0le : C0 ≤ max (max C0 4) 1 :=
    le_trans (le_max_left C0 4) (le_max_left (max C0 4) 1)
  have hCnn : (0 : ℝ) ≤ max (max C0 4) 1 := le_trans zero_le_one (le_max_right (max C0 4) 1)
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hLnn : (0 : ℝ) ≤ Real.log x ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hscale : (0 : ℝ) ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := mul_nonneg hYpos.le hLnn
  by_cases htY : t ≤ x ^ (11 / 20 + ε)
  · have hemp : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := upper_self_scaled_principal_empty_prefix hε htY
    rw [hemp, Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg hCnn hYpos.le) hLnn
  · have htge : x ^ (11 / 20 + ε) ≤ t := le_of_lt (not_le.mp htY)
    have hcore : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) - ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hC0 x hx0 t htge ht
    have hsum : ∀ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b1 x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
          ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε))) =
        ((b1 x m : ℂ) - ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) + upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε))) := by
      intro m hm
      rw [upper_self_scaled_principal_trivial_character q m, mul_one]
    rw [Finset.sum_congr rfl hsum]
    refine le_trans hcore ?_
    calc C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = C0 * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
      _ ≤ max (max C0 4) 1 * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_right hC0le hscale
      _ = max (max C0 4) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Upper312Route
