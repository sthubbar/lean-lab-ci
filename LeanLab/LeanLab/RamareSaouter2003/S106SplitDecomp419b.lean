import LeanLab.RamareSaouter2003.Decomp419b

/-!
S106 split of Decomp419b.backlund_zero_mass_count.
Backlund pp. 357 to 360, displays 45 to 50, and Rosser pp. 223 and 224.
The selection step of Jensen's inequality on Backlund p. 360, that keeping
only some zeros can only decrease the zero mass, is proved here.
The argument principle and the pairing of zeros remain one HARD leaf.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.S106SplitDecomp419b
open Real Complex MeasureTheory Decomp359g Decomp419b

/-- LEAF: Backlund p. 360, the selection remark after display 49.
Keeping only the zeros in a finite set s can only decrease the Jensen
zero mass, since every divisor weight of the analytic G is nonnegative
and every logarithmic weight in the closed disk is nonnegative. PROVED. -/
theorem selected_mass_le (T : ℝ) (hT : 1400 ≤ T) (N : ℕ) (s : Finset ℂ) :
    ∑ z ∈ s, (MeromorphicOn.divisor (poweredZeta T N)
      (Metric.closedBall 0 |(1.32 : ℝ)|) z : ℝ) * Real.log (1.32 * ‖(0 : ℂ) - z‖⁻¹) ≤
      zeroMass T N := by
  set D := MeromorphicOn.divisor (poweredZeta T N) (Metric.closedBall 0 |(1.32 : ℝ)|)
  set f : ℂ → ℝ := fun z => (D z : ℝ) * Real.log (1.32 * ‖(0 : ℂ) - z‖⁻¹) with hf
  have hD : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg (powered_analytic T hT N)
  have hfin := D.finiteSupport (isCompact_closedBall 0 _)
  have hnn : ∀ z, 0 ≤ f z := by
    intro z
    by_cases hz : D z = 0
    · simp [hf, hz]
    have hzb : z ∈ Metric.closedBall (0 : ℂ) |(1.32 : ℝ)| := D.supportWithinDomain hz
    have hDz : (0 : ℝ) ≤ (D z : ℝ) := by exact_mod_cast hD z
    refine mul_nonneg hDz ?_
    by_cases h0 : z = 0
    · simp [h0]
    have hn : ‖z‖ ≤ 1.32 := by
      simpa [Metric.mem_closedBall, dist_zero_right,
        abs_of_pos (by norm_num : (0 : ℝ) < 1.32)] using hzb
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr h0
    apply Real.log_nonneg
    rw [zero_sub, norm_neg, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
    exact hn
  have hsupp : Function.support f ⊆ (hfin.toFinset : Set ℂ) := by
    intro z hz
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h
    apply hz
    simp [hf, h]
  have hmass : zeroMass T N = ∑ z ∈ hfin.toFinset, f z :=
    finsum_eq_sum_of_support_subset f hsupp
  rw [hmass]
  calc ∑ z ∈ s, f z ≤ ∑ z ∈ s ∪ hfin.toFinset, f z :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun z _ _ => hnn z)
    _ = ∑ z ∈ hfin.toFinset, f z := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z _ hz
        have : z ∉ Function.support f := fun h => hz (by exact_mod_cast hsupp h)
        simpa using this

/-- LEAF: Backlund pp. 357 to 360, displays 45 to 48, with Rosser p. 224 for
the N-th powers. HARD for Codex. The argument principle along the path from
5/4 to 1/2 at height T bounds the count error by n divided by N plus the
fixed terms, where n counts the last passages of the argument of zeta to
the N through the odd multiples of pi over two. These are zeros of G on the
real segment from minus 3/4 to 0. Backlund's symmetry estimate 44 and
display 48 pair them with zeros on the reflected segment, so a finite set s
of zeros carries Jensen weight at least 2 q n up to a constant independent
of N. The selection of s inside the full zero mass is selected_mass_le. -/
theorem backlund_selected_zeros (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ N : ℕ, 0 < N → poweredZeta T N 0 ≠ 0 →
      ∃ n : ℕ, ∃ s : Finset ℂ,
        |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
          (n : ℝ) / N + 1 / 2 + 4 / (π * T) + |gammaRemainder T| / π + c / N ∧
        2 * Real.log (4 * 1.32 / 3) * n ≤
          ∑ z ∈ s, (MeromorphicOn.divisor (poweredZeta T N)
            (Metric.closedBall 0 |(1.32 : ℝ)|) z : ℝ) *
              Real.log (1.32 * ‖(0 : ℂ) - z‖⁻¹) + c := by
  sorry

/-- Exactly the statement of Decomp419b.backlund_zero_mass_count.
CONDITIONAL ON backlund_selected_zeros. No sorry occurs in this assembly. -/
theorem backlund_zero_mass_count (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ N : ℕ, 0 < N → poweredZeta T N 0 ≠ 0 →
      |L1Zeta.NZr T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
        zeroMass T N / (2 * Real.log (4 * 1.32 / 3) * N) +
          1 / 2 + 4 / (π * T) + |gammaRemainder T| / π + k / N := by
  obtain ⟨c, hc, h⟩ := backlund_selected_zeros A T hA hFA hT
  have hq : 0 < Real.log (4 * 1.32 / 3) := Real.log_pos (by norm_num)
  refine ⟨c + c / (2 * Real.log (4 * 1.32 / 3)), by positivity, fun N hN hG => ?_⟩
  obtain ⟨n, s, hcount, hpair⟩ := h N hN hG
  have hsel := selected_mass_le T (hA.trans hT) N s
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set q := Real.log (4 * 1.32 / 3)
  have hn : (n : ℝ) / N ≤ (zeroMass T N + c) / (2 * q * N) := by
    rw [div_le_div_iff₀ hNpos (by positivity)]
    nlinarith
  have heq : (zeroMass T N + c) / (2 * q * N) =
      zeroMass T N / (2 * q * N) + c / (2 * q) / N := by
    field_simp
  have heq2 : (c + c / (2 * q)) / N = c / N + c / (2 * q) / N := by ring
  rw [heq2]
  linarith

end LeanLab.RamareSaouter2003.S106SplitDecomp419b

#print axioms LeanLab.RamareSaouter2003.S106SplitDecomp419b.selected_mass_le
#print axioms LeanLab.RamareSaouter2003.S106SplitDecomp419b.backlund_selected_zeros
#print axioms LeanLab.RamareSaouter2003.S106SplitDecomp419b.backlund_zero_mass_count
