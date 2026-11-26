/-
Reduction of the two open range leaves `prime_minor_multi_525_mid` and
`prime_minor_multi_525_long` of SPLIT_prime_minor_multi_525.lean, burst S10.

Source: Bhowmik and Grimmelt 2026, arXiv 2607.27282, page 27, proof of Lemma 7.3,
display 7.8, minor arc part, which applies the argument of Lemma 4.2, page 16, to the
smoothed sum.

The parent `prime_minor_multi_525` has word for word the statement of
`prime_minor_multi_451`, which burst feed1122 already split and wired in
LEAF_feed1122_prime_minor_multi_451.lean as `prime_minor_multi_451_from_leaves`, from:

* `split_leaf_ssum_minor_log2`, the pointwise minor arc bound at log power two, the
  QUESTION 2 input of the folder, which LEAVES THE PAPER: display 4.8 prints power four
  and the displayed proof of Lemma 4.2 then gives power nine, see `minor_second_moment84`;
* `leaf_nonprime_partial_feed1122`, MEDIUM, removing the higher prime powers;
* `leaf_prime_family_feed1122`, MEDIUM, the family second moment with the supremum
  pulled out, the prime analogue of the PROVED `supported_family_sharp261`, whose
  weighted variation argument is what handles the N dependence of phi of n over N
  that the single function Bessel step of page 16 does not.

Each range leaf is the parent sum with the terms outside one range switched off, so it
follows from the parent bound with the same constant. No new sorry: both units are
CONDITIONAL ON the three open leaves above. AI wrote the Lean code. Binary Goldbach is
open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_prime_minor_multi_525
import LeanLab.BhowmikGrimmelt2026.LEAF_feed1122_prime_minor_multi_451

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- Switching off part of a family of nonnegative terms does not increase its sum. -/
theorem sum_ite_le_S10 (X : ℕ) (p : ℕ → Prop) {inst : DecidablePred p} (f : ℕ → ℝ)
    (hf : ∀ N, 0 ≤ f N) :
    ∑ N ∈ Finset.Icc 1 X, (if p N then f N else 0) ≤ ∑ N ∈ Finset.Icc 1 X, f N := by
  refine Finset.sum_le_sum fun N _ => ?_
  split_ifs
  · exact le_rfl
  · exact hf N

/-- Assembly of `prime_minor_multi_525_mid` exact statement, from `prime_minor_multi_451_from_leaves`, whose statement is word for word that of the parent `prime_minor_multi_525`. -/
theorem prime_minor_multi_525_mid_S10 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if Nat.sqrt X < N ∧ N ≤ (Nat.sqrt X + X) / 2 then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := prime_minor_multi_451_from_leaves hϕ ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX hR =>
    (sum_ite_le_S10 X _ _ (fun N => sq_nonneg _)).trans (h X hX hR)⟩

/-- Assembly of `prime_minor_multi_525_long` exact statement, from `prime_minor_multi_451_from_leaves`, whose statement is word for word that of the parent `prime_minor_multi_525`. -/
theorem prime_minor_multi_525_long_S10 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → 2 ≤ (X : ℝ) ^ ϑ →
      (∑ N ∈ Finset.Icc 1 X,
        (if (Nat.sqrt X + X) / 2 < N then
          ‖∫ α in (0 : ℝ)..1, if MajorArc X ((X : ℝ) ^ ϑ) α then 0 else (∑ n ∈ (Finset.range (X + 1)).filter (fun n => n.Prime), ((vonMangoldt n * ϕ (n / N) : ℝ) : ℂ) * ee (α * n)) ^ 2 * ee (-(N * α))‖ ^ 2
        else 0)) ≤
        C * (((X : ℝ) ^ ϑ)⁻¹ + (X : ℝ) ^ (-(2 / 5) : ℝ)) * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C, hC, h⟩ := prime_minor_multi_451_from_leaves hϕ ϑ hϑ hϑ'
  exact ⟨C, hC, fun X hX hR =>
    (sum_ite_le_S10 X _ _ (fun N => sq_nonneg _)).trans (h X hX hR)⟩

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.sum_ite_le_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_mid_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prime_minor_multi_525_long_S10
