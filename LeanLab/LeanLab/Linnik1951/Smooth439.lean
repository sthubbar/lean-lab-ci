/-
P0093 page 168 equations 10.5 and 10.6. Finite smooth Euler sums.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Euler439

namespace LeanLab.Linnik1951

open Finset
open LeanLab.HeathBrown1985

/-- P0093 page 168 equation 10.6. The finite prime product is the full
sum over positive integers whose prime factors lie below the cutoff. -/
theorem finite_euler_smooth439 (n Q : ℕ) (hn : 1 ≤ n) :
    (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime,
      (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) =
        ∑' q : Nat.factoredNumbers (Finset.Icc 1 Q), gm n q := by
  have h := EulerProduct.prod_filter_prime_tsum_eq_tsum_factoredNumbers
    (gm_one n) (fun hab => gm_mul n hab) (summable_abs_gm n hn) (Finset.Icc 1 Q)
  rw [← h]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  rw [gm_prime_pow_tsum n p hprime]
  by_cases hd : p ∣ n
  · rw [if_pos hd, vloc_dvd hprime hd]
  · rw [if_neg hd, vloc_not_dvd hprime hd]
    ring

/-- P0093 page 168 equation 10.5. An arbitrary finite subset of the
absolute coefficient tail obeys the existing Heath Brown divisor bound.
The zero term can be included because its coefficient vanishes. -/
theorem finite_absolute_tail439 (n Q : ℕ) (hn : 1 ≤ n) (hQ : 1 ≤ Q)
    (s : Finset ℕ) (hs : ∀ q ∈ s, q = 0 ∨ Q < q) :
    ∑ q ∈ s, |gm n q| ≤
      4 * ((6 + 2 * Real.log Q) * (n.divisors.card : ℝ) ^ 2 / Q) := by
  classical
  have heq : ∑ q ∈ s, |gm n q| = ∑ q ∈ s.erase 0, |gm n q| := by
    symm
    apply Finset.sum_subset (Finset.erase_subset _ _)
    intro q hq hnot
    have : q = 0 := by simpa only [Finset.mem_erase, hq, and_true, not_not] using hnot
    simp [this, gm_zero]
  rw [heq]
  have hsub : s.erase 0 ⊆ Finset.Ioc Q (s.sup id) := by
    intro q hq
    obtain ⟨hq0, hqs⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_Ioc.mpr ⟨(hs q hqs).resolve_left hq0, Finset.le_sup (f := id) hqs⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans
    (sum_abs_gm_Ioc_le n Q (s.sup id) hn hQ)

/-- P0093 page 168 equation 10.5. The omitted smooth coefficients all
lie in the ordinary tail. This retains the divisor count squared and the
logarithmic cutoff factor, without asserting a uniform rate in the residual. -/
theorem finite_product_absolute_error439 (n Q : ℕ) (hn : 1 ≤ n) (hQ : 1 ≤ Q) :
    |(∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime,
      (if p ∣ n then 1 + 1 / ((p : ℝ) - 1) else 1 - 1 / ((p : ℝ) - 1) ^ 2)) -
        ∑' q : ℕ, gm n q| ≤
          4 * ((6 + 2 * Real.log Q) * (n.divisors.card : ℝ) ^ 2 / Q) := by
  classical
  let S := Nat.factoredNumbers (Finset.Icc 1 Q)
  have ha := summable_abs_gm n hn
  have hsplit := ha.of_norm.tsum_subtype_add_tsum_subtype_compl S
  rw [finite_euler_smooth439 n Q hn, ← hsplit, sub_add_cancel_left, abs_neg]
  refine (norm_tsum_le_tsum_norm (ha.subtype _)).trans ?_
  apply Real.tsum_le_of_sum_le
  · intro q
    exact norm_nonneg _
  intro s
  have heq : ∑ q ∈ s, ‖gm n q‖ = ∑ q ∈ s.image (fun q : {q : ℕ // q ∉ S} => (q : ℕ)), |gm n q| := by
    rw [Finset.sum_image]
    · simp only [Real.norm_eq_abs]
      rfl
    · exact fun _ _ _ _ h => Subtype.ext h
  rw [heq]
  apply finite_absolute_tail439 n Q hn hQ
  intro q hq
  obtain ⟨q, hqs, rfl⟩ := Finset.mem_image.mp hq
  by_cases hq0 : (q : ℕ) = 0
  · exact Or.inl hq0
  · right
    by_contra hle
    have hsmall : (q : ℕ) ≤ Q := by omega
    apply q.property
    apply Nat.mem_factoredNumbers_iff_forall_le.mpr
    refine ⟨hq0, ?_⟩
    intro p hp hprime hpd
    exact Finset.mem_Icc.mpr ⟨hprime.one_le, hp.trans hsmall⟩

end LeanLab.Linnik1951
