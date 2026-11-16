/-
P0069, Section 5, page 51, display 5.17.
Counting the exponent cells that meet finitely many boundary hyperplanes
on a fixed coordinate fibre. Endpoint cells are counted on both sides.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentMesh517
import Mathlib.Order.SuccPred.IntervalSucc

namespace LeanLab.BHP1997.LowerShortC165
open Classical
open scoped BigOperators

/-- Page 51 display 5.17. A threshold belongs to at most one half open cell
of a monotone grid. This uses Mathlib's disjoint adjacent intervals. -/
theorem four_exponent_halfopen_boundary_card (e : ℕ → ℝ) (he : Monotone e)
    (S : Finset ℕ) (t : ℝ) :
    (S.filter (fun n => e n < t ∧ t ≤ e (n+1))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hne
  have hd := he.pairwise_disjoint_on_Ioc_succ hne
  exact Set.disjoint_left.mp hd
    (by simpa [Set.mem_Ioc, Order.succ_eq_add_one] using (Finset.mem_filter.mp ha).2)
    (by simpa [Set.mem_Ioc, Order.succ_eq_add_one] using (Finset.mem_filter.mp hb).2)

/-- Page 51 display 5.17. A threshold meets at most two closed cells of a
strict grid. The factor two includes a threshold at a common endpoint. -/
theorem four_exponent_closed_boundary_card (e : ℕ → ℝ) (he : StrictMono e)
    (S : Finset ℕ) (t : ℝ) :
    (S.filter (fun n => e n ≤ t ∧ t ≤ e (n+1))).card ≤ 2 := by
  have heq : (S.filter (fun n => e n = t)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact he.injective ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hsub : S.filter (fun n => e n ≤ t ∧ t ≤ e (n+1)) ⊆
      S.filter (fun n => e n < t ∧ t ≤ e (n+1)) ∪ S.filter (fun n => e n = t) := by
    intro n hn
    obtain ⟨hnS, hlo, hhi⟩ := Finset.mem_filter.mp hn
    rcases hlo.eq_or_lt with h | h
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnS, h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnS, h, hhi⟩)
  calc _ ≤ (S.filter (fun n => e n < t ∧ t ≤ e (n+1)) ∪
        S.filter (fun n => e n = t)).card := Finset.card_le_card hsub
    _ ≤ (S.filter (fun n => e n < t ∧ t ≤ e (n+1))).card +
        (S.filter (fun n => e n = t)).card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := add_le_add (four_exponent_halfopen_boundary_card e he.monotone S t) heq
    _ = 2 := rfl

/-- Page 51 display 5.17. On a fibre with a strict grid, the cells that meet
any of finitely many thresholds number at most twice the threshold count. -/
theorem four_exponent_boundary_card (e : ℕ → ℝ) (he : StrictMono e)
    (S : Finset ℕ) (T : Finset ℝ) :
    (S.filter (fun n => ∃ t ∈ T, e n ≤ t ∧ t ≤ e (n+1))).card ≤ 2 * T.card := by
  have hu : S.filter (fun n => ∃ t ∈ T, e n ≤ t ∧ t ≤ e (n+1)) =
      T.biUnion (fun t => S.filter (fun n => e n ≤ t ∧ t ≤ e (n+1))) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hn, t, ht, hlo, hhi⟩
      exact ⟨t, ht, hn, hlo, hhi⟩
    · rintro ⟨t, ht, hn, hlo, hhi⟩
      exact ⟨hn, t, ht, hlo, hhi⟩
  rw [hu]
  calc _ ≤ ∑ t ∈ T, (S.filter (fun n => e n ≤ t ∧ t ≤ e (n+1))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 2 := Finset.sum_le_sum (fun t _ => four_exponent_closed_boundary_card e he S t)
    _ = 2 * T.card := by simp [mul_comm]

/-- Page 51 display 5.17. If a boundary cell costs at most D, the total
boundary cost on a coordinate fibre is at most twice the threshold count times D. -/
theorem four_exponent_boundary_sum (e : ℕ → ℝ) (he : StrictMono e)
    (S : Finset ℕ) (T : Finset ℝ) (r : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hr : ∀ n ∈ S, (∃ t ∈ T, e n ≤ t ∧ t ≤ e (n+1)) → |r n| ≤ D) :
    ∑ n ∈ S.filter (fun n => ∃ t ∈ T, e n ≤ t ∧ t ≤ e (n+1)), |r n| ≤
      (2 * T.card : ℕ) * D := by
  calc _ ≤ ∑ _n ∈ S.filter (fun n => ∃ t ∈ T, e n ≤ t ∧ t ≤ e (n+1)), D := by
        apply Finset.sum_le_sum
        intro n hn
        exact hr n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
    _ = ((S.filter (fun n => ∃ t ∈ T, e n ≤ t ∧ t ≤ e (n+1))).card : ℝ) * D := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * T.card : ℕ) * D :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast four_exponent_boundary_card e he S T) hD

#print axioms four_exponent_halfopen_boundary_card
#print axioms four_exponent_closed_boundary_card
#print axioms four_exponent_boundary_card
#print axioms four_exponent_boundary_sum
end LeanLab.BHP1997.LowerShortC165
