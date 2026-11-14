/-
Jia 1996 pages 269 to 286, Lemmas 24 to 28.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Geometry316

namespace LeanLab.Languasco2004.GroupSplit548
open Finset Real Decomp279a Decomp316c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Display 52: select one region when selected is true and its group
complement when false. Both retain the finite caps and recovery clipping. -/
def pieceSum (j i : ℕ) (selected : Bool) (N Y : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
    Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
    ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
      if groupOf (regionIndex Y p q) = j ∧ decide (regionIndex Y p q = i) = selected
        then (sifted N Y n (p * q) q : ℝ) else 0

/-- Display 52: a region and its complement partition the group. -/
theorem pieceSum_add (j i : ℕ) (N Y : ℝ) (n : ℕ) :
    pieceSum j i true N Y n + pieceSum j i false N Y n = groupSum j N Y n := by
  unfold pieceSum groupSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  by_cases hg : groupOf (regionIndex Y p q) = j <;>
    by_cases hi : regionIndex Y p q = i <;> simp [hg, hi]

/-- Display 52: each selected contribution is nonnegative. -/
theorem pieceSum_nonneg (j i : ℕ) (selected : Bool) (N Y : ℝ) (n : ℕ) :
    0 ≤ pieceSum j i selected N Y n := by
  unfold pieceSum
  apply sum_nonneg
  intro p hp
  apply sum_nonneg
  intro q hq
  split_ifs <;> positivity

/-- Lemmas 24 to 28: failure of the sum bound forces a component failure. -/
theorem bad_subset_union (w : Finset ℕ) (f g m : ℕ → ℝ) (a b : ℝ) :
    w.filter (fun n => f n + g n < (a + b) * m n) ⊆
      w.filter (fun n => f n < a * m n) ∪ w.filter (fun n => g n < b * m n) := by
  intro n hn
  obtain ⟨hnw, hn⟩ := mem_filter.mp hn
  by_cases hf : f n < a * m n
  · exact mem_union_left _ (mem_filter.mpr ⟨hnw, hf⟩)
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨hnw, ?_⟩
    push Not at hf
    nlinarith

/-- Lemmas 24 to 28: combine two exceptional estimates at fixed parameters. -/
theorem combine_counts (w : Finset ℕ) (f g h m : ℕ → ℝ) (a b c K L : ℝ)
    (hc : a + b = c) (hadd : ∀ n, f n + g n = h n)
    (hf : ((w.filter (fun n => f n < a * m n)).card : ℝ) ≤ K)
    (hg : ((w.filter (fun n => g n < b * m n)).card : ℝ) ≤ L) :
    ((w.filter (fun n => h n < c * m n)).card : ℝ) ≤ K + L := by
  have hs := bad_subset_union w f g m a b
  simp only [hadd, hc] at hs
  have hn := (card_le_card hs).trans (card_union_le _ _)
  have hr : ((w.filter (fun n => h n < c * m n)).card : ℝ) ≤
      ((w.filter (fun n => f n < a * m n)).card : ℝ) +
      ((w.filter (fun n => g n < b * m n)).card : ℝ) := by exact_mod_cast hn
  exact hr.trans (add_le_add hf hg)

/-- Pages 267 to 269: the assigned region equals a label exactly when
its original source inequalities hold, on the positive source domain. -/
theorem regionIndex_eq_iff (i : Fin 69) (Y : ℝ) (p q : ℕ)
    (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q) :
    regionIndex Y p q = i.val + 1 ↔
      Y ^ (regionData (i.val + 1) 0 : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ Y ^ (regionData (i.val + 1) 1 : ℝ) ∧
      (p : ℝ) ^ (regionData (i.val + 1) 2 : ℝ) *
        Y ^ (regionData (i.val + 1) 3 : ℝ) < (q : ℝ) ∧
      (q : ℝ) < (p : ℝ) ^ (regionData (i.val + 1) 4 : ℝ) *
        Y ^ (regionData (i.val + 1) 5 : ℝ) := by
  constructor
  · intro heq
    unfold regionIndex at heq
    split_ifs at heq with hex
    · have hs := Nat.find_spec hex
      rw [heq] at hs
      exact hs.2
  · exact Geometry316.regionIndex_eq_of_mem i Y p q hY hp hq

/-- Pages 267 to 269: the selected piece is precisely its source region
sum with the sealed finite caps. No priority or clipping premise is admitted. -/
theorem pieceSum_true_eq_source (i : Fin 69) (j : ℕ) (N Y : ℝ) (n : ℕ)
    (hY : 1 < Y) (hgroup : groupOf (i.val + 1) = j) :
    pieceSum j (i.val + 1) true N Y n =
      ∑ p ∈ (range (n + 1)).filter (fun p : ℕ => p.Prime ∧
        Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt (2 * Y)),
        ∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          Y ^ (16 / 135 : ℝ) < (q : ℝ) ∧
          (q : ℝ) < min (p : ℝ) (Real.sqrt (2 * Y / (p : ℝ)))),
          if Y ^ (regionData (i.val + 1) 0 : ℝ) < (p : ℝ) ∧
              (p : ℝ) ≤ Y ^ (regionData (i.val + 1) 1 : ℝ) ∧
              (p : ℝ) ^ (regionData (i.val + 1) 2 : ℝ) *
                Y ^ (regionData (i.val + 1) 3 : ℝ) < (q : ℝ) ∧
              (q : ℝ) < (p : ℝ) ^ (regionData (i.val + 1) 4 : ℝ) *
                Y ^ (regionData (i.val + 1) 5 : ℝ)
            then (sifted N Y n (p * q) q : ℝ) else 0 := by
  unfold pieceSum
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  have hi := regionIndex_eq_iff i Y p q hY
    (mem_filter.mp hp).2.1.pos (mem_filter.mp hq).2.1.pos
  by_cases heq : regionIndex Y p q = i.val + 1
  · simp [heq, hgroup, hi.mp heq]
  · have hnot := mt hi.mpr heq
    simp [heq, hnot]

/-- Empty finite caps give concrete values for either piece. -/
theorem pieceSum_empty (j i : ℕ) (selected : Bool) (N Y : ℝ) :
    pieceSum j i selected N Y 0 = 0 := by
  unfold pieceSum
  apply sum_eq_zero
  intro p hp
  obtain ⟨hp, hprime, _⟩ := mem_filter.mp hp
  have hp0 : p = 0 := by have := mem_range.mp hp; omega
  subst p
  exact False.elim ((by decide : ¬ Nat.Prime 0) hprime)

/-- Nonempty unit mass data satisfy every premise of the finite assembly. -/
theorem combine_counts_instance :
    ((({0} : Finset ℕ).filter (fun _ => (2 : ℝ) < (1 + 1) * 1)).card : ℝ) ≤ 0 + 0 := by
  have h := combine_counts ({0} : Finset ℕ) (fun _ => (1 : ℝ)) (fun _ => 1)
    (fun _ => 2) (fun _ => 1) 1 1 2 0 0
    (by norm_num) (by intro n; norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢

/-- Pages 267 to 269: every printed row has a strict rational interior.
This certifies geometric nonemptiness, without asserting prime distribution. -/
theorem region_interior_certificate : ∀ i : Fin 69,
    let r := regionData (i.val + 1)
    let x := (r 0 + r 1) / 2
    let y := (r 2 * x + r 3 + (r 4 * x + r 5)) / 2
    r 0 < x ∧ x < r 1 ∧ r 2 * x + r 3 < y ∧ y < r 4 * x + r 5 := by
  decide +kernel

/-- Lemmas 24 to 28: every chosen split has a distinct label on each side. -/
theorem split_label_certificate :
    groupOf 11 = 1 ∧ groupOf 14 = 1 ∧ (11 : ℕ) ≠ 14 ∧
    groupOf 47 = 2 ∧ groupOf 50 = 2 ∧ (47 : ℕ) ≠ 50 ∧
    groupOf 4 = 3 ∧ groupOf 6 = 3 ∧ (4 : ℕ) ≠ 6 ∧
    groupOf 30 = 4 ∧ groupOf 33 = 4 ∧ (30 : ℕ) ≠ 33 ∧
    groupOf 1 = 5 ∧ groupOf 2 = 5 ∧ (1 : ℕ) ≠ 2 := by
  norm_num [groupOf]

#print axioms pieceSum_add
#print axioms pieceSum_nonneg
#print axioms bad_subset_union
#print axioms combine_counts
#print axioms regionIndex_eq_iff
#print axioms pieceSum_true_eq_source
#print axioms pieceSum_empty
#print axioms combine_counts_instance
#print axioms region_interior_certificate
#print axioms split_label_certificate
end
end LeanLab.Languasco2004.GroupSplit548
