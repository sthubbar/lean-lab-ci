/-
Jia 1996 pages 282 to 285, displays 57 to 64.
Source https://doi.org/10.4064/aa-77-3-207-287.
Finite source sums for the two proper parts of Lemma 28.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Sieve565
import LeanLab.Languasco2004.GroupSplit548

namespace LeanLab.Languasco2004.Source565
open Finset Real Decomp279a Decomp316a Decomp316c GroupSplit548 Sieve565
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Display 57 and page 285: the selected pair domain with the source exponent truncation. -/
def pairDomain (selected : Bool) (Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n + 1)).product (range (n + 1))).filter (fun pq =>
    pq.1.Prime ∧ Y ^ (16 / 135 : ℝ) < (pq.1 : ℝ) ∧
    (pq.1 : ℝ) ≤ Real.sqrt (2 * Y) ∧
    pq.2.Prime ∧ Y ^ (16 / 135 : ℝ) < (pq.2 : ℝ) ∧
    (pq.2 : ℝ) < min (pq.1 : ℝ) (Real.sqrt (2 * Y / (pq.1 : ℝ))) ∧
    groupOf (regionIndex Y pq.1 pq.2) = 5 ∧
    decide (regionIndex Y pq.1 pq.2 = 1) = selected ∧
    (selected = true → (pq.1 : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)))

/-- Displays 58 and 62: the A or B source set before applying the prime sieve. -/
def sourceSet (model : Bool) (N Y : ℝ) (n d : ℕ) : Finset ℕ :=
  (Icc 1 n).filter (fun a => d ∣ a ∧
    if model then Y < (a : ℝ) ∧ (a : ℝ) ≤ 2 * Y
    else (n - a).Prime ∧ N - Y < ((n - a : ℕ) : ℝ) ∧ ((n - a : ℕ) : ℝ) ≤ N)

/-- Displays 58 and 60: the pair contribution at a specified sieve cutoff.
The B model sifts by all primes. The A set excludes primes dividing n. -/
def pairMass (model selected : Bool) (N Y : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ∑ pq ∈ pairDomain selected Y n,
    ((sieved (sourceSet model N Y n (pq.1 * pq.2)) (if model then 1 else n) z).card : ℝ)

/-- Display 59: the low cutoff terms removed from the pair contribution. -/
def pairRemoved (model selected : Bool) (N Y : ℝ) (n : ℕ) (z α : ℝ) : ℝ :=
  ∑ pq ∈ pairDomain selected Y n,
    lowLayers (sourceSet model N Y n (pq.1 * pq.2)) (if model then 1 else n) z α

/-- Displays 61 and 62: the relaxed triple contribution at a specified cutoff. -/
def tripleMass (model selected : Bool) (N Y : ℝ) (n : ℕ) (α z : ℝ) : ℝ :=
  ∑ pq ∈ pairDomain selected Y n,
    tripleSieved n (sourceSet model N Y n (pq.1 * pq.2)) (if model then 1 else n) α pq.2 z

/-- Display 63: the low cutoff terms removed from the triple contribution. -/
def tripleRemoved (model selected : Bool) (N Y : ℝ) (n : ℕ) (α z : ℝ) : ℝ :=
  ∑ pq ∈ pairDomain selected Y n,
    tripleLayers n (sourceSet model N Y n (pq.1 * pq.2)) (if model then 1 else n) α pq.2 z

/-- Displays 58 and 62: the sum of the two absolute Iwaniec transfer errors. -/
def iwaniecError (selected : Bool) (N Y : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  |pairMass false selected N Y n (Y ^ delta ε) -
    singular n / log N * pairMass true selected N Y n (Y ^ delta ε)| +
  |tripleMass false selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε) -
    singular n / log N * tripleMass true selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε)|

/-- Displays 59 and 63: the sum of the two absolute Lemma 19 transfer errors. -/
def lemma19Error (selected : Bool) (N Y : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  |pairRemoved false selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)) -
    singular n / log N * pairRemoved true selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ))| +
  |tripleRemoved false selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε) -
    singular n / log N * tripleRemoved true selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε)|

/-- Display 60: the model pair contribution after exact cancellation. -/
def modelPair (selected : Bool) (N Y : ℝ) (n : ℕ) : ℝ :=
  singular n / log N * pairMass true selected N Y n (Y ^ (16 / 135 : ℝ))

/-- Page 284 after display 63: the model triple contribution after exact cancellation. -/
def modelTriple (selected : Bool) (N Y : ℝ) (n : ℕ) : ℝ :=
  singular n / log N * tripleMass true selected N Y n
    (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ))

/-- Displays 58 and 62: every source integer is positive and below the common finite cap. -/
theorem sourceSet_bounds (model : Bool) (N Y : ℝ) (n d : ℕ) :
    ∀ a ∈ sourceSet model N Y n d, 0 < a ∧ a ≤ n := by
  intro a ha
  obtain ⟨ha, _⟩ := mem_filter.mp ha
  obtain ⟨h1, h2⟩ := mem_Icc.mp ha
  exact ⟨by omega, h2⟩

/-- Display 57: the A source count is the sealed sifted count. -/
theorem sourceSet_A_count (N Y : ℝ) (n d : ℕ) (z : ℝ) :
    (sieved (sourceSet false N Y n d) n z).card = sifted N Y n d z := by
  unfold sieved sourceSet sifted
  congr 1
  ext a
  simp only [mem_filter, Bool.false_eq_true, ite_false]
  tauto

/-- Display 60: cancel the low cutoff terms across the entire pair family. -/
theorem pair_cancellation (model selected : Bool) (N Y : ℝ) (n : ℕ) (z α : ℝ)
    (hz : z ≤ α) :
    pairMass model selected N Y n z - pairRemoved model selected N Y n z α =
      pairMass model selected N Y n α := by
  unfold pairMass pairRemoved
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro pq hpq
  exact low_cutoff_cancellation _ (if model then 1 else n) z α
    (fun a ha => (sourceSet_bounds model N Y n _ a ha).1) hz

/-- Displays 62 and 63: cancel the low cutoff terms across the entire triple family. -/
theorem triples_cancellation (model selected : Bool) (N Y : ℝ) (n : ℕ) (z α : ℝ)
    (hz : z ≤ α) :
    tripleMass model selected N Y n α z - tripleRemoved model selected N Y n α z =
      tripleMass model selected N Y n α α := by
  unfold tripleMass tripleRemoved
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro pq hpq
  exact triple_cancellation n _ (if model then 1 else n) α pq.2 z
    (fun a ha => (sourceSet_bounds model N Y n _ a ha).1) hz

/-- Display 57: retaining only the truncated pair domain lowers the selected contribution. -/
theorem pair_domain_le_piece (selected : Bool) (N Y : ℝ) (n : ℕ) :
    (∑ pq ∈ pairDomain selected Y n, (sifted N Y n (pq.1 * pq.2) pq.2 : ℝ)) ≤
      pieceSum 5 1 selected N Y n := by
  unfold pairDomain pieceSum
  rw [sum_filter]
  rw [Finset.product_eq_sprod, Finset.sum_product]
  rw [sum_filter]
  apply sum_le_sum
  intro p hp
  simp only [Prod.fst, Prod.snd]
  by_cases hP : p.Prime ∧ Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ Real.sqrt (2 * Y)
  · simp only [hP, ite_true]
    rw [sum_filter]
    apply sum_le_sum
    intro q hq
    split_ifs <;> first | exact le_rfl | positivity | tauto
  · simp only [hP, ite_false]
    apply sum_nonpos
    intro q hq
    split_ifs with hFull
    · exact False.elim (hP ⟨hFull.1, hFull.2.1, hFull.2.2.1⟩)
    · exact le_rfl

/-- Displays 57 to 63: finite Buchstab subtraction for the actual selected pair family. -/
theorem family_buchstab_lower (selected : Bool) (N Y : ℝ) (n : ℕ) (z : ℝ)
    (hz : z ≤ Y ^ (16 / 135 : ℝ)) :
    pairMass false selected N Y n z - pairRemoved false selected N Y n z (Y ^ (16 / 135 : ℝ)) -
      (tripleMass false selected N Y n (Y ^ (16 / 135 : ℝ)) z -
        tripleRemoved false selected N Y n (Y ^ (16 / 135 : ℝ)) z) ≤
      pieceSum 5 1 selected N Y n := by
  apply le_trans _ (pair_domain_le_piece selected N Y n)
  unfold pairMass pairRemoved tripleMass tripleRemoved
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_le_sum
  intro pq hpq
  have hα : Y ^ (16 / 135 : ℝ) ≤ (pq.2 : ℝ) :=
    le_of_lt (mem_filter.mp hpq).2.2.2.2.2.1
  have hb := buchstab_lower n (sourceSet false N Y n (pq.1 * pq.2)) n z
    (Y ^ (16 / 135 : ℝ)) pq.2 (sourceSet_bounds false N Y n _) hz hα
  simpa only [Bool.false_eq_true, ite_false, sourceSet_A_count] using hb

/-- Pages 208 and 283: a fixed positive epsilon cutoff guarantees ordered sieve cutoffs. -/
theorem delta_cutoff (ε : ℝ) (hε : 0 < ε) (hsmall : ε ≤ (16 / 135 : ℝ)^3) :
    delta ε ≤ 16 / 135 := by
  have h := Real.rpow_le_rpow hε.le hsmall (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
  have he : (((16 / 135 : ℝ)^3) ^ (3 : ℝ)⁻¹) = 16 / 135 :=
    Real.pow_rpow_inv_natCast (n := 3) (by norm_num) (by decide)
  rw [he] at h
  simpa only [delta, one_div] using h

/-- Displays 58 to 64: the two transfer errors and the two model bounds imply the region bound. -/
theorem pointwise_from_transfers (selected : Bool) (N Y : ℝ) (n : ℕ) (ε m t : ℝ)
    (hz : Y ^ delta ε ≤ Y ^ (16 / 135 : ℝ)) (hs : 0 ≤ scale N Y n)
    (hI : iwaniecError selected N Y n ε ≤ 0.0000001 * scale N Y n)
    (h19 : lemma19Error selected N Y n ε ≤ 0.0000001 * scale N Y n)
    (hP : (m + 0.0000004) * scale N Y n ≤ modelPair selected N Y n)
    (hT : modelTriple selected N Y n ≤ (t + 0.0000001) * scale N Y n) :
    (m - t) * scale N Y n ≤ pieceSum 5 1 selected N Y n := by
  have hfinite := family_buchstab_lower selected N Y n (Y ^ delta ε) hz
  have hp := pair_cancellation true selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)) hz
  have ht := triples_cancellation true selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)) hz
  have hp' : modelPair selected N Y n =
      singular n / log N * pairMass true selected N Y n (Y ^ delta ε) -
      singular n / log N * pairRemoved true selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)) := by
    unfold modelPair
    rw [← hp]
    ring
  have ht' : modelTriple selected N Y n =
      singular n / log N * tripleMass true selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε) -
      singular n / log N * tripleRemoved true selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε) := by
    unfold modelTriple
    rw [← ht]
    ring
  have hA := neg_abs_le (pairMass false selected N Y n (Y ^ delta ε) -
    singular n / log N * pairMass true selected N Y n (Y ^ delta ε))
  have hB := le_abs_self (pairRemoved false selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)) -
    singular n / log N * pairRemoved true selected N Y n (Y ^ delta ε) (Y ^ (16 / 135 : ℝ)))
  have hC := le_abs_self (tripleMass false selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε) -
    singular n / log N * tripleMass true selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε))
  have hD := neg_abs_le (tripleRemoved false selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε) -
    singular n / log N * tripleRemoved true selected N Y n (Y ^ (16 / 135 : ℝ)) (Y ^ delta ε))
  unfold iwaniecError at hI
  unfold lemma19Error at h19
  nlinarith

/-- Pages 283 to 285: the union of two logarithmically exceptional families stays exceptional. -/
theorem exceptional_union (P Q : ℝ → ℝ → ℕ → Prop)
    (hP : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (P ε N)).card : ℝ) ≤ C * windowLength N ε / log N ^ B)
    (hQ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        (((window N ε).filter (Q ε N)).card : ℝ) ≤ C * windowLength N ε / log N ^ B) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
      ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
        ((@Finset.filter ℕ (fun n => P ε N n ∨ Q ε N n) (fun n => Classical.propDecidable _) (window N ε)).card : ℝ) ≤
          C * windowLength N ε / log N ^ B := by
  obtain ⟨eP, heP, hP⟩ := hP
  obtain ⟨eQ, heQ, hQ⟩ := hQ
  refine ⟨min eP eQ, lt_min heP heQ, ?_⟩
  intro ε B hε he hB
  obtain ⟨CP, NP, hCP⟩ := hP ε B hε (he.trans_le (min_le_left _ _)) hB
  obtain ⟨CQ, NQ, hCQ⟩ := hQ ε B hε (he.trans_le (min_le_right _ _)) hB
  refine ⟨CP + CQ, max NP NQ, ?_⟩
  intro N hN
  have hsub : @Finset.filter ℕ (fun n => P ε N n ∨ Q ε N n) (fun n => Classical.propDecidable _) (window N ε) ⊆
      (window N ε).filter (P ε N) ∪ (window N ε).filter (Q ε N) := by
    intro n hn
    obtain ⟨hn, hp | hq⟩ :=
      (@Finset.mem_filter ℕ (fun n => P ε N n ∨ Q ε N n)
        (fun n => Classical.propDecidable _) (window N ε) n).mp hn
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, hp⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, hq⟩)
  have hc : ((@Finset.filter ℕ (fun n => P ε N n ∨ Q ε N n) (fun n => Classical.propDecidable _) (window N ε)).card : ℝ) ≤
      (((window N ε).filter (P ε N)).card : ℝ) + (((window N ε).filter (Q ε N)).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have h := hc.trans (add_le_add
    (hCP N ((le_max_left _ _).trans hN)) (hCQ N ((le_max_right _ _).trans hN)))
  convert h using 1 <;> ring

#print axioms pointwise_from_transfers
#print axioms exceptional_union
#print axioms sourceSet_bounds
#print axioms sourceSet_A_count
#print axioms pair_cancellation
#print axioms triples_cancellation
#print axioms pair_domain_le_piece
#print axioms family_buchstab_lower
#print axioms delta_cutoff
end
end LeanLab.Languasco2004.Source565
