/-
Jia 1996 pages 282 to 285, nonvacuity of the supplied region families.
Source https://doi.org/10.4064/aa-77-3-207-287.
These are finite definition instances outside the eventual analytic regime.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Source565
import LeanLab.Languasco2004.LogApprox565
import LeanLab.Languasco2004.Integral565

namespace LeanLab.Languasco2004.Instances565
open Finset Real Decomp279a Decomp316a Decomp316c Geometry316 GroupSplit548 Source565
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Page 282 display 57: actual primes three and two lie in the truncated region one domain. -/
theorem region1_pair_instance : (3, 2) ∈ pairDomain true 320 9 := by
  have hlow : (320 : ℝ) ^ (16 / 135 : ℝ) < 2 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 135)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 320)]
    norm_num
  have htrunc : (3 : ℝ) ≤ (320 : ℝ) ^ (89 / 462 - 0.00000001 : ℝ) := by
    have hsafe : (3 : ℝ) ≤ (320 : ℝ) ^ (19 / 99 : ℝ) := by
      apply (Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 3) (by positivity)
        (by norm_num : (0 : ℝ) < 99)).mp
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 320)]
      norm_num
    exact hsafe.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  have hi : regionIndex 320 3 2 = 1 := by
    apply regionIndex_eq_of_mem (⟨0, by decide⟩ : Fin 69) (Y := 320) (p := 3) (q := 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [regionData]
    refine ⟨by linarith only [hlow], ?_, hlow⟩
    exact htrunc.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  apply mem_filter.mpr
  refine ⟨?_, by decide, by linarith only [hlow], ?_, by decide, hlow, ?_, ?_, ?_, ?_⟩
  · rw [Finset.product_eq_sprod]
    norm_num
  · apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  · apply lt_min (by norm_num)
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  · norm_num [hi, groupOf]
  · simp [hi]
  · intro _
    exact htrunc

/-- Page 285 remaining family: actual primes five and three lie in region two. -/
theorem remainder_pair_instance : (5, 3) ∈ pairDomain false 2000 18 := by
  have hlow : (2000 : ℝ) ^ (16 / 135 : ℝ) < 3 := by
    apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : (0 : ℝ) < 135)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2000)]
    norm_num
  have hi : regionIndex 2000 5 3 = 2 := by
    apply regionIndex_eq_of_mem (⟨1, by decide⟩ : Fin 69) (Y := 2000) (p := 5) (q := 3)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [regionData]
    refine ⟨?_, ?_, hlow, ?_⟩
    · apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num : (0 : ℝ) ≤ 5)
        (by norm_num : (0 : ℝ) < 462)).mp
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2000)]
      norm_num
      all_goals norm_num [pow_succ]
    · apply (Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 5) (by positivity)
        (by norm_num : (0 : ℝ) < 180)).mp
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2000)]
      norm_num
    · apply (Real.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) ≤ 3) (by positivity)
        (by norm_num : (0 : ℝ) < 288)).mp
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2000)]
      norm_num
      all_goals norm_num [pow_succ]
  apply mem_filter.mpr
  refine ⟨?_, by decide, by linarith only [hlow], ?_, by decide, hlow, ?_, ?_, ?_, ?_⟩
  · rw [Finset.product_eq_sprod]
    norm_num
  · apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  · apply lt_min (by norm_num)
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  · norm_num [hi, groupOf]
  · simp [hi]
  · simp

/-- Displays 57 and 64: the A count for the actual region one pair is nonzero. -/
theorem region1_sifted_instance : 1 ≤ sifted 3 320 9 6 2 := by
  apply Nat.succ_le_of_lt
  apply card_pos.mpr
  refine ⟨6, mem_filter.mpr ⟨by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩⟩
  intro p hp hp2
  have hpL := hp.two_le
  have hpU : p < 2 := by exact_mod_cast hp2
  omega

/-- Page 285 remaining family: the A count for the actual region two pair is nonzero. -/
theorem remainder_sifted_instance : 1 ≤ sifted 3 2000 18 15 3 := by
  apply Nat.succ_le_of_lt
  apply card_pos.mpr
  refine ⟨15, mem_filter.mpr ⟨by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_⟩⟩
  intro p hp hp3 hpn hpd
  have hpL := hp.two_le
  have hpU : p < 3 := by exact_mod_cast hp3
  have hp2 : p = 2 := by omega
  subst p
  norm_num at hpd

/-- Pages 283 to 285: a positive source interval satisfies the log approximation domain. -/
theorem enclosure_domain_instance :
    (1 / 10 : ℝ) ≤ 3 / 20 ∧ 3 / 5 * (1 / 5 : ℝ) ≤ 3 / 20 ∧
      (3 / 20 : ℝ) ≤ 1 / 5 ∧ 0 < (1 / 5 : ℝ) ∧
      ∀ t ∈ Set.Icc (3 / 20 : ℝ) (1 / 5), 1 ≤ (3 / 2 : ℝ) + 0 * t ∧
        (3 / 2 : ℝ) + 0 * t ≤ 2 := by
  norm_num

/-- Page 208: the small positive epsilon used by the source cutoff lemma exists. -/
theorem epsilon_domain_instance :
    (0 : ℝ) < 0.000001 ∧ (0.000001 : ℝ) ≤ (16 / 135 : ℝ)^3 ∧
      delta 0.000001 ≤ 16 / 135 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  exact delta_cutoff _ (by norm_num) (by norm_num)

/-- Display 57: one selected source pair supplies a lower bound on the full selected piece. -/
theorem selected_pair_le_piece (selected : Bool) (N Y : ℝ) (n p q : ℕ)
    (hpair : (p, q) ∈ pairDomain selected Y n) :
    (sifted N Y n (p * q) q : ℝ) ≤ pieceSum 5 1 selected N Y n := by
  have h := single_le_sum (s := pairDomain selected Y n)
    (f := fun pq : ℕ × ℕ => (sifted N Y n (pq.1 * pq.2) pq.2 : ℝ))
    (fun pq _ => by positivity) hpair
  exact h.trans (pair_domain_le_piece selected N Y n)

/-- Displays 57 and 64: both supplied region families have genuine positive prime contributions. -/
theorem positive_piece_instances :
    0 < pieceSum 5 1 true 3 320 9 ∧ 0 < pieceSum 5 1 false 3 2000 18 := by
  have h1 := selected_pair_le_piece true 3 320 9 3 2 region1_pair_instance
  have h2 := selected_pair_le_piece false 3 2000 18 5 3 remainder_pair_instance
  have hp1 : (0 : ℝ) < sifted 3 320 9 6 2 := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) region1_sifted_instance
  have hp2 : (0 : ℝ) < sifted 3 2000 18 15 3 := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) remainder_sifted_instance
  exact ⟨hp1.trans_le h1, hp2.trans_le h2⟩

#print axioms selected_pair_le_piece
#print axioms positive_piece_instances
#print axioms region1_pair_instance
#print axioms remainder_pair_instance
#print axioms region1_sifted_instance
#print axioms remainder_sifted_instance
#print axioms enclosure_domain_instance
#print axioms epsilon_domain_instance
end
end LeanLab.Languasco2004.Instances565
