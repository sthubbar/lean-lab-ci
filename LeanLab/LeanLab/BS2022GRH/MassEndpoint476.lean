/- AI wrote the Lean code for CODEX task476. Goldbach is open.
Keep the lower prime endpoint in the actual finite count of journal p. 1237.
This is a sharper finite bound, not a closure of main_at_threshold.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.SliceMass236
import LeanLab.BS2022GRH.Instances339

namespace LeanLab.BS2022GRH.MassEndpoint476
open Real Finset Classical ChenThresholdGRH DecompC164c SliceMass236
noncomputable section

/-- The p3 fiber plus all primes below p2 fits inside the upper prime count.
Derived from journal p. 1237 display 30, retaining the discarded lower endpoint. -/
theorem triple_fiber_add_lower_le_pi (n : ℕ) (ε₁ : ℝ) (q : ℕ × ℕ)
    (hq : q ∈ pairRange n ε₁) :
    (((relaxedTriples n ε₁).filter (fun t => t.1 = q)).card : ℝ) +
      PaperInputs148.primeCount (q.2 - 1 : ℕ) ≤
        PaperInputs148.primeCount ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) := by
  obtain ⟨_, hp1, hp2, _, _, _, hprod⟩ := mem_filter.mp hq
  have hp1R : (0 : ℝ) < q.1 := by exact_mod_cast hp1.pos
  have hp2R : (0 : ℝ) < q.2 := by exact_mod_cast hp2.pos
  have hq0 : (0 : ℝ) < (q.1 : ℝ) * q.2 := mul_pos hp1R hp2R
  let x : ℝ := (1 + ε₁) * n / ((q.1 : ℝ) * q.2)
  have hqx : (q.2 : ℝ) < x := by
    dsimp [x]
    rw [lt_div_iff₀ hq0]
    nlinarith only [hprod]
  let T := (relaxedTriples n ε₁).filter (fun t => t.1 = q)
  let L := (range q.2).filter Nat.Prime
  let U := (range (⌊x⌋₊ + 1)).filter Nat.Prime
  have hinj : Set.InjOn (fun t : (ℕ × ℕ) × ℕ => t.2) T := by
    intro t ht u hu heq
    exact Prod.ext ((mem_filter.mp ht).2.trans (mem_filter.mp hu).2.symm) heq
  have hsub : T.image (fun t => t.2) ∪ L ⊆ U := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      obtain ⟨htt, htq⟩ := mem_filter.mp ht
      obtain ⟨_, _, _, hp3, _, _, _, _, htp⟩ := mem_filter.mp htt
      have hlt : (t.2 : ℝ) < x := by
        dsimp [x]
        rw [lt_div_iff₀ hq0]
        rw [htq] at htp
        nlinarith only [htp]
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hlt.le)), hp3⟩
    · obtain ⟨hpr, hpp⟩ := mem_filter.mp hp
      have hpq : (p : ℝ) < q.2 := by exact_mod_cast mem_range.mp hpr
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hpq.trans hqx).le)), hpp⟩
  have hdis : Disjoint (T.image (fun t => t.2)) L := by
    apply disjoint_left.mpr
    intro p hp hL
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
    obtain ⟨htt, htq⟩ := mem_filter.mp ht
    have horder := (mem_filter.mp htt).2.2.2.2.2.2.2.1
    have htlo : q.2 ≤ t.2 := by simpa only [htq] using horder
    have hthi : t.2 < q.2 := mem_range.mp (mem_filter.mp hL).1
    omega
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, card_image_of_injOn hinj] at hc
  have hL : (L.card : ℝ) = PaperInputs148.primeCount (q.2 - 1 : ℕ) := by
    unfold PaperInputs148.primeCount
    rw [Nat.floor_natCast]
    have hqpos := hp2.pos
    have heq : q.2 - 1 + 1 = q.2 := by omega
    rw [heq]
  change (T.card : ℝ) + PaperInputs148.primeCount (q.2 - 1 : ℕ) ≤ (U.card : ℝ)
  rw [← hL]
  exact_mod_cast hc

/-- Sum the retained lower endpoint over all admissible pairs.
This sharpens the finite prime count reduction in journal p. 1237 display 30. -/
theorem mass_le_pi_difference (n : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    mass n ε₁ ≤ ∑ q ∈ pairRange n ε₁,
      (PaperInputs148.primeCount ((1 + ε₁) * n / ((q.1 : ℝ) * q.2)) -
        PaperInputs148.primeCount (q.2 - 1 : ℕ)) := by
  have hc := card_eq_sum_card_fiberwise
    (s := relaxedTriples n ε₁) (t := pairRange n ε₁) (f := fun t => t.1)
    (fun t ht => pair_mem_of_triple ht)
  calc
    mass n ε₁ ≤ ((relaxedTriples n ε₁).card : ℝ) := mass_le_relaxed n ε₁ hn hε
    _ = ∑ q ∈ pairRange n ε₁,
        (((relaxedTriples n ε₁).filter (fun t => t.1 = q)).card : ℝ) := by exact_mod_cast hc
    _ ≤ _ := by
      apply sum_le_sum
      intro q hq
      linarith only [triple_fiber_add_lower_le_pi n ε₁ q hq]

/-- The retained correction is positive on a genuine finite slice domain.
This is a concrete instance of the derived bound on journal p. 1237. -/
theorem positive_correction_instance :
    mass 256 (3 / 4) + 3 ≤ ∑ q ∈ pairRange 256 (3 / 4),
      PaperInputs148.primeCount ((1 + (3 / 4 : ℝ)) * 256 / ((q.1 : ℝ) * q.2)) := by
  have hy := Instances339.small_y
  have hq : (3, 7) ∈ pairRange 256 (3 / 4) := by
    norm_num [pairRange, Instances339.small_z, hy.1, hy.2]
  have hp : PaperInputs148.primeCount ((7 : ℕ) - 1 : ℕ) = 3 := by
    norm_num [PaperInputs148.primeCount]
    exact_mod_cast (show ((range 7).filter Nat.Prime).card = 3 by decide)
  have hs := single_le_sum (s := pairRange 256 (3 / 4))
    (f := fun q => PaperInputs148.primeCount (q.2 - 1 : ℕ))
    (fun q _ => by unfold PaperInputs148.primeCount; positivity) hq
  change PaperInputs148.primeCount ((7 : ℕ) - 1 : ℕ) ≤ _ at hs
  rw [hp] at hs
  have hm := mass_le_pi_difference 256 (3 / 4) (by norm_num) (by norm_num)
  rw [sum_sub_distrib] at hm
  linarith only [hm, hs]

end
end LeanLab.BS2022GRH.MassEndpoint476
#print axioms LeanLab.BS2022GRH.MassEndpoint476.triple_fiber_add_lower_le_pi

#print axioms LeanLab.BS2022GRH.MassEndpoint476.mass_le_pi_difference

#print axioms LeanLab.BS2022GRH.MassEndpoint476.positive_correction_instance
