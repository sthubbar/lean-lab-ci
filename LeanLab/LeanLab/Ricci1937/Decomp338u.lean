import LeanLab.Ricci1937.Decomp338t

/-!
Ricci 1937, exact mixed block mass and first endpoint estimates.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary low block identity for the mixed density on first memoir page 88.
The encoded density agrees with the original pair density below v. -/
lemma decomp338_mixed_low_block (h y w v t : ℕ) (hwv : w ≤ v) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) =
      ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
  exact decomp338_encoded_gap_low h v t p hpprime ((mem_Ioc.mp hpI).2.trans hwv)

/-- Auxiliary high block identity for the mixed density on first memoir page 88.
Every density in the high part is one over its prime. -/
lemma decomp338_mixed_high_block (h y w v t : ℕ) (hvy : v ≤ y) (hwt : w ≤ t) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) =
      ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
  obtain ⟨hyp, hpw⟩ := mem_Ioc.mp hpI
  exact decomp338_encoded_gap_high h v t p hpprime (hvy.trans_lt hyp) (hpw.trans hwt)

/-- Auxiliary exact mixed mass split for first memoir page 88 and second memoir page 115.
The low contribution has the original pair density and the high contribution has one root. -/
lemma decomp338_mixed_mass_split (h y v w t : ℕ) (hyv : y ≤ v) (hvw : v ≤ w) (hwt : w ≤ t) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) =
      (∑ p ∈ (Ioc y v).filter Nat.Prime, nuN h p) +
        ∑ p ∈ (Ioc v w).filter Nat.Prime, (1 : ℝ) / p := by
  have hs := sum_Ioc_consecutive
    (fun p => if p.Prime then nuN (decomp338EncodedGap h v t) p else 0) hyv hvw
  rw [← sum_filter, ← sum_filter, ← sum_filter] at hs
  rw [← hs, decomp338_mixed_low_block h y v v t le_rfl,
    decomp338_mixed_high_block h v w v t le_rfl hwt]

/-- Auxiliary mixed mass upper bound for first memoir page 88 and second memoir page 115.
Below the transition v the logarithmic coefficient is two and above it the coefficient is one. -/
lemma decomp338_mixed_mass_upper (h y v w t : ℕ) (hy : 2 ≤ y)
    (hyv : y ≤ v) (hvw : v ≤ w) (hwt : w ≤ t) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) ≤
      2 * Real.log (Real.log v / Real.log y) + Real.log (Real.log w / Real.log v) +
        28 / Real.log y + 14 / Real.log v := by
  rw [decomp338_mixed_mass_split h y v w t hyv hvw hwt]
  have hlo := decompJ365_pair_block_mass_upper h y v hy hyv
  have hhi := decompJ365_prime_block_upper v w (hy.trans hyv) hvw
  linarith

/-- Auxiliary endpoint location for the mixed sieve on second memoir page 115.
If the entire high prime mass fits the first printed target, the first greedy cutoff is at most v. -/
lemma decomp338_mixed_first_cutoff_le (h Y v t : ℕ) (hYv : Y ≤ v) (hvt : v ≤ t)
    (hmass : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.90) :
    decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 0 ≤ v := by
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ t ∧
      (∑ p ∈ (Ioc y t).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) ≤
        (decomp305HeadMass 0 : ℝ) / 100 := by
    refine ⟨v, hYv, hvt, ?_⟩
    rw [decomp338_mixed_high_block h v t v t le_rfl le_rfl]
    norm_num [decomp305HeadMass] at *
    exact hmass
  change decomp338GreedyStep (decomp338EncodedGap h v t) Y t 0 ≤ v
  unfold decomp338GreedyStep
  rw [dif_pos hex]
  apply Nat.find_min' hex
  refine ⟨hYv, hvt, ?_⟩
  rw [decomp338_mixed_high_block h v t v t le_rfl le_rfl]
  norm_num [decomp305HeadMass] at *
  exact hmass

end
end LeanLab.Ricci1937
