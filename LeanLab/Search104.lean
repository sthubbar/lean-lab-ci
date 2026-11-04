import LeanLab.Ricci1937.DecompJ365

namespace LeanLab.Ricci1937

open Finset Filter Real Asymptotics
open LeanLab.PNTSieve.Mertens

noncomputable section
attribute [local instance] Classical.propDecidable

section PairSieve
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

/-- scratch: density product bridge -/
lemma test_density_product_lower (h : N) (S : Finset N) (z : N) (hz : 3 ≤ z)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ p ≤ z) :
    exp (-52 : R) / Real.log z ^ 2 ≤ ∏ p ∈ S, (1 - nuN h p) := by
  have hnu : ∀ p ∈ S, nuN h p ≤ (2 : R) / p := by
    intro p hp
    have hpprime := (hS p hp).1
    rw [nuN_prime hpprime]
    have hwt : wt h p ≤ 2 := wt_le_two h p
    have hp0 : (0 : R) < p := by exact_mod_cast hpprime.pos
    rw [div_le_div_of_nonneg_right hwt hp0.le]
  have hfacge : ∀ p ∈ S, 1 - (2 : R) / p ≤ 1 - nuN h p := by
    intro p hp
    have hpprime := (hS p hp).1
    have hp0 : (0 : R) < p := by exact_mod_cast hpprime.pos
    have hp3 : (3 : R) ≤ p := by exact_mod_cast (hS p hp).2.1
    have h23 : (2 : R) / p ≤ 2 / 3 := by
      apply div_le_div_of_nonneg_right
      · norm_num
      · exact hp0.le
      · linarith
    linarith [hnu p hp]
  have hprod : (∏ p ∈ S, (1 - (2 : R) / p)) ≤ ∏ p ∈ S, (1 - nuN h p) :=
    Finset.prod_le_prod (fun p hp => hfacge p hp)
  have hlow := decompJ365_prime_product_lower z hz S hS
  exact hlow.trans hprod

/-- scratch: survivors enter the W count -/
lemma test_sieve_survivors_le_wCount (a b N z : N) (hN : Even N) (hz : 3 ≤ z)
    (htA : (N : R) ^ (1 / ((a : R) + 1)) ≤ z)
    (htB : (N : R) ^ (1 / ((b : R) + 1)) ≤ z) :
    #{m ∈ range N | Odd m ∧ ∀ p ∈ (Icc 3 z).filter Nat.Prime, ¬ p | m * (N - m)} ≤
      wCount a b N := by
  unfold wCount
  apply card_le_card
  intro m hm
  rw [mem_filter] at hm
  obtain ⟨hmrange, hmOdd, hmsurv⟩ := hm
  have hmN : m < N := mem_range.mp hmrange
  have hmne0 : m ≠ 0 := by
    intro h0
    have h3 : (3 : N) ∈ (Icc 3 z).filter Nat.Prime :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, Nat.prime_three⟩
    exact hmsurv 3 h3 (by simp [h0])
  have hm1 : 1 ≤ m := by omega
  have hNm1 : 1 ≤ N - m := by omega
  have hNmN : N - m < N := by omega
  have hfirst : ∀ p ∈ m.primeFactorsList, (N : R) ^ (1 / ((a : R) + 1)) < (p : R) := by
    intro p hp
    obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList hmne0).mp hp
    have hpne2 : p ≠ 2 := by
      intro h2
      subst h2
      exact (Nat.not_even_iff_odd.mp hmOdd) (Nat.even_iff_two_dvd.mpr hpdvd)
    have hp3 : 3 ≤ p := by
      have hp2 := hpprime.two_le
      omega
    have hpz : z < p := by
      by_contra hle
      have hmem : p ∈ (Icc 3 z).filter Nat.Prime :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hp3, le_of_not_gt hle⟩, hpprime⟩
      exact hmsurv p hmem (dvd_mul_of_dvd_left hpdvd _)
    have hzR : (z : R) ≤ (p : R) := by exact_mod_cast (by omega)
    have htA' : (N : R) ^ (1 / ((a : R) + 1)) ≤ (p : R) := htA.trans hzR
    exact htA'
  have hsecond : ∀ p ∈ (N - m).primeFactorsList,
      (N : R) ^ (1 / ((b : R) + 1)) < (p : R) := by
    intro p hp
    obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList (by omega : N - m ≠ 0)).mp hp
    have hpne2 : p ≠ 2 := by
      intro h2
      subst h2
      have hmeven : Even m := by
        apply Nat.even_iff_two_dvd.mpr
        have : 2 ∣ N - m := hpdvd
        have : 2 ∣ N := (Nat.even_iff_two_dvd.mp hN)
        omega
      exact (Nat.not_even_iff_odd.mp hmOdd) hmeven
    have hp3 : 3 ≤ p := by
      have hp2 := hpprime.two_le
      omega
    have hpz : z < p := by
      by_contra hle
      have hmem : p ∈ (Icc 3 z).filter Nat.Prime :=
        mem_filter.mpr ⟨mem_Icc.mpr ⟨hp3, le_of_not_gt hle⟩, hpprime⟩
      exact hmsurv p hmem (dvd_mul_of_dvd_right hpdvd _)
    have hzR : (z : R) ≤ (p : R) := by exact_mod_cast (by omega)
    have htB' : (N : R) ^ (1 / ((b : R) + 1)) ≤ (p : R) := htB.trans hzR
    exact htB'
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, by omega⟩, ?_, ?_⟩
  · exact decompJ365_almostGT_of_lt hm1 hmN hfirst
  · exact decompJ365_almostGT_of_lt hNm1 hNmN hsecond

end PairSieve
end LeanLab.Ricci1937
