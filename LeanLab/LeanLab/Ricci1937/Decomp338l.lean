import LeanLab.Ricci1937.Decomp338c

/-!
Ricci 1937, mixed pair density preparation.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary density encoding for the mixed sieve on first memoir page 88.
Multiplying the gap by the high prime product makes every high local density one over p.
This is an encoding of densities, not a replacement of the actual shifted pair. -/
def decomp338EncodedGap (h v t : ℕ) : ℕ := h * ∏ p ∈ (Ioc v t).filter Nat.Prime, p

/-- Auxiliary evenness of the mixed density encoding, first memoir page 88. -/
lemma decomp338_encoded_gap_even (h v t : ℕ) (heven : Even h) :
    Even (decomp338EncodedGap h v t) := by
  obtain ⟨k, hk⟩ := heven
  refine ⟨k * (∏ p ∈ (Ioc v t).filter Nat.Prime, p), ?_⟩
  unfold decomp338EncodedGap
  rw [hk]
  ring

/-- Auxiliary low prime densities for the mixed sieve on first memoir page 88.
The high prime product is coprime to every low prime, so its pair density is unchanged. -/
lemma decomp338_encoded_gap_low (h v t p : ℕ) (hp : p.Prime) (hpv : p ≤ v) :
    nuN (decomp338EncodedGap h v t) p = nuN h p := by
  have hcop : Nat.Coprime p (∏ q ∈ (Ioc v t).filter Nat.Prime, q) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    obtain ⟨hqI, hqprime⟩ := mem_filter.mp hq
    apply hp.coprime_iff_not_dvd.mpr
    intro hpd
    have heq := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpd
    have hqv := (mem_Ioc.mp hqI).1
    omega
  have hnot := hp.coprime_iff_not_dvd.mp hcop
  have hdiv : p ∣ decomp338EncodedGap h v t ↔ p ∣ h := by
    simp only [decomp338EncodedGap, hp.dvd_mul, hnot, or_false]
  simp only [nuN_prime hp, wt, hdiv]

/-- Auxiliary high prime densities for the mixed sieve on first memoir page 88.
Every encoded high prime has the one root density one over p. -/
lemma decomp338_encoded_gap_high (h v t p : ℕ) (hp : p.Prime) (hpv : v < p) (hpt : p ≤ t) :
    nuN (decomp338EncodedGap h v t) p = 1 / (p : ℝ) := by
  have hpB : p ∈ (Ioc v t).filter Nat.Prime := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpv, hpt⟩, hp⟩
  have hprod : p ∣ ∏ q ∈ (Ioc v t).filter Nat.Prime, q := dvd_prod_of_mem id hpB
  have hd : p ∣ decomp338EncodedGap h v t := dvd_mul_of_dvd_right hprod h
  simp only [nuN_prime hp, wt, if_pos hd, Nat.cast_one]

/-- Auxiliary lower numerical bound for the route comparison on first memoir page 89.
The unshifted dimension two profile has tau strictly greater than two and one half. -/
lemma decomp338_tau_two_gt : (2.5 : ℝ) < ricciTau 2 := by
  have h045 : exp (0.45 : ℝ) ≤ 1.6 := ricci_exp_upper_small
    (by norm_num) (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have h073 : exp (0.73 : ℝ) ≤ 2.1 := ricci_exp_upper_small
    (by norm_num) (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have h099 : exp (0.99 : ℝ) ≤ 2.719 := by
    have hh := exp_le_exp.mpr (by norm_num : (0.99 : ℝ) ≤ 1)
    linarith [exp_one_lt_d9]
  have hn045 : (1 / 1.6 : ℝ) ≤ exp (-0.45 : ℝ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (exp_pos _) h045
  have hn073 : (1 / 2.1 : ℝ) ≤ exp (-0.73 : ℝ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (exp_pos _) h073
  have hn099 : (1 / 2.719 : ℝ) ≤ exp (-0.99 : ℝ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (exp_pos _) h099
  have hq : (0.75 : ℝ) ≤ exp (-0.25 : ℝ) := by linarith [add_one_le_exp (-0.25 : ℝ)]
  have hden : 0 < 1 - exp (-0.25 : ℝ) := sub_pos.mpr (exp_lt_one_iff.mpr (by norm_num))
  have htail : (1 / 2.719 : ℝ) / 0.25 ≤ exp (-0.99 : ℝ) / (1 - exp (-0.25 : ℝ)) :=
    div_le_div₀ (by positivity) hn099 hden (by linarith)
  norm_num [ricciTau] at *
  linarith

/-- Auxiliary negative route certificate for first memoir page 89.
A cutoff exponent above one sixth cannot retain a saved power with the unshifted support profile.
This does not refute the mixed pair count. -/
lemma decomp338_unshifted_profile_not_case_two (δ : ℝ) (hδ : 1 / 6 < δ) :
    1 < δ * (1 + 2 * ricciTau 2) := by
  have ht := decomp338_tau_two_gt
  have hm := mul_pos (show 0 < δ by linarith) (sub_pos.mpr ht)
  nlinarith

/-- Auxiliary warning against replacing the actual gap by its density encoding.
At x three, the gap ten pair survives prime five but the gap two pair does not. -/
lemma decomp338_encoded_pair_nontransfer :
    ¬ (∀ x : ℕ, Nat.Coprime 5 (x * (x + 10)) → Nat.Coprime 5 (x * (x + 2))) := by
  intro h
  have hh := h 3 (by norm_num)
  norm_num at hh

end
end LeanLab.Ricci1937
