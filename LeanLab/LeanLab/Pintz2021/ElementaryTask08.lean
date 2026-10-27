import LeanLab.Pintz2021.Applications
import LeanLab.ChenExplicit.TwinCNumeric

/-!
Elementary pieces of P0054, author copy pages 9 and 14.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.ElementaryTask08

open Finset

attribute [local instance] Classical.propDecidable

/-- The sum in Lemma 2 is empty when m is at most q. -/
theorem lemma2_sum_eq_zero (m q K : ℕ) (hmq : m ≤ q) :
    ∑ ν ∈ (Icc 1 K).filter (fun ν => 2 ^ ν < m ∧ q ∣ m - 2 ^ ν),
      Sing (m - 2 ^ ν) = 0 := by
  have hempty : (Icc 1 K).filter (fun ν => 2 ^ ν < m ∧ q ∣ m - 2 ^ ν) = ∅ := by
    ext ν
    simp only [mem_filter, mem_Icc, notMem_empty, iff_false]
    rintro ⟨_, hp, hd⟩
    have hpos : 0 < m - 2 ^ ν := Nat.sub_pos_of_lt hp
    have hqle := Nat.le_of_dvd hpos hd
    have hp0 : 0 < 2 ^ ν := by positivity
    omega
  rw [hempty, sum_empty]

/-- Display 3.3 with its numeric singular-series input discharged. -/
theorem eq33_proved {X : ℝ} (hX : 0 < X) (ε : ℝ) (m : ℕ) (hm : X / 2 ≤ m) :
    X ^ (1 - ε) / 4 < m * Sing m / (2 * X ^ ε) := by
  apply Applications.eq33 ?_ hX ε m hm
  rw [Applications.C0_eq_twinC]
  have h := LeanLab.ChenExplicit.twinC_ge_065
  linarith

/-- Expand the singular series product into positive squarefree subset weights. -/
theorem Sing_eq_subset_sum (m : ℕ) :
    Sing m = 2 * C0 *
      ∑ s ∈ (m.primeFactors.filter fun p => 2 < p).powerset,
        ∏ p ∈ s, (1 / ((p : ℝ) - 2)) := by
  unfold Sing
  rw [prod_one_add]

/-- Distinct subsets of odd prime divisors have distinct products. -/
theorem subset_prod_injective (m : ℕ) :
    Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p)
      ((m.primeFactors.filter fun p => 2 < p).powerset : Set (Finset ℕ)) := by
  intro s hs t ht heq
  have hs' : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp ((mem_powerset.mp hs) hp)).1
  have ht' : ∀ p ∈ t, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp ((mem_powerset.mp ht) hp)).1
  calc s = (∏ p ∈ s, p).primeFactors := (Nat.primeFactors_prod hs').symm
    _ = (∏ p ∈ t, p).primeFactors := congrArg Nat.primeFactors heq
    _ = t := Nat.primeFactors_prod ht'

end LeanLab.Pintz2021.ElementaryTask08

#print axioms LeanLab.Pintz2021.ElementaryTask08.lemma2_sum_eq_zero
#print axioms LeanLab.Pintz2021.ElementaryTask08.eq33_proved

#print axioms LeanLab.Pintz2021.ElementaryTask08.Sing_eq_subset_sum

#print axioms LeanLab.Pintz2021.ElementaryTask08.subset_prod_injective
