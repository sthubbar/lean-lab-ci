/-
Kumchev and Liu 2007, P0088. ROUTE BURST S98 burst-20261122 deepen of
`leaf_moebius_rough` of SPLIT_lemma34_second_sum_dyadic_b.lean: proved outright,
from Mathlib's Moebius inversion `moebius_mul_coe_zeta`, by passing to the
squarefree kernel g of the z smooth part of k.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_second_sum_dyadic_b

namespace LeanLab.KumchevLiu2007.Eq33RouteD.SplitB

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 11, the first display of the proof of Lemma 3.4, proved. -/
theorem leaf_moebius_rough_split (z : ℝ) (k : ℕ) (hk : 0 < k) :
    roughWeight z k = ∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
      (r : ℝ) < z), ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  set S := k.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) with hS
  set g := ∏ p ∈ S, p with hgdef
  have hSp : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hSp p hp).ne_zero
  have hgk : g ∣ k := dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _))
    (Nat.prod_primeFactors_dvd k)
  have hpf : g.primeFactors = S := Nat.primeFactors_prod hSp
  have hk0 : k ≠ 0 := hk.ne'
  have step1 : (∑ d ∈ k.divisors.filter (fun d : ℕ => ∀ r : ℕ, r.Prime → r ∣ d →
      (r : ℝ) < z), ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      ∑ d ∈ g.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
    symm
    apply Finset.sum_subset
    · intro d hd
      have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdg.trans hgk, hk0⟩, ?_⟩
      intro r hr hrd
      have : r ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrd.trans hdg, hg0⟩
      rw [hpf] at this
      exact (Finset.mem_filter.mp this).2
    · intro d hd hdn
      obtain ⟨hdk, hsm⟩ := Finset.mem_filter.mp hd
      have hdk' := Nat.dvd_of_mem_divisors hdk
      have hd0 : d ≠ 0 := fun h => hk0 (by rw [h] at hdk'; exact Nat.eq_zero_of_zero_dvd hdk')
      by_contra hmu
      have hmu' : ArithmeticFunction.moebius d ≠ 0 := by
        intro h; apply hmu; simp [h]
      have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu'
      apply hdn
      refine Nat.mem_divisors.mpr ⟨?_, hg0⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hdk', hk0⟩,
        hsm p hpp hpd⟩
  have step2 : (∑ d ∈ g.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
      ((if g = 1 then 1 else 0 : ℤ) : ℂ) := by
    rw [← Int.cast_sum]
    congr 1
    have h := congrArg (fun F : ArithmeticFunction ℤ => F g)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    exact h
  have step3 : (∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)) ↔ g = 1 := by
    constructor
    · intro h
      have : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpp, hpk, -⟩ := Nat.mem_primeFactors.mp hp1
        exact absurd (h p hpp hpk) (not_le.mpr hp2)
      rw [hgdef, this, Finset.prod_empty]
    · intro h p hpp hpk
      by_contra hlt
      have hmem : p ∈ S := Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpk, hk0⟩, not_le.mp hlt⟩
      rw [← hpf, h] at hmem
      simp at hmem
  rw [step1, step2]
  unfold roughWeight
  by_cases hc : ∀ p : ℕ, p.Prime → p ∣ k → z ≤ (p : ℝ)
  · rw [if_pos hc, if_pos (step3.mp hc)]; simp
  · rw [if_neg hc, if_neg (fun h => hc (step3.mpr h))]; simp

/-- The split statement is the leaf statement. -/
example : type_of% @leaf_moebius_rough := leaf_moebius_rough_split

end LeanLab.KumchevLiu2007.Eq33RouteD.SplitB
