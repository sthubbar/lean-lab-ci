/-
P0069, page 27, identity after equation 4.15.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Buchstab

namespace LeanLab.BakerHarmanPintz1997
open Finset ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- Partition all nonempty prime subsets by their greatest prime. -/
theorem sum_powerset_by_max (P : Finset ℕ) (f : Finset ℕ → ℂ) :
    ∑ T ∈ P.powerset, f T = f ∅ +
      ∑ p ∈ P, ∑ T ∈ (P.filter (fun q => q < p)).powerset, f (insert p T) := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert p P hp ih =>
    have hpnot : p ∉ P := by intro h; exact (hp p h).false
    have hfilterp : (insert p P).filter (fun q => q < p) = P := by
      ext q
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨h | h, hlt⟩
        · subst q; omega
        · exact h
      · intro hq
        exact ⟨Or.inr hq, hp q hq⟩
    have hfilterq : ∀ q ∈ P, (insert p P).filter (fun r => r < q) = P.filter (fun r => r < q) := by
      intro q hq
      ext r
      simp only [mem_filter, mem_insert]
      have hqp := hp q hq
      constructor
      · rintro ⟨hr | hr, hrq⟩
        · subst r; omega
        · exact ⟨hr, hrq⟩
      · rintro ⟨hr, hrq⟩
        exact ⟨Or.inr hr, hrq⟩
    rw [sum_powerset_insert hpnot, ih, sum_insert hpnot, hfilterp]
    have heq : (∑ q ∈ P, ∑ T ∈ ((insert p P).filter (fun r => r < q)).powerset,
        f (insert q T)) = ∑ q ∈ P, ∑ T ∈ (P.filter (fun r => r < q)).powerset,
        f (insert q T) := by
      apply sum_congr rfl
      intro q hq
      rw [hfilterq q hq]
    rw [heq]
    abel

/-- The Moebius function of a product of distinct primes is minus one to their count. -/
theorem moebius_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    moebius (∏ p ∈ P, p) = (-1 : ℤ) ^ P.card := by
  rw [isMultiplicative_moebius.map_prod_of_prime P hP]
  calc ∏ p ∈ P, moebius p = ∏ _p ∈ P, (-1 : ℤ) := by
        apply prod_congr rfl
        intro p hp
        exact moebius_apply_prime (hP p hp)
    _ = _ := by simp

/-- The weighted inclusion exclusion identity after equation 4.15, in prime subset form. -/
theorem weighted_inclusion_exclusion (P : Finset ℕ) (g : ℕ → ℂ) :
    (∑ T ∈ P.powerset, (-1 : ℂ) ^ T.card * g (∏ q ∈ T, q)) = g 1 -
      ∑ p ∈ P, ∑ T ∈ (P.filter (fun q => q < p)).powerset,
        (-1 : ℂ) ^ T.card * g (p * ∏ q ∈ T, q) := by
  rw [sum_powerset_by_max]
  simp only [card_empty, pow_zero, prod_empty, one_mul]
  have heq : (∑ p ∈ P, ∑ T ∈ (P.filter (fun q => q < p)).powerset,
      (-1 : ℂ) ^ (insert p T).card * g (∏ q ∈ insert p T, q)) =
      -(∑ p ∈ P, ∑ T ∈ (P.filter (fun q => q < p)).powerset,
        (-1 : ℂ) ^ T.card * g (p * ∏ q ∈ T, q)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro T hT
    have hpnot : p ∉ T := by
      intro h
      have := (mem_filter.mp ((mem_powerset.mp hT) h)).2
      omega
    rw [card_insert_of_notMem hpnot, prod_insert hpnot, pow_succ]
    ring
  rw [heq]
  ring

/-- Reindex divisors of a squarefree prime product by its prime subsets. -/
theorem sum_divisors_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, f d) = ∑ T ∈ P.powerset, f (∏ p ∈ T, p) := by
  have hsq : Squarefree (∏ p ∈ P, p) := moebius_ne_zero_iff_squarefree.mp (by
    rw [moebius_prime_product P hP]
    exact pow_ne_zero _ (by norm_num))
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsq,
    Nat.sum_divisors_filter_squarefree hsq.ne_zero, Nat.factors_eq]
  rw [List.toFinset_coe, Nat.toFinset_factors, Nat.primeFactors_prod hP]
  simp only [Finset.prod_val, id]

/-- The exact divisor form of the weighted identity below equation 4.15 on page 27. -/
theorem weighted_moebius_identity (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (g : ℕ → ℂ) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, (moebius d : ℂ) * g d) = g 1 -
      ∑ p ∈ P, ∑ d ∈ (∏ q ∈ P.filter (fun q => q < p), q).divisors,
        (moebius d : ℂ) * g (p * d) := by
  rw [sum_divisors_prime_product P hP]
  have hleft : (∑ T ∈ P.powerset, (moebius (∏ q ∈ T, q) : ℂ) * g (∏ q ∈ T, q)) =
      ∑ T ∈ P.powerset, (-1 : ℂ) ^ T.card * g (∏ q ∈ T, q) := by
    apply sum_congr rfl
    intro T hT
    rw [moebius_prime_product T (fun q hq => hP q ((mem_powerset.mp hT) hq))]
    push_cast
    rfl
  rw [hleft, weighted_inclusion_exclusion]
  congr 1
  apply sum_congr rfl
  intro p hp
  rw [sum_divisors_prime_product _ (fun q hq => hP q (mem_filter.mp hq).1)]
  apply sum_congr rfl
  intro T hT
  rw [moebius_prime_product T
    (fun q hq => hP q (mem_filter.mp ((mem_powerset.mp hT) hq)).1)]
  push_cast
  rfl

#print axioms sum_powerset_by_max
#print axioms moebius_prime_product
#print axioms weighted_inclusion_exclusion
#print axioms sum_divisors_prime_product
#print axioms weighted_moebius_identity
end LeanLab.BakerHarmanPintz1997
