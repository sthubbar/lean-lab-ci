/- AI-written Lean code by OpenAI Codex, task113, 2026-10-26. Binary Goldbach is open. -/
import LeanLab.Tchudakov1938.Lemma4Abs113
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LeanLab.Tchudakov1938.Euler113
open LeanLab.Tchudakov1938.Decomp113 LeanLab.Tchudakov1938.PrimeValues113 LeanLab.Tchudakov1938.Lemma4Abs113
/-- P0064, page 27, A_m extended by zero at modulus zero for the Mathlib Euler product interface. -/
noncomputable def coefficientNat (m q : ℕ) : ℂ :=
  if h : q = 0 then 0 else coefficient m ⟨q, Nat.pos_of_ne_zero h⟩

/-- LEAF. P0064, pages 27 and 29, the term at modulus one equals one. -/
theorem coefficientNat_one (m : ℕ) : coefficientNat m 1 = 1 := by simp [coefficientNat, coefficient_one]
/-- LEAF. P0064, page 28, Lemma 3 for the zero extension. -/
theorem coefficientNat_mul (m : ℕ) {a b : ℕ} (h : a.Coprime b) :
    coefficientNat m (a * b) = coefficientNat m a * coefficientNat m b := by
  by_cases ha : a = 0
  · subst a; simp [coefficientNat]
  by_cases hb : b = 0
  · subst b; simp [coefficientNat]
  simp only [coefficientNat, dite_eq_right ha, dite_eq_right hb, dite_eq_right (Nat.mul_ne_zero ha hb)]
  exact lemma3 m ⟨a, Nat.pos_of_ne_zero ha⟩ ⟨b, Nat.pos_of_ne_zero hb⟩ h

/-- LEAF. P0064, page 29, inequality 2 with the zero term adjoined. -/
theorem summable_norm_coefficientNat (m : ℕ) (hm : 0 < m) : Summable (fun q : ℕ => ‖coefficientNat m q‖) := by
  have H := Equiv.pnatEquivNat.symm.summable_iff.mpr (summable_norm_coefficient m hm)
  apply (summable_nat_add_iff 1).mp
  simpa [Function.comp_def, coefficientNat, Nat.succPNat] using H

/-- LEAF. P0064, page 29, Euler factors. Only exponents zero and one contribute. -/
theorem tsum_prime_powers (m : ℕ) (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, coefficientNat m (p ^ k)) = 1 + coefficientNat m p := by
  have hz (k : ℕ) (hk : 2 ≤ k) : coefficientNat m (p ^ k) = 0 := by
    have hne : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
    have hsq : ¬ Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega : k ≠ 0)]
      simp [show k ≠ 1 by omega]
    simp only [coefficientNat, dite_eq_right hne]
    exact coefficient_not_squarefree m ⟨p ^ k, Nat.pos_of_ne_zero hne⟩ hsq
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coefficientNat_one]
  · intro k hk
    apply hz
    simp only [Finset.mem_range, not_lt] at hk
    exact hk

/-- LEAF. P0064, page 29, the first Euler product equality, as a convergent product. -/
theorem hasProd_local (m : ℕ) (hm : 0 < m) :
    HasProd (fun p : Nat.Primes => 1 + coefficientNat m p) (∑' q : ℕ, coefficientNat m q) := by
  have H := EulerProduct.eulerProduct_hasProd (coefficientNat_one m)
    (coefficientNat_mul m) (summable_norm_coefficientNat m hm) (by simp [coefficientNat])
  convert H using 1
  funext p
  exact (tsum_prime_powers m p p.property).symm


/-- LEAF. P0064, page 29, adjoining the zero term preserves the sum. -/
theorem tsum_positive_eq_nat (m : ℕ) (hm : 0 < m) :
    (∑' q : ℕ+, coefficient m q) = ∑' q : ℕ, coefficientNat m q := by
  have H := tsum_zero_pnat_eq_tsum_nat ((summable_norm_iff).mp (summable_norm_coefficientNat m hm))
  have he (q : ℕ+) : coefficientNat m q = coefficient m q := by
    rw [coefficientNat, dite_eq_right q.ne_zero]
    rfl
  simpa only [show coefficientNat m 0 = 0 by simp [coefficientNat], zero_add, he] using H

/-- LEAF. P0064, page 29, partition the prime factors by divisibility into m. -/
theorem split_euler (m : ℕ) (hm : 0 < m) :
    (∑' q : ℕ, coefficientNat m q) =
    (∏' p : {p : Nat.Primes // p.val ∣ m}, (1 + coefficientNat m p.val.val)) *
    (∏' p : {p : Nat.Primes // ¬ p.val ∣ m}, (1 + coefficientNat m p.val.val)) := by
  have hc := (summable_norm_iff).mp (summable_norm_coefficientNat m hm)
  have hcP : Summable (fun p : Nat.Primes => coefficientNat m p.val) :=
    hc.comp_injective Subtype.val_injective
  have hs : Multipliable (fun p : {p : Nat.Primes // p.val ∣ m} =>
      1 + coefficientNat m p.val.val) :=
    Complex.multipliable_one_add_of_summable (hcP.comp_injective Subtype.val_injective)
  have hsc : Multipliable (fun p : {p : Nat.Primes // ¬ p.val ∣ m} =>
      1 + coefficientNat m p.val.val) :=
    Complex.multipliable_one_add_of_summable (hcP.comp_injective Subtype.val_injective)
  apply Eq.trans (hasProd_local m hm).tprod_eq.symm
  symm
  exact Multipliable.tprod_mul_tprod_compl
    (f := fun p : Nat.Primes => 1 + coefficientNat m p.val)
    (s := {p : Nat.Primes | p.val ∣ m}) hs hsc

/-- P0064, page 29, the printed Euler product identity with explicit prime factors. -/
theorem euler_product_explicit (m : ℕ) (hm : 0 < m) :
    (∑' q : ℕ+, coefficient m q) =
    (∏' p : {p : Nat.Primes // p.val ∣ m}, (1 + 1 / ((p.val.val : ℂ) - 1))) *
    (∏' p : {p : Nat.Primes // ¬ p.val ∣ m}, (1 - 1 / ((p.val.val : ℂ) - 1)^2)) := by
  rw [tsum_positive_eq_nat m hm, split_euler m hm]
  congr 1
  · apply tprod_congr
    intro p
    rw [coefficientNat, dite_eq_right p.val.property.ne_zero,
      coefficient_prime ⟨p.val.val, p.val.property.pos⟩ p.val.property m]
    simp only [PNat.mk_coe, ite_eq_left p.property]
  · apply tprod_congr
    intro p
    rw [coefficientNat, dite_eq_right p.val.property.ne_zero,
      coefficient_prime ⟨p.val.val, p.val.property.pos⟩ p.val.property m]
    simp only [PNat.mk_coe, ite_eq_right p.property]
    ring

/-- CITED. P0064, Lemma 4 part 2, page 28, proved on page 29.
The two prime products are the factors for divisors and nondivisors of m. -/
def lemma4EulerStatement : Prop :=
  ∀ (m : ℕ), 0 < m →
    (∑' q : ℕ+, coefficient m q) =
    (∏' p : {p : Nat.Primes // p.val ∣ m}, (1 + 1 / ((p.val.val : ℂ) - 1))) *
    (∏' p : {p : Nat.Primes // ¬ p.val ∣ m}, (1 - 1 / ((p.val.val : ℂ) - 1)^2))

/-- P0064, Lemma 4 part 2. Exact cited proposition assembled from the leaves. -/
theorem lemma4_euler : lemma4EulerStatement :=
  euler_product_explicit

end LeanLab.Tchudakov1938.Euler113
