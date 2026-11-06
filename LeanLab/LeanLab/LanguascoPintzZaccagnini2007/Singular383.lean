import LeanLab.LanguascoPintzZaccagnini2007.Decomp383a

/-!
Journal page 772. The parity remark and the lower bound from display 2.
These use the same Euler product as the arithmetic supply.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

/-- Journal page 772, the remark before display 2. The singular series vanishes
at every odd natural number because its factor at the prime 2 is zero. -/
theorem singular_odd_zero383 {n : ℕ} (hn : Odd n) : Sing n = 0 := by
  have hd : ¬ 2 ∣ n := fun h => (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr h)
  unfold Sing
  refine (hasProd_zero_of_exists_eq_zero ⟨⟨2, Nat.prime_two⟩, ?_⟩).tprod_eq
  norm_num [hd]

/-- Journal page 772 display 2. At every positive even input, the singular
series is at least 2c0 because every factor of H is at least one. -/
theorem singular_even_lower383 {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    2 * LeanLab.ChenExplicit.twinC ≤ Sing n := by
  rw [singular_factorization383 hn h0]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_H n)
    (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)

/-- Journal page 772, parity remark and display 2. For positive natural n,
the singular series is positive exactly when n is even. -/
theorem singular_pos_iff_even383 {n : ℕ} (h0 : n ≠ 0) : 0 < Sing n ↔ Even n := by
  constructor
  · intro hp
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · rw [singular_odd_zero383 ho] at hp
      exact False.elim (lt_irrefl 0 hp)
  · intro he
    exact (mul_pos (by norm_num) LeanLab.ChenExplicit.twinC_pos).trans_le (singular_even_lower383 he h0)

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.singular_odd_zero383
#print axioms LeanLab.LPZ2007.singular_even_lower383
#print axioms LeanLab.LPZ2007.singular_pos_iff_even383
