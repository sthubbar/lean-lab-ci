/-
P0069, page 25, equation 4.6, and page 28, first line of equation 4.16.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.InclusionExclusion

namespace LeanLab.BakerHarmanPintz1997
open Finset ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- The primes below a real sieve cutoff. -/
noncomputable def primesBelow (z : ℝ) : Finset ℕ := (range ⌈z⌉₊).filter Nat.Prime

/-- The paper's product P z. -/
noncomputable def siftingProduct (z : ℝ) : ℕ := ∏ p ∈ primesBelow z, p

/-- Membership in the finite prime set uses the paper's strict cutoff. -/
theorem mem_primesBelow {p : ℕ} {z : ℝ} :
    p ∈ primesBelow z ↔ p.Prime ∧ (p : ℝ) < z := by
  simp only [primesBelow, mem_filter, mem_range, Nat.lt_ceil, and_comm]

/-- The product of the sieve primes is nonzero. -/
theorem siftingProduct_ne_zero (z : ℝ) : siftingProduct z ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro p hp
  exact (mem_primesBelow.mp hp).1.ne_zero

/-- The paper's coprimality condition agrees with Rough. -/
theorem rough_iff_coprime_siftingProduct (n : ℕ) (z : ℝ) :
    Rough n z ↔ Nat.Coprime (siftingProduct z) n := by
  rw [siftingProduct, Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    have hp' := mem_primesBelow.mp hp
    exact hp'.1.coprime_iff_not_dvd.mpr (h p hp'.1 hp'.2)
  · intro h p hp hpz
    exact hp.coprime_iff_not_dvd.mp (h p (mem_primesBelow.mpr ⟨hp, hpz⟩))

/-- The Moebius sum over common divisors is the coprimality indicator. -/
theorem moebius_sum_common_divisors {P : ℕ} (hP : P ≠ 0) (n : ℕ) :
    (∑ d ∈ P.divisors with d ∣ n, (moebius d : ℂ)) =
      if Nat.Coprime P n then 1 else 0 := by
  have hg : Nat.gcd P n ≠ 0 := by
    intro h
    exact hP ((Nat.gcd_eq_zero_iff.mp h).1)
  have hset : P.divisors.filter (fun d => d ∣ n) = (Nat.gcd P n).divisors := by
    ext d
    constructor
    · intro h
      obtain ⟨hd, hdn⟩ := mem_filter.mp h
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 hdn, hg⟩
    · intro h
      obtain ⟨hdP, hdn⟩ := Nat.dvd_gcd_iff.mp (Nat.mem_divisors.mp h).1
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdP, hP⟩, hdn⟩
  rw [hset]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (Nat.gcd P n))
    (coe_moebius_mul_coe_zeta (R := ℂ))
  simpa only [coe_mul_zeta_apply, intCoe_apply, ArithmeticFunction.one_apply,
    Nat.coprime_iff_gcd_eq_one] using h

/-- The rough indicator is the Moebius sum used in equation 4.16 on page 28. -/
theorem psi_eq_moebius_sum (n : ℕ) (z : ℝ) :
    psi n z = ∑ d ∈ (siftingProduct z).divisors with d ∣ n, (moebius d : ℂ) := by
  rw [moebius_sum_common_divisors (siftingProduct_ne_zero z), psi,
    rough_iff_coprime_siftingProduct]
  split_ifs <;> rfl

#print axioms mem_primesBelow
#print axioms siftingProduct_ne_zero
#print axioms rough_iff_coprime_siftingProduct
#print axioms moebius_sum_common_divisors
#print axioms psi_eq_moebius_sum
end LeanLab.BakerHarmanPintz1997
