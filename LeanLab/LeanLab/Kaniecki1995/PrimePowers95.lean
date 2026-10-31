/-
P0022, page 369, the per prime geometric identity behind display 20.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Kaniecki1995.Lemma5Red

namespace LeanLab.Kaniecki1995.PrimePowers95
open Real Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- Page 369, display 20. The geometric tail at one prime splits into the
all even contribution and the odd remainder. Here z stands for p to the s. -/
theorem geometric_split (z b : ℂ) (hz : 1 < ‖z‖) :
    (∑' r : ℕ, b / z ^ (r + 2)) = b / (z ^ 2 - 1) + b / (z * (z ^ 2 - 1)) := by
  have hz0 : z ≠ 0 := by
    intro h
    have heq : ‖z‖ = 0 := by simp [h]
    linarith
  have hn0 : 0 < ‖z‖ := by linarith
  have hsmall : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact (inv_lt_one₀ hn0).mpr hz
  have hz2 : z ^ 2 - 1 ≠ 0 := by
    intro h
    have heq := congrArg norm (sub_eq_zero.mp h)
    rw [norm_pow, norm_one] at heq
    nlinarith
  have hzminus : -1 + z ≠ 0 := by
    intro h
    have heq : z = 1 := by linear_combination h
    have hn := congrArg norm heq
    rw [norm_one] at hn
    linarith
  have hden : 1 - z⁻¹ ≠ 0 := by
    intro h
    have heq : z⁻¹ = 1 := (sub_eq_zero.mp h).symm
    rw [heq, norm_one] at hsmall
    exact lt_irrefl _ hsmall
  calc (∑' r : ℕ, b / z ^ (r + 2)) =
      (b * z⁻¹ ^ 2) * ∑' r : ℕ, z⁻¹ ^ r := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro r
        rw [div_eq_mul_inv, inv_pow, pow_add]
        ring
    _ = (b * z⁻¹ ^ 2) * (1 - z⁻¹)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hsmall]
    _ = b / (z ^ 2 - 1) + b / (z * (z ^ 2 - 1)) := by
      field_simp [hz0, hz2, hden, hzminus]
      ring_nf
      field_simp [hzminus]
      <;> ring

/-- Page 369, display 20. The preceding identity for a prime p and Re s positive.
This is a local identity. The exchange of the prime sums is a separate step. -/
theorem prime_split {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (∑' r : ℕ, (Real.log p : ℂ) / (p : ℂ) ^ (((r + 2 : ℕ) : ℂ) * s)) =
      (Real.log p : ℂ) / ((p : ℂ) ^ (2 * s) - 1) +
      (Real.log p : ℂ) / ((p : ℂ) ^ s * ((p : ℂ) ^ (2 * s) - 1)) := by
  have hn : 1 < ‖(p : ℂ) ^ s‖ := by
    rw [norm_natCast_cpow_of_pos hp.pos]
    exact Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hs
  have hpow : (p : ℂ) ^ (2 * s) = ((p : ℂ) ^ s) ^ 2 := by
    simpa using Complex.cpow_nat_mul (p : ℂ) 2 s
  rw [hpow]
  simpa only [Complex.cpow_nat_mul] using geometric_split ((p : ℂ) ^ s) (Real.log p) hn

/-- Page 369. The local geometric identity applies at p equal to two and s equal to one. -/
theorem prime_split_instance : 0 < (1 : ℂ).re ∧ Nat.Prime 2 := by
  norm_num

/-- Page 369, display 20. The geometric sum starting at the first power. -/
theorem geometric_full (z b : ℂ) (hz : 1 < ‖z‖) :
    (∑' r : ℕ, b / z ^ (r + 1)) = b / (z - 1) := by
  have hz0 : z ≠ 0 := by
    intro h
    have heq : ‖z‖ = 0 := by simp [h]
    linarith
  have hsmall : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact (inv_lt_one₀ (by linarith)).mpr hz
  have hz1 : z - 1 ≠ 0 := by
    intro h
    have heq := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one] at heq
    linarith
  have hden : 1 - z⁻¹ ≠ 0 := by
    intro h
    have heq : z⁻¹ = 1 := (sub_eq_zero.mp h).symm
    rw [heq, norm_one] at hsmall
    exact lt_irrefl _ hsmall
  calc (∑' r : ℕ, b / z ^ (r + 1)) =
      (b * z⁻¹) * ∑' r : ℕ, z⁻¹ ^ r := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro r
        rw [div_eq_mul_inv, inv_pow, pow_succ]
        ring
    _ = (b * z⁻¹) * (1 - z⁻¹)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hsmall]
    _ = b / (z - 1) := by field_simp [hz0, hz1, hden]

/-- Page 369, display 20. The von Mangoldt series is the corresponding prime sum.
Applying this at twice s identifies the even powers in g. -/
theorem vonMangoldt_prime_sum {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗Λ s = ∑' p : Nat.Primes, (Real.log p : ℂ) / ((p : ℂ) ^ s - 1) := by
  let f : ℕ → ℂ := LSeries.term ↗Λ s
  have hf : Summable f := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsupport : Function.support f ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    have hzero : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
    apply hn
    simp [f, LSeries.term, hzero]
  change (∑' n : ℕ, f n) = _
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hf hsupport]
  apply tsum_congr
  intro p
  calc (∑' r : ℕ, f (p ^ (r + 1))) =
      ∑' r : ℕ, (Real.log p : ℂ) / ((p : ℂ) ^ s) ^ (r + 1) := by
        apply tsum_congr
        intro r
        have hpow : (((p : ℕ) ^ (r + 1) : ℕ) : ℂ) ^ s =
            ((p : ℂ) ^ s) ^ (r + 1) := by
          rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
        dsimp only [f]
        rw [LSeries.term_of_ne_zero (pow_ne_zero (r + 1) p.prop.ne_zero)]
        change (↑(Λ ((p : ℕ) ^ (r + 1))) : ℂ) / _ = _
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
          ArithmeticFunction.vonMangoldt_apply_prime p.prop, hpow]
    _ = (Real.log p : ℂ) / ((p : ℂ) ^ s - 1) := by
      apply geometric_full
      rw [norm_natCast_cpow_of_pos p.prop.pos]
      exact Real.one_lt_rpow (by exact_mod_cast p.prop.one_lt) (by linarith)

end LeanLab.Kaniecki1995.PrimePowers95

#print axioms LeanLab.Kaniecki1995.PrimePowers95.geometric_split
#print axioms LeanLab.Kaniecki1995.PrimePowers95.prime_split
#print axioms LeanLab.Kaniecki1995.PrimePowers95.prime_split_instance

#print axioms LeanLab.Kaniecki1995.PrimePowers95.geometric_full
#print axioms LeanLab.Kaniecki1995.PrimePowers95.vonMangoldt_prime_sum
