import Mathlib

/-!
Integer certificates for the proper prime power lower bounds in
Schoenfeld page 356, displays 9.2 and 9.3.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
open Real Finset

/-- Product of the extra prime factors counted by psi minus theta.
The square root cutoff removes all zero exponent contributions.
This is derived integer proof data for page 356, display 9.3. -/
def gapProduct (N : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE (Nat.sqrt N), p ^ (Nat.log p N - 1)

/-- The logarithm of the integer certificate product is the actual
proper prime power gap. Derived identity for page 356, display 9.3. -/
theorem gap_eq_log_product (N : ℕ) (hN : 1 ≤ N) :
    Chebyshev.psi N - Chebyshev.theta N = log (gapProduct N) := by
  have hrewrite : Chebyshev.psi N - Chebyshev.theta N =
      ∑ p ∈ Nat.primesLE N, ((Nat.log p N - 1 : ℕ) : ℝ) * log p := by
    rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log,
      ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hpN : p ≤ N := (Nat.mem_primesLE.mp hp).1
    have hlog : 1 ≤ Nat.log p N := Nat.log_pos hpp.one_lt hpN
    rw [Nat.cast_sub hlog]
    norm_num only [Nat.cast_one]
    ring
  have hsub : Nat.primesLE (Nat.sqrt N) ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.sqrt_le_self N),
      (Nat.mem_primesLE.mp hp).2⟩
  have hrestrict : (∑ p ∈ Nat.primesLE N, ((Nat.log p N - 1 : ℕ) : ℝ) * log p) =
      ∑ p ∈ Nat.primesLE (Nat.sqrt N), ((Nat.log p N - 1 : ℕ) : ℝ) * log p := by
    symm
    apply sum_subset hsub
    intro p hp hpnot
    have hroot : Nat.sqrt N < p := by
      by_contra h
      exact hpnot (Nat.mem_primesLE.mpr ⟨by omega, (Nat.mem_primesLE.mp hp).2⟩)
    have hlog : Nat.log p N ≤ 1 := by
      by_contra h
      have hpow : p ^ 2 ≤ N := Nat.pow_le_of_le_log (by omega : N ≠ 0) (by omega)
      have hh : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr hpow
      omega
    simp [Nat.sub_eq_zero_of_le hlog]
  rw [hrewrite, hrestrict, gapProduct, Nat.cast_prod,
    log_prod (fun p hp => by
      have hp0 : p ≠ 0 := (Nat.mem_primesLE.mp hp).2.ne_zero
      exact_mod_cast pow_ne_zero (Nat.log p N - 1) hp0)]
  simp only [Nat.cast_pow, log_pow]

/-- Monotonicity of the proper prime power gap, including real
endpoints. Derived transfer for page 356, display 9.3. -/
theorem gap_mono {X Y : ℝ} (hXY : X ≤ Y) :
    Chebyshev.psi X - Chebyshev.theta X ≤ Chebyshev.psi Y - Chebyshev.theta Y := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hn, hp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,
      (mem_Ioc.mp hn).2.trans (Nat.floor_mono hXY)⟩, hp⟩
  · intro n hn hnot
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- A rational exponential certificate gives a lower bound for the
prime power gap. The base is a rounded upper bound for exp 1.
Derived certificate transfer for page 356, display 9.3. -/
theorem gap_of_certificate (N m d : ℕ) (hN : 1 ≤ N) (hd : 0 < d)
    (hc : 2718282 ^ m < gapProduct N ^ d * 1000000 ^ m) :
    (m : ℝ) / d < Chebyshev.psi N - Chebyshev.theta N := by
  have hb : exp (1 : ℝ) < 2718282 / 1000000 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hp : 0 < gapProduct N := by
    unfold gapProduct
    exact prod_pos fun p hp => pow_pos (Nat.mem_primesLE.mp hp).2.pos _
  have hcR : ((2718282 : ℝ) / 1000000) ^ m < (gapProduct N : ℝ) ^ d := by
    rw [div_pow, div_lt_iff₀ (by positivity)]
    exact_mod_cast hc
  have hm : exp (m : ℝ) ≤ ((2718282 : ℝ) / 1000000) ^ m := by
    rw [← mul_one (m : ℝ), exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le hb.le _
  have hh := hm.trans_lt hcR
  have hl := log_lt_log (exp_pos _) hh
  rw [log_exp, log_pow, ← gap_eq_log_product N hN] at hl
  apply (div_lt_iff₀ (by exact_mod_cast hd)).mpr
  simpa only [mul_comm] using hl

/-- A smallest factor implementation of the same integer product.
This is executable proof data for page 356, display 9.3. -/
def fastGapProduct (N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (Nat.sqrt N + 1)).filter
    (fun p => 2 ≤ p ∧ Nat.minFac p = p), p ^ (Nat.log p N - 1)

/-- The executable product equals the arithmetic product by Mathlib's
smallest factor criterion. Derived transfer for page 356, display 9.3. -/
theorem gapProduct_eq_fast (N : ℕ) : gapProduct N = fastGapProduct N := by
  simp only [gapProduct, fastGapProduct, ← Nat.prime_def_minFac]
  rfl

end LeanLab.LiuWang2002.Task352

#print axioms LeanLab.LiuWang2002.Task352.gap_eq_log_product
#print axioms LeanLab.LiuWang2002.Task352.gap_mono
#print axioms LeanLab.LiuWang2002.Task352.gap_of_certificate

#print axioms LeanLab.LiuWang2002.Task352.gapProduct_eq_fast
