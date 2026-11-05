import LeanLab.LiuWang2002.PowerCert345
import LeanLab.LiuWang2002.Numeric345

/-!
Task345. Transfer of the compressed certificate to the proper prime power bound.
Source: Schoenfeld page 356, display 5.3 star.
The initial interval certificate is derived proof data.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345
open Real Finset

/-- The proper prime power gap at a positive natural endpoint is at most
0.694 times its compressed bit count. This is the semantic transfer for
Schoenfeld page 356, display 5.3 star. Mathlib supplies the prime logarithm
formula for psi and the base two ceiling logarithm comparison. -/
theorem gap_nat_le_bits (N : ℕ) (hN : 1 ≤ N) :
    Chebyshev.psi N - Chebyshev.theta N ≤ 0.694 * (powerBitSum N : ℝ) := by
  have log_bound (p : ℕ) (hp : p.Prime) : log p ≤ 0.694 * (Nat.clog 2 p : ℝ) := by
    have hpow : (p : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 p := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) p
    have hl := Real.log_le_log (by exact_mod_cast hp.pos) hpow
    rw [Real.log_pow] at hl
    have h2 : log (2 : ℝ) ≤ 0.694 := Real.log_two_lt_d9.le.trans (by norm_num)
    have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (Nat.clog 2 p) : (0 : ℝ) ≤ _)
    nlinarith
  have hrewrite : Chebyshev.psi N - Chebyshev.theta N =
      ∑ p ∈ Nat.primesLE N, ((Nat.log p N - 1 : ℕ) : ℝ) * log p := by
    rw [Chebyshev.psi_eq_sum_mul_log_prime, Chebyshev.theta_eq_sum_primesLE_log, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
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
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hroot : Nat.sqrt N < p := by
      by_contra h
      apply hpnot
      exact Nat.mem_primesLE.mpr ⟨by omega, hpp⟩
    have hlog : Nat.log p N ≤ 1 := by
      by_contra h
      have hpow : p ^ 2 ≤ N := Nat.pow_le_of_le_log (by omega : N ≠ 0) (by omega)
      have hh : p ≤ Nat.sqrt N := Nat.le_sqrt'.mpr hpow
      omega
    simp [Nat.sub_eq_zero_of_le hlog]
  rw [hrewrite, hrestrict]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt N),
        ((Nat.log p N - 1 : ℕ) : ℝ) * (0.694 * (Nat.clog 2 p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (log_bound p (Nat.mem_primesLE.mp hp).2) (Nat.cast_nonneg _)
    _ = 0.694 * (powerBitSum N : ℝ) := by
      unfold powerBitSum
      rw [Nat.cast_sum, mul_sum]
      apply sum_congr rfl
      intro p hp
      push_cast
      ring

/-- The nine certified intervals cover every natural endpoint from 64
through 16384. Their lower square and cube roots fit below the endpoint
and their weighted bit count fits the scaled error budget. These are
derived initial range data for Schoenfeld page 356, display 5.3 star. -/
theorem power_intervals (n : ℕ) (hn : 64 ≤ n) (hn' : n ≤ 16384) :
    ∃ l h a b : ℕ, l ≤ n ∧ n < h ∧ a ^ 2 ≤ l ∧ b ^ 3 ≤ l ∧
      694000 * powerBitSum (h - 1) < 1001093 * a + 3000000 * b := by
  rcases power_bit_certificate with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hc : (64 ≤ n ∧ n < 169) ∨
      (169 ≤ n ∧ n < 361) ∨
      (361 ≤ n ∧ n < 841) ∨
      (841 ≤ n ∧ n < 1681) ∨
      (1681 ≤ n ∧ n < 2809) ∨
      (2809 ≤ n ∧ n < 4913) ∨
      (4913 ≤ n ∧ n < 7921) ∨
      (7921 ≤ n ∧ n < 11881) ∨
      (11881 ≤ n ∧ n < 16385) := by omega
  rcases hc with h | h | h | h | h | h | h | h | h 
  all_goals first
    | exact ⟨64, 169, 8, 4, h.1, h.2, by decide, by decide, by norm_num [h0]⟩
    | exact ⟨169, 361, 13, 5, h.1, h.2, by decide, by decide, by norm_num [h1]⟩
    | exact ⟨361, 841, 19, 7, h.1, h.2, by decide, by decide, by norm_num [h2]⟩
    | exact ⟨841, 1681, 29, 9, h.1, h.2, by decide, by decide, by norm_num [h3]⟩
    | exact ⟨1681, 2809, 41, 11, h.1, h.2, by decide, by decide, by norm_num [h4]⟩
    | exact ⟨2809, 4913, 53, 14, h.1, h.2, by decide, by decide, by norm_num [h5]⟩
    | exact ⟨4913, 7921, 70, 17, h.1, h.2, by decide, by decide, by norm_num [h6]⟩
    | exact ⟨7921, 11881, 89, 19, h.1, h.2, by decide, by decide, by norm_num [h7]⟩
    | exact ⟨11881, 16385, 109, 22, h.1, h.2, by decide, by decide, by norm_num [h8]⟩

/-- The initial real range of Schoenfeld page 356, display 5.3 star.
Every positive X through 16384 is covered by the small range proof or
one of the nine certified intervals. No cited analytic input is used. -/
theorem prime_power_initial (X : ℝ) (hX : 0 < X) (hXcap : X ≤ 16384) :
    Chebyshev.psi X - Chebyshev.theta X <
      1.001093 * √X + 3 * X ^ (1 / 3 : ℝ) := by
  by_cases hsmall : X ≤ 64
  · exact prime_power_small X hX hsmall
  have h64 : 64 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast (le_of_not_ge hsmall))
  have hNcap := Nat.floor_mono hXcap
  norm_num at hNcap
  obtain ⟨l, h, a, b, hl, hh, ha, hb, hbudget⟩ := power_intervals ⌊X⌋₊ h64 hNcap
  have hlX : (l : ℝ) ≤ X :=
    (show (l : ℝ) ≤ (⌊X⌋₊ : ℝ) by exact_mod_cast hl).trans (Nat.floor_le hX.le)
  have haR : (a : ℝ) ^ 2 ≤ X :=
    (show (a : ℝ) ^ 2 ≤ (l : ℝ) by exact_mod_cast ha).trans hlX
  have hbR : (b : ℝ) ^ 3 ≤ X :=
    (show (b : ℝ) ^ 3 ≤ (l : ℝ) by exact_mod_cast hb).trans hlX
  have hs : (a : ℝ) ≤ √X := (Real.le_sqrt (Nat.cast_nonneg _) hX.le).mpr haR
  have hc : (b : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hX.le (by norm_num)).mpr
    have he : (b : ℝ) ^ (3 : ℝ) = (b : ℝ) ^ (3 : ℕ) := by
      simpa using Real.rpow_natCast (b : ℝ) 3
    rwa [he]
  have hcap : 1 ≤ h - 1 := by omega
  have hgap : Chebyshev.psi X - Chebyshev.theta X ≤
      Chebyshev.psi (h - 1 : ℕ) - Chebyshev.theta (h - 1 : ℕ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨hk, hkp⟩ := mem_filter.mp hk
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, ?_⟩, hkp⟩
      have hkn := (mem_Ioc.mp hk).2
      omega
    · intro k hk hnot
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hscaled : 0.694 * (powerBitSum (h - 1) : ℝ) <
      1.001093 * (a : ℝ) + 3 * (b : ℝ) := by
    have hi : (694000 : ℝ) * powerBitSum (h - 1) <
        1001093 * (a : ℝ) + 3000000 * (b : ℝ) := by exact_mod_cast hbudget
    linarith
  have hbound := (hgap.trans (gap_nat_le_bits (h - 1) hcap)).trans_lt hscaled
  linarith

/-- The global proper prime power estimate of Schoenfeld page 356,
display 5.3 star, from the explicitly supplied theta estimate 5.1 star.
CONDITIONAL ON hTheta. The entire initial range is proved by the compressed
certificate and the infinite range by the finite root expansion. -/
theorem prime_power_of_theta (hTheta : ∀ Y : ℝ, 0 < Y → Chebyshev.theta Y < 1.001093 * Y)
    (X : ℝ) (hX : 0 < X) :
    Chebyshev.psi X - Chebyshev.theta X <
      1.001093 * √X + 3 * X ^ (1 / 3 : ℝ) := by
  by_cases hlarge : exp 9.634 ≤ X
  · exact prime_power_large_of_theta hTheta X hlarge
  · have he : exp (9.634 : ℝ) ≤ 16384 := by
      apply (le_log_iff_exp_le (by norm_num : (0 : ℝ) < 16384)).mp
      rw [show (16384 : ℝ) = (2 : ℝ) ^ 14 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_gt_d9]
    exact prime_power_initial X hX ((le_of_not_ge hlarge).trans he)

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.gap_nat_le_bits
#print axioms LeanLab.LiuWang2002.Task345.power_intervals

#print axioms LeanLab.LiuWang2002.Task345.prime_power_initial

#print axioms LeanLab.LiuWang2002.Task345.prime_power_of_theta
