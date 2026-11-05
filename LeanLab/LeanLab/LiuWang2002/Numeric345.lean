import LeanLab.LiuWang2002.Decomp345a

/-!
Task345. The denominator threshold in display 6.5 on page 168.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345

open Real

/-- The denominator half of display 6.5 on page 168.
It follows from the size half of that display and the lower bound in 6.3. -/
theorem q_exp_lower (N : ℝ) (q : ℕ) (hN : exp 30.95 ≤ N)
    (hq : (0.28 / 1.0012) ^ 2 * log N ^ 4 < q) : exp 11 ≤ (q : ℝ) := by
  have hNp : 0 < N := (exp_pos _).trans_le hN
  have hL : 30.95 ≤ log N := (le_log_iff_exp_le hNp).mpr hN
  have he : exp 1 ≤ (2.72 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  calc
    exp 11 = exp 1 ^ 11 := by simpa using exp_nat_mul (1 : ℝ) 11
    _ ≤ 2.72 ^ 11 := pow_le_pow_left₀ (exp_pos 1).le he 11
    _ ≤ (0.28 / 1.0012) ^ 2 * (30.95 : ℝ) ^ 4 := by norm_num
    _ ≤ (0.28 / 1.0012) ^ 2 * log N ^ 4 := by gcongr
    _ ≤ (q : ℝ) := hq.le

open Finset

/-- A derived numerical budget for the higher prime powers in display 5.3 star
on Schoenfeld page 356. Splitting exponents three through eight leaves the
coarse ninth-root tail. This certifies its scalar envelope for log X at least
9.634. The finite sum and initial range transfers remain separate tasks.
The five exponential rates are the differences from the cube root exponent. -/
theorem higher_root_profile (L : ℝ) (hL : 9.634 ≤ L) :
    1.001093 * (1 + exp (-((1 / 12 : ℝ) * L)) + exp (-((2 / 15 : ℝ) * L)) +
      exp (-((1 / 6 : ℝ) * L)) + exp (-((4 / 21 : ℝ) * L)) +
        exp (-((5 / 24 : ℝ) * L)) +
          (L / log 2 - 8) * exp (-((2 / 9 : ℝ) * L))) < 3 := by
  have endpoint (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
      (hs : 1 ≤ c * (∑ i ∈ range 10, (r * 9.634) ^ i / (i.factorial : ℝ))) :
      exp (-(r * L)) ≤ c := by
    have ht := Real.sum_le_exp_of_nonneg (mul_nonneg hr (by norm_num : (0 : ℝ) ≤ 9.634)) 10
    have hm : exp (r * 9.634) ≤ exp (r * L) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hr)
    have hb : 1 ≤ c * exp (r * L) :=
      hs.trans (mul_le_mul_of_nonneg_left (ht.trans hm) hc)
    rw [exp_neg]
    simpa only [one_div] using (div_le_iff₀ (exp_pos (r * L))).mpr hb
  have h4 := endpoint (1 / 12) 0.45 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have h5 := endpoint (2 / 15) 0.28 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have h6 := endpoint (1 / 6) 0.202 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have h7 := endpoint (4 / 21) 0.16 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have h8 := endpoint (5 / 24) 0.135 (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hl : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hf : 9 / (2 * log (2 : ℝ)) ≤ 6.5 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.log_two_gt_d9]
  have hs : (9.2 : ℝ) ≤ exp 2.23 := by
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2.23) 10
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    linarith
  have ha : (2.23 : ℝ) ≤ (16 / 9 : ℝ) * log 2 + 1 := by
    linarith [Real.log_two_gt_d9]
  have hi : exp (-((16 / 9 : ℝ) * log 2 + 1)) ≤ 1 / 9.2 := by
    rw [exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9.2) (hs.trans (exp_le_exp.mpr ha))
  have ht : ((2 / 9 : ℝ) * L - (16 / 9 : ℝ) * log 2) * exp (-((2 / 9 : ℝ) * L)) ≤
      exp (-((16 / 9 : ℝ) * log 2 + 1)) := by
    calc
      _ ≤ exp ((2 / 9 : ℝ) * L - (16 / 9 : ℝ) * log 2 - 1) *
          exp (-((2 / 9 : ℝ) * L)) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        linarith [Real.add_one_le_exp ((2 / 9 : ℝ) * L - (16 / 9 : ℝ) * log 2 - 1)]
      _ = _ := by rw [← exp_add]; congr 1; ring
  have htail : (L / log 2 - 8) * exp (-((2 / 9 : ℝ) * L)) ≤ 0.71 := by
    calc
      _ = (9 / (2 * log (2 : ℝ))) *
          (((2 / 9 : ℝ) * L - (16 / 9 : ℝ) * log 2) * exp (-((2 / 9 : ℝ) * L))) := by
        field_simp
        ring
      _ ≤ (9 / (2 * log (2 : ℝ))) * exp (-((16 / 9 : ℝ) * log 2 + 1)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ 6.5 * (1 / 9.2) := mul_le_mul hf hi (exp_pos _).le (by norm_num)
      _ ≤ 0.71 := by norm_num
  linarith

/-- A derived higher prime power root sum estimate for Schoenfeld page 356,
display 5.3 star. For X at least exp 9.634, the finite third through K-th
root sum times 1.001093 is below three cube roots whenever K lies between
eight and log X divided by log 2. This is a scalar sum, without theta or psi. -/
theorem higher_root_sum (X : ℝ) (K : ℕ) (hX : exp 9.634 ≤ X) (hK8 : 8 ≤ K)
    (hK : (K : ℝ) ≤ log X / log 2) :
    1.001093 * (∑ k ∈ Icc 3 K, X ^ (1 / (k : ℝ))) < 3 * X ^ (1 / 3 : ℝ) := by
  have hXp : 0 < X := (exp_pos _).trans_le hX
  have hL : 9.634 ≤ log X := (le_log_iff_exp_le hXp).mpr hX
  have hX1 : 1 ≤ X := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 9.634)).trans hX
  have hsplit : Icc 3 K = Icc (3 : ℕ) 8 ∪ Icc 9 K := by ext n; simp only [mem_Icc, mem_union]; omega
  have hd : Disjoint (Icc (3 : ℕ) 8) (Icc 9 K) := by
    apply disjoint_left.mpr
    intro n hn hm
    simp only [mem_Icc] at hn hm
    omega
  have ht : (∑ k ∈ Icc 9 K, X ^ (1 / (k : ℝ))) ≤
      (log X / log 2 - 8) * X ^ (1 / 9 : ℝ) := by
    calc
      _ ≤ ∑ _k ∈ Icc 9 K, X ^ (1 / 9 : ℝ) := by
        apply sum_le_sum
        intro k hk
        have hk9 : (9 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        exact Real.rpow_le_rpow_of_exponent_le hX1
          (one_div_le_one_div_of_le (by norm_num) hk9)
      _ = ((K : ℝ) - 8) * X ^ (1 / 9 : ℝ) := by
        simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hh : K + 1 - 9 = K - 8 := by omega
        rw [hh, Nat.cast_sub hK8]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hK 8) (Real.rpow_nonneg hXp.le _)
  have he (k : ℕ) : X ^ (1 / (k : ℝ)) =
      X ^ (1 / 3 : ℝ) * exp (-((1 / 3 - 1 / (k : ℝ)) * log X)) := by
    rw [Real.rpow_def_of_pos hXp, Real.rpow_def_of_pos hXp, ← exp_add]
    congr 1
    ring
  have h4 := he 4
  have h5 := he 5
  have h6 := he 6
  have h7 := he 7
  have h8 := he 8
  have h9 := he 9
  norm_num at h4 h5 h6 h7 h8 h9
  have hp : (∑ k ∈ Icc (3 : ℕ) 8, X ^ (1 / (k : ℝ))) =
      X ^ (1 / 3 : ℝ) * (1 + exp (-((1 / 12 : ℝ) * log X)) +
        exp (-((2 / 15 : ℝ) * log X)) + exp (-((1 / 6 : ℝ) * log X)) +
          exp (-((4 / 21 : ℝ) * log X)) + exp (-((5 / 24 : ℝ) * log X))) := by
    rw [show Icc (3 : ℕ) 8 = ({3, 4, 5, 6, 7, 8} : Finset ℕ) by decide]
    norm_num
    rw [h4, h5, h6, h7, h8]
    ring
  have hb : (∑ k ∈ Icc 3 K, X ^ (1 / (k : ℝ))) ≤
      X ^ (1 / 3 : ℝ) * (1 + exp (-((1 / 12 : ℝ) * log X)) +
        exp (-((2 / 15 : ℝ) * log X)) + exp (-((1 / 6 : ℝ) * log X)) +
          exp (-((4 / 21 : ℝ) * log X)) + exp (-((5 / 24 : ℝ) * log X)) +
            (log X / log 2 - 8) * exp (-((2 / 9 : ℝ) * log X))) := by
    rw [hsplit, sum_union hd]
    calc
      _ ≤ (∑ k ∈ Icc (3 : ℕ) 8, X ^ (1 / (k : ℝ))) + (log X / log 2 - 8) * X ^ (1 / 9 : ℝ) :=
        add_le_add le_rfl ht
      _ = _ := by rw [hp, h9]; ring
  calc
    _ ≤ 1.001093 * (X ^ (1 / 3 : ℝ) * (1 + exp (-((1 / 12 : ℝ) * log X)) +
        exp (-((2 / 15 : ℝ) * log X)) + exp (-((1 / 6 : ℝ) * log X)) +
          exp (-((4 / 21 : ℝ) * log X)) + exp (-((5 / 24 : ℝ) * log X)) +
            (log X / log 2 - 8) * exp (-((2 / 9 : ℝ) * log X)))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = X ^ (1 / 3 : ℝ) * (1.001093 * (1 + exp (-((1 / 12 : ℝ) * log X)) +
        exp (-((2 / 15 : ℝ) * log X)) + exp (-((1 / 6 : ℝ) * log X)) +
          exp (-((4 / 21 : ℝ) * log X)) + exp (-((5 / 24 : ℝ) * log X)) +
            (log X / log 2 - 8) * exp (-((2 / 9 : ℝ) * log X)))) := by ring
    _ < X ^ (1 / 3 : ℝ) * 3 :=
      mul_lt_mul_of_pos_left (higher_root_profile (log X) hL) (Real.rpow_pos_of_pos hXp _)
    _ = _ := by ring

/-- The large range of Schoenfeld page 356, display 5.3 star, from an explicit
global theta upper bound. CONDITIONAL ON hTheta. The finite root expansion,
its cutoff and the numerical tail are proved here. The original global
prime_power_upper statement also needs the smaller positive X range. -/
theorem prime_power_large_of_theta (hTheta : ∀ Y : ℝ, 0 < Y → Chebyshev.theta Y < 1.001093 * Y)
    (X : ℝ) (hX : exp 9.634 ≤ X) :
    Chebyshev.psi X - Chebyshev.theta X < 1.001093 * √X + 3 * X ^ (1 / 3 : ℝ) := by
  have hXp : 0 < X := (exp_pos _).trans_le hX
  have hL : 9.634 ≤ log X := (le_log_iff_exp_le hXp).mpr hX
  have hl2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hLp : 0 < log X := by linarith
  let K : ℕ := ⌊log X / log 2⌋₊
  have hK8 : 8 ≤ K := by
    apply Nat.le_floor
    apply (le_div_iff₀ hl2).mpr
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  have hK : (K : ℝ) ≤ log X / log 2 := Nat.floor_le (by positivity)
  have hX2 : 2 ≤ X := by linarith [Real.add_one_le_exp (9.634 : ℝ)]
  have hsplit : Icc 2 K = {2} ∪ Icc 3 K := by
    ext n
    simp only [mem_Icc, mem_union, mem_singleton]
    omega
  have hd : Disjoint ({2} : Finset ℕ) (Icc 3 K) := by
    apply disjoint_left.mpr
    intro n hn hm
    simp only [mem_singleton] at hn
    subst n
    simp at hm
  have hi := Chebyshev.psi_eq_theta_add_sum_theta hX2
  change Chebyshev.psi X = Chebyshev.theta X +
    ∑ k ∈ Icc 2 K, Chebyshev.theta (X ^ (1 / (k : ℝ))) at hi
  rw [hsplit, sum_union hd, sum_singleton] at hi
  simp only [Nat.cast_ofNat] at hi
  rw [show X ^ (1 / (2 : ℝ)) = √X from (Real.sqrt_eq_rpow X).symm] at hi
  have ht : (∑ k ∈ Icc 3 K, Chebyshev.theta (X ^ (1 / (k : ℝ)))) ≤
      1.001093 * ∑ k ∈ Icc 3 K, X ^ (1 / (k : ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    exact (hTheta _ (Real.rpow_pos_of_pos hXp _)).le
  have hs := hTheta (√X) (Real.sqrt_pos.mpr hXp)
  have hr := higher_root_sum X K hX hK8 hK
  linarith

/-- An unconditional initial range of display 5.3 star on Schoenfeld page 356.
The cutoff 64 is a derived verification range. Exact proper prime power sums
at 16 and 64 and monotonicity cover every positive real X through 64.
No theta estimate from a cited source is used. -/
theorem prime_power_small (X : ℝ) (hX : 0 < X) (hX64 : X ≤ 64) :
    Chebyshev.psi X - Chebyshev.theta X <
      1.001093 * √X + 3 * X ^ (1 / 3 : ℝ) := by
  have h16eq : Chebyshev.psi 16 - Chebyshev.theta 16 = 3 * log 2 + log 3 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter]
    simp +decide [Finset.sum_Ioc_succ_top, ArithmeticFunction.vonMangoldt_apply]
    <;> simp only [show IsPrimePow 9 by decide +kernel,
      show ¬IsPrimePow 15 by decide +kernel, ite_true, ite_false]
    <;> ring
  have h64eq : Chebyshev.psi 64 - Chebyshev.theta 64 = 5 * log 2 + 2 * log 3 + log 5 + log 7 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter]
    simp +decide [Finset.sum_Ioc_succ_top, ArithmeticFunction.vonMangoldt_apply]
    <;> simp only [show IsPrimePow 9 by decide +kernel,
        show ¬IsPrimePow 15 by decide +kernel,
        show ¬IsPrimePow 21 by decide +kernel,
        show IsPrimePow 25 by decide +kernel,
        show IsPrimePow 27 by decide +kernel,
        show ¬IsPrimePow 33 by decide +kernel,
        show ¬IsPrimePow 35 by decide +kernel,
        show ¬IsPrimePow 39 by decide +kernel,
        show ¬IsPrimePow 45 by decide +kernel,
        show IsPrimePow 49 by decide +kernel,
        show ¬IsPrimePow 51 by decide +kernel,
        show ¬IsPrimePow 55 by decide +kernel,
        show ¬IsPrimePow 57 by decide +kernel,
        show ¬IsPrimePow 63 by decide +kernel, ite_true, ite_false]
    <;> ring
  have h3 : log (3 : ℝ) ≤ 1.6 * log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3 ^ 5)
      (by norm_num : (3 : ℝ) ^ 5 ≤ 2 ^ 8)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have h5 : log (5 : ℝ) ≤ 2.4 * log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 5 ^ 5)
      (by norm_num : (5 : ℝ) ^ 5 ≤ 2 ^ 12)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have h7 : log (7 : ℝ) ≤ 2.9 * log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 7 ^ 10)
      (by norm_num : (7 : ℝ) ^ 10 ≤ 2 ^ 29)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have hb16 : Chebyshev.psi 16 - Chebyshev.theta 16 < 4 := by
    rw [h16eq]
    linarith [Real.log_two_lt_d9]
  have hb64 : Chebyshev.psi 64 - Chebyshev.theta 64 < 10 := by
    rw [h64eq]
    linarith [Real.log_two_lt_d9]
  have hm (n : ℕ) (hn : ⌊X⌋₊ ≤ n) :
      Chebyshev.psi X - Chebyshev.theta X ≤ Chebyshev.psi n - Chebyshev.theta n := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨hk, hkp⟩ := mem_filter.mp hk
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hn⟩, hkp⟩
    · intro k hk hnot
      exact ArithmeticFunction.vonMangoldt_nonneg
  by_cases h4 : X < 4
  · have hf : ⌊X⌋₊ ≤ 3 := by
      by_contra h
      have hh : (4 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast (show 4 ≤ ⌊X⌋₊ by omega)
      linarith [Nat.floor_le hX.le]
    have hb := hm 3 hf
    have hz : Chebyshev.psi 3 - Chebyshev.theta 3 = 0 := by
      norm_num [Chebyshev.psi_sub_theta_eq_sum_not_prime, sum_filter,
        Finset.sum_Ioc_succ_top, ArithmeticFunction.vonMangoldt_apply]
    norm_num only [Nat.cast_ofNat] at hb
    rw [hz] at hb
    have hr : 0 < 1.001093 * √X + 3 * X ^ (1 / 3 : ℝ) := by positivity
    linarith
  · have hX4 : 4 ≤ X := le_of_not_gt h4
    by_cases h16 : X < 16
    · have hf := Nat.floor_mono h16.le
      norm_num at hf
      have hb := (hm 16 hf).trans_lt hb16
      have hs : (2 : ℝ) ≤ √X := (Real.le_sqrt (by norm_num) hX.le).mpr (by nlinarith)
      have hc : (1 : ℝ) ≤ X ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      nlinarith
    · have hX16 : 16 ≤ X := le_of_not_gt h16
      have hf := Nat.floor_mono hX64
      norm_num at hf
      have hb := (hm 64 hf).trans_lt hb64
      have hs : (4 : ℝ) ≤ √X := (Real.le_sqrt (by norm_num) hX.le).mpr (by nlinarith)
      have hc : (2 : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
        rw [one_div]
        apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hX.le (by norm_num)).mpr
        norm_num [Real.rpow_natCast]
        linarith
      nlinarith

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.q_exp_lower

#print axioms LeanLab.LiuWang2002.Task345.higher_root_profile

#print axioms LeanLab.LiuWang2002.Task345.higher_root_sum

#print axioms LeanLab.LiuWang2002.Task345.prime_power_large_of_theta

#print axioms LeanLab.LiuWang2002.Task345.prime_power_small
