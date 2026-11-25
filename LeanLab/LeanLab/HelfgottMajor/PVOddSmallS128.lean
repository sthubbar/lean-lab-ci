import Mathlib

/-!
Route burst S128, burst-20261122. Split of the EASY LEAF `PVCases1122.odd_small`, Pomerance
2011 Theorem 1, odd case, for the moduli q below 7 left out of `odd_truncated`, into one
LEAF per modulus. q = 0 is excluded by NeZero, q = 1 by hypothesis, and q = 2 has no odd
character since -1 = 1 in ZMod 2; that case is PROVED in `PVCases1122.odd_small`.
All four, odd_small_q3 to odd_small_q6, are PROVED here by S128; q = 6 needs no primitivity, since the odd character values mod 6 are forced; each remaining LEAF is a finite check over one period: the initial segment sums of an odd primitive
character mod q have norm at most sqrt 2, so an interval sum, a difference of two of them,
has norm at most 2 sqrt 2, against a bound above 2.08 for q = 3, above 2.65 for q = 4 and
above 3.14 for q = 5. Mod 6 there is no primitive character.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddSmallS128

open Real Finset

namespace Q3

lemma chi_vals (χ : DirichletCharacter ℂ 3) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    χ (n : ZMod 3) = if n % 3 = 0 then 0 else if n % 3 = 1 then 1 else -1 := by
  have hm1 : χ (-1) = -1 := by
    have h2 : χ (-1) ^ 2 = 1 := by
      rw [← map_pow]; norm_num
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [h2]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hodd
    · exact eq_neg_of_add_eq_zero_left h
  have hn : (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
  rw [hn]
  have hr : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 3
  · simp only [Nat.cast_zero, ite_true]
    exact MulChar.map_nonunit χ not_isUnit_zero
  · simp
  · have : ((2 : ℕ) : ZMod 3) = -1 := by decide
    simp only [this, hm1]; norm_num

lemma partial_eq (χ : DirichletCharacter ℂ 3) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ∑ m ∈ range n, χ (m : ZMod 3) = if n % 3 = 2 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, chi_vals χ hodd k]
    have hr : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hk : (k + 1) % 3 = (k % 3 + 1) % 3 := by omega
    rw [hk]
    interval_cases h : k % 3 <;> norm_num

lemma partial_norm_le (χ : DirichletCharacter ℂ 3) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ‖∑ m ∈ range n, χ (m : ZMod 3)‖ ≤ 1 := by
  rw [partial_eq χ hodd n]; split_ifs <;> simp only [norm_one, norm_zero, zero_le_one, le_refl]

lemma interval_norm_le (χ : DirichletCharacter ℂ 3) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod 3)‖ ≤ 2 := by
  by_cases hMN : M ≤ N + 1
  · have hI : Icc M N = Ico M (N + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, sum_Ico_eq_sub _ hMN]
    calc _ ≤ ‖∑ m ∈ range (N+1), χ (m : ZMod 3)‖ + ‖∑ m ∈ range M, χ (m : ZMod 3)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (partial_norm_le χ hodd _) (partial_norm_le χ hodd _)
      _ = 2 := by norm_num
  · have : Icc M N = ∅ := by ext x; simp; omega
    rw [this]; simp

lemma rhs_ge :
    (2:ℝ) ≤ 1 / (2 * π) * sqrt (3:ℕ) * log (3:ℕ) + 1 / π * sqrt (3:ℕ) * log (log (3:ℕ)) + sqrt (3:ℕ) := by
  push_cast
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hl3 : (1 : ℝ) ≤ log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hll : 0 ≤ log (log 3) := Real.log_nonneg hl3
  have hs : (1.732 : ℝ) ≤ sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have hs0 : 0 ≤ sqrt 3 := Real.sqrt_nonneg _
  have h1 : 1 / (2 * π) * sqrt 3 * log 3 ≥ 1 / (2 * π) * sqrt 3 :=
    by have : 0 ≤ 1 / (2 * π) * sqrt 3 := by positivity
       nlinarith
  have h2 : 0 ≤ 1 / π * sqrt 3 * log (log 3) := by positivity
  have h3 : 1 / (2 * π) ≥ 1 / 6.3 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have h4 : 1 / (2 * π) * sqrt 3 ≥ 1 / 6.3 * sqrt 3 := mul_le_mul_of_nonneg_right h3 hs0
  nlinarith

end Q3

namespace Q4

lemma chi_vals (χ : DirichletCharacter ℂ 4) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    χ (n : ZMod 4) = if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 := by
  have hm1 : χ (-1) = -1 := by
    have h2 : χ (-1) ^ 2 = 1 := by
      rw [← map_pow]; norm_num
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [h2]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hodd
    · exact eq_neg_of_add_eq_zero_left h
  have hn : (n : ZMod 4) = ((n % 4 : ℕ) : ZMod 4) := (ZMod.natCast_mod n 4).symm
  rw [hn]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 4
  · have hu : ¬ IsUnit ((0 : ℕ) : ZMod 4) := by decide
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    exact MulChar.map_nonunit χ hu
  · simp
  · have hu : ¬ IsUnit ((2 : ℕ) : ZMod 4) := by decide
    rw [if_neg (by norm_num), if_neg (by norm_num)]
    exact MulChar.map_nonunit χ hu
  · have : ((3 : ℕ) : ZMod 4) = -1 := by decide
    simp only [this, hm1]; norm_num

lemma partial_eq (χ : DirichletCharacter ℂ 4) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ∑ m ∈ range n, χ (m : ZMod 4) = if n % 4 = 2 ∨ n % 4 = 3 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, chi_vals χ hodd k]
    have hr : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hk : (k + 1) % 4 = (k % 4 + 1) % 4 := by omega
    rw [hk]
    interval_cases h : k % 4 <;> norm_num

lemma partial_norm_le (χ : DirichletCharacter ℂ 4) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ‖∑ m ∈ range n, χ (m : ZMod 4)‖ ≤ 1 := by
  rw [partial_eq χ hodd n]; split_ifs <;> simp only [norm_one, norm_zero, zero_le_one, le_refl]

lemma interval_norm_le (χ : DirichletCharacter ℂ 4) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod 4)‖ ≤ 2 := by
  by_cases hMN : M ≤ N + 1
  · have hI : Icc M N = Ico M (N + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, sum_Ico_eq_sub _ hMN]
    calc _ ≤ ‖∑ m ∈ range (N+1), χ (m : ZMod 4)‖ + ‖∑ m ∈ range M, χ (m : ZMod 4)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (partial_norm_le χ hodd _) (partial_norm_le χ hodd _)
      _ = 2 := by norm_num
  · have : Icc M N = ∅ := by ext x; simp; omega
    rw [this]; simp

lemma rhs_ge :
    (2:ℝ) ≤ 1 / (2 * π) * sqrt (4:ℕ) * log (4:ℕ) + 1 / π * sqrt (4:ℕ) * log (log (4:ℕ)) + sqrt (4:ℕ) := by
  push_cast
  have hpi0 : 0 < π := Real.pi_pos
  have hl4 : (1 : ℝ) ≤ log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hll : 0 ≤ log (log 4) := Real.log_nonneg hl4
  have hs : sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs]
  have h1 : 0 ≤ 1 / (2 * π) * 2 * log 4 := by have : (0:ℝ) ≤ log 4 := by linarith
                                              positivity
  have h2 : 0 ≤ 1 / π * 2 * log (log 4) := by positivity
  linarith

end Q4

/-- Former LEAF, PROVED by S128: Pomerance 2011 Theorem 1, odd case, the modulus q = 3, one case of
`PVCases1122.odd_small`. The odd character mod 3 is the Legendre symbol, with initial segment sums 0 and 1. Class EASY. -/
theorem odd_small_q3 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 3) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  subst hqk
  exact (Q3.interval_norm_le χ hodd M N).trans Q3.rhs_ge

/-- Former LEAF, PROVED by S128: Pomerance 2011 Theorem 1, odd case, the modulus q = 4, one case of
`PVCases1122.odd_small`. The odd character mod 4 takes 1, 0, -1, 0, with initial segment sums 0 and 1. Class EASY. -/
theorem odd_small_q4 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 4) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  subst hqk
  exact (Q4.interval_norm_le χ hodd M N).trans Q4.rhs_ge

namespace Q5

lemma odd_m1 (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) : χ (-1) = -1 := by
  have h2 : χ (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hodd
  · exact eq_neg_of_add_eq_zero_left h

lemma chi_vals (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    χ (n : ZMod 5) = if n % 5 = 0 then 0 else if n % 5 = 1 then 1 else if n % 5 = 2 then χ 2
      else if n % 5 = 3 then -χ 2 else -1 := by
  have hm1 := odd_m1 χ hodd
  have hn : (n : ZMod 5) = ((n % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod n 5).symm
  rw [hn]
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 5
  · have hu : ¬ IsUnit ((0 : ℕ) : ZMod 5) := by decide
    simp only [if_true]; exact MulChar.map_nonunit χ hu
  · simp
  · simp
  · have : ((3 : ℕ) : ZMod 5) = -1 * 2 := by decide
    simp only [this, map_mul, hm1]; norm_num
  · have : ((4 : ℕ) : ZMod 5) = -1 := by decide
    simp only [this, hm1]; norm_num

lemma partial_eq (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ∑ m ∈ range n, χ (m : ZMod 5) = if n % 5 = 0 ∨ n % 5 = 1 then 0 else if n % 5 = 3 then 1 + χ 2
      else 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, chi_vals χ hodd k]
    have hr : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hk : (k + 1) % 5 = (k % 5 + 1) % 5 := by omega
    rw [hk]
    interval_cases h : k % 5 <;> simp <;> ring

lemma chi2_sq (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) : χ 2 ^ 2 = -1 := by
  rw [← map_pow, show (2 : ZMod 5) ^ 2 = -1 by decide, odd_m1 χ hodd]

lemma norm_one_add (z : ℂ) (hz : z ^ 2 = -1) : ‖1 + z‖ ≤ 1.415 := by
  have hre : z.re ^ 2 - z.im ^ 2 = -1 ∧ 2 * z.re * z.im = 0 := by
    have h1 := congrArg Complex.re hz; have h2 := congrArg Complex.im hz
    simp [pow_two] at h1 h2
    constructor <;> nlinarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hre.2 with h | h
    · linarith
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have him : z.im ^ 2 = 1 := by rw [hre0] at hre; linarith [hre.1]
  have hn : ‖1 + z‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hre0]; nlinarith
  have h0 : 0 ≤ ‖1 + z‖ := norm_nonneg _
  nlinarith

lemma partial_norm_le (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ‖∑ m ∈ range n, χ (m : ZMod 5)‖ ≤ 1.415 := by
  rw [partial_eq χ hodd n]
  split_ifs
  · norm_num
  · exact norm_one_add _ (chi2_sq χ hodd)
  · norm_num

lemma interval_norm_le (χ : DirichletCharacter ℂ 5) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod 5)‖ ≤ 2.83 := by
  by_cases hMN : M ≤ N + 1
  · have hI : Icc M N = Ico M (N + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, sum_Ico_eq_sub _ hMN]
    calc _ ≤ ‖∑ m ∈ range (N+1), χ (m : ZMod 5)‖ + ‖∑ m ∈ range M, χ (m : ZMod 5)‖ := norm_sub_le _ _
      _ ≤ 1.415 + 1.415 := add_le_add (partial_norm_le χ hodd _) (partial_norm_le χ hodd _)
      _ = 2.83 := by norm_num
  · have : Icc M N = ∅ := by ext x; simp only [mem_Icc]; simp; omega
    rw [this, sum_empty, norm_zero]; norm_num

lemma rhs_ge :
    (2.83:ℝ) ≤ 1 / (2 * π) * sqrt (5:ℕ) * log (5:ℕ) + 1 / π * sqrt (5:ℕ) * log (log (5:ℕ)) + sqrt (5:ℕ) := by
  push_cast
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hl5 : (1.4 : ℝ) ≤ log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := Real.exp_one_lt_d9
    have hm := Real.add_one_le_exp (-0.4 : ℝ)
    have hprod : Real.exp 0.4 * Real.exp (-0.4) = 1 := by rw [← Real.exp_add]; norm_num
    have hsplit : Real.exp 1.4 = Real.exp 1 * Real.exp 0.4 := by rw [← Real.exp_add]; norm_num
    have hp : 0 < Real.exp 0.4 := Real.exp_pos _
    have h04 : Real.exp 0.4 ≤ 1 / 0.6 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    rw [hsplit]
    have h1 : 0 < Real.exp 1 := Real.exp_pos _
    nlinarith
  have hll : (0.2857 : ℝ) ≤ log (log 5) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < log 5 by linarith)
    have : (log 5)⁻¹ ≤ (1.4:ℝ)⁻¹ := inv_anti₀ (by norm_num) hl5
    norm_num at *; linarith
  have hs : (2.236 : ℝ) ≤ sqrt 5 := Real.le_sqrt_of_sq_le (by norm_num)
  have h3 : 1 / (2 * π) ≥ 1 / 6.3 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have h3' : 1 / π ≥ 1 / 3.15 := by
    rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hA : 1 / (2 * π) * sqrt 5 * log 5 ≥ 1 / 6.3 * 2.236 * 1.4 := by
    have : 1 / (2 * π) * sqrt 5 ≥ 1 / 6.3 * 2.236 :=
      mul_le_mul h3 hs (by norm_num) (by positivity)
    nlinarith
  have hB : 1 / π * sqrt 5 * log (log 5) ≥ 1 / 3.15 * 2.236 * 0.2857 := by
    have : 1 / π * sqrt 5 ≥ 1 / 3.15 * 2.236 :=
      mul_le_mul h3' hs (by norm_num) (by positivity)
    nlinarith
  nlinarith

end Q5

/-- Former LEAF, PROVED by S128: Pomerance 2011 Theorem 1, odd case, the modulus q = 5, one case of
`PVCases1122.odd_small`. An odd character mod 5 has chi 2 equal to i or -i, so its initial segment sums are 0, 1, 1 + chi 2 and 1, of norm at most sqrt 2. Class EASY. -/
theorem odd_small_q5 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 5) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  subst hqk
  exact (Q5.interval_norm_le χ hodd M N).trans Q5.rhs_ge

namespace Q6

lemma chi_vals (χ : DirichletCharacter ℂ 6) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    χ (n : ZMod 6) = if n % 6 = 1 then 1 else if n % 6 = 5 then -1 else 0 := by
  have hm1 : χ (-1) = -1 := by
    have h2 : χ (-1) ^ 2 = 1 := by
      rw [← map_pow]; norm_num
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [h2]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hodd
    · exact eq_neg_of_add_eq_zero_left h
  have hn : (n : ZMod 6) = ((n % 6 : ℕ) : ZMod 6) := (ZMod.natCast_mod n 6).symm
  rw [hn]
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 6
  · have hu : ¬ IsUnit ((0 : ℕ) : ZMod 6) := by decide
    rw [if_neg (by norm_num), if_neg (by norm_num)]; exact MulChar.map_nonunit χ hu
  · simp
  · have hu : ¬ IsUnit ((2 : ℕ) : ZMod 6) := by decide
    rw [if_neg (by norm_num), if_neg (by norm_num)]; exact MulChar.map_nonunit χ hu
  · have hu : ¬ IsUnit ((3 : ℕ) : ZMod 6) := by decide
    rw [if_neg (by norm_num), if_neg (by norm_num)]; exact MulChar.map_nonunit χ hu
  · have hu : ¬ IsUnit ((4 : ℕ) : ZMod 6) := by decide
    rw [if_neg (by norm_num), if_neg (by norm_num)]; exact MulChar.map_nonunit χ hu
  · have : ((5 : ℕ) : ZMod 6) = -1 := by decide
    simp only [this, hm1]; norm_num

lemma partial_eq (χ : DirichletCharacter ℂ 6) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ∑ m ∈ range n, χ (m : ZMod 6) = if n % 6 = 0 ∨ n % 6 = 1 then 0 else 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, chi_vals χ hodd k]
    have hr : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have hk : (k + 1) % 6 = (k % 6 + 1) % 6 := by omega
    rw [hk]
    interval_cases h : k % 6 <;> norm_num

lemma partial_norm_le (χ : DirichletCharacter ℂ 6) (hodd : χ (-1) ≠ 1) (n : ℕ) :
    ‖∑ m ∈ range n, χ (m : ZMod 6)‖ ≤ 1 := by
  rw [partial_eq χ hodd n]; split_ifs <;> simp only [norm_one, norm_zero, zero_le_one, le_refl]

lemma interval_norm_le (χ : DirichletCharacter ℂ 6) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod 6)‖ ≤ 2 := by
  by_cases hMN : M ≤ N + 1
  · have hI : Icc M N = Ico M (N + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI, sum_Ico_eq_sub _ hMN]
    calc _ ≤ ‖∑ m ∈ range (N+1), χ (m : ZMod 6)‖ + ‖∑ m ∈ range M, χ (m : ZMod 6)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (partial_norm_le χ hodd _) (partial_norm_le χ hodd _)
      _ = 2 := by norm_num
  · have : Icc M N = ∅ := by ext x; simp only [mem_Icc]; simp; omega
    rw [this, sum_empty, norm_zero]; norm_num

lemma rhs_ge :
    (2:ℝ) ≤ 1 / (2 * π) * sqrt (6:ℕ) * log (6:ℕ) + 1 / π * sqrt (6:ℕ) * log (log (6:ℕ)) + sqrt (6:ℕ) := by
  push_cast
  have hpi0 : 0 < π := Real.pi_pos
  have hl6 : (1 : ℝ) ≤ log 6 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hll : 0 ≤ log (log 6) := Real.log_nonneg hl6
  have hs : (2 : ℝ) ≤ sqrt 6 := Real.le_sqrt_of_sq_le (by norm_num)
  have h1 : 0 ≤ 1 / (2 * π) * sqrt 6 * log 6 := by
    have : (0:ℝ) ≤ log 6 := by linarith
    positivity
  have h2 : 0 ≤ 1 / π * sqrt 6 * log (log 6) := by positivity
  linarith

end Q6

/-- Former LEAF, PROVED by S128: Pomerance 2011 Theorem 1, odd case, the modulus q = 6, one case of
`PVCases1122.odd_small`. There is no primitive character mod 6, since every character mod 6 is induced from one mod 3, so the hypotheses are contradictory. Class EASY. -/
theorem odd_small_q6 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqk : q = 6) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  subst hqk
  exact (Q6.interval_norm_le χ hodd M N).trans Q6.rhs_ge

end LeanLab.HelfgottMajor.PVOddSmallS128
