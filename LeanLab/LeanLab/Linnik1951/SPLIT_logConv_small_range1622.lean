/-
Split unit of LeanLab/Linnik1951/SPLIT_log_convolution_estimate1622. This file adds leaves
for the finite range leaf logConv_small_range1622 of that file, plus the assembly theorem
logConv_small_range1622_split. No statement of the parent file is changed; no definition is
added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write L for log n, A(n) for n / L^2 and W(n) for 1 / sqrt(log n). The range is
2 <= n <= 1000, so the whole claim is elementary: the two constants log 2 and log 1000
control it. Every summand of logConvolution1622 n is at most 1 / (log 2)^2 and at least
1 / L^2, because 2 <= m <= n - 2 puts both log m and log (n - m) between log 2 and L. So the
sum lies between (n - 3) / L^2 and (n - 3) / (log 2)^2, and the index set has n - 3 elements
by Nat.card_Icc. Subtracting A(n) leaves the sum inside
[-3 / L^2, n / (log 2)^2 - A(n)], and the two scale leaves compare those two numbers with
500 * A(n) * W(n) using log n <= 7 and log 2 >= 0.69 over the finite range. n equal to 2 and
n equal to 3 have an empty index set and are carried by one leaf with the same constant 500.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. The empty end of the range: for 2 <= n <= 3 the index set 2 <= m <= n - 2 is empty,
so the convolution is zero and the claim holds with constant 500. This is the step that keeps
n equal to 2 and n equal to 3 out of the index count n - 3, which needs n at least 4. -/
theorem logConv_small_initial1622 (n : ℕ) (hn : 2 ≤ n) (hn3 : n ≤ 3) :
    |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
      500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  have h_conv : logConvolution1622 n = 0 := by
    rw [logConvolution1622]
    have h_empty : Finset.Icc 2 (n - 2) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [h_empty, Finset.sum_empty]
  rw [h_conv, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
  have hpos : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≥ 0 := by positivity
  have h2 : 1 ≤ 500 * (1 / Real.sqrt (Real.log (n : ℝ))) := by
    have hn2_3 : n = 2 ∨ n = 3 := by omega
    rcases hn2_3 with rfl | rfl
    · have hlog2 : Real.log 2 ≤ 1 := Real.log_le_sub_one_of_pos zero_lt_two |>.trans (by norm_num)
      have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hsqrt2 : Real.sqrt (Real.log 2) ≤ 1 := by
        nlinarith [Real.sqrt_pos.mpr hlog2pos, (@Real.sqrt_le_iff (Real.log 2) 1).mpr ⟨by norm_num, by linarith⟩]
      have hsqrt2pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2pos
      calc (1 : ℝ)
        _ ≤ 500 * 1 := by norm_num
        _ ≤ 500 * (1 / Real.sqrt (Real.log 2)) := mul_le_mul_of_nonneg_left (one_le_one_div hsqrt2pos hsqrt2) (by norm_num)
    · have hlog3 : Real.log 3 ≤ 4 := Real.log_le_sub_one_of_pos (by norm_num) |>.trans (by norm_num)
      have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hsqrt3 : Real.sqrt (Real.log 3) ≤ 2 := by
        nlinarith [Real.sqrt_pos.mpr hlog3pos, (@Real.sqrt_le_iff (Real.log 3) 2).mpr ⟨by norm_num, by linarith⟩]
      have hsqrt3pos : 0 < Real.sqrt (Real.log 3) := Real.sqrt_pos.mpr hlog3pos
      calc (1 : ℝ)
        _ ≤ 500 * (1 / 2) := by norm_num
        _ ≤ 500 * (1 / Real.sqrt (Real.log 3)) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hsqrt3pos hsqrt3) (by norm_num)
  calc
    (n : ℝ) / Real.log n ^ 2 = 1 * ((n : ℝ) / Real.log n ^ 2) := by ring
    _ ≤ (500 * (1 / Real.sqrt (Real.log (n : ℝ)))) * ((n : ℝ) / Real.log n ^ 2) := mul_le_mul_of_nonneg_right h2 hpos
    _ = 500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by ring

/-- LEAF. Termwise upper bound: for an index m of the convolution sum,
1 / (log m * log (n - m)) is at most 1 / (log 2)^2, because the two indices are at least 2 and
give both logarithms at least log 2 while their product stays positive. This is the step that
turns the index count into an upper bound for the whole sum. -/
theorem logConv_small_term_upper1622 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / Real.log 2 ^ 2 := by
  have hm1 : 2 ≤ m := Finset.mem_Icc.mp hm |>.1
  have hm2 : m ≤ n - 2 := Finset.mem_Icc.mp hm |>.2
  have hnm : 2 ≤ n - m := by omega
  have hlog1 : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log zero_lt_two (by exact_mod_cast hm1)
  have hlog2 : Real.log 2 ≤ Real.log ((n - m : ℕ) : ℝ) := Real.log_le_log zero_lt_two (by exact_mod_cast hnm)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul : Real.log 2 * Real.log 2 ≤ Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) :=
    mul_le_mul hlog1 hlog2 hlog2pos.le (hlog2pos.le.trans hlog1)
  rw [sq]
  exact one_div_le_one_div_of_le (mul_pos hlog2pos hlog2pos) hmul

/-- LEAF. Termwise lower bound: for 2 <= n and an index m of the convolution sum,
1 / (log m * log (n - m)) is at least 1 / (log n)^2, because both indices are at most n and
make both logarithms positive and at most log n. This is the step that turns the index count
into a lower bound for the whole sum. -/
theorem logConv_small_term_lower1622 (n : ℕ) (hn : 2 ≤ n) (m : ℕ)
    (hm : m ∈ Finset.Icc 2 (n - 2)) :
    1 / Real.log (n : ℝ) ^ 2 ≤ 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
  have hm1 : 2 ≤ m := Finset.mem_Icc.mp hm |>.1
  have hm2 : m ≤ n - 2 := Finset.mem_Icc.mp hm |>.2
  have hnm1 : 2 ≤ n - m := by omega
  have hmn : m ≤ n := by omega
  have hnmn : n - m ≤ n := by omega
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm1)
  have hlognm : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hnm1)
  have hlog1 : Real.log (m : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by exact_mod_cast (zero_lt_two.trans_le hm1)) (by exact_mod_cast hmn)
  have hlog2 : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by exact_mod_cast (zero_lt_two.trans_le hnm1)) (by exact_mod_cast hnmn)
  have hmul : Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) :=
    mul_le_mul hlog1 hlog2 hlognm.le (hlogm.le.trans hlog1)
  rw [sq]
  exact one_div_le_one_div_of_le (mul_pos hlogm hlognm) hmul

/-- LEAF. Scale comparison, upper side: for 4 <= n <= 1000 the crude upper bound n / (log 2)^2
of the convolution overshoots the main term n / (log n)^2 by at most 500 times the main term
times 1 / sqrt (log n). Only the two constants log n <= 7 and log 2 >= 0.69 are used, and no
property of the convolution. -/
theorem logConv_small_scale_upper1622 (n : ℕ) (hn : 4 ≤ n) (hn1000 : n ≤ 1000) :
    (n : ℝ) * (1 / Real.log 2 ^ 2) - (n : ℝ) / Real.log n ^ 2 ≤
      500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog2_ge : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two

  have hlogn_le : Real.log (n : ℝ) ≤ 7 := by
    have h1 : (n:ℝ) ≤ Real.exp 7 := by
      calc (n : ℝ)
        _ ≤ 1000 := by exact_mod_cast hn1000
        _ ≤ 2.7 ^ 7 := by norm_num
        _ ≤ Real.exp 1 ^ 7 := by
          apply pow_le_pow_left₀ (by norm_num)
          linarith [Real.exp_one_gt_d9]
        _ = Real.exp 7 := by rw [← Real.exp_nat_mul] ; ring_nf
    have h2 : Real.log (n:ℝ) ≤ Real.log (Real.exp 7) := Real.log_le_log hn_pos h1
    rwa [Real.log_exp] at h2

  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsqrt_logn : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogn_pos

  have h_frac1 : (Real.log (n : ℝ) / Real.log 2) ^ 2 ≤ (7 / 0.69) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_pos (div_pos hlogn_pos hlog2pos), abs_of_pos (by norm_num)]
    apply div_le_div₀ (by norm_num) hlogn_le (by norm_num) hlog2_ge

  have h_frac1_val : (7 / 0.69 : ℝ) ^ 2 ≤ 104 := by norm_num

  have h_frac2 : 185 ≤ 500 / Real.sqrt (Real.log (n : ℝ)) := by
    have hsqrt7 : Real.sqrt (Real.log (n : ℝ)) ≤ 2.7 := by
      calc Real.sqrt (Real.log (n : ℝ))
        _ ≤ Real.sqrt 7 := Real.sqrt_le_sqrt hlogn_le
        _ ≤ 2.7 := by apply (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
    have hinv : 1 / 2.7 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) := one_div_le_one_div_of_le hsqrt_logn hsqrt7
    have hmul : 500 * (1 / 2.7) ≤ 500 * (1 / Real.sqrt (Real.log (n : ℝ))) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    have hval : (185 : ℝ) ≤ 500 * (1 / 2.7) := by norm_num
    calc (185 : ℝ)
      _ ≤ 500 * (1 / 2.7) := hval
      _ ≤ 500 * (1 / Real.sqrt (Real.log (n : ℝ))) := hmul
      _ = 500 / Real.sqrt (Real.log (n : ℝ)) := by ring

  have h_main : (Real.log (n : ℝ) / Real.log 2) ^ 2 - 1 ≤ 500 / Real.sqrt (Real.log (n : ℝ)) := by
    calc (Real.log (n : ℝ) / Real.log 2) ^ 2 - 1
      _ ≤ (7 / 0.69 : ℝ) ^ 2 - 1 := sub_le_sub_right h_frac1 1
      _ ≤ 104 - 1 := sub_le_sub_right h_frac1_val 1
      _ = 103 := by norm_num
      _ ≤ 185 := by norm_num
      _ ≤ 500 / Real.sqrt (Real.log (n : ℝ)) := h_frac2

  have h_mul : ((n : ℝ) / Real.log (n : ℝ) ^ 2) * ((Real.log (n : ℝ) / Real.log 2) ^ 2 - 1) ≤
      ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (500 / Real.sqrt (Real.log (n : ℝ))) := by
    apply mul_le_mul_of_nonneg_left h_main
    positivity

  have h_eq : (n : ℝ) * (1 / Real.log 2 ^ 2) - (n : ℝ) / Real.log (n : ℝ) ^ 2 =
      ((n : ℝ) / Real.log (n : ℝ) ^ 2) * ((Real.log (n : ℝ) / Real.log 2) ^ 2 - 1) := by
    have hln : Real.log (n : ℝ) ≠ 0 := ne_of_gt hlogn_pos
    have h1 : ((Real.log (n : ℝ) / Real.log 2) ^ 2 - 1) = (Real.log (n : ℝ) ^ 2 / Real.log 2 ^ 2) - 1 := by rw [div_pow]
    rw [h1]
    calc (n : ℝ) * (1 / Real.log 2 ^ 2) - (n : ℝ) / Real.log (n : ℝ) ^ 2
      _ = (n : ℝ) / Real.log 2 ^ 2 - (n : ℝ) / Real.log (n : ℝ) ^ 2 := by ring
      _ = ((n : ℝ) * Real.log (n : ℝ) ^ 2) / (Real.log 2 ^ 2 * Real.log (n : ℝ) ^ 2) - (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
        congr 1
        have : (n : ℝ) / Real.log 2 ^ 2 = ((n : ℝ) * Real.log (n : ℝ) ^ 2) / (Real.log 2 ^ 2 * Real.log (n : ℝ) ^ 2) := by
          have h3 : (n : ℝ) / Real.log 2 ^ 2 = ((n : ℝ) / Real.log 2 ^ 2) * (Real.log (n : ℝ) ^ 2 / Real.log (n : ℝ) ^ 2) := by
            rw [div_self (pow_ne_zero 2 hln), mul_one]
          rw [h3]
          ring
        exact this
      _ = ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (Real.log (n : ℝ) ^ 2 / Real.log 2 ^ 2) - ((n : ℝ) / Real.log (n : ℝ) ^ 2) := by ring
      _ = ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (Real.log (n : ℝ) ^ 2 / Real.log 2 ^ 2 - 1) := by ring

  calc (n : ℝ) * (1 / Real.log 2 ^ 2) - (n : ℝ) / Real.log n ^ 2
    _ = ((n : ℝ) / Real.log (n : ℝ) ^ 2) * ((Real.log (n : ℝ) / Real.log 2) ^ 2 - 1) := h_eq
    _ ≤ ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (500 / Real.sqrt (Real.log (n : ℝ))) := h_mul
    _ = 500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by ring

/-- LEAF. Scale comparison, lower side: for 4 <= n <= 1000 the loss 3 / (log n)^2 by which the
index count n - 3 falls short of n is at most 500 times the main term times
1 / sqrt (log n). This is the step that closes the absolute value from below, and it uses no
property of the convolution. -/
theorem logConv_small_scale_lower1622 (n : ℕ) (hn : 4 ≤ n) (hn1000 : n ≤ 1000) :
    -(500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n))) ≤
      -(3 / Real.log n ^ 2) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsqrt_logn : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogn_pos

  rw [neg_le_neg_iff]
  have h_frac1 : 3 ≤ 500 * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
    have h1 : 4 ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn_le : Real.log (n : ℝ) ≤ 7 := by
      have h1 : (n:ℝ) ≤ Real.exp 7 := by
        calc (n : ℝ)
          _ ≤ 1000 := by exact_mod_cast hn1000
          _ ≤ 2.7 ^ 7 := by norm_num
          _ ≤ Real.exp 1 ^ 7 := by
            apply pow_le_pow_left₀ (by norm_num)
            linarith [Real.exp_one_gt_d9]
          _ = Real.exp 7 := by rw [← Real.exp_nat_mul] ; ring_nf
      have h2 : Real.log (n:ℝ) ≤ Real.log (Real.exp 7) := Real.log_le_log hn_pos h1
      rwa [Real.log_exp] at h2
    have hsqrt7 : Real.sqrt (Real.log (n : ℝ)) ≤ 2.7 := by
      calc Real.sqrt (Real.log (n : ℝ))
        _ ≤ Real.sqrt 7 := Real.sqrt_le_sqrt hlogn_le
        _ ≤ 2.7 := by apply (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
    have hinv : 1 / 2.7 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) := one_div_le_one_div_of_le hsqrt_logn hsqrt7
    have hval : (3 : ℝ) ≤ 500 * 4 * (1 / 2.7) := by norm_num
    calc (3 : ℝ)
      _ ≤ 500 * 4 * (1 / 2.7) := hval
      _ ≤ 500 * (n : ℝ) * (1 / 2.7) := by
        apply mul_le_mul_of_nonneg_right
        apply mul_le_mul_of_nonneg_left h1 (by norm_num)
        norm_num
      _ ≤ 500 * (n : ℝ) * (1 / Real.sqrt (Real.log (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left hinv
        positivity
      _ = 500 * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by ring

  calc 3 / Real.log (n : ℝ) ^ 2
    _ = 3 * (1 / Real.log (n : ℝ) ^ 2) := by ring
    _ ≤ (500 * (n : ℝ) / Real.sqrt (Real.log (n : ℝ))) * (1 / Real.log (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right h_frac1 (by positivity)
    _ = 500 * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by ring

/-- The target statement of the parent file, assembled from the five leaves above with no
remaining gap: constant 500, the empty end 2 <= n <= 3, and for 4 <= n <= 1000 the sum
sandwiched between (n - 3) / (log n)^2 and (n - 3) / (log 2)^2, which the two scale leaves
compare with 500 times the main term times 1 / sqrt (log n). -/
theorem logConv_small_range1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → n ≤ 1000 →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  refine ⟨500, by norm_num, ?_⟩
  intro n hn hn1000
  rcases lt_or_ge 3 n with h3lt | hn3
  · have hn4 : 4 ≤ n := by omega
    have hcpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc2 : 0 < 1 / Real.log 2 ^ 2 :=
      div_pos one_pos (pow_pos hcpos 2)
    have hcard : ((Finset.Icc 2 (n - 2)).card : ℝ) = (n : ℝ) - 3 := by
      have h1 : (Finset.Icc 2 (n - 2)).card = n - 3 := by
        rw [Nat.card_Icc]
        omega
      rw [h1, Nat.cast_sub (show 3 ≤ n by omega)]
      norm_num
    have hupper_sum : logConvolution1622 n ≤
        (n : ℝ) * (1 / Real.log 2 ^ 2) := by
      have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
          1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / Real.log 2 ^ 2 :=
        fun m hm => logConv_small_term_upper1622 n m hm
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at h
      have hcast : ((Finset.Icc 2 (n - 2)).card : ℝ) ≤ (n : ℝ) := by
        rw [hcard]
        have h3n : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
        linarith
      have hstep := mul_le_mul_of_nonneg_right hcast (le_of_lt hc2)
      have hfold : logConvolution1622 n ≤
          ((Finset.Icc 2 (n - 2)).card : ℝ) * (1 / Real.log 2 ^ 2) := by
        simpa [logConvolution1622] using h
      linarith [hfold, hstep]
    have hlower_sum : ((n : ℝ) - 3) * (1 / Real.log (n : ℝ) ^ 2) ≤
        logConvolution1622 n := by
      have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
          1 / Real.log (n : ℝ) ^ 2 ≤
            1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) :=
        fun m hm => logConv_small_term_lower1622 n hn m hm
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul] at h
      rw [hcard] at h
      simpa [logConvolution1622] using h
    have hkey : ((n : ℝ) - 3) * (1 / Real.log (n : ℝ) ^ 2) =
        (n : ℝ) / Real.log (n : ℝ) ^ 2 - 3 / Real.log (n : ℝ) ^ 2 := by
      ring
    have hylow : -(3 / Real.log (n : ℝ) ^ 2) ≤
        logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
      linarith [hlower_sum, hkey]
    have hyhigh : logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤
        500 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
          (1 / Real.sqrt (Real.log (n : ℝ))) := by
      have hscale := logConv_small_scale_upper1622 n hn4 hn1000
      linarith [hupper_sum, hscale]
    have hlow := logConv_small_scale_lower1622 n hn4 hn1000
    rw [abs_le]
    constructor
    · linarith [hylow, hlow]
    · linarith [hyhigh]
  · exact logConv_small_initial1622 n hn hn3

end LeanLab.Linnik1951
