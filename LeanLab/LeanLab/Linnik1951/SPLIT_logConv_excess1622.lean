/-
Split unit of Linnik1951/SPLIT_log_convolution_estimate1622.
Sub-leaves for the elementary excess estimate logConv_excess1622, plus the assembly
theorem logConv_excess1622_split. No statement of the parent file is changed and no
definition is added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write u = log m, v = log (n - m) and L = log n, so that the summand is
1 / (u * v) and the shift is 2L - u - v, the logarithm of n^2 / (m (n - m)). The
summand is at most 1/L^2 + 2 (2L - u - v)/L^3 wherever the shift is at most L/2,
and the shift has total at most a constant times n over the whole range. The two
ends of the range, where the shift is large, hold only about the square root of n
terms of size at most a constant over L, which is again at most a constant times
n / L^3. Adding the three pieces gives the excess with one constant.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. Positivity of the shift: for every index of the convolution the logarithm
of m (n - m) is at most twice the logarithm of n, that is the shift 2 log n minus
log m minus log (n - m) is nonnegative. This is the step that lets the shift be
weight summed over the range without a sign condition. -/
theorem logConv_shift_nonneg1622 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    0 ≤ 2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)) := by
  have hm1 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
  have hm2 : m ≤ n - 2 := (Finset.mem_Icc.mp hm).2
  have hm_lt_n : m < n := by omega
  have h_pos_m : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h_pos_nm : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast (show 0 < n - m by omega)
  have h_pos_n : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [sub_nonneg]
  have h_log_add : Real.log m + Real.log (n - m : ℕ) = Real.log (m * (n - m : ℕ)) := by
    exact (Real.log_mul (ne_of_gt h_pos_m) (ne_of_gt h_pos_nm)).symm
  rw [h_log_add]
  have h_log_pow : 2 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 2) := by
    have h1 : 2 * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) := by ring
    rw [h1]
    have h2 : (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) := by ring
    rw [h2]
    exact (Real.log_mul (ne_of_gt h_pos_n) (ne_of_gt h_pos_n)).symm
  rw [h_log_pow]
  apply Real.log_le_log
  · positivity
  · have : (m : ℝ) * (n - m : ℕ) = (m * (n - m) : ℕ) := by push_cast; rfl
    rw [this]
    push_cast
    have h_ineq : m * (n - m) ≤ n ^ 2 := by
      calc m * (n - m) ≤ n * n := by
            have h1 : m ≤ n := by omega
            have h2 : n - m ≤ n := by omega
            exact Nat.mul_le_mul h1 h2
        _ = n ^ 2 := by ring
    exact_mod_cast h_ineq

/-- LEAF. Total of the shift: summed over the whole range 2 <= m <= n - 2 the shift
2 log n - log m - log (n - m) is at most a constant times n. The shift is the
logarithm of n^2 / (m (n - m)), and the sum of the logarithms is read off a lower
bound for the logarithm of the factorial (n - 2)!, so the constant is absolute. -/
theorem logConv_shift_sum1622 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1000 ≤ n →
      (∑ m ∈ Finset.Icc 2 (n - 2),
          (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ K * (n : ℝ) := by
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  have hsym : (∑ m ∈ Finset.Icc 2 (n - 2), Real.log (n - m : ℕ)) =
      ∑ m ∈ Finset.Icc 2 (n - 2), Real.log m := by
    refine Finset.sum_bij (fun m _ => n - m) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      refine ⟨n - b, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hb ⊢
        omega
      · simp only [Finset.mem_Icc] at hb
        omega
    · intro m hm
      rfl
  have hset : Finset.Ioc 0 n =
      insert 1 (insert (n - 1) (insert n (Finset.Icc 2 (n - 2)))) := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h1 : (1 : ℕ) ∉ insert (n - 1) (insert n (Finset.Icc 2 (n - 2))) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h2 : n - 1 ∉ insert n (Finset.Icc 2 (n - 2)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have h3 : n ∉ Finset.Icc 2 (n - 2) := by
    simp only [Finset.mem_Icc]; omega
  have hfull := Real.le_sum_log_nat n
  rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3] at hfull
  simp only [Nat.cast_one, Real.log_one, zero_add] at hfull
  have hlog : Real.log (n - 1 : ℕ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < n - 1 by omega)) (by exact_mod_cast Nat.sub_le n 1)
  have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hcard : ((Finset.Icc 2 (n - 2)).card : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.card_Icc]
    have h : n - 2 + 1 - 2 = n - 3 := by omega
    rw [h, Nat.cast_sub (by omega)]
    norm_num
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, hsym, hcard]
  nlinarith


/-- LEAF. Termwise majorant: for positive u, v and L with u + v at most 2 L and with
the shift 2 L - u - v at most L / 2, the reciprocal product 1 / (u v) is at most
1 / L^2 plus twice the shift over L^3. This is the elementary inequality
4 u v <= (u + v)^2 together with a quadratic estimate for the reciprocal of
1 - shift / L. -/
theorem logConv_term_majorant1622 (u v L : ℝ) (hu : 0 < u) (hv : 0 < v) (hL : 0 < L)
    (hsum : u + v ≤ 2 * L) (hshift : 2 * L - (u + v) ≤ L / 2) :
    1 / (u * v) ≤ 1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v)) := by
  sorry

/-- The exact universal majorant annotation is false. This audits the split
annotation of page 161 after equation 6.3, rather than the paper estimate. -/
theorem not_logConv_term_majorant1622 :
    ¬ (∀ (u v L : ℝ), (0 < u) → (0 < v) → (0 < L) →
      (u + v ≤ 2 * L) → (2 * L - (u + v) ≤ L / 2) →
      1 / (u * v) ≤ 1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v))) := by
  intro h
  have hbad := h (1 / 2) (3 / 2) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad

/-- The valid termwise estimate includes the upper bounds on both logarithms.
These hold for convolution indices on page 161 after equation 6.3. -/
theorem logConv_term_majorant_bounded474 (u v L : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hL : 0 < L) (huL : u ≤ L) (hvL : v ≤ L)
    (hshift : 2 * L - (u + v) ≤ L / 2) :
    1 / (u * v) ≤ 1 / L ^ 2 + (2 / L ^ 3) * (2 * L - (u + v)) := by
  have hprod : L ^ 2 - L * (2 * L - (u + v)) ≤ u * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huL) (sub_nonneg.mpr hvL)]
  have hs : 0 ≤ 2 * L - (u + v) := by linarith
  have ht : 0 ≤ (2 * L - (u + v)) * (L - 2 * (2 * L - (u + v))) :=
    mul_nonneg hs (by linarith)
  have hmult := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ L + 2 * (2 * L - (u + v)) by positivity)
  have hn : L ^ 3 ≤ (L + 2 * (2 * L - (u + v))) * (u * v) := by
    nlinarith [mul_nonneg hL.le ht]
  calc
    _ ≤ (L + 2 * (2 * L - (u + v))) / L ^ 3 := by
      apply (div_le_div_iff₀ (mul_pos hu hv) (pow_pos hL 3)).mpr
      simpa only [one_mul] using hn
    _ = _ := by field_simp [ne_of_gt hL]

/-- LEAF. Small shift in the middle of the range: for n at least 10^3 and for an
index m with 2 sqrt n <= m <= n - 2 sqrt n the product m (n - m) is at least
n^(3/2), so the shift 2 log n - log m - log (n - m) is at most half of log n. This
is the step that makes the termwise majorant applicable away from the two ends. -/
theorem logConv_middle_shift1622 (n m : ℕ) (hn : 1000 ≤ n)
    (hm1 : 2 * Nat.sqrt n ≤ m) (hm2 : m ≤ n - 2 * Nat.sqrt n) :
    2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)) ≤ Real.log (n : ℝ) / 2 := by
  have hs : 31 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hs2 := Nat.sqrt_le n
  have hns := Nat.sqrt_le_add n
  have hmn : m ≤ n := by omega
  have hmpos : 0 < m := by omega
  have hnmp : 0 < n - m := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hsp : (0 : ℝ) < (Nat.sqrt n + 1 : ℕ) := by positivity
  have hproduct : (n : ℝ) * (Nat.sqrt n + 1 : ℕ) ≤
      (m : ℝ) * (n - m : ℕ) := by
    have ha : (2 * Nat.sqrt n : ℕ) ≤ n - m := by omega
    have hb : (0 : ℝ) ≤ ((m : ℝ) - 2 * (Nat.sqrt n : ℝ)) *
        ((n - m : ℕ) - 2 * (Nat.sqrt n : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hm1))
        (sub_nonneg.mpr (by exact_mod_cast ha))
    have hc : (n - m : ℕ) + (m : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hmn
    have hd : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by simpa only [pow_two] using (show (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) by exact_mod_cast hs2)
    have he : (31 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hs
    have hf := mul_nonneg (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) - 5 by linarith)
      (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) ^ 2 by positivity)
    have hg := mul_nonneg (show (0 : ℝ) ≤ (Nat.sqrt n : ℝ) - 1 by linarith)
      (show (0 : ℝ) ≤ (n : ℝ) - (Nat.sqrt n : ℝ) ^ 2 by linarith)
    push_cast
    nlinarith
  have hns' : (n : ℝ) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast (show n ≤ (Nat.sqrt n + 1) ^ 2 by nlinarith)
  have hlogn := Real.log_le_log hnpos hns'
  rw [Real.log_pow] at hlogn
  norm_num only [Nat.cast_ofNat] at hlogn
  have hlogprod := Real.log_le_log (mul_pos hnpos hsp) hproduct
  rw [Real.log_mul (ne_of_gt hnpos) (ne_of_gt hsp),
    Real.log_mul (by positivity) (by positivity)] at hlogprod
  linarith


/-- LEAF. Mass of the two ends: summed over the indices m of the range which fail
2 sqrt n <= m <= n - 2 sqrt n, that is over the two ends of the range, the summand
1 / (log m log (n - m)) is at most a constant times n / (log n)^3. Each such index
has both logarithms at least half of log n, and there are at most 4 sqrt n of them. -/
theorem logConv_end_mass1622 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1000 ≤ n →
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
  classical
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨128 / Real.log 2, by positivity, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hpoint : ∀ m ∈ Finset.Icc 2 (n - 2),
      1 / (Real.log m * Real.log (n - m : ℕ)) ≤
        2 / (Real.log 2 * Real.log (n : ℝ)) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hnm : 2 ≤ n - m := by omega
    have hu : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hm1)
    have hv : Real.log 2 ≤ Real.log (n - m : ℕ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hnm)
    have hsum : Real.log (n : ℝ) ≤ 2 * max (Real.log m) (Real.log (n - m : ℕ)) := by
      rcases le_total m (n - m) with h | h
      · have hc : (n : ℝ) ≤ 2 * (n - m : ℕ) := by
          exact_mod_cast (show n ≤ 2 * (n - m) by omega)
        have ht := Real.log_le_log hnpos hc
        rw [Real.log_mul (by norm_num) (by positivity)] at ht
        have hh : Real.log m ≤ Real.log (n - m : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast h)
        rw [max_eq_right hh]
        linarith
      · have hc : (n : ℝ) ≤ 2 * (m : ℝ) := by
          exact_mod_cast (show n ≤ 2 * m by omega)
        have ht := Real.log_le_log hnpos hc
        rw [Real.log_mul (by norm_num) (by positivity)] at ht
        have hh : Real.log (n - m : ℕ) ≤ Real.log m :=
          Real.log_le_log (by positivity) (by exact_mod_cast h)
        rw [max_eq_left hh]
        linarith
    have hprod : Real.log 2 * Real.log (n : ℝ) ≤
        2 * (Real.log m * Real.log (n - m : ℕ)) := by
      rcases le_total (Real.log m) (Real.log (n - m : ℕ)) with h | h
      · rw [max_eq_right h] at hsum
        nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ Real.log (n - m : ℕ) by linarith)]
      · rw [max_eq_left h] at hsum
        nlinarith [mul_nonneg (sub_nonneg.mpr hv) (show 0 ≤ Real.log (m : ℝ) by linarith)]
    have hp : 0 < Real.log m * Real.log (n - m : ℕ) :=
      mul_pos (lt_of_lt_of_le htwo hu) (lt_of_lt_of_le htwo hv)
    apply (div_le_div_iff₀ hp (mul_pos htwo hL)).mpr
    simpa only [one_mul] using hprod
  have hcard : (((Finset.Icc 2 (n - 2)).filter
      (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n))).card : ℝ)
        ≤ 4 * (Nat.sqrt n : ℝ) := by
    have hsub : (Finset.Icc 2 (n - 2)).filter
        (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)) ⊆
        Finset.range (2 * Nat.sqrt n) ∪
          (Finset.range (2 * Nat.sqrt n)).image (fun k => n - k) := by
      intro m hm
      obtain ⟨hmem, hnot⟩ := Finset.mem_filter.mp hm
      have hm' := Finset.mem_Icc.mp hmem
      by_cases h : m < 2 * Nat.sqrt n
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨n - m, Finset.mem_range.mpr (by omega), by omega⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hi := Finset.card_image_le (s := Finset.range (2 * Nat.sqrt n)) (f := fun k => n - k)
    simp only [Finset.card_range] at hc hi
    exact_mod_cast (show ((Finset.Icc 2 (n - 2)).filter
      (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n))).card ≤
        4 * Nat.sqrt n by omega)
  have hlog2 : Real.log (n : ℝ) ^ 2 ≤ 16 * Real.sqrt (n : ℝ) := by
    have hy : 0 < Real.sqrt (Real.sqrt (n : ℝ)) := by positivity
    have ht := Real.log_le_self hy.le
    rw [Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)] at ht
    have hs := Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))
    have hh : 0 ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) - Real.log (n : ℝ) := by linarith
    nlinarith [mul_nonneg hh (show 0 ≤ 4 * Real.sqrt (Real.sqrt (n : ℝ)) + Real.log (n : ℝ) by positivity)]
  have hsle : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    simpa only [pow_two] using (show (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.sqrt_le n)
  have hmass : (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ^ 2 ≤ 16 * (n : ℝ) := by
    calc
      _ ≤ Real.sqrt (n : ℝ) * (16 * Real.sqrt (n : ℝ)) :=
        mul_le_mul hsle hlog2 (by positivity) (by positivity)
      _ = _ := by nlinarith [Real.sq_sqrt hnpos.le]
  calc
    _ ≤ ∑ m ∈ (Finset.Icc 2 (n - 2)).filter
        (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          2 / (Real.log 2 * Real.log (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hpoint m (Finset.mem_filter.mp hm).1
    _ = (((Finset.Icc 2 (n - 2)).filter
        (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n))).card : ℝ) *
          (2 / (Real.log 2 * Real.log (n : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * (Nat.sqrt n : ℝ)) * (2 / (Real.log 2 * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (128 / Real.log 2) * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
      calc
        _ = (8 * (Nat.sqrt n : ℝ)) / (Real.log 2 * Real.log (n : ℝ)) := by ring
        _ ≤ (128 * (n : ℝ)) / (Real.log 2 * Real.log (n : ℝ) ^ 3) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith [mul_nonneg (show 0 ≤ 8 * Real.log 2 * Real.log (n : ℝ) by positivity)
            (show 0 ≤ 16 * (n : ℝ) - (Nat.sqrt n : ℝ) * Real.log (n : ℝ) ^ 2 by linarith)]
        _ = _ := by ring


/-- The excess estimate of the parent file, assembled from the leaves above with no
remaining gap: the range of the convolution is cut at 2 sqrt n, the middle carries the
main term n / (log n)^2 plus twice the total shift over log n cubed, and the two ends
carry a constant times n / (log n)^3. -/
theorem logConv_excess1622_split :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1000 ≤ n →
      logConvolution1622 n - (n : ℝ) / Real.log n ^ 2 ≤ C * ((n : ℝ) / Real.log n ^ 3) := by
  classical
  obtain ⟨K, hKpos, hK⟩ := logConv_shift_sum1622
  obtain ⟨Ke, hKepos, hKe⟩ := logConv_end_mass1622
  refine ⟨2 * K + Ke, by linarith, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hLne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hL
  have hT : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 (n - 2))
    (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)
    (fun m => 1 / (Real.log m * Real.log (n - m : ℕ)))
  -- the middle range
  have hmid :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 + 2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
    have hpoint : ∀ m ∈ (Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
        1 / (Real.log m * Real.log (n - m : ℕ))
          ≤ 1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))) := by
      intro m hmf
      obtain ⟨hmem, hm1, hm2⟩ := Finset.mem_filter.mp hmf
      have hu : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hv : 0 < Real.log ((n - m : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n - m by omega))
      have hsum : Real.log m + Real.log (n - m : ℕ) ≤ 2 * Real.log (n : ℝ) := by
        linarith [logConv_shift_nonneg1622 n m hmem]
      have hshift := logConv_middle_shift1622 n m hn hm1 hm2
      have huL : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
          (by exact_mod_cast (show m ≤ n by omega))
      have hvL : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < (n - m : ℕ) by omega))
          (by exact_mod_cast Nat.sub_le n m)
      exact logConv_term_majorant_bounded474 (Real.log m) (Real.log (n - m : ℕ))
        (Real.log (n : ℝ)) hu hv hL huL hvL (by linarith)
    have hcard : (((Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) ≤ (n : ℝ) := by
      have h1 : ((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card ≤ n := by
        have h2 := Finset.card_le_card (Finset.filter_subset
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n) (Finset.Icc 2 (n - 2)))
        have h3 : (Finset.Icc 2 (n - 2)).card = n - 2 + 1 - 2 := Nat.card_Icc 2 (n - 2)
        omega
      exact_mod_cast h1
    have hsums :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
          ≤ K * (n : ℝ) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans (hK n hn)
      intro x hx _
      exact logConv_shift_nonneg1622 n x hx
    have hE :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))))
          = (((Finset.Icc 2 (n - 2)).filter
              (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
                (1 / Real.log (n : ℝ) ^ 2) +
              (2 / Real.log (n : ℝ) ^ 3) *
                (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
                  (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
                  (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hcast : (0 : ℝ) ≤ 1 / Real.log (n : ℝ) ^ 2 := by positivity
    have hfac : (0 : ℝ) ≤ 2 / Real.log (n : ℝ) ^ 3 := by positivity
    have hle1 : (((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
            (1 / Real.log (n : ℝ) ^ 2) ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hcast
    have hle2 : (2 / Real.log (n : ℝ) ^ 3) *
          (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsums hfac
    calc (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ ∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) :=
          Finset.sum_le_sum hpoint
      _ = _ := hE
      _ ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) +
            (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) := add_le_add hle1 hle2
      _ = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
            2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
          field_simp
  -- the two ends
  have hends :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hKe n hn
  have hcomb : (n : ℝ) / Real.log (n : ℝ) ^ 2 +
        2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) +
          Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3)
      = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
          (2 * K + Ke) * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by ring
  have hunfold : logConvolution1622 n =
      ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ)) := rfl
  rw [hunfold]
  linarith [hsplit, hmid, hends, hcomb]
/-- The convolution excess estimate from the bounded majorant. This proof
uses the two logarithm upper bounds and avoids the false sealed annotation. -/
theorem logConv_excess_corrected474 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1000 ≤ n →
      logConvolution1622 n - (n : ℝ) / Real.log n ^ 2 ≤ C * ((n : ℝ) / Real.log n ^ 3) := by
  classical
  obtain ⟨K, hKpos, hK⟩ := logConv_shift_sum1622
  obtain ⟨Ke, hKepos, hKe⟩ := logConv_end_mass1622
  refine ⟨2 * K + Ke, by linarith, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hLne : Real.log (n : ℝ) ≠ 0 := ne_of_gt hL
  have hT : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 (n - 2))
    (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)
    (fun m => 1 / (Real.log m * Real.log (n - m : ℕ)))
  -- the middle range
  have hmid :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 + 2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
    have hpoint : ∀ m ∈ (Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
        1 / (Real.log m * Real.log (n - m : ℕ))
          ≤ 1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))) := by
      intro m hmf
      obtain ⟨hmem, hm1, hm2⟩ := Finset.mem_filter.mp hmf
      have hu : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hv : 0 < Real.log ((n - m : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n - m by omega))
      have hsum : Real.log m + Real.log (n - m : ℕ) ≤ 2 * Real.log (n : ℝ) := by
        linarith [logConv_shift_nonneg1622 n m hmem]
      have hshift := logConv_middle_shift1622 n m hn hm1 hm2
      exact logConv_term_majorant_bounded474 (Real.log m) (Real.log (n - m : ℕ)) (Real.log (n : ℝ))
        hu hv hL
        (Real.log_le_log (by exact_mod_cast (show 0 < m by omega))
          (by exact_mod_cast (show m ≤ n by omega)))
        (Real.log_le_log (by exact_mod_cast (show 0 < n - m by omega))
          (by exact_mod_cast Nat.sub_le n m))
        (by linarith)
    have hcard : (((Finset.Icc 2 (n - 2)).filter
        (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) ≤ (n : ℝ) := by
      have h1 : ((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card ≤ n := by
        have h2 := Finset.card_le_card (Finset.filter_subset
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n) (Finset.Icc 2 (n - 2)))
        have h3 : (Finset.Icc 2 (n - 2)).card = n - 2 + 1 - 2 := Nat.card_Icc 2 (n - 2)
        omega
      exact_mod_cast h1
    have hsums :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
          ≤ K * (n : ℝ) := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans (hK n hn)
      intro x hx _
      exact logConv_shift_nonneg1622 n x hx
    have hE :
        (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))))
          = (((Finset.Icc 2 (n - 2)).filter
              (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
                (1 / Real.log (n : ℝ) ^ 2) +
              (2 / Real.log (n : ℝ) ^ 3) *
                (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
                  (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
                  (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hcast : (0 : ℝ) ≤ 1 / Real.log (n : ℝ) ^ 2 := by positivity
    have hfac : (0 : ℝ) ≤ 2 / Real.log (n : ℝ) ^ 3 := by positivity
    have hle1 : (((Finset.Icc 2 (n - 2)).filter
          (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)).card : ℝ) *
            (1 / Real.log (n : ℝ) ^ 2) ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hcast
    have hle2 : (2 / Real.log (n : ℝ) ^ 3) *
          (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ))))
        ≤ (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsums hfac
    calc (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ ∑ m ∈ (Finset.Icc 2 (n - 2)).filter
            (fun m => 2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n),
            (1 / Real.log (n : ℝ) ^ 2 +
              (2 / Real.log (n : ℝ) ^ 3) *
                (2 * Real.log (n : ℝ) - (Real.log m + Real.log (n - m : ℕ)))) :=
          Finset.sum_le_sum hpoint
      _ = _ := hE
      _ ≤ (n : ℝ) * (1 / Real.log (n : ℝ) ^ 2) +
            (2 / Real.log (n : ℝ) ^ 3) * (K * (n : ℝ)) := add_le_add hle1 hle2
      _ = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
            2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
          field_simp
  -- the two ends
  have hends :
      (∑ m ∈ (Finset.Icc 2 (n - 2)).filter
          (fun m => ¬ (2 * Nat.sqrt n ≤ m ∧ m ≤ n - 2 * Nat.sqrt n)),
          1 / (Real.log m * Real.log (n - m : ℕ)))
        ≤ Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hKe n hn
  have hcomb : (n : ℝ) / Real.log (n : ℝ) ^ 2 +
        2 * K * ((n : ℝ) / Real.log (n : ℝ) ^ 3) +
          Ke * ((n : ℝ) / Real.log (n : ℝ) ^ 3)
      = (n : ℝ) / Real.log (n : ℝ) ^ 2 +
          (2 * K + Ke) * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by ring
  have hunfold : logConvolution1622 n =
      ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log m * Real.log (n - m : ℕ)) := rfl
  rw [hunfold]
  linarith [hsplit, hmid, hends, hcomb]

end LeanLab.Linnik1951
