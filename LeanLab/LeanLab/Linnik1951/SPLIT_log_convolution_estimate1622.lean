/-
Split unit of U-1622. This file adds leaves for the elementary convolution estimate
log_convolution_estimate1622 of Linnik1951/SPLIT1622_major.lean, plus the assembly
theorem log_convolution_estimate1622_split. No statement of the parent file is
changed; no definition is added.
AI wrote the Lean code. Binary Goldbach is open.

Route. Write A(n) for n / (log n)^2 and L(n) for the convolution
logConvolution1622 n, a sum over 2 <= m <= n-2. For n at most 10^3 the claim is a
finite range statement, carried by one leaf. For n at least 10^3 the sum dominates
A(n) and exceeds it only by O(n / (log n)^3), which is A(n) times 1/log n. There
log n is at least one, so 1/log n is at most 1/sqrt(log n), which is the relative
weight of the target. The two ranges cover every n at least 2 and give one pair of
constants.
-/
import LeanLab.Linnik1951.SPLIT1622_major

namespace LeanLab.Linnik1951

/-! ## Elementary logarithm facts -/

private lemma log_two_pos1622 : 0 < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_four_eq1622 : Real.log 4 = 2 * Real.log 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, Real.log_pow]
  norm_num

/-- `log 3` is at most `2 log 2 - 1/4`, from `log (3/4) ≤ 3/4 - 1`. -/
private lemma log_three_le1622 : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := by
  have h : Real.log 4 + Real.log (3 / 4) = Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h34 : Real.log (3 / 4) ≤ 3 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := log_four_eq1622
  linarith

/-- `log 5` is at least `2 log 2 + 1/5`, from `1 - 1/x ≤ log x` at `x = 5/4`. -/
private lemma log_five_ge1622 : 2 * Real.log 2 + 1 / 5 ≤ Real.log 5 := by
  have h : Real.log 4 + Real.log (5 / 4) = Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h54 : 1 - (5 / 4 : ℝ)⁻¹ ≤ Real.log (5 / 4) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := log_four_eq1622
  have hc : (1 : ℝ) - (5 / 4 : ℝ)⁻¹ = 1 / 5 := by norm_num
  linarith

/-- `log 6` is at least `(5/2) log 2`, because `4 * sqrt 2 ≤ 6`. -/
private lemma log_six_ge1622 : 5 / 2 * Real.log 2 ≤ Real.log 6 := by
  have hsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := log_four_eq1622
  have hmul : Real.log 4 + Real.log (Real.sqrt 2) = Real.log (4 * Real.sqrt 2) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hle : 4 * Real.sqrt 2 ≤ 6 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hlog : Real.log (4 * Real.sqrt 2) ≤ Real.log 6 :=
    Real.log_le_log (by positivity) hle
  linarith

/-- `1000 ≤ exp 7`. -/
private lemma exp_seven_ge1622 : (1000 : ℝ) ≤ Real.exp 7 := by
  have hexp : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 7 ≤ Real.exp 1 ^ 7 := by
    exact pow_le_pow_left₀ (by norm_num) h1.le 7
  nlinarith

/-- LEAF. Well-definedness of the summand: every index of the convolution sum has
both logarithms positive, so the summand is defined and no factor vanishes. This is
the step that lets the two one-sided leaves divide by log m and log (n - m). -/
theorem logConv_denominator_pos1622 (n m : ℕ) (hm : m ∈ Finset.Icc 2 (n - 2)) :
    0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := by
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm2, hmn⟩ := hm
  have hnm : 2 ≤ n - m := by omega
  have h1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have h2 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
  exact mul_pos (Real.log_pos h1) (Real.log_pos h2)

/-- LEAF. Scale control, main term is dominated: from n equal to 4 upwards the
convolution sum is at least n / (log n)^2. The sum has about n terms each of size
about 1 / (log n)^2, and this leaf asserts only the one-sided floor, with no error
term. It is the step that removes the absolute value in the large range. -/
theorem logConv_main_le1622 (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / Real.log n ^ 2 ≤ logConvolution1622 n := by
  have h2pos : 0 < Real.log 2 := log_two_pos1622
  rcases eq_or_lt_of_le hn with h4 | h4
  · -- n = 4: the sum is the single term at m = 2, and log 4 = 2 log 2
    subst h4
    rw [logConvolution_four1622]
    push_cast
    rw [log_four_eq1622]
    have h2 : Real.log 2 ≠ 0 := h2pos.ne'
    field_simp
    norm_num
  · rcases eq_or_lt_of_le (show 5 ≤ n by omega) with h5 | h5
    · -- n = 5: two terms, both equal to 1 / (log 2 * log 3)
      subst h5
      have hval : logConvolution1622 5 = 2 / (Real.log 2 * Real.log 3) := by
        have hset : Finset.Icc 2 (5 - 2) = ({2, 3} : Finset ℕ) := by decide
        rw [logConvolution1622, hset, Finset.sum_pair (by norm_num)]
        norm_num
        field_simp
        try ring
      rw [hval]
      push_cast
      have ha1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have ha2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have h3 : Real.log 3 ≤ 2 * Real.log 2 - 1 / 4 := log_three_le1622
      have h5b : 2 * Real.log 2 + 1 / 5 ≤ Real.log 5 := log_five_ge1622
      have hL3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hL5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
      have h3' : 5 * Real.log 2 * Real.log 3 ≤ 5 * Real.log 2 * (2 * Real.log 2 - 1 / 4) := by
        apply mul_le_mul_of_nonneg_left h3
        linarith
      have h5sq : (2 * Real.log 2 + 1 / 5) ^ 2 ≤ Real.log 5 ^ 2 := by
        have hpos : (0 : ℝ) ≤ Real.log 5 - (2 * Real.log 2 + 1 / 5) := by linarith
        have hsum : (0 : ℝ) ≤ Real.log 5 + (2 * Real.log 2 + 1 / 5) := by linarith
        nlinarith [hpos, hsum]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h3', h5sq, ha1, ha2]
    · -- n ≥ 6: two end terms of size 1 / (log 2 * log (n-2)), the rest at 1 / L^2
      have hn6 : 6 ≤ n := h5
      set L : ℝ := Real.log (n : ℝ) with hL
      have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hnR
      have hdecomp : Finset.Icc 2 (n - 2) = insert 2 (insert (n - 2) (Finset.Icc 3 (n - 3))) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hmem1 : (2 : ℕ) ∉ insert (n - 2) (Finset.Icc 3 (n - 3)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hmem2 : (n - 2) ∉ Finset.Icc 3 (n - 3) := by
        simp only [Finset.mem_Icc]
        omega
      have hmid : ∀ m ∈ Finset.Icc 3 (n - 3),
          1 / L ^ 2 ≤ 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
        intro m hm
        simp only [Finset.mem_Icc] at hm
        obtain ⟨hm3, hmn⟩ := hm
        have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
        have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
        have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
        have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
        have h1 : Real.log (m : ℝ) ≤ L := by
          rw [hL]
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < m))
            (by exact_mod_cast (by omega : m ≤ n))
        have h2 : Real.log ((n - m : ℕ) : ℝ) ≤ L := by
          rw [hL]
          exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n - m))
            (by exact_mod_cast (by omega : n - m ≤ n))
        have hprod : Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) ≤ L * L :=
          mul_le_mul h1 h2 hnmpos.le hLpos.le
        have hpos : 0 < Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) := mul_pos hmpos hnmpos
        have h := one_div_le_one_div_of_le hpos hprod
        simpa [pow_two] using h
      have hcard : (Finset.Icc 3 (n - 3)).card = n - 5 := by
        rw [Nat.card_Icc]
        omega
      have hsum_ge : ((n - 5 : ℕ) : ℝ) * (1 / L ^ 2) ≤
          ∑ m ∈ Finset.Icc 3 (n - 3), 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) := by
        have h := Finset.sum_le_sum hmid
        rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
        exact h
      have hlogend : 0 < Real.log ((n - 2 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n - 2))
      have hleend : Real.log ((n - 2 : ℕ) : ℝ) ≤ L := by
        rw [hL]
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n - 2))
          (by exact_mod_cast (by omega : n - 2 ≤ n))
      have hend1 : 1 / (Real.log 2 * L) ≤ 1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos h2pos hlogend)
          (mul_le_mul_of_nonneg_left hleend h2pos.le)
      have hend2 : 1 / (L * Real.log 2) ≤ 1 / (Real.log ((n - 2 : ℕ) : ℝ) * Real.log 2) :=
        one_div_le_one_div_of_le (mul_pos hlogend h2pos)
          (mul_le_mul_of_nonneg_right hleend h2pos.le)
      have h5a : 5 * Real.log 2 ≤ 2 * L := by
        have h6 : 5 / 2 * Real.log 2 ≤ Real.log 6 := log_six_ge1622
        have h6n : Real.log 6 ≤ L := by
          rw [hL]
          exact Real.log_le_log (by norm_num) (by exact_mod_cast hn6)
        linarith
      have h5div : (5 : ℝ) / L ^ 2 ≤ 2 / (Real.log 2 * L) := by
        rw [div_le_div_iff₀ (by nlinarith [hLpos] : (0 : ℝ) < L ^ 2) (mul_pos h2pos hLpos)]
        have hh := mul_le_mul_of_nonneg_right h5a hLpos.le
        nlinarith [hh]
      have htwo : 2 / (Real.log 2 * L) = 1 / (Real.log 2 * L) + 1 / (L * Real.log 2) := by
        have h2 : Real.log 2 ≠ 0 := h2pos.ne'
        field_simp
        try ring
      have hkey : (n : ℝ) / L ^ 2 ≤ 2 / (Real.log 2 * L) + ((n - 5 : ℕ) : ℝ) * (1 / L ^ 2) := by
        have hc : ((n - 5 : ℕ) : ℝ) = (n : ℝ) - 5 := by
          rw [Nat.cast_sub (show 5 ≤ n by omega)]
          push_cast
          ring
        have hid1 : (n : ℝ) / L ^ 2 = (5 : ℝ) / L ^ 2 + ((n : ℝ) - 5) * (1 / L ^ 2) := by
          field_simp
          try ring
        rw [hid1, hc]
        linarith [h5div]
      have hgoal : (n : ℝ) / L ^ 2 ≤
          1 / (Real.log 2 * Real.log ((n - 2 : ℕ) : ℝ)) +
            (1 / (Real.log ((n - 2 : ℕ) : ℝ) * Real.log 2) +
              ∑ m ∈ Finset.Icc 3 (n - 3),
                1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ))) := by
        linarith [hkey, htwo, hend1, hend2, hsum_ge]
      rw [logConvolution1622, hdecomp, Finset.sum_insert hmem1, Finset.sum_insert hmem2]
      rw [show n - (n - 2) = 2 from by omega]
      exact hgoal

open MeasureTheory

private lemma log_two_pos_l3 : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- Two-variable AM-GM in reciprocal form. -/
private lemma inv_mul_le_l3 (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    1 / (u * v) ≤ (1 / 2) * (1 / u ^ 2 + 1 / v ^ 2) := by
  have h : 0 ≤ (u - v) ^ 2 := sq_nonneg _
  rw [div_le_iff₀ (mul_pos hu hv)]
  field_simp
  nlinarith [h]

private lemma reindex_l3 (n : ℕ) (hn : 4 ≤ n) :
    ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log ((n - m : ℕ) : ℝ)) ^ 2
      = ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2 := by
  refine Finset.sum_bij' (fun m _ => n - m) (fun m _ => n - m) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  · intro a ha
    rfl

private lemma anti_l3 (N : ℕ) (hN : 4 ≤ N) :
    AntitoneOn (fun x : ℝ => 1 / (Real.log x) ^ 2) (Set.Icc 2 (N : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Icc] at hx hy
  have hx1 : (1 : ℝ) < x := by linarith [hx.1]
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log (by linarith [hx.1]) hxy
  have hpx : 0 < Real.log x := Real.log_pos hx1
  have hsq : Real.log x ^ 2 ≤ Real.log y ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (by positivity) hsq

private lemma sum_le_integral_l3 (N : ℕ) (hN : 4 ≤ N) :
    ∑ m ∈ Finset.Ico 3 (N + 1), 1 / (Real.log (m : ℝ)) ^ 2
      ≤ ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 2 := by
  have h := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => 1 / (Real.log x) ^ 2)
    (a := 2) (b := N) (by omega : 2 ≤ N) (anti_l3 N hN)
  have hre : ∑ i ∈ Finset.Ico 2 N, 1 / (Real.log ((i + 1 : ℕ) : ℝ)) ^ 2
      = ∑ m ∈ Finset.Ico 3 (N + 1), 1 / (Real.log (m : ℝ)) ^ 2 := by
    rw [← Finset.sum_Ico_add (f := fun m : ℕ => 1 / (Real.log (m : ℝ)) ^ 2)
      (a := 2) (b := N) (c := 1)]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring_nf
  rwa [hre] at h

private lemma hasderiv_l3 (x : ℝ) (hx : 2 ≤ x) :
    HasDerivAt (fun y : ℝ => y * (1 / (Real.log y) ^ 2))
      (1 / (Real.log x) ^ 2 - 2 * (1 / (Real.log x) ^ 3)) x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have h0 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
  have h1 : HasDerivAt (fun y : ℝ => (Real.log y)⁻¹) (-(x⁻¹) / (Real.log x) ^ 2) x :=
    h0.inv hL.ne'
  have h2 : HasDerivAt (fun y : ℝ => (Real.log y)⁻¹ ^ 2)
      (2 * (Real.log x)⁻¹ ^ (2 - 1) * (-(x⁻¹) / (Real.log x) ^ 2)) x := h1.pow 2
  have h2' : HasDerivAt (fun y : ℝ => 1 / (Real.log y) ^ 2)
      (2 * (Real.log x)⁻¹ ^ (2 - 1) * (-(x⁻¹) / (Real.log x) ^ 2)) x := by
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [one_div, inv_pow]
  have h3 : HasDerivAt (fun y : ℝ => y * (1 / (Real.log y) ^ 2))
      (1 * (1 / (Real.log x) ^ 2) +
        x * (2 * (Real.log x)⁻¹ ^ (2 - 1) * (-(x⁻¹) / (Real.log x) ^ 2))) x :=
    (hasDerivAt_id x).mul h2'
  refine h3.congr_deriv ?_
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  field_simp
  try ring

private lemma cont_l3 (N : ℕ) (hN : 4 ≤ N) :
    ContinuousOn (fun x : ℝ => 1 / (Real.log x) ^ 2) (Set.Icc (2 : ℝ) (N : ℝ)) := by
  have hne : ∀ x ∈ Set.Icc (2 : ℝ) (N : ℝ), Real.log x ≠ 0 := by
    intro x hx
    exact (Real.log_pos (by linarith [hx.1])).ne'
  have hlog : ContinuousOn Real.log (Set.Icc (2 : ℝ) (N : ℝ)) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.1])
  have h := (hlog.inv₀ hne).pow 2
  have hfun : (fun x : ℝ => 1 / (Real.log x) ^ 2) = Real.log⁻¹ ^ 2 := by
    funext x
    simp [one_div, inv_pow]
  rwa [hfun]

private lemma cont_l3' (N : ℕ) (hN : 4 ≤ N) :
    ContinuousOn (fun x : ℝ => 1 / (Real.log x) ^ 3) (Set.Icc (2 : ℝ) (N : ℝ)) := by
  have hne : ∀ x ∈ Set.Icc (2 : ℝ) (N : ℝ), Real.log x ≠ 0 := by
    intro x hx
    exact (Real.log_pos (by linarith [hx.1])).ne'
  have hlog : ContinuousOn Real.log (Set.Icc (2 : ℝ) (N : ℝ)) :=
    Real.continuousOn_log.mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hx.1])
  have h := (hlog.inv₀ hne).pow 3
  have hfun : (fun x : ℝ => 1 / (Real.log x) ^ 3) = Real.log⁻¹ ^ 3 := by
    funext x
    simp [one_div, inv_pow]
  rwa [hfun]

private lemma integral_inv_log_sq_l3 (N : ℕ) (hN : 4 ≤ N) :
    ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 2
      = (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) - 2 * (1 / (Real.log 2) ^ 2)
        + 2 * ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 3 := by
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have h4N : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2i : IntervalIntegrable (fun x : ℝ => 1 / (Real.log x) ^ 2) volume (2 : ℝ) (N : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc h2N (cont_l3 N hN)
  have h3i : IntervalIntegrable (fun x : ℝ => 1 / (Real.log x) ^ 3) volume (2 : ℝ) (N : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc h2N (cont_l3' N hN)
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun y : ℝ => y * (1 / (Real.log y) ^ 2))
        (1 / (Real.log x) ^ 2 - 2 * (1 / (Real.log x) ^ 3)) x := by
    intro x hx
    rw [Set.uIcc_of_le h2N] at hx
    exact hasderiv_l3 x hx.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => y * (1 / (Real.log y) ^ 2))
    (f' := fun x : ℝ => 1 / (Real.log x) ^ 2 - 2 * (1 / (Real.log x) ^ 3))
    (a := (2 : ℝ)) (b := (N : ℝ)) hderiv (h2i.sub (h3i.const_mul 2))
  have h1 : ∫ x in (2 : ℝ)..(N : ℝ), (1 / (Real.log x) ^ 2 - 2 * (1 / (Real.log x) ^ 3))
      = (∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 2)
        - 2 * ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 3 := by
    rw [intervalIntegral.integral_sub h2i (h3i.const_mul 2), intervalIntegral.integral_const_mul]
  rw [h1] at h
  have hNval : (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
      = (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2) := rfl
  linarith [h]

private lemma int_cube_l3 (N : ℕ) (hN : 4 ≤ N) :
    ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 3
      ≤ 4 * Real.sqrt (N : ℝ) + 8 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have h4N : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hLpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  set s : ℝ := Real.sqrt (N : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hNpos
  have hs2 : (2 : ℝ) ≤ s := by
    rw [hs]
    have h4 : Real.sqrt 4 = 2 := by
      have h := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
      have hnn := Real.sqrt_nonneg 4
      nlinarith
    rw [← h4]
    exact Real.sqrt_le_sqrt h4N
  have hsN : s ≤ (N : ℝ) := by
    rw [hs, Real.sqrt_le_left hNpos.le]
    nlinarith
  have hlogsmid : Real.log s = Real.log (N : ℝ) / 2 := by
    rw [hs]; exact Real.log_sqrt hNpos.le
  have hi1 : IntervalIntegrable (fun x : ℝ => 1 / (Real.log x) ^ 3) volume (2 : ℝ) s :=
    ContinuousOn.intervalIntegrable_of_Icc hs2 ((cont_l3' N hN).mono (by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨hx.1, le_trans hx.2 hsN⟩))
  have hi2 : IntervalIntegrable (fun x : ℝ => 1 / (Real.log x) ^ 3) volume s (N : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hsN ((cont_l3' N hN).mono (by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      exact ⟨le_trans hs2 hx.1, hx.2⟩))
  have hsplit : ((∫ x in (2 : ℝ)..s, 1 / (Real.log x) ^ 3)
      + ∫ x in s..(N : ℝ), 1 / (Real.log x) ^ 3)
      = ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 3 := by
    rw [intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  rw [← hsplit]
  have hleft : ∫ x in (2 : ℝ)..s, 1 / (Real.log x) ^ 3 ≤ 4 * s := by
    have hconst : IntervalIntegrable (fun _ : ℝ => 1 / (Real.log 2) ^ 3) volume (2 : ℝ) s :=
      intervalIntegrable_const
    have hmono : ∫ x in (2 : ℝ)..s, 1 / (Real.log x) ^ 3
        ≤ ∫ x in (2 : ℝ)..s, (fun _ : ℝ => 1 / (Real.log 2) ^ 3) x := by
      refine intervalIntegral.integral_mono_on hs2 hi1 hconst ?_
      intro x hx
      simp only [Set.mem_Icc] at hx
      have h2p : 0 < Real.log 2 := log_two_pos_l3
      have hxp : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx.1
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h2p.le hlog 3)
    have hval : ∫ x in (2 : ℝ)..s, (fun _ : ℝ => 1 / (Real.log 2) ^ 3) x
        = (s - 2) * (1 / (Real.log 2) ^ 3) := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
    have hconstle : 1 / (Real.log 2) ^ 3 ≤ 4 := by
      have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hp : 0 < Real.log 2 := log_two_pos_l3
      have h2 : ((0.6931471803 : ℝ)) ^ 3 ≤ (Real.log 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
      rw [div_le_iff₀ (by positivity)]
      nlinarith [h2]
    have hnonneg : (0 : ℝ) ≤ s - 2 := by linarith
    calc ∫ x in (2 : ℝ)..s, 1 / (Real.log x) ^ 3
        ≤ ∫ x in (2 : ℝ)..s, (fun _ : ℝ => 1 / (Real.log 2) ^ 3) x := hmono
      _ = (s - 2) * (1 / (Real.log 2) ^ 3) := hval
      _ ≤ (s - 2) * 4 := by
          apply mul_le_mul_of_nonneg_left hconstle hnonneg
      _ ≤ 4 * s := by nlinarith
  have hright : ∫ x in s..(N : ℝ), 1 / (Real.log x) ^ 3
      ≤ 8 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by
    have hconst : IntervalIntegrable (fun _ : ℝ => 8 * (1 / (Real.log (N : ℝ)) ^ 3))
        volume s (N : ℝ) := intervalIntegrable_const
    have hmono : ∫ x in s..(N : ℝ), 1 / (Real.log x) ^ 3
        ≤ ∫ x in s..(N : ℝ), (fun _ : ℝ => 8 * (1 / (Real.log (N : ℝ)) ^ 3)) x := by
      refine intervalIntegral.integral_mono_on hsN hi2 hconst ?_
      intro x hx
      simp only [Set.mem_Icc] at hx
      have hxp : 0 < Real.log x := Real.log_pos (by linarith [hx.1, hs2])
      have hLsp : 0 < Real.log s := by rw [hlogsmid]; linarith
      have hlog : Real.log s ≤ Real.log x := Real.log_le_log hs0 hx.1
      have h1 : 1 / (Real.log x) ^ 3 ≤ 1 / (Real.log s) ^ 3 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hLsp.le hlog 3)
      have h2 : 1 / (Real.log s) ^ 3 = 8 * (1 / (Real.log (N : ℝ)) ^ 3) := by
        rw [hlogsmid]
        field_simp
        try ring
      linarith [h1, h2.le, h2.ge]
    have hval : ∫ x in s..(N : ℝ), (fun _ : ℝ => 8 * (1 / (Real.log (N : ℝ)) ^ 3)) x
        = ((N : ℝ) - s) * (8 * (1 / (Real.log (N : ℝ)) ^ 3)) := by
      simp [intervalIntegral.integral_const, smul_eq_mul]
      try ring
    have hnonneg : (0 : ℝ) ≤ (N : ℝ) - s := by linarith
    calc ∫ x in s..(N : ℝ), 1 / (Real.log x) ^ 3
        ≤ ∫ x in s..(N : ℝ), (fun _ : ℝ => 8 * (1 / (Real.log (N : ℝ)) ^ 3)) x := hmono
      _ = ((N : ℝ) - s) * (8 * (1 / (Real.log (N : ℝ)) ^ 3)) := hval
      _ ≤ 8 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by
          have hc : (0 : ℝ) ≤ 8 * (1 / (Real.log (N : ℝ)) ^ 3) := by positivity
          nlinarith [hnonneg, hc]
  linarith [hleft, hright]

/-- `log N ^ 3 ≤ 216 * sqrt N`, from `log x ≤ 6 x ^ (1/6)`. -/
private lemma log_cube_le_sqrt_l3 (N : ℕ) (hN : 4 ≤ N) :
    (Real.log (N : ℝ)) ^ 3 ≤ 216 * Real.sqrt (N : ℝ) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlog : Real.log (N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) :=
    Real.log_le_rpow_div hN0 (by norm_num)
  have hrpow : ((N : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    rw [Real.sqrt_eq_rpow]
    norm_num
  have hcube : (Real.log (N : ℝ)) ^ 3 ≤ ((N : ℝ) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6)) ^ 3 := by
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) := by positivity
    exact pow_le_pow_left₀ (by positivity) hlog 3
  calc (Real.log (N : ℝ)) ^ 3
      ≤ ((N : ℝ) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6)) ^ 3 := hcube
    _ = 216 * Real.sqrt (N : ℝ) := by
        have he : (N : ℝ) ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6) = 6 * (N : ℝ) ^ ((1 : ℝ) / 6) := by
          field_simp
        rw [he, mul_pow, hrpow]
        norm_num


/-- The sum of `1 / log^2` over `2..N`, with a second order error. -/
private lemma sum_inv_log_sq_l3 (N : ℕ) (hN : 4 ≤ N) :
    ∑ m ∈ Finset.Icc 2 N, 1 / (Real.log (m : ℝ)) ^ 2
      ≤ (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
        + 2000 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by
  have hdecomp : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : (2 : ℕ) ∉ Finset.Icc 3 N := by
    simp only [Finset.mem_Icc]
    omega
  have hico : Finset.Ico 3 (N + 1) = Finset.Icc 3 N := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit : ∑ m ∈ Finset.Icc 2 N, 1 / (Real.log (m : ℝ)) ^ 2
      = 1 / (Real.log 2) ^ 2
        + ∑ m ∈ Finset.Icc 3 N, 1 / (Real.log (m : ℝ)) ^ 2 := by
    rw [hdecomp, Finset.sum_insert hnotmem]
    simp
  rw [hsplit, ← hico]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hLpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have h1 : ∑ m ∈ Finset.Ico 3 (N + 1), 1 / (Real.log (m : ℝ)) ^ 2
      ≤ ∫ x in (2 : ℝ)..(N : ℝ), 1 / (Real.log x) ^ 2 := sum_le_integral_l3 N hN
  have h2 := integral_inv_log_sq_l3 N hN
  have h3 := int_cube_l3 N hN
  have h4 : (Real.log (N : ℝ)) ^ 3 ≤ 216 * Real.sqrt (N : ℝ) := log_cube_le_sqrt_l3 N hN
  have hL3pos : (0 : ℝ) < (Real.log (N : ℝ)) ^ 3 := by positivity
  have hs0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
    rw [← sq, Real.sq_sqrt hNpos.le]
  have h6 : 8 * Real.sqrt (N : ℝ) ≤ 1728 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by
    have hstep : 8 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 3 ≤ 1728 * (N : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 8 * Real.sqrt (N : ℝ))
      nlinarith [hm, hs2, hs0]
    have hrw : 1728 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3))
        = 1728 * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := by
      field_simp
    rw [hrw, le_div_iff₀ hL3pos]
    linarith [hstep]
  have hNL3 : (0 : ℝ) < (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3) := by positivity
  have hlog2sq : 0 < (1 : ℝ) / (Real.log 2) ^ 2 := by positivity
  have h5 : 2 * (4 * Real.sqrt (N : ℝ) + 8 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)))
      = 8 * Real.sqrt (N : ℝ) + 16 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by ring
  linarith [h1, h2, h3, h5, h6, hlog2sq, hNL3]

private lemma log_four_eq_l3 : Real.log 4 = 2 * Real.log 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, Real.log_pow]
  norm_num

/-- The convolution is bounded by the main term plus `20000 n / log^3 n`. -/
private lemma excess_core_l3 (n : ℕ) (hn : 1000 ≤ n) :
    logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2
      ≤ 20000 * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
  have hn2 : 2 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set N : ℕ := n - 2 with hN
  have hN4 : 4 ≤ N := by omega
  have hNcast : (N : ℝ) = (n : ℝ) - 2 := by
    rw [hN]
    push_cast [show 2 ≤ n by omega]
    ring
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hn1000 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNle : (N : ℝ) ≤ (n : ℝ) := by rw [hNcast]; linarith
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN4R : (4 : ℝ) ≤ (N : ℝ) := by rw [hNcast]; linarith
  -- AM-GM, term by term
  have hAM : logConvolution1622 n ≤ ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2 := by
    rw [logConvolution1622]
    have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
        1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ))
          ≤ (1 / 2) * (1 / (Real.log (m : ℝ)) ^ 2 + 1 / (Real.log ((n - m : ℕ) : ℝ)) ^ 2) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      obtain ⟨hm2, hmn⟩ := hm
      have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
      have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
      have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
      have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
      exact inv_mul_le_l3 (Real.log (m : ℝ)) (Real.log ((n - m : ℕ) : ℝ)) hmpos hnmpos
    calc ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ))
        ≤ ∑ m ∈ Finset.Icc 2 (n - 2),
            (1 / 2) * (1 / (Real.log (m : ℝ)) ^ 2
              + 1 / (Real.log ((n - m : ℕ) : ℝ)) ^ 2) := Finset.sum_le_sum hterm
      _ = (1 / 2) * ((∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2)
            + ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log ((n - m : ℕ) : ℝ)) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ = (1 / 2) * ((∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2)
            + ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2) := by
          rw [reindex_l3 n hn4]
      _ = ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2 := by ring
  have hB : ∑ m ∈ Finset.Icc 2 (n - 2), 1 / (Real.log (m : ℝ)) ^ 2
      ≤ (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
        + 2000 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)) := by
    have h := sum_inv_log_sq_l3 N hN4
    rw [← hN]
    exact h
  -- the weight conversion
  set L : ℝ := Real.log (n : ℝ) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hLNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have ht_eq : L - Real.log (N : ℝ) = Real.log ((n : ℝ) / (N : ℝ)) := by
    rw [hL, Real.log_div (ne_of_gt hnpos) (ne_of_gt hNpos)]
    try ring
  have ht_nonneg : 0 ≤ L - Real.log (N : ℝ) := by
    rw [ht_eq]
    apply Real.log_nonneg
    rw [le_div_iff₀ hNpos]
    linarith
  have hratio : (n : ℝ) / (N : ℝ) = 1 + 2 / (N : ℝ) := by
    rw [hNcast]
    have hne : (n : ℝ) - 2 ≠ 0 := by linarith
    field_simp
    ring
  have htle : Real.log ((n : ℝ) / (N : ℝ)) ≤ 2 / (N : ℝ) := by
    rw [hratio]
    have hpos : (0 : ℝ) < 1 + 2 / (N : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hratio2 : (n : ℝ) / (N : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hNpos]
    rw [hNcast]
    linarith
  have hlogratio2 : Real.log ((n : ℝ) / (N : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    exact hratio2
  have hL4 : 2 * Real.log 2 ≤ L := by
    rw [hL]
    have h4log : Real.log 4 = 2 * Real.log 2 := log_four_eq_l3
    rw [← h4log]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn4)
  have h2Nsmall : 2 / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]
    linarith only [hN4R]
  have hz1 : (L - Real.log (N : ℝ)) / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hLpos]
    linarith only [ht_eq, htle, hlogratio2, hL4, h2Nsmall, Real.log_two_gt_d9]
  have hz0 : 0 ≤ (L - Real.log (N : ℝ)) / L := div_nonneg ht_nonneg hLpos.le
  have hgeo : 1 / (1 - (L - Real.log (N : ℝ)) / L) ^ 2
      ≤ 1 + 6 * ((L - Real.log (N : ℝ)) / L) := by
    have hpos : (0 : ℝ) < 1 - (L - Real.log (N : ℝ)) / L := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hfac : (0 : ℝ) ≤ (2 * ((L - Real.log (N : ℝ)) / L) - 1) *
        (3 * ((L - Real.log (N : ℝ)) / L) - 4) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have := mul_nonneg hz0 hfac
    nlinarith [this]
  have hLNrep : 1 / (Real.log (N : ℝ)) ^ 2
      = (1 / L ^ 2) * (1 / (1 - (L - Real.log (N : ℝ)) / L) ^ 2) := by
    have hLne : L ≠ 0 := hLpos.ne'
    have hLNne : Real.log (N : ℝ) ≠ 0 := hLNpos.ne'
    have h1 : 1 - (L - Real.log (N : ℝ)) / L = Real.log (N : ℝ) / L := by
      field_simp
      try ring
    rw [h1, div_pow]
    field_simp
    try ring
  have hstep1 : (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
      ≤ (n : ℝ) * (1 / L ^ 2) + 12 * ((n : ℝ) * (1 / L ^ 3)) := by
    have hA : 1 / (Real.log (N : ℝ)) ^ 2
        ≤ (1 / L ^ 2) * (1 + 6 * ((L - Real.log (N : ℝ)) / L)) := by
      rw [hLNrep]
      exact mul_le_mul_of_nonneg_left hgeo (by positivity)
    have ht_le : (L - Real.log (N : ℝ)) / L ≤ (2 / (N : ℝ)) / L := by
      rw [ht_eq]
      exact div_le_div_of_nonneg_right htle hLpos.le
    have hkey : (N : ℝ) * ((1 / L ^ 2) * (1 + 6 * ((L - Real.log (N : ℝ)) / L)))
        = (N : ℝ) * (1 / L ^ 2) + 6 * ((L - Real.log (N : ℝ)) / L) * (N : ℝ) * (1 / L ^ 2) := by
      ring
    have hmm : 6 * ((L - Real.log (N : ℝ)) / L) * (N : ℝ) * (1 / L ^ 2)
        ≤ 12 * ((n : ℝ) * (1 / L ^ 3)) := by
      have hb : ((L - Real.log (N : ℝ)) / L) * (N : ℝ) ≤ (2 / (N : ℝ)) / L * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right ht_le hNpos.le
      have hc : (2 / (N : ℝ)) / L * (N : ℝ) = 2 / L := by
        field_simp
      have hb' : ((L - Real.log (N : ℝ)) / L) * (N : ℝ) ≤ 2 / L := by
        rw [← hc]; exact hb
      have hd : 6 * ((L - Real.log (N : ℝ)) / L) * (N : ℝ) * (1 / L ^ 2) ≤ 6 * (2 / L) * (1 / L ^ 2) := by
        calc 6 * ((L - Real.log (N : ℝ)) / L) * (N : ℝ) * (1 / L ^ 2)
            = (6 * (1 / L ^ 2)) * (((L - Real.log (N : ℝ)) / L) * (N : ℝ)) := by ring
          _ ≤ (6 * (1 / L ^ 2)) * (2 / L) := by
              apply mul_le_mul_of_nonneg_left hb'
              positivity
          _ = 6 * (2 / L) * (1 / L ^ 2) := by ring
      have he : 6 * (2 / L) * (1 / L ^ 2) ≤ 12 * ((n : ℝ) * (1 / L ^ 3)) := by
        have h1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
        have h2 : 6 * (2 / L) * (1 / L ^ 2) = 12 * (1 / L ^ 3) := by
          field_simp
          try ring
        rw [h2]
        have h3 : (0 : ℝ) < 1 / L ^ 3 := by positivity
        nlinarith [h1, h3]
      linarith [hd, he]
    calc (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)
        ≤ (N : ℝ) * ((1 / L ^ 2) * (1 + 6 * ((L - Real.log (N : ℝ)) / L))) := by
          apply mul_le_mul_of_nonneg_left hA hNpos.le
      _ = (N : ℝ) * (1 / L ^ 2) + 6 * ((L - Real.log (N : ℝ)) / L) * (N : ℝ) * (1 / L ^ 2) := hkey
      _ ≤ (n : ℝ) * (1 / L ^ 2) + 12 * ((n : ℝ) * (1 / L ^ 3)) := by
          have hlead : (N : ℝ) * (1 / L ^ 2) ≤ (n : ℝ) * (1 / L ^ 2) := by
            apply mul_le_mul_of_nonneg_right hNle
            positivity
          linarith [hlead, hmm]
  have hhalf : L / 2 ≤ Real.log (N : ℝ) := by
    have h := hz1
    rw [div_le_iff₀ hLpos] at h
    linarith
  have hstep2 : 2000 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3))
      ≤ 16000 * ((n : ℝ) * (1 / L ^ 3)) := by
    have hcube : (L / 2) ^ 3 ≤ (Real.log (N : ℝ)) ^ 3 := by
      have h0 : (0 : ℝ) ≤ L / 2 := by linarith
      exact pow_le_pow_left₀ h0 hhalf 3
    have hinv : 1 / (Real.log (N : ℝ)) ^ 3 ≤ 8 * (1 / L ^ 3) := by
      have h1 : 1 / (Real.log (N : ℝ)) ^ 3 ≤ 1 / (L / 2) ^ 3 :=
        one_div_le_one_div_of_le (by positivity) hcube
      have h2 : 1 / (L / 2) ^ 3 = 8 * (1 / L ^ 3) := by
        field_simp
        try ring
      linarith [h1, h2.le, h2.ge]
    calc 2000 * ((N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3))
        ≤ 2000 * ((n : ℝ) * (8 * (1 / L ^ 3))) := by
          have h1 : (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3) ≤ (n : ℝ) * (8 * (1 / L ^ 3)) := by
            have h0 : (0 : ℝ) < 8 * (1 / L ^ 3) := by positivity
            calc (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3)
                ≤ (n : ℝ) * (1 / (Real.log (N : ℝ)) ^ 3) := by
                  apply mul_le_mul_of_nonneg_right hNle
                  positivity
              _ ≤ (n : ℝ) * (8 * (1 / L ^ 3)) := by
                  apply mul_le_mul_of_nonneg_left hinv hnpos.le
          nlinarith [h1]
      _ = 16000 * ((n : ℝ) * (1 / L ^ 3)) := by ring
  have hx3 : (0 : ℝ) ≤ (n : ℝ) * (1 / L ^ 3) := by positivity
  have hx2 : (0 : ℝ) ≤ (n : ℝ) * (1 / L ^ 2) := by positivity
  have key2 : logConvolution1622 n - (n : ℝ) * (1 / L ^ 2) ≤ 20000 * ((n : ℝ) * (1 / L ^ 3)) := by
    linarith [hAM, hB, hstep1, hstep2, hx2, hx3]
  have e1 : (n : ℝ) * (1 / L ^ 2) = (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
    rw [hL]
    ring
  have e2 : 20000 * ((n : ℝ) * (1 / L ^ 3)) = 20000 * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := by
    rw [hL]
    ring
  rw [e1, e2] at key2
  exact key2

/-- LEAF. Scale control, second order excess: from n equal to 10^3 upwards the
excess of the convolution over n / (log n)^2 is bounded by a constant times
n / (log n)^3, that is by the main term times 1 / log n. One-sided only, and no
absolute value. -/
theorem logConv_excess1622 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1000 ≤ n →
      logConvolution1622 n - (n : ℝ) / Real.log n ^ 2 ≤
        C * ((n : ℝ) / Real.log n ^ 3) := by
  refine ⟨20000, by norm_num, ?_⟩
  intro n hn
  exact excess_core_l3 n hn

/-- LEAF. The finite range: for 2 <= n <= 10^3 the whole claim of the target holds
with one constant, in absolute value and with the relative weight 1/sqrt(log n).
Finitely many cases and no asymptotic content. -/
theorem logConv_small_range1622 :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → n ≤ 1000 →
      |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤
        B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro n hn2 hn1000
  have h2pos : 0 < Real.log 2 := log_two_pos1622
  have hlogmax : Real.log (n : ℝ) ≤ 7 := by
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1000R : (n : ℝ) ≤ Real.exp 7 := by
      have h : (n : ℝ) ≤ 1000 := by exact_mod_cast hn1000
      linarith [exp_seven_ge1622]
    calc Real.log (n : ℝ) ≤ Real.log (Real.exp 7) := Real.log_le_log hnR hn1000R
      _ = 7 := Real.log_exp 7
  have hsqrtle : Real.sqrt (Real.log (n : ℝ)) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 3)]
    linarith
  have hrecip : 1 / 3 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) := by
    apply one_div_le_one_div_of_le (by
      have hpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      positivity) hsqrtle
  rcases Nat.lt_or_ge n 4 with hsmall | hbig
  · -- n = 2 or n = 3: the sum is empty
    interval_cases n
    · have hS : logConvolution1622 2 = 0 := by
        rw [logConvolution1622, show (2 - 2 : ℕ) = 0 from rfl]
        exact Finset.sum_empty
      rw [hS, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hl2 : 0 < Real.log (2 : ℝ) ^ 2 := by positivity
      have hstep : (2 : ℝ) / Real.log (2 : ℝ) ^ 2 ≤
          1000 * ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (2 : ℝ))) := by
        have h1 : (1 : ℝ) ≤ 1000 * (1 / Real.sqrt (Real.log (2 : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1000)
          linarith
        calc (2 : ℝ) / Real.log (2 : ℝ) ^ 2
            = 1 * ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) := by ring
          _ ≤ (1000 * (1 / Real.sqrt (Real.log (2 : ℝ)))) *
                ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 / Real.log (2 : ℝ) ^ 2)
          _ = 1000 * ((2 : ℝ) / Real.log (2 : ℝ) ^ 2) *
                (1 / Real.sqrt (Real.log (2 : ℝ))) := by ring
      exact hstep
    · have hS : logConvolution1622 3 = 0 := by
        rw [logConvolution1622, show (3 - 2 : ℕ) = 1 from rfl]
        exact Finset.sum_empty
      rw [hS, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hl3 : 0 < Real.log (3 : ℝ) ^ 2 := by
        have : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
        positivity
      have hstep : (3 : ℝ) / Real.log (3 : ℝ) ^ 2 ≤
          1000 * ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (3 : ℝ))) := by
        have h1 : (1 : ℝ) ≤ 1000 * (1 / Real.sqrt (Real.log (3 : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1000)
          linarith
        calc (3 : ℝ) / Real.log (3 : ℝ) ^ 2
            = 1 * ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) := by ring
          _ ≤ (1000 * (1 / Real.sqrt (Real.log (3 : ℝ)))) *
                ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 3 / Real.log (3 : ℝ) ^ 2)
          _ = 1000 * ((3 : ℝ) / Real.log (3 : ℝ) ^ 2) *
                (1 / Real.sqrt (Real.log (3 : ℝ))) := by ring
      exact hstep
  · -- 4 ≤ n: floor from the main-term leaf, ceiling from the size of one term
    have hn4 : 4 ≤ n := hbig
    have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos hnR
    have hlow : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ logConvolution1622 n :=
      logConv_main_le1622 n hn4
    have hbound : logConvolution1622 n ≤ (n : ℝ) * (1 / (Real.log 2) ^ 2) := by
      rw [logConvolution1622]
      have hterm : ∀ m ∈ Finset.Icc 2 (n - 2),
          1 / (Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ)) ≤ 1 / (Real.log 2) ^ 2 := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm2, hmn⟩ := hm
        have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
        have hnm1 : (1 : ℝ) < ((n - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n - m)
        have hmpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
        have hnmpos : 0 < Real.log ((n - m : ℕ) : ℝ) := Real.log_pos hnm1
        have h2le : Real.log 2 ≤ Real.log (m : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ m))
        have h2le' : Real.log 2 ≤ Real.log ((n - m : ℕ) : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n - m))
        have hprod : Real.log 2 * Real.log 2 ≤ Real.log (m : ℝ) * Real.log ((n - m : ℕ) : ℝ) :=
          mul_le_mul h2le h2le' h2pos.le hmpos.le
        have hpos : 0 < Real.log 2 * Real.log 2 := mul_pos h2pos h2pos
        have h := one_div_le_one_div_of_le hpos hprod
        simpa [pow_two] using h
      have hsum := Finset.sum_le_sum hterm
      have hcard : (Finset.Icc 2 (n - 2)).card = n - 3 := by
        rw [Nat.card_Icc]
        omega
      rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
      have hcast : ((n - 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : (n - 3 : ℕ) ≤ n := by omega
        exact_mod_cast this
      have hpos : (0 : ℝ) < 1 / (Real.log 2) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hcast hpos.le
      linarith [hsum, this]
    have habs : |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
        = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := abs_of_nonneg (by linarith)
    rw [habs]
    have hLs : 0 < Real.log (n : ℝ) ^ 2 := by positivity
    have hsL : (0 : ℝ) < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hLpos
    have hkey : Real.log (n : ℝ) ^ 2 * Real.sqrt (Real.log (n : ℝ)) ≤
        1000 * (Real.log 2) ^ 2 := by
      have h1 : Real.log (n : ℝ) ^ 2 ≤ 49 := by nlinarith [hlogmax, hLpos]
      have h2 : Real.sqrt (Real.log (n : ℝ)) ≤ 3 := hsqrtle
      nlinarith [h1, h2, hsL, hLs, Real.log_two_gt_d9]
    have hconst : (1 / (Real.log 2) ^ 2) ≤
        1000 * (1 / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) := by
      have hden : (0 : ℝ) < Real.log (n : ℝ) ^ 2 * Real.sqrt (Real.log (n : ℝ)) := by positivity
      rw [div_le_iff₀ (by positivity)]
      have e : 1000 * (1 / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) *
          (Real.log 2) ^ 2 =
          1000 * (Real.log 2) ^ 2 / (Real.log (n : ℝ) ^ 2 * Real.sqrt (Real.log (n : ℝ))) := by
        field_simp
        try ring
      rw [e, le_div_iff₀ hden]
      linarith [hkey]
    have hposn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hratio : (0 : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 := by positivity
    have : logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2
        ≤ (n : ℝ) * (1 / (Real.log 2) ^ 2) := by linarith
    have htarget : (n : ℝ) * (1 / (Real.log 2) ^ 2) ≤
        1000 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) := by
      have := mul_le_mul_of_nonneg_left hconst hposn
      calc (n : ℝ) * (1 / (Real.log 2) ^ 2)
          ≤ (n : ℝ) * (1000 * (1 / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := this
        _ = 1000 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by
            field_simp
            try ring
    linarith

/-- LEAF. The power identity that turns the excess into the relative weight:
n / (log n)^3 is n / (log n)^2 times 1 / log n, for every n at least 2, where the
logarithm does not vanish. -/
theorem logConv_log_cube_split1622 (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / Real.log n ^ 3 = ((n : ℝ) / Real.log n ^ 2) * (1 / Real.log n) := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos h1)
  field_simp
  try ring

/-- LEAF. The logarithmic weight comparison: for n at least 10^3 the logarithm is at
least one, so 1 / log n is at most 1 / sqrt(log n). This is what converts the
second order excess into the exact weight of the target. -/
theorem logConv_recip_log_le_sqrt1622 (n : ℕ) (hn : 1000 ≤ n) :
    1 / Real.log n ≤ 1 / Real.sqrt (Real.log n) := by
  have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos h1
  have hexp : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    have he : Real.exp 1 < (n : ℝ) := by
      have h2 : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) he.le
    simpa [Real.log_exp] using h
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hL
  have hle : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
    rw [Real.sqrt_le_left hL.le]
    nlinarith
  exact one_div_le_one_div_of_le hsqrtpos hle

/-- The target statement of the parent file, assembled from the leaves above with no
remaining gap: one constant covering the finite range 2 <= n <= 10^3 and the half
line 10^3 <= n. -/
theorem log_convolution_estimate1622_split :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → |logConvolution1622 n - (n : ℝ) / Real.log n ^ 2| ≤ B * ((n : ℝ) / Real.log n ^ 2) * (1 / Real.sqrt (Real.log n)) := by
  obtain ⟨C, hCpos, hC⟩ := logConv_excess1622
  obtain ⟨B1, hB1pos, hB1⟩ := logConv_small_range1622
  refine ⟨max B1 C, lt_of_lt_of_le hB1pos (le_max_left B1 C), ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hsqrtpos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hA : 0 ≤ (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
    div_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hS : 0 ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
    div_nonneg zero_le_one hsqrtpos.le
  have hX : 0 ≤ ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.sqrt (Real.log (n : ℝ))) :=
    mul_nonneg hA hS
  rcases le_total n 1000 with hsmall | hlarge
  · have h := hB1 n hn hsmall
    calc
      |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          ≤ B1 * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := h
      _ ≤ max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ hS
            exact mul_le_mul_of_nonneg_right (le_max_left B1 C) hA
  · have h1000 : 1000 ≤ n := hlarge
    have h4 : 4 ≤ n := by omega
    have hmain : (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤ logConvolution1622 n :=
      logConv_main_le1622 n h4
    have hexc : logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 ≤
        C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hC n h1000
    have habs : |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
        = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 :=
      abs_of_nonneg (by linarith)
    have hid : (n : ℝ) / Real.log (n : ℝ) ^ 3 =
        ((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ)) :=
      logConv_log_cube_split1622 n hn
    have hrec : 1 / Real.log (n : ℝ) ≤ 1 / Real.sqrt (Real.log (n : ℝ)) :=
      logConv_recip_log_le_sqrt1622 n h1000
    calc
      |logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2|
          = logConvolution1622 n - (n : ℝ) / Real.log (n : ℝ) ^ 2 := habs
      _ ≤ C * ((n : ℝ) / Real.log (n : ℝ) ^ 3) := hexc
      _ = C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) * (1 / Real.log (n : ℝ))) := by
            rw [hid]
      _ ≤ C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hCpos.le
            exact mul_le_mul_of_nonneg_left hrec hA
      _ ≤ max B1 C * (((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ)))) := by
            refine mul_le_mul_of_nonneg_right ?_ hX
            exact le_max_right B1 C
      _ = max B1 C * ((n : ℝ) / Real.log (n : ℝ) ^ 2) *
              (1 / Real.sqrt (Real.log (n : ℝ))) := by ring

end LeanLab.Linnik1951
