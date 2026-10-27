import LeanLab.LZCesaroShort.Layer

/-!
# The exact partial triangle kernel

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, page 5, the remark after Lemma 5.
The polynomial form also holds when the frequency is an integer.
-/

namespace LeanLab.LZCesaroShort

open Finset
open LeanLab.PNTPort.LargeSieve
open LeanLab.PNTPort.Vinogradov

/-- The polynomial identity for a linearly increasing geometric sum. -/
lemma ramp_geometric (H : ℕ) (q : ℂ) :
    (1 - q) ^ 2 * (∑ j ∈ range (H + 1), (j : ℂ) * q ^ j)
      = q - (H + 1 : ℕ) * q ^ (H + 1) + (H : ℂ) * q ^ (H + 2) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    simp only [pow_succ]
    ring

/-- Reindex a natural interval for complex valued sums. -/
lemma sum_Icc_eq_range_complex (F : ℕ → ℂ) (a i : ℕ) :
    ∑ n ∈ Icc a (a + i), F n = ∑ j ∈ range (i + 1), F (a + j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ← ih, show a + (i + 1) = (a + i) + 1 by ring,
      sum_Icc_succ_top (by omega)]

/-- The partial kernel at the centre is an increasing geometric ramp. -/
theorem TH_center_ramp {N H : ℕ} (hHN : H ≤ N) (α : ℝ) :
    TH N H 0 α = e ((N - H : ℕ) * α) *
      ∑ j ∈ range (H + 1), (j : ℂ) * e α ^ j := by
  have hfilter : (Icc (N - H) (N + H)).filter (fun n : ℕ => (n : ℝ) ≤ N + 0)
      = Icc (N - H) N := by
    ext n
    simp only [mem_filter, mem_Icc, add_zero, Nat.cast_le]
    omega
  unfold TH
  rw [hfilter]
  have hsum := sum_Icc_eq_range_complex
    (fun n => (((H : ℝ) - |(n : ℝ) - N| : ℝ) : ℂ) * e (n * α)) (N - H) H
  rw [Nat.sub_add_cancel hHN] at hsum
  rw [hsum, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjH : j ≤ H := by have := mem_range.mp hj; omega
  have hweight : (H : ℝ) - |((N - H + j : ℕ) : ℝ) - N| = j := by
    rw [Nat.cast_add, Nat.cast_sub hHN]
    have hjHr : (j : ℝ) ≤ H := by exact_mod_cast hjH
    rw [abs_of_nonpos (by linarith)]
    ring
  have he : e ((N - H + j : ℕ) * α) = e ((N - H : ℕ) * α) * e α ^ j := by
    rw [← e_nat_mul, ← e_add]
    congr 1
    push_cast
    ring
  rw [hweight, he]
  push_cast
  ring

/-- The denominator free form of the paper's remark at `y = 0`. -/
theorem TH_center_polynomial {N H : ℕ} (hHN : H ≤ N) (α : ℝ) :
    (1 - e α) ^ 2 * TH N H 0 α = e ((N - H : ℕ) * α) *
      (e α - (H + 1 : ℕ) * e α ^ (H + 1) + (H : ℂ) * e α ^ (H + 2)) := by
  rw [TH_center_ramp hHN, ← mul_assoc, mul_comm ((1 - e α) ^ 2), mul_assoc,
    ramp_geometric]

/-- At a natural cutoff the filtered range is a natural interval. -/
lemma TH_nat_cutoff {N H y : ℕ} (hy : y ≤ H) (α : ℝ) :
    TH N H y α = ∑ n ∈ Icc (N - H) (N + y),
      (((H : ℝ) - |(n : ℝ) - N| : ℝ) : ℂ) * e (n * α) := by
  unfold TH
  congr 1
  ext n
  simp only [mem_filter, mem_Icc]
  have hcast : (n : ℝ) ≤ (N : ℝ) + y ↔ n ≤ N + y := by
    rw [← Nat.cast_add, Nat.cast_le]
  rw [hcast]
  omega

/-- Adding the next term of the decreasing half of the triangle. -/
lemma TH_nat_step {N H y : ℕ} (hy : y + 1 ≤ H) (α : ℝ) :
    TH N H (y + 1 : ℕ) α = TH N H y α +
      (((H : ℝ) - (y + 1 : ℕ) : ℝ) : ℂ) * e ((N + y + 1 : ℕ) * α) := by
  rw [TH_nat_cutoff hy, TH_nat_cutoff (by omega : y ≤ H),
    show N + (y + 1) = (N + y) + 1 by omega, sum_Icc_succ_top (by omega)]
  congr 2
  push_cast
  rw [abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) y; linarith :
    (0 : ℝ) ≤ N + y + 1 - N)]
  push_cast
  ring

/-- The exact polynomial identity in the remark after Lemma 5. -/
theorem TH_partial_polynomial {N H y : ℕ} (hHN : H ≤ N) (hy : y ≤ H) (α : ℝ) :
    (1 - e α) ^ 2 * TH N H y α = e ((N - H : ℕ) * α) *
      (e α - 2 * e α ^ (H + 1) + e α ^ (H + y + 1) +
        ((y : ℂ) - H) * (1 - e α) * e α ^ (H + y + 1)) := by
  revert hy
  induction y with
  | zero =>
    intro hy
    rw [Nat.cast_zero, TH_center_polynomial hHN]
    simp only [add_zero, Nat.cast_zero, zero_sub]
    congr 1
    push_cast
    simp only [pow_succ]
    ring
  | succ y ih =>
    intro hy
    have he : e ((N + y + 1 : ℕ) * α) =
        e ((N - H : ℕ) * α) * e α ^ (H + y + 1) := by
      rw [← e_nat_mul, ← e_add]
      congr 1
      push_cast [Nat.cast_sub hHN]
      ring
    rw [TH_nat_step hy, mul_add, ih (by omega), he]
    push_cast
    simp only [pow_add, pow_one]
    ring

/-- The rational form of the partial kernel away from integer frequencies. -/
theorem TH_partial_formula {N H y : ℕ} (hHN : H ≤ N) (hy : y ≤ H)
    {α : ℝ} (hα : e α ≠ 1) :
    TH N H y α = (e ((N - H : ℕ) * α) *
      (e α - 2 * e α ^ (H + 1) + e α ^ (H + y + 1) +
        ((y : ℂ) - H) * (1 - e α) * e α ^ (H + y + 1))) / (1 - e α) ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hα.symm))).mpr
  rw [mul_comm]
  exact TH_partial_polynomial hHN hy α

/-- The centre partial sum has size `H / 2` at a half integer frequency for even `H`. -/
theorem TH_center_even_half {N m : ℕ} (hHN : 2 * m ≤ N) :
    ‖TH N (2 * m) 0 (1 / 2)‖ = m := by
  have hehalf : e (1 / 2 : ℝ) = -1 := by
    unfold e
    rw [show Complex.I * (((2 * Real.pi * (1 / 2) : ℝ)) : ℂ) =
      (Real.pi : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  have hp := TH_center_polynomial hHN (1 / 2)
  rw [hehalf] at hp
  have hev : (-1 : ℂ) ^ (2 * m) = 1 := by rw [pow_mul]; simp
  simp only [pow_add, hev, pow_one, neg_one_sq, mul_one, one_mul] at hp
  have heq : TH N (2 * m) 0 (1 / 2) = e ((N - 2 * m : ℕ) * (1 / 2)) * (m : ℂ) := by
    push_cast at hp
    linear_combination hp / 4
  rw [heq, norm_mul, norm_e, one_mul, Complex.norm_natCast]

/-- Partial kernels at frequency `1 / 2` have no bound independent of `H`. -/
theorem TH_center_half_unbounded (C : ℝ) :
    ∃ N H : ℕ, 2 ≤ N ∧ 1 ≤ H ∧ H ≤ N ∧ C < ‖TH N H 0 (1 / 2)‖ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max C 1)
  have hm1 : 1 < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hmn : 1 < m := by exact_mod_cast hm1
  refine ⟨2 * m, 2 * m, by omega, by omega, le_rfl, ?_⟩
  rw [TH_center_even_half le_rfl]
  exact lt_of_le_of_lt (le_max_left _ _) hm

/-- The full kernel bound by `G squared` cannot hold uniformly for partial kernels. -/
theorem not_partial_full_kernel_bound :
    ¬ ∃ C : ℝ, ∀ N H : ℕ, 2 ≤ N → 1 ≤ H → H ≤ N → ∀ α : ℝ,
      |α| ≤ 1 / 2 → ‖TH N H 0 α‖ ≤ C * G H α ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨N, H, hN, hH, hHN, hlarge⟩ := TH_center_half_unbounded C
  have hb := hC N H hN hH hHN (1 / 2) (by norm_num)
  have hd : dist0 (1 / 2 : ℝ) = 1 / 2 := by
    simpa using dist0_eq_abs (α := (1 / 2 : ℝ)) (by norm_num)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hG : G H (1 / 2) = 1 := by
    unfold G
    rw [hd]
    norm_num [min_eq_right hH1]
  rw [hG, one_pow, mul_one] at hb
  linarith

end LeanLab.LZCesaroShort
