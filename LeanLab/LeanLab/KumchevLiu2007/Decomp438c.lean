/-
Coefficient and numerical supplies for the three-square off diagonal.
Source page 15 second and third displays. The coefficient leaf has a clean supply.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438d

namespace LeanLab.KumchevLiu2007.Task438c

open Real Complex Task129b Task129c
open scoped BigOperators

/-- LEAF. Page 14 display 47 in the weaker power form used on page 15.
Only one coefficient occurs. Multiplicativity, odd prime estimates and
vanishing above the third power at 2 suffice for this elementary input.
This bound has no interval, second modulus, smooth cutoff or mean square. -/
theorem coefficient_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n q : ℕ, 0 < q →
      ‖A3 n q‖ ≤ K * (q : ℝ) ^ (1 / 8 : ℝ) / (q : ℝ) := by
  exact Task438d.coefficient_power_bound

/-- Page 15 third display. Counting moduli bounds their small positive powers. -/
theorem power_sum_bound (P Y : ℝ) (hY : 1 ≤ Y) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊, (q : ℝ) ^ (1 / 8 : ℝ)) ≤
      Y ^ (9 / 8 : ℝ) := by
  calc
    _ ≤ ∑ _q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊, Y ^ (1 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by linarith))
    _ = ((Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊).card : ℝ) * Y ^ (1 / 8 : ℝ) := by simp
    _ ≤ Y * Y ^ (1 / 8 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hc : (Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊).card ≤ ⌊Y⌋₊ := by
        simp only [Nat.card_Ioc]
        omega
      exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (by linarith))
    _ = Y ^ (9 / 8 : ℝ) := by
      rw [show (9 / 8 : ℝ) = 1 + 1 / 8 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_one]

/-- Page 15 third display. The ordered distinct pair count has exponent three quarters. -/
theorem power_pair_sum (y P : ℝ) (hy : 1 ≤ y) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
      ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
        (q : ℝ) ^ (1 / 8 : ℝ) * (r : ℝ) ^ (1 / 8 : ℝ)) ≤
      y ^ (3 / 4 : ℝ) := by
  classical
  let S := Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊
  have hs := power_sum_bound P (y ^ (1 / 3 : ℝ))
    (Real.one_le_rpow hy (by norm_num))
  change (∑ q ∈ S, ∑ r ∈ S.erase q, _) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ r ∈ S, (q : ℝ) ^ (1 / 8 : ℝ) * (r : ℝ) ^ (1 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q S)
        (fun r hr hnot => by positivity)
    _ = (∑ q ∈ S, (q : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    _ ≤ ((y ^ (1 / 3 : ℝ)) ^ (9 / 8 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun q hq => by positivity)) hs 2
    _ = y ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by linarith : 0 ≤ y)]
      norm_num

/-- Page 15 second display. Cancellation over one period and the coefficient
power bound control each distinct modulus pair. CONDITIONAL on the explicit coefficient hypothesis. -/
theorem weighted_pair_interval {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (K : ℝ) (hK : 0 < K)
    (hb : ∀ n q : ℕ, 0 < q → ‖A3 n q‖ ≤ K * (q : ℝ) ^ (1 / 8 : ℝ) / (q : ℝ))
    (x y Q : ℝ) :
    (∑ n ∈ intervalNumbers x y,
      ((-(smoothWeight q Q : ℂ) * A3 n q) *
        (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
      2 * K ^ 2 * ((q : ℝ) ^ (1 / 8 : ℝ) * (r : ℝ) ^ (1 / 8 : ℝ)) := by
  let u : ℂ := -(smoothWeight q Q : ℂ)
  let v : ℂ := -(smoothWeight r Q : ℂ)
  have hu : ‖u‖ ≤ 1 := by simpa [u] using Task271b.smoothWeight_norm_le_one q Q
  have hv : ‖v‖ ≤ 1 := by simpa [v] using Task271b.smoothWeight_norm_le_one r Q
  have huv : ‖u * (starRingEnd ℂ) v‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact mul_le_one₀ hu (norm_nonneg _) hv
  have heq : (∑ n ∈ intervalNumbers x y,
      ((u * A3 n q) * (starRingEnd ℂ) (v * A3 n r)).re) =
      ((u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        A3 n q * (starRingEnd ℂ) (A3 n r))).re := by
    rw [← Complex.re_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    ring
  change (∑ n ∈ intervalNumbers x y,
      ((u * A3 n q) * (starRingEnd ℂ) (v * A3 n r)).re) ≤ _
  rw [heq]
  have hperiod : (∑ n ∈ Finset.range (q * r),
      ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖) ≤
        K ^ 2 * ((q : ℝ) ^ (1 / 8 : ℝ) * (r : ℝ) ^ (1 / 8 : ℝ)) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (q * r),
          (K * (q : ℝ) ^ (1 / 8 : ℝ) / q) *
          (K * (r : ℝ) ^ (1 / 8 : ℝ) / r) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_conj]
        exact mul_le_mul (hb n q hq) (hb n r hr) (norm_nonneg _)
          ((norm_nonneg _).trans (hb n q hq))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
        have hq0 : (q : ℝ) ≠ 0 := by positivity
        have hr0 : (r : ℝ) ≠ 0 := by positivity
        field_simp
  calc
    _ ≤ ‖(u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        A3 n q * (starRingEnd ℂ) (A3 n r))‖ := Complex.re_le_norm _
    _ ≤ ‖∑ n ∈ intervalNumbers x y, A3 n q * (starRingEnd ℂ) (A3 n r)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) huv
    _ ≤ 2 * ∑ n ∈ Finset.range (q * r),
        ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using
        Task403b.A3_conjugate_interval_bound hq hr hqr
          (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    _ ≤ _ := by nlinarith [hperiod]

/-- Page 15 second and third displays. Exact Task403c off diagonal target.
The coefficient power estimate and the pair counting estimate are proved. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := coefficient_power_bound
  refine ⟨2 * K ^ 2, by positivity, ?_⟩
  intro x y P Q hx hy hP
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          2 * K ^ 2 * ((q : ℝ) ^ (1 / 8 : ℝ) * (r : ℝ) ^ (1 / 8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hrn : 0 < r := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hr)).1
      exact weighted_pair_interval hqn hrn (Finset.ne_of_mem_erase hr).symm K hK hb x y Q
    _ ≤ (2 * K ^ 2) * y ^ (3 / 4 : ℝ) := by
      simp only [← Finset.mul_sum]
      have h := power_pair_sum y P hy
      simp only [← Finset.mul_sum] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)

end LeanLab.KumchevLiu2007.Task438c
