/-
Conjugated incomplete periods and the off diagonal term, page 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp292a

namespace LeanLab.KumchevLiu2007.Task292b

open Real Complex Task129b Task292a
open scoped BigOperators

/-- LEAF. Page 13 display 45 and property v, used on page 15 after
 display 51. Pairing a with minus a makes A2 real. This algebraic leaf
contains no estimate and applies to every natural modulus. -/
theorem A2_conj (n q : ℕ) :
    (starRingEnd ℂ) (U1534.A2 n q) = U1534.A2 n q := by
  sorry

/-- Page 15 second display. The conjugated interval estimate follows
from the already proved unconjugated estimate. CONDITIONAL on A2_conj. -/
theorem A2_conjugate_interval_bound {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ ≤
      2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
  simpa only [A2_conj] using A2_interval_bound hq hr hqr a b

/-- Page 15 second display and page 14 display 47. The coefficient
product bound controls the full period absolute sum. CONDITIONAL on
A2_coprime_mul through coefficient_product_bound. -/
theorem complete_period_majorant {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    (∑ n ∈ Finset.range (q * r),
      ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖) ≤
        localMajorant q * localMajorant r := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    _ ≤ ∑ _n ∈ Finset.range (q * r),
        (localMajorant q / (q : ℝ)) * (localMajorant r / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_conj]
      exact mul_le_mul (coefficient_product_bound n q hq)
        (coefficient_product_bound n r hr) (norm_nonneg _)
        ((norm_nonneg _).trans (coefficient_product_bound n q hq))
    _ = localMajorant q * localMajorant r := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
      field_simp

/-- LEAF. Page 15 third display, numerical part of the double sum.
The local products have arbitrarily small positive power growth by
page 14 display 47. Summing two such factors up to y to the one third
costs at most y to the three quarters. No A2, interval, or weight occurs. -/
theorem majorant_pair_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ y P : ℝ, 1 ≤ y → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          localMajorant q * localMajorant r) ≤ C * y ^ (3 / 4 : ℝ) := by
  sorry

/-- Page 15 second display. Weights constant in n have norm at most one.
CONDITIONAL on A2_conj and A2_coprime_mul. -/
theorem weighted_pair_interval {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (x y Q : ℝ) :
    (∑ n ∈ intervalNumbers x y,
      ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
        (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
      2 * (localMajorant q * localMajorant r) := by
  let u : ℂ := -(smoothWeight q Q : ℂ)
  let v : ℂ := -(smoothWeight r Q : ℂ)
  have hu : ‖u‖ ≤ 1 := by simpa [u] using Task271b.smoothWeight_norm_le_one q Q
  have hv : ‖v‖ ≤ 1 := by simpa [v] using Task271b.smoothWeight_norm_le_one r Q
  have huv : ‖u * (starRingEnd ℂ) v‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact mul_le_one₀ hu (norm_nonneg _) hv
  have heq : (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) =
      ((u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))).re := by
    rw [← Complex.re_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    ring
  change (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) ≤ _
  rw [heq]
  calc
    _ ≤ ‖(u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))‖ := Complex.re_le_norm _
    _ ≤ ‖∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) huv
    _ ≤ 2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using
        A2_conjugate_interval_bound hq hr hqr (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    _ ≤ _ := mul_le_mul_of_nonneg_left (complete_period_majorant hq hr) (by norm_num)

/-- Page 15 third display. Exact Task271b.off_diagonal_power_bound
statement. CONDITIONAL on multiplicativity, reality and the numerical
prime product sum. There is no sorry in this assembly. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := majorant_pair_sum
  refine ⟨2 * C, by positivity, ?_⟩
  intro x y P Q hx hy hP
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          2 * (localMajorant q * localMajorant r) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hrn : 0 < r := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hr)).1
      exact weighted_pair_interval hqn hrn (Finset.ne_of_mem_erase hr).symm x y Q
    _ ≤ (2 * C) * y ^ (3 / 4 : ℝ) := by
      simp only [← Finset.mul_sum]
      have h := hb y P hy hP
      simp only [← Finset.mul_sum] at h
      nlinarith [h]

end LeanLab.KumchevLiu2007.Task292b
