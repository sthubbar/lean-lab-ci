/-
P0069 page 8, displays 2.8 and 2.9.
Elementary common envelope for the two divisor tails.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace LeanLab.BHP1997.Decomp561a
open Finset

/-- P0069 page 8 displays 2.8 and 2.9, auxiliary elementary totient envelope.
The divisor totient identity bounds n by tau n times phi n. -/
theorem le_card_divisors_mul_totient (n : ℕ) :
    n ≤ n.divisors.card * n.totient := by
  by_cases hn : n = 0
  · simp [hn]
  calc
    n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors, n.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp

/-- P0069 page 8 displays 2.8 and 2.9, auxiliary pointwise ratio estimate.
This weaker envelope trades the paper tau squared moment for tau fourth. -/
theorem divisor_totient_ratio_le {N d : ℕ} (hd : d ∈ N.divisors) :
    (d : ℝ) / d.totient ≤ (N.divisors.card : ℝ) := by
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd0
  apply (div_le_iff₀ hphi).mpr
  have h := le_card_divisors_mul_totient d
  have hc : d.divisors.card ≤ N.divisors.card := Finset.card_le_card
    (Nat.divisors_subset_of_dvd (Nat.ne_zero_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd))
  exact_mod_cast h.trans (Nat.mul_le_mul_right d.totient hc)

/-- P0069 page 8 display 2.8, the small divisor weight is at most tau squared over P.
This finite inequality assumes no short interval estimate. -/
theorem small_tail_le {P : ℝ} (hP : 0 < P) (N : ℕ) :
    (∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
      (d : ℝ) / (Nat.totient d : ℝ) / P) ≤ (N.divisors.card : ℝ) ^ 2 / P := by
  calc
    _ ≤ ∑ _d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ P),
        (N.divisors.card : ℝ) / P := by
      apply Finset.sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right (divisor_totient_ratio_le (Finset.mem_filter.mp hd).1) hP.le
    _ ≤ ∑ _d ∈ N.divisors, (N.divisors.card : ℝ) / P :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [pow_two]; ring

/-- P0069 page 8 display 2.9, the large divisor weight has the same tau envelope.
The strict cutoff is used before summing. -/
theorem large_tail_le {P : ℝ} (hP : 0 < P) (N : ℕ) :
    (∑ d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)),
      1 / (Nat.totient d : ℝ)) ≤ (N.divisors.card : ℝ) ^ 2 / P := by
  calc
    _ ≤ ∑ _d ∈ N.divisors.filter (fun d : ℕ => P < (d : ℝ)),
        (N.divisors.card : ℝ) / P := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd, hPd⟩ := Finset.mem_filter.mp hd
      have hd0 : (0 : ℝ) < d := hP.trans hPd
      calc
        1 / (Nat.totient d : ℝ) = ((d : ℝ) / d.totient) / d := by field_simp
        _ ≤ (N.divisors.card : ℝ) / d :=
          div_le_div_of_nonneg_right (divisor_totient_ratio_le hd) hd0.le
        _ ≤ (N.divisors.card : ℝ) / P :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hP hPd.le
    _ ≤ ∑ _d ∈ N.divisors, (N.divisors.card : ℝ) / P :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by simp [pow_two]; ring

/-- P0069 page 8 displays 2.8 and 2.9, a finite fourth divisor moment controls
any nonnegative tail satisfying the common envelope. -/
theorem tail_square_sum_le (S : Finset ℕ) {P : ℝ} (_hP : 0 < P) (w : ℕ → ℝ)
    (hw0 : ∀ N ∈ S, 0 ≤ w N)
    (hw : ∀ N ∈ S, w N ≤ (N.divisors.card : ℝ) ^ 2 / P) :
    ∑ N ∈ S, w N ^ 2 ≤ (∑ N ∈ S, (N.divisors.card : ℝ) ^ 4) / P ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro N hN
  calc
    _ ≤ ((N.divisors.card : ℝ) ^ 2 / P) ^ 2 :=
      pow_le_pow_left₀ (hw0 N hN) (hw N hN) 2
    _ = _ := by ring

end LeanLab.BHP1997.Decomp561a
