import Mathlib

/-!
The finite arithmetic argument of P0082 page 364 display 22.
The progression estimates are explicit hypotheses. They are not proved here.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Finset

/-- P0082 page 363 before display 22. The gcd is bounded by the sum of
positive divisor weights for divisors of r that also divide m. -/
theorem gcd_le_divisor_sum (r : ℕ) (hr : 0 < r) (m : ℤ) :
    (Int.gcd m r : ℝ) ≤
      ∑ d ∈ r.divisors, if (d : ℤ) ∣ m then (d : ℝ) else 0 := by
  have hgr : Int.gcd m r ∣ r := by
    have h := Int.gcd_dvd_right m (r : ℤ)
    exact_mod_cast h
  have hgmem : Int.gcd m r ∈ r.divisors := Nat.mem_divisors.mpr ⟨hgr, hr.ne'⟩
  have h := single_le_sum (s := r.divisors)
    (f := fun d : ℕ => if (d : ℤ) ∣ m then (d : ℝ) else 0)
    (fun d _ => by split_ifs <;> positivity) hgmem
  simpa only [if_pos (Int.gcd_dvd_left m (r : ℤ))] using h

/-- P0082 page 364 display 22, before dividing by the conductor.
CONDITIONAL ON the displayed progression counts. This is a finite implication
for any integer sequence, with the exact two arithmetic terms retained. -/
theorem gcd_moment_of_progressions (s : Finset ℕ) (m : ℕ → ℤ)
    (r : ℕ) (hr : 0 < r) (C E : ℝ) (N : ℕ) (hE : 0 < E)
    (hprog : ∀ d ∈ r.divisors,
      ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤
        C * ((N : ℝ) / d + N / E)) :
    ∑ n ∈ s, (Int.gcd (m n) r : ℝ) ≤
      C * N * r.divisors.card + C * N / E * ∑ d ∈ r.divisors, (d : ℝ) := by
  calc
    _ ≤ ∑ n ∈ s, ∑ d ∈ r.divisors,
        if (d : ℤ) ∣ m n then (d : ℝ) else 0 :=
      sum_le_sum (fun n _ => gcd_le_divisor_sum r hr (m n))
    _ = ∑ d ∈ r.divisors,
        (d : ℝ) * ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ d ∈ r.divisors, (C * N + C * N / E * (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by
        exact_mod_cast Nat.pos_of_mem_divisors hd
      calc
        _ ≤ (d : ℝ) * (C * ((N : ℝ) / d + N / E)) :=
          mul_le_mul_of_nonneg_left (hprog d hd) hd0.le
        _ = _ := by field_simp
                  <;> ring
    _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]; ring

/-- P0082 page 364 display 22. The large gcd count is a finite consequence
of progression estimates. It retains tau and sigma rather than asserting
an asymptotic saving. CONDITIONAL ON the explicit progression hypothesis. -/
theorem large_gcd_of_progressions (s : Finset ℕ) (m : ℕ → ℤ)
    (r : ℕ) (hr : 0 < r) (C E : ℝ) (N : ℕ) (hE : 0 < E)
    (hprog : ∀ d ∈ r.divisors,
      ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤
        C * ((N : ℝ) / d + N / E)) :
    ((s.filter (fun n => (r : ℝ) / 24 ≤ (Int.gcd (m n) r : ℝ))).card : ℝ) ≤
      24 * (C * N * r.divisors.card + C * N / E * ∑ d ∈ r.divisors, (d : ℝ)) / r := by
  classical
  let t := s.filter (fun n => (r : ℝ) / 24 ≤ (Int.gcd (m n) r : ℝ))
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlow : (t.card : ℝ) * ((r : ℝ) / 24) ≤ ∑ n ∈ t, (Int.gcd (m n) r : ℝ) := by
    simpa only [nsmul_eq_mul] using t.card_nsmul_le_sum
      (fun n => (Int.gcd (m n) r : ℝ)) ((r : ℝ) / 24)
      (fun n hn => (mem_filter.mp hn).2)
  have hsum : ∑ n ∈ t, (Int.gcd (m n) r : ℝ) ≤ ∑ n ∈ s, (Int.gcd (m n) r : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hm := gcd_moment_of_progressions s m r hr C E N hE hprog
  have h := (le_div_iff₀ (show 0 < (r : ℝ) / 24 by positivity)).mpr
    (hlow.trans (hsum.trans hm))
  convert h using 1
  field_simp
  <;> ring

end LeanLab.ExceptionalSet.Supply465
