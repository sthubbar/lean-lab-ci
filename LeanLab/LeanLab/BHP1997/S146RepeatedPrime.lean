/-
Split of the MEDIUM leaf `upper_self_scaled_deleted_repeated_prime_bound` of
SPLIT_upper_self_scaled_deleted_centred_prefix_bound into two faithful counting leaves, with the
leaf's exact statement proved from them as `upper_self_scaled_deleted_repeated_prime_bound_s146`.

Source: P0069 Baker, Harman and Pintz 1997, Section 5, page 53. At the self scale Y = m the
weight log m over log Y times k_m minus its kept part is bounded, since m has at most 1/c1 prime
factors at least m^c1, so at most (1/c1)^3 triples, each term in [0, 1], and log m over log Y is
at most 2 on J. The indicator is nonzero only when p^2 divides m for a prime p at least m^c1, and
such m in J number at most the sum over p of 2Y/p^2 plus 1, which is O(Y^(1-c1)) since c1 < 1/2.

This file adds no definition and edits no existing file. AI wrote the Lean code.
Binary Goldbach is OPEN.
-/
import LeanLab.BHP1997.SPLIT_upper_self_scaled_principal_centred_prefix_bound

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: bounded weight in the deleted part of k_m at the self scale, P0069 page 53. EASY: for
x large and m in J, the weight log m over log Y times k_m minus its kept part at Y = m is bounded
by a constant B, because m has at most 1/c1 prime factors p at least m^c1, so k_m and its kept
part are sums of at most (1/c1)^3 terms in [0, 1], and log m over log Y is at most 2 on J. -/
theorem upper_self_scaled_deleted_weight_bounded {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ B C0 : ℝ, ∀ x : ℝ, C0 ≤ x → ∀ m ∈ rightInterval ε x,
      |Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m)| ≤ B := by
  sorry

/-- LEAF: count of m in J with a repeated prime factor p at least m^c1, P0069 page 53. MEDIUM:
the number of m in J = (Y, 2Y] with p^2 dividing m for some prime p at least m^c1, hence at
least Y^c1, is at most the sum over such p up to (2Y)^(1/2) of 2Y/p^2 plus 1, which is at most
C Y^(1-c1) since c1 is about 1/8, below 1/2. -/
theorem upper_self_scaled_repeated_prime_count {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      (((rightInterval ε x).filter (fun m : ℕ =>
          ¬ ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε)).card : ℝ) ≤
        C * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
  sorry

/-- The exact statement of `upper_self_scaled_deleted_repeated_prime_bound`, proved from the two
leaves above: each term is at most B times the indicator, and the indicator sums to the count. -/
theorem upper_self_scaled_deleted_repeated_prime_bound_s146
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, x ^ (11 / 20 + ε) ≤ t →
      t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
                  then 0 else 1)) : ℝ) : ℂ))‖ ≤
          C * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
  obtain ⟨B, C0, hB⟩ := upper_self_scaled_deleted_weight_bounded hε hε8
  obtain ⟨C, hC⟩ := upper_self_scaled_repeated_prime_count hε hε8
  refine ⟨max (max C0 C) 0 + |B| * |C|, fun x hx t _ _ => ?_⟩
  have hx0 : C0 ≤ x := by
    have : 0 ≤ |B| * |C| := by positivity
    linarith [le_max_left C0 C, le_max_left (max C0 C) 0]
  have hxC : C ≤ x := by
    have : 0 ≤ |B| * |C| := by positivity
    linarith [le_max_right C0 C, le_max_left (max C0 C) 0]
  set P : ℕ → Prop := fun m => ∀ p ∈ m.primeFactors, p ^ 2 ∣ m → (p : ℝ) < (m : ℝ) ^ upperC1 ε
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)
  set T := (rightInterval ε x).filter (fun m : ℕ => ¬ P m)
  set w : ℕ → ℝ := fun m => Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
          (upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m)
  have hY : 0 ≤ (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
    have hxpos : 0 ≤ x := by
      have : 0 ≤ |B| * |C| := by positivity
      linarith [le_max_right (max C0 C) 0]
    positivity
  have hcast : (∑ m ∈ S, (((Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) *
              ((upperK ε (m : ℝ) m - upperKept ε (m : ℝ) m) *
                (if P m then 0 else 1)) : ℝ) : ℂ))) =
      (((∑ m ∈ S, w m * (if P m then 0 else 1) : ℝ)) : ℂ) := by
    push_cast [w]; refine Finset.sum_congr rfl (fun m _ => ?_); ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hterm : ∀ m ∈ S, |w m * (if P m then 0 else 1)| ≤
      |B| * (if P m then 0 else 1) := by
    intro m hm
    have hmJ : m ∈ rightInterval ε x := (Finset.mem_filter.mp hm).1
    by_cases h : P m
    · simp [h]
    · simp only [h, if_false, mul_one]
      exact le_trans (hB x hx0 m hmJ) (le_abs_self B)
  calc |∑ m ∈ S, w m * (if P m then 0 else 1)|
      ≤ ∑ m ∈ S, |w m * (if P m then 0 else 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ S, |B| * (if P m then 0 else 1) := Finset.sum_le_sum hterm
    _ = |B| * ((S.filter (fun m => ¬ P m)).card : ℝ) := by
        rw [← Finset.mul_sum]; congr 1
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
          mul_one]
    _ ≤ |B| * (T.card : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact_mod_cast Finset.card_le_card (fun m hm => by
          simp only [S, T, Finset.mem_filter] at hm ⊢; exact ⟨hm.1.1, hm.2⟩)
    _ ≤ |B| * (C * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε)) :=
        mul_le_mul_of_nonneg_left (hC x hxC) (abs_nonneg _)
    _ ≤ |B| * (|C| * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hY) (abs_nonneg _)
    _ ≤ (max (max C0 C) 0 + |B| * |C|) * (x ^ (11 / 20 + ε)) ^ (1 - upperC1 ε) := by
        have : 0 ≤ max (max C0 C) 0 := le_max_right _ _
        nlinarith [mul_nonneg this hY]

end LeanLab.BHP1997.Upper312Route
