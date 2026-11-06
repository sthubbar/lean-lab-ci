/-
Resonant Mobius inputs for P0013 page 23 equation 3.40.
These use the proved Granville and Ramare estimate.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.MobiusLog325

namespace LeanLab.HelfgottArcs.Mobius325
open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- Multiples of q factor through the Mobius coefficient restricted to coprime indices.
Source: P0013 page 23, the change of variable in the resonant main term. -/
theorem moebius_multiple_factor325 (q n : ℕ) :
    (moebius : ArithmeticFunction ℝ) (q * n) =
      (moebius : ArithmeticFunction ℝ) q * coprimeMu q n := by
  by_cases hc : n.Coprime q
  · have hh := (isMultiplicative_moebius.intCast (R := ℝ)).map_mul_of_coprime hc.symm
    simpa only [coprimeMu, ArithmeticFunction.coe_mk, ite_eq_left hc] using hh
  · have hs : ¬ Squarefree (q * n) := by
      intro hh
      exact hc (Nat.coprime_of_squarefree_mul hh).symm
    simp [coprimeMu, hc, ArithmeticFunction.intCoe_apply,
      moebius_eq_zero_of_not_squarefree hs]

/-- The reciprocal Mobius sum on q multiples has absolute value at most inverse q.
Source: P0013 page 23 equation 3.40, derived from equation 2.7. -/
theorem moebius_multiples_reciprocal_bound325 (q N : ℕ) (hq : 0 < q) :
    |∑ n ∈ Icc 1 N, (moebius : ArithmeticFunction ℝ) (q * n) / (q * n : ℕ)| ≤
      1 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : ∑ n ∈ Icc 1 N, (moebius : ArithmeticFunction ℝ) (q * n) / (q * n : ℕ) =
      ((moebius : ArithmeticFunction ℝ) q / q) * ∑ n ∈ Icc 1 N, coprimeMu q n / n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [moebius_multiple_factor325, Nat.cast_mul]
    ring
  rw [heq, abs_mul, abs_div, abs_of_pos hq0]
  calc
    _ ≤ (|(moebius : ArithmeticFunction ℝ) q| / q) * 1 :=
      mul_le_mul_of_nonneg_left (coprime_mobius_reciprocal_bound q N) (by positivity)
    _ ≤ 1 / (q : ℝ) := by
      rw [mul_one]
      apply div_le_div_of_nonneg_right _ hq0.le
      change |((moebius q : ℤ) : ℝ)| ≤ 1
      exact_mod_cast (abs_moebius_le_one (n := q))

/-- Reindex a reciprocal sum restricted to multiples of q.
Source: P0013 page 23, the substitution of q times an integer in the main term. -/
theorem moebius_multiples_reindex325 (q M : ℕ) (hq : 0 < q) :
    (∑ n ∈ (Icc 1 M).filter (fun n => q ∣ n),
      (moebius : ArithmeticFunction ℝ) n / n) =
        ∑ n ∈ Icc 1 (M / q), (moebius : ArithmeticFunction ℝ) (q * n) / (q * n : ℕ) := by
  apply sum_bij' (fun n _ => n / q) (fun n _ => q * n)
  · intro n hn
    obtain ⟨hn, hd⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
    have hmul : q * (n / q) = n := Nat.mul_div_cancel' hd
    apply mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le hq).mpr
      simpa only [one_mul] using Nat.le_of_dvd (by omega : 0 < n) hd
    · exact Nat.div_le_div_right hnM
  · intro n hn
    obtain ⟨hn1, hnM⟩ := mem_Icc.mp hn
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right q n⟩
    have hh := (Nat.le_div_iff_mul_le hq).mp hnM
    simpa only [mul_comm] using hh
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2
  · intro n _
    exact Nat.mul_div_cancel_left n hq
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

/-- The resonant reciprocal Mobius sum below a cutoff has norm at most inverse q.
Source: P0013 page 23 equation 3.40, from the written Granville and Ramare input. -/
theorem resonant_mobius_reciprocal_bound325 (q M : ℕ) (hq : 0 < q) :
    |∑ n ∈ (Icc 1 M).filter (fun n => q ∣ n),
      (moebius : ArithmeticFunction ℝ) n / n| ≤ 1 / (q : ℝ) := by
  rw [moebius_multiples_reindex325 q M hq]
  exact moebius_multiples_reciprocal_bound325 q (M / q) hq

/-- The same bound holds when the multiplier index is odd.
Source: P0013 page 23 equation 3.40, the odd coprime main term after scaling by q. -/
theorem odd_moebius_multiples_reciprocal_bound325 (q N : ℕ) (hq : 0 < q) :
    |∑ n ∈ (Icc 1 N).filter Odd,
      (moebius : ArithmeticFunction ℝ) (q * n) / (q * n : ℕ)| ≤ 1 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum : |∑ n ∈ (Icc 1 N).filter Odd, coprimeMu q n / n| ≤ 1 := by
    have heq : (∑ n ∈ (Icc 1 N).filter Odd, coprimeMu q n / n) =
        ∑ n ∈ Icc 1 N, coprimeMu (2 * q) n / n := by
      rw [sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases ho : Odd n <;> by_cases hc : n.Coprime q <;>
        simp [coprimeMu, Nat.coprime_mul_iff_right, Nat.coprime_two_right, ho, hc]
    rw [heq]
    exact coprime_mobius_reciprocal_bound (2 * q) N
  have heq : (∑ n ∈ (Icc 1 N).filter Odd,
      (moebius : ArithmeticFunction ℝ) (q * n) / (q * n : ℕ)) =
        ((moebius : ArithmeticFunction ℝ) q / q) *
          ∑ n ∈ (Icc 1 N).filter Odd, coprimeMu q n / n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    rw [moebius_multiple_factor325, Nat.cast_mul]
    ring
  rw [heq, abs_mul, abs_div, abs_of_pos hq0]
  calc
    _ ≤ (|(moebius : ArithmeticFunction ℝ) q| / q) * 1 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 / (q : ℝ) := by
      rw [mul_one]
      apply div_le_div_of_nonneg_right _ hq0.le
      change |((moebius q : ℤ) : ℝ)| ≤ 1
      exact_mod_cast (abs_moebius_le_one (n := q))

example := moebius_multiple_factor325 6 5
example := moebius_multiple_factor325 6 3
example := moebius_multiples_reciprocal_bound325 6 10 (by norm_num)
example := moebius_multiples_reindex325 6 61 (by norm_num)
example := resonant_mobius_reciprocal_bound325 6 61 (by norm_num)
example := odd_moebius_multiples_reciprocal_bound325 3 10 (by norm_num)

end LeanLab.HelfgottArcs.Mobius325
