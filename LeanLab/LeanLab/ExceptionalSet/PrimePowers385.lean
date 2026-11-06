import LeanLab.ExceptionalSet.BhowmikGrimmelt2026
import LeanLab.ExceptionalSet.BG2026Prop81MPR

/-!
Prime powers in the passage from weighted representations to prime representations.
Source: P0029 pages 4 and 13, definition of r2 and the conclusion after display 3.8.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real ArithmeticFunction

noncomputable section

/-- The von Mangoldt weight of an index below N is at most log N. -/
theorem weight_le_log {n N : ℕ} (hN : 1 ≤ N) (hn : n ≤ N) :
    Λ n ≤ Real.log (N : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using Real.log_nonneg (by exact_mod_cast hN)
  · exact vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hn))

/-- A weighted convolution without any prime pair is bounded by its nonprime mass.
Source: P0029 page 4 definition of r2. -/
theorem r2_le_nonprime_mass {N : ℕ} (hN : 1 ≤ N) (hbad : ¬ IsGoldbachSum N) :
    r2 N ≤ 2 * Real.log (N : ℝ) *
      ∑ n ∈ range (N + 1), if n.Prime then 0 else Λ n := by
  classical
  let w : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n
  have hterm (n : ℕ) (hn : n ∈ range (N + 1)) :
      Λ n * Λ (N - n) ≤ Real.log N * (w n + w (N - n)) := by
    have hnN : n ≤ N := by have := mem_range.mp hn; omega
    have hnp : ¬ (n.Prime ∧ (N - n).Prime) := by
      rintro ⟨hp, hq⟩
      exact hbad ⟨n, N - n, hp, hq, by omega⟩
    have hL := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    by_cases hp : n.Prime
    · have hq : ¬ (N - n).Prime := fun h => hnp ⟨hp, h⟩
      simp only [w, ite_eq_left hp, ite_eq_right hq, zero_add]
      exact mul_le_mul_of_nonneg_right (weight_le_log hN hnN) vonMangoldt_nonneg
    · by_cases hq : (N - n).Prime
      · simp only [w, ite_eq_right hp, ite_eq_left hq, add_zero]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left (weight_le_log hN (Nat.sub_le N n))
            (vonMangoldt_nonneg (n := n))
      · simp only [w, ite_eq_right hp, ite_eq_right hq]
        calc Λ n * Λ (N - n) ≤ Real.log N * Λ (N - n) :=
            mul_le_mul_of_nonneg_right (weight_le_log hN hnN) vonMangoldt_nonneg
          _ ≤ Real.log N * (Λ n + Λ (N - n)) := by
            gcongr
            exact le_add_of_nonneg_left vonMangoldt_nonneg
  have hreflect : ∑ n ∈ range (N + 1), w (N - n) = ∑ n ∈ range (N + 1), w n := by
    simpa only [Nat.add_sub_cancel] using sum_range_reflect w (N + 1)
  calc r2 N ≤ ∑ n ∈ range (N + 1), Real.log N * (w n + w (N - n)) :=
      sum_le_sum hterm
    _ = 2 * Real.log N * ∑ n ∈ range (N + 1), w n := by
      rw [← mul_sum, sum_add_distrib, hreflect]
      ring

/-- The nonprime mass equals the difference between the Chebyshev functions.
Source: P0029 page 4 and Mathlib Chebyshev.psi_sub_theta_eq_sum_not_prime. -/
theorem nonprime_mass_eq (N : ℕ) :
    (∑ n ∈ range (N + 1), if n.Prime then (0 : ℝ) else Λ n) =
      Chebyshev.psi N - Chebyshev.theta N := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
  have hset : range (N + 1) = insert 0 (Ioc 0 N) := by
    ext n
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hset, sum_insert (by simp)]
  simp only [Nat.not_prime_zero, ↓reduceIte, ArithmeticFunction.map_zero, zero_add]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

/-- At a Goldbach exception, only proper prime powers contribute to r2.
Source: P0029 page 13 after display 3.8. -/
theorem r2_le_sqrt_log_sq {N : ℕ} (hN : 1 ≤ N) (hbad : ¬ IsGoldbachSum N) :
    r2 N ≤ 4 * Real.sqrt N * Real.log N ^ 2 := by
  have h := r2_le_nonprime_mass hN hbad
  rw [nonprime_mass_eq] at h
  have hψ := Chebyshev.psi_sub_theta_le (x := N) (by exact_mod_cast hN)
  have hL := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  calc r2 N ≤ 2 * Real.log N * (Chebyshev.psi N - Chebyshev.theta N) := h
    _ ≤ 2 * Real.log N * (2 * Real.sqrt N * Real.log N) := by gcongr
    _ = _ := by ring

/-- The prime power contribution is eventually at most C0 times N.
Source: P0029 page 13, the passage from r2 to sums of two primes. -/
theorem prime_power_eventually_small :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ¬ IsGoldbachSum N →
      r2 N ≤ C0 * N := by
  have hlo := isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) 2 (by norm_num)
  have hb := hlo.bound (show 0 < C0 / 4 by exact div_pos C0_pos (by norm_num))
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hb
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hnat
  refine ⟨max N₀ 1, le_max_right _ _, fun N hN hbad => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hbN := hN₀ N ((le_max_left _ _).trans hN)
  have hs : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hN0 _
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  simp only [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),
    abs_of_nonneg hs] at hbN
  rw [← Real.sqrt_eq_rpow] at hbN
  have hsq := Real.sq_sqrt hN0
  calc r2 N ≤ 4 * Real.sqrt N * Real.log N ^ 2 := r2_le_sqrt_log_sq hN1 hbad
    _ ≤ 4 * Real.sqrt N * (C0 / 4 * Real.sqrt N) := by gcongr
    _ = C0 * (Real.sqrt N) ^ 2 := by ring
    _ = C0 * N := by rw [hsq]

end

end LeanLab.ExceptionalSet.BG2026.Supply385
