import LeanLab.ExceptionalSet.Bridge385

/-!
An unconditional polynomial energy estimate gives a concrete instance of the clean converter.
It is too weak for the sublinear exponent in P0029 page 9 Theorem 3.1.
Source: the definitions on P0029 pages 4 and 6 and page 13 before display 3.8.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real ArithmeticFunction

/-- The even Euler product is bounded above by 2 C0 times its positive index.
Source: P0029 page 6 display 2.10, the even singular series product. -/
theorem singular_le_linear {N : ℕ} (hN : 1 ≤ N) : Sing N ≤ 2 * C0 * N := by
  classical
  let s := N.primeFactors.filter (fun p => 2 < p)
  have hdiv : (∏ p ∈ s, p) ∣ N :=
    (prod_dvd_prod_of_subset s N.primeFactors id (filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd N)
  have hrad : (∏ p ∈ s, (p : ℝ)) ≤ (N : ℝ) := by
    have hcast : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by omega : 0 < N) hdiv
    push_cast at hcast
    exact hcast
  have hprod : (∏ p ∈ s, (1 + 1 / ((p : ℝ) - 2))) ≤ ∏ p ∈ s, (p : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (by
        have := (mem_filter.mp hp).2; omega : 3 ≤ p)
      exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
    · intro p hp
      have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (by
        have := (mem_filter.mp hp).2; omega : 3 ≤ p)
      have hd : 0 < (p : ℝ) - 2 := by linarith
      have hi : 1 / ((p : ℝ) - 2) ≤ 1 := (div_le_one hd).mpr (by linarith)
      linarith
  have hC : 0 ≤ 2 * C0 := mul_nonneg (by norm_num) C0_pos.le
  exact mul_le_mul_of_nonneg_left (hprod.trans hrad) hC

/-- A coarse cubic bound for the weighted representation count.
Source: P0029 page 4 definition of r2. -/
theorem weighted_count_le_cubic {N : ℕ} (hN : 1 ≤ N) : r2 N ≤ 2 * (N : ℝ) ^ 3 := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≤ N := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    linarith
  have hterm (n : ℕ) (hn : n ∈ range (N + 1)) : Λ n * Λ (N - n) ≤ (N : ℝ) ^ 2 := by
    have hnN : n ≤ N := by have := mem_range.mp hn; omega
    have h1 := (weight_le_log hN hnN).trans hlog
    have h2 := (weight_le_log hN (Nat.sub_le N n)).trans hlog
    simpa only [pow_two] using mul_le_mul h1 h2 vonMangoldt_nonneg (by linarith : (0 : ℝ) ≤ N)
  calc r2 N ≤ ∑ _n ∈ range (N + 1), (N : ℝ) ^ 2 := sum_le_sum hterm
    _ = ((N : ℝ) + 1) * (N : ℝ) ^ 2 := by simp
    _ ≤ 2 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hx)]

/-- A uniform cubic bound for the weighted error up to a positive cutoff.
Source: P0029 page 13 definition of E2. -/
theorem error_le_cubic {n X : ℕ} (hX : 1 ≤ X) (hn : n ≤ X) :
    |error n| ≤ (2 + 2 * C0) * (X : ℝ) ^ 3 := by
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hC := C0_pos
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [error, r2]
    positivity
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnX : (n : ℝ) ≤ X := by exact_mod_cast hn
  have hr0 : 0 ≤ r2 n := sum_nonneg (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  have hs0 : 0 ≤ (n : ℝ) * Sing n := mul_nonneg hnr (Sing_pos n).le
  have habs : |error n| ≤ r2 n + (n : ℝ) * Sing n := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hr0, abs_of_nonneg hs0])
  have hcount := weighted_count_le_cubic hn0
  have hsing := mul_le_mul_of_nonneg_left (singular_le_linear hn0) hnr
  have hpow : (n : ℝ) ^ 3 ≤ (X : ℝ) ^ 3 := by gcongr
  have hsq : (n : ℝ) ^ 2 ≤ (X : ℝ) ^ 3 := by
    calc (n : ℝ) ^ 2 ≤ (X : ℝ) ^ 2 := by gcongr
      _ ≤ (X : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (X : ℝ)) (sub_nonneg.mpr hXr)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]

/-- A coarse unconditional seventh power bound for the even weighted energy.
Source: P0029 page 13 definition of E2, using only finite sums. -/
theorem rough_even_energy {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤
      (2 * (2 + 2 * C0) ^ 2) * (X : ℝ) ^ 7 := by
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hC := C0_pos
  have hterm (n : ℕ) (hn : n ∈ range (X + 1)) :
      (error n) ^ 2 ≤ (2 + 2 * C0) ^ 2 * (X : ℝ) ^ 6 := by
    have hnX : n ≤ X := by have := mem_range.mp hn; omega
    have hb := error_le_cubic hX hnX
    calc (error n) ^ 2 = |error n| ^ 2 := (sq_abs _).symm
      _ ≤ ((2 + 2 * C0) * (X : ℝ) ^ 3) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by ring
  calc ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2
      ≤ ∑ n ∈ range (X + 1), (error n) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ _n ∈ range (X + 1), (2 + 2 * C0) ^ 2 * (X : ℝ) ^ 6 := sum_le_sum hterm
    _ = ((X : ℝ) + 1) * ((2 + 2 * C0) ^ 2 * (X : ℝ) ^ 6) := by simp
    _ ≤ (2 * (X : ℝ)) * ((2 + 2 * C0) ^ 2 * (X : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- A concrete unconditional instance of the explicit energy input at theta equal to five.
Source: P0029 page 13, auxiliary finite sum bound. -/
theorem coarse_energy_instance :
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤ C * (X : ℝ) ^ ((5 : ℝ) + 2) := by
  refine ⟨2 * (2 + 2 * C0) ^ 2, 1, fun X hX => ?_⟩
  simpa only [show (5 : ℝ) + 2 = 7 by norm_num, Real.rpow_ofNat] using rough_even_energy hX

end LeanLab.ExceptionalSet.BG2026.Supply385
