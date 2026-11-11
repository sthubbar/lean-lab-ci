import LeanLab.ExceptionalSet.PrimePowers385
import LeanLab.ExceptionalSet.Counting385
import LeanLab.ExceptionalSet.BG2026MinorCont
import LeanLab.HeathBrown1985.DivisorEps
import LeanLab.PNTPort.DirichletZF.LogDeriv
import LeanLab.PNTPort.ZetaZeros.GammaBounds
import LeanLab.PNTPort.PsiChi.SmoothedDirichlet

/-!
Auxiliary estimates for the weighted error in P0029 page 13 display 3.8.
The elementary estimates below do not assert the analytic saving in that display.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply480

open Finset Real ArithmeticFunction
open Filter Topology
open MeasureTheory
open Supply385

/-- P0029 page 6 display 2.10. Multiplication by two leaves the even Euler product unchanged. -/
theorem singular_two_mul (n : ℕ) : Sing (2 * n) = Sing n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rfl
  unfold Sing
  rw [Nat.primeFactors_mul (by norm_num) hn]
  simp [Nat.prime_two.primeFactors, Finset.filter_insert]

/-- P0029 page 13 display 3.8. Every split interval contains a multiple of four at arbitrarily
large scales. The witnesses are 24k, 28k and 32k at scale 32k. -/
theorem split_windows_inhabited (k : ℕ) (hk : 1 ≤ k) :
    24 * k ∈ (Icc (32 * k / 2 + 1) (3 * (32 * k) / 4)).filter
      (fun n => Even n ∧ 4 ∣ n) ∧
    28 * k ∈ (Icc (3 * (32 * k) / 4 + 1) (7 * (32 * k) / 8)).filter
      (fun n => Even n ∧ 4 ∣ n) ∧
    32 * k ∈ (Icc (7 * (32 * k) / 8 + 1) (32 * k)).filter
      (fun n => Even n ∧ 4 ∣ n) := by
  simp only [mem_filter, mem_Icc, even_iff_two_dvd]
  omega

/-- P0029 page 6 display 2.10. The even singular series is at most twice C0 times the divisor
count. This estimate uses each local factor at most two and the divisor product formula. -/
theorem singular_le_divisor_count {n : ℕ} (hn : 1 ≤ n) :
    Sing n ≤ 2 * C0 * (n.divisors.card : ℝ) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors.filter (fun p => 2 < p)) :
      1 + 1 / ((p : ℝ) - 2) ≤ (n.factorization p : ℝ) + 1 := by
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
    have he : 1 ≤ n.factorization p :=
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).factorization_pos_of_dvd hn0
        (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
    have heR : (1 : ℝ) ≤ n.factorization p := by exact_mod_cast he
    have hi : 1 / ((p : ℝ) - 2) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hprod : (∏ p ∈ n.primeFactors.filter (fun p => 2 < p),
      (1 + 1 / ((p : ℝ) - 2))) ≤ (n.divisors.card : ℝ) := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), ((n.factorization p : ℝ) + 1) := by
        apply prod_le_prod₀
        · intro p hp
          have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
          have : 0 < (p : ℝ) - 2 := by linarith
          positivity
        · exact hlocal
      _ ≤ ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
        exact prod_le_prod_of_subset_of_one_le₀ (filter_subset _ _) (by intros; positivity)
          (by intro p _ _; linarith [Nat.cast_nonneg (n.factorization p) (α := ℝ)])
      _ = _ := by rw [Nat.card_divisors hn0]; push_cast; rfl
  have hC := C0_pos
  exact mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 2 * C0)

/-- P0029 page 4 definition of r2. Chebyshev's linear bound for psi gives a linear logarithmic
bound for the weighted convolution, with no zero free hypothesis. -/
theorem weighted_count_le_linear_log {n : ℕ} (hn : 1 ≤ n) :
    r2 n ≤ (Real.log 4 + 4) * (n : ℝ) * Real.log n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hpsi : ∑ m ∈ range (n + 1), Λ m = Chebyshev.psi n := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    congr 1
    ext m
    simp only [mem_range, mem_Icc]
    omega
  calc
    r2 n ≤ ∑ m ∈ range (n + 1), Λ m * Real.log n := by
      apply sum_le_sum
      intro m _
      exact mul_le_mul_of_nonneg_left (weight_le_log hn (Nat.sub_le n m)) vonMangoldt_nonneg
    _ = Chebyshev.psi n * Real.log n := by rw [← sum_mul, hpsi]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)) hlog

/-- P0029 page 13 definition of E2. The elementary pointwise bound is linear times any
reciprocal integer power, uniformly below a positive cutoff. -/
theorem error_le_linear_rpow (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (X n : ℕ), 1 ≤ X → n ≤ X →
      |error n| ≤ A * (X : ℝ) ^ (1 + (k : ℝ)⁻¹) := by
  obtain ⟨D, hD, hdiv⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hC := C0_pos
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 4) * k + 2 * C0 * D, by positivity, fun X n hX hnX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [error, r2]
    positivity
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnXR : (n : ℝ) ≤ X := by exact_mod_cast hnX
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlogmono : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn) hnXR
  have hlog : Real.log (X : ℝ) ≤ (k : ℝ) * (X : ℝ) ^ (k : ℝ)⁻¹ := by
    simpa only [div_inv_eq_mul, mul_comm] using
      Real.log_le_rpow_div hX0.le (inv_pos.mpr hkR)
  have hr : r2 n ≤ (Real.log 4 + 4) * (X : ℝ) * Real.log X := by
    calc
      _ ≤ (Real.log 4 + 4) * (n : ℝ) * Real.log n := weighted_count_le_linear_log hn
      _ ≤ _ := by gcongr
  have hs : (n : ℝ) * Sing n ≤ 2 * C0 * D * (X : ℝ) * (X : ℝ) ^ (k : ℝ)⁻¹ := by
    calc
      _ ≤ (n : ℝ) * (2 * C0 * (n.divisors.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (singular_le_divisor_count hn) hnR
      _ ≤ (X : ℝ) * (2 * C0 * (D * (X : ℝ) ^ (k : ℝ)⁻¹)) := by
        gcongr
        exact (hdiv n hn).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hnR hnXR (by positivity)) hD.le)
      _ = _ := by ring
  have habs : |error n| ≤ r2 n + (n : ℝ) * Sing n := by
    have hr0 : 0 ≤ r2 n :=
      sum_nonneg (fun _ _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hr0,
      abs_of_nonneg (mul_nonneg hnR (Sing_pos n).le)]
  calc
    _ ≤ (Real.log 4 + 4) * (X : ℝ) * Real.log X +
        2 * C0 * D * (X : ℝ) * (X : ℝ) ^ (k : ℝ)⁻¹ := habs.trans (add_le_add hr hs)
    _ ≤ (Real.log 4 + 4) * (X : ℝ) * ((k : ℝ) * (X : ℝ) ^ (k : ℝ)⁻¹) +
        2 * C0 * D * (X : ℝ) * (X : ℝ) ^ (k : ℝ)⁻¹ := by gcongr
    _ = _ := by rw [Real.rpow_add hX0, Real.rpow_one]; ring

/-- P0029 page 13 display 3.8, an unconditional comparison estimate. The exponent approaches
three from above. It does not give the exponent below three needed in the sealed leaves. -/
theorem elementary_energy (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → ∀ s : Finset ℕ, s ⊆ range (X + 1) →
      ∑ n ∈ s, (error n) ^ 2 ≤ C * (X : ℝ) ^ (3 + 2 * (k : ℝ)⁻¹) := by
  obtain ⟨A, hA, hbound⟩ := error_le_linear_rpow k hk
  refine ⟨2 * A ^ 2, by positivity, fun X hX s hs => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hterm (n : ℕ) (hn : n ∈ range (X + 1)) :
      (error n) ^ 2 ≤ A ^ 2 * (X : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹) := by
    have hb := hbound X n hX (by have := mem_range.mp hn; omega)
    calc
      _ = |error n| ^ 2 := (sq_abs _).symm
      _ ≤ (A * (X : ℝ) ^ (1 + (k : ℝ)⁻¹)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = A ^ 2 * ((X : ℝ) ^ (1 + (k : ℝ)⁻¹)) ^ 2 := by ring
      _ = _ := by rw [← Real.rpow_mul_natCast hX0.le]; congr 2; push_cast; ring
  calc
    _ ≤ ∑ n ∈ range (X + 1), (error n) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ _n ∈ range (X + 1), A ^ 2 * (X : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹) :=
      sum_le_sum hterm
    _ = ((X : ℝ) + 1) * (A ^ 2 * (X : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹)) := by simp
    _ ≤ (2 * (X : ℝ)) * (A ^ 2 * (X : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (2 * A ^ 2) * ((X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (2 + 2 * (k : ℝ)⁻¹)) := by
      rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hX0]; congr 2; ring

/-- P0029 page 13 display 3.8, audit of the elementary comparison route. Every positive multiple
of the bound just proved eventually exceeds any proposed bound at the sealed exponent.
This compares upper bounds and is not a negation of any energy leaf. -/
theorem elementary_bound_not_dominated (Θ ε : ℝ) (hsublinear : ε < 3 / 2 - 2 * Θ)
    (k : ℕ) (hk : 1 ≤ k) (A : ℝ) (hA : 0 < A) (C : ℝ) (Y₀ : ℕ) :
    ∃ Y : ℕ, max 1 Y₀ ≤ Y ∧
      C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) <
        A * (Y : ℝ) ^ (3 + 2 * (k : ℝ)⁻¹) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hgap : 0 < (3 + 2 * (k : ℝ)⁻¹) - (3 / 2 + 2 * Θ + ε) := by
    have := inv_pos.mpr hkR
    linarith
  have ht : Tendsto (fun Y : ℕ =>
      (Y : ℝ) ^ ((3 + 2 * (k : ℝ)⁻¹) - (3 / 2 + 2 * Θ + ε))) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_gt_atTop (C / A))
  let Y := max (max 1 Y₀) N
  refine ⟨Y, le_max_left _ _, ?_⟩
  have hY1 : 1 ≤ Y := (le_max_left 1 Y₀).trans (le_max_left _ _)
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hlarge := hN Y (le_max_right _ _)
  rw [Real.rpow_sub hYr] at hlarge
  have hcross := (div_lt_div_iff₀ hA (Real.rpow_pos_of_pos hYr _)).mp hlarge
  simpa only [mul_comm] using hcross

/-- P0029 page 4, the weighted representation count with all proper prime powers removed. -/
noncomputable def primeOnly (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), if n.Prime ∧ (N - n).Prime then Λ n * Λ (N - n) else 0

/-- P0029 page 4, the neglected proper prime powers. Their contribution is nonnegative and at
most four times the square root of N times log N squared, at every positive integer N. -/
theorem prime_power_correction_bound {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ r2 N - primeOnly N ∧
      r2 N - primeOnly N ≤ 4 * Real.sqrt N * Real.log N ^ 2 := by
  classical
  let w : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n
  have heq : r2 N - primeOnly N =
      ∑ n ∈ range (N + 1), if n.Prime ∧ (N - n).Prime then 0 else Λ n * Λ (N - n) := by
    rw [r2, primeOnly, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    split_ifs <;> ring
  have hterm (n : ℕ) (hn : n ∈ range (N + 1)) :
      (if n.Prime ∧ (N - n).Prime then 0 else Λ n * Λ (N - n)) ≤
        Real.log N * (w n + w (N - n)) := by
    have hnN : n ≤ N := by have := mem_range.mp hn; omega
    have hL := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
    by_cases hp : n.Prime
    · by_cases hq : (N - n).Prime
      · simp [w, hp, hq]
      · simp only [w, hp, hq, and_false, ↓reduceIte, zero_add]
        exact mul_le_mul_of_nonneg_right (weight_le_log hN hnN) vonMangoldt_nonneg
    · by_cases hq : (N - n).Prime
      · simp only [w, hp, hq, false_and, ↓reduceIte, add_zero]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (weight_le_log hN (Nat.sub_le N n)) (vonMangoldt_nonneg (n := n))
      · simp only [w, hp, hq, false_and, ↓reduceIte]
        calc
          Λ n * Λ (N - n) ≤ Real.log N * Λ (N - n) :=
            mul_le_mul_of_nonneg_right (weight_le_log hN hnN) vonMangoldt_nonneg
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left vonMangoldt_nonneg) hL
  have hreflect : ∑ n ∈ range (N + 1), w (N - n) = ∑ n ∈ range (N + 1), w n := by
    simpa only [Nat.add_sub_cancel] using sum_range_reflect w (N + 1)
  constructor
  · rw [heq]
    apply sum_nonneg
    intro n _
    split_ifs <;> positivity
  · calc
      _ ≤ ∑ n ∈ range (N + 1), Real.log N * (w n + w (N - n)) := by
        rw [heq]
        exact sum_le_sum hterm
      _ = 2 * Real.log N * ∑ n ∈ range (N + 1), w n := by
        rw [← mul_sum, sum_add_distrib, hreflect]
        ring
      _ = 2 * Real.log N * (Chebyshev.psi N - Chebyshev.theta N) := by
        rw [show (∑ n ∈ range (N + 1), w n) = _ from nonprime_mass_eq N]
      _ ≤ 2 * Real.log N * (2 * Real.sqrt N * Real.log N) :=
        mul_le_mul_of_nonneg_left
          (Chebyshev.psi_sub_theta_le (by exact_mod_cast hN))
          (by have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); positivity)
      _ = _ := by ring

/-- P0029 pages 4 and 13, the proper prime powers omitted by the survey. Their squared total
contribution on every subset through X is at most 131072 times X to the power five halves. -/
theorem prime_power_energy {X : ℕ} (hX : 1 ≤ X) (s : Finset ℕ)
    (hs : s ⊆ range (X + 1)) :
    ∑ n ∈ s, (r2 n - primeOnly n) ^ 2 ≤ 131072 * (X : ℝ) ^ (5 / 2 : ℝ) := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
  have hlog : Real.log (X : ℝ) ≤ 8 * (X : ℝ) ^ (1 / 8 : ℝ) := by
    convert Real.log_le_rpow_div hX0.le (by norm_num : (0 : ℝ) < 1 / 8) using 1 <;> ring
  have hlog2 : Real.log (X : ℝ) ^ 2 ≤ 64 * (X : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (8 * (X : ℝ) ^ (1 / 8 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlogX hlog 2
      _ = 64 * ((X : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by ring
      _ = _ := by rw [← Real.rpow_mul_natCast hX0.le]; norm_num
  have hsqrt : Real.sqrt X * (X : ℝ) ^ (1 / 4 : ℝ) = (X : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX0]
    norm_num
  have hpoint (n : ℕ) (hnX : n ≤ X) :
      0 ≤ r2 n - primeOnly n ∧ r2 n - primeOnly n ≤ 256 * (X : ℝ) ^ (3 / 4 : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [r2, primeOnly]
      positivity
    have hpp := prime_power_correction_bound hn
    have hnR : (n : ℝ) ≤ X := by exact_mod_cast hnX
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlogmono : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn) hnR
    refine ⟨hpp.1, ?_⟩
    calc
      _ ≤ 4 * Real.sqrt n * Real.log n ^ 2 := hpp.2
      _ ≤ 4 * Real.sqrt X * Real.log X ^ 2 := by gcongr
      _ ≤ 4 * Real.sqrt X * (64 * (X : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = 256 * (Real.sqrt X * (X : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = _ := by rw [hsqrt]
  have hterm (n : ℕ) (hn : n ∈ range (X + 1)) :
      (r2 n - primeOnly n) ^ 2 ≤ 65536 * (X : ℝ) ^ (3 / 2 : ℝ) := by
    have hb := hpoint n (by have := mem_range.mp hn; omega)
    calc
      _ ≤ (256 * (X : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hb.1 hb.2 2
      _ = 65536 * ((X : ℝ) ^ (3 / 4 : ℝ)) ^ 2 := by ring
      _ = _ := by rw [← Real.rpow_mul_natCast hX0.le]; norm_num
  calc
    _ ≤ ∑ n ∈ range (X + 1), (r2 n - primeOnly n) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ _n ∈ range (X + 1), 65536 * (X : ℝ) ^ (3 / 2 : ℝ) := sum_le_sum hterm
    _ = ((X : ℝ) + 1) * (65536 * (X : ℝ) ^ (3 / 2 : ℝ)) := by simp
    _ ≤ (2 * (X : ℝ)) * (65536 * (X : ℝ) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 131072 * ((X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hX0]; norm_num

/-- P0029 pages 4 and 13, transfer from representations by primes to von Mangoldt weights.
CONDITIONAL ON the explicit prime representation energy bound. -/
theorem weighted_energy_of_prime_energy {X : ℕ} (hX : 1 ≤ X) (s : Finset ℕ)
    (hs : s ⊆ range (X + 1)) {p C : ℝ} (hp : 5 / 2 ≤ p)
    (henergy : ∑ n ∈ s, (primeOnly n - (n : ℝ) * Sing n) ^ 2 ≤ C * (X : ℝ) ^ p) :
    ∑ n ∈ s, (error n) ^ 2 ≤ (2 * C + 262144) * (X : ℝ) ^ p := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hcor : ∑ n ∈ s, (r2 n - primeOnly n) ^ 2 ≤ 131072 * (X : ℝ) ^ p := by
    exact (prime_power_energy hX s hs).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hp) (by norm_num))
  have hpoint (n : ℕ) : (error n) ^ 2 ≤
      2 * ((primeOnly n - (n : ℝ) * Sing n) ^ 2 + (r2 n - primeOnly n) ^ 2) := by
    convert (add_sq_le (a := primeOnly n - (n : ℝ) * Sing n)
      (b := r2 n - primeOnly n)) using 1 <;> unfold error <;> ring
  calc
    _ ≤ ∑ n ∈ s, 2 * ((primeOnly n - (n : ℝ) * Sing n) ^ 2 +
        (r2 n - primeOnly n) ^ 2) := sum_le_sum (fun n _ => hpoint n)
    _ = 2 * ∑ n ∈ s, (primeOnly n - (n : ℝ) * Sing n) ^ 2 +
        2 * ∑ n ∈ s, (r2 n - primeOnly n) ^ 2 := by
      rw [← mul_sum, sum_add_distrib, mul_add]
    _ ≤ 2 * (C * (X : ℝ) ^ p) + 2 * (131072 * (X : ℝ) ^ p) :=
      add_le_add (mul_le_mul_of_nonneg_left henergy (by norm_num))
        (mul_le_mul_of_nonneg_left hcor (by norm_num))
    _ = _ := by ring

/-- P0029 pages 4 and 13, reverse comparison. Removing proper prime powers preserves every
energy exponent at least five halves. CONDITIONAL ON the explicit weighted energy bound. -/
theorem prime_energy_of_weighted_energy {X : ℕ} (hX : 1 ≤ X) (s : Finset ℕ)
    (hs : s ⊆ range (X + 1)) {p C : ℝ} (hp : 5 / 2 ≤ p)
    (henergy : ∑ n ∈ s, (error n) ^ 2 ≤ C * (X : ℝ) ^ p) :
    ∑ n ∈ s, (primeOnly n - (n : ℝ) * Sing n) ^ 2 ≤ (2 * C + 262144) * (X : ℝ) ^ p := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hcor : ∑ n ∈ s, (r2 n - primeOnly n) ^ 2 ≤ 131072 * (X : ℝ) ^ p := by
    exact (prime_power_energy hX s hs).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 hp) (by norm_num))
  have hpoint (n : ℕ) : (primeOnly n - (n : ℝ) * Sing n) ^ 2 ≤
      2 * ((error n) ^ 2 + (r2 n - primeOnly n) ^ 2) := by
    convert (add_sq_le (a := error n) (b := -(r2 n - primeOnly n))) using 1 <;>
      unfold error <;> ring
  calc
    _ ≤ ∑ n ∈ s, 2 * ((error n) ^ 2 + (r2 n - primeOnly n) ^ 2) :=
      sum_le_sum (fun n _ => hpoint n)
    _ = 2 * ∑ n ∈ s, (error n) ^ 2 + 2 * ∑ n ∈ s, (r2 n - primeOnly n) ^ 2 := by
      rw [← mul_sum, sum_add_distrib, mul_add]
    _ ≤ 2 * (C * (X : ℝ) ^ p) + 2 * (131072 * (X : ℝ) ^ p) :=
      add_le_add (mul_le_mul_of_nonneg_left henergy (by norm_num))
        (mul_le_mul_of_nonneg_left hcor (by norm_num))
    _ = _ := by ring

/-- P0029 page 12, the Parseval mass of the prime generating polynomial. Every positive
exponent loss absorbs the logarithm using Chebyshev's psi bound. The finite cutoff form of
the generating function is the one in page 14 display 4.4. -/
theorem prime_generating_mass {X : ℕ} (hX : 1 ≤ X) {η : ℝ} (hη : 0 < η) :
    ∫ α in (0 : ℝ)..1, ‖SΛ (X + 1) α‖ ^ 2 ≤
      ((Real.log 4 + 4) / η) * (X : ℝ) ^ (1 + η) := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hpsi : ∑ n ∈ range (X + 1), Λ n = Chebyshev.psi X := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    congr 1
    ext n
    simp only [mem_range, mem_Icc]
    omega
  calc
    _ = ∑ n ∈ range (X + 1), (Λ n) ^ 2 := integral_norm_sq_S _
    _ ≤ ∑ n ∈ range (X + 1), Λ n * Real.log X := by
      apply sum_le_sum
      intro n hn
      simpa only [pow_two] using mul_le_mul_of_nonneg_left
        (weight_le_log hX (by have := mem_range.mp hn; omega)) (vonMangoldt_nonneg (n := n))
    _ = Chebyshev.psi X * Real.log X := by rw [← sum_mul, hpsi]
    _ ≤ ((Real.log 4 + 4) * (X : ℝ)) * Real.log X :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self hX0.le) hL
    _ ≤ ((Real.log 4 + 4) * (X : ℝ)) * ((X : ℝ) ^ η / η) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hX0.le hη) (by positivity)
    _ = _ := by rw [Real.rpow_add hX0, Real.rpow_one]; ring

/-- P0029 pages 12 and 13, the Parseval perturbation step between displays 3.7 and 3.8.
This is the continuous coefficient estimate for an explicit uniform approximation.
Its application to the paper is CONDITIONAL ON the uniform approximation to its model. -/
theorem square_error_bessel (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (B : ℝ) (hclose : ∀ α ∈ Set.Icc (0 : ℝ) 1, ‖f α - g α‖ ≤ B) (s : Finset ℤ) :
    ∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => f α ^ 2 - g α ^ 2) n‖ ^ 2 ≤
      B ^ 2 * ∫ α in (0 : ℝ)..1, ‖f α + g α‖ ^ 2 := by
  have hcont : Continuous (fun α => f α ^ 2 - g α ^ 2) := (hf.pow 2).sub (hg.pow 2)
  have hL2 : MemLp (fun α => f α ^ 2 - g α ^ 2) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
      (hcont.norm.pow 2).integrableOn_Ioc
  have hbessel : ∑ n ∈ s,
      ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => f α ^ 2 - g α ^ 2) n‖ ^ 2 ≤
        ∫ α in (0 : ℝ)..1, ‖f α ^ 2 - g α ^ 2‖ ^ 2 := by
    simpa using sum_le_hasSum s (fun _ _ => sq_nonneg _)
      (hasSum_sq_fourierCoeffOn (zero_lt_one' ℝ) hL2)
  have hi1 : IntervalIntegrable (fun α => ‖f α ^ 2 - g α ^ 2‖ ^ 2) volume 0 1 :=
    (hcont.norm.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun α => B ^ 2 * ‖f α + g α‖ ^ 2) volume 0 1 :=
    (continuous_const.mul ((hf.add hg).norm.pow 2)).intervalIntegrable _ _
  calc
    _ ≤ ∫ α in (0 : ℝ)..1, ‖f α ^ 2 - g α ^ 2‖ ^ 2 := hbessel
    _ ≤ ∫ α in (0 : ℝ)..1, B ^ 2 * ‖f α + g α‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on zero_le_one hi1 hi2
      intro α hα
      rw [show f α ^ 2 - g α ^ 2 = (f α - g α) * (f α + g α) by ring,
        norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hclose α hα) 2) (sq_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- P0029 pages 12 and 13, the exponent in display 3.8 from an explicit uniform version
of the error suggested by display 3.7 and a quadratic mass bound with an allocated exponent loss.
CONDITIONAL ON both explicit analytic estimates. -/
theorem square_error_energy_of_uniform (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    {X : ℝ} (hX : 0 < X) (Θ ε K A : ℝ)
    (hclose : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖f α - g α‖ ≤ K * X ^ (Θ + 1 / 4 + ε / 4))
    (hmass : ∫ α in (0 : ℝ)..1, ‖f α + g α‖ ^ 2 ≤ A * X ^ (1 + ε / 2)) (s : Finset ℤ) :
    ∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => f α ^ 2 - g α ^ 2) n‖ ^ 2 ≤
      (K ^ 2 * A) * X ^ (3 / 2 + 2 * Θ + ε) := by
  calc
    _ ≤ (K * X ^ (Θ + 1 / 4 + ε / 4)) ^ 2 *
        ∫ α in (0 : ℝ)..1, ‖f α + g α‖ ^ 2 :=
      square_error_bessel f g hf hg _ hclose s
    _ ≤ (K * X ^ (Θ + 1 / 4 + ε / 4)) ^ 2 * (A * X ^ (1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = (K ^ 2 * A) * ((X ^ (Θ + 1 / 4 + ε / 4)) ^ 2 * X ^ (1 + ε / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hX.le, ← Real.rpow_add hX]
      congr 2
      push_cast
      ring

/-- P0029 pages 12 and 13, the continuous squared generating error with the prime mass
discharged. The finite prime sum uses page 14 display 4.4.
CONDITIONAL ON the explicit uniform approximation and model mass estimates. -/
theorem prime_square_error_energy {X : ℕ} (hX : 1 ≤ X) (Θ ε K A : ℝ) (hε : 0 < ε)
    (g : ℝ → ℂ) (hg : Continuous g)
    (hclose : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖SΛ (X + 1) α - g α‖ ≤ K * (X : ℝ) ^ (Θ + 1 / 4 + ε / 4))
    (hmodel : ∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2 ≤ A * (X : ℝ) ^ (1 + ε / 2))
    (s : Finset ℤ) :
    ∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ)
      (fun α => SΛ (X + 1) α ^ 2 - g α ^ 2) n‖ ^ 2 ≤
        (K ^ 2 * (2 * ((Real.log 4 + 4) / (ε / 2)) + 2 * A)) *
          (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hmass := prime_generating_mass hX (show 0 < ε / 2 by linarith)
  have hiF : IntervalIntegrable (fun α => ‖SΛ (X + 1) α‖ ^ 2) volume 0 1 :=
    ((SΛ_continuous (X + 1)).norm.pow 2).intervalIntegrable _ _
  have hiG : IntervalIntegrable (fun α => ‖g α‖ ^ 2) volume 0 1 :=
    (hg.norm.pow 2).intervalIntegrable _ _
  apply square_error_energy_of_uniform _ _ (SΛ_continuous _) hg hXr Θ ε K
    (2 * ((Real.log 4 + 4) / (ε / 2)) + 2 * A) hclose _ s
  calc
    _ ≤ ∫ α in (0 : ℝ)..1, 2 * (‖SΛ (X + 1) α‖ ^ 2 + ‖g α‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        ((((SΛ_continuous _).add hg).norm.pow 2).intervalIntegrable _ _)
        ((continuous_const.mul (((SΛ_continuous _).norm.pow 2).add
          (hg.norm.pow 2))).intervalIntegrable _ _)
      intro α _
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
    _ = 2 * (∫ α in (0 : ℝ)..1, ‖SΛ (X + 1) α‖ ^ 2) +
        2 * (∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiF hiG]
      ring
    _ ≤ 2 * (((Real.log 4 + 4) / (ε / 2)) * (X : ℝ) ^ (1 + ε / 2)) +
        2 * (A * (X : ℝ) ^ (1 + ε / 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (by norm_num))
        (mul_le_mul_of_nonneg_left hmodel (by norm_num))
    _ = _ := by ring

/-- P0029 page 14 display 4.2. Fourier coefficients on the unit interval are linear on
continuous functions. This local form is used for the model subtraction. -/
theorem coefficient_sub_continuous (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (n : ℤ) :
    fourierCoeffOn (zero_lt_one' ℝ) (fun α => f α - g α) n =
      fourierCoeffOn (zero_lt_one' ℝ) f n - fourierCoeffOn (zero_lt_one' ℝ) g n := by
  letI : Fact (0 < (1 : ℝ) - 0) := ⟨by norm_num⟩
  have hi (f : ℝ → ℂ) (hf : Continuous f) :
      IntervalIntegrable (fun α : ℝ => fourier (-n) (α : AddCircle ((1 : ℝ) - 0)) • f α)
        volume 0 1 := by
    apply Continuous.intervalIntegrable
    simp only [fourier_coe_apply, smul_eq_mul]
    fun_prop
  simp only [fourierCoeffOn_eq_integral, show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  simp_rw [smul_sub]
  exact intervalIntegral.integral_sub (hi f hf) (hi g hg)

/-- P0029 page 14 display 4.2, with finite cutoff X and coefficient index n at most X. -/
theorem weighted_count_coefficient {X n : ℕ} (hn : n ≤ X) :
    fourierCoeffOn (zero_lt_one' ℝ) (fun α => SΛ (X + 1) α ^ 2) (n : ℤ) = (r2 n : ℂ) := by
  rw [fourierCoeffOn_eq_integral, show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  calc
    _ = ∫ α in (0 : ℝ)..1, SΛ (X + 1) α ^ 2 * eC (-((n : ℝ) * α)) := by
      apply intervalIntegral.integral_congr
      intro α _
      dsimp only
      rw [fourier_coe_apply, smul_eq_mul, mul_comm]
      unfold eC
      congr 2
      push_cast
      ring
    _ = _ := r2_eq_integral (by omega)

/-- P0029 pages 12 to 14, the complete continuous model reduction for a finite subset.
CONDITIONAL ON a uniform model approximation, model mass and the lower order model
coefficient residual. No zero free implication for these inputs is asserted. -/
theorem weighted_energy_of_model {X : ℕ} (hX : 1 ≤ X) (Θ ε K A D : ℝ)
    (hΘ : 1 / 2 ≤ Θ) (hε : 0 < ε) (hD : 0 ≤ D) (g : ℝ → ℂ) (hg : Continuous g)
    (hclose : ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖SΛ (X + 1) α - g α‖ ≤ K * (X : ℝ) ^ (Θ + 1 / 4 + ε / 4))
    (hmodel : ∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2 ≤ A * (X : ℝ) ^ (1 + ε / 2))
    (s : Finset ℕ) (hs : s ⊆ range (X + 1))
    (hcoeff : ∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => g α ^ 2) (n : ℤ) -
      ((n : ℝ) * Sing n : ℝ)‖ ^ 2 ≤ D * (X : ℝ) ^ (2 + ε)) :
    ∑ n ∈ s, (error n) ^ 2 ≤
      (2 * (K ^ 2 * (2 * ((Real.log 4 + 4) / (ε / 2)) + 2 * A)) + 2 * D) *
        (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  have hspec := prime_square_error_energy hX Θ ε K A hε g hg hclose hmodel
    (s.map Nat.castEmbedding)
  rw [sum_map] at hspec
  simp only [Nat.castEmbedding_apply] at hspec
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hcoeff' : ∑ n ∈ s,
      ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => g α ^ 2) (n : ℤ) -
        ((n : ℝ) * Sing n : ℝ)‖ ^ 2 ≤ D * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    hcoeff.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hD)
  have hpoint (n : ℕ) (hn : n ∈ s) : (error n) ^ 2 ≤
      2 * (‖fourierCoeffOn (zero_lt_one' ℝ)
        (fun α => SΛ (X + 1) α ^ 2 - g α ^ 2) (n : ℤ)‖ ^ 2 +
          ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => g α ^ 2) (n : ℤ) -
            ((n : ℝ) * Sing n : ℝ)‖ ^ 2) := by
    have hnX : n ≤ X := by have := mem_range.mp (hs hn); omega
    have heq : (error n : ℂ) =
        fourierCoeffOn (zero_lt_one' ℝ) (fun α => SΛ (X + 1) α ^ 2 - g α ^ 2) (n : ℤ) +
          (fourierCoeffOn (zero_lt_one' ℝ) (fun α => g α ^ 2) (n : ℤ) -
            ((n : ℝ) * Sing n : ℝ)) := by
      rw [coefficient_sub_continuous (fun α => SΛ (X + 1) α ^ 2) (fun α => g α ^ 2)
        ((SΛ_continuous (X + 1)).pow 2) (hg.pow 2),
        weighted_count_coefficient hnX]
      simp [error]
    have hnrm : (error n) ^ 2 = ‖(error n : ℂ)‖ ^ 2 := by simp
    rw [hnrm, heq]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans add_sq_le
  calc
    _ ≤ ∑ n ∈ s, 2 * (‖fourierCoeffOn (zero_lt_one' ℝ)
        (fun α => SΛ (X + 1) α ^ 2 - g α ^ 2) (n : ℤ)‖ ^ 2 +
          ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => g α ^ 2) (n : ℤ) -
            ((n : ℝ) * Sing n : ℝ)‖ ^ 2) := sum_le_sum hpoint
    _ = 2 * (∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ)
        (fun α => SΛ (X + 1) α ^ 2 - g α ^ 2) (n : ℤ)‖ ^ 2) +
          2 * (∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => g α ^ 2) (n : ℤ) -
            ((n : ℝ) * Sing n : ℝ)‖ ^ 2) := by
      rw [← mul_sum, sum_add_distrib, mul_add]
    _ ≤ _ := by nlinarith [hspec, hcoeff']

/-- P0029 page 10, Farey order equal to the floor of square root X. For X at least four,
the floor is positive, at most square root X, and at least half square root X. -/
theorem farey_floor_bounds {X : ℝ} (hX : 4 ≤ X) :
    0 < (⌊Real.sqrt X⌋₊ : ℝ) ∧ (⌊Real.sqrt X⌋₊ : ℝ) ≤ Real.sqrt X ∧
      Real.sqrt X ≤ 2 * (⌊Real.sqrt X⌋₊ : ℝ) := by
  have hs : (2 : ℝ) ≤ Real.sqrt X := by
    nlinarith [Real.sq_sqrt (show 0 ≤ X by linarith), Real.sqrt_nonneg X]
  have hfloor : 2 ≤ ⌊Real.sqrt X⌋₊ :=
    (Nat.le_floor_iff (Real.sqrt_nonneg X)).mpr (by norm_cast)
  have hfloorR : (2 : ℝ) ≤ (⌊Real.sqrt X⌋₊ : ℝ) := by exact_mod_cast hfloor
  refine ⟨by linarith, Nat.floor_le (Real.sqrt_nonneg X), ?_⟩
  have hupper := Nat.lt_floor_add_one (Real.sqrt X)
  linarith

/-- P0029 pages 10 and 12, geometric uniformization on a Farey arc. The modulus and the
off-center square root factor together cost at most square root three times X to one quarter.
This is a bound on the geometric factor, without a zero sum estimate. -/
theorem farey_error_factor {X Q q β : ℝ} (hX : 0 < X) (hQ : 0 < Q) (hq : 0 < q)
    (hqQ : q ≤ Q) (hQsqrt : Q ≤ Real.sqrt X) (hsqrtQ : Real.sqrt X ≤ 2 * Q)
    (hβ : |β| ≤ 1 / (q * Q)) :
    Real.sqrt q * Real.sqrt (1 + X * |β|) ≤ Real.sqrt 3 * X ^ (1 / 4 : ℝ) := by
  have hβ' : |β| * (q * Q) ≤ 1 := (le_div_iff₀ (mul_pos hq hQ)).mp hβ
  have hscaled : q * X * |β| ≤ X / Q := by
    apply (le_div_iff₀ hQ).mpr
    calc
      _ = X * (|β| * (q * Q)) := by ring
      _ ≤ X * 1 := mul_le_mul_of_nonneg_left hβ' hX.le
      _ = X := by ring
  have hratio : X / Q ≤ 2 * Real.sqrt X := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith [Real.sq_sqrt hX.le,
      mul_le_mul_of_nonneg_left hsqrtQ (Real.sqrt_nonneg X)]
  have hprod : q * (1 + X * |β|) ≤ 3 * Real.sqrt X := by
    calc
      _ = q + q * X * |β| := by ring
      _ ≤ Real.sqrt X + 2 * Real.sqrt X :=
        add_le_add (hqQ.trans hQsqrt) (hscaled.trans hratio)
      _ = _ := by ring
  have hsqrt : Real.sqrt (Real.sqrt X) = X ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]
    norm_num
  calc
    _ = Real.sqrt (q * (1 + X * |β|)) := (Real.sqrt_mul hq.le _).symm
    _ ≤ Real.sqrt (3 * Real.sqrt X) := Real.sqrt_le_sqrt hprod
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), hsqrt]

/-- P0029 pages 10 and 12, a floor cutoff uniformization of a specified off-center estimate.
CONDITIONAL ON the explicit character sum error estimate. That estimate is not asserted here. -/
theorem farey_uniform_error {X q β K Θ η : ℝ} (hX : 4 ≤ X) (hq : 0 < q)
    (hqQ : q ≤ (⌊Real.sqrt X⌋₊ : ℝ))
    (hβ : |β| ≤ 1 / (q * (⌊Real.sqrt X⌋₊ : ℝ))) (hK : 0 ≤ K) (E : ℂ)
    (hE : ‖E‖ ≤ K * Real.sqrt q * X ^ (Θ + η) * Real.sqrt (1 + X * |β|)) :
    ‖E‖ ≤ (Real.sqrt 3 * K) * X ^ (Θ + 1 / 4 + η) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hQ, hQsqrt, hsqrtQ⟩ := farey_floor_bounds hX
  have hfactor := farey_error_factor hX0 hQ hq hqQ hQsqrt hsqrtQ hβ
  calc
    _ ≤ K * Real.sqrt q * X ^ (Θ + η) * Real.sqrt (1 + X * |β|) := hE
    _ = (K * X ^ (Θ + η)) * (Real.sqrt q * Real.sqrt (1 + X * |β|)) := by ring
    _ ≤ (K * X ^ (Θ + η)) * (Real.sqrt 3 * X ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg hK (Real.rpow_nonneg hX0.le _))
    _ = (Real.sqrt 3 * K) * (X ^ (Θ + η) * X ^ (1 / 4 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hX0]; congr 2; ring

/-- P0029 pages 10 to 13, the Parseval perturbation inequality for square integrable models.
This version permits measurable piecewise Farey models and an almost everywhere error bound.
CONDITIONAL ON the explicit square integrability and uniform error hypotheses. -/
theorem piecewise_square_error_bessel (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (B : ℝ) (hclose : ∀ᵐ α ∂volume.restrict (Set.Ioc (0 : ℝ) 1), ‖f α - g α‖ ≤ B)
    (s : Finset ℤ) :
    ∑ n ∈ s, ‖fourierCoeffOn (zero_lt_one' ℝ) (fun α => f α ^ 2 - g α ^ 2) n‖ ^ 2 ≤
      B ^ 2 * ∫ α in (0 : ℝ)..1, ‖f α + g α‖ ^ 2 := by
  have hdiff : MemLp (fun α => f α - g α) ⊤
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable) B hclose
  have hsum : MemLp (fun α => f α + g α) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := hf.add hg
  have hL2 : MemLp (fun α => f α ^ 2 - g α ^ 2) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    convert hsum.mul hdiff using 1
    · ext α
      dsimp only [Pi.mul_apply]
      ring
    · infer_instance
  have hi1 : Integrable (fun α => ‖f α ^ 2 - g α ^ 2‖ ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
  have hi2 : Integrable (fun α => ‖f α + g α‖ ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).mp hsum
  have hpoint : ∀ᵐ α ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      ‖f α ^ 2 - g α ^ 2‖ ^ 2 ≤ B ^ 2 * ‖f α + g α‖ ^ 2 := by
    filter_upwards [hclose] with α hα
    rw [show f α ^ 2 - g α ^ 2 = (f α - g α) * (f α + g α) by ring, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hα 2) (sq_nonneg _)
  have hbessel := sum_le_hasSum s (fun _ _ => sq_nonneg _)
    (hasSum_sq_fourierCoeffOn (zero_lt_one' ℝ) hL2)
  calc
    _ ≤ ∫ α in (0 : ℝ)..1, ‖f α ^ 2 - g α ^ 2‖ ^ 2 := by simpa using hbessel
    _ ≤ _ := by
      simp only [intervalIntegral.integral_of_le zero_le_one]
      rw [← integral_const_mul]
      exact integral_mono_ae hi1 (hi2.const_mul _) hpoint

section CharacterBounds

open LeanLab.PNTPort.DirichletZF Complex Metric

/-- P0029 page 11 display 3.5, an auxiliary growth bound for the contour shift. This widens
the existing local growth disc to radius one while keeping its uniform conductor factor. -/
theorem nonprincipal_disc_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖DirichletCharacter.LFunction χ (z + ((3 : ℂ) / 2 + I * t))‖ ≤
      2 * q * (|t| + 3) := by
  let s : ℂ := z + ((3 : ℂ) / 2 + I * t)
  have hsre : (1 / 2 : ℝ) ≤ s.re := by
    have hzre : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
    dsimp only [s]
    rw [Complex.add_re, re_c]
    linarith [(abs_le.mp hzre).1]
  have hs0 : 0 < s.re := by linarith
  have hsnorm : ‖s‖ ≤ |t| + 3 := by
    have h1 : ‖(3 : ℂ) / 2‖ = (3 / 2 : ℝ) := by norm_num
    have h2 : ‖I * (t : ℂ)‖ = |t| := by simp
    calc
      ‖s‖ ≤ ‖z‖ + (‖(3 : ℂ) / 2‖ + ‖I * (t : ℂ)‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ _ := by rw [h1, h2]; linarith
  calc
    _ ≤ (q : ℝ) * ‖s‖ / s.re := norm_LFunction_le hχ hs0
    _ ≤ (q : ℝ) * (|t| + 3) / s.re :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsnorm (Nat.cast_nonneg q)) hs0.le
    _ ≤ _ := by
      apply (div_le_iff₀ hs0).mpr
      calc
        _ = (2 * q * (|t| + 3)) * (1 / 2 : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsre (by positivity)

/-- P0029 pages 11 and 12, a contour input under the paper zero free hypothesis.
Every fixed positive distance to the right of Theta gives a logarithmic derivative bound
uniform in the conductor and height. CONDITIONAL ON the stated ZeroFreeBeyond hypothesis. -/
theorem logDerivative_from_zeroFree (Θ : ℝ) (hΘ : 1 / 2 ≤ Θ) (hZF : ZeroFreeBeyond Θ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : Θ + δ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, Θ + δ ≤ σ → σ ≤ 2 →
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * t) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + I * t)‖ ≤ C * Real.log (Bt q t) := by
  let rp : ℝ := 3 / 2 - Θ - δ
  let r : ℝ := 3 / 2 - Θ - 3 * δ / 4
  let Rp : ℝ := 3 / 2 - Θ - δ / 2
  let R : ℝ := 3 / 2 - Θ - δ / 4
  have hrp : 0 < rp := by dsimp [rp]; linarith
  have hrrp : rp < r := by dsimp [rp, r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrRp : r < Rp := by dsimp [r, Rp]; linarith
  have hRpR : Rp < R := by dsimp [Rp, R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  let K : ℝ := 16 * r ^ 2 / (r - rp) ^ 3 +
    1 / ((R ^ 2 / Rp - Rp) * Real.log (R / Rp))
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q _ χ hχ σ t hσ hσ2
  let c : ℂ := (3 : ℂ) / 2 + I * t
  let f : ℂ → ℂ := fShift χ t
  let g : ℂ → ℂ := fun w => f w / f 0
  let z : ℂ := ((σ : ℂ) + I * t) - c
  have hf0 : f 0 ≠ 0 := fShift_zero_ne χ t
  have hg0 : g 0 = 1 := by simp [g, hf0]
  have hgAnalytic : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    fun w _ => (fShift_analyticAt hχ t w).div_const
  have hzeros : ∀ a : ℝ, SetOfZeros a g = SetOfZeros a f := by
    intro a
    ext w
    simp [SetOfZeros, g, hf0]
  have hgFinite : (SetOfZeros 1 g).Finite := by
    rw [hzeros]
    exact fShift_finite_zeros hχ t
  have hgBound : ∀ w : ℂ, ‖w‖ ≤ R → ‖g w‖ ≤ Bt q t := by
    intro w hw
    have h1 : ‖f w‖ ≤ 2 * q * (|t| + 3) :=
      nonprincipal_disc_bound hχ t (hw.trans hR1.le)
    have h2 := norm_LFunction_ge χ t
    have hf0norm : ‖f 0‖ = ‖DirichletCharacter.LFunction χ c‖ := by simp [f, fShift, c]
    have hlower : 1 ≤ Z * ‖f 0‖ := by
      rw [hf0norm]
      simpa only [mul_comm] using (div_le_iff₀ Z_pos).mp h2
    change ‖f w / f 0‖ ≤ _
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hf0)]
    calc
      _ ≤ 2 * q * (|t| + 3) := h1
      _ ≤ (2 * q * (|t| + 3)) * (Z * ‖f 0‖) :=
        le_mul_of_one_le_right (by positivity) hlower
      _ = _ := by unfold Bt; ring
  have hLnonzero (s : ℂ) (hs : Θ < s.re) : DirichletCharacter.LFunction χ s ≠ 0 := by
    by_cases hs1 : s = 1
    · rw [hs1]
      exact DirichletCharacter.LFunction_apply_one_ne_zero hχ
    · exact hZF q χ s hs hs1
  have hgNonzero (w : ℂ) (hw : ‖w‖ ≤ Rp) : g w ≠ 0 := by
    have hwre : |w.re| ≤ Rp := (Complex.abs_re_le_norm w).trans hw
    have hs : Θ < (w + c).re := by
      rw [Complex.add_re, show c.re = (3 / 2 : ℝ) from re_c t]
      have hl := (abs_le.mp hwre).1
      dsimp [Rp] at hl
      linarith
    change f w / f 0 ≠ 0
    exact div_ne_zero (hLnonzero (w + c) hs) hf0
  have hzNorm : ‖z‖ ≤ rp := by
    have heq : z = ((σ - 3 / 2 : ℝ) : ℂ) := by dsimp [z, c]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp [rp]
    constructor <;> linarith
  have hzNotZero : z ∉ SetOfZeros Rp g := fun hz => hgNonzero z hz.1 hz.2
  have key := FinalBound (B := Bt q t) (r' := rp) (r := r) (R' := Rp) (R := R)
    (f := g) (z := z) (one_lt_Bt t) hrp hrrp hr1 hrRp hRpR hR1
    hgAnalytic hg0 hgFinite hgBound ⟨mem_closedBall_zero_iff.mpr hzNorm, hzNotZero⟩
  have hsum : ∑ ρ ∈ (finiteSetOfZeros_mono hr1 hgFinite).toFinset,
      analyticOrderNatAt g ρ / (z - ρ) = 0 := by
    apply Finset.sum_eq_zero
    intro ρ hρ
    have hρ' : ‖ρ‖ ≤ r ∧ g ρ = 0 := (finiteSetOfZeros_mono hr1 hgFinite).mem_toFinset.mp hρ
    exact False.elim (hgNonzero ρ (hρ'.1.trans hrRp.le) hρ'.2)
  rw [hsum, sub_zero] at key
  have hfz : f z ≠ 0 := by
    intro h
    apply hgNonzero z (hzNorm.trans (hrrp.le.trans hrRp.le))
    simp [g, h]
  have hgDeriv : deriv g z / g z = deriv f z / f z := by
    have hd : deriv g z = deriv f z / f 0 := by
      dsimp only [g]
      rw [deriv_div_const]
    rw [hd]
    dsimp only [g]
    field_simp
  have he : z + c = (σ : ℂ) + I * t := by dsimp [z]; ring
  have hv : f z = DirichletCharacter.LFunction χ ((σ : ℂ) + I * t) := by
    change DirichletCharacter.LFunction χ (z + c) = _
    rw [he]
  have hdv : deriv f z = deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + I * t) := by
    change deriv (fun w => DirichletCharacter.LFunction χ (w + c)) z = _
    rw [deriv_comp_add_const, he]
  rw [hgDeriv, hv, hdv] at key
  calc
    _ ≤ K * Real.log (Bt q t) := key
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.log_pos (one_lt_Bt t)).le

#print axioms logDerivative_from_zeroFree
#print axioms nonprincipal_disc_bound

end CharacterBounds

/-- P0029 pages 10 and 11, an argument estimate for the off-center Gamma factor.
The loss from replacing the argument of a plus it by pi over two is uniformly at most a. -/
theorem arg_exponential_loss (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    t * (Real.pi / 2 - Complex.arg ((a : ℂ) + Complex.I * t)) ≤ a := by
  have hargabs : |Complex.arg ((a : ℂ) + Complex.I * t)| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    left
    simpa using ha
  have harg : Complex.arg ((a : ℂ) + Complex.I * t) = Real.arctan (t / a) := by
    have h := Real.arctan_tan (abs_lt.mp hargabs).1 (abs_lt.mp hargabs).2
    rw [Complex.tan_arg] at h
    simpa using h.symm
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · simp [← ht0, ha.le]
  have hinv : Real.pi / 2 - Complex.arg ((a : ℂ) + Complex.I * t) = Real.arctan (a / t) := by
    rw [harg, ← Real.arctan_inv_of_pos (div_pos htpos ha)]
    congr 1
    field_simp
  rw [hinv]
  calc
    _ ≤ t * (a / t) := mul_le_mul_of_nonneg_left (Real.arctan_le_self (by positivity)) ht
    _ = a := by field_simp

section GammaSupply

open Complex Set

/-- P0029 page 11, the displayed damped Gamma integral immediately before display 3.5. -/
theorem damped_gamma_integral {N : ℝ} (hN : 0 < N) {ρ : ℂ} (hρ : 0 < ρ.re) :
    (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t / N) : ℝ) : ℂ) * (t : ℂ) ^ (ρ - 1)) =
      Complex.Gamma ρ * (N : ℂ) ^ ρ := by
  simpa [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_inv,
    div_eq_mul_inv, mul_comm] using
      (Complex.integral_cpow_mul_exp_neg_mul_Ioi hρ (inv_pos.mpr hN))

/-- P0029 page 11, a uniform integrable majorant for the Gamma factor on the strip needed
by Mellin inversion. The constant is derived from the existing exponential strip bound. -/
theorem gamma_vertical_decay (σ t : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    ‖Complex.Gamma ((σ : ℂ) + Complex.I * t)‖ ≤
      (19 * Real.sqrt (2 * Real.pi)) / (1 + t ^ 2) := by
  let u : ℝ := |t|
  have hu : 0 ≤ u := abs_nonneg t
  have hsym : ‖Complex.Gamma ((σ : ℂ) + I * t)‖ =
      ‖Complex.Gamma ((σ : ℂ) + I * u)‖ := by
    by_cases ht : 0 ≤ t
    · simp [u, abs_of_nonneg ht]
    · have he : ((σ : ℂ) + I * t) = star ((σ : ℂ) + I * (-t)) := by
        apply Complex.ext <;> simp
      have hn : ‖Complex.Gamma (star ((σ : ℂ) + I * (-t)))‖ =
          ‖Complex.Gamma ((σ : ℂ) + I * (-t))‖ := by
        change ‖Complex.Gamma (starRingEnd ℂ _)‖ = _
        rw [Complex.Gamma_conj]
        exact norm_star _
      calc
        _ = ‖Complex.Gamma (star ((σ : ℂ) + I * (-t)))‖ := congrArg (fun z => ‖Complex.Gamma z‖) he
        _ = _ := by simpa only [u, abs_of_neg (lt_of_not_ge ht), Complex.ofReal_neg] using hn
  have hnorm : ‖((σ : ℂ) + I * u) + 1‖ ≤ u + 4 := by
    have he : ((σ : ℂ) + I * u) + 1 = ((σ + 1 : ℝ) : ℂ) + I * u := by
      push_cast
      ring
    rw [he]
    calc
      _ ≤ |σ + 1| + |u| := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul]
          using norm_add_le (((σ + 1 : ℝ) : ℂ)) (I * (u : ℂ))
      _ ≤ _ := by rw [abs_of_pos (by linarith : 0 < σ + 1), abs_of_nonneg hu]; linarith
  have hcoarse : ‖Complex.Gamma ((σ : ℂ) + I * t)‖ ≤
      Real.sqrt (2 * Real.pi) * (u + 4) * Real.exp (-(Real.pi * u / 2)) := by
    rw [hsym]
    have h := LeanLab.PNTPort.ZetaZeros.norm_Gamma_le_PL
      (s := (σ : ℂ) + I * u) (by simpa using hσ) (by simpa using hσ')
    calc
      _ ≤ Real.sqrt (2 * Real.pi) * ‖((σ : ℂ) + I * u) + 1‖ *
          Real.exp (-(Real.pi * u / 2)) := by simpa using h
      _ ≤ _ := by gcongr
  have hp1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hp2 := Real.pow_div_factorial_le_exp u hu 2
  have hp3 := Real.pow_div_factorial_le_exp u hu 3
  norm_num at hp2 hp3
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hsquare : t ^ 2 = u ^ 2 := by dsimp [u]; rw [sq_abs]
  have hpoly : (u + 4) * (1 + t ^ 2) ≤ 19 * Real.exp u := by
    rw [hsquare]
    nlinarith
  have hexp : Real.exp u * Real.exp (-(Real.pi * u / 2)) ≤ 1 := by
    rw [← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    have hπ : 0 ≤ Real.pi / 2 - 1 := by linarith [Real.pi_gt_three]
    nlinarith [mul_nonneg hπ hu]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).mpr
  calc
    _ ≤ (Real.sqrt (2 * Real.pi) * (u + 4) * Real.exp (-(Real.pi * u / 2))) * (1 + t ^ 2) :=
      mul_le_mul_of_nonneg_right hcoarse (by positivity)
    _ = Real.sqrt (2 * Real.pi) * ((u + 4) * (1 + t ^ 2)) * Real.exp (-(Real.pi * u / 2)) := by ring
    _ ≤ Real.sqrt (2 * Real.pi) * (19 * Real.exp u) * Real.exp (-(Real.pi * u / 2)) := by gcongr
    _ = (19 * Real.sqrt (2 * Real.pi)) * (Real.exp u * Real.exp (-(Real.pi * u / 2))) := by ring
    _ ≤ (19 * Real.sqrt (2 * Real.pi)) * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

/-- P0029 page 11, absolute vertical convergence of the Gamma Mellin kernel. -/
theorem gamma_vertical_integrable (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    Complex.VerticalIntegrable Complex.Gamma σ := by
  have hc : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro m he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  change Integrable (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I))
  apply (integrable_inv_one_add_sq.const_mul (19 * Real.sqrt (2 * Real.pi))).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with t
  simpa only [mul_comm (t : ℂ) I, div_eq_mul_inv] using gamma_vertical_decay σ t hσ hσ'

/-- P0029 page 11, the inverse Mellin Gamma kernel for positive real arguments. -/
theorem mellinInv_Gamma (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    {x : ℝ} (hx : 0 < x) :
    mellinInv σ Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  let f : ℝ → ℂ := fun t => (Real.exp (-t) : ℂ)
  have hσpos : 0 < σ := by linarith
  have hline (t : ℝ) : mellin f ((σ : ℂ) + t * I) =
      Complex.Gamma ((σ : ℂ) + t * I) := by
    rw [← Complex.GammaIntegral_eq_mellin]
    exact (Complex.Gamma_eq_integral (by simpa using hσpos)).symm
  have hf : MellinConvergent f (σ : ℂ) := by
    simpa only [MellinConvergent, f, smul_eq_mul, mul_comm] using
      Complex.GammaIntegral_convergent (s := (σ : ℂ)) (by simpa using hσpos)
  have hF : Complex.VerticalIntegrable (mellin f) σ := by
    change Integrable (fun t : ℝ => mellin f ((σ : ℂ) + t * I))
    simp_rw [hline]
    exact gamma_vertical_integrable σ hσ hσ'
  have h := mellinInv_mellin_eq σ f hx hf hF (by dsimp [f]; fun_prop)
  change mellinInv σ Complex.Gamma x = f x
  rw [← h]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun t => by dsimp only; rw [hline]

/-- P0029 pages 10 and 11, a normalized Gamma bound with the sharp strip polynomial. -/
theorem gamma_normalized_strip {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖Complex.Gamma s * Complex.exp (s - (s - 1 / 2) * Complex.log (s + 1))‖ ≤
      Real.exp (3 / 2) * Real.sqrt (2 * Real.pi) := by
  let g : ℂ → ℂ := fun z => Complex.Gamma z * Complex.exp (z - (z - 1 / 2) * Complex.log (z + 1))
  have hn (z : ℂ) : ‖g z‖ = ‖Complex.Gamma z‖ *
      Real.exp (z.re - (z.re - 1 / 2) * Real.log ‖z + 1‖ + z.im * Complex.arg (z + 1)) := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp only [Complex.sub_re, Complex.mul_re, Complex.log_re, Complex.log_im,
      Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
    ring
  have hden (z : ℂ) (hz : 1 / 2 ≤ z.re) : 1 ≤ ‖z + 1‖ := by
    have h := Complex.re_le_norm (z + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have harg (z : ℂ) (hz : 1 / 2 ≤ z.re) :
      z.im * Complex.arg (z + 1) ≤ Real.pi * |z.im| / 2 := by
    have ha : |Complex.arg (z + 1)| ≤ Real.pi / 2 := by
      apply Complex.abs_arg_le_pi_div_two_iff.mpr
      simp only [Complex.add_re, Complex.one_re]
      linarith
    calc
      _ ≤ |z.im * Complex.arg (z + 1)| := le_abs_self _
      _ = |z.im| * |Complex.arg (z + 1)| := abs_mul _ _
      _ ≤ |z.im| * (Real.pi / 2) := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
      _ = _ := by ring
  have hconj (z : ℂ) : ‖Complex.Gamma (star z)‖ = ‖Complex.Gamma z‖ := by
    change ‖Complex.Gamma (starRingEnd ℂ z)‖ = _
    rw [Complex.Gamma_conj]
    exact norm_star _
  have hhalf (t : ℝ) : ‖Complex.Gamma (1 / 2 + t * I)‖ *
      Real.exp (Real.pi * |t| / 2) ≤ Real.sqrt (2 * Real.pi) := by
    by_cases ht : 0 ≤ t
    · simpa only [abs_of_nonneg ht] using LeanLab.PNTPort.ZetaZeros.norm_Gamma_half_mul_exp_le t
    · have he : (1 / 2 + t * I : ℂ) = star (1 / 2 + (-t : ℝ) * I) := by
        apply Complex.ext <;> simp
      rw [he, hconj]
      simpa only [abs_of_neg (lt_of_not_ge ht)] using
        LeanLab.PNTPort.ZetaZeros.norm_Gamma_half_mul_exp_le (-t)
  have hdiff (z : ℂ) (hz : 0 < z.re) : DifferentiableAt ℂ g z := by
    have hGamma : DifferentiableAt ℂ Complex.Gamma z := by
      apply Complex.differentiableAt_Gamma
      intro m he
      have hr := congrArg Complex.re he
      simp at hr
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hlog : DifferentiableAt ℂ (fun w : ℂ => Complex.log (w + 1)) z := by
      apply (Complex.differentiableAt_log ?_).comp z (by fun_prop)
      apply Complex.mem_slitPlane_iff.mpr
      left
      simpa only [Complex.add_re, Complex.one_re] using (by linarith : 0 < z.re + 1)
    dsimp only [g]
    fun_prop
  have hcl : closure (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (3 / 2)) ⊆
      {z : ℂ | 0 < z.re} := by
    have hc := closure_minimal (preimage_mono Set.Ioo_subset_Icc_self :
      Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (3 / 2) ⊆ Complex.re ⁻¹' Set.Icc (1 / 2 : ℝ) (3 / 2))
      (isClosed_Icc.preimage Complex.continuous_re)
    intro z hz
    have hz' := hc hz
    simp only [Set.mem_preimage, Set.mem_Icc] at hz'
    change 0 < z.re
    linarith [hz'.1]
  have hfd : DiffContOnCl ℂ g (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (3 / 2)) :=
    DifferentiableOn.diffContOnCl (fun z hz => (hdiff z (hcl hz)).differentiableWithinAt)
  let K : ℝ := Real.Gamma (1 / 2) + Real.Gamma (3 / 2)
  have hK : 0 ≤ K := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    dsimp [K]
    positivity
  have hB : ∃ c < Real.pi / ((3 / 2 : ℝ) - 1 / 2), ∃ B,
      g =O[Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
        𝓟 (Complex.re ⁻¹' Set.Ioo (1 / 2 : ℝ) (3 / 2))]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, by have := Real.pi_gt_three; norm_num; linarith, Real.pi + 2, ?_⟩
    apply Asymptotics.IsBigO.of_bound K
    apply Filter.eventually_inf_principal.mpr
    apply Eventually.of_forall
    intro z hz
    simp only [Set.mem_preimage, Set.mem_Ioo] at hz
    have hlog := Real.log_nonneg (hden z hz.1.le)
    have hterm : 0 ≤ (z.re - 1 / 2) * Real.log ‖z + 1‖ := mul_nonneg (by linarith) hlog
    have he1 : 1 ≤ Real.exp |z.im| := Real.one_le_exp_iff.mpr (abs_nonneg _)
    have he2 : |z.im| ≤ Real.exp |z.im| := by linarith [Real.add_one_le_exp |z.im|]
    have he : z.re - (z.re - 1 / 2) * Real.log ‖z + 1‖ + z.im * Complex.arg (z + 1) ≤
        (Real.pi + 2) * Real.exp (1 * |z.im|) := by
      rw [one_mul]
      have ha := harg z hz.1.le
      have hπ := Real.pi_pos
      have habs := abs_nonneg z.im
      nlinarith
    rw [hn, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul (LeanLab.PNTPort.ZetaZeros.norm_Gamma_strip_le hz.1.le hz.2.le)
      (Real.exp_le_exp.mpr he) (Real.exp_pos _).le hK
  apply PhragmenLindelof.vertical_strip hfd hB _ _ h1 h2
  · intro z hz
    have hzre : z.re = 1 / 2 := hz
    have he : z = 1 / 2 + z.im * I := by apply Complex.ext <;> simp [hzre]
    have ha := harg z (by linarith)
    have hga : ‖Complex.Gamma z‖ * Real.exp (z.im * Complex.arg (z + 1)) ≤
        Real.sqrt (2 * Real.pi) := by
      calc
        _ ≤ ‖Complex.Gamma z‖ * Real.exp (Real.pi * |z.im| / 2) := by gcongr
        _ ≤ _ := by convert hhalf z.im using 1; rw [← he]
    rw [hn, hzre]
    simp only [sub_self, zero_mul, sub_zero, Real.exp_add]
    calc
      _ = Real.exp (1 / 2) * (‖Complex.Gamma z‖ * Real.exp (z.im * Complex.arg (z + 1))) := by ring
      _ ≤ Real.exp (1 / 2) * Real.sqrt (2 * Real.pi) := mul_le_mul_of_nonneg_left hga (Real.exp_pos _).le
      _ ≤ _ := by gcongr <;> norm_num
  · intro z hz
    have hzre : z.re = 3 / 2 := hz
    have he : z = 3 / 2 + z.im * I := by apply Complex.ext <;> simp [hzre]
    have hgamma : ‖Complex.Gamma z‖ ≤ ‖z + 1‖ * ‖Complex.Gamma (1 / 2 + z.im * I)‖ := by
      have hrec : Complex.Gamma z = (1 / 2 + z.im * I) * Complex.Gamma (1 / 2 + z.im * I) := by
        have he' : z = (1 / 2 + z.im * I) + 1 := by
          apply Complex.ext <;> simp [hzre] <;> norm_num
        calc
          _ = Complex.Gamma ((1 / 2 + z.im * I) + 1) := congrArg Complex.Gamma he'
          _ = _ := Complex.Gamma_add_one _ (by intro h; have hr := congrArg Complex.re h; norm_num at hr)
      rw [hrec, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [Complex.norm_def, Complex.norm_def]
      apply Real.sqrt_le_sqrt
      simp [Complex.normSq_apply, hzre]
      nlinarith
    have ha := harg z (by linarith)
    have hga : ‖Complex.Gamma (1 / 2 + z.im * I)‖ * Real.exp (z.im * Complex.arg (z + 1)) ≤
        Real.sqrt (2 * Real.pi) := by
      calc
        _ ≤ ‖Complex.Gamma (1 / 2 + z.im * I)‖ * Real.exp (Real.pi * |z.im| / 2) := by gcongr
        _ ≤ _ := hhalf z.im
    have hnorm : 0 < ‖z + 1‖ := lt_of_lt_of_le (by norm_num) (hden z (by linarith))
    rw [hn, hzre]
    norm_num only [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, one_mul]
    calc
      _ ≤ (‖z + 1‖ * ‖Complex.Gamma (1 / 2 + z.im * I)‖) *
          Real.exp (3 / 2 - Real.log ‖z + 1‖ + z.im * Complex.arg (z + 1)) :=
        mul_le_mul_of_nonneg_right hgamma (Real.exp_pos _).le
      _ = Real.exp (3 / 2) * (‖Complex.Gamma (1 / 2 + z.im * I)‖ *
          Real.exp (z.im * Complex.arg (z + 1))) := by
        rw [Real.exp_add, Real.exp_sub, Real.exp_log hnorm]
        field_simp
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hga (Real.exp_pos _).le

/-- P0029 pages 10 and 11, uniform Gamma decay with the sharp strip polynomial factor. -/
theorem gamma_stirling_strip (σ t : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2) :
    ‖Complex.Gamma ((σ : ℂ) + I * t)‖ ≤
      (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) *
        (|t| + 3) ^ (σ - 1 / 2) * Real.exp (-(Real.pi * |t| / 2)) := by
  have hpos {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) (ht : 0 ≤ s.im) :
      ‖Complex.Gamma s‖ ≤ (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) *
        ‖s + 1‖ ^ (s.re - 1 / 2) * Real.exp (-(Real.pi * s.im / 2)) := by
    have hnorm : 0 < ‖s + 1‖ := by
      have hr := Complex.re_le_norm (s + 1)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith
    have hb := gamma_normalized_strip h1 h2
    rw [norm_mul, Complex.norm_exp] at hb
    have hre : (s - (s - 1 / 2) * Complex.log (s + 1)).re =
        s.re - (s.re - 1 / 2) * Real.log ‖s + 1‖ + s.im * Complex.arg (s + 1) := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.log_re, Complex.log_im,
        Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re, Complex.one_im]
      ring
    rw [hre] at hb
    have ha := arg_exponential_loss (s.re + 1) s.im (by linarith) ht
    have he : ((s.re + 1 : ℝ) : ℂ) + I * s.im = s + 1 := by
      apply Complex.ext <;> simp
    rw [he] at ha
    have hdiv := (le_div_iff₀ (Real.exp_pos _)).mpr hb
    rw [div_eq_mul_inv, ← Real.exp_neg] at hdiv
    calc
      _ ≤ (Real.exp (3 / 2) * Real.sqrt (2 * Real.pi)) *
          Real.exp (-(s.re - (s.re - 1 / 2) * Real.log ‖s + 1‖ + s.im * Complex.arg (s + 1))) := hdiv
      _ ≤ (Real.exp (3 / 2) * Real.sqrt (2 * Real.pi)) *
          Real.exp (1 + (s.re - 1 / 2) * Real.log ‖s + 1‖ - Real.pi * s.im / 2) := by
        gcongr
        nlinarith
      _ = _ := by
        rw [Real.rpow_def_of_pos hnorm]
        have he : Real.exp (3 / 2) *
            Real.exp (1 + (s.re - 1 / 2) * Real.log ‖s + 1‖ - Real.pi * s.im / 2) =
            Real.exp (5 / 2) * Real.exp (Real.log ‖s + 1‖ * (s.re - 1 / 2)) *
              Real.exp (-(Real.pi * s.im / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc
          _ = Real.sqrt (2 * Real.pi) * (Real.exp (3 / 2) *
              Real.exp (1 + (s.re - 1 / 2) * Real.log ‖s + 1‖ - Real.pi * s.im / 2)) := by ring
          _ = _ := by rw [he]; ring
  let u : ℝ := |t|
  have hu : 0 ≤ u := abs_nonneg _
  have hsym : ‖Complex.Gamma ((σ : ℂ) + I * t)‖ =
      ‖Complex.Gamma ((σ : ℂ) + I * u)‖ := by
    by_cases ht : 0 ≤ t
    · simp [u, abs_of_nonneg ht]
    · have he : ((σ : ℂ) + I * t) = star ((σ : ℂ) + I * (-t)) := by
        apply Complex.ext <;> simp
      have hn : ‖Complex.Gamma (star ((σ : ℂ) + I * (-t)))‖ =
          ‖Complex.Gamma ((σ : ℂ) + I * (-t))‖ := by
        change ‖Complex.Gamma (starRingEnd ℂ _)‖ = _
        rw [Complex.Gamma_conj]
        exact norm_star _
      calc
        _ = ‖Complex.Gamma (star ((σ : ℂ) + I * (-t)))‖ := congrArg (fun z => ‖Complex.Gamma z‖) he
        _ = _ := by simpa only [u, abs_of_neg (lt_of_not_ge ht), Complex.ofReal_neg] using hn
  have hn : ‖((σ : ℂ) + I * u) + 1‖ ≤ u + 3 := by
    have hb := Complex.norm_le_abs_re_add_abs_im (((σ : ℂ) + I * u) + 1)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.one_re,
      Complex.add_im, Complex.mul_im, zero_add, one_mul, mul_one, Complex.one_im, add_zero] at hb
    rw [abs_of_pos (by linarith : 0 < σ + 1), abs_of_nonneg hu] at hb
    linarith
  rw [hsym]
  have hb := hpos (s := (σ : ℂ) + I * u) (by simpa using hσ) (by simpa using hσ') (by simpa using hu)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, one_mul, mul_one] at hb
  exact hb.trans (by gcongr)

/-- P0029 pages 10 and 11, the complete off-center Gamma Mellin kernel majorant. -/
theorem gamma_mellin_kernel_bound (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    (z : ℂ) (hz : 0 < z.re) :
    0 < Real.pi / 2 - |Complex.arg z| ∧ ∀ t : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ ≤
        (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ) *
          (|t| + 3) ^ (σ - 1 / 2) *
            Real.exp (-((Real.pi / 2 - |Complex.arg z|) * |t|)) := by
  have harg : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  refine ⟨by linarith, ?_⟩
  intro t
  have hp : ‖z ^ (-((σ : ℂ) + I * t))‖ = ‖z‖ ^ (-σ) * Real.exp (Complex.arg z * t) := by
    rw [Complex.norm_cpow_of_ne_zero hz0]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.neg_im, Complex.add_im, Complex.mul_im, zero_add, one_mul, mul_one]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  have ha : Complex.arg z * t ≤ |Complex.arg z| * |t| := by
    simpa only [abs_mul] using le_abs_self (Complex.arg z * t)
  rw [norm_mul, hp]
  calc
    _ ≤ ((Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) *
        (|t| + 3) ^ (σ - 1 / 2) * Real.exp (-(Real.pi * |t| / 2))) *
        (‖z‖ ^ (-σ) * Real.exp (Complex.arg z * t)) :=
      mul_le_mul_of_nonneg_right (gamma_stirling_strip σ t hσ hσ') (by positivity)
    _ = (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ) *
        (|t| + 3) ^ (σ - 1 / 2) * Real.exp (-(Real.pi * |t| / 2) + Complex.arg z * t) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      gcongr
      nlinarith

/-- P0029 page 10, quantitative argument gap for the damped right half plane parameter. -/
theorem right_half_plane_arg_gap (z : ℂ) (hz : 0 < z.re) :
    z.re / ‖z‖ ≤ Real.pi / 2 - |Complex.arg z| := by
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have ha : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  calc
    _ = Real.cos (Complex.arg z) := (Complex.cos_arg hz0).symm
    _ = Real.sin (Real.pi / 2 - |Complex.arg z|) := by rw [Real.sin_pi_div_two_sub, Real.cos_abs]
    _ ≤ _ := Real.sin_le (by linarith)

/-- P0029 pages 10 and 11, absolute convergence of the complete off-center Gamma kernel. -/
theorem gamma_mellin_kernel_integrable (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => Complex.Gamma ((σ : ℂ) + I * t) *
      z ^ (-((σ : ℂ) + I * t))) := by
  let δ : ℝ := Real.pi / 2 - |Complex.arg z|
  have hδ : 0 < δ := (gamma_mellin_kernel_bound σ hσ hσ' z hz).1
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hlin : IntegrableOn (fun t : ℝ => t * Real.exp (-δ * t)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (b := δ) (by norm_num) (by norm_num) hδ
  have he : IntegrableOn (fun t : ℝ => Real.exp (-δ * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hδ) 0
  have hi : IntegrableOn (fun t : ℝ => (t + 3) * Real.exp (-δ * t)) (Set.Ioi 0) := by
    convert hlin.add (he.const_mul 3) using 1
    ext t
    dsimp only [Pi.add_apply]
    ring
  have hpos : IntegrableOn (fun t : ℝ => (|t| + 3) * Real.exp (-δ * |t|)) (Set.Ioi 0) :=
    hi.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hneg : IntegrableOn (fun t : ℝ => (|t| + 3) * Real.exp (-δ * |t|)) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hpos
  have hiAll : Integrable (fun t : ℝ => (|t| + 3) * Real.exp (-δ * |t|)) := by
    have h := hneg.union hpos
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h
  have hc : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + I * t) *
      z ^ (-((σ : ℂ) + I * t))) := by
    have hg : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + I * t)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
      intro m he
      have hr := congrArg Complex.re he
      simp at hr
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact hg.mul ((continuous_const_cpow' hz0).comp (by fun_prop))
  apply (hiAll.const_mul ((Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ))).mono'
    hc.aestronglyMeasurable
  filter_upwards [] with t
  have hp : (|t| + 3) ^ (σ - 1 / 2) ≤ |t| + 3 :=
    Real.rpow_le_self_of_one_le (by linarith [abs_nonneg t]) (by linarith)
  have hb := (gamma_mellin_kernel_bound σ hσ hσ' z hz).2 t
  apply hb.trans
  simp only [← neg_mul]
  calc
    _ ≤ ((Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ)) *
        (|t| + 3) * Real.exp (-δ * |t|) :=
      by simpa only [δ, neg_mul] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
          (by positivity : 0 ≤ (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ)))
          (Real.exp_pos (-δ * |t|)).le
    _ = _ := by ring

/-- P0029 pages 10 and 11, an explicit norm integral bound for the off-center Gamma kernel. -/
theorem gamma_mellin_kernel_L1_bound (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ, ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) ≤
      2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ) *
        ((1 / (Real.pi / 2 - |Complex.arg z|)) ^ (σ + 1 / 2) * Real.Gamma (σ + 1 / 2) +
          3 ^ (σ - 1 / 2) / (Real.pi / 2 - |Complex.arg z|)) := by
  let δ : ℝ := Real.pi / 2 - |Complex.arg z|
  let a : ℝ := σ - 1 / 2
  let K : ℝ := (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ)
  let F : ℝ → ℝ := fun t => (t ^ a + 3 ^ a) * Real.exp (-δ * t)
  have hδ : 0 < δ := (gamma_mellin_kernel_bound σ hσ hσ' z hz).1
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a ≤ 1 := by dsimp [a]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpow : IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-δ * t)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := a) (p := 1) (b := δ) (by linarith) (by norm_num) hδ
  have he : IntegrableOn (fun t : ℝ => Real.exp (-δ * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hδ) 0
  have hi : IntegrableOn F (Set.Ioi 0) := by
    convert hpow.add (he.const_mul (3 ^ a)) using 1
    ext t
    dsimp only [F, Pi.add_apply]
    ring
  have hpos : IntegrableOn (fun t : ℝ => F |t|) (Set.Ioi 0) :=
    hi.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hneg : IntegrableOn (fun t : ℝ => F |t|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hpos
  have hiAll : Integrable (fun t : ℝ => F |t|) := by
    have h := hneg.union hpos
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h
  have hmass : (∫ t : ℝ, F |t|) = 2 *
      ((1 / δ) ^ (σ + 1 / 2) * Real.Gamma (σ + 1 / 2) + 3 ^ a / δ) := by
    rw [integral_comp_abs]
    congr 1
    have hpc : (∫ t : ℝ in Set.Ioi 0, t ^ a * Real.exp (-δ * t)) =
        (1 / δ) ^ (σ + 1 / 2) * Real.Gamma (σ + 1 / 2) := by
      simpa only [show σ + 1 / 2 - 1 = a by dsimp [a]; ring, neg_mul] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 1 / 2) (r := δ) (by linarith) hδ
    have hec : (∫ t : ℝ in Set.Ioi 0, Real.exp (-δ * t)) = 1 / δ := by
      simpa using integral_exp_mul_Ioi (a := -δ) (by linarith) 0
    dsimp only [F]
    simp_rw [add_mul]
    rw [integral_add hpow (he.const_mul (3 ^ a)), integral_const_mul, hpc, hec]
    ring
  have hb (t : ℝ) : ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ ≤ K * F |t| := by
    have h := (gamma_mellin_kernel_bound σ hσ hσ' z hz).2 t
    have hp := Real.rpow_add_le_add_rpow (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 3) ha ha'
    calc
      _ ≤ K * (|t| + 3) ^ a * Real.exp (-δ * |t|) := by
        simpa only [K, a, δ, neg_mul] using h
      _ ≤ K * (|t| ^ a + 3 ^ a) * Real.exp (-δ * |t|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK) (Real.exp_pos _).le
      _ = _ := by dsimp [F]; ring
  calc
    _ ≤ ∫ t : ℝ, K * F |t| := integral_mono
      (gamma_mellin_kernel_integrable σ hσ hσ' z hz).norm (hiAll.const_mul K) hb
    _ = K * (2 * ((1 / δ) ^ (σ + 1 / 2) * Real.Gamma (σ + 1 / 2) + 3 ^ a / δ)) := by
      rw [integral_const_mul, hmass]
    _ = _ := by dsimp [K, a, δ]; ring

/-- P0029 pages 10 and 11, off-center norm integral in geometric right half plane parameters. -/
theorem gamma_mellin_kernel_L1_geometry (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    (z : ℂ) (hz : 0 < z.re) :
    (∫ t : ℝ, ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) ≤
      (2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * (Real.Gamma (σ + 1 / 2) + 6)) *
        ‖z‖ ^ (1 / 2 : ℝ) / z.re ^ (σ + 1 / 2) := by
  let δ : ℝ := Real.pi / 2 - |Complex.arg z|
  let a : ℝ := σ - 1 / 2
  let x : ℝ := σ + 1 / 2
  let B : ℝ := (1 / δ) ^ x
  let K : ℝ := Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)
  have hδ : 0 < δ := (gamma_mellin_kernel_bound σ hσ hσ' z hz).1
  have hδ2 : δ ≤ 2 := by dsimp [δ]; linarith [Real.pi_lt_four, abs_nonneg (Complex.arg z)]
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a ≤ 1 := by dsimp [a]; linarith
  have hδa : δ ^ a ≤ 2 := by
    by_cases hδ1 : δ ≤ 1
    · exact (Real.rpow_le_one hδ.le hδ1 ha).trans (by norm_num)
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hδ1) ha').trans hδ2
  have h3a : (3 : ℝ) ^ a ≤ 3 := Real.rpow_le_self_of_one_le (by norm_num) ha'
  have hm : (3 : ℝ) ^ a * δ ^ a ≤ 6 := by
    calc
      _ ≤ 3 * 2 := mul_le_mul h3a hδa (Real.rpow_nonneg hδ.le _) (by norm_num)
      _ = _ := by norm_num
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hid : (3 : ℝ) ^ a / δ = 3 ^ a * δ ^ a * B := by
    dsimp only [B]
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow, mul_assoc, ← Real.rpow_add hδ]
    rw [show a + -x = -1 by dsimp [a, x]; ring, Real.rpow_neg_one]
    ring
  have hs : B * Real.Gamma x + 3 ^ a / δ ≤ (Real.Gamma x + 6) * B := by
    have hh : 3 ^ a / δ ≤ 6 * B := by rw [hid]; exact mul_le_mul_of_nonneg_right hm hB
    nlinarith
  have hz0 : z ≠ 0 := by intro h; simpa [h] using hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hgap : z.re / ‖z‖ ≤ δ := right_half_plane_arg_gap z hz
  have hratio : 1 / δ ≤ ‖z‖ / z.re := by
    apply (div_le_div_iff₀ hδ hz).mpr
    have hh := (div_le_iff₀ hn).mp hgap
    nlinarith
  have hBp : B ≤ (‖z‖ / z.re) ^ x :=
    Real.rpow_le_rpow (by positivity) hratio (by dsimp [x]; linarith)
  have hprod : ‖z‖ ^ (-σ) * (‖z‖ / z.re) ^ x = ‖z‖ ^ (1 / 2 : ℝ) / z.re ^ x := by
    rw [Real.div_rpow hn.le hz.le, ← mul_div_assoc, ← Real.rpow_add hn]
    congr 1
    congr 1
    dsimp [x]
    ring
  have hΓ : 0 ≤ Real.Gamma x := Real.Gamma_nonneg_of_nonneg (by dsimp [x]; linarith)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ 2 * K * ‖z‖ ^ (-σ) * (B * Real.Gamma x + 3 ^ a / δ) := by
      simpa only [K, B, a, x, δ] using gamma_mellin_kernel_L1_bound σ hσ hσ' z hz
    _ ≤ 2 * K * ‖z‖ ^ (-σ) * ((Real.Gamma x + 6) * B) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (2 * K * (Real.Gamma x + 6)) * (‖z‖ ^ (-σ) * B) := by ring
    _ ≤ (2 * K * (Real.Gamma x + 6)) * (‖z‖ ^ (-σ) * (‖z‖ / z.re) ^ x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBp (by positivity)) (by positivity)
    _ = _ := by rw [hprod]; dsimp [K, x]; ring

/-- P0029 pages 10 and 11, the sharp scaling of the damped off-center Gamma kernel. -/
theorem damped_gamma_kernel_L1 (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    (N b : ℝ) (hN : 0 < N) :
    (∫ t : ℝ, ‖Complex.Gamma ((σ : ℂ) + I * t) *
      (((1 / N : ℝ) : ℂ) + I * b) ^ (-((σ : ℂ) + I * t))‖) ≤
      (2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * (Real.Gamma (σ + 1 / 2) + 6)) *
        N ^ σ * (1 + N * |b|) ^ (1 / 2 : ℝ) := by
  let z : ℂ := ((1 / N : ℝ) : ℂ) + I * b
  let C : ℝ := 2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * (Real.Gamma (σ + 1 / 2) + 6)
  have hz : 0 < z.re := by simpa [z] using (div_pos zero_lt_one hN)
  have hc : 0 ≤ C := by
    have hΓ : 0 ≤ Real.Gamma (σ + 1 / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
    dsimp [C]
    positivity
  have hn : ‖z‖ ≤ 1 / N + |b| := by
    calc
      _ ≤ ‖((1 / N : ℝ) : ℂ)‖ + ‖I * (b : ℂ)‖ := norm_add_le _ _
      _ = _ := by simp [abs_of_pos hN]
  have hn' : N * ‖z‖ ≤ 1 + N * |b| := by
    have h := mul_le_mul_of_nonneg_left hn hN.le
    have hi : N * (1 / N) = 1 := by field_simp
    nlinarith
  have hp : ‖z‖ ^ (1 / 2 : ℝ) * N ^ (σ + 1 / 2) =
      N ^ σ * (N * ‖z‖) ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_add hN, Real.mul_rpow hN.le (norm_nonneg z)]
    ring
  have hd : (1 / N) ^ (σ + 1 / 2) = (N ^ (σ + 1 / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow hN.le]
  have hb := gamma_mellin_kernel_L1_geometry σ hσ hσ' z hz
  have hr : z.re = 1 / N := by simp [z]
  rw [hr, hd, div_inv_eq_mul] at hb
  calc
    _ ≤ C * ‖z‖ ^ (1 / 2 : ℝ) * N ^ (σ + 1 / 2) := hb
    _ = C * N ^ σ * (N * ‖z‖) ^ (1 / 2 : ℝ) := by rw [mul_assoc, hp]; ring
    _ ≤ _ := by gcongr

/-- P0029 pages 10 to 12, the Gamma kernel is uniform on complete Farey arcs.
The frequency parameter is exactly one over N minus two pi i beta. -/
theorem damped_gamma_kernel_farey (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ' : σ ≤ 3 / 2)
    {N q β : ℝ} (hN : 4 ≤ N) (hq : 0 < q) (hqQ : q ≤ (⌊Real.sqrt N⌋₊ : ℝ))
    (hβ : |β| ≤ 1 / (q * (⌊Real.sqrt N⌋₊ : ℝ))) :
    Real.sqrt q * (∫ t : ℝ, ‖Complex.Gamma ((σ : ℂ) + I * t) *
      (((1 / N : ℝ) : ℂ) - (2 * Real.pi : ℝ) * I * β) ^ (-((σ : ℂ) + I * t))‖) ≤
      ((2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * (Real.Gamma (σ + 1 / 2) + 6)) *
        Real.sqrt (2 * Real.pi) * Real.sqrt 3) * N ^ (σ + 1 / 4) := by
  have hN0 : 0 < N := by linarith
  let b : ℝ := -(2 * Real.pi * β)
  let C : ℝ := 2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * (Real.Gamma (σ + 1 / 2) + 6)
  have hC : 0 ≤ C := by
    have hΓ : 0 ≤ Real.Gamma (σ + 1 / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
    dsimp [C]
    positivity
  have hbn : |b| = 2 * Real.pi * |β| := by simp [b, abs_mul, Real.pi_pos.le]
  have he : (((1 / N : ℝ) : ℂ) + I * b) =
      (((1 / N : ℝ) : ℂ) - (2 * Real.pi : ℝ) * I * β) := by
    dsimp [b]
    push_cast
    ring
  have hi := damped_gamma_kernel_L1 σ hσ hσ' N b hN0
  rw [he, ← Real.sqrt_eq_rpow] at hi
  have hs : Real.sqrt (1 + N * |b|) ≤ Real.sqrt (2 * Real.pi) * Real.sqrt (1 + N * |β|) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    apply Real.sqrt_le_sqrt
    rw [hbn]
    nlinarith [Real.pi_gt_three]
  obtain ⟨hQ, hQs, hsQ⟩ := farey_floor_bounds hN
  have hf := farey_error_factor hN0 hQ hq hqQ hQs hsQ hβ
  have hf' : Real.sqrt q * Real.sqrt (1 + N * |b|) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt 3 * N ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ Real.sqrt q * (Real.sqrt (2 * Real.pi) * Real.sqrt (1 + N * |β|)) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg q)
      _ = Real.sqrt (2 * Real.pi) * (Real.sqrt q * Real.sqrt (1 + N * |β|)) := by ring
      _ ≤ Real.sqrt (2 * Real.pi) * (Real.sqrt 3 * N ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt q * (C * N ^ σ * Real.sqrt (1 + N * |b|)) :=
      mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg q)
    _ = (C * N ^ σ) * (Real.sqrt q * Real.sqrt (1 + N * |b|)) := by ring
    _ ≤ (C * N ^ σ) * (Real.sqrt (2 * Real.pi) * Real.sqrt 3 * N ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hf' (by positivity)
    _ = (C * Real.sqrt (2 * Real.pi) * Real.sqrt 3) * (N ^ σ * N ^ (1 / 4 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hN0]

set_option backward.isDefEq.respectTransparency false in
/-- P0029 page 11 display 3.5, absolute interchange for the Gamma weighted Dirichlet series.
Adapted from PNTPort.PsiChi.smoothedSum_aux_tsum_integral and the PrimeNumberTheoremAnd port.
The compact smoothing Mellin kernel is replaced by the proved Gamma kernel. -/
theorem gamma_LSeries_tsum_integral {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N σ : ℝ} (hN : 0 < N) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    (∫ t : ℝ, ∑' n : ℕ, a n / (n : ℂ) ^ ((σ : ℂ) + t * I) *
      Complex.Gamma ((σ : ℂ) + t * I) * (N : ℂ) ^ ((σ : ℂ) + t * I)) =
    ∑' n : ℕ, ∫ t : ℝ, a n / (n : ℂ) ^ ((σ : ℂ) + t * I) *
      Complex.Gamma ((σ : ℂ) + t * I) * (N : ℂ) ^ ((σ : ℂ) + t * I) := by
  have cont_gamma : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro m he
    have hr := congrArg Complex.re he
    simp at hr
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : N ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero, LeanLab.PNTPort.PsiChi.a_zero ha] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp[i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos hN, norm_toNNReal, abs_two]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(N ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert LeanLab.PNTPort.PsiChi.summable_norm_div ha hσ using 2 with n
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact (gamma_vertical_integrable σ (by linarith) hσ').hasFiniteIntegral

/-- P0029 page 11 display 3.5, the damped Mellin identity before a contour shift. -/
theorem damped_LSeries_mellin {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n)
    {N σ : ℝ} (hN : 0 < N) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      LSeries a ((σ : ℂ) + t * I) * Complex.Gamma ((σ : ℂ) + t * I) *
        (N : ℂ) ^ ((σ : ℂ) + t * I)) =
      ∑' n : ℕ, a n * (Real.exp (-(n : ℝ) / N) : ℂ) := by
  have hpower (r : ℝ) (hr : 0 < r) (s : ℂ) :
      (r : ℂ) ^ (-s) * (N : ℂ) ^ s = ((r / N : ℝ) : ℂ) ^ (-s) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hr hN).ne'),
      ← Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_log hr.le, ← Complex.ofReal_log hN.le,
      ← Complex.ofReal_log (div_pos hr hN).le, Real.log_div hr.ne' hN.ne']
    push_cast
    ring
  have hsingle (n : ℕ) : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, a n / (n : ℂ) ^ ((σ : ℂ) + t * I) *
        Complex.Gamma ((σ : ℂ) + t * I) * (N : ℂ) ^ ((σ : ℂ) + t * I)) =
      a n * (Real.exp (-(n : ℝ) / N) : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, LeanLab.PNTPort.PsiChi.a_zero ha]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hk := mellinInv_Gamma σ (by linarith) hσ' (x := (n : ℝ) / N) (div_pos hnpos hN)
    simp only [mellinInv, Complex.real_smul, smul_eq_mul] at hk
    have hp (t : ℝ) : a n / (n : ℂ) ^ ((σ : ℂ) + t * I) *
        Complex.Gamma ((σ : ℂ) + t * I) * (N : ℂ) ^ ((σ : ℂ) + t * I) =
        a n * (((((n : ℝ) / N : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I))) *
          Complex.Gamma ((σ : ℂ) + t * I)) := by
      have hpn := hpower (n : ℝ) hnpos ((σ : ℂ) + t * I)
      simp only [Complex.ofReal_natCast] at hpn
      calc
        _ = a n * ((n : ℂ) ^ (-((σ : ℂ) + t * I)) * (N : ℂ) ^ ((σ : ℂ) + t * I)) *
            Complex.Gamma ((σ : ℂ) + t * I) := by rw [div_eq_mul_inv, Complex.cpow_neg]; ring
        _ = _ := by rw [hpn]; ring
    have hi : (∫ t : ℝ, a n / (n : ℂ) ^ ((σ : ℂ) + t * I) *
        Complex.Gamma ((σ : ℂ) + t * I) * (N : ℂ) ^ ((σ : ℂ) + t * I)) =
        a n * (∫ t : ℝ, (((n : ℝ) / N : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) *
          Complex.Gamma ((σ : ℂ) + t * I)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ hp)
    rw [hi, mul_left_comm]
    rw [hk]
    congr 2
    ring
  calc
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, ∑' n : ℕ,
        a n / (n : ℂ) ^ ((σ : ℂ) + t * I) * Complex.Gamma ((σ : ℂ) + t * I) *
          (N : ℂ) ^ ((σ : ℂ) + t * I)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [LeanLab.PNTPort.PsiChi.LSeries_eq_tsum (LeanLab.PNTPort.PsiChi.a_zero ha)]
      rw [← tsum_mul_right, ← tsum_mul_right]
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∑' n : ℕ, ∫ t : ℝ,
        a n / (n : ℂ) ^ ((σ : ℂ) + t * I) * Complex.Gamma ((σ : ℂ) + t * I) *
          (N : ℂ) ^ ((σ : ℂ) + t * I)) := by rw [gamma_LSeries_tsum_integral ha hN hσ hσ']
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
        a n / (n : ℂ) ^ ((σ : ℂ) + t * I) * Complex.Gamma ((σ : ℂ) + t * I) *
          (N : ℂ) ^ ((σ : ℂ) + t * I)) := by rw [← tsum_mul_left]
    _ = _ := tsum_congr hsingle

/-- P0029 page 11, the damped character sum as a logarithmic derivative Mellin integral.
This is before a contour shift and takes no zero free hypothesis. -/
theorem damped_character_mellin {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {N σ : ℝ} (hN : 0 < N) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + t * I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + t * I)) *
          Complex.Gamma ((σ : ℂ) + t * I) * (N : ℂ) ^ ((σ : ℂ) + t * I)) =
      ∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) *
        (Real.exp (-(n : ℝ) / N) : ℂ) := by
  have h := damped_LSeries_mellin (LeanLab.PNTPort.PsiChi.norm_chi_vonMangoldt_le χ) hN hσ hσ'
  have hf (t : ℝ) := LeanLab.PNTPort.PsiChi.LSeries_chi_vonMangoldt_eq χ
    (s := (σ : ℂ) + t * I) (by simpa using hσ)
  simpa only [hf, Pi.mul_apply] using h

#print axioms damped_LSeries_mellin
/-- P0029 pages 10 to 12, a positive Gamma kernel moment for absorbing logarithmic losses. -/
theorem gamma_mellin_kernel_moment (σ η : ℝ) (hσ : 1 / 2 ≤ σ) (hη : 0 ≤ η)
    (hση : σ + η ≤ 3 / 2) (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => (|t| + 3) ^ η *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) ∧
    (∫ t : ℝ, (|t| + 3) ^ η *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) ≤
      2 * (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ) *
        ((1 / (Real.pi / 2 - |Complex.arg z|)) ^ (σ + 1 / 2 + η) *
            Real.Gamma (σ + 1 / 2 + η) +
          3 ^ (σ - 1 / 2 + η) / (Real.pi / 2 - |Complex.arg z|)) := by
  have hσ' : σ ≤ 3 / 2 := by linarith
  let δ : ℝ := Real.pi / 2 - |Complex.arg z|
  let a : ℝ := σ - 1 / 2 + η
  let K : ℝ := (Real.exp (5 / 2) * Real.sqrt (2 * Real.pi)) * ‖z‖ ^ (-σ)
  let F : ℝ → ℝ := fun t => (t ^ a + 3 ^ a) * Real.exp (-δ * t)
  have hδ : 0 < δ := (gamma_mellin_kernel_bound σ hσ hσ' z hz).1
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a ≤ 1 := by dsimp [a]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpow : IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-δ * t)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := a) (p := 1) (b := δ) (by linarith) (by norm_num) hδ
  have he : IntegrableOn (fun t : ℝ => Real.exp (-δ * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_iff_pos.mpr hδ) 0
  have hi : IntegrableOn F (Set.Ioi 0) := by
    convert hpow.add (he.const_mul (3 ^ a)) using 1
    ext t
    dsimp only [F, Pi.add_apply]
    ring
  have hpos : IntegrableOn (fun t : ℝ => F |t|) (Set.Ioi 0) :=
    hi.congr_fun (fun t ht => by rw [abs_of_pos ht]) measurableSet_Ioi
  have hneg : IntegrableOn (fun t : ℝ => F |t|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hpos
  have hiAll : Integrable (fun t : ℝ => F |t|) := by
    have h := hneg.union hpos
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using h
  have hmass : (∫ t : ℝ, F |t|) = 2 *
      ((1 / δ) ^ (σ + 1 / 2 + η) * Real.Gamma (σ + 1 / 2 + η) + 3 ^ a / δ) := by
    rw [integral_comp_abs]
    congr 1
    have hpc : (∫ t : ℝ in Set.Ioi 0, t ^ a * Real.exp (-δ * t)) =
        (1 / δ) ^ (σ + 1 / 2 + η) * Real.Gamma (σ + 1 / 2 + η) := by
      simpa only [show σ + 1 / 2 + η - 1 = a by dsimp [a]; ring, neg_mul] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 1 / 2 + η) (r := δ) (by linarith) hδ
    have hec : (∫ t : ℝ in Set.Ioi 0, Real.exp (-δ * t)) = 1 / δ := by
      simpa using integral_exp_mul_Ioi (a := -δ) (by linarith) 0
    dsimp only [F]
    simp_rw [add_mul]
    rw [integral_add hpow (he.const_mul (3 ^ a)), integral_const_mul, hpc, hec]
    ring
  have hb (t : ℝ) : (|t| + 3) ^ η *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ ≤ K * F |t| := by
    have h := (gamma_mellin_kernel_bound σ hσ hσ' z hz).2 t
    have hp := Real.rpow_add_le_add_rpow (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 3) ha ha'
    calc
      _ ≤ (|t| + 3) ^ η * (K * (|t| + 3) ^ (σ - 1 / 2) * Real.exp (-δ * |t|)) :=
        mul_le_mul_of_nonneg_left (by simpa only [K, δ, neg_mul] using h) (by positivity)
      _ = K * (|t| + 3) ^ a * Real.exp (-δ * |t|) := by
        dsimp only [a]
        rw [Real.rpow_add (by positivity : (0 : ℝ) < |t| + 3)]
        ring
      _ ≤ K * (|t| ^ a + 3 ^ a) * Real.exp (-δ * |t|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hK) (Real.exp_pos _).le
      _ = _ := by dsimp [F]; ring
  have hm : AEStronglyMeasurable (fun t : ℝ => (|t| + 3) ^ η *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) := by
    have hw : Continuous (fun t : ℝ => (|t| + 3) ^ η) := by
      fun_prop (disch := positivity)
    exact hw.aestronglyMeasurable.mul
      (gamma_mellin_kernel_integrable σ hσ hσ' z hz).norm.aestronglyMeasurable
  have hiWeighted : Integrable (fun t : ℝ => (|t| + 3) ^ η *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) := by
    apply (hiAll.const_mul K).mono' hm
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb t
  refine ⟨hiWeighted, ?_⟩
  calc
    _ ≤ ∫ t : ℝ, K * F |t| := integral_mono
      hiWeighted (hiAll.const_mul K) hb
    _ = K * (2 * ((1 / δ) ^ (σ + 1 / 2 + η) * Real.Gamma (σ + 1 / 2 + η) + 3 ^ a / δ)) := by
      rw [integral_const_mul, hmass]
    _ = _ := by dsimp [K, a, δ]; ring

/-- P0029 pages 11 and 12, a logarithmic height weight costs an arbitrary positive moment. -/
theorem gamma_mellin_kernel_log_weight (σ η : ℝ) (hσ : 1 / 2 ≤ σ) (hη : 0 < η)
    (hση : σ + η ≤ 3 / 2) (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => Real.log (|t| + 3) *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) ∧
    (∫ t : ℝ, Real.log (|t| + 3) *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) ≤
      (1 / η) * ∫ t : ℝ, (|t| + 3) ^ η *
        ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ := by
  have hσ' : σ ≤ 3 / 2 := by linarith
  have hm := (gamma_mellin_kernel_moment σ η hσ hη.le hση z hz).1
  have hnonneg (t : ℝ) : 0 ≤ Real.log (|t| + 3) *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ :=
    mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) (norm_nonneg _)
  have hb (t : ℝ) : Real.log (|t| + 3) *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ ≤
      (1 / η) * ((|t| + 3) ^ η *
        ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) := by
    have h := Real.log_le_rpow_div (by linarith [abs_nonneg t] : (0 : ℝ) ≤ |t| + 3) hη
    calc
      _ ≤ ((|t| + 3) ^ η / η) *
          ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.log (|t| + 3) *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) := by
    have hl : Continuous (fun t : ℝ => Real.log (|t| + 3)) := by
      have hbase : Continuous (fun t : ℝ => |t| + 3) := continuous_abs.add continuous_const
      exact hbase.log (fun t => ne_of_gt (by linarith [abs_nonneg t]))
    exact hl.aestronglyMeasurable.mul
      (gamma_mellin_kernel_integrable σ hσ hσ' z hz).norm.aestronglyMeasurable
  have hi : Integrable (fun t : ℝ => Real.log (|t| + 3) *
      ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) := by
    apply (hm.const_mul (1 / η)).mono' hmeas
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
    exact hb t
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ t : ℝ, (1 / η) * ((|t| + 3) ^ η *
        ‖Complex.Gamma ((σ : ℂ) + I * t) * z ^ (-((σ : ℂ) + I * t))‖) :=
      integral_mono hi (hm.const_mul (1 / η)) hb
    _ = _ := integral_const_mul _ _

#print axioms gamma_mellin_kernel_log_weight

#print axioms gamma_mellin_kernel_moment

#print axioms damped_character_mellin

#print axioms gamma_LSeries_tsum_integral

#print axioms damped_gamma_kernel_farey

#print axioms damped_gamma_kernel_L1

#print axioms gamma_mellin_kernel_L1_geometry

#print axioms gamma_mellin_kernel_L1_bound

#print axioms right_half_plane_arg_gap
#print axioms gamma_mellin_kernel_integrable

#print axioms gamma_mellin_kernel_bound

#print axioms gamma_stirling_strip

#print axioms gamma_normalized_strip

#print axioms gamma_vertical_integrable
#print axioms mellinInv_Gamma

#print axioms damped_gamma_integral
#print axioms gamma_vertical_decay

end GammaSupply

#print axioms arg_exponential_loss
#print axioms piecewise_square_error_bessel
#print axioms farey_floor_bounds
#print axioms farey_error_factor
#print axioms farey_uniform_error
#print axioms coefficient_sub_continuous
#print axioms weighted_count_coefficient
#print axioms weighted_energy_of_model
#print axioms prime_generating_mass
#print axioms prime_square_error_energy
#print axioms square_error_bessel
#print axioms square_error_energy_of_uniform
#print axioms weighted_energy_of_prime_energy
#print axioms prime_energy_of_weighted_energy
#print axioms prime_power_energy
#print axioms prime_power_correction_bound
#print axioms elementary_bound_not_dominated
#print axioms elementary_energy
#print axioms error_le_linear_rpow
#print axioms weighted_count_le_linear_log
#print axioms singular_two_mul
#print axioms split_windows_inhabited
#print axioms singular_le_divisor_count

end LeanLab.ExceptionalSet.BG2026.Supply480
