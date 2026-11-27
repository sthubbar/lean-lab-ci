/-
Burst 2026-11-22, BHP1997, wave 3: the two window leaves of `DQ517WindowSplit`,
`leaf_two_window` and `leaf_four_window`, split once along the paper.
Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17: "It is a straightforward
consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`, that ...".

The E2 and E4 terms of b0, display 5.15 on page 50, are sums over outer primes `p1 p2` or
`p1 p2 p3 p4` of the rough indicator of the cofactor. The prime number theorem enters twice:
* for the primes of the rough cofactor, giving its Buchstab density `ω(u) / log z` on every
  integer interval: `leaf_rough_window_density`, HARD;
* for the outer primes, turning the sum of those Buchstab densities into the E2 or E4 integral
  at `m = Z ^ s`: `leaf_two_main_window` and `leaf_four_main_window`, HARD.
This is the cut of the proved prefix assembly `LowerPrincipal517g.two_rough_density_of_leaves`
and `four_rough_density_of_leaves`, with every log power error replaced by the error of 5.17,
`Y T0^(-5)` where `T0 = exp(L^(1/3))`. The prime number theorem error `exp(-ε L^(1/2))` of the
paper beats every power of `T0`, so the leaves are stated with the error `exp(-N L^(1/3))`, the
form of the lab input `DQ517StrongPNTInput.psi_error_stretched`.

PROVED here, from the three leaves: `two_window_of_leaves` and `four_window_of_leaves`, with
exactly the statements of `DQ517Window.leaf_two_window` and `DQ517Window.leaf_four_window`,
which now close by them.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DQLowerExceptionalMeanSquareDecisions
import LeanLab.BHP1997.LowerPrincipal517g
import LeanLab.BHP1997.DQ517StrongPNTInput

namespace LeanLab.BHP1997.DQ517Window
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open MeasureTheory
open LeanLab.BHP1997.Decomp514a
open scoped BigOperators


/-- The Chebyshev theta function as a sum of `primeWeight m * log m`. -/
private theorem theta_sum_eq (n : ℕ) :
    Chebyshev.theta (n : ℝ) = ∑ m ∈ Finset.Ioc 0 n, primeWeight m * Real.log m := by
  rw [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold primeWeight
  split_ifs <;> simp

/-- The prime number theorem with a stretched exponential error in theta form. -/
private theorem theta_error_sharp (N : ℝ) :
    ∃ C X : ℝ, 0 < C ∧ ∀ x : ℝ, X ≤ x →
      |Chebyshev.theta x - x| ≤ C * x * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨C1, X1, hC1, hψ⟩ := DQ517StrongPNTInput.psi_error_stretched N
  set M := max 343 (max ((6 * |N|) ^ 3) 36) with hM
  refine ⟨max C1 0 + 4, Real.exp M + max X1 2 + 2, by positivity, fun x hx => ?_⟩
  have hXe : Real.exp M ≤ x := by
    have h2 : (0 : ℝ) ≤ max X1 2 + 2 := by positivity
    linarith
  have hXL : max X1 2 + 2 ≤ x := by
    have h1 : (0 : ℝ) ≤ Real.exp M := (Real.exp_pos M).le
    linarith
  have hx1 : 1 < x := by
    have h1 : (1 : ℝ) < Real.exp M := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith [le_max_left (343:ℝ) (max ((6 * |N|) ^ 3) 36)])
    linarith
  have hx0 : 0 < x := by linarith
  have hxX1 : X1 ≤ x := by
    have : X1 ≤ max X1 2 := le_max_left _ _
    linarith
  set L := Real.log x with hL
  have hL0 : 0 < L := Real.log_pos hx1
  have hMe : M ≤ L := by
    have h := Real.log_le_log (Real.exp_pos M) hXe
    rwa [Real.log_exp] at h
  have h343M : (343 : ℝ) ≤ M := le_max_left _ _
  have hL343 : 343 ≤ L := h343M.trans hMe
  have hcubeM : (6 * |N|) ^ 3 ≤ M :=
    (le_max_left ((6 * |N|) ^ 3) 36).trans (le_max_right 343 (max ((6 * |N|) ^ 3) 36))
  have hLcube : (6 * |N|) ^ 3 ≤ L := hcubeM.trans hMe
  have hu6 : 6 * |N| ≤ L ^ (1 / 3 : ℝ) := by
    have h1 : ((6 * |N|) ^ 3) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hLcube (by norm_num)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 6 * |N|),
      show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h1
    exact h1
  have hu0 : 0 ≤ L ^ (1 / 3 : ℝ) := Real.rpow_nonneg hL0.le _
  have hNL : N * L ^ (1 / 3 : ℝ) ≤ L / 6 := by
    have h4 : 6 * (|N| * L ^ (1 / 3 : ℝ)) ≤ L := by
      have h5 : 6 * (|N| * L ^ (1 / 3 : ℝ)) ≤ L ^ (1 / 3 : ℝ) * L ^ (1 / 3 : ℝ) := by
        have hm := mul_le_mul_of_nonneg_right hu6 hu0
        calc 6 * (|N| * L ^ (1 / 3 : ℝ)) = (6 * |N|) * L ^ (1 / 3 : ℝ) := by ring
          _ ≤ L ^ (1 / 3 : ℝ) * L ^ (1 / 3 : ℝ) := hm
      calc 6 * (|N| * L ^ (1 / 3 : ℝ)) ≤ L ^ (1 / 3 : ℝ) * L ^ (1 / 3 : ℝ) := h5
        _ = L ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
        _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = L := Real.rpow_one L
    have h6 : N * L ^ (1 / 3 : ℝ) ≤ |N| * L ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self N) hu0
    linarith
  have hpoly : 2 * L ≤ Real.exp (L / 3) := by
    have h := Real.pow_div_factorial_le_exp (L / 3) (by positivity) 2
    have h2 : ((L / 3) ^ 2) / ((Nat.factorial 2 : ℕ) : ℝ) = L ^ 2 / 18 := by
      norm_num [Nat.factorial]; ring
    rw [h2] at h
    nlinarith
  have htwo : 2 * L ≤ Real.exp (L / 2 - N * L ^ (1 / 3 : ℝ)) := by
    refine hpoly.trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hxexp : x = Real.exp L := (Real.exp_log hx0).symm
  have hsq : Real.sqrt x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, hL]
    congr 1
    ring
  have hmain : 2 * Real.sqrt x * Real.log x ≤ x * Real.exp (-N * L ^ (1 / 3 : ℝ)) := by
    have hEN : Real.exp (L / 2) * Real.exp (L / 2 - N * L ^ (1 / 3 : ℝ)) =
        Real.exp (-N * L ^ (1 / 3 : ℝ)) * Real.exp L := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc 2 * Real.sqrt x * Real.log x = Real.exp (L / 2) * (2 * L) := by rw [hsq, hL]; ring
      _ ≤ Real.exp (L / 2) * Real.exp (L / 2 - N * L ^ (1 / 3 : ℝ)) := by
          gcongr
      _ = Real.exp (-N * L ^ (1 / 3 : ℝ)) * Real.exp L := hEN
      _ = x * Real.exp (-N * L ^ (1 / 3 : ℝ)) := by rw [hxexp, mul_comm]
  have hθ : |Chebyshev.theta x - x| ≤ |Chebyshev.theta x - Chebyshev.psi x| +
      |Chebyshev.psi x - x| := by
    rw [show Chebyshev.theta x - x = (Chebyshev.theta x - Chebyshev.psi x) +
      (Chebyshev.psi x - x) by ring]
    exact abs_add_le _ _
  have hψθ : |Chebyshev.theta x - Chebyshev.psi x| ≤ 2 * Real.sqrt x * Real.log x := by
    rw [abs_sub_comm]
    exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1.le
  have hpsi : |Chebyshev.psi x - x| ≤ C1 * x * Real.exp (-N * L ^ (1 / 3 : ℝ)) := by
    rw [hL]
    exact hψ x hxX1
  calc |Chebyshev.theta x - x| ≤ 2 * Real.sqrt x * Real.log x + C1 * x *
        Real.exp (-N * L ^ (1 / 3 : ℝ)) := hθ.trans (add_le_add hψθ hpsi)
    _ ≤ x * Real.exp (-N * L ^ (1 / 3 : ℝ)) + C1 * x *
        Real.exp (-N * L ^ (1 / 3 : ℝ)) := by gcongr
    _ = (C1 + 1) * (x * Real.exp (-N * L ^ (1 / 3 : ℝ))) := by ring
    _ ≤ (max C1 0 + 4) * (x * Real.exp (-N * L ^ (1 / 3 : ℝ))) := by
        have h4 : C1 + 1 ≤ max C1 0 + 4 := by
          have := le_max_left C1 0; linarith
        exact mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = (max C1 0 + 4) * x * Real.exp (-N * L ^ (1 / 3 : ℝ)) := by ring

/-- Telescoping of first differences over an integer interval. -/
private theorem sum_Ico_telescope (f : ℕ → ℝ) (a : ℕ) : ∀ n : ℕ,
    ∑ k ∈ Finset.Ico a (a + n), (f k - f (k + 1)) = f a - f (a + n)
  | 0 => by simp
  | (n + 1) => by
    have h : a + (n + 1) = (a + n) + 1 := by ring
    rw [h, Finset.sum_Ico_succ_top (by omega), sum_Ico_telescope f a n]
    ring

/-- The total variation of `1 / log` over an integer interval above `3` is at most one. -/
private theorem variation_inv_log (P i : ℕ) (hP : 3 ≤ P) (hPi : P ≤ i) :
    ∑ k ∈ Finset.Ico P i, |1 / Real.log ((k + 1 : ℕ) : ℝ) - 1 / Real.log (k : ℝ)| ≤ 1 := by
  have hmono : ∀ k : ℕ, 2 ≤ k → 1 / Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 / Real.log (k : ℝ) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hlt : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hlog' : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_le_log hk0 hlt
    exact one_div_le_one_div_of_le hlog hlog'
  have hterm : ∀ k ∈ Finset.Ico P i,
      |1 / Real.log ((k + 1 : ℕ) : ℝ) - 1 / Real.log (k : ℝ)| =
        1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk1, -⟩ := Finset.mem_Ico.mp hk
    have h2 : 2 ≤ k := by omega
    have hle := hmono k h2
    have hnn : (0 : ℝ) ≤ 1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by linarith
    rw [abs_sub_comm, abs_of_nonneg hnn]
  rw [Finset.sum_congr rfl hterm]
  have hi : P + (i - P) = i := Nat.add_sub_of_le hPi
  have htel := sum_Ico_telescope (fun k => 1 / Real.log (k : ℝ)) P (i - P)
  rw [hi] at htel
  rw [htel]
  have hfl : 1 / Real.log (P : ℝ) ≤ 1 := by
    have h3 : (3 : ℝ) ≤ P := by exact_mod_cast hP
    have h1 : 1 ≤ Real.log (P : ℝ) := by
      rw [← Real.log_exp 1]
      refine Real.log_le_log (Real.exp_pos 1) ?_
      have := Real.exp_one_lt_d9; linarith
    have h0 : 0 < Real.log (P : ℝ) := by linarith
    rw [div_le_one h0]; exact h1
  have hpos : 0 ≤ 1 / Real.log ((i : ℝ)) := by
    have hi3 : (3 : ℝ) ≤ (i : ℝ) := by
      have h1 : (3 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
      have h2 : (P : ℝ) ≤ (i : ℝ) := by exact_mod_cast hPi
      linarith
    have : 0 < Real.log (i : ℝ) := Real.log_pos (by linarith)
    positivity
  linarith

/-- The function `t ↦ t * exp (-N' * (log t) ^ (1/3))` on `[1, T]` is at most one or its value
at the right end. -/
private theorem mul_exp_rpow_le_max {N' : ℝ} (hN' : 0 < N') {t T : ℝ} (ht : 1 ≤ t) (htT : t ≤ T) :
    t * Real.exp (-N' * Real.log t ^ (1 / 3 : ℝ)) ≤
      max 1 (T * Real.exp (-N' * Real.log T ^ (1 / 3 : ℝ))) := by
  have ht0 : 0 < t := by linarith
  have hT0 : 0 < T := by linarith
  set u := Real.log t with hu
  set U := Real.log T with hU
  set a := u ^ (1 / 3 : ℝ) with ha
  set b := U ^ (1 / 3 : ℝ) with hb
  have hu0 : 0 ≤ u := Real.log_nonneg ht
  have hU0 : 0 ≤ U := Real.log_nonneg (by linarith)
  have ha0 : 0 ≤ a := Real.rpow_nonneg hu0 _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hU0 _
  have huab : a ^ 3 = u := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
  have hUab : b ^ 3 = U := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hU0]; norm_num
  have hle : a ≤ b := by
    have h1 : u ≤ U := by
      rw [hu, hU]; exact Real.log_le_log ht0 htT
    exact Real.rpow_le_rpow hu0 h1 (by norm_num)
  have ht_exp : t = Real.exp (a ^ 3) := by rw [huab, Real.exp_log ht0]
  have hT_exp : T = Real.exp (b ^ 3) := by rw [hUab, Real.exp_log hT0]
  have harg : -N' * Real.log t ^ (1 / 3 : ℝ) = -N' * a := by rw [← hu, ← ha]
  have hargT : -N' * Real.log T ^ (1 / 3 : ℝ) = -N' * b := by rw [← hU, ← hb]
  rw [ht_exp, harg, hT_exp, hargT]
  rcases le_or_gt (N' / 3) (a ^ 2) with hcase | hcase
  · -- large `a`: the exponent is monotone in `a`
    have hmono : a ^ 3 - N' * a ≤ b ^ 3 - N' * b := by
      have h1 : b ^ 3 - a ^ 3 = (b - a) * (b ^ 2 + b * a + a ^ 2) := by ring
      have h2 : 3 * a ^ 2 ≤ b ^ 2 + b * a + a ^ 2 := by nlinarith
      have h3 : 0 ≤ b - a := by linarith
      have h4 : N' * (b - a) ≤ (b - a) * 3 * a ^ 2 := by
        have : N' ≤ 3 * a ^ 2 := by linarith
        nlinarith
      have h5 : (b - a) * (3 * a ^ 2) ≤ (b - a) * (b ^ 2 + b * a + a ^ 2) := by
        exact mul_le_mul_of_nonneg_left h2 h3
      nlinarith
    calc Real.exp (a ^ 3) * Real.exp (-N' * a)
        = Real.exp (a ^ 3 - N' * a) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (b ^ 3 - N' * b) := Real.exp_le_exp.mpr hmono
      _ = Real.exp (b ^ 3) * Real.exp (-N' * b) := by rw [← Real.exp_add]; ring_nf
      _ ≤ max 1 (Real.exp (b ^ 3) * Real.exp (-N' * b)) := le_max_right _ _
  · -- small `a`: the exponent is nonpositive
    have hsmall : a ^ 3 - N' * a ≤ 0 := by
      have h2 : a ^ 2 * a = a ^ 3 := by ring
      nlinarith
    calc Real.exp (a ^ 3) * Real.exp (-N' * a)
        = Real.exp (a ^ 3 - N' * a) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hsmall
      _ = 1 := Real.exp_zero
      _ ≤ max 1 (Real.exp (b ^ 3) * Real.exp (-N' * b)) := le_max_left _ _

/-- Small values of `primeWeight k - 1 / log k`. -/
private theorem prime_weight_small : ∀ k : ℕ, k ≤ 4 →
    |primeWeight k - 1 / Real.log (k : ℝ)| ≤ 3 := by
  intro k hk
  have hpk1 : primeWeight k ≤ 1 := by unfold primeWeight; split_ifs <;> norm_num
  have hpk0 : 0 ≤ primeWeight k := by unfold primeWeight; split_ifs <;> norm_num
  have hlog : |1 / Real.log (k : ℝ)| ≤ 2 := by
    interval_cases k
    · simp
    · simp
    · have h1 : (0.5 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have h2 : 0 < Real.log 2 := by linarith
      have h3 : (Real.log 2)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ h2]; nlinarith
      rw [abs_of_pos (by positivity), one_div]
      exact h3
    · have h1 : (1 : ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
        have := Real.exp_one_lt_d9; linarith
      have h2 : 0 < Real.log 3 := by linarith
      have h3 : 1 / Real.log (3 : ℝ) ≤ 2 := (div_le_iff₀ h2).mpr (by nlinarith)
      rw [abs_of_pos (by positivity)]
      simpa using h3
    · have h1 : (1 : ℝ) ≤ Real.log 4 := by
        rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
        have := Real.exp_one_lt_d9; linarith
      have h2 : 0 < Real.log 4 := by linarith
      have h3 : 1 / Real.log (4 : ℝ) ≤ 2 := (div_le_iff₀ h2).mpr (by nlinarith)
      rw [abs_of_pos (by positivity)]
      simpa using h3
  calc |primeWeight k - 1 / Real.log (k : ℝ)| ≤ |primeWeight k| + |1 / Real.log (k : ℝ)| :=
        abs_sub _ _
    _ ≤ 1 + 2 := by
        have : |primeWeight k| = primeWeight k := abs_of_nonneg hpk0
        rw [this]; linarith
    _ = 3 := by norm_num

set_option maxHeartbeats 2000000 in
/-- The prime number theorem with a stretched exponential error, in the discrete logarithmic
integral form, uniformly on integer intervals. -/
private theorem prime_prefix_level_exp {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ X : ℝ, Cq ≤ X → ∀ Y : ℝ, X ^ c ≤ Y → Y ≤ X →
      ∀ L i : ℕ, L ≤ i → (i : ℝ) ≤ Y →
        |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
          Cq * Y * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  set N' := N / c ^ (1 / 3 : ℝ) + 1 with hN'def
  have hc3 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hN'pos : 0 < N' := by positivity
  have hN'c : N ≤ N' * c ^ (1 / 3 : ℝ) := by
    have h1 : (N / c ^ (1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = N := by field_simp
    nlinarith [h1, hc3]
  obtain ⟨C1, X1, hC1, hθ⟩ := theta_error_sharp N'
  set K : ℝ := 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) + Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1))
    with hK
  refine ⟨K, by positivity, fun X hX Y hY hYX L i hLi hiY => ?_⟩
  have hXe : Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) ≤ X := by
    have h1 : Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) ≤ K := by
      rw [hK]
      have h2 : (0 : ℝ) ≤ 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) := by positivity
      linarith
    linarith
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXe
  have hL1 : 1 ≤ Real.log X := by
    have h1 : Real.exp 1 ≤ Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) :=
      Real.exp_le_exp.mpr (le_trans (by norm_num : (1:ℝ) ≤ 2) (le_max_left (2 : ℝ) _))
    have h2 := Real.log_le_log (Real.exp_pos 1) (h1.trans hXe)
    rwa [Real.log_exp] at h2
  have hX3 : (3 : ℝ) ≤ X := by
    have h2 : (2 : ℝ) ≤ Real.log X := by
      have h2' : (2 : ℝ) ≤ max 2 ((|N| / c + 1) ^ 3 + 1) := le_max_left (2 : ℝ) _
      have h3 : Real.exp 2 ≤ Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) :=
        Real.exp_le_exp.mpr h2'
      have h4 : Real.exp 2 ≤ X := le_trans h3 hXe
      have h5 := Real.log_le_log (Real.exp_pos 2) h4
      rwa [Real.log_exp] at h5
    have h3 : (7 : ℝ) ≤ Real.exp 2 := by
      have h4 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have h5 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    have h4 : X = Real.exp (Real.log X) := (Real.exp_log hX0).symm
    rw [h4]
    calc (3 : ℝ) ≤ Real.exp 2 := by linarith
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr h2
  set E := Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 c) hY
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc.le) hY
  -- `Y * E ≥ 1`
  have hLc : N * Real.log X ^ (1 / 3 : ℝ) ≤ c * Real.log X := by
    have hM : |N| / c + 1 ≤ Real.log X ^ (1 / 3 : ℝ) := by
      have h1 : max 2 ((|N| / c + 1) ^ 3 + 1) ≤ Real.log X := by
        have h2 : Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) ≤ X := hXe
        have h3 := Real.log_le_log (Real.exp_pos _) h2
        rwa [Real.log_exp] at h3
      have h3 : (|N| / c + 1) ^ 3 ≤ max 2 ((|N| / c + 1) ^ 3 + 1) := by
        have h4 : (|N| / c + 1) ^ 3 + 1 ≤ max 2 ((|N| / c + 1) ^ 3 + 1) := le_max_right _ _
        linarith
      have h4 : (|N| / c + 1) ^ 3 ≤ Real.log X := le_trans h3 h1
      have h5 : ((|N| / c + 1) ^ 3) ^ (1 / 3 : ℝ) ≤ Real.log X ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ |N| / c + 1),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h5
      exact h5
    set M := Real.log X ^ (1 / 3 : ℝ) with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hM1 : 1 ≤ M := by
      have habs : (0 : ℝ) ≤ |N| / c := by positivity
      linarith
    have hcM : |N| ≤ c * M := by
      have h1 : |N| / c ≤ M := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hc.le
      have h3 : |N| / c * c = |N| := div_mul_cancel₀ _ hc.ne'
      rw [h3] at h2
      nlinarith
    have hcube : M ^ 3 = Real.log X := by
      rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have habs : N * M ≤ |N| * M := by
      have := le_abs_self N
      nlinarith
    have h1 : |N| * M ≤ (c * M) * M := mul_le_mul_of_nonneg_right hcM hM0
    have h2 : (c * M) * M ≤ c * M ^ 3 := by
      have h3 : M * M ≤ M ^ 3 := by nlinarith
      calc (c * M) * M = c * (M * M) := by ring
        _ ≤ c * M ^ 3 := by
            exact mul_le_mul_of_nonneg_left h3 hc.le
    calc N * M ≤ |N| * M := habs
      _ ≤ (c * M) * M := h1
      _ ≤ c * M ^ 3 := h2
      _ = c * Real.log X := by rw [hcube]
  have hYE : 1 ≤ Y * E := by
    have h1 : Real.exp (c * Real.log X) ≤ Y := by
      rw [← Real.log_rpow hX0, Real.exp_log (Real.rpow_pos_of_pos hX0 c)]
      exact hY
    have h2 : Real.exp (-(c * Real.log X)) ≤ E := by
      rw [hE]
      apply Real.exp_le_exp.mpr
      linarith
    calc (1 : ℝ) = Real.exp (c * Real.log X) * Real.exp (-(c * Real.log X)) := by
          rw [← Real.exp_add]; ring_nf; simp
      _ ≤ Y * E := by
          refine mul_le_mul h1 h2 (by positivity) (by positivity)

  -- the sharp error at scale `Y`
  set EY := Real.exp (-N' * Real.log Y ^ (1 / 3 : ℝ)) with hEY
  have hEYE : EY ≤ E := by
    rw [hEY, hE]
    apply Real.exp_le_exp.mpr
    have hlogY : c * Real.log X ≤ Real.log Y := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hY
      rwa [Real.log_rpow hX0] at h1
    have h2 : c ^ (1 / 3 : ℝ) * Real.log X ^ (1 / 3 : ℝ) ≤ Real.log Y ^ (1 / 3 : ℝ) := by
      rw [← Real.mul_rpow hc.le (by linarith : (0:ℝ) ≤ Real.log X)]
      exact Real.rpow_le_rpow (by positivity) hlogY (by norm_num)
    have h3 : N * Real.log X ^ (1 / 3 : ℝ) ≤ N' * Real.log Y ^ (1 / 3 : ℝ) := by
      have h4 : N' * (c ^ (1 / 3 : ℝ) * Real.log X ^ (1 / 3 : ℝ)) ≤
          N' * Real.log Y ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left h2 hN'pos.le
      have h5 : N' * (c ^ (1 / 3 : ℝ) * Real.log X ^ (1 / 3 : ℝ)) =
          (N' * c ^ (1 / 3 : ℝ)) * Real.log X ^ (1 / 3 : ℝ) := by ring
      have h6 : N * Real.log X ^ (1 / 3 : ℝ) ≤
          (N' * c ^ (1 / 3 : ℝ)) * Real.log X ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hN'c (by positivity)
      linarith
    linarith
  -- the theta error bound
  set BB := C1 * (Y * E) + (Real.log 4 + 5) * (|X1| + 1) + 3 with hBB
  have hBB0 : 0 ≤ BB := by positivity
  have hth : ∀ t : ℝ, 0 ≤ t → t ≤ Y →
      |Chebyshev.theta t - t| ≤ BB := by
    intro t ht0 htY
    have hBB3 : (3 : ℝ) ≤ BB := by
      rw [hBB]
      have h1 : (0 : ℝ) ≤ C1 * (Y * E) := by positivity
      have h2 : (0 : ℝ) ≤ (Real.log 4 + 5) * (|X1| + 1) := by positivity
      linarith
    rcases le_or_gt 1 t with h1t | h1t
    · rcases le_or_gt X1 t with hcase | hcase
      · -- sharp branch
        have h1 := hθ t hcase
        have h3 : t * Real.exp (-N' * Real.log t ^ (1 / 3 : ℝ)) ≤ max 1 (Y * EY) :=
          mul_exp_rpow_le_max hN'pos h1t htY
        have h4 : max 1 (Y * EY) ≤ Y * E := by
          rw [max_le_iff]
          exact ⟨hYE, mul_le_mul_of_nonneg_left hEYE hY0.le⟩
        calc |Chebyshev.theta t - t| ≤ C1 * t * Real.exp (-N' * Real.log t ^ (1 / 3 : ℝ)) := h1
          _ = C1 * (t * Real.exp (-N' * Real.log t ^ (1 / 3 : ℝ))) := by ring
          _ ≤ C1 * (Y * E) := by
              exact mul_le_mul_of_nonneg_left (h3.trans h4) hC1.le
          _ ≤ BB := by
              rw [hBB]
              have hp : (0 : ℝ) ≤ (Real.log 4 + 5) * (|X1| + 1) := by positivity
              linarith
      · -- coarse branch
        have htX : t ≤ |X1| + 1 := by
          have h5 : X1 ≤ |X1| := le_abs_self X1
          linarith
        have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        have h1 : Chebyshev.theta t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0
        have hK0 : (0 : ℝ) ≤ (Real.log 4 + 5) * (|X1| + 1) := by positivity
        have h2 : Chebyshev.theta t - t ≤ (Real.log 4 + 5) * (|X1| + 1) := by nlinarith
        have h3 : |Chebyshev.theta t - t| ≤ (Real.log 4 + 5) * (|X1| + 1) := by
          rw [abs_le]
          refine ⟨?_, h2⟩
          have h6 : (0:ℝ) ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
          have h7 : |X1| + 1 ≤ (Real.log 4 + 5) * (|X1| + 1) := by nlinarith
          linarith
        calc |Chebyshev.theta t - t| ≤ (Real.log 4 + 5) * (|X1| + 1) := h3
          _ ≤ BB := by
              rw [hBB]
              have hp : (0 : ℝ) ≤ C1 * (Y * E) := by positivity
              linarith
    · -- `t < 1`
      have h1 : Chebyshev.theta t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht0
      have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hlog42 : Real.log 4 ≤ 2 := by
        rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 4)]
        have h5 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
        have h6 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      have h3 : (Real.log 4 + 1) * t ≤ 3 := by nlinarith
      have h4 : |Chebyshev.theta t - t| ≤ (Real.log 4 + 1) * t := by
        rw [abs_le]
        constructor
        · have h6 : (0:ℝ) ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
          nlinarith
        · nlinarith
      linarith
  rcases le_or_gt i 2 with hi2 | hi2
  · -- at most two terms
    have hb : |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤ 6 := by
      have hsub : Finset.Ioc L i ⊆ Finset.Ioc L 2 := fun k hk => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hk
        exact Finset.mem_Ioc.mpr ⟨h1, by omega⟩
      have h1 : |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
          ∑ k ∈ Finset.Ioc L 2, |primeWeight k - 1 / Real.log (k : ℝ)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
      have h2 : ∀ k ∈ Finset.Ioc L 2, |primeWeight k - 1 / Real.log (k : ℝ)| ≤ 3 := by
        intro k hk
        exact prime_weight_small k (by have := (Finset.mem_Ioc.mp hk).2; omega)
      calc |_| ≤ ∑ k ∈ Finset.Ioc L 2, |primeWeight k - 1 / Real.log (k : ℝ)| := h1
        _ ≤ ∑ _k ∈ Finset.Ioc L 2, (3 : ℝ) := Finset.sum_le_sum h2
        _ ≤ 6 := by
            rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
            have hc2 : (2 - L : ℕ) ≤ 2 := by omega
            have h : ((2 - L : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hc2
            nlinarith
    refine hb.trans ?_
    have h1 : (6 : ℝ) ≤ K * Y * E := by
      have h4 : (6 : ℝ) ≤ 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) := by
        have : (0:ℝ) ≤ C1 + (Real.log 4 + 5) * (|X1| + 1) := by positivity
        linarith
      have h5 : 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) ≤ K := by
        rw [hK]; linarith [Real.exp_pos (max 2 ((|N| / c + 1) ^ 3 + 1))]
      have h6 : (1 : ℝ) ≤ Y * E := hYE
      calc (6 : ℝ) ≤ 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) * (Y * E) := by
            nlinarith [h4, h6]
        _ ≤ K * (Y * E) := by gcongr
        _ = K * Y * E := by ring
    exact h1
  -- the general case
  have hi3 : 3 ≤ i := by omega
  set a := max L 3 with ha
  have hLa : L ≤ a := le_max_left _ _
  have hai : a ≤ i := max_le hLi hi3
  have ha3 : 3 ≤ a := le_max_right _ _
  have hsplit : ∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ)) =
      ∑ k ∈ Finset.Ioc L a, (primeWeight k - 1 / Real.log (k : ℝ)) +
        ∑ k ∈ Finset.Ioc a i, (primeWeight k - 1 / Real.log (k : ℝ)) :=
    (Finset.sum_Ioc_consecutive _ hLa hai).symm
  have hsmall : |∑ k ∈ Finset.Ioc L a, (primeWeight k - 1 / Real.log (k : ℝ))| ≤ 9 := by
    rcases le_or_gt a 3 with ha3' | ha3'
    · have h1 : |∑ k ∈ Finset.Ioc L a, (primeWeight k - 1 / Real.log (k : ℝ))| ≤
          ∑ k ∈ Finset.Ioc L 3, |primeWeight k - 1 / Real.log (k : ℝ)| := by
        have hsub : Finset.Ioc L a ⊆ Finset.Ioc L 3 := fun k hk => by
          obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hk
          exact Finset.mem_Ioc.mpr ⟨h1, by omega⟩
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
      have h2 : ∑ k ∈ Finset.Ioc L 3, |primeWeight k - 1 / Real.log (k : ℝ)| ≤ 9 := by
        have h3 : ∀ k ∈ Finset.Ioc L 3, |primeWeight k - 1 / Real.log (k : ℝ)| ≤ 3 := by
          intro k hk
          exact prime_weight_small k (by have := (Finset.mem_Ioc.mp hk).2; omega)
        refine (Finset.sum_le_sum h3).trans ?_
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        have hc2 : (3 - L : ℕ) ≤ 3 := by omega
        have h : ((3 - L : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hc2
        nlinarith
      linarith
    · have hemp : Finset.Ioc L a = ∅ := by
        rw [Finset.Ioc_eq_empty]
        omega
      rw [hemp, Finset.sum_empty, abs_zero]
      norm_num

  -- Abel summation on `(a, i]`
  have hR : ∀ j : ℕ, a ≤ j → j ≤ i →
      |∑ n ∈ Finset.Ioc a j, (primeWeight n * Real.log (n : ℝ) - 1)| ≤ 2 * BB := by
    intro j haj hji
    have hjY : (j : ℝ) ≤ Y := le_trans (by exact_mod_cast hji) hiY
    have hja : (a : ℝ) ≤ j := by exact_mod_cast haj
    have hpref : ∑ n ∈ Finset.Ioc a j, (primeWeight n * Real.log (n : ℝ) - 1) =
        (Chebyshev.theta (j : ℝ) - Chebyshev.theta (a : ℝ)) - ((j : ℝ) - (a : ℝ)) := by
      have hsum : ∑ n ∈ Finset.Ioc a j, primeWeight n * Real.log (n : ℝ) =
          Chebyshev.theta (j : ℝ) - Chebyshev.theta (a : ℝ) := by
        have hc := Finset.sum_Ioc_consecutive (fun n => primeWeight n * Real.log (n : ℝ))
          (Nat.zero_le a) haj
        rw [theta_sum_eq j, theta_sum_eq a, ← hc]
        ring
      rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
        Nat.cast_sub haj]
    rw [hpref]
    have h3a := hth (a : ℝ) (by positivity) (by
      have : (a : ℝ) ≤ i := by exact_mod_cast hai
      linarith)
    have h3j := hth (j : ℝ) (by positivity) hjY
    rw [show (Chebyshev.theta (j : ℝ) - Chebyshev.theta (a : ℝ)) - ((j : ℝ) - (a : ℝ))
        = (Chebyshev.theta (j : ℝ) - (j : ℝ)) - (Chebyshev.theta (a : ℝ) - (a : ℝ)) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have habel := abel_Ioc_bound (fun k : ℕ => 1 / Real.log (k : ℝ))
    (fun k : ℕ => primeWeight k * Real.log (k : ℝ) - 1) hai hR
  -- convert the Abel sum to the prime sum
  have hconv : ∑ k ∈ Finset.Ioc a i,
        (1 / Real.log (k : ℝ)) * (primeWeight k * Real.log (k : ℝ) - 1) =
      ∑ k ∈ Finset.Ioc a i, (primeWeight k - 1 / Real.log (k : ℝ)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, -⟩ := Finset.mem_Ioc.mp hk
    have hk3 : 3 ≤ k := le_trans ha3 hk1.le
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    field_simp
  have hfi : |1 / Real.log (i : ℝ)| ≤ 1 := by
    have hi3' : (3 : ℝ) ≤ i := by exact_mod_cast hi3
    have h1 : 1 ≤ Real.log (i : ℝ) := by
      rw [← Real.log_exp 1]
      refine Real.log_le_log (Real.exp_pos 1) ?_
      have := Real.exp_one_lt_d9; linarith
    rw [abs_of_pos (by positivity)]
    rw [div_le_one (by linarith)]; exact h1
  have hvar : ∑ k ∈ Finset.Ico a i, |1 / Real.log ((k + 1 : ℕ) : ℝ) - 1 / Real.log (k : ℝ)| ≤ 1 :=
    variation_inv_log a i ha3 hai
  have hbound : |∑ k ∈ Finset.Ioc a i,
      (1 / Real.log (k : ℝ)) * (primeWeight k * Real.log (k : ℝ) - 1)| ≤
        (1 + 1) * (2 * BB) := by
    refine habel.trans ?_
    have : (|1 / Real.log (i : ℝ)| + ∑ k ∈ Finset.Ico a i,
        |1 / Real.log ((k + 1 : ℕ) : ℝ) - 1 / Real.log (k : ℝ)|) ≤ 1 + 1 := by
      linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  rw [hsplit, hconv] at *
  have htot : |∑ k ∈ Finset.Ioc L a, (primeWeight k - 1 / Real.log (k : ℝ)) +
      ∑ k ∈ Finset.Ioc a i, (primeWeight k - 1 / Real.log (k : ℝ))| ≤ 9 + 2 * (2 * BB) := by
    refine (abs_add_le _ _).trans ?_
    linarith
  refine htot.trans ?_
  -- the final arithmetic
  have hBBE : BB ≤ (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) * (Y * E) := by
    rw [hBB]
    have hp : (0 : ℝ) ≤ (Real.log 4 + 5) * (|X1| + 1) := by positivity
    have h1 : (Real.log 4 + 5) * (|X1| + 1) + 3 ≤ ((Real.log 4 + 5) * (|X1| + 1) + 3) * (Y * E) := by
      have h2 : ((Real.log 4 + 5) * (|X1| + 1) + 3) * 1 ≤
          ((Real.log 4 + 5) * (|X1| + 1) + 3) * (Y * E) :=
        mul_le_mul_of_nonneg_left hYE (by positivity)
      linarith
    have h3 : C1 * (Y * E) ≤ C1 * (Y * E) * (Y * E) := by
      have h0 : (0 : ℝ) < C1 * (Y * E) := by positivity
      have h4 : C1 * (Y * E) * 1 ≤ C1 * (Y * E) * (Y * E) :=
        mul_le_mul_of_nonneg_left hYE h0.le
      linarith
    nlinarith
  have hfin : 9 + 2 * (2 * BB) ≤ K * Y * E := by
    have h6 : (1 : ℝ) ≤ Y * E := hYE
    have h7 : 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) ≤ K := by
      rw [hK]; linarith [Real.exp_pos (max 2 ((|N| / c + 1) ^ 3 + 1))]
    have h8 : 9 + 2 * (2 * BB) ≤ 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) * (Y * E) := by
      have hp : (0 : ℝ) ≤ (Real.log 4 + 5) * (|X1| + 1) := by positivity
      have h9 := hBBE
      have h10 := hYE
      nlinarith
    calc 9 + 2 * (2 * BB) ≤ 16 * (C1 + (Real.log 4 + 5) * (|X1| + 1) + 3) * (Y * E) := h8
      _ ≤ K * (Y * E) := by gcongr
      _ = K * Y * E := by ring
  exact hfin

set_option maxHeartbeats 1000000 in
/-- `1 / z` is below a stretched exponential in the ambient scale, once `z ≥ X ^ c`. -/
private theorem inv_le_scale_exp {c : ℝ} (hc : 0 < c) (N : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      1 / (z : ℝ) ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  refine ⟨Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) + 2, by positivity, fun X hX z hzX => ?_⟩
  have hXe : Real.exp (max 2 ((|N| / c + 1) ^ 3 + 1)) ≤ X := by
    have h1 : (0:ℝ) ≤ 2 := by norm_num
    linarith
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXe
  have h2 : (2 : ℝ) ≤ Real.log X := by
    have h3 : max 2 ((|N| / c + 1) ^ 3 + 1) ≤ Real.log X := by
      rw [← Real.log_exp (max 2 ((|N| / c + 1) ^ 3 + 1))]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have h5 : (2 : ℝ) ≤ max 2 ((|N| / c + 1) ^ 3 + 1) := le_max_left (2:ℝ) _
    linarith
  set L := Real.log X with hL
  have hL0 : 0 < L := by linarith
  -- `N * L ^ (1/3) ≤ c * L`
  have hNL : N * L ^ (1 / 3 : ℝ) ≤ c * L := by
    have hM : |N| / c + 1 ≤ L ^ (1 / 3 : ℝ) := by
      have h3 : (|N| / c + 1) ^ 3 ≤ max 2 ((|N| / c + 1) ^ 3 + 1) := by
        have h4 : (|N| / c + 1) ^ 3 + 1 ≤ max 2 ((|N| / c + 1) ^ 3 + 1) := le_max_right _ _
        linarith
      have h4 : (|N| / c + 1) ^ 3 ≤ L := by
        have h5 : max 2 ((|N| / c + 1) ^ 3 + 1) ≤ L := by
          rw [hL, ← Real.log_exp (max 2 ((|N| / c + 1) ^ 3 + 1))]
          exact Real.log_le_log (Real.exp_pos _) hXe
        linarith
      have h5 : ((|N| / c + 1) ^ 3) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ |N| / c + 1),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h5
      exact h5
    set M := L ^ (1 / 3 : ℝ) with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hM1 : 1 ≤ M := by
      have habs : (0 : ℝ) ≤ |N| / c := by positivity
      linarith
    have hcM : |N| ≤ c * M := by
      have h1 : |N| / c ≤ M := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 hc.le
      have h3 : |N| / c * c = |N| := div_mul_cancel₀ _ hc.ne'
      rw [h3] at h2
      nlinarith
    have hcube : M ^ 3 = L := by
      rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have habs : N * M ≤ |N| * M := by
      have := le_abs_self N; nlinarith
    have h1 : |N| * M ≤ (c * M) * M := mul_le_mul_of_nonneg_right hcM hM0
    have h2 : (c * M) * M ≤ c * M ^ 3 := by
      have h3 : M * M ≤ M ^ 3 := by nlinarith
      calc (c * M) * M = c * (M * M) := by ring
        _ ≤ c * M ^ 3 := mul_le_mul_of_nonneg_left h3 hc.le
    calc N * M ≤ |N| * M := habs
      _ ≤ (c * M) * M := h1
      _ ≤ c * M ^ 3 := h2
      _ = c * L := by rw [hcube]
  have h1 : 1 / (z : ℝ) ≤ X ^ (-c) := by
    rw [Real.rpow_neg hX0.le, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hX0 c) hzX
  have hNL' : N * Real.log X ^ (1 / 3 : ℝ) ≤ c * Real.log X := by
    rw [hL] at hNL
    exact hNL
  have h3c : c * Real.log X = Real.log X * c := by ring
  have hexpX : Real.exp (N * Real.log X ^ (1 / 3 : ℝ)) ≤ X ^ c := by
    rw [Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.mpr
    linarith
  have hEinv : Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) =
      (Real.exp (N * Real.log X ^ (1 / 3 : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  calc 1 / (z : ℝ) ≤ X ^ (-c) := h1
    _ = (X ^ c)⁻¹ := Real.rpow_neg hX0.le c
    _ ≤ (Real.exp (N * Real.log X ^ (1 / 3 : ℝ)))⁻¹ :=
        inv_anti₀ (Real.exp_pos _) hexpX
    _ = Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := hEinv.symm

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the continuous Buchstab identity, at stretched exponential precision. -/
private theorem buchstab_telescope_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log n else 0) +
            ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cz, hCz, hzX⟩ := inv_le_scale_exp (c := c) hc N
  have hc6 : 0 < 2 * (1 / c) + 6 := by positivity
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2, by positivity,
    fun X hX z hzX0 a b ha hb => ?_⟩
  have hK2 : 0 < 2 * (1 / c) + 6 := hc6
  have hX3 : 3 ≤ X := by
    have h1 : (3:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := le_max_right _ _
    have h2 : max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 ≤ X := by
      have h3 : max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 ≤
          max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 := le_rfl
      linarith
    linarith
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by
    have h1 : ((3 : ℝ) ^ (1 / c)) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := le_max_left _ _
    have h2 : max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 ≤ X := by
      have h3 : max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 ≤
          max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 := le_rfl
      linarith
    linarith
  have hX0 : 0 < X := by linarith
  have hCzX : Cz ≤ X := by
    have : Cz ≤ max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 := by
      have h1 : (0:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
      have h2 : (0:ℝ) ≤ 2 * (1 / c) + 6 := by positivity
      linarith
    linarith
  have h3z : (3 : ℝ) ≤ z := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX0
  have hz3 : 3 ≤ z := by exact_mod_cast h3z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX0
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| ≤
      (2 * (1 / c) + 6) / (z : ℝ) := by
    intro n hn
    obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    by_cases hzn : z ≤ n
    · rw [ite_eq_left hzn]
      refine buchstab_telescope_term hω hz hz3 hzn ?_
      exact (Real.log_le_log hn0 (le_trans (by exact_mod_cast hnb) hb)).trans hlogz
    · rw [ite_eq_right hzn, Finset.Ico_eq_empty_of_le (by omega), Finset.sum_empty, add_zero,
        sub_zero]
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log hn0 (by exact_mod_cast (by omega : n < z))
      rw [hz _ hu, zero_div, abs_zero]
      positivity
  have hzinv : 1 / (z : ℝ) ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) :=
    hzX X hCzX z hzX0
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hEpos : 0 < Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := Real.exp_pos _
  calc _ ≤ ∑ n ∈ Finset.Ioc a b, |ω (Real.log n / Real.log z) / Real.log z -
      ((if z ≤ n then 1 / Real.log n else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _ 
    _ ≤ ∑ _n ∈ Finset.Ioc a b, (2 * (1 / c) + 6) / (z : ℝ) := Finset.sum_le_sum hterm
    _ = ((b - a : ℕ) : ℝ) * ((2 * (1 / c) + 6) * (1 / (z : ℝ))) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        ring
    _ ≤ (b : ℝ) * ((2 * (1 / c) + 6) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by
        have h1 : ((b - a : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b a
        have h2 : (2 * (1 / c) + 6) * (1 / (z : ℝ)) ≤
            (2 * (1 / c) + 6) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hzinv hc6.le
        have hp0 : (0 : ℝ) ≤ (2 * (1 / c) + 6) * (1 / (z : ℝ)) := by positivity
        calc ((b - a : ℕ) : ℝ) * ((2 * (1 / c) + 6) * (1 / (z : ℝ)))
            ≤ b * ((2 * (1 / c) + 6) * (1 / (z : ℝ))) := mul_le_mul_of_nonneg_right h1 hp0
          _ ≤ b * ((2 * (1 / c) + 6) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_left h2 hb0
    _ = (2 * (1 / c) + 6) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2) * b *
        Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have h1 : (2 * (1 / c) + 6) ≤ max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2 := by
          have h2 : (0:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
          have h3 : (0:ℝ) ≤ Cz := hCz.le
          linarith
        have h4 : (0:ℝ) ≤ b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by positivity
        calc (2 * (1 / c) + 6) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))
            = (2 * (1 / c) + 6) * (b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by ring
          _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + (2 * (1 / c) + 6) + Cz + 2) *
              (b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_right h1 h4
          _ = _ := by ring

/-- A fixed power of `log X` is absorbed by the stretched exponential. -/
private theorem log_pow_mul_exp_le (N : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X →
      Real.log X ^ k * Real.exp (-(N + k + 1) * Real.log X ^ (1 / 3 : ℝ)) ≤
        Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  refine ⟨Real.exp 100000, by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 100000) hX
  set L := Real.log X with hLdef
  have hL100 : 100000 ≤ L := by
    have h1 := Real.log_le_log (Real.exp_pos 100000) hX
    rwa [Real.log_exp] at h1
  have hL0 : 0 < L := by linarith
  set u := L ^ (1 / 3 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hL0 _
  have hu3 : u ^ 3 = L := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  -- `k log L ≤ (k+1) u`
  have hlog : (k : ℝ) * Real.log L ≤ ((k : ℝ) + 1) * u := by
    have h1 : Real.log L ≤ 6 * L ^ (1 / 6 : ℝ) := by
      have h2 := Real.log_le_rpow_div hL0.le (by norm_num : (0:ℝ) < 1 / 6)
      have h3 : L ^ (1 / 6 : ℝ) / (1 / 6) = 6 * L ^ (1 / 6 : ℝ) := by
        field_simp
      linarith [h2, h3]
    have h4 : L ^ (1 / 6 : ℝ) ≤ u := by
      rw [hu]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h6 : L ^ (1 / 6 : ℝ) ≥ 6 := by
      have h7 : (46656 : ℝ) ≤ L := by linarith
      calc (6 : ℝ) = (46656 : ℝ) ^ (1 / 6 : ℝ) := by
            rw [show (46656 : ℝ) = 6 ^ 6 by norm_num]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ L ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by norm_num) h7 (by norm_num)
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h7 : 6 * (k : ℝ) ≤ ((k : ℝ) + 1) * L ^ (1 / 6 : ℝ) := by nlinarith
    have h8 : (k : ℝ) * Real.log L ≤ (k : ℝ) * (6 * L ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 hk0
    have h9 : (k : ℝ) * (6 * L ^ (1 / 6 : ℝ)) = 6 * (k : ℝ) * L ^ (1 / 6 : ℝ) := by ring
    have h10 : 6 * (k : ℝ) * L ^ (1 / 6 : ℝ) ≤ ((k : ℝ) + 1) * L ^ (1 / 6 : ℝ) * L ^ (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    have h11 : L ^ (1 / 6 : ℝ) * L ^ (1 / 6 : ℝ) = L ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h12 : ((k : ℝ) + 1) * L ^ (1 / 6 : ℝ) * L ^ (1 / 6 : ℝ) = ((k : ℝ) + 1) * u := by
      rw [mul_assoc, h11, hu]
    linarith
  -- exponentiate
  have hexp : L ^ k = Real.exp ((k : ℝ) * Real.log L) := by
    rw [← Real.log_pow L k, Real.exp_log (by positivity)]
  have hkey : L ^ k * Real.exp (-(N + k + 1) * u) ≤ Real.exp (-N * u) := by
    rw [hexp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hk1 : ((k : ℝ) + 1) * u = (k : ℝ) * u + u := by ring
    nlinarith
  have hEu : Real.exp (-(N + k + 1) * Real.log X ^ (1 / 3 : ℝ)) = Real.exp (-(N + k + 1) * u) := by
    rw [hu]
  have hEN : Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) = Real.exp (-N * u) := by rw [hu]
  rw [hEu, hEN]
  exact hkey

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the lattice half of the Buchstab identity, at stretched exponential
precision. -/
private theorem lattice_abel_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
            ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
              ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cz, hCz, hzX⟩ := inv_le_scale_exp (c := c) hc (N + 2)
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 1
  refine ⟨max ((3 : ℝ) ^ (1 / c)) 3 + 8 + Cz + CL + 30, by positivity,
    fun X hX z hzX0 a b ha hb => ?_⟩
  have hX3 : 3 ≤ X := by
    have h1 : (3:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := le_max_right _ _
    have h0 : (0:ℝ) ≤ 8 + Cz + CL + 30 := by positivity
    linarith
  have hXc : (3 : ℝ) ^ (1 / c) ≤ X := by
    have h1 : ((3 : ℝ) ^ (1 / c)) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := le_max_left _ _
    have h0 : (0:ℝ) ≤ 8 + Cz + CL + 30 := by positivity
    linarith
  have hX0 : 0 < X := by linarith
  have hCzX : Cz ≤ X := by
    have h1 : (0:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
    have h2 : (0:ℝ) ≤ CL + 30 := by positivity
    linarith
  have hCLX : CL ≤ X := by
    have h1 : (0:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
    have h2 : (0:ℝ) ≤ 8 + Cz := by positivity
    linarith
  have hz3 : 3 ≤ z := three_le_level hc hXc hzX0
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (by omega : 0 < z)
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hswap : ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), ∑ n ∈ Finset.Ioc a b,
        ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := by
    calc _ = ∑ n ∈ Finset.Ioc a b, ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_subset ?_ ?_
          · intro k hk
            have h1 := Finset.mem_Ico.mp hk
            have h2 := Finset.mem_Ioc.mp hn
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h1.1⟩
          · intro k hk hnot
            obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
            have hnk : n ≤ k := by
              by_contra h
              exact hnot (Finset.mem_Ico.mpr ⟨hzk, by omega⟩)
            have hn0 : (0 : ℝ) < n := by
              exact_mod_cast (by have := (Finset.mem_Ioc.mp hn).1; omega : 0 < n)
            have hl := hlogk k (by omega)
            have hu : Real.log n / Real.log k - 1 < 1 := by
              have h3 : Real.log n / Real.log k ≤ 1 :=
                (div_le_one (by linarith)).mpr (Real.log_le_log hn0 (by exact_mod_cast hnk))
              linarith
            rw [hz _ hu, zero_div]
      _ = _ := Finset.sum_comm
  have hlevel : ∀ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
      (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
          ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) := by
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hkb : k ≤ b := (Finset.mem_Icc.mp hk1).2
    have hk3 : 3 ≤ k := by omega
    have hl := hlogk k hk3
    have hκ0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h1 : ∀ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) =
        if k ∣ n then ω (Real.log ((k * (n / k) : ℕ) : ℝ) / Real.log k - 1) /
          (k * Real.log k ^ 2) * k else 0 := by
      intro n _
      by_cases hd : k ∣ n
      · simp only [hd, ite_true]
        rw [Nat.mul_div_cancel' hd]
      · simp [hd]
    rw [Finset.sum_congr rfl h1, sum_dvd_reindex_real (by omega : 1 ≤ k) a b
      (fun m : ℕ => ω (Real.log ((k * m : ℕ) : ℝ) / Real.log k - 1) /
          (k * Real.log k ^ 2) * k),
      cofactor_one_split (by omega : 2 ≤ k) hkb]
    have h0 : ω (Real.log ((k * 1 : ℕ) : ℝ) / Real.log k - 1) / (k * Real.log k ^ 2) * k = 0 := by
      rw [mul_one, div_self (by linarith), sub_self, hz 0 (by norm_num), zero_div, zero_mul]
    rw [h0, ite_self, zero_add, Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (0 : ℝ) < m := by
      exact_mod_cast (by have := (Finset.mem_Ioc.mp hm).1; omega : 0 < m)
    have e : Real.log ((k * m : ℕ) : ℝ) / Real.log k - 1 = Real.log m / Real.log k := by
      push_cast
      rw [Real.log_mul hκ0.ne' hm0.ne']
      field_simp
      ring
    rw [e]
    field_simp
  rw [hswap, Finset.sum_congr rfl hlevel, ← Finset.sum_sub_distrib]
  have hkbound : ∀ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
      |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0)| ≤
        4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := by
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hk3 : 3 ≤ k := by omega
    have hl := hlogk k hk3
    have hκ0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hrhs : 0 ≤ 4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := by positivity
    have e : ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
        ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          (if k ∣ n then (k : ℝ) else 0) =
        -∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
          ((if k ∣ n then (k : ℝ) else 0) - 1) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e, abs_neg]
    by_cases hkb : k ^ 2 ≤ b
    · have hab : a ≤ b ∨ b < a := le_or_gt a b
      rcases hab with hab | hab
      · have hkb' : (k : ℝ) ^ 2 ≤ b := by exact_mod_cast hkb
        have hbpos : (0 : ℝ) < b := lt_of_lt_of_le (by positivity) hkb'
        have h1 : 1 ≤ (b : ℝ) * (1 / (k : ℝ) ^ 2) := by
          rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
          exact hkb'
        have h2 : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
        calc _ ≤ 3 + Real.log b := lattice_level_bound hω hz hk3 ha hab
          _ ≤ 4 * Real.log X * 1 := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
      · rw [Finset.Ioc_eq_empty_of_le hab.le, Finset.sum_empty, abs_zero]
        exact hrhs
    · have hzero : ∑ n ∈ Finset.Ioc a b,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
            ((if k ∣ n then (k : ℝ) else 0) - 1) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hu : Real.log n / Real.log k - 1 < 1 := by
          have h2l : Real.log n < 2 * Real.log k := by
            have := Real.log_lt_log hn0
              (by exact_mod_cast (by omega : n < k ^ 2) : (n : ℝ) < (k : ℝ) ^ 2)
            rw [Real.log_pow] at this
            push_cast at this
            linarith
          have : Real.log n / Real.log k < 2 := (div_lt_iff₀ (by linarith)).mpr h2l
          linarith
        rw [hz _ hu, zero_div, zero_mul]
      rw [hzero, abs_zero]
      exact hrhs
  have hsum : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k), 1 / (k : ℝ) ^ 2 ≤ 2 / (z : ℝ) := by
    refine le_trans ?_ (sum_inv_sq_Ico (by omega : 2 ≤ z) (max z (b + 1)) (le_max_left _ _))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro k hk
    obtain ⟨hk1, hzk⟩ := Finset.mem_filter.mp hk
    have hkb : k ≤ b := (Finset.mem_Icc.mp hk1).2
    exact Finset.mem_Ico.mpr ⟨hzk, lt_of_lt_of_le (by omega : k < b + 1) (le_max_right _ _)⟩
  have hzinv : 1 / (z : ℝ) ≤ Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) :=
    hzX X hCzX z hzX0
  have hE2pos : 0 < Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := Real.exp_pos _
  have habsorb : Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
      Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have h := hLX X hCLX
    rw [pow_one] at h
    have he : (-(N + (1:ℕ) + 1) : ℝ) = -(N + 2) := by push_cast; ring
    rwa [he] at h
  calc _ ≤ ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) *
            (if k ∣ n then (k : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        4 * Real.log X * (b * (1 / (k : ℝ) ^ 2)) := Finset.sum_le_sum hkbound
    _ = 4 * Real.log X * b * ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        1 / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ 4 * Real.log X * b * (2 * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) := by
        have h2 : 2 / (z : ℝ) = 2 * (1 / (z : ℝ)) := by ring
        have h3 : 2 / (z : ℝ) ≤ 2 * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left hzinv (by norm_num)
        exact mul_le_mul_of_nonneg_left (hsum.trans h3) (by positivity)
    _ = 8 * (Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) * b := by ring
    _ ≤ 8 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) * b := by
        have h8 : (0:ℝ) ≤ 8 := by norm_num
        have h9 : (0:ℝ) ≤ b := Nat.cast_nonneg b
        have := habsorb
        nlinarith
    _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + 8 + Cz + CL + 30) * b *
        Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have h1 : 8 ≤ max ((3 : ℝ) ^ (1 / c)) 3 + 8 + Cz + CL + 30 := by
          have h2 : (0:ℝ) ≤ max ((3 : ℝ) ^ (1 / c)) 3 := by positivity
          have h3 : (0:ℝ) ≤ Cz := hCz.le
          have h4 : (0:ℝ) ≤ CL := hCL.le
          linarith
        have h5 : (0:ℝ) ≤ b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by positivity
        calc 8 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) * b
            = 8 * (b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by ring
          _ ≤ (max ((3 : ℝ) ^ (1 / c)) 3 + 8 + Cz + CL + 30) *
              (b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_right h1 h5
          _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the prime number theorem applied to the least prime factor in the
Buchstab recursion, at stretched exponential precision. -/
private theorem prime_weight_transfer_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            ((if a < k then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
                ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cq, hCq, hpnt⟩ := prime_prefix_level_exp (c := c) hc (N + 3) (by linarith)
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 2
  have hE0 : (0 : ℝ) ≤ 2 / c + 1 := by positivity
  set K := max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) *
      ((3 + 4 * (2 / c + 1)) + 4) + 4 with hK
  refine ⟨K, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hA0 : (0 : ℝ) ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := by
    have h1 : (0 : ℝ) ≤ max ((4 : ℝ) ^ (1 / c)) 4 :=
      le_trans (by norm_num : (0:ℝ) ≤ 4) (le_max_right _ _)
    have h2 : (0 : ℝ) ≤ Cq + 4 := by linarith
    have h3 : (0 : ℝ) ≤ max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4) :=
      le_trans h1 (le_max_left _ _)
    exact le_trans h3 (le_max_left _ _)
  have hB1 : (1 : ℝ) ≤ (3 + 4 * (2 / c + 1)) + 4 := by
    have h0 : (0 : ℝ) < 2 / c + 1 := by positivity
    linarith
  have hAcq : Cq ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := by
    have ha1 : Cq ≤ Cq + 4 := by linarith
    have hb1 : Cq + 4 ≤ max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4) := le_max_right _ _
    exact le_trans (le_trans ha1 hb1) (le_max_left _ _)
  have hAc : (4 : ℝ) ^ (1 / c) ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := by
    have hb1 : ((4 : ℝ) ^ (1 / c)) ≤ max ((4 : ℝ) ^ (1 / c)) 4 := le_max_left _ _
    exact le_trans (le_trans hb1 (le_max_left _ _)) (le_max_left _ _)
  have hAl : CL ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hK4 : (4 : ℝ) ≤ K := by
    rw [hK]
    have h0 : (0 : ℝ) ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) *
        (3 + 4 * (2 / c + 1) + 4) := mul_nonneg hA0 (by positivity)
    linarith
  have hX4 : 4 ≤ X := hK4.trans hX
  have hXc : (4 : ℝ) ^ (1 / c) ≤ X := by
    rw [hK] at hX
    have h1 : (4 : ℝ) ^ (1 / c) ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) *
        ((3 + 4 * (2 / c + 1)) + 4) := by
      have h2 : (4 : ℝ) ^ (1 / c) * 1 ≤
          max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) * ((3 + 4 * (2 / c + 1)) + 4) :=
        mul_le_mul hAc hB1 (by norm_num) hA0
      linarith
    linarith
  have hXq : Cq ≤ X := by
    rw [hK] at hX
    have h1 : Cq ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) *
        ((3 + 4 * (2 / c + 1)) + 4) := by
      have h2 : Cq * 1 ≤
          max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) * ((3 + 4 * (2 / c + 1)) + 4) :=
        mul_le_mul hAcq hB1 (by norm_num) hA0
      linarith
    linarith
  have hXl : CL ≤ X := by
    rw [hK] at hX
    have h1 : CL ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) *
        ((3 + 4 * (2 / c + 1)) + 4) := by
      have h2 : CL * 1 ≤
          max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) * ((3 + 4 * (2 / c + 1)) + 4) :=
        mul_le_mul hAl hB1 (by norm_num) hA0
      linarith
    linarith
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hX0).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog0 : 0 < Real.log X := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have h4z : (4 : ℝ) ≤ z := by
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / c)) ^ c := by
          rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ X ^ c := Real.rpow_le_rpow (by positivity) hXc hc.le
      _ ≤ z := hzX
  have hz4 : 4 ≤ z := by exact_mod_cast h4z
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : Real.log X ≤ 1 / c * Real.log z := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 c) hzX
    rw [Real.log_rpow hX0] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / c)
    have e : 1 / c * (c * Real.log X) = Real.log X := by field_simp
    linarith
  have hlogk : ∀ k : ℕ, 3 ≤ k → 1 ≤ Real.log k := by
    intro k hk
    have h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    exact (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  set E := Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  by_cases hzb : z ≤ b
  swap
  · have hK : (Finset.Icc 1 b).filter (fun k => z ≤ k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    have hP : (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun k hk => by
        have := (Finset.mem_Icc.mp hk).2
        omega)
    rw [hK, hP, Finset.sum_empty, Finset.sum_empty, sub_zero, abs_zero]
    positivity
  have hmain := prime_transfer_abstract
    (fun m k : ℕ => ω (Real.log m / Real.log k) / Real.log k) (a := a)
    (E := 2 / c + 1) (R := Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)))
    (by omega : 2 ≤ z) hzb hE0 (by positivity)
    (by
      intro m k hm hmk
      have hl := hlogk k (by omega)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hu : Real.log m / Real.log k < 1 := by
        rw [div_lt_one (by linarith)]
        exact Real.log_lt_log hm0 (by exact_mod_cast hmk)
      rw [hz _ hu, zero_div])
    (by
      intro m i hzi him hmb
      have hi3 : 3 ≤ i := by omega
      have hi0 : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hi2 : i + 1 ≤ i ^ 2 := by nlinarith
      have hzi2 : z ≤ i ^ 2 := le_trans (by omega) hi2
      have h1 : Real.log z ≤ 2 * Real.log i := by
        have := Real.log_le_log hz0 (by exact_mod_cast hzi2 : (z : ℝ) ≤ (i : ℝ) ^ 2)
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      have h2 : Real.log m ≤ Real.log X :=
        Real.log_le_log hm0 (le_trans (by exact_mod_cast hmb) hb)
      have h3 : 1 / c * Real.log z ≤ 1 / c * (2 * Real.log i) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have hM : Real.log m ≤ 2 / c * Real.log i := by
        have e : 1 / c * (2 * Real.log i) = 2 / c * Real.log i := by ring
        linarith
      exact density_level_step hω hz hi3 him hM)
    (by
      intro m k hzk
      have hl := hlogk k (by omega)
      rw [abs_div, abs_of_pos (by linarith : 0 < Real.log k)]
      exact (div_le_one (by linarith)).mpr ((abs_buchstab_le_one hω hz _).trans hl))
    (by
      intro Y hzY hYb L i hLi hiY
      have h1 := hpnt X hXq Y (hzX.trans hzY) (hYb.trans hb) L i hLi hiY
      calc |∑ k ∈ Finset.Ioc L i, (primeWeight k - 1 / Real.log (k : ℝ))|
          ≤ Cq * Y * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) := h1
        _ = Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * Y := by ring)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  have hlb : Real.log b ≤ Real.log X := Real.log_le_log hbpos hb
  have h1 : 1 + Real.log b ≤ 2 * Real.log X := by linarith
  have h2 : 1 + (2 / c + 1) * (1 + Real.log b) ≤ (1 + 2 * (2 / c + 1)) * Real.log X := by
    nlinarith
  have h3 : (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b) ≤
      ((1 + 2 * (2 / c + 1)) * Real.log X) * (2 * Real.log X) :=
    mul_le_mul h2 h1 (by linarith) (by positivity)
  have h4 : 1 ≤ Real.log X ^ 2 := by nlinarith
  have hCb : 0 ≤ Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b := by positivity
  have hCqE : Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b *
      (1 + (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b)) ≤
      Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b *
        ((3 + 4 * (2 / c + 1)) * Real.log X ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hCb
    nlinarith
  have habs : Real.log X ^ 2 * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) ≤
      Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have h := hLX X hXl
    have he : (-(N + (2:ℕ) + 1) : ℝ) = -(N + 3) := by push_cast; ring
    rwa [he] at h
  calc _ ≤ Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b +
        (1 + (2 / c + 1) * (1 + Real.log b)) *
          (Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b * (1 + Real.log b)) := hmain
    _ = Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b *
        (1 + (1 + (2 / c + 1) * (1 + Real.log b)) * (1 + Real.log b)) := by ring
    _ ≤ Cq * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ)) * b *
        ((3 + 4 * (2 / c + 1)) * Real.log X ^ 2) := hCqE
    _ = (3 + 4 * (2 / c + 1)) * Cq * b *
        (Real.log X ^ 2 * Real.exp (-(N + 3) * Real.log X ^ (1 / 3 : ℝ))) := by ring
    _ ≤ (3 + 4 * (2 / c + 1)) * Cq * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have h5 : (0:ℝ) ≤ (3 + 4 * (2 / c + 1)) * Cq * b := by positivity
        exact mul_le_mul_of_nonneg_left habs h5
    _ ≤ K * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have h6 : (3 + 4 * (2 / c + 1)) * Cq ≤ K := by
          rw [hK]
          have h7 : (0:ℝ) ≤ (3 + 4 * (2 / c + 1)) := by positivity
          have h8 : (0:ℝ) ≤ Cq := hCq.le
          have h9 : Cq ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := by
            have ha1 : Cq ≤ Cq + 4 := by linarith
            have hb1 : Cq + 4 ≤ max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4) := le_max_right _ _
            have hc1 : max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4) ≤
                max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := le_max_left _ _
            linarith
          have h10 : (0:ℝ) ≤ max (max (max ((4 : ℝ) ^ (1 / c)) 4) (Cq + 4)) (max CL (max Cq 2)) := by positivity
          nlinarith
        have h7 : (0:ℝ) ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
        calc (3 + 4 * (2 / c + 1)) * Cq * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))
            = ((3 + 4 * (2 / c + 1)) * Cq) * (b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by ring
          _ ≤ K * (b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              linarith
          _ = K * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the one-level Buchstab step, at stretched exponential precision. -/
private theorem buchstab_main_term_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨CA, hCA, hA'⟩ := prime_weight_transfer_exp ω hω hz hc (N + 2) (by linarith)
  obtain ⟨C1, hC1, h1'⟩ := buchstab_telescope_exp ω hω hz hc (N + 2) (by linarith)
  obtain ⟨C2, hC2, h2'⟩ := lattice_abel_exp ω hω hz hc (N + 2) (by linarith)
  refine ⟨CA + C1 + C2 + 3, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hAb := hA' X (by linarith) z hzX a b ha hb
  have h1 := h1' X (by linarith) z hzX a b ha hb
  have h2 := h2' X (by linarith) z hzX a b ha hb
  have hid : ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        (if a < k then (1 : ℝ) else 0) / Real.log k := by
    have hI : Finset.Ioc a b = (Finset.Icc 1 b).filter (fun k => a < k) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : a < k <;> by_cases h2 : z ≤ k <;> simp [h1, h2]
  have e1 : ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)) =
      ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := Finset.sum_add_distrib
  have e2 : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        ((if a < k then (1 : ℝ) else 0) +
          ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (if a < k then (1 : ℝ) else 0) / Real.log k +
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k := by
    simp only [add_div, Finset.sum_add_distrib]
  rw [e1, hid] at h1
  rw [e2] at hAb
  obtain ⟨hA1, hA2⟩ := abs_le.mp hAb
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp h2
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hE0 : 0 < Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := Real.exp_pos _
  have hX3 : (3 : ℝ) ≤ X := by
    have h1 : (0 : ℝ) ≤ CA + C1 + C2 := by positivity
    linarith
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have hu0 : 0 ≤ Real.log X ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hEE : Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
      Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hstep : (CA + C1 + C2) * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
      (CA + C1 + C2 + 3) * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := by
    have h0 : (0 : ℝ) ≤ b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := by positivity
    have h1 : CA + C1 + C2 ≤ CA + C1 + C2 + 3 := by linarith
    calc (CA + C1 + C2) * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))
        = (CA + C1 + C2) * (b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) := by ring
      _ ≤ (CA + C1 + C2 + 3) * (b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring
  refine le_trans ?_ ((le_trans hstep (mul_le_mul_of_nonneg_left hEE (by positivity))))
  rw [abs_le]
  constructor <;> linarith

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the induction on the number of prime factors, at stretched exponential
precision. -/
private theorem rough_density_strip_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (k : ℕ) : ∀ N : ℝ, 0 < N →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X → b < z ^ (k + 1) →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  induction k with
  | zero =>
    intro N hN
    refine ⟨1, one_pos, fun X hX z hzX a b ha hb hbz => ?_⟩
    rw [zero_add, pow_one] at hbz
    have hzero : ∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
        ω (Real.log n / Real.log z) / Real.log z) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
      have hnz : n < z := lt_of_le_of_lt hnb hbz
      have hr : Task308.roughIndicator n z = 0 := by
        unfold Task308.roughIndicator
        rw [ite_eq_right]
        rintro (h | h)
        · omega
        · have := Nat.minFac_le (by omega : 0 < n)
          omega
      have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnz)
      rw [hr, hz _ hu]
      simp
    rw [hzero, abs_zero]
    positivity
  | succ k ih =>
    intro N hN
    obtain ⟨C1, hC1, h1⟩ := ih (N + 2) (by linarith)
    obtain ⟨C2, hC2, h2⟩ := buchstab_main_term_exp ω hω hz hc N hN
    obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 1
    refine ⟨max (max (max C1 C2) 3) CL + 2 * C1 + C2 + 10, by positivity,
      fun X hX z hzX a b ha hb hbz => ?_⟩
    have hC1le : C1 ≤ max (max (max C1 C2) 3) CL :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    have hC2le : C2 ≤ max (max (max C1 C2) 3) CL :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    have hCLle : CL ≤ max (max (max C1 C2) 3) CL := le_max_right _ _
    have hX1 : C1 ≤ X := by linarith
    have hX2 : C2 ≤ X := by linarith
    have hXL : CL ≤ X := by linarith
    have hX3 : 3 ≤ X := by
      have h3 : (3:ℝ) ≤ max (max (max C1 C2) 3) CL :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have hlog1 : 1 ≤ Real.log X :=
      (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
    have hlog0 : 0 < Real.log X := by linarith
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hsplit : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        ∑ m ∈ Finset.Ioc (a / p) (b / p), Task308.roughIndicator m p =
          (if a < p then (1 : ℝ) else 0) +
            ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), Task308.roughIndicator m p := by
      intro p hp
      obtain ⟨hpI, hpp, -⟩ := Finset.mem_filter.mp hp
      rw [cofactor_one_split hpp.two_le (Finset.mem_Icc.mp hpI).2 (fun m => Task308.roughIndicator m p)]
      simp [Task308.roughIndicator]
    have key : ∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z) =
        ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
          ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (Task308.roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p) -
        (∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)) := by
      rw [Finset.sum_sub_distrib, rough_sum_decomp z a b ha, Finset.sum_congr rfl hsplit]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have hinner : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        |∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (Task308.roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| ≤
          C1 * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) * (p : ℝ)⁻¹ := by
      intro p hp
      obtain ⟨hpI, hpp, hzp⟩ := Finset.mem_filter.mp hp
      have hp0 : 0 < p := hpp.pos
      have hbp : b / p < p ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
        exact lt_of_lt_of_le hbz (Nat.pow_le_pow_left hzp _)
      have hcast : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / p := Nat.cast_div_le
      have hbpX : ((b / p : ℕ) : ℝ) ≤ X :=
        le_trans (by exact_mod_cast Nat.div_le_self b p) hb
      have h := h1 X hX1 p (hzX.trans (by exact_mod_cast hzp)) (max (a / p) 1) (b / p)
        (le_max_right _ _) hbpX hbp
      calc _ ≤ C1 * ((b / p : ℕ) : ℝ) * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := h
        _ ≤ C1 * ((b : ℝ) / p) * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := by gcongr
        _ = _ := by rw [div_eq_mul_inv]; ring
    have hharm : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
        2 * Real.log X := by
      have hs : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
          ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
      have hh : ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ = (harmonic b : ℝ) := by
        simp [harmonic_eq_sum_Icc]
      have hl : Real.log b ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0
          simpa using hlog0.le
        · exact Real.log_le_log (by exact_mod_cast h0) hb
      have := harmonic_le_one_add_log b
      linarith
    have hleaf := h2 X hX2 z hzX a b ha hb
    have habs : Real.log X ^ 1 * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
        Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
      have h := hLX X hXL
      have he : (-(N + (1:ℕ) + 1) : ℝ) = -(N + 2) := by push_cast; ring
      rwa [he] at h
    rw [pow_one] at habs
    have hbound1 : C1 * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) * (2 * Real.log X) ≤
        2 * C1 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
      have h1' : Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
          Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := habs
      have h2' : (0:ℝ) ≤ 2 * C1 * b := by positivity
      calc C1 * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) * (2 * Real.log X)
          = 2 * C1 * b * (Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) := by ring
        _ ≤ 2 * C1 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left h1' h2'
    have hEE : Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
        Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
      refine le_trans ?_ habs
      have h1' : (0:ℝ) ≤ Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
      have h2' : (1:ℝ) ≤ Real.log X := hlog1
      nlinarith
    rw [key]
    calc _ ≤ |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                (Task308.roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| +
            C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (abs_sub _ _).trans (by gcongr)
      _ ≤ ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              C1 * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) * (p : ℝ)⁻¹ +
            C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hinner)
      _ ≤ C1 * b * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) * (2 * Real.log X) +
            C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
          rw [← Finset.mul_sum]
          gcongr
      _ ≤ 2 * C1 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) +
            C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by linarith
      _ ≤ (max (max (max C1 C2) 3) CL + 2 * C1 + C2 + 10) * b *
            Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
          have hcoef : 2 * C1 + C2 ≤ max (max (max C1 C2) 3) CL + 2 * C1 + C2 + 10 := by linarith
          have hpos : (0:ℝ) ≤ b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcoef hpos]

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17 in the form of the leaf of this file: the Buchstab local density of the
integers of `(a, b]` free of prime factors below `z ≥ X ^ c`, with a stretched exponential
error. -/
private theorem rough_interval_density_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := rough_density_strip_exp ω hω hz hc ⌈1 / c⌉₊ N hN
  refine ⟨C + 2, by linarith, fun X hX z hzX a b ha hb => ?_⟩
  have hX1 : 1 < X := by linarith
  have hk : 1 < c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 : 1 / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hc] at h1
    push_cast
    nlinarith
  have hbz : b < z ^ (⌈1 / c⌉₊ + 1) := by
    have h3 : X < (z : ℝ) ^ (⌈1 / c⌉₊ + 1) := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ < X ^ (c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt hX1 hk
        _ = (X ^ c) ^ (⌈1 / c⌉₊ + 1) := by
            rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
        _ ≤ (z : ℝ) ^ (⌈1 / c⌉₊ + 1) :=
            pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hzX _
    exact_mod_cast lt_of_le_of_lt hb h3
  calc _ ≤ C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) :=
        h X (by linarith) z hzX a b ha hb hbz
    _ ≤ (C + 2) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        have hE : (0:ℝ) ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
        have hcb : (0:ℝ) ≤ b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 2) hcb]


/-- Cell integrability passes to the whole interval. -/
private theorem intervalIntegrable_of_cells {φ : ℝ → ℝ} {A : ℕ}
    (hint : ∀ n : ℕ, A < n → IntervalIntegrable φ volume ((n : ℝ) - 1) (n : ℝ)) :
    ∀ B : ℕ, A ≤ B → IntervalIntegrable φ volume (A : ℝ) (B : ℝ) := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_⟩ <;>
      exact MeasureTheory.IntegrableOn.of_measure_zero (by simp)
  | succ b hab ih =>
    have hcast : ((b + 1 : ℕ) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
    have hcell : IntervalIntegrable φ volume (b : ℝ) ((b + 1 : ℕ) : ℝ) := by
      have h := hint (b + 1) (Nat.lt_succ_of_le hab)
      rwa [hcast] at h
    exact ih.trans hcell

/-- P0069 page 51 display 5.17, passage from the integers of an interval to the integral.
If on each cell `(n-1, n]` the value at the right endpoint is within `δ n` of the values
on the cell, then the sum over the integers of `(A, B]` is within `∑ δ` of the integral.
This is the cell by cell form of `BuchstabIntegral517.sum_sub_integral_le_of_lipschitz`,
whose constant multiplies the whole length of the interval and therefore does not decay;
here `δ n` may decay like `1/n^2`. -/
private theorem sum_sub_integral_le_of_cell (φ : ℝ → ℝ) (δ : ℕ → ℝ) (A : ℕ)
    (hδ0 : ∀ n : ℕ, A < n → 0 ≤ δ n)
    (hint : ∀ n : ℕ, A < n → IntervalIntegrable φ volume ((n : ℝ) - 1) (n : ℝ))
    (hosc : ∀ n : ℕ, A < n → ∀ t ∈ Set.Icc ((n : ℝ) - 1) (n : ℝ), |φ (n : ℝ) - φ t| ≤ δ n) :
    ∀ B : ℕ, A ≤ B →
      |(∑ n ∈ Finset.Ioc A B, φ n) - ∫ t in (A : ℝ)..(B : ℝ), φ t| ≤
        ∑ n ∈ Finset.Ioc A B, δ n := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hcast : ((b + 1 : ℕ) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
    have hcell : IntervalIntegrable φ volume (b : ℝ) ((b + 1 : ℕ) : ℝ) := by
      have h := hint (b + 1) (Nat.lt_succ_of_le hab)
      rwa [hcast] at h
    have hAb : IntervalIntegrable φ volume (A : ℝ) (b : ℝ) :=
      intervalIntegrable_of_cells hint b hab
    have hadd := intervalIntegral.integral_add_adjacent_intervals hAb hcell
    -- the last cell
    have hlast : |φ ((b + 1 : ℕ) : ℝ) - ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t| ≤
        δ (b + 1) := by
      have hconst : (∫ _t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ ((b + 1 : ℕ) : ℝ)) =
          φ ((b + 1 : ℕ) : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        have h1 : ((b + 1 : ℕ) : ℝ) - (b : ℝ) = 1 := by push_cast; ring
        rw [h1, one_mul]
      have hdiff : φ ((b + 1 : ℕ) : ℝ) - ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t =
          ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), (φ ((b + 1 : ℕ) : ℝ) - φ t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hcell, hconst]
      rw [hdiff]
      have hb1le : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (b : ℝ)) (b := ((b + 1 : ℕ) : ℝ)) (C := δ (b + 1))
        (f := fun t => φ ((b + 1 : ℕ) : ℝ) - φ t) (by
          intro t ht
          rw [show Set.uIoc (b : ℝ) ((b + 1 : ℕ) : ℝ) =
              Set.Ioc (b : ℝ) ((b + 1 : ℕ) : ℝ) from Set.uIoc_of_le hb1le] at ht
          have htm : t ∈ Set.Icc (((b + 1 : ℕ) : ℝ) - 1) ((b + 1 : ℕ) : ℝ) := by
            rw [hcast]
            exact ⟨le_of_lt ht.1, ht.2⟩
          rw [Real.norm_eq_abs]
          exact hosc (b + 1) (Nat.lt_succ_of_le hab) t htm)
      rw [Real.norm_eq_abs] at hbnd
      have hone : |((b + 1 : ℕ) : ℝ) - (b : ℝ)| = 1 := by
        rw [show ((b + 1 : ℕ) : ℝ) - (b : ℝ) = 1 by push_cast; ring]; norm_num
      rw [hone, mul_one] at hbnd
      exact hbnd
    rw [Finset.sum_Ioc_succ_top hab, ← hadd]
    have he : (∑ n ∈ Finset.Ioc A b, φ n) + φ ((b + 1 : ℕ) : ℝ) -
        ((∫ t in (A : ℝ)..(b : ℝ), φ t) + ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t) =
        ((∑ n ∈ Finset.Ioc A b, φ n) - ∫ t in (A : ℝ)..(b : ℝ), φ t) +
          (φ ((b + 1 : ℕ) : ℝ) - ∫ t in (b : ℝ)..((b + 1 : ℕ) : ℝ), φ t) := by ring
    rw [he, Finset.sum_Ioc_succ_top hab]
    exact (abs_add_le _ _).trans (add_le_add ih hlast)


/-! ### Stage 2: a log power is smaller than any power of `x` -/

/-- `log x` is at most `x ^ r / r` for `x > 0`, `r > 0` (from `log y ≤ y - 1` at `y = x ^ r`). -/
private theorem log_le_rpow_div {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    Real.log x ≤ x ^ r / r := by
  have hxr : 0 < x ^ r := Real.rpow_pos_of_pos hx r
  have h1 : Real.log x * r = Real.log (x ^ r) := by
    rw [Real.log_rpow hx r]; ring
  have h2 : Real.log (x ^ r) ≤ x ^ r - 1 := Real.log_le_sub_one_of_pos hxr
  have h3 : Real.log x * r ≤ x ^ r := by linarith
  rw [le_div_iff₀ hr]
  linarith

/-- `(log x) ^ m` is bounded by a constant times `x ^ c`, for every real `m` and every `c > 0`. -/
private theorem exists_log_rpow_le_mul_rpow {c : ℝ} (hc : 0 < c) (m : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → Real.log x ^ m ≤ C * x ^ c := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt m 0 with hm | hm
  · refine ⟨(Real.log 2) ^ m / 2 ^ c, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hle : Real.log x ^ m ≤ Real.log 2 ^ m :=
      Real.rpow_le_rpow_of_nonpos h2 hl2 hm
    have hx2 : (1:ℝ) ≤ x ^ c := Real.one_le_rpow (by linarith : (1:ℝ) ≤ x) hc.le
    have hxe : (1:ℝ) ≤ (2:ℝ) ^ c := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) hc.le
    have hpos : 0 < (2:ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have hxc : (2:ℝ) ^ c ≤ x ^ c := Real.rpow_le_rpow (by norm_num) hx hc.le
    have hlm : 0 < Real.log 2 ^ m := Real.rpow_pos_of_pos h2 m
    have hkey : Real.log 2 ^ m ≤ Real.log 2 ^ m / (2:ℝ) ^ c * x ^ c := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hxc hlm.le
    linarith
  · refine ⟨(c / m) ^ (-m), by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hr : 0 < c / m := by positivity
    have h1 : Real.log x ≤ x ^ (c / m) / (c / m) := log_le_rpow_div hx0 hr
    have hle : Real.log x ^ m ≤ (x ^ (c / m) / (c / m)) ^ m :=
      Real.rpow_le_rpow hl0.le h1 hm.le
    have hrr : (x ^ (c / m) / (c / m)) ^ m = x ^ c / (c / m) ^ m := by
      rw [Real.div_rpow (Real.rpow_pos_of_pos hx0 (c / m)).le hr.le,
        ← Real.rpow_mul hx0.le (c / m) m, show c / m * m = c from by field_simp]
    have key : x ^ c / (c / m) ^ m = (c / m) ^ (-m) * x ^ c := by
      rw [Real.rpow_neg hr.le, div_eq_inv_mul, mul_comm]
    exact hle.trans (le_of_eq (hrr.trans key))


/-- The absorption used at the end of both leaves: a factor `x ^ (-c)` with `c > 0`, times any
fixed log power, is bounded by `C log ^ (-A) x`. -/
private theorem rpow_neg_mul_log_rpow_le {c : ℝ} (hc : 0 < c) (j A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      x ^ (-c) * Real.log x ^ j ≤ C * Real.log x ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ := exists_log_rpow_le_mul_rpow (c := c / 2) (by linarith) (j + A)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log x ^ (j + A) ≤ C * x ^ (c / 2) := hC x hx
  have hsplit : Real.log x ^ (j + A) = Real.log x ^ j * Real.log x ^ A :=
    Real.rpow_add hl0 j A
  have hA0 : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hl0 A
  have hxj : Real.log x ^ j = Real.log x ^ (j + A) / Real.log x ^ A := by
    rw [hsplit, mul_div_cancel_right₀ _ (ne_of_gt hA0)]
  have hxc : 0 < x ^ (-c) := Real.rpow_pos_of_pos hx0 _
  have hgp : (1:ℝ) ≤ x ^ (c / 2) :=
    Real.one_le_rpow (le_trans (by norm_num) hx) (by linarith)
  have hnc : x ^ (-(c / 2)) ≤ 1 := by
    rw [Real.rpow_neg hx0.le]
    simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hgp
  have hlogneg : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hl0.le _
  calc x ^ (-c) * Real.log x ^ j
      = x ^ (-c) * (Real.log x ^ (j + A) / Real.log x ^ A) := by rw [hxj]
    _ ≤ x ^ (-c) * (C * x ^ (c / 2) / Real.log x ^ A) := by
        refine mul_le_mul_of_nonneg_left ?_ hxc.le
        exact div_le_div_of_nonneg_right h1 hA0.le
    _ = C * (x ^ (-c) * x ^ (c / 2)) * Real.log x ^ (-A) := by
        rw [Real.rpow_neg hl0.le, div_eq_mul_inv]; ring
    _ = C * x ^ (-(c / 2)) * Real.log x ^ (-A) := by
        rw [show x ^ (-c) * x ^ (c / 2) = x ^ (-(c / 2)) by
          rw [← Real.rpow_add hx0]; ring_nf]
    _ ≤ C * 1 * Real.log x ^ (-A) := by
        refine mul_le_mul_of_nonneg_right ?_ hlogneg
        exact mul_le_mul_of_nonneg_left hnc hC0.le
    _ = C * Real.log x ^ (-A) := by ring

/-- `log t - log a ≤ (t - a) / a` for `0 < a ≤ t`. -/
private theorem log_sub_log_le_div {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Real.log t - Real.log a ≤ (t - a) / a := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  rw [← Real.log_div ht.ne' ha.ne']
  have h1 : Real.log (t / a) ≤ t / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : t / a - 1 = (t - a) / a := by rw [div_sub_one ha.ne']
  linarith


/-! ### Stage 3: the two objects are the same function of the exponent `α` -/

/-- The Buchstab argument of the leaf, in the exponent variables `α = log a / log Z`,
`β = log b / log Z`: `(s - α - β)/β = log (m/(a b)) / log b` for `s = log m / log Z`. -/
private theorem two_pair_arg_eq {Z m a b : ℝ} (hZ : 0 < Real.log Z) (hm : 0 < m) (ha : 0 < a)
    (hb : 1 < b) :
    (Real.log m / Real.log Z - Real.log a / Real.log Z - Real.log b / Real.log Z) /
        (Real.log b / Real.log Z) = Real.log (m / (a * b)) / Real.log b := by
  have hb0 : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hab : 0 < a * b := by positivity
  rw [Real.log_div hm.ne' hab.ne', Real.log_mul ha.ne' hb0.ne']
  field_simp
  ring


/-- On one cell `a ≤ t ≤ a + 1` with `a ≥ 4`, on which the Buchstab argument is at least one,
the smooth factor `ω(log (m/(a b)) / log b) / (a log a)` moves by at most `8 / (a^2 log a)`.
This is the per cell oscillation that makes `sum_sub_integral_le_of_cell` give a decaying bound
(compare `BuchstabIntegral517.sum_sub_integral_le_of_lipschitz`, whose constant does not decay). -/
private theorem two_pair_cell_osc {ω : ℝ → ℝ} (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {m b a t : ℝ} (hb : 2 ≤ b) (hm : 0 < m) (ha : 4 ≤ a) (ht : a ≤ t) (hta : t ≤ a + 1)
    (hu : 1 ≤ Real.log (m / (t * b)) / Real.log b) :
    |ω (Real.log (m / (t * b)) / Real.log b) / (t * Real.log t) -
        ω (Real.log (m / (a * b)) / Real.log b) / (a * Real.log a)| ≤
      8 / (a ^ 2 * Real.log a) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < Real.log b := Real.log_pos (by linarith)
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
    have h1 : Real.log (1/2:ℝ) ≤ 1/2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (1/2:ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    linarith
  have hlb2 : (1/2:ℝ) ≤ Real.log b := by
    have h : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
    linarith
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlat : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht
  -- the two Buchstab arguments, and their order
  set ua : ℝ := Real.log (m / (a * b)) / Real.log b with hua
  set ut : ℝ := Real.log (m / (t * b)) / Real.log b with hut
  have htab : 0 < t * b := by positivity
  have haab : 0 < a * b := by positivity
  have harg : ut - ua = Real.log (a / t) / Real.log b := by
    rw [hua, hut, ← sub_div, ← Real.log_div (ne_of_gt (by positivity : (0:ℝ) < m / (t * b)))
      (ne_of_gt (by positivity : (0:ℝ) < m / (a * b)))]
    congr 1
    field_simp
  have hlogat : Real.log (a / t) ≤ 0 := by
    apply Real.log_nonpos
    · positivity
    · rw [div_le_one ht0]; exact ht
  have hut_le : ut ≤ ua := by
    have : ut - ua ≤ 0 := by rw [harg]; exact div_nonpos_of_nonpos_of_nonneg hlogat hb1.le
    linarith
  have hua1 : 1 ≤ ua := le_trans hu hut_le
  -- Lipschitz of omega
  have hw : |ω ut - ω ua| ≤ ua - ut := by
    have h1 : |ω ut - ω ua| ≤ |ut - ua| := buchstab_lipschitz_abs hω hz hu hua1
    rw [abs_of_nonpos (by linarith : ut - ua ≤ 0)] at h1
    linarith
  -- the change of the Buchstab argument across the cell
  have hdu : ua - ut ≤ 2 / a := by
    have h2 : ua - ut = Real.log (t / a) / Real.log b := by
      rw [← neg_sub, harg]; rw [show a / t = (t / a)⁻¹ by field_simp]
      rw [Real.log_inv]; ring
    have h3 : Real.log (t / a) ≤ (t - a) / a := by
      rw [Real.log_div ht0.ne' ha0.ne']
      exact log_sub_log_le_div ha0 ht
    have h4 : (t - a) / a ≤ 1 / a :=
      div_le_div_of_nonneg_right (by linarith : t - a ≤ 1) ha0.le
    have h5 : Real.log (t / a) ≤ 1 / a := le_trans h3 h4
    rw [h2]
    have h6 : (1 / a) / (1 / 2) = 2 / a := by field_simp
    calc Real.log (t / a) / Real.log b ≤ (1 / a) / Real.log b :=
          div_le_div_of_nonneg_right h5 hb1.le
      _ ≤ (1 / a) / (1 / 2) := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hlb2
      _ = 2 / a := h6
  -- the difference of the two reciprocal logarithms
  have hlog : |1 / (t * Real.log t) - 1 / (a * Real.log a)| ≤ 6 / (a ^ 2 * Real.log a) := by
    have hkey : 1 / (t * Real.log t) - 1 / (a * Real.log a) =
        (a * Real.log a - t * Real.log t) / (a * t * Real.log a * Real.log t) := by
      field_simp
    have hden : 0 < a * t * Real.log a * Real.log t := by positivity
    have hden2 : a ^ 2 * Real.log a * Real.log a ≤ a * t * Real.log a * Real.log t := by
      have h1 : a * a ≤ a * t := by
        exact mul_le_mul_of_nonneg_left ht ha0.le
      have h2 : Real.log a * Real.log a ≤ Real.log a * Real.log t :=
        mul_le_mul_of_nonneg_left hlat hla.le
      nlinarith
    have htl : t * Real.log t ≥ a * Real.log a := by
      have h1 := mul_le_mul ht hlat hla.le (by linarith : (0:ℝ) ≤ t)
      simpa using h1
    have hnum : |a * Real.log a - t * Real.log t| = t * Real.log t - a * Real.log a := by
      rw [abs_of_nonpos (by linarith)]; ring
    have hnum2 : t * Real.log t - a * Real.log a ≤ (t - a) * (Real.log (a + 1) + 1) := by
      have e1 : t * Real.log t - a * Real.log a =
          (t - a) * Real.log t + a * (Real.log t - Real.log a) := by ring
      have e2 : (t - a) * Real.log t ≤ (t - a) * Real.log (a + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.log_le_log (by linarith) hta
      have e3 : a * (Real.log t - Real.log a) ≤ a * ((t - a) / a) := by
        refine mul_le_mul_of_nonneg_left ?_ ha0.le
        exact log_sub_log_le_div ha0 ht
      have e4 : a * ((t - a) / a) = t - a := by field_simp
      have e5 : (t - a) * Real.log (a + 1) + (t - a) = (t - a) * (Real.log (a + 1) + 1) := by
        ring
      rw [e1]
      nlinarith [e2, e3, e4, e5]
    have hnum3 : (t - a) * (Real.log (a + 1) + 1) ≤ Real.log (a + 1) + 1 := by
      have hX : (0:ℝ) < Real.log (a + 1) + 1 := by
        have h : 0 < Real.log (a + 1) := Real.log_pos (by linarith)
        linarith
      have h1 : (t - a) * (Real.log (a + 1) + 1) ≤ 1 * (Real.log (a + 1) + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hX.le
      linarith
    have hla1 : Real.log (a + 1) ≤ Real.log a + 1 / a := by
      have h := log_sub_log_le_div ha0 (by linarith : a ≤ a + 1)
      have e : a + 1 - a = 1 := by ring
      rw [e] at h
      linarith
    have hla2 : 1 / a ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    have hlog4 : (1:ℝ) ≤ Real.log a := by
      have h : Real.log 4 ≤ Real.log a := Real.log_le_log (by norm_num) ha
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        push_cast; ring
      linarith
    have hb1 : Real.log (a + 1) + 1 ≤ 6 * Real.log a := by
      have : Real.log (a + 1) ≤ Real.log a + 1 / 4 := le_trans hla1 (by linarith [hla2])
      nlinarith
    have hstep : (t * Real.log t - a * Real.log a) / (a * t * Real.log a * Real.log t) ≤
        6 / (a ^ 2 * Real.log a) := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [hnum2, hnum3, hb1, hden2, Real.log_pos (by linarith : (1:ℝ) < a + 1)]
    rw [hkey, abs_div, abs_of_pos hden, hnum]
    calc (t * Real.log t - a * Real.log a) / (a * t * Real.log a * Real.log t) ≤
          6 / (a ^ 2 * Real.log a) := hstep
      _ = 6 / (a ^ 2 * Real.log a) := rfl
  -- assemble
  have hsplit : ω ut / (t * Real.log t) - ω ua / (a * Real.log a) =
      (ω ut - ω ua) / (t * Real.log t) + ω ua * (1 / (t * Real.log t) - 1 / (a * Real.log a)) := by
    field_simp
    ring
  have hw1 : ω ua ≤ 1 := LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz ua
  have hw0 : 0 ≤ ω ua := Decomp514a.two_density_buchstab_nonneg hω hz ua
  have htla : a * Real.log a ≤ t * Real.log t := by
    have h1 := mul_le_mul ht hlat hla.le (by linarith : (0:ℝ) ≤ t)
    simpa using h1
  have hden_t : 0 < t * Real.log t := by positivity
  have h1 : |(ω ut - ω ua) / (t * Real.log t)| ≤ 2 / (a ^ 2 * Real.log a) := by
    have hbnd : |ω ut - ω ua| ≤ 2 / a := le_trans hw hdu
    have hpos : 0 < a ^ 2 * Real.log a := by positivity
    rw [abs_div, abs_of_pos hden_t, div_le_div_iff₀ hden_t hpos]
    have hmul : |ω ut - ω ua| * (a ^ 2 * Real.log a) ≤ (2 / a) * (a ^ 2 * Real.log a) :=
      mul_le_mul_of_nonneg_right hbnd hpos.le
    have heq : (2 / a) * (a ^ 2 * Real.log a) = 2 * (a * Real.log a) := by
      field_simp
    have h2 : 2 * (a * Real.log a) ≤ 2 * (t * Real.log t) := by linarith
    linarith [hmul, heq, h2]
  have h2 : |ω ua * (1 / (t * Real.log t) - 1 / (a * Real.log a))| ≤
      6 / (a ^ 2 * Real.log a) := by
    rw [abs_mul, abs_of_nonneg hw0]
    calc ω ua * |1 / (t * Real.log t) - 1 / (a * Real.log a)|
        ≤ 1 * (6 / (a ^ 2 * Real.log a)) := by
          refine mul_le_mul hw1 hlog (abs_nonneg _) (by norm_num)
      _ = 6 / (a ^ 2 * Real.log a) := one_mul _
  rw [hsplit]
  have := abs_add_le ((ω ut - ω ua) / (t * Real.log t))
    (ω ua * (1 / (t * Real.log t) - 1 / (a * Real.log a)))
  have hsum : 2 / (a ^ 2 * Real.log a) + 6 / (a ^ 2 * Real.log a) =
      8 / (a ^ 2 * Real.log a) := by ring
  linarith [this]


/-- Order transfer: if `t` is not in `[α, α')`, then `α ≤ t` and `α' ≤ t` agree. -/
private theorem le_iff_of_not_switch {α α' t : ℝ} (h : α ≤ α') (hno : ¬(α ≤ t ∧ t ≤ α')) :
    (α ≤ t ↔ α' ≤ t) := by
  constructor
  · intro h1
    by_contra h2
    push_neg at h2
    exact hno ⟨h1, le_of_lt h2⟩
  · intro h1; linarith

/-- Order transfer in the reverse form. -/
private theorem le_iff_of_not_switch' {α α' t : ℝ} (h : α ≤ α') (hno : ¬(α ≤ t ∧ t ≤ α')) :
    (t ≤ α ↔ t ≤ α') := by
  constructor
  · intro h1; linarith
  · intro h1
    by_contra h2
    push_neg at h2
    exact hno ⟨le_of_lt h2, h1⟩

/-- P0069 page 51: the discarded region `E₂` as a function of the first exponent `α`. Every atom of
`lowerTwoDiscarded` is of the form `α ≤ L` or `L ≤ α` with `L` affine in `β`, so between
consecutive switch points the truth value does not change. The hypotheses are the atom-wise
transfers `t ≤ α ↔ t ≤ α'` and `α ≤ t ↔ α' ≤ t` at the fourteen switch points
`1/2`, `β`, `1 - 2β`, `1/2 + c₃ - 2ε - 2β`, `(2 + θ - ε - 7β)/4`, `1/2 - (θ + 3c₁)/4 + ε - β`,
`(2 + θ - ε - 5β)/4`, `1/2 - (θ + c₁)/4 + ε - β`, `(36θ - 2)/11 - ε`, `2β - θ + ε`,
`(2 ∓ (θ - ε) - 3β)/4` and `(2 ∓ (θ - ε) - β)/4`. -/
private theorem sect_same {ε β α α' : ℝ} (hα : α ≤ α')
    (h1 : β ≤ α ↔ β ≤ α') (h2 : α ≤ 1/2 ↔ α' ≤ 1/2)
    (h3 : α + 2*β ≤ 1 ↔ α' + 2*β ≤ 1)
    (h4 : α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε ↔
          α' + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε)
    (h5 : 4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 7*β ≤ 2+2*(1/16-1/10^5)-ε)
    (h6 : 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β)
    (h7 : 4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 5*β ≤ 2+2*(1/16-1/10^5)-ε)
    (h8 : 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β)
    (h11 : 2*β - (2*(1/16-1/10^5)) + ε ≤ α ↔ 2*β - (2*(1/16-1/10^5)) + ε ≤ α')
    (h12 : α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ↔ α' ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
    (h13 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε)
    (h14 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + β - 2| ≤ 2*(1/16-1/10^5)-ε) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α' β) := by
  unfold lowerTwoDiscarded upperPairRegion
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h11, h12, h13, h14]


/-! ### Stage 4: the change of variables `a = Z ^ α` -/

/-- The passage from the exponent `α` to the integer `a`: `dα = da / (a log Z)`, so an integral over
`α ∈ [1/10, 1/2]` is an integral over `a ∈ [Z^(1/10), Z^(1/2)]`. No hypothesis on `g` is needed
(`intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg`, the monotone case). -/
private theorem integral_log_subst {Z : ℝ} (hZ : 1 < Z) (g : ℝ → ℝ) :
    (∫ a in Z ^ (1/10:ℝ)..Z ^ (1/2:ℝ), g (Real.log a / Real.log Z) * (1 / (a * Real.log Z))) =
      ∫ α in (1/10:ℝ)..(1/2:ℝ), g α := by
  have hZ0 : 0 < Z := by linarith
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have ha0 : 0 < Z ^ (1/10:ℝ) := Real.rpow_pos_of_pos hZ0 _
  have hb0 : 0 < Z ^ (1/2:ℝ) := Real.rpow_pos_of_pos hZ0 _
  have hab : Z ^ (1/10:ℝ) ≤ Z ^ (1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hmin : min (Z ^ (1/10:ℝ)) (Z ^ (1/2:ℝ)) = Z ^ (1/10:ℝ) := min_eq_left hab
  have hfa : Real.log (Z ^ (1/10:ℝ)) / Real.log Z = 1/10 := by
    rw [Real.log_rpow hZ0]; field_simp
  have hfb : Real.log (Z ^ (1/2:ℝ)) / Real.log Z = 1/2 := by
    rw [Real.log_rpow hZ0]; field_simp
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f := fun a : ℝ => Real.log a / Real.log Z) (f' := fun a : ℝ => 1 / (a * Real.log Z))
    (a := Z ^ (1/10:ℝ)) (b := Z ^ (1/2:ℝ)) (g := g)
    (by
      refine ContinuousOn.div_const ?_ _
      refine Real.continuousOn_log.mono ?_
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hx0
      rw [Set.uIcc_of_le hab] at hx
      rw [hx0] at hx
      linarith [hx.1])
    (by
      intro x hx
      have hx0 : x ≠ 0 := by
        have h1 : Z ^ (1/10:ℝ) < x := by rw [← hmin]; exact hx.1
        have : (0:ℝ) < Z ^ (1/10:ℝ) := ha0
        linarith
      have hd := (Real.hasDerivAt_log hx0).div_const (Real.log Z)
      convert hd using 1
      field_simp)
    (by
      intro x hx
      have hx0 : 0 < x := by
        have h1 : Z ^ (1/10:ℝ) < x := by rw [← hmin]; exact hx.1
        have : (0:ℝ) < Z ^ (1/10:ℝ) := ha0
        linarith
      positivity)
  rw [hfa, hfb] at h
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h


/-! ### Stage 5: the leaf's summand is the density `Φ` times the weight `1 / (b log^2 b)` -/

/-- The summand of `leaf_two_pair_riemann_first` at `(a, b)` is the density
`[E₂] ω (log (m/(a b)) / log b) / (a log a)` of `leaf_two_pair_riemann_second` at `a`, times the
weight `1 / (b log^2 b)` of the outer variable. This is the only point at which the two leaves
share their integrand; the arithmetic is `1/log b / (a b) * (1/log a * 1/log b) =
1/(a log a) * 1/(b log^2 b)`. -/
private theorem summand_eq_density_weight (ω : ℝ → ℝ) {ε x : ℝ} {m a b : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
        ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
          Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
      else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ))) =
      (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
        ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ))
      else 0) * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
  have ha1 : (1:ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  have hb1 : (1:ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hla : Real.log (a : ℝ) ≠ 0 := ne_of_gt (Real.log_pos ha1)
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hb1)
  by_cases h : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
  · simp only [h, if_true]
    field_simp
  · simp only [h, if_false]
    ring

/-- The support bound: a nonzero summand of `leaf_two_pair_riemann_first` forces
`b ≥ Z ^ (c₁ - ε)`, and `Decomp514a.scaleZ_rpow_ge` turns that into `b ≥ x ^ (11/200)`. This is
what makes the Riemann sum against the integral converge: the lowest admissible integer `b`, and
with it every admissible `a`, is at least `x ^ (11/200)`. -/
private theorem support_ge {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x) {a b : ℕ}
    (h : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)) :
    scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15 - ε) ≤ (b : ℝ) := by
  obtain ⟨hZx, hZ1⟩ := scaleZ_rpow_ge hε hε8 hx
  have hZ0 : 0 < scaleZ ε x := by linarith
  have hlogZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  obtain ⟨hc, -, -, -, -⟩ := h
  have hexp : expo ε x b = Real.log (b : ℝ) / Real.log (scaleZ ε x) := rfl
  rw [hexp] at hc
  have h1 : ((1+7*(2*(1/16-1/10^5)))/15 - ε) * Real.log (scaleZ ε x) ≤ Real.log (b : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_right hc hlogZ.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogZ)] at h2
  have hlogb : 0 < Real.log (b : ℝ) := by
    have h3 : 0 < ((1+7*(2*(1/16-1/10^5)))/15 - ε) * Real.log (scaleZ ε x) := by
      have : (0:ℝ) < (1+7*(2*(1/16-1/10^5)))/15 - ε := by linarith
      positivity
    linarith
  have hbpos : (0:ℝ) < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · rw [h0] at hlogb; simp at hlogb
    · exact_mod_cast h0
  have hZc : 0 < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15 - ε) :=
    Real.rpow_pos_of_pos hZ0 _
  rw [← Real.log_rpow (x := scaleZ ε x)
    (y := (1+7*(2*(1/16-1/10^5)))/15 - ε) hZ0] at h1
  exact (Real.log_le_log_iff hZc hbpos).mp h1


/-! ### Stage 6: the leaf's integral over `α` is the integral of the density over `a` -/

/-- For a fixed `b`, the integral over `α ∈ [1/10, 1/2]` of the leaf's E2 integrand is the integral
over `a ∈ [Z^(1/10), Z^(1/2)]` of the density `Φ_b` at `a = Z^α`. Both the indicator and the
Buchstab argument agree: `(s - α - β)/β = log (m/(a b)) / log b` (`two_pair_arg_eq`) and
`dα / α = da / (a log a)`. -/
private theorem per_b_integral_eq {ω : ℝ → ℝ} {ε x : ℝ} (hZ1 : 1 < scaleZ ε x) {m b : ℕ}
    (hm : 0 < m) (hb2 : 2 ≤ b) :
    (∫ α in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) =
      ∫ a in (scaleZ ε x) ^ (1/10:ℝ)..(scaleZ ε x) ^ (1/2:ℝ),
        if lowerTwoDiscarded ε (Real.log a / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (a * (b : ℝ))) / Real.log (b : ℝ)) /
            (a * Real.log a)
        else 0 := by
  have hZ0 : 0 < scaleZ ε x := by linarith
  have hL : Real.log (scaleZ ε x) ≠ 0 := ne_of_gt (Real.log_pos hZ1)
  have hb1 : (2:ℝ) ≤ b := by exact_mod_cast hb2
  have hlb : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < b))
  have h := integral_log_subst hZ1
    (fun α : ℝ => if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
      else 0)
  rw [← h]
  refine intervalIntegral.integral_congr fun a ha => ?_
  have hmin : min ((scaleZ ε x) ^ (1/10:ℝ)) ((scaleZ ε x) ^ (1/2:ℝ)) = (scaleZ ε x) ^ (1/10:ℝ) :=
    min_eq_left (Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num))
  have ha_ge : (scaleZ ε x) ^ (1/10:ℝ) ≤ a := by
    rw [Set.uIcc, hmin] at ha
    exact ha.1
  have hZt : (1:ℝ) < (scaleZ ε x) ^ (1/10:ℝ) := Real.one_lt_rpow hZ1 (by norm_num)
  have ha1 : (0:ℝ) < a := by linarith
  have ha_gt : (1:ℝ) < a := by linarith
  have hla : Real.log a ≠ 0 := ne_of_gt (Real.log_pos ha_gt)
  have hane : a ≠ 0 := ne_of_gt ha1
  simp only [expo]
  by_cases hind : lowerTwoDiscarded ε (Real.log a / Real.log (scaleZ ε x))
      (Real.log (b : ℝ) / Real.log (scaleZ ε x))
  · simp only [hind, if_true]
    have harg : (Real.log (m : ℝ) / Real.log (scaleZ ε x) - Real.log a / Real.log (scaleZ ε x) -
          Real.log (b : ℝ) / Real.log (scaleZ ε x)) / (Real.log (b : ℝ) / Real.log (scaleZ ε x)) =
        Real.log ((m : ℝ) / (a * (b : ℝ))) / Real.log (b : ℝ) := by
      refine two_pair_arg_eq (Z := scaleZ ε x) ?_ ?_ ?_ ?_
      · exact Real.log_pos hZ1
      · exact_mod_cast hm
      · exact ha1
      · linarith
    rw [harg]
    have hsplit : Real.log a = (Real.log a / Real.log (scaleZ ε x)) * Real.log (scaleZ ε x) := by
      field_simp
    rw [hsplit] at *
    field_simp
  · simp only [hind, if_false]
    ring

/-! ### Stage 7: which cells can carry a jump -/

/-- If a switch point `t` of the exponent lies in the cell `[log a / log Z, log (a+1) / log Z]`,
then `Z ^ t` lies between `a` and `a + 1`. -/
private theorem switch_cell {Z t : ℝ} (hZ : 1 < Z) {a : ℕ} (ha : 1 ≤ a)
    (h1 : Real.log (a : ℝ) / Real.log Z ≤ t)
    (h2 : t ≤ Real.log ((a : ℝ) + 1) / Real.log Z) :
    (a : ℝ) ≤ Z ^ t ∧ Z ^ t ≤ (a : ℝ) + 1 := by
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have hZ0 : 0 < Z := by linarith
  have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have e1 : Real.log (a : ℝ) ≤ t * Real.log Z := by
    have h := mul_le_mul_of_nonneg_right h1 hL.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hL)] at h
  have e2 : Real.log (a : ℝ) ≤ Real.log (Z ^ t) := by
    rw [Real.log_rpow hZ0]
    exact e1
  have e3 : (a : ℝ) ≤ Z ^ t :=
    (Real.log_le_log_iff ha0 (Real.rpow_pos_of_pos hZ0 t)).mp e2
  have f1 : t * Real.log Z ≤ Real.log ((a : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_right h2 hL.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hL)] at h
  have f2 : Real.log (Z ^ t) ≤ Real.log ((a : ℝ) + 1) := by
    rw [Real.log_rpow hZ0]
    exact f1
  have f3 : Z ^ t ≤ (a : ℝ) + 1 :=
    (Real.log_le_log_iff (Real.rpow_pos_of_pos hZ0 t) (by positivity)).mp f2
  exact ⟨e3, f3⟩

/-- The converse form: the index of a cell containing a switch point is the floor of `Z ^ t` or
the floor minus one. At most two integers per switch point, so at most `2 * 14` cells of the sum
carry a jump. -/
private theorem switch_cell_floor {Z t : ℝ} (hZ : 1 < Z) {a : ℕ} (ha : 1 ≤ a)
    (h1 : Real.log (a : ℝ) / Real.log Z ≤ t)
    (h2 : t ≤ Real.log ((a : ℝ) + 1) / Real.log Z) :
    Nat.floor (Z ^ t) = a ∨ Nat.floor (Z ^ t) = a + 1 := by
  obtain ⟨hb1, hb2⟩ := switch_cell hZ ha h1 h2
  have hle : a ≤ Nat.floor (Z ^ t) := Nat.le_floor hb1
  have hlt : Nat.floor (Z ^ t) < a + 2 := by
    have hltR : ((Nat.floor (Z ^ t) : ℕ) : ℝ) < ((a + 2 : ℕ) : ℝ) := by
      have h := Nat.floor_le (show (0:ℝ) ≤ Z ^ t by positivity)
      push_cast
      linarith
    exact_mod_cast hltR
  omega


/-- Only finitely many cells of the sum carry a jump. If each index in `P` has a switch point `t`
of `T` in its cell, then those indices are the floor of `Z ^ t` or one less (`switch_cell_floor`),
so there are at most `2 * T.card` of them: with the fourteen switch points of `sect_same`, at
most `28`. The predicate is a variable so that its argument stays a natural number. -/
private theorem bad_cell_count {Z : ℝ} (hZ : 1 < Z) (T : Finset ℝ) (P : ℕ → Prop)
    (hP : ∀ a : ℕ, P a → ∃ t : ℝ, t ∈ T ∧
      Real.log (a : ℝ) / Real.log Z ≤ t ∧ t ≤ Real.log ((a : ℝ) + 1) / Real.log Z)
    {A B : ℕ} (hA : 1 ≤ A) :
    ((Finset.Ioc A B).filter P).card ≤ 2 * T.card := by
  set S : Finset ℕ := (T.image (fun t => Nat.floor (Z ^ t))) ∪
    (T.image (fun t => Nat.floor (Z ^ t) - 1)) with hS
  have hsub : (Finset.Ioc A B).filter P ⊆ S := by
    intro a ha
    obtain ⟨hain, hPa⟩ := Finset.mem_filter.mp ha
    obtain ⟨t, htT, h1, h2⟩ := hP a hPa
    have haA : 1 ≤ a := le_trans hA (le_of_lt (Finset.mem_Ioc.mp hain).1)
    have hfl := switch_cell_floor hZ haA h1 h2
    rw [hS]
    simp only [Finset.mem_union, Finset.mem_image]
    rcases hfl with h | h
    · exact Or.inl ⟨t, htT, h⟩
    · exact Or.inr ⟨t, htT, by omega⟩
  calc ((Finset.Ioc A B).filter P).card ≤ S.card := Finset.card_le_card hsub
    _ ≤ (T.image (fun t => Nat.floor (Z ^ t))).card +
          (T.image (fun t => Nat.floor (Z ^ t) - 1)).card := Finset.card_union_le _ _
    _ ≤ T.card + T.card := by
        have h1 := Finset.card_image_le (s := T) (f := fun t => Nat.floor (Z ^ t))
        have h2 := Finset.card_image_le (s := T) (f := fun t => Nat.floor (Z ^ t) - 1)
        omega
    _ = 2 * T.card := by ring


/-! ### Stage 8: the density vanishes outside the support -/

/-- The density is zero to the left of `b`: `E₂` needs `β ≤ α`, i.e. `b ≤ a`. This is what lets
the sum over `Ioc b M` be replaced by a sum over the aligned integer range, since `support_ge`
puts every admissible `b` above `Z ^ (c₁ - ε) > Z ^ (1/10)`. -/
private theorem density_zero_of_lt {ε Z : ℝ} (hZ : 1 < Z) (ω : ℝ → ℝ) {m a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    (if lowerTwoDiscarded ε (Real.log a / Real.log Z) (Real.log b / Real.log Z) then
        ω (Real.log (m / (a * b)) / Real.log b) / (a * Real.log a) else 0) = 0 := by
  rw [if_neg]
  intro h
  obtain ⟨-, hba, -, -, -⟩ := h
  have hL : 0 < Real.log Z := Real.log_pos hZ
  have h1 : Real.log b ≤ Real.log a := by
    have h2 := mul_le_mul_of_nonneg_right hba hL.le
    have h3 : Real.log a / Real.log Z * Real.log Z = Real.log a :=
      div_mul_cancel₀ _ (ne_of_gt hL)
    have h4 : Real.log b / Real.log Z * Real.log Z = Real.log b :=
      div_mul_cancel₀ _ (ne_of_gt hL)
    linarith
  have h3 : b ≤ a := (Real.log_le_log_iff hb ha).mp h1
  linarith

/-- The density is zero to the right of `α = 1/2`: `E₂` needs `α ≤ 1/2`. So a summand with
`a > Z ^ (1/2)` vanishes, and the sum can stop at `⌊Z ^ (1/2)⌋`. -/
private theorem density_zero_of_half_lt {ε Z : ℝ} (hZ : 1 < Z) (ω : ℝ → ℝ) {m a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 1/2 < Real.log a / Real.log Z) :
    (if lowerTwoDiscarded ε (Real.log a / Real.log Z) (Real.log b / Real.log Z) then
        ω (Real.log (m / (a * b)) / Real.log b) / (a * Real.log a) else 0) = 0 := by
  rw [if_neg]
  intro h
  obtain ⟨-, -, hle, -, -⟩ := h
  linarith




/-! ### Stage 9: per cell oscillation of the density in the integer variable -/

/-- The density `Φ_b` of `leaf_two_pair_riemann_first` in the integer variable `t`:
`[E₂] ω (log (m/(t b)) / log b) / (t log t)`. -/
private theorem density_abs_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m t : ℝ} {b : ℕ} (ht : 2 ≤ t) (hb : 2 ≤ b) :
    abs (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0) ≤
      1 / (t * Real.log t) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hpos : (0:ℝ) < t * Real.log t := by positivity
  have hw1 : ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _
  have hw0 : 0 ≤ ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) :=
    Decomp514a.two_density_buchstab_nonneg hω hz _
  by_cases h : lowerTwoDiscarded ε (Real.log t / Real.log Z) β
  · rw [if_pos h, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, hw1⟩) hpos.le
  · rw [if_neg h, abs_zero]
    positivity

/-- The crude cell oscillation: on the cell `[a, a+1]` the density moves by at most
`2 / (a log a)`, with no condition on the discarded region or on the Buchstab argument. -/
private theorem cell_osc_crude {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m t : ℝ} {b : ℕ} (hb : 2 ≤ b) {a : ℕ} (ha : 2 ≤ a)
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (a : ℝ) + 1) :
    abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      2 / ((a : ℝ) * Real.log a) := by
  have ha2 : (2:ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0:ℝ) < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have ht2 : (2:ℝ) ≤ t := le_trans ha2 ht1
  have ha1 : (2:ℝ) ≤ (a:ℝ) + 1 := by linarith
  have h1 := density_abs_le hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) ha1 hb
  have h2 := density_abs_le hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) ht2 hb
  -- monotonicity of `x log x` on `[2, ∞)`
  have hmono : ∀ x y : ℝ, 2 ≤ x → x ≤ y → x * Real.log x ≤ y * Real.log y := by
    intro x y hx hxy
    have hx0 : (0:ℝ) < x := by linarith
    have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hlxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    have hy0 : (0:ℝ) ≤ y := by linarith
    calc x * Real.log x ≤ y * Real.log x := by
          exact mul_le_mul_of_nonneg_right hxy hl
      _ ≤ y * Real.log y := by
          exact mul_le_mul_of_nonneg_left hlxy hy0
  have hbase : (0:ℝ) < a * Real.log a := by positivity
  have hle1 : 1 / (((a:ℝ) + 1) * Real.log ((a:ℝ) + 1)) ≤ 1 / (a * Real.log a) :=
    one_div_le_one_div_of_le hbase (hmono a ((a:ℝ)+1) ha2 (by linarith))
  have hle2 : 1 / (t * Real.log t) ≤ 1 / (a * Real.log a) :=
    one_div_le_one_div_of_le hbase (hmono a t ha2 ht1)
  have htri : abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      1 / (((a:ℝ) + 1) * Real.log ((a:ℝ) + 1)) + 1 / (t * Real.log t) := by
    refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
    · have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      linarith [h1'.2, h2'.1]
    · have h1' := abs_le.mp h1
      have h2' := abs_le.mp h2
      linarith [h1'.1, h2'.2]
  have hfin : 1 / (((a:ℝ) + 1) * Real.log ((a:ℝ) + 1)) + 1 / (t * Real.log t) ≤
      2 / ((a:ℝ) * Real.log a) := by
    have e : 1 / ((a:ℝ) * Real.log a) + 1 / ((a:ℝ) * Real.log a) = 2 / ((a:ℝ) * Real.log a) := by ring
    linarith
  linarith [htri, hfin]



/-! ### Stage 10: the discarded region is constant on a cell with no switch point -/

/-- P0069 page 51: if none of the fourteen switch points of the discarded region `E₂` lies in
`[α, α']`, then the region takes the same value at `α` and at `α'`. This is `sect_same` with its
twelve atom-wise transfers read off from the absence of the corresponding switch point. -/
private theorem cell_region_const {ε β α α' : ℝ} (hα : α ≤ α')
    (h1 : ¬(α ≤ β ∧ β ≤ α'))
    (h2 : ¬(α ≤ 1/2 ∧ (1/2 : ℝ) ≤ α'))
    (h3 : ¬(α ≤ 1 - 2*β ∧ 1 - 2*β ≤ α'))
    (h4 : ¬(α ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β ∧
            1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β ≤ α'))
    (h5 : ¬(α ≤ (2 + 2*(1/16-1/10^5) - ε - 7*β)/4 ∧
            (2 + 2*(1/16-1/10^5) - ε - 7*β)/4 ≤ α'))
    (h6 : ¬(α ≤ 1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ∧
            1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α'))
    (h7 : ¬(α ≤ (2 + 2*(1/16-1/10^5) - ε - 5*β)/4 ∧
            (2 + 2*(1/16-1/10^5) - ε - 5*β)/4 ≤ α'))
    (h8 : ¬(α ≤ 1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ∧
            1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α'))
    (h10 : ¬(α ≤ 2*β - 2*(1/16-1/10^5) + ε ∧ 2*β - 2*(1/16-1/10^5) + ε ≤ α'))
    (h11 : ¬(α ≤ (36*(2*(1/16-1/10^5)) - 2)/11 - ε ∧ (36*(2*(1/16-1/10^5)) - 2)/11 - ε ≤ α'))
    (h12a : ¬(α ≤ (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
              (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α'))
    (h12b : ¬(α ≤ (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
              (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α'))
    (h13a : ¬(α ≤ (2 - (2*(1/16-1/10^5) - ε) - β)/4 ∧
              (2 - (2*(1/16-1/10^5) - ε) - β)/4 ≤ α'))
    (h13b : ¬(α ≤ (2 + (2*(1/16-1/10^5) - ε) - β)/4 ∧
              (2 + (2*(1/16-1/10^5) - ε) - β)/4 ≤ α')) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α' β) := by
  -- the atom-wise transfers
  have e1 : β ≤ α ↔ β ≤ α' := le_iff_of_not_switch' hα h1
  have e2 : α ≤ 1/2 ↔ α' ≤ 1/2 := le_iff_of_not_switch hα h2
  have e3 : α + 2*β ≤ 1 ↔ α' + 2*β ≤ 1 := by
    have a1 : (α + 2*β ≤ 1) ↔ (α ≤ 1 - 2*β) := by constructor <;> intro h <;> linarith
    have a2 : (α' + 2*β ≤ 1) ↔ (α' ≤ 1 - 2*β) := by constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h3).trans a2.symm)
  have e4 : α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε ↔
      α' + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε := by
    have a1 : (α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε) ↔
        (α ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β) := by
      constructor <;> intro h <;> linarith
    have a2 : (α' + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε) ↔
        (α' ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β) := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h4).trans a2.symm)
  have e5 : 4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 7*β ≤ 2+2*(1/16-1/10^5)-ε := by
    have a1 : (4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α ≤ (2 + 2*(1/16-1/10^5) - ε - 7*β)/4) := by
      constructor <;> intro h <;> linarith
    have a2 : (4*α' + 7*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α' ≤ (2 + 2*(1/16-1/10^5) - ε - 7*β)/4) := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h5).trans a2.symm)
  have e6 : 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
      1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β := by
    have a1 : (1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α) := by
      constructor <;> intro h <;> linarith
    have a2 : (1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α') := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch' hα h6).trans a2.symm)
  have e7 : 4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α' + 5*β ≤ 2+2*(1/16-1/10^5)-ε := by
    have a1 : (4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α ≤ (2 + 2*(1/16-1/10^5) - ε - 5*β)/4) := by
      constructor <;> intro h <;> linarith
    have a2 : (4*α' + 5*β ≤ 2+2*(1/16-1/10^5)-ε) ↔
        (α' ≤ (2 + 2*(1/16-1/10^5) - ε - 5*β)/4) := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch hα h7).trans a2.symm)
  have e8 : 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
      1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β := by
    have a1 : (1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α) := by
      constructor <;> intro h <;> linarith
    have a2 : (1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α' + β) ↔
        (1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β ≤ α') := by
      constructor <;> intro h <;> linarith
    exact a1.trans ((le_iff_of_not_switch' hα h8).trans a2.symm)
  have e11 : 2*β - (2*(1/16-1/10^5)) + ε ≤ α ↔ 2*β - (2*(1/16-1/10^5)) + ε ≤ α' :=
    le_iff_of_not_switch' hα h10
  have e12 : α ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ↔ α' ≤ (36*(2*(1/16-1/10^5))-2)/11-ε :=
    le_iff_of_not_switch hα h11
  have e13 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε := by
    have a1 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α ≤ (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α) := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have a2 : |4*α' + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α' ≤ (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4 ≤ α') := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [a1, a2]
    exact and_congr (le_iff_of_not_switch hα h12b) (le_iff_of_not_switch' hα h12a)
  have e14 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α' + β - 2| ≤ 2*(1/16-1/10^5)-ε := by
    have a1 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α ≤ (2 + (2*(1/16-1/10^5) - ε) - β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - β)/4 ≤ α) := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have a2 : |4*α' + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔
        (α' ≤ (2 + (2*(1/16-1/10^5) - ε) - β)/4 ∧
          (2 - (2*(1/16-1/10^5) - ε) - β)/4 ≤ α') := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [a1, a2]
    exact and_congr (le_iff_of_not_switch hα h13b) (le_iff_of_not_switch' hα h13a)
  exact sect_same hα e1 e2 e3 e4 e5 e6 e7 e8 e11 e12 e13 e14



/-- The Buchstab argument `log (m/(t b)) / log b` is nonincreasing in `t > 0`. -/
private theorem two_pair_arg_anti {m b t t' : ℝ} (hm : 0 < m) (hb : 1 < b)
    (ht : 0 < t) (htt : t ≤ t') :
    Real.log (m / (t' * b)) / Real.log b ≤ Real.log (m / (t * b)) / Real.log b := by
  have hb0 : 0 < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb
  have ht'0 : 0 < t' := lt_of_lt_of_le ht htt
  have htbh : 0 < t * b := by positivity
  have htb'h : 0 < t' * b := by positivity
  have hle : m / (t' * b) ≤ m / (t * b) := by
    apply div_le_div_of_nonneg_left hm.le htbh
    exact mul_le_mul_of_nonneg_right htt hb0.le
  have hlt : Real.log (m / (t' * b)) ≤ Real.log (m / (t * b)) :=
    Real.log_le_log (by positivity) hle
  exact div_le_div_of_nonneg_right hlt hlb.le

/-- The good cell: on a cell on which the discarded region does not change and the Buchstab
argument stays at least one, the density moves by at most `16 / (a^2 log a)`. This is
`two_pair_cell_osc` applied at the two endpoints of the cell. -/
private theorem cell_osc_good {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m t : ℝ} {b : ℕ} (hb : 2 ≤ b) (hm : 0 < m) {a : ℕ} (ha : 4 ≤ a)
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (a : ℝ) + 1)
    (hreg : lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β ↔
            lowerTwoDiscarded ε (Real.log t / Real.log Z) β)
    (hu : 1 ≤ Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) :
    abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      16 / ((a : ℝ) ^ 2 * Real.log a) := by
  have haR : (4:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have ha0 : (0:ℝ) < a := by linarith
  have ha1pos : (0:ℝ) < (a:ℝ) + 1 := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by linarith : (0:ℝ) < a) ht1
  by_cases hD : lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β
  · have hDt : lowerTwoDiscarded ε (Real.log t / Real.log Z) β := hreg.mp hD
    simp only [hD, hDt, if_true]
    have hu2 : 1 ≤ Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ) :=
      le_trans hu (two_pair_arg_anti hm (by linarith : (1:ℝ) < b) ht0 ht2)
    have h1 := two_pair_cell_osc hω hz (m := m) (b := (b:ℝ)) (a := (a:ℝ))
      (t := (a:ℝ) + 1) hbR hm haR (by linarith) le_rfl hu
    have h2 := two_pair_cell_osc hω hz (m := m) (b := (b:ℝ)) (a := (a:ℝ))
      (t := t) hbR hm haR ht1 ht2 hu2
    have hpos : (0:ℝ) < (a:ℝ) ^ 2 * Real.log a := by
      have : (0:ℝ) < Real.log a := Real.log_pos (by linarith)
      positivity
    have e : ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) -
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) =
        (ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) -
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log a)) +
        (ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) / ((a : ℝ) * Real.log a) -
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)) := by
      ring
    rw [e]
    have h3 : abs (ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
        ((a : ℝ) * Real.log a) -
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)) =
        abs (ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) -
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log a)) := abs_sub_comm _ _
    have h4 := abs_add_le (ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) -
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log a))
      (ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) / ((a : ℝ) * Real.log a) -
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t))
    rw [h3] at h4
    have hfin : 8 / ((a : ℝ) ^ 2 * Real.log a) + 8 / ((a : ℝ) ^ 2 * Real.log a) =
        16 / ((a : ℝ) ^ 2 * Real.log a) := by ring
    linarith [h1, h2, h4]
  · have hDt : ¬ lowerTwoDiscarded ε (Real.log t / Real.log Z) β :=
      fun h => hD (hreg.mpr h)
    simp only [hD, hDt, if_false, sub_zero, abs_zero]
    have : (0:ℝ) < Real.log a := Real.log_pos (by linarith)
    positivity



/-! ### Stage 11: measurability, integrability and two summation bounds -/

/-- Buchstab's function is measurable: continuous off the single point `1`. -/
private theorem measurable_buchstab {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) : Measurable ω := by
  refine measurable_of_continuousOn_compl_singleton (1 : ℝ) ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] ω := by
      filter_upwards [isOpen_Iio.mem_nhds h] with y hy
      exact (hz y hy).symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  · exact (hω.1.continuousAt (Ici_mem_nhds h)).continuousWithinAt

/-- The density is measurable. -/
private theorem measurable_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    (ε Z β : ℝ) (m : ℝ) (b : ℕ) :
    Measurable (fun t : ℝ => if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0) := by
  have hωm : Measurable ω := measurable_buchstab hω hz
  have hs : MeasurableSet {t : ℝ | lowerTwoDiscarded ε (Real.log t / Real.log Z) β} := by
    unfold lowerTwoDiscarded upperPairRegion
    measurability
  have hf : Measurable (fun t : ℝ =>
      ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)) := by
    measurability
  exact Measurable.ite hs hf measurable_const

/-- The density is interval integrable on `[u, v]` for `u ≥ 2`. -/
private theorem intervalIntegrable_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m : ℝ} {b : ℕ} (hb : 2 ≤ b) {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t : ℝ => if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)
      volume u v := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le huv]
  have hmeas := (measurable_density hω hz ε Z β m b).aestronglyMeasurable (μ := volume)
  refine MeasureTheory.Integrable.of_bound hmeas.restrict 1 ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  have hx2 : 2 ≤ x := le_trans hu (le_of_lt hx.1)
  have hb1 := density_abs_le hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) hx2 hb
  have hx0 : (0:ℝ) < x := by linarith
  have hl : (1/2:ℝ) ≤ Real.log x := by
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
    have h2' : (1/2:ℝ) ≤ Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    linarith
  have hden : (1:ℝ) ≤ x * Real.log x := by nlinarith [hx2, hl]
  have hpos : (0:ℝ) < x * Real.log x := by nlinarith [hx0, hl]
  have hle : 1 / (x * Real.log x) ≤ 1 := by
    rw [div_le_one hpos]
    exact hden
  rw [Real.norm_eq_abs]
  exact hb1.trans hle

/-- An interval integral of a function that vanishes on the open interval is zero: the end points
carry no mass. -/
private theorem integral_eq_zero_of_open {f : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (h : ∀ x, u < x → x < v → f x = 0) : (∫ x in u..v, f x) = 0 := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
    intervalIntegral.integral_zero]
  rw [MeasureTheory.ae_iff]
  have hsub : {x : ℝ | ¬(x ∈ Set.uIoc u v → f x = 0)} ⊆ {v} := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_imp] at hx
    obtain ⟨hxin, hfx⟩ := hx
    have hxv : x = v := by
      by_contra hne
      rw [Set.uIoc_of_le huv] at hxin
      exact hfx (h x hxin.1 (lt_of_le_of_ne hxin.2 hne))
    simp [hxv]
  exact measure_mono_null hsub (measure_singleton v)

/-- `∑_{A < a ≤ B} 1 / a^2 ≤ 1 / A` for `A ≥ 1`. -/
private theorem sum_inv_sq_le {A B : ℕ} (hA : 1 ≤ A) :
    (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2)) ≤ 1 / (A : ℝ) := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  rcases le_or_gt A B with h | h
  · have := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := A) (n := B) (by omega) h
    have he : (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2)) =
        ∑ a ∈ Finset.Ioc A B, (((a : ℝ)) ^ 2)⁻¹ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [one_div]
    rw [he]
    refine this.trans ?_
    have hB0 : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
    have hle : 0 ≤ ((B:ℝ))⁻¹ := by positivity
    rw [← one_div]
    linarith
  · have hempty : Finset.Ioc A B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- `∑_{A < a ≤ B} 1 / (a^2 log a) ≤ 2 / (A log A)` for `A ≥ 2`. -/
private theorem inv_sq_log_sum_le {A B : ℕ} (hA : 2 ≤ A) :
    (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ))) ≤
      2 / ((A : ℝ) * Real.log (A : ℝ)) := by
  have hA0 : (0:ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hA2 : (2:ℝ) ≤ A := by exact_mod_cast hA
  have hlogA : 0 < Real.log (A:ℝ) := by
    have h2 : Real.log 2 ≤ Real.log (A:ℝ) := Real.log_le_log (by norm_num) hA2
    have h2' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have step : ∀ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ)) ≤
      (1 / Real.log (A:ℝ)) * (1 / ((a : ℝ) ^ 2)) := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp ha
    have haA : (2:ℝ) ≤ a := by
      have : (A:ℝ) ≤ a := by exact_mod_cast le_of_lt h1
      linarith
    have ha0 : (0:ℝ) < a := by linarith
    have hla : 0 < Real.log (a:ℝ) := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 2) haA
      have h2' : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hlogle : Real.log (A:ℝ) ≤ Real.log (a:ℝ) := by
      apply Real.log_le_log hA0
      exact_mod_cast le_of_lt h1
    have h1' : 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ)) ≤ 1 / ((a : ℝ) ^ 2 * Real.log (A:ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (0:ℝ) < (a:ℝ)^2 := by positivity
      exact mul_le_mul_of_nonneg_left hlogle this.le
    have h2' : 1 / ((a : ℝ) ^ 2 * Real.log (A:ℝ)) = (1 / Real.log (A:ℝ)) * (1 / ((a : ℝ) ^ 2)) := by
      field_simp
    linarith [h1', h2'.le, h2'.ge]
  calc (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2 * Real.log (a : ℝ)))
      ≤ ∑ a ∈ Finset.Ioc A B, (1 / Real.log (A:ℝ)) * (1 / ((a : ℝ) ^ 2)) :=
        Finset.sum_le_sum step
    _ = (1 / Real.log (A:ℝ)) * (∑ a ∈ Finset.Ioc A B, 1 / ((a : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ (1 / Real.log (A:ℝ)) * (1 / (A:ℝ)) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_sq_le (by omega)) (by positivity)
    _ ≤ 2 / ((A:ℝ) * Real.log (A:ℝ)) := by
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hA0 hlogA]



/-! ### Stage 12: the switch points as one finset -/

/-- The fourteen switch points of the discarded region `E₂` as a finset. -/
private theorem cell_region_const_auto {ε β α α' : ℝ} (hα : α ≤ α')
    (hno : ∀ τ ∈ ([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset,
        ¬(α ≤ τ ∧ τ ≤ α')) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α' β) :=
  cell_region_const hα
    (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp))
    (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp))
    (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp)) (hno _ (by simp))
    (hno _ (by simp)) (hno _ (by simp))

/-- The good cell oscillation of the density: the discarded region does not change across the cell
and the Buchstab argument does not cross `1`. -/
private theorem cell_osc_density {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} {m : ℝ} {b : ℕ} (hb : 2 ≤ b) (hm : 0 < m) {a : ℕ} (ha : 4 ≤ a) {t : ℝ}
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (a : ℝ) + 1)
    (hreg : lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β ↔
            lowerTwoDiscarded ε (Real.log t / Real.log Z) β)
    (hcase : 1 ≤ Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ) ∨
             Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ) < 1) :
    abs ((if lowerTwoDiscarded ε (Real.log ((a : ℝ) + 1) / Real.log Z) β then
        ω (Real.log (m / (((a : ℝ) + 1) * (b : ℝ))) / Real.log (b : ℝ)) /
          (((a : ℝ) + 1) * Real.log ((a : ℝ) + 1)) else 0) -
      (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)) ≤
      16 / ((a : ℝ) ^ 2 * Real.log a) := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have haR : (4:ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1:ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hpos : (0:ℝ) < (a:ℝ)^2 * Real.log a := by positivity
  rcases hcase with hu | hlt
  · exact cell_osc_good hω hz hb hm ha ht1 ht2 hreg hu
  · -- the Buchstab argument is below one on the whole cell, so both values vanish
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht1
    have h1 : Real.log (m / (((a:ℝ)+1) * (b:ℝ))) / Real.log (b:ℝ) < 1 :=
      lt_of_le_of_lt (two_pair_arg_anti hm hbR (by linarith) (by linarith)) hlt
    have h2 : Real.log (m / (t * (b:ℝ))) / Real.log (b:ℝ) < 1 :=
      lt_of_le_of_lt (two_pair_arg_anti hm hbR ha0 ht1) hlt
    have e1 : (if lowerTwoDiscarded ε (Real.log ((a:ℝ)+1) / Real.log Z) β then
        ω (Real.log (m / (((a:ℝ)+1) * (b:ℝ))) / Real.log (b:ℝ)) /
          (((a:ℝ)+1) * Real.log ((a:ℝ)+1)) else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε (Real.log ((a:ℝ)+1) / Real.log Z) β
      · rw [if_pos hD, hz _ h1]
        ring
      · rw [if_neg hD]
    have e2 : (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
        ω (Real.log (m / (t * (b:ℝ))) / Real.log (b:ℝ)) / (t * Real.log t) else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε (Real.log t / Real.log Z) β
      · rw [if_pos hD, hz _ h2]
        ring
      · rw [if_neg hD]
    rw [e1, e2, sub_zero, abs_zero]
    positivity

/-- Reindexing a sum over `Ioc A B` by `n ↦ n - 1`. -/
private theorem sum_Ioc_shift {A B : ℕ} (hA : 1 ≤ A) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc A B, g (n - 1)) = ∑ a ∈ Finset.Ioc (A - 1) (B - 1), g a := by
  refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro n1 hn1 n2 hn2 he
    obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hn1
    obtain ⟨h3, _⟩ := Finset.mem_Ioc.mp hn2
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp ha
    refine ⟨a + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro n hn
    rfl

/-- Reindexing a filtered cardinality over `Ioc A B` by `n ↦ n - 1`. -/
private theorem card_filter_Ioc_shift {A B : ℕ} (hA : 1 ≤ A) (P : ℕ → Prop) :
    ((Finset.Ioc A B).filter (fun n => P (n - 1))).card =
      ((Finset.Ioc (A - 1) (B - 1)).filter P).card := by
  refine Finset.card_bij (fun n _ => n - 1) ?_ ?_ ?_
  · intro n hn
    obtain ⟨hin, hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hin
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hP⟩
  · intro n1 hn1 n2 hn2 he
    obtain ⟨hin, _⟩ := Finset.mem_filter.mp hn1
    obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hin
    omega
  · intro a ha
    obtain ⟨hin, hP⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hin
    exact ⟨a + 1, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩,
      by simpa using hP⟩, by omega⟩



/-! ### Stage 13: the per-`b` Riemann comparison, sum against integral -/

/-- P0069 page 51 display 5.17, the passage from the sum over the first outer variable to the
integral, for one fixed second variable `b`: the sum over the integers `a` of the E2 density is
the integral over the exponent range, up to `200 / (b log b)`. The sum is taken over the integers
as they stand, cell by cell; on each cell the density moves by `16 / (a^2 log a)`, except on the
at most `28` cells that carry a switch point of the discarded region and the at most `2` cells
that carry the point at which the Buchstab argument crosses one, where the crude bound
`2 / (a log a)` is used. -/
private theorem per_b_riemann {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z β : ℝ} (hZ : 1 < Z) (hZ4 : 4 ≤ Z) (hZ10 : (2:ℝ) ≤ Z ^ (1/10:ℝ)) (hβ : 0 < β)
    {m : ℝ} (hm : 0 < m) {b M : ℕ} (hb : 4 ≤ b) (hbM : b ≤ M)
    (hbZ : Z ^ (1/10:ℝ) ≤ (b:ℝ)) (hbZ2 : (b:ℝ) ≤ Z ^ (1/2:ℝ)) (hM : Z ^ (1/2:ℝ) ≤ (M:ℝ))
    (hβb : β = Real.log (b:ℝ) / Real.log Z) :
    abs ((∑ a ∈ Finset.Ioc b M,
        (if lowerTwoDiscarded ε (Real.log (a:ℝ) / Real.log Z) β then
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0))
      - (∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)))
      ≤ 100 / ((b : ℝ) * Real.log (b : ℝ)) := by
  have hb2 : 2 ≤ b := by omega
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb2
  have hb0 : (0:ℝ) < (b:ℝ) := by linarith
  have hb1 : (1:ℝ) < b := by linarith
  have hlb : 0 < Real.log (b:ℝ) := Real.log_pos hb1
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : 0 < Real.log Z := Real.log_pos hZ
  set φ : ℝ → ℝ := fun t => if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
      ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0 with hφ
  -- the switch points and the two kinds of bad cell
  set bad1 : ℕ → Prop := fun a => ∃ τ ∈ ([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset,
      Real.log (a:ℝ) / Real.log Z ≤ τ ∧ τ ≤ Real.log ((a:ℝ)+1) / Real.log Z with hbad1
  set bad2 : ℕ → Prop := fun a =>
      Real.log (a:ℝ) / Real.log Z ≤ Real.log m / Real.log Z - 2*β ∧
      Real.log m / Real.log Z - 2*β ≤ Real.log ((a:ℝ)+1) / Real.log Z with hbad2
  set bad : ℕ → Prop := fun a => bad1 a ∨ bad2 a with hbad
  set δ : ℕ → ℝ := fun n => 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)) +
      (if bad (n-1) then 2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0) with hδ
  -- integrability of the density on the cells
  have hcell : ∀ n : ℕ, b < n → IntervalIntegrable φ volume ((n:ℝ)-1) (n:ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnb : (b:ℝ) ≤ (n:ℝ) - 1 := by
      have h1 : b + 1 ≤ n := by omega
      have h2 : (b:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h1
      linarith
    have hu2 : 2 ≤ (n:ℝ) - 1 := le_trans hbR hnb
    have hle : (n:ℝ) - 1 ≤ (n:ℝ) := by linarith
    rw [hφ]
    exact intervalIntegrable_density hω hz hb2 hu2 hle
  -- the per cell oscillation
  have hosc : ∀ n : ℕ, b < n → ∀ t ∈ Set.Icc ((n:ℝ)-1) (n:ℝ), abs (φ (n:ℝ) - φ t) ≤ δ n := by
    intro n hn t ht
    have hn1 : 1 ≤ n := by omega
    have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
      push_cast [Nat.cast_sub hn1]; ring
    have hcast1 : (((n - 1 : ℕ)) : ℝ) + 1 = (n:ℝ) := by rw [hcast]; ring
    have ha4 : 4 ≤ n - 1 := by omega
    have ha2 : 2 ≤ n - 1 := by omega
    have haR : (4:ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast ha4
    have ha0 : (0:ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
    have hla : 0 < Real.log (((n - 1 : ℕ)) : ℝ) := Real.log_pos (by linarith)
    have ht1 : (((n - 1 : ℕ)) : ℝ) ≤ t := by rw [hcast]; linarith [ht.1]
    have ht2 : t ≤ (((n - 1 : ℕ)) : ℝ) + 1 := by rw [hcast1]; exact ht.2
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht1
    have hk4 : 1 ≤ n - 1 := by omega
    have hcrude : abs (φ (n:ℝ) - φ t) ≤ 2 / ((((n - 1 : ℕ)) : ℝ) * Real.log (((n - 1 : ℕ)) : ℝ)) := by
      have h := cell_osc_crude hω hz (ε := ε) (Z := Z) (β := β) (m := m) (b := b) hb2
        (a := n - 1) ha2 ht1 ht2
      rw [hcast1] at h
      simpa only [hφ] using h
    rw [hδ]
    beta_reduce
    rw [← hcast]
    by_cases hbc : bad (n-1)
    · rw [if_pos hbc]
      have h2 : (0:ℝ) ≤ 16 / ((((n - 1 : ℕ)) : ℝ) ^ 2 * Real.log (((n - 1 : ℕ)) : ℝ)) :=
        div_nonneg (by norm_num) (by positivity)
      linarith [hcrude]
    · rw [if_neg hbc, add_zero]
      obtain ⟨hb1', hb2'⟩ := not_or.mp hbc
      -- the discarded region does not change across the cell
      have hno : ∀ τ ∈ ([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset,
          ¬(Real.log t / Real.log Z ≤ τ ∧ τ ≤ Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z) := by
        intro τ hτ hτin
        apply hb1'
        exact ⟨τ, hτ, by
          have := div_le_div_of_nonneg_right (Real.log_le_log ha0 ht1) hLZ.le
          linarith [hτin.1], hτin.2⟩
      have hαn : Real.log t / Real.log Z ≤ Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z := by
        rw [hcast1]
        exact div_le_div_of_nonneg_right (Real.log_le_log ht0 ht.2) hLZ.le
      have hreg : lowerTwoDiscarded ε (Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z) β ↔
          lowerTwoDiscarded ε (Real.log t / Real.log Z) β :=
        (cell_region_const_auto (ε := ε) (β := β) hαn hno).symm
      -- the Buchstab argument does not cross one
      have hcase : 1 ≤ Real.log (m / (((((n - 1 : ℕ)) : ℝ) + 1) * (b:ℝ))) / Real.log (b:ℝ) ∨
          Real.log (m / ((((n - 1 : ℕ)) : ℝ) * (b:ℝ))) / Real.log (b:ℝ) < 1 := by
        by_cases hle : Real.log m / Real.log Z - 2*β < Real.log (((n - 1 : ℕ)) : ℝ) / Real.log Z
        · right
          have harg : Real.log (m / ((((n - 1 : ℕ)) : ℝ) * (b:ℝ))) / Real.log (b:ℝ) =
              (Real.log m / Real.log Z - Real.log (((n - 1 : ℕ)) : ℝ) / Real.log Z - β) / β := by
            rw [hβb]
            exact (two_pair_arg_eq hLZ hm ha0 hb1).symm
          rw [harg, div_lt_one hβ]
          linarith
        · left
          have hstep : Real.log (((n - 1 : ℕ)) : ℝ) / Real.log Z ≤
              Real.log m / Real.log Z - 2*β := not_lt.mp hle
          have hle' : Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z <
              Real.log m / Real.log Z - 2*β := by
            by_contra hcon
            exact hb2' ⟨hstep, not_lt.mp hcon⟩
          have harg : Real.log (m / (((((n - 1 : ℕ)) : ℝ) + 1) * (b:ℝ))) / Real.log (b:ℝ) =
              (Real.log m / Real.log Z - Real.log ((((n - 1 : ℕ)) : ℝ) + 1) / Real.log Z - β) / β := by
            rw [hβb]
            exact (two_pair_arg_eq hLZ hm (by linarith : (0:ℝ) < (((n - 1 : ℕ)) : ℝ) + 1) hb1).symm
          rw [harg, le_div_iff₀ hβ]
          linarith
      have hgood := cell_osc_density hω hz hb2 hm ha4 ht1 ht2 hreg hcase
      rw [hcast1] at hgood
      simpa only [hφ] using hgood
  -- the per cell bounds are nonnegative
  have hδ0 : ∀ n : ℕ, b < n → 0 ≤ δ n := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hcast : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
      push_cast [Nat.cast_sub hn1]; ring
    have ha2 : (2:ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      have : (2:ℕ) ≤ n - 1 := by omega
      exact_mod_cast this
    have ha0 : (0:ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
    have hla : 0 < Real.log (((n - 1 : ℕ)) : ℝ) := Real.log_pos (by linarith)
    rw [hδ]
    beta_reduce
    rw [← hcast]
    have h1 : (0:ℝ) ≤ 16 / ((((n - 1 : ℕ)) : ℝ) ^ 2 * Real.log (((n - 1 : ℕ)) : ℝ)) :=
      div_nonneg (by norm_num) (by positivity)
    have h2 : (0:ℝ) ≤ if bad (n-1) then 2 / ((((n - 1 : ℕ)) : ℝ) * Real.log (((n - 1 : ℕ)) : ℝ)) else 0 := by
      split_ifs with h
      · exact div_nonneg (by norm_num) (by positivity)
      · norm_num
    linarith
  -- the sum of the per cell bounds
  have hsum1 : (∑ n ∈ Finset.Ioc b M, 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)))
      ≤ 32 / ((b:ℝ) * Real.log (b:ℝ)) := by
    have hshift : (∑ n ∈ Finset.Ioc b M, 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1))) =
        ∑ a ∈ Finset.Ioc (b-1) (M-1), 16 / ((a:ℝ)^2 * Real.log (a:ℝ)) := by
      rw [← sum_Ioc_shift (A := b) (B := M) (by omega : 1 ≤ b)
        (fun a => 16 / ((a:ℝ)^2 * Real.log (a:ℝ)))]
      refine Finset.sum_congr rfl fun n hmem => ?_
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hmem
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1, Nat.cast_one]
    rw [hshift]
    have hstep : (∑ a ∈ Finset.Ioc (b-1) (M-1), 16 / ((a:ℝ)^2 * Real.log (a:ℝ)))
        ≤ (16 / Real.log (b:ℝ)) * (∑ a ∈ Finset.Ioc (b-1) (M-1), 1 / ((a:ℝ)^2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a ha => ?_
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp ha
      have haB : b ≤ a := by omega
      have haA : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast haB
      have ha0 : (0:ℝ) < (a:ℝ) := by linarith
      have ha2 : (2:ℝ) ≤ (a:ℝ) := le_trans hbR haA
      have hlogle : Real.log (b:ℝ) ≤ Real.log (a:ℝ) := Real.log_le_log hb0 haA
      have hla : 0 < Real.log (a:ℝ) := Real.log_pos (by linarith)
      have hden1 : (0:ℝ) < (a:ℝ)^2 * Real.log (a:ℝ) := by positivity
      have hden2 : (0:ℝ) < (a:ℝ)^2 * Real.log (b:ℝ) := by
        have : (0:ℝ) < Real.log (b:ℝ) := hlb
        positivity
      have hmono : (a:ℝ)^2 * Real.log (b:ℝ) ≤ (a:ℝ)^2 * Real.log (a:ℝ) :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
      have hle : 1 / ((a:ℝ)^2 * Real.log (a:ℝ)) ≤ 1 / ((a:ℝ)^2 * Real.log (b:ℝ)) :=
        one_div_le_one_div_of_le hden2 hmono
      have he : 16 / ((a:ℝ)^2 * Real.log (a:ℝ)) ≤
          16 * (1 / ((a:ℝ)^2 * Real.log (b:ℝ))) := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left (by norm_num) hden2 hmono
      have he2 : (16 / Real.log (b:ℝ)) * (1 / ((a:ℝ)^2)) =
          16 * (1 / ((a:ℝ)^2 * Real.log (b:ℝ))) := by
        field_simp
      linarith [he, he2.le, he2.ge]
    refine hstep.trans ?_
    have hsq := sum_inv_sq_le (A := b-1) (B := M-1) (by omega : 1 ≤ b - 1)
    have hsq' : (∑ a ∈ Finset.Ioc (b-1) (M-1), 1 / ((a:ℝ)^2)) ≤ 2 / (b:ℝ) := by
      refine hsq.trans ?_
      rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      have hhalf : (b:ℝ) / 2 ≤ (b:ℝ) - 1 := by linarith
      have hmono : 1 / ((b:ℝ) - 1) ≤ 1 / ((b:ℝ) / 2) :=
        one_div_le_one_div_of_le (by linarith) hhalf
      have heq : 1 / ((b:ℝ) / 2) = 2 / (b:ℝ) := by field_simp
      linarith [hmono, heq.le, heq.ge]
    calc (16 / Real.log (b:ℝ)) * (∑ a ∈ Finset.Ioc (b-1) (M-1), 1 / ((a:ℝ)^2))
        ≤ (16 / Real.log (b:ℝ)) * (2 / (b:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = 32 / ((b:ℝ) * Real.log (b:ℝ)) := by field_simp; ring
  -- the bad cells
  have hcard1 : ((Finset.Ioc (b-1) (M-1)).filter bad1).card ≤ 28 := by
    have hsub : (Finset.Ioc (b-1) (M-1)).filter bad1 ⊆
        (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ))) ∪
        (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ) - 1)) := by
      intro a ha
      obtain ⟨hain, hb⟩ := Finset.mem_filter.mp ha
      obtain ⟨τ, hτ, h1, h2⟩ := hb
      have haA : 1 ≤ a := by
        obtain ⟨hx, -⟩ := Finset.mem_Ioc.mp hain
        omega
      have hfl := switch_cell_floor hZ haA h1 h2
      rcases hfl with h | h
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨τ, hτ, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨τ, hτ, by omega⟩)
    have hcL : (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset).card ≤ 14 :=
      (List.toFinset_card_le _).trans (le_of_eq rfl)
    calc ((Finset.Ioc (b-1) (M-1)).filter bad1).card
        ≤ ((([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ))) ∪
            (([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ) - 1))).card :=
          Finset.card_le_card hsub
      _ ≤ ((([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ)))).card +
            ((([β, 1/2, 1 - 2*β,
        1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - 2*β,
        (2 + 2*(1/16-1/10^5) - ε - 7*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (2 + 2*(1/16-1/10^5) - ε - 5*β)/4,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - β,
        (36*(2*(1/16-1/10^5)) - 2)/11 - ε,
        2*β - 2*(1/16-1/10^5) + ε,
        (2 - (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - 3*β)/4,
        (2 - (2*(1/16-1/10^5) - ε) - β)/4,
        (2 + (2*(1/16-1/10^5) - ε) - β)/4] : List ℝ).toFinset.image (fun τ : ℝ => Nat.floor (Z ^ τ) - 1))).card :=
          Finset.card_union_le _ _
      _ ≤ 14 + 14 := by
          refine Nat.add_le_add ?_ ?_
          · exact Finset.card_image_le.trans hcL
          · exact Finset.card_image_le.trans hcL
      _ = 28 := rfl
  have hcard2 : ((Finset.Ioc (b-1) (M-1)).filter bad2).card ≤ 2 := by
    have hsub : (Finset.Ioc (b-1) (M-1)).filter bad2 ⊆
        ({Nat.floor (Z ^ (Real.log m / Real.log Z - 2*β)),
          Nat.floor (Z ^ (Real.log m / Real.log Z - 2*β)) - 1} : Finset ℕ) := by
      intro a ha
      obtain ⟨hain, hb⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb1, hb2⟩ := hb
      have haA : 1 ≤ a := by
        obtain ⟨hx, -⟩ := Finset.mem_Ioc.mp hain
        omega
      have hfl := switch_cell_floor hZ haA hb1 hb2
      rcases hfl with h | h
      · rw [h]
        exact Finset.mem_insert_self _ _
      · rw [h]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hsum2 : (∑ n ∈ Finset.Ioc b M, (if bad (n-1) then
      2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0))
      ≤ 60 / ((b:ℝ) * Real.log (b:ℝ)) := by
    have hshift : (∑ n ∈ Finset.Ioc b M, (if bad (n-1) then
        2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0)) =
        ∑ a ∈ Finset.Ioc (b-1) (M-1), (if bad a then
          2 / ((a:ℝ) * Real.log (a:ℝ)) else 0) := by
      rw [← sum_Ioc_shift (A := b) (B := M) (by omega : 1 ≤ b)
        (fun a => if bad a then 2 / ((a:ℝ) * Real.log (a:ℝ)) else 0)]
      refine Finset.sum_congr rfl fun n hmem => ?_
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hmem
      have hn1 : 1 ≤ n := by omega
      have hcastn : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
        push_cast [Nat.cast_sub hn1]; ring
      beta_reduce
      by_cases hb' : bad (n - 1)
      · rw [if_pos hb', if_pos hb', hcastn]
      · rw [if_neg hb', if_neg hb']
    rw [hshift]
    rw [← Finset.sum_filter]
    have hterm : ∀ a ∈ (Finset.Ioc (b-1) (M-1)).filter bad,
        2 / ((a:ℝ) * Real.log (a:ℝ)) ≤ 2 / ((b:ℝ) * Real.log (b:ℝ)) := by
      intro a ha
      obtain ⟨hain, hba⟩ := Finset.mem_filter.mp ha
      obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hain
      have haB : b ≤ a := by omega
      have haA : (b:ℝ) ≤ (a:ℝ) := by exact_mod_cast haB
      have ha0 : (0:ℝ) < (a:ℝ) := by linarith
      have hlogle : Real.log (b:ℝ) ≤ Real.log (a:ℝ) := Real.log_le_log hb0 haA
      have hden : (0:ℝ) < (b:ℝ) * Real.log (b:ℝ) := by positivity
      have hden2 : (b:ℝ) * Real.log (b:ℝ) ≤ (a:ℝ) * Real.log (a:ℝ) :=
        mul_le_mul haA hlogle (le_of_lt hlb) (le_of_lt ha0)
      exact div_le_div_of_nonneg_left (by norm_num) hden hden2
    have hsumle := Finset.sum_le_card_nsmul ((Finset.Ioc (b-1) (M-1)).filter bad)
      (fun a => 2 / ((a:ℝ) * Real.log (a:ℝ))) (2 / ((b:ℝ) * Real.log (b:ℝ))) hterm
    rw [nsmul_eq_mul] at hsumle
    have hcardle : ((Finset.Ioc (b-1) (M-1)).filter bad).card ≤ 30 := by
      have hsub : (Finset.Ioc (b-1) (M-1)).filter bad ⊆
          (Finset.Ioc (b-1) (M-1)).filter bad1 ∪ (Finset.Ioc (b-1) (M-1)).filter bad2 := by
        intro a ha
        obtain ⟨hins, hb⟩ := Finset.mem_filter.mp ha
        rcases hb with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hins, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hins, h⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le ((Finset.Ioc (b-1) (M-1)).filter bad1)
        ((Finset.Ioc (b-1) (M-1)).filter bad2)
      omega
    refine hsumle.trans ?_
    have hstep : ((Finset.Ioc (b-1) (M-1)).filter bad).card * (2 / ((b:ℝ) * Real.log (b:ℝ)))
        ≤ 30 * (2 / ((b:ℝ) * Real.log (b:ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcardle
    have hlast : 30 * (2 / ((b:ℝ) * Real.log (b:ℝ))) =
        60 / ((b:ℝ) * Real.log (b:ℝ)) := by ring
    linarith [hstep, hlast.le, hlast.ge]
  -- the integral identity: the density vanishes outside the exponent range
  have hint_eq : (∫ t in (b:ℝ)..(M:ℝ), φ t) =
      ∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)), φ t := by
    have hZ2 : (2:ℝ) ≤ Z ^ (1/2:ℝ) := by
      have h := Real.sqrt_le_sqrt (by linarith : (4:ℝ) ≤ Z)
      have h4 : Real.sqrt 4 = (2:ℝ) := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4, Real.sqrt_eq_rpow] at h
      exact h
    have hi1 : IntervalIntegrable φ volume (b:ℝ) (Z ^ (1/2:ℝ)) := by
      rw [hφ]; exact intervalIntegrable_density hω hz hb2 hbR hbZ2
    have hi2 : IntervalIntegrable φ volume (Z ^ (1/2:ℝ)) (M:ℝ) := by
      rw [hφ]; exact intervalIntegrable_density hω hz hb2 hZ2 hM
    have hi3 : IntervalIntegrable φ volume (Z ^ (1/10:ℝ)) (b:ℝ) := by
      rw [hφ]; exact intervalIntegrable_density hω hz hb2 hZ10 hbZ
    have e1 : (∫ t in (Z ^ (1/2:ℝ))..(M:ℝ), φ t) = 0 := by
      refine integral_eq_zero_of_open hM ?_
      intro x hx1 hx2
      have hx0 : 0 < x := lt_trans (Real.rpow_pos_of_pos hZ0 _) hx1
      have hl : Real.log (Z ^ (1/2:ℝ)) < Real.log x := Real.log_lt_log (Real.rpow_pos_of_pos hZ0 _) hx1
      rw [Real.log_rpow hZ0] at hl
      have hα : 1/2 < Real.log x / Real.log Z := by
        rw [lt_div_iff₀ hLZ]; linarith
      rw [hφ]
      simp only
      rw [hβb]
      exact density_zero_of_half_lt hZ ω hx0 hb0 hα
    have e2 : (∫ t in (Z ^ (1/10:ℝ))..(b:ℝ), φ t) = 0 := by
      refine integral_eq_zero_of_open hbZ ?_
      intro x hx1 hx2
      have hx0 : 0 < x := lt_trans (Real.rpow_pos_of_pos hZ0 _) hx1
      rw [hφ]
      simp only
      rw [hβb]
      exact density_zero_of_lt hZ ω hx0 hb0 hx2
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, e1, add_zero]
    rw [← intervalIntegral.integral_add_adjacent_intervals hi3 hi1, e2, zero_add]
  -- assemble
  have hcells := sum_sub_integral_le_of_cell φ δ b hδ0 hcell hosc M hbM
  have hsumδ : (∑ n ∈ Finset.Ioc b M, δ n) ≤ 100 / ((b:ℝ) * Real.log (b:ℝ)) := by
    have hsplit : (∑ n ∈ Finset.Ioc b M, δ n) =
        (∑ n ∈ Finset.Ioc b M, 16 / (((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1))) +
        (∑ n ∈ Finset.Ioc b M, (if bad (n-1) then
          2 / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)) else 0)) := by
      rw [hδ, Finset.sum_add_distrib]
    rw [hsplit]
    have hden : (0:ℝ) < (b:ℝ) * Real.log (b:ℝ) := by positivity
    refine (add_le_add hsum1 hsum2).trans ?_
    have e : 32 / ((b:ℝ) * Real.log (b:ℝ)) + 60 / ((b:ℝ) * Real.log (b:ℝ)) =
        92 / ((b:ℝ) * Real.log (b:ℝ)) := by ring
    rw [e]
    exact div_le_div_of_nonneg_right (by norm_num) hden.le
  calc abs ((∑ a ∈ Finset.Ioc b M,
        (if lowerTwoDiscarded ε (Real.log (a:ℝ) / Real.log Z) β then
          ω (Real.log (m / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0))
      - (∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log Z) β then
          ω (Real.log (m / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)))
      = abs ((∑ a ∈ Finset.Ioc b M, φ a) - (∫ t in (Z ^ (1/10:ℝ))..(Z ^ (1/2:ℝ)), φ t)) := by
        simp only [hφ]
    _ = abs ((∑ a ∈ Finset.Ioc b M, φ a) - (∫ t in (b:ℝ)..(M:ℝ), φ t)) := by rw [hint_eq]
    _ ≤ 100 / ((b:ℝ) * Real.log (b:ℝ)) := hcells.trans hsumδ




/-! ### Stage 14: the leaf's inner sum and inner integral in the `φ_b` form -/

/-- The leaf's inner sum at a fixed `b ≥ 2` is the density sum of `per_b_riemann` times the
outer weight `1 / (b log^2 b)`. -/
private theorem two_pair_inner_sum {ω : ℝ → ℝ} {ε x : ℝ} {m B b : ℕ} (hb : 2 ≤ b) :
    (∑ a ∈ Finset.Ioc b B,
      (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
        else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ))))
      = (∑ a ∈ Finset.Ioc b B,
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              ((a : ℝ) * Real.log (a : ℝ)) else 0)) *
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha2 : 2 ≤ a := by
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp ha
    omega
  exact summand_eq_density_weight ω ha2 hb

/-- The leaf's inner integral at a fixed `b ≥ 2` is the integral over the exponent range of
`per_b_riemann`, divided by the outer weight. -/
private theorem two_pair_inner_int {ω : ℝ → ℝ} {ε x : ℝ} {m b : ℕ}
    (hZ : 1 < scaleZ ε x) (hm : 0 < m) (hb : 2 ≤ b) :
    (∫ α in (1/10:ℝ)..(1/2:ℝ),
        if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)
      = (∫ t in (scaleZ ε x) ^ (1/10:ℝ)..(scaleZ ε x) ^ (1/2:ℝ),
          (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
            ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
          else 0)) / ((b : ℝ) * Real.log (b : ℝ) ^ 2) := by
  rw [per_b_integral_eq hZ hm hb]



/-! ### Stage 15: the discarded region is empty off the exponent range -/

/-- On `E₂` the second exponent is above `12499/100000`. Hence below that level the region is
empty and the density vanishes identically. -/
private theorem lowerTwo_beta_gt {ε α β : ℝ} (hε8 : ε ≤ 1/10^8)
    (h : lowerTwoDiscarded ε α β) : (12499:ℝ)/100000 < β := by
  obtain ⟨hc, -, -, -, -⟩ := h
  linarith [hε8]

/-- On `E₂` the second exponent is at most `1/2`: above that level the region is empty. -/
private theorem lowerTwo_beta_le_half {ε α β : ℝ} (h : lowerTwoDiscarded ε α β) : β ≤ 1/2 := by
  obtain ⟨-, hba, ha, -, -⟩ := h
  linarith

/-- Below the level `12499/100000` both the density sum and the density integral vanish. -/
private theorem two_pair_per_b_small {ω : ℝ → ℝ} {ε : ℝ} (hε8 : ε ≤ 1/10^8)
    {x : ℝ} (hZ : 0 < Real.log (scaleZ ε x)) {m B b : ℕ}
    (hsmall : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 12499/100000) :
    (∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0)) = 0 ∧
      (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have := lowerTwo_beta_gt hε8 h
    rw [hb0] at this
    linarith
  constructor
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (hnd _)]
  · have h0 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = ∫ α in (1/10:ℝ)..(1/2:ℝ), (0:ℝ) :=
      intervalIntegral.integral_congr fun α _ => by rw [if_neg (hnd α)]
    rw [h0, intervalIntegral.integral_zero]

/-- Above the level `1/2` both the density sum and the density integral vanish. -/
private theorem two_pair_per_b_large {ω : ℝ → ℝ} {ε : ℝ}
    {x : ℝ} (hZ : 1 < scaleZ ε x) {m B b : ℕ}
    (hlarge : (1/2:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)) :
    (∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0)) = 0 ∧
      (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have := lowerTwo_beta_le_half h
    rw [hb0] at this
    linarith
  constructor
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (hnd _)]
  · have h0 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α (expo ε x b) then
          ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0)) = ∫ α in (1/10:ℝ)..(1/2:ℝ), (0:ℝ) :=
      intervalIntegral.integral_congr fun α _ => by rw [if_neg (hnd α)]
    rw [h0, intervalIntegral.integral_zero]

/-- `4 ≤ Z ^ (12499/100000)` for `Z ≥ 2^20`: the lowest level of `E₂` is above `4`.
Proved through `log`, since `Real.rpow` rewrites on numerals do not elaborate here. -/
private theorem rpow_level_ge_four {Z : ℝ} (hZ : (1048576:ℝ) ≤ Z) :
    (4:ℝ) ≤ Z ^ (12499/100000:ℝ) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  rw [Real.le_rpow_iff_log_le (by norm_num : (0:ℝ) < 4) hZ0]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log (1048576:ℝ) ≤ Real.log Z := Real.log_le_log (by norm_num) hZ
  have h2 : Real.log (1048576:ℝ) = 20 * Real.log 2 := by
    rw [show (1048576:ℝ) = 2 ^ (20:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h3]
  nlinarith [h1, h2, hl2]

/-- `2 ≤ Z ^ (1/10)` for `Z ≥ 1024`. -/
private theorem rpow_tenth_ge_two {Z : ℝ} (hZ : (1024:ℝ) ≤ Z) :
    (2:ℝ) ≤ Z ^ (1/10:ℝ) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  rw [Real.le_rpow_iff_log_le (by norm_num : (0:ℝ) < 2) hZ0]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log (1024:ℝ) ≤ Real.log Z := Real.log_le_log (by norm_num) hZ
  have h2 : Real.log (1024:ℝ) = 10 * Real.log 2 := by
    rw [show (1024:ℝ) = 2 ^ (10:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h2] at h1
  linarith [h1]




/-- Below the level `12499/100000` the density integral in the variable `t` vanishes. -/
private theorem two_pair_int_zero_small {ω : ℝ → ℝ} {ε : ℝ} (hε8 : ε ≤ 1/10^8)
    {x : ℝ} (hZ : 0 < Real.log (scaleZ ε x)) {m b : ℕ}
    (hsmall : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 12499/100000) :
    (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have hgt := lowerTwo_beta_gt hε8 h
    rw [hb0] at hgt
    linarith
  have h0 : (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) =
      ∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)), (0:ℝ) :=
    intervalIntegral.integral_congr fun t _ => by rw [if_neg (hnd _)]
  rw [h0, intervalIntegral.integral_zero]

/-- Above the level `1/2` the density integral in the variable `t` vanishes. -/
private theorem two_pair_int_zero_large {ω : ℝ → ℝ} {ε : ℝ}
    {x : ℝ} (hZ : 1 < scaleZ ε x) {m b : ℕ}
    (hlarge : (1/2:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)) :
    (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) = 0 := by
  have hb0 : expo ε x b = Real.log (b:ℝ) / Real.log (scaleZ ε x) := rfl
  have hnd : ∀ α : ℝ, ¬ lowerTwoDiscarded ε α (expo ε x b) := by
    intro α h
    have hle := lowerTwo_beta_le_half h
    rw [hb0] at hle
    linarith
  have h0 : (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
        else 0)) =
      ∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)), (0:ℝ) :=
    intervalIntegral.integral_congr fun t _ => by rw [if_neg (hnd _)]
  rw [h0, intervalIntegral.integral_zero]

set_option maxHeartbeats 1000000 in
/-- The per `b` comparison of the density sum with the density integral over the exponent range:
`100 / (b log b)` on the support of `E₂`, `0` where the region is empty. -/
private theorem two_pair_per_b {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {x : ℝ}
    (hZbig : (1048576:ℝ) ≤ scaleZ ε x)
    {m B b : ℕ} (hm : 0 < m) (hbB : b ≤ B)
    (hZB : (scaleZ ε x) ^ (1/2:ℝ) ≤ (B:ℝ)) :
    abs ((∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) else 0))
      - (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
        (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
          ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t) else 0)))
      ≤ if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
          100 / ((b:ℝ) * Real.log (b:ℝ)) else 0 := by
  have hZ1 : 1 < scaleZ ε x := by linarith
  have hZ0 : (0:ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  by_cases hcase : (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ)
  · rw [if_pos hcase]
    have hb0 : (0:ℝ) < (b:ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 _) hcase
    by_cases hhalf : (1/2:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)
    · obtain ⟨h1, -⟩ := two_pair_per_b_large (ω := ω) (ε := ε) hZ1 (m := m) (B := B) (b := b) hhalf
      have h2 := two_pair_int_zero_large (ω := ω) (ε := ε) hZ1 (m := m) (b := b) hhalf
      rw [h1, h2, sub_zero, abs_zero]
      positivity
    · have hβle : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 1/2 := not_lt.mp hhalf
      have hβpos : (0:ℝ) < expo ε x b := by
        have hmono : (12499:ℝ)/100000 * Real.log (scaleZ ε x) ≤ Real.log (b:ℝ) := by
          have hlog : Real.log ((scaleZ ε x) ^ (12499/100000:ℝ)) ≤ Real.log (b:ℝ) :=
            Real.log_le_log (Real.rpow_pos_of_pos hZ0 _) hcase
          rw [Real.log_rpow hZ0] at hlog
          linarith
        have hpos : (0:ℝ) < 12499/100000 * Real.log (scaleZ ε x) := by positivity
        show (0:ℝ) < Real.log (b:ℝ) / Real.log (scaleZ ε x)
        exact div_pos (lt_of_lt_of_le hpos hmono) hLZ
      have hb4 : 4 ≤ b := by
        have h4 := rpow_level_ge_four (by linarith : (1048576:ℝ) ≤ scaleZ ε x)
        have h45 : (4:ℝ) ≤ (b:ℝ) := le_trans h4 hcase
        exact_mod_cast h45
      have hbZ2 : (b:ℝ) ≤ (scaleZ ε x) ^ (1/2:ℝ) := by
        rw [← Real.log_le_log_iff hb0 (Real.rpow_pos_of_pos hZ0 _), Real.log_rpow hZ0]
        rw [div_le_iff₀ hLZ] at hβle
        linarith
      have hbZ1 : (scaleZ ε x) ^ (1/10:ℝ) ≤ (b:ℝ) :=
        le_trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)) hcase
      have hZ10 : (2:ℝ) ≤ (scaleZ ε x) ^ (1/10:ℝ) :=
        rpow_tenth_ge_two (by linarith : (1024:ℝ) ≤ scaleZ ε x)
      exact per_b_riemann (ω := ω) (ε := ε) (Z := scaleZ ε x) (β := expo ε x b)
        (m := (m : ℝ)) (b := b) (M := B) hω hz hZ1
        (by linarith : (4:ℝ) ≤ scaleZ ε x) hZ10 hβpos (by exact_mod_cast hm) hb4 hbB
        hbZ1 hbZ2 hZB rfl
  · rw [if_neg hcase]
    have hsmall : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 12499/100000 := by
      rcases Nat.eq_zero_or_pos b with hbzero | hbpos
      · subst hbzero
        simp only [Nat.cast_zero, Real.log_zero, zero_div]
        norm_num
      · have hb0' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbpos
        by_contra hcon
        have hlt : (12499:ℝ)/100000 < Real.log (b:ℝ) / Real.log (scaleZ ε x) := not_le.mp hcon
        have hprod : (12499:ℝ)/100000 * Real.log (scaleZ ε x) < Real.log (b:ℝ) := by
          rw [lt_div_iff₀ hLZ] at hlt
          linarith
        have hZb : (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) := by
          have e1 : (scaleZ ε x) ^ (12499/100000:ℝ) =
              Real.exp (Real.log (scaleZ ε x) * (12499/100000)) := Real.rpow_def_of_pos hZ0 _
          rw [e1]
          have e2 : Real.exp (Real.log (b:ℝ)) = (b:ℝ) := Real.exp_log hb0'
          rw [← e2]
          exact Real.exp_le_exp.mpr (by linarith)
        exact hcase hZb
    obtain ⟨h1, -⟩ := two_pair_per_b_small (ω := ω) hε8 hLZ (m := m) (B := B) (b := b) hsmall
    have h2 := two_pair_int_zero_small (ω := ω) hε8 hLZ (m := m) (b := b) hsmall
    rw [h1, h2, sub_zero, abs_zero]

set_option maxHeartbeats 800000 in
/-- P0069 page 51: the outer sum of the per `b` weights, cut at the level `z0 ≥ x^(11/200)`.
`Σ_b (1/(b log^2 b)) · (100/(b log b))` above `z0` is `O(x^(-11/200) / log^3 x)`. -/
private theorem two_pair_weight_sum {x z0 : ℝ} (hx2 : 2 ≤ x) (hz0 : 4 ≤ z0)
    (hz0x : x ^ (11/200:ℝ) ≤ z0) {B : ℕ} :
    (∑ b ∈ Finset.Ioc 1 B, (1 / ((b:ℝ) * Real.log (b:ℝ) ^ 2)) *
        (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) * Real.log (b:ℝ)) else 0))
      ≤ 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
  have hx0 : (0:ℝ) < x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hz00 : (0:ℝ) < z0 := by linarith
  have hlz0 : Real.log x / 20 ≤ Real.log z0 := by
    have h1 : Real.log (x ^ (11/200:ℝ)) ≤ Real.log z0 :=
      Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hz0x
    rw [Real.log_rpow hx0] at h1
    nlinarith [h1, hl0]
  have hlz00 : (0:ℝ) < Real.log z0 := by linarith
  -- the summand is `100 / (b^2 log^3 b)` on the support and `0` off it
  have hstep : ∀ b ∈ Finset.Ioc 1 B, (1 / ((b:ℝ) * Real.log (b:ℝ) ^ 2)) *
        (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) * Real.log (b:ℝ)) else 0)
      ≤ (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) else 0) := by
    intro b hb
    by_cases h : z0 ≤ (b:ℝ)
    · rw [if_pos h, if_pos h]
      have hb3 : 2 ≤ b := by
        obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hb
        omega
      have hb2 : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb3
      have hb0 : (0:ℝ) < (b:ℝ) := by linarith
      have hL : Real.log (b:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      have hbne : (b:ℝ) ≠ 0 := ne_of_gt hb0
      field_simp
      norm_num
    · rw [if_neg h, if_neg h, mul_zero]
  refine (Finset.sum_le_sum hstep).trans ?_
  -- cut the range at `⌊z0⌋ - 1`
  have hdrop : (∑ b ∈ Finset.Ioc 1 B,
        (if z0 ≤ (b:ℝ) then 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) else 0))
      ≤ ∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B, 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hb1
    have h3 : Nat.floor z0 ≤ b := by
      exact_mod_cast le_trans (Nat.floor_le (le_of_lt hz00)) hb2
    exact Finset.mem_Ioc.mpr ⟨by omega, h2⟩
  refine hdrop.trans ?_
  have hA1 : 1 ≤ Nat.floor z0 - 1 := by
    have h2 : 2 ≤ Nat.floor z0 := Nat.le_floor (a := z0) (n := 2) (by push_cast; linarith)
    omega
  have hAeq : ((Nat.floor z0 - 1 : ℕ) : ℝ) = ((Nat.floor z0 : ℕ) : ℝ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ Nat.floor z0)]
    ring
  have hAge : (z0 : ℝ) / 2 ≤ ((Nat.floor z0 - 1 : ℕ) : ℝ) := by
    have h1 : ((Nat.floor z0 : ℕ) : ℝ) ≤ z0 := Nat.floor_le (by linarith)
    have h2 : z0 - 1 ≤ ((Nat.floor z0 : ℕ) : ℝ) := by
      have h3 := Nat.lt_floor_add_one z0
      linarith
    rw [hAeq]; linarith
  -- each term is at most `(800 / log^3 z0) * (1/b^2)`
  have hstep3 : (∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B,
        100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3))
      ≤ (800 / Real.log z0 ^ 3) *
          (∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B, 1 / ((b:ℝ) ^ 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hb
    have hbA : ((Nat.floor z0 - 1 : ℕ) : ℝ) ≤ (b:ℝ) := by
      have h2 : (Nat.floor z0 - 1) ≤ b := by omega
      exact_mod_cast h2
    have hb2 : (2:ℝ) ≤ (b:ℝ) := by linarith
    have hb0 : (0:ℝ) < (b:ℝ) := by linarith
    have hlogb : Real.log z0 / 2 ≤ Real.log (b:ℝ) := by
      have h2 : Real.log (z0 / 2) ≤ Real.log (b:ℝ) :=
        Real.log_le_log (by linarith) (le_trans hAge hbA)
      have h3 : Real.log (z0 / 2) = Real.log z0 - Real.log 2 :=
        Real.log_div (ne_of_gt hz00) (by norm_num)
      have h4 : Real.log 2 ≤ Real.log z0 / 2 := by
        have h5 : Real.log 4 ≤ Real.log z0 := Real.log_le_log (by norm_num) hz0
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        linarith
      linarith
    have hlogb0 : 0 < Real.log (b:ℝ) := by linarith
    have hcube : Real.log z0 ^ 3 / 8 ≤ Real.log (b:ℝ) ^ 3 := by
      have h8 : (Real.log z0 / 2) ^ 3 ≤ Real.log (b:ℝ) ^ 3 :=
        pow_le_pow_left₀ (by linarith) hlogb 3
      have h9 : (Real.log z0 / 2) ^ 3 = Real.log z0 ^ 3 / 8 := by ring
      linarith [h8, h9.le, h9.ge]
    have hden : 0 < (b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3 :=
      mul_pos (pow_pos hb0 2) (pow_pos hlogb0 3)
    have hden2 : 0 < (b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8) := by
      have hlz3 : (0:ℝ) < Real.log z0 ^ 3 / 8 := div_pos (pow_pos (by linarith : (0:ℝ) < Real.log z0) 3) (by norm_num)
      exact mul_pos (pow_pos hb0 2) hlz3
    have hmono : (b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8) ≤ (b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have hle : 1 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3) ≤
        1 / ((b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8)) :=
      one_div_le_one_div_of_le hden2 hmono
    have he : (800 / Real.log z0 ^ 3) * (1 / ((b:ℝ) ^ 2)) =
        100 * (1 / ((b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8))) := by
      field_simp
      ring
    calc 100 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3)
        = 100 * (1 / ((b:ℝ) ^ 2 * Real.log (b:ℝ) ^ 3)) := by rw [mul_one_div]
      _ ≤ 100 * (1 / ((b:ℝ) ^ 2 * (Real.log z0 ^ 3 / 8))) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
      _ = (800 / Real.log z0 ^ 3) * (1 / ((b:ℝ) ^ 2)) := he.symm
  refine hstep3.trans ?_
  have hsq := sum_inv_sq_le (A := Nat.floor z0 - 1) (B := B) hA1
  have hsq' : (∑ b ∈ Finset.Ioc (Nat.floor z0 - 1) B, 1 / ((b:ℝ) ^ 2)) ≤ 2 / z0 := by
    refine hsq.trans ?_
    have h2 : 1 / ((Nat.floor z0 - 1 : ℕ) : ℝ) ≤ 1 / (z0 / 2) :=
      one_div_le_one_div_of_le (by linarith) hAge
    have h3 : 1 / (z0 / 2) = 2 / z0 := by field_simp
    linarith [h2, h3.le, h3.ge]

  have hfin : (800 / Real.log z0 ^ 3) * (2 / z0) ≤
      20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
    have h1 : 1 / z0 ≤ x ^ (-(11/200:ℝ)) := by
      rw [Real.rpow_neg hx0.le, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 _) hz0x
    have h2 : 1 / Real.log z0 ^ 3 ≤ 8000 / Real.log x ^ 3 := by
      have hl3 : (Real.log x / 20) ^ 3 ≤ Real.log z0 ^ 3 :=
        pow_le_pow_left₀ (by linarith) hlz0 3
      have e : (Real.log x / 20) ^ 3 = Real.log x ^ 3 / 8000 := by ring
      rw [show (8000:ℝ) / Real.log x ^ 3 = 1 / (Real.log x ^ 3 / 8000) by field_simp]
      have hx3 : (0:ℝ) < Real.log x ^ 3 / 8000 :=
        div_pos (a := Real.log x ^ 3) (b := 8000) (pow_pos hl0 3) (by norm_num)
      exact one_div_le_one_div_of_le hx3 (by linarith [hl3, e.le, e.ge])
    have hpos1 : (0:ℝ) ≤ 1 / Real.log z0 ^ 3 :=
      div_nonneg (by norm_num) (pow_pos hlz00 3).le
    have hpos2 : (0:ℝ) ≤ x ^ (-(11/200:ℝ)) := by positivity
    have hmul : (1 / Real.log z0 ^ 3) * (1 / z0) ≤
        (8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ)) :=
      mul_le_mul h2 h1 (by positivity)
        (le_of_lt (div_pos (a := (8000:ℝ)) (b := Real.log x ^ 3) (by norm_num) (pow_pos hl0 3)))
    have he : (800 / Real.log z0 ^ 3) * (2 / z0) =
        1600 * (1 / Real.log z0 ^ 3) * (1 / z0) := by
      field_simp
      ring
    have he2 : 1600 * (8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ)) =
        12800000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
      field_simp
      ring
    have hle2 : 1600 * ((1 / Real.log z0 ^ 3) * (1 / z0)) ≤
        1600 * ((8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ))) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    have hsmall : (12800000:ℝ) * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 ≤
        20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by
      have hp : (0:ℝ) < x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by positivity
      have : (12800000:ℝ) * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) ≤
          20000000 * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) := by
        apply mul_le_mul_of_nonneg_right (by norm_num) hp.le
      calc (12800000:ℝ) * x ^ (-(11/200:ℝ)) / Real.log x ^ 3
          = 12800000 * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) := by ring
        _ ≤ 20000000 * (x ^ (-(11/200:ℝ)) / Real.log x ^ 3) := this
        _ = 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := by ring
    calc (800 / Real.log z0 ^ 3) * (2 / z0)
        = 1600 * (1 / Real.log z0 ^ 3) * (1 / z0) := he
      _ = 1600 * ((1 / Real.log z0 ^ 3) * (1 / z0)) := by ring
      _ ≤ 1600 * ((8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ))) := hle2
      _ = 1600 * (8000 / Real.log x ^ 3) * x ^ (-(11/200:ℝ)) := by ring
      _ = 12800000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := he2
      _ ≤ 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3 := hsmall
  have hcoef2 : (0:ℝ) ≤ 800 / Real.log z0 ^ 3 := by
    have hlz00 : (0:ℝ) < Real.log z0 := by linarith
    exact div_nonneg (by norm_num) (pow_pos hlz00 3).le
  exact mul_le_mul_of_nonneg_left hsq' hcoef2
    |>.trans hfin


/-! ### Stage 16: `leaf_two_pair_riemann_first` -/

set_option maxHeartbeats 1000000 in
/-- P0069 page 51: the per `b` term of `leaf_two_pair_riemann_first`, bounded by the weight
`1/(b log^2 b)` times the per `b` comparison of `two_pair_per_b`. -/
private theorem two_pair_term_bound {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) {x : ℝ}
    (hZ1 : 1 < scaleZ ε x) (hZbig : (1048576:ℝ) ≤ scaleZ ε x)
    {m B b : ℕ} (hm : 0 < m) (hbB : b ≤ B)
    (hZB : (scaleZ ε x) ^ (1/2:ℝ) ≤ (B:ℝ)) :
    abs ((∑ a ∈ Finset.Ioc b B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
              Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
          else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ))))
      - (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2))
      ≤ (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
            100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · -- `b = 0`: an empty sum and a zero weight
    subst hb0
    have h1 : (∑ a ∈ Finset.Ioc 0 B,
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x 0) then
            ω (Real.log ((m : ℝ) / ((a : ℝ) * ((0:ℕ) : ℝ))) / Real.log ((0:ℕ) : ℝ)) /
              Real.log ((0:ℕ) : ℝ) / ((a : ℝ) * ((0:ℕ) : ℝ))
          else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log ((0:ℕ) : ℝ)))) = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      simp
    have h2 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x 0) then
            ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x 0) / expo ε x 0) / α
          else 0) / (((0:ℕ) : ℝ) * Real.log ((0:ℕ) : ℝ) ^ 2) = 0 := by
      simp
    rw [h1, h2, sub_zero, abs_zero]
    simp
  · -- `b ≥ 1`
    have hw : (0:ℝ) ≤ 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2) := by positivity
    have hw2 : (0:ℝ) ≤ ((b : ℝ) * Real.log (b : ℝ) ^ 2)⁻¹ := by positivity
    rcases Nat.eq_or_lt_of_le hbpos with hb1 | hb2
    · -- `b = 1`: both sides vanish
      subst hb1
      have h1 : (∑ a ∈ Finset.Ioc 1 B,
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x 1) then
              ω (Real.log ((m : ℝ) / ((a : ℝ) * ((1:ℕ) : ℝ))) / Real.log ((1:ℕ) : ℝ)) /
                Real.log ((1:ℕ) : ℝ) / ((a : ℝ) * ((1:ℕ) : ℝ))
            else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log ((1:ℕ) : ℝ)))) = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        simp
      have h2 : (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x 1) then
              ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x 1) / expo ε x 1) / α
            else 0) / (((1:ℕ) : ℝ) * Real.log ((1:ℕ) : ℝ) ^ 2) = 0 := by
        simp
      rw [h1, h2, sub_zero, abs_zero]
      simp
    · -- `b ≥ 2`: the per `b` comparison
      have hA : (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log (m : ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) =
          ∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
            (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
              ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
            else 0) :=
        per_b_integral_eq (ω := ω) (ε := ε) (x := x) (m := m) (b := b) hZ1
          (by exact_mod_cast hm) hb2
      have hsum_eq := two_pair_inner_sum (ω := ω) (ε := ε) (x := x) (m := m) (B := B) (b := b) hb2
      rw [hsum_eq]
      rw [hA]
      have hcore := two_pair_per_b (ω := ω) (ε := ε) (x := x) (m := m) (B := B) (b := b)
        hω hz hε hε8 hZbig hm hbB hZB
      calc abs ((∑ a ∈ Finset.Ioc b B,
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  ((a : ℝ) * Real.log (a : ℝ)) else 0)) *
            (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
          (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
              (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
                ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
              else 0)) / ((b : ℝ) * Real.log (b : ℝ) ^ 2))
          = abs ((∑ a ∈ Finset.Ioc b B,
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  ((a : ℝ) * Real.log (a : ℝ)) else 0)) -
              (∫ t in ((scaleZ ε x) ^ (1/10:ℝ))..((scaleZ ε x) ^ (1/2:ℝ)),
                (if lowerTwoDiscarded ε (Real.log t / Real.log (scaleZ ε x)) (expo ε x b) then
                  ω (Real.log ((m : ℝ) / (t * (b : ℝ))) / Real.log (b : ℝ)) / (t * Real.log t)
                else 0))) * ((b : ℝ) * Real.log (b : ℝ) ^ 2)⁻¹ := by
            rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, ← sub_mul, abs_mul, abs_of_nonneg hw2]
        _ ≤ ((b : ℝ) * Real.log (b : ℝ) ^ 2)⁻¹ *
              (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
                100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hcore hw2
        _ = (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
              (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
                100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
            rw [one_div]




/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. Interchange of
the two outer variables over the triangle `1 ≤ b < a ≤ N`. -/
private theorem two_pair_triangle_swap (N : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, g a b =
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, g a b := by
  refine Finset.sum_comm' fun b a => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. Exact algebra
of the two applications of the prime number theorem: with `w` the indicator of the primes and
`l` the density `1 / log`, the sum over `w b w a` is the sum over `l a l b` plus an error with
the factor `w a - l a` for each fixed `b` and an error with the factor `w b - l b` for each
fixed `a`. -/
private theorem two_pair_sum_split (N : ℕ) (w l : ℕ → ℝ) (F : ℕ → ℕ → ℝ) :
    ∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, w a * F a b =
      (∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, (w a - l a) * F a b) +
      (∑ a ∈ Finset.Icc 1 N, l a * ∑ b ∈ Finset.Ico 1 a, (w b - l b) * F a b) +
      ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, F a b * (l a * l b) := by
  have e1 : ∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, w a * F a b =
      (∑ b ∈ Finset.Icc 1 N, w b * ∑ a ∈ Finset.Ioc b N, (w a - l a) * F a b) +
      ∑ b ∈ Finset.Icc 1 N, ∑ a ∈ Finset.Ioc b N, w b * (l a * F a b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have e2 := two_pair_triangle_swap N (fun a b => w b * (l a * F a b))
  have e3 : ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, w b * (l a * F a b) =
      (∑ a ∈ Finset.Icc 1 N, l a * ∑ b ∈ Finset.Ico 1 a, (w b - l b) * F a b) +
      ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Ico 1 a, F a b * (l a * l b) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := two_pair_triangle_swap N (fun a b => F a b * (l a * l b))
  beta_reduce at e2 e4
  rw [e1, e2, e3, ← e4]
  ring

/-- P0069 page 51 display 5.17, the outer primes of the E2 sum of display 5.15. The sum over
the prime pairs `p2 < p1` up to `N` with a condition `E` is the iterated sum over `b` and then
`a > b` weighted by the indicator of the primes. -/
private theorem two_pair_sum_iterated (N : ℕ) (E : ℕ → ℕ → Prop) (t : ℕ → ℕ → ℝ) :
    ∑ i ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧ E i.1 i.2), t i.1 i.2 =
      ∑ b ∈ Finset.Icc 1 N, primeWeight b *
        ∑ a ∈ Finset.Ioc b N, primeWeight a * (if E a b then t a b else 0) := by
  rw [Finset.sum_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb1 := (Finset.mem_Icc.mp hb).1
  have hIoc : Finset.Ioc b N = (Finset.Icc 1 N).filter (fun a => b < a) := by
    ext a
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hIoc, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h1 : a.Prime <;> by_cases h2 : b.Prime <;> by_cases h3 : b < a <;>
    by_cases h4 : E a b <;> simp [primeWeight, h1, h2, h3, h4]

/-- `lowerTwoDiscarded` in `β` at fixed `α`: every atom is `β ≤ L` or `L ≤ β` with `L` affine in
`α`, so between consecutive switch points the truth value does not change. -/
private theorem sect_same_beta {ε α β β' : ℝ}
    (h0 : (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β ↔ (1+7*(2*(1/16-1/10^5)))/15-ε ≤ β')
    (h1 : β ≤ α ↔ β' ≤ α)
    (h3 : α + 2*β ≤ 1 ↔ α + 2*β' ≤ 1)
    (h4 : α + 2*β ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε ↔
          α + 2*β' ≤ 1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε)
    (h5 : 4*α + 7*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α + 7*β' ≤ 2+2*(1/16-1/10^5)-ε)
    (h6 : 1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β')
    (h7 : 4*α + 5*β ≤ 2+2*(1/16-1/10^5)-ε ↔ 4*α + 5*β' ≤ 2+2*(1/16-1/10^5)-ε)
    (h8 : 1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β ↔
          1/2-((2*(1/16-1/10^5))+((1+7*(2*(1/16-1/10^5)))/15-ε))/4+ε ≤ α + β')
    (h12 : β ≤ (36*(2*(1/16-1/10^5))-2)/11-ε ↔ β' ≤ (36*(2*(1/16-1/10^5))-2)/11-ε)
    (h11 : 2*β - (2*(1/16-1/10^5)) + ε ≤ α ↔ 2*β' - (2*(1/16-1/10^5)) + ε ≤ α)
    (h13 : |4*α + 3*β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α + 3*β' - 2| ≤ 2*(1/16-1/10^5)-ε)
    (h14 : |4*α + β - 2| ≤ 2*(1/16-1/10^5)-ε ↔ |4*α + β' - 2| ≤ 2*(1/16-1/10^5)-ε) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α β') := by
  unfold lowerTwoDiscarded upperPairRegion
  rw [h0, h1, h3, h4, h5, h6, h7, h8, h12, h11, h13, h14]

/-- The discarded region at fixed `α` is a measurable set in the integer variable `t` with
`β = log t / log Z`. -/
private theorem measurableSet_lowerTwo_beta {ε α Z : ℝ} :
    MeasurableSet {t : ℝ | lowerTwoDiscarded ε α (Real.log t / Real.log Z)} := by
  unfold lowerTwoDiscarded upperPairRegion
  measurability

/-- Buchstab's function is measurable: continuous off the single point `1`. -/
private theorem measurable_buchstab_new {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω) : Measurable ω := by
  refine measurable_of_continuousOn_compl_singleton (1 : ℝ) ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rcases lt_or_gt_of_ne hx with h | h
  · have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds x] ω := by
      filter_upwards [isOpen_Iio.mem_nhds h] with y hy
      exact (hz y hy).symm
    exact (continuousAt_const.congr hev).continuousWithinAt
  · exact (hω.1.continuousAt (Ici_mem_nhds h)).continuousWithinAt

/-- The `α`-integrand of the second passage is measurable in the integer variable `t`. -/
private theorem phi_measurable {ω : ℝ → ℝ} (hωm : Measurable ω) {ε Z s α : ℝ} :
    Measurable (fun t : ℝ => if lowerTwoDiscarded ε α (Real.log t / Real.log Z) then
      ω ((s - α - Real.log t / Real.log Z) / (Real.log t / Real.log Z)) / α else 0) := by
  have hs : MeasurableSet {t : ℝ | lowerTwoDiscarded ε α (Real.log t / Real.log Z)} :=
    measurableSet_lowerTwo_beta
  have hf : Measurable (fun t : ℝ =>
      ω ((s - α - Real.log t / Real.log Z) / (Real.log t / Real.log Z)) / α) := by
    measurability
  exact Measurable.ite hs hf measurable_const



/-! ### NEW: elementary sum estimates -/

/-- `log v - log u ≤ (v - u)/u` for `0 < u ≤ v` (copy of the target's `log_sub_log_le_div`,
restated here so that the WIP compiles on its own). -/
private theorem log_sub_log_le_div_new {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    Real.log t - Real.log a ≤ (t - a) / a := by
  have ht : 0 < t := lt_of_lt_of_le ha hat
  rw [← Real.log_div ht.ne' ha.ne']
  have h1 : Real.log (t / a) ≤ t / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : t / a - 1 = (t - a) / a := by rw [div_sub_one ha.ne']
  linarith

/-- `1/n ≤ log (n/(n-1))` for `n ≥ 2`. -/
private theorem inv_le_log_ratio {n : ℕ} (hn : 2 ≤ n) :
    1/(n:ℝ) ≤ Real.log ((n:ℝ)/((n:ℝ)-1)) := by
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hx : (0:ℝ) < (n:ℝ)/((n:ℝ)-1) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (x := (n:ℝ)/((n:ℝ)-1)) hx
  have e : 1 - ((n:ℝ)/((n:ℝ)-1))⁻¹ = 1/(n:ℝ) := by
    rw [inv_div]
    field_simp
    ring
  rwa [e] at h

/-- `∑_{N < n ≤ B} 1/(n log^2 n) ≤ 1/log N` for `N ≥ 4`, by telescoping
`1/(n log^2 n) ≤ 1/log (n-1) - 1/log n`. -/
private theorem sum_inv_log_sq_le {N B : ℕ} (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Ioc N B, 1 / ((n:ℝ) * Real.log (n:ℝ)^2)) ≤ 1 / Real.log (N:ℝ) := by
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 2 ≤ N)
  have hlogN : 0 < Real.log (N:ℝ) := by
    have h : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hN2
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hstep : ∀ n ∈ Finset.Ioc N B,
      1 / ((n:ℝ) * Real.log (n:ℝ)^2) ≤
        1 / Real.log ((n:ℝ) - 1) - 1 / Real.log (n:ℝ) := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hn
    have hn2 : 2 ≤ n := by omega
    have hn5 : 5 ≤ n := by omega
    have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    have hn5R : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn5
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hln : 0 < Real.log (n:ℝ) := by
      have h : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hnR
      have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hlm : 0 < Real.log ((n:ℝ) - 1) := Real.log_pos (by linarith)
    have hlm_le : Real.log ((n:ℝ) - 1) ≤ Real.log (n:ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    have e1 : 1 / Real.log ((n:ℝ) - 1) - 1 / Real.log (n:ℝ) =
        Real.log ((n:ℝ)/((n:ℝ)-1)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) := by
      rw [Real.log_div hn0.ne' (by linarith : ((n:ℝ)-1) ≠ 0)]
      field_simp
    have hinv : 1/(n:ℝ) ≤ Real.log ((n:ℝ)/((n:ℝ)-1)) := inv_le_log_ratio hn2
    have hA : (1/(n:ℝ)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) ≤
        Real.log ((n:ℝ)/((n:ℝ)-1)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) :=
      div_le_div_of_nonneg_right hinv (by positivity)
    have e2 : (1/(n:ℝ)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) =
        1/((n:ℝ) * (Real.log ((n:ℝ)-1) * Real.log (n:ℝ))) := by
      field_simp
    have hmul : Real.log ((n:ℝ)-1) * Real.log (n:ℝ) ≤ Real.log (n:ℝ)^2 := by
      have h1 : Real.log ((n:ℝ)-1) * Real.log (n:ℝ) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) :=
        mul_le_mul_of_nonneg_right hlm_le hln.le
      calc Real.log ((n:ℝ)-1) * Real.log (n:ℝ) ≤ Real.log (n:ℝ) * Real.log (n:ℝ) := h1
        _ = Real.log (n:ℝ)^2 := by ring
    have hB : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤
        (1/(n:ℝ)) / (Real.log ((n:ℝ)-1) * Real.log (n:ℝ)) := by
      rw [e2]
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hmul hn0.le
    rw [e1]
    exact hB.trans hA
  refine (Finset.sum_le_sum hstep).trans ?_
  have htel : ∀ B' : ℕ, N ≤ B' →
      (∑ n ∈ Finset.Ioc N B', (1 / Real.log ((n:ℝ) - 1) - 1 / Real.log (n:ℝ)))
        = 1 / Real.log (N:ℝ) - 1 / Real.log (B':ℝ) := by
    intro B' hB'
    induction B', hB' using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ioc_succ_top hb, ih]
      have hcast : ((b + 1 : ℕ) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
      have hsub : (b:ℝ) + 1 - 1 = (b:ℝ) := by ring
      rw [hcast, hsub]
      ring
  rcases le_or_gt N B with h | h
  · rw [htel B h]
    have hB0 : (0:ℝ) ≤ 1 / Real.log (B:ℝ) := by
      rcases Nat.eq_zero_or_pos B with hB | hB
      · rw [hB]; simp
      · have hB1 : (2:ℝ) ≤ (B:ℝ) := by
          have : 2 ≤ B := by omega
          exact_mod_cast this
        have h2 : 0 < Real.log (B:ℝ) := by
          have h3 : Real.log 2 ≤ Real.log (B:ℝ) := Real.log_le_log (by norm_num) hB1
          have h4 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          linarith
        exact le_of_lt (one_div_pos.mpr h2)
    linarith
  · have hempty : Finset.Ioc N B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    positivity

/-- `∑_{A < n ≤ B} 1/(n^2 log^k n) ≤ 1/(A log^k A)` for `A ≥ 4`, `1 ≤ k`. -/
private theorem sum_inv_sq_log_pow_le {A B : ℕ} (hA : 2 ≤ A) {k : ℕ} (hk : 1 ≤ k) :
    (∑ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2 * Real.log (n:ℝ)^k)) ≤
      1 / ((A:ℝ) * Real.log (A:ℝ)^k) := by
  have hA2 : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hA0 : (0:ℝ) < (A:ℝ) := by linarith
  have hlogA : 0 < Real.log (A:ℝ) := by
    have h : Real.log 2 ≤ Real.log (A:ℝ) := Real.log_le_log (by norm_num) hA2
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hstep : ∀ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2 * Real.log (n:ℝ)^k) ≤
      (1 / Real.log (A:ℝ)^k) * (1 / ((n:ℝ)^2)) := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_Ioc.mp hn
    have hnA : (A:ℝ) ≤ (n:ℝ) := by exact_mod_cast le_of_lt h1
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hln : 0 < Real.log (n:ℝ) := lt_of_lt_of_le hlogA (Real.log_le_log hA0 hnA)
    have hle : Real.log (A:ℝ)^k ≤ Real.log (n:ℝ)^k :=
      pow_le_pow_left₀ hlogA.le (Real.log_le_log hA0 hnA) k
    have hb : 1 / ((n:ℝ)^2 * Real.log (n:ℝ)^k) ≤ 1 / ((n:ℝ)^2 * Real.log (A:ℝ)^k) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    have e : 1 / ((n:ℝ)^2 * Real.log (A:ℝ)^k) = (1 / Real.log (A:ℝ)^k) * (1 / ((n:ℝ)^2)) := by
      field_simp
    linarith [hb, e.le, e.ge]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hsq : (∑ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2)) ≤ 1 / (A:ℝ) := sum_inv_sq_le (by omega)
  have hfin : (1 / Real.log (A:ℝ)^k) * (1 / (A:ℝ)) = 1 / ((A:ℝ) * Real.log (A:ℝ)^k) := by
    field_simp
  calc (1 / Real.log (A:ℝ)^k) * (∑ n ∈ Finset.Ioc A B, 1 / ((n:ℝ)^2))
      ≤ (1 / Real.log (A:ℝ)^k) * (1 / (A:ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / ((A:ℝ) * Real.log (A:ℝ)^k) := hfin



/-! ### NEW: the discarded region is constant on a `b`-cell with no switch point -/

set_option maxHeartbeats 4000000 in
/-- The switch points of `E₂` as a function of the second exponent `β` at fixed `α`, `s`: if none
of them lies in `[β, β']` then the region takes the same value at `β` and `β'`. -/
private theorem cell_region_const_beta {ε α s β β' : ℝ} (hββ' : β ≤ β')
    (hno : ∀ τ ∈ (([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset), ¬(β ≤ τ ∧ τ ≤ β')) :
    (lowerTwoDiscarded ε α β ↔ lowerTwoDiscarded ε α β') := by
  refine sect_same_beta (h0 := ?_) (h1 := ?_) (h3 := ?_) (h4 := ?_) (h5 := ?_) (h6 := ?_)
    (h7 := ?_) (h8 := ?_) (h12 := ?_) (h11 := ?_) (h13 := ?_) (h14 := ?_)
  · -- `c₁ - ε ≤ β`
    have hz := hno ((1+7*(2*(1/16-1/10^5)))/15-ε) (by simp)
    constructor
    · intro h; linarith
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
  · -- `β ≤ α`
    have hz := hno (α) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `α + 2β ≤ 1`
    have hz := hno ((1-α)/2) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `α + 2β ≤ c₃ - 2ε`
    have hz := hno ((1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `4α + 7β ≤ 2 + θ - ε`
    have hz := hno ((2 + 2*(1/16-1/10^5) - ε - 4*α)/7) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `c₅ ≤ α + β`
    have hz := hno (1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α) (by simp)
    constructor
    · intro h; linarith
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
  · -- `4α + 5β ≤ 2 + θ - ε`
    have hz := hno ((2 + 2*(1/16-1/10^5) - ε - 4*α)/5) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `c₇ ≤ α + β`
    have hz := hno (1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α) (by simp)
    constructor
    · intro h; linarith
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
  · -- `β ≤ (36θ - 2)/11 - ε`
    have hz := hno ((36*(2*(1/16-1/10^5))-2)/11-ε) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `2β - θ + ε ≤ α`
    have hz := hno ((α + 2*(1/16-1/10^5) - ε)/2) (by simp)
    constructor
    · intro h
      by_contra hc
      refine hz ⟨?_, ?_⟩ <;> linarith
    · intro h; linarith
  · -- `|4α + 3β - 2| ≤ θ - ε`
    have hzu := hno ((2 + (2*(1/16-1/10^5) - ε) - 4*α)/3) (by simp : ((2 + (2*(1/16-1/10^5) - ε) - 4*α)/3) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    have hzl := hno ((2 - (2*(1/16-1/10^5) - ε) - 4*α)/3) (by simp : ((2 - (2*(1/16-1/10^5) - ε) - 4*α)/3) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    rw [abs_le, abs_le]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · linarith
      · by_contra hc
        refine hzu ⟨?_, ?_⟩ <;> linarith
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · by_contra hc
        refine hzl ⟨?_, ?_⟩ <;> linarith
      · linarith
  · -- `|4α + β - 2| ≤ θ - ε`
    have hzu := hno (2 + (2*(1/16-1/10^5) - ε) - 4*α) (by simp : (2 + (2*(1/16-1/10^5) - ε) - 4*α) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    have hzl := hno (2 - (2*(1/16-1/10^5) - ε) - 4*α) (by simp : (2 - (2*(1/16-1/10^5) - ε) - 4*α) ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset)
    rw [abs_le, abs_le]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · linarith
      · by_contra hc
        refine hzu ⟨?_, ?_⟩ <;> linarith
    · intro h
      obtain ⟨h1, h2⟩ := h
      constructor
      · by_contra hc
        refine hzl ⟨?_, ?_⟩ <;> linarith
      · linarith


/-! ### NEW: the good cell oscillation in the `b` variable -/

/-- `(s - α - β)/β` is antitone in `β > 0`. -/
private theorem arg_beta_anti {s α β β' : ℝ} (hβ : 0 < β) (hβ' : 0 < β') (h : β ≤ β')
    (hsa : α ≤ s) :
    (s - α - β')/β' ≤ (s - α - β)/β := by
  have e1 : (s - α - β')/β' = (s - α)/β' - 1 := by
    rw [sub_div, div_self (ne_of_gt hβ')]
  have e2 : (s - α - β)/β = (s - α)/β - 1 := by
    rw [sub_div, div_self (ne_of_gt hβ)]
  rw [e1, e2]
  have h1 : (s - α)/β' ≤ (s - α)/β := by
    have hsa0 : 0 ≤ s - α := by linarith
    exact div_le_div_of_nonneg_left hsa0 hβ h
  linarith

set_option maxHeartbeats 1000000 in
/-- One good `b`-cell: if the region does not change across the cell and the Buchstab argument
stays on one side of one, the `α`-integrand of the second passage moves by at most
`200 log Z / ((n-1) log^2 (n-1))` over the cell. -/
private theorem phi_cell_osc {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s α : ℝ} (hZ : 1 < Z) {n : ℕ} (hn : 4 ≤ n) {t : ℝ}
    (ht1 : (n:ℝ) - 1 ≤ t) (ht2 : t ≤ (n:ℝ))
    (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) (hs0 : 1/2 ≤ s) (hs : s ≤ 1)
    (hreg : lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) ↔
            lowerTwoDiscarded ε α (Real.log t/Real.log Z))
    (hcase : 1 ≤ (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) ∨
             (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) < 1) :
    |(if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
        ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
      (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
      200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : 0 < Real.log Z := Real.log_pos hZ
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hnm : (3:ℝ) ≤ (n:ℝ) - 1 := by linarith
  have hnm0 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hα0 : (0:ℝ) < α := by linarith
  have hlogn : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogm : 0 < Real.log ((n:ℝ)-1) := Real.log_pos (by linarith)
  have hβn : 0 < Real.log (n:ℝ)/Real.log Z := div_pos hlogn hLZ
  have hβt : 0 < Real.log t/Real.log Z := div_pos hlogt hLZ
  have hlogn_le : Real.log ((n:ℝ)-1) ≤ Real.log (n:ℝ) := Real.log_le_log hnm0 (by linarith)
  have hβle : Real.log t/Real.log Z ≤ Real.log (n:ℝ)/Real.log Z :=
    div_le_div_of_nonneg_right (Real.log_le_log ht0 ht2) hLZ.le
  have harganti : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) ≤
      (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) :=
    arg_beta_anti hβt hβn hβle (by linarith)
  have hβdiff : Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z ≤
      1/(((n:ℝ)-1)*Real.log Z) := by
    rw [← sub_div]
    have e : 1/(((n:ℝ)-1)*Real.log Z) = (1/((n:ℝ)-1))/Real.log Z := by field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hLZ.le
    have h1 : Real.log (n:ℝ) - Real.log t ≤ ((n:ℝ) - t)/t := log_sub_log_le_div_new ht0 ht2
    have h2 : ((n:ℝ) - t)/t ≤ ((n:ℝ) - t)/((n:ℝ) - 1) :=
      div_le_div_of_nonneg_left (by linarith) hnm0 (by linarith)
    have h3 : ((n:ℝ) - t)/((n:ℝ) - 1) ≤ 1/((n:ℝ) - 1) := by
      rw [div_le_div_iff₀ hnm0 hnm0]
      nlinarith
    linarith
  rcases hcase with hu | hlt
  · -- the Buchstab argument is at least one at both points
    have hut : 1 ≤ (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) := le_trans hu harganti
    have hlip := buchstab_lipschitz_abs hω hz hu hut
    by_cases hD : lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z)
    · have hDt : lowerTwoDiscarded ε α (Real.log t/Real.log Z) := hreg.mp hD
      rw [if_pos hD, if_pos hDt, ← sub_div, abs_div, abs_of_pos hα0]
      -- the argument difference
      have e1 : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) =
          (s - α)/(Real.log (n:ℝ)/Real.log Z) - 1 := by
        rw [sub_div, div_self (ne_of_gt hβn)]
      have e2 : (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) =
          (s - α)/(Real.log t/Real.log Z) - 1 := by
        rw [sub_div, div_self (ne_of_gt hβt)]
      have hargdiff : |(s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) -
          (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z)| ≤
          Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
        rw [e1, e2]
        have hmul : ((s - α)/(Real.log (n:ℝ)/Real.log Z) - 1) -
            ((s - α)/(Real.log t/Real.log Z) - 1) =
            (s - α) * (1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)) := by ring
        rw [hmul, abs_mul]
        have habs1 : |s - α| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have hb2 : |1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)| ≤
            Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
          have hnum0 : 0 ≤ Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z := by linarith
          have hβl : 0 < Real.log ((n:ℝ)-1)/Real.log Z := div_pos hlogm hLZ
          have ht_ge : Real.log ((n:ℝ)-1)/Real.log Z ≤ Real.log t/Real.log Z :=
            div_le_div_of_nonneg_right (Real.log_le_log hnm0 ht1) hLZ.le
          have hn_ge : Real.log ((n:ℝ)-1)/Real.log Z ≤ Real.log (n:ℝ)/Real.log Z :=
            div_le_div_of_nonneg_right (Real.log_le_log hnm0 (by linarith)) hLZ.le
          have hden : Real.log ((n:ℝ)-1)/Real.log Z * (Real.log ((n:ℝ)-1)/Real.log Z) ≤
              Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z) :=
            mul_le_mul hn_ge ht_ge (le_of_lt hβl) (le_trans (le_of_lt hβl) hn_ge)
          have e3 : 1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z) =
              (Real.log t/Real.log Z - Real.log (n:ℝ)/Real.log Z) /
                ((Real.log (n:ℝ)/Real.log Z)*(Real.log t/Real.log Z)) := by
            field_simp
          have habs : |1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)| =
              (Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z) /
                ((Real.log (n:ℝ)/Real.log Z)*(Real.log t/Real.log Z)) := by
            have hsig : |Real.log t/Real.log Z - Real.log (n:ℝ)/Real.log Z| =
                (Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z) := by
              rw [abs_sub_comm, abs_of_nonneg hnum0]
            rw [e3, abs_div, abs_of_pos (mul_pos hβn hβt), hsig]
          have h3a : (Real.log (n:ℝ)/Real.log Z - Real.log t/Real.log Z) /
              (Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z)) ≤
              (1/(((n:ℝ)-1)*Real.log Z)) /
                (Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z)) :=
            div_le_div_of_nonneg_right hβdiff (by positivity)
          have h3b : (1/(((n:ℝ)-1)*Real.log Z)) /
                (Real.log (n:ℝ)/Real.log Z * (Real.log t/Real.log Z)) ≤
              (1/(((n:ℝ)-1)*Real.log Z)) /
                (Real.log ((n:ℝ)-1)/Real.log Z * (Real.log ((n:ℝ)-1)/Real.log Z)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          have hfin : (1/(((n:ℝ)-1)*Real.log Z)) /
              (Real.log ((n:ℝ)-1)/Real.log Z * (Real.log ((n:ℝ)-1)/Real.log Z)) =
              Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
            field_simp
          rw [habs]
          linarith [h3a, h3b, hfin]
        calc |s - α| * |1/(Real.log (n:ℝ)/Real.log Z) - 1/(Real.log t/Real.log Z)|
            ≤ 1 * (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) :=
              mul_le_mul habs1 hb2 (abs_nonneg _) (by norm_num)
          _ = Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by ring
      have h1 : |ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z)) -
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))| ≤
          Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := hlip.trans hargdiff
      have hb : |ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z)) -
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))| / α ≤
          (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) := by
        have hb1 : |ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z)) -
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))| / α ≤
            (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / α :=
          div_le_div_of_nonneg_right h1 hα0.le
        have hb2 : (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / α ≤
            (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hα1
        linarith
      have h2 : (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) ≤
          200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
        have ee1 : (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) / (1/10) =
            10 * (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) := by field_simp
        have ee2 : 200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) =
            200 * (Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) := by ring
        rw [ee1, ee2]
        apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      linarith [hb, h2]
    · have hDt : ¬ lowerTwoDiscarded ε α (Real.log t/Real.log Z) := fun h => hD (hreg.mpr h)
      rw [if_neg hD, if_neg hDt, sub_zero, abs_zero]
      positivity
  · -- the Buchstab argument is below one at both points, so both values vanish
    have hnt : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) < 1 :=
      lt_of_le_of_lt harganti hlt
    have e1 : (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
        ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z)
      · rw [if_pos hD, hz _ hnt, zero_div]
      · rw [if_neg hD]
    have e2 : (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) = 0 := by
      by_cases hD : lowerTwoDiscarded ε α (Real.log t/Real.log Z)
      · rw [if_pos hD, hz _ hlt, zero_div]
      · rw [if_neg hD]
    rw [e1, e2, sub_zero, abs_zero]
    positivity


/-! ### NEW: weight monotonicity, cell oscillation and the integrand bound -/

/-- `u log^2 u` is monotone on `[1, ∞)`, so `1/(u log^2 u)` is antitone there. -/
private theorem weight_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    1/(b * Real.log b^2) ≤ 1/(a * Real.log a^2) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hla0 : 0 < Real.log a := Real.log_pos ha
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha.le
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  have hlb : 0 ≤ Real.log b := le_trans hla hlab
  have h1 : a * Real.log a^2 ≤ b * Real.log b^2 := by
    have h2 : Real.log a^2 ≤ Real.log b^2 := by
      apply pow_le_pow_left₀ hla hlab
    exact mul_le_mul hab h2 (by positivity) (by linarith)
  exact one_div_le_one_div_of_le (by positivity) h1

/-- On the cell `[n-1, n]` the weight moves by at most its drop `1/((n-1)log^2(n-1)) -
1/(n log^2 n)`. -/
private theorem weight_cell_osc {n : ℕ} (hn : 4 ≤ n) {t : ℝ}
    (ht1 : (n:ℝ) - 1 ≤ t) (ht2 : t ≤ (n:ℝ)) :
    |1/((n:ℝ) * Real.log (n:ℝ)^2) - 1/(t * Real.log t^2)| ≤
      1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have ht2' : t ≤ (n:ℝ) := ht2
  have hle1 : (1:ℝ) < t := by linarith
  have hle2 : (1:ℝ) < (n:ℝ) - 1 := by linarith
  have hWt : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤ 1/(t * Real.log t^2) :=
    weight_mono hle1 ht2'
  have hWm : 1/(t * Real.log t^2) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
    weight_mono hle2 ht1
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Telescoping weight drop: `∑_{N < n ≤ B} (w(n-1) - w(n)) = w(N) - w(B) ≤ w(N)`. -/
private theorem tel_weight {N B : ℕ} (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Ioc N B,
        (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))) ≤
      1/((N:ℝ) * Real.log (N:ℝ)^2) := by
  have htel : ∀ B' : ℕ, N ≤ B' →
      (∑ n ∈ Finset.Ioc N B',
          (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2)))
        = 1/((N:ℝ) * Real.log (N:ℝ)^2) - 1/((B':ℝ) * Real.log (B':ℝ)^2) := by
    intro B' hB'
    induction B', hB' using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ioc_succ_top hb, ih]
      have hcast : ((b + 1 : ℕ) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
      have hsub : (b:ℝ) + 1 - 1 = (b:ℝ) := by ring
      rw [hcast, hsub]
      ring
  rcases le_or_gt N B with h | h
  · rw [htel B h]
    have hN4 : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hpos : (0:ℝ) < 1/((B:ℝ) * Real.log (B:ℝ)^2) := by
      have hB4 : (4:ℝ) ≤ (B:ℝ) := by
        have : 4 ≤ B := by omega
        exact_mod_cast this
      have hlog : 0 < Real.log (B:ℝ) := Real.log_pos (by linarith)
      positivity
    linarith
  · have hempty : Finset.Ioc N B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    have hN4 : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by linarith)
    positivity

/-- `|Φ| ≤ 10` for the `α`-integrand of the second passage, for `α, β ≥ 1/10`. -/
private theorem phi_abs_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s α β : ℝ} (hα1 : 1/10 ≤ α) :
    |(if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/α else 0)| ≤ 10 := by
  have hα0 : (0:ℝ) < α := by linarith
  have hw1 : ω ((s - α - β)/β) ≤ 1 :=
    LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _
  have hw0 : 0 ≤ ω ((s - α - β)/β) :=
    Decomp514a.two_density_buchstab_nonneg hω hz _
  have hinv : 1/α ≤ 10 := by
    rw [div_le_iff₀ hα0]
    linarith
  by_cases h : lowerTwoDiscarded ε α β
  · rw [if_pos h, abs_div, abs_of_pos hα0]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ ω ((s - α - β)/β))]
    rw [div_le_iff₀ hα0]
    calc ω ((s - α - β)/β) ≤ 1 := hw1
      _ ≤ 10 * α := by nlinarith
  · rw [if_neg h, abs_zero]
    norm_num



/-- `1/(t log^2 t)` times the `α`-integrand is at most `10/(t log^2 t)`. -/
private theorem phi_weight_abs_le {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s α : ℝ} (hα1 : 1/10 ≤ α) (t : ℝ) (ht : 1 < t) :
    |(1/(t * Real.log t^2)) *
      (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
      10 * (1/(t * Real.log t^2)) := by
  have hw : 0 < 1/(t * Real.log t^2) := by
    have : 0 < Real.log t := Real.log_pos ht
    positivity
  have h1 : |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
      ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| ≤ 10 :=
    phi_abs_le hω hz (ε := ε) (Z := Z) (s := s) (α := α) (β := Real.log t/Real.log Z) hα1
  calc |(1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)|
      = (1/(t * Real.log t^2)) *
        |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| := by
        rw [abs_mul, abs_of_pos hw]
    _ ≤ (1/(t * Real.log t^2)) * 10 := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
    _ = 10 * (1/(t * Real.log t^2)) := by ring

/-! ### NEW: the second passage at one point `α` -/

set_option maxHeartbeats 150000000 in
/-- The sum over the integer variable against the integral, cell by cell: the first half of the
second passage, with the weight telescoping. -/
private theorem second_passage_cell {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s : ℝ} (hε8 : ε ≤ 1/10^8) (hZ : 1 < Z) (hZbig : (2:ℝ)^20 ≤ Z)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) {α : ℝ} (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) :
    |(∑ b ∈ Finset.Ioc ⌊Z^(1/10:ℝ)⌋₊ ⌊Z^(1/2:ℝ)⌋₊,
        (1/((b:ℝ) * Real.log (b:ℝ)^2)) *
          (if lowerTwoDiscarded ε α (Real.log (b:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (b:ℝ)/Real.log Z)/(Real.log (b:ℝ)/Real.log Z))/α else 0)) -
      (∫ t in ((⌊Z^(1/10:ℝ)⌋₊ : ℝ))..((⌊Z^(1/2:ℝ)⌋₊ : ℝ)), (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))| ≤
      500000 * (1 + Real.log Z) /
        (((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1) * Real.log ((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1)^2) := by
  classical
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : (0:ℝ) < Real.log Z := Real.log_pos hZ
  set u : ℝ := Z^(1/10:ℝ) with hu
  set v : ℝ := Z^(1/2:ℝ) with hv
  set B0 : ℕ := ⌊u⌋₊ with hB0
  set B1 : ℕ := ⌊v⌋₊ with hB1
  have hu4 : (4:ℝ) ≤ u := by
    have h1 : ((2:ℝ)^20)^(1/10:ℝ) ≤ Z^(1/10:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/10:ℝ) = 4 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hu]
    linarith
  have hu0 : (0:ℝ) < u := by linarith
  have huv : u ≤ v := by
    rw [hu, hv]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hB0ge : 4 ≤ B0 := by
    rw [hB0]
    exact Nat.le_floor (by push_cast; exact hu4)
  have hB0le : ((B0:ℝ)) ≤ u := by
    rw [hB0]; exact Nat.floor_le (by positivity)
  have hB1le : ((B1:ℝ)) ≤ v := by
    rw [hB1]; exact Nat.floor_le (by positivity)
  have hB0B1 : B0 ≤ B1 := by
    have h1 : (B0:ℝ) ≤ v := le_trans hB0le huv
    rw [hB1]
    exact Nat.le_floor h1
  have hB0w : (1:ℝ) ≤ (B0:ℝ) := by
    have : 1 ≤ B0 := by omega
    exact_mod_cast this
  have hB0R4 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0ge
  have huB1 : u ≤ (B1:ℝ) := by
    -- `u + 1 ≤ v` and `v - 1 ≤ B1`
    have hvpow : v = u^5 := by
      rw [hu, hv, ← Real.rpow_natCast]
      rw [show (1/2:ℝ) = (1/10:ℝ) * 5 by norm_num, Real.rpow_mul (le_of_lt hZ0)]
      norm_num
    have huv1 : u + 1 ≤ v := by
      rw [hvpow]
      have hpow : (4:ℝ)^4 ≤ u^4 := pow_le_pow_left₀ (by norm_num) hu4 4
      have hmul : u * 4^4 ≤ u^5 := by
        rw [show u^5 = u * u^4 by ring]
        exact mul_le_mul_of_nonneg_left hpow (by linarith)
      nlinarith [hmul, hu4]
    have hfl : v - 1 ≤ (B1:ℝ) := by
      rw [hB1]
      have := Nat.lt_floor_add_one v
      linarith
    linarith
  have hε8' : ε ≤ 1/8 := by linarith
  -- the switch points and the bad cells
  set T : Finset ℝ := ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
        (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
        (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
        (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
        1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
        (α + 2*(1/16-1/10^5) - ε)/2,
        (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
        (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
        2 - (2*(1/16-1/10^5) - ε) - 4*α,
        2 + (2*(1/16-1/10^5) - ε) - 4*α,
        (s - α)/2] : List ℝ).toFinset with hT
  set P : ℕ → Prop := fun n => ∃ τ ∈ T, Real.log ((n:ℝ)-1)/Real.log Z ≤ τ ∧
    τ ≤ Real.log (n:ℝ)/Real.log Z with hP
  -- the per cell allowance
  -- the `α`-integrand is measurable and bounded by `10 / (t log^2 t)`
  have hΦmeas : Measurable (fun t : ℝ => if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
      ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) :=
    phi_measurable (measurable_buchstab_new hω hz) (Z := Z) (s := s) (α := α) (ε := ε)
  have hWmeas : Measurable (fun t : ℝ => 1/(t * Real.log t^2)) := by measurability
  have hphimeas : Measurable (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) := hWmeas.mul hΦmeas
  have hphib : ∀ t : ℝ, 1 < t → |(fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t| ≤
        10 * (1/(t * Real.log t^2)) := by
    intro t ht
    have hw : 0 < 1/(t * Real.log t^2) := by
      have : 0 < Real.log t := Real.log_pos ht
      positivity
    have h1 : |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
        ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| ≤ 10 :=
      phi_abs_le hω hz (ε := ε) (Z := Z) (s := s) (α := α) (β := Real.log t/Real.log Z) hα1
    calc |(1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)|
        = (1/(t * Real.log t^2)) *
          |if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0| := by
          rw [abs_mul, abs_of_pos hw]
      _ ≤ (1/(t * Real.log t^2)) * 10 := mul_le_mul_of_nonneg_left h1 (le_of_lt hw)
      _ = 10 * (1/(t * Real.log t^2)) := by ring
  -- `phi_cell_osc`'s constant, shifted: `200 log Z / ((n-1) log^2 (n-1))`, the weight drop, and
  -- the allowance of a cell carrying a jump
  have hint : ∀ n : ℕ, B0 < n →
      IntervalIntegrable (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) volume ((n:ℝ) - 1) (n:ℝ) := by
    intro n hn
    have hn5 : (5:ℝ) ≤ (n:ℝ) := by
      have : 5 ≤ n := by omega
      exact_mod_cast this
    rw [intervalIntegrable_iff]
    have hle : ((n:ℝ) - 1) ≤ (n:ℝ) := by linarith
    rw [Set.uIoc_of_le hle]
    refine MeasureTheory.Integrable.of_bound hphimeas.aestronglyMeasurable.restrict
      (10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hx1 : (1:ℝ) < x := by linarith [hx.1]
    have hbx := hphib x hx1
    have hmono : 1/(x * Real.log x^2) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
      weight_mono (by linarith : (1:ℝ) < (n:ℝ) - 1) (le_of_lt hx.1)
    have hpos : (0:ℝ) < 1/(x * Real.log x^2) := by
      have : 0 < Real.log x := Real.log_pos hx1
      positivity
    rw [Real.norm_eq_abs]
    exact hbx.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  have hδ0 : ∀ n : ℕ, B0 < n → 0 ≤
      ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
          (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
        + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
        + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0)) := by
    intro n hn
    have hnR : (B0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by linarith
    have hnm1 : (1:ℝ) < (n:ℝ) - 1 := by linarith
    have hdrop : 0 ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
      have h := weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
      linarith
    have hWn : 0 ≤ 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
      have : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
      positivity
    have hcoef : 0 ≤ 200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
      have h1 : 0 < Real.log ((n:ℝ)-1) := Real.log_pos hnm1
      positivity
    have hthird : 0 ≤ (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0) := by
      split_ifs
      · have : 0 < Real.log (B0:ℝ) := Real.log_pos (by linarith)
        positivity
      · norm_num
    have := mul_nonneg hWn hcoef
    linarith
  -- the per cell oscillation
  have hosc : ∀ n : ℕ, B0 < n → ∀ t ∈ Set.Icc ((n:ℝ) - 1) (n:ℝ),
      |(fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ) -
       (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t| ≤
      ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
          (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
        + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
        + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0)) := by
    intro n hn t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hn4n : 4 ≤ n := by omega
    have hn5n : 5 ≤ n := by omega
    have hnR : (B0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hn5 : (5:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn5n
    have hn4 : (4:ℝ) ≤ (n:ℝ) := by linarith
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hnm0 : (0:ℝ) < (n:ℝ) - 1 := by linarith
    have hnm1 : (1:ℝ) < (n:ℝ) - 1 := by linarith
    have ht1' : (4:ℝ) ≤ t := by linarith
    have ht0 : (0:ℝ) < t := by linarith
    have ht1'' : (1:ℝ) < t := by linarith
    have htn : t ≤ (n:ℝ) := ht2
    have hWosc : |1/((n:ℝ) * Real.log (n:ℝ)^2) - 1/(t * Real.log t^2)| ≤
        1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) :=
      weight_cell_osc hn4n ht1 ht2
    have hWn0 : (0:ℝ) < 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
      have : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
      positivity
    have hWB0 : (0:ℝ) ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) := by
      have : 0 < Real.log (B0:ℝ) := Real.log_pos (by linarith)
      positivity
    have hB0t : (B0:ℝ) ≤ t := by
      have h1 : (B0:ℝ) + 1 ≤ (n:ℝ) := by
        have h2 : B0 + 1 ≤ n := by omega
        exact_mod_cast h2
      linarith
    have hB0n : (B0:ℝ) ≤ (n:ℝ) := by
      have h2 : B0 ≤ n := by omega
      exact_mod_cast h2
    by_cases hPn : P n
    · -- a cell carrying a jump: the crude bound
      have hthird : (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0) =
          20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by rw [if_pos hPn]
      have hWB0t : 1/(t * Real.log t^2) ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) :=
        weight_mono (by linarith : (1:ℝ) < (B0:ℝ)) hB0t
      have hWB0n : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) :=
        weight_mono (by linarith : (1:ℝ) < (B0:ℝ)) hB0n
      have h1 : |(1/((n:ℝ) * Real.log (n:ℝ)^2)) *
          (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0)| ≤
          10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
        have h2 := hphib _ (by linarith : (1:ℝ) < (n:ℝ))
        exact h2.trans (mul_le_mul_of_nonneg_left hWB0n (by norm_num))
      have h2 : |(1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
        have h3 := hphib t ht1''
        exact h3.trans (mul_le_mul_of_nonneg_left hWB0t (by norm_num))
      have htri : |(1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
          (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
        · linarith [abs_le.mp h2, abs_le.mp h1]
        · linarith [abs_le.mp h1, abs_le.mp h2]
      have hcoef : (0:ℝ) ≤ 200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by
        have : 0 < Real.log ((n:ℝ)-1) := Real.log_pos hnm1
        positivity
      have hdrop : 0 ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2) := by
        have hm := weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
        linarith
      have := mul_nonneg hWn0.le hcoef
      rw [hthird]
      linarith
    · -- a good cell
      have hthird : (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0) = 0 := by
        rw [if_neg hPn]
      -- no switch point in the cell
      have hnoCell : ∀ τ ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
          (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
          (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
          1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          (α + 2*(1/16-1/10^5) - ε)/2,
          (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
          (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
          2 - (2*(1/16-1/10^5) - ε) - 4*α,
          2 + (2*(1/16-1/10^5) - ε) - 4*α,
          (s - α)/2] : List ℝ).toFinset,
          ¬(Real.log ((n:ℝ)-1)/Real.log Z ≤ τ ∧ τ ≤ Real.log (n:ℝ)/Real.log Z) := by
        intro τ hτ hc
        have hτT : τ ∈ T := by
          rw [hT]
          simpa using hτ
        exact hPn ⟨τ, hτT, hc⟩
      have hβt0 : (0:ℝ) < Real.log t/Real.log Z :=
        div_pos (Real.log_pos ht1'') hLZ
      have hβn0 : (0:ℝ) < Real.log (n:ℝ)/Real.log Z :=
        div_pos (Real.log_pos (by linarith)) hLZ
      have hβtn : Real.log t/Real.log Z ≤ Real.log (n:ℝ)/Real.log Z :=
        div_le_div_of_nonneg_right (Real.log_le_log ht0 htn) hLZ.le
      have hβm_t : Real.log ((n:ℝ)-1)/Real.log Z ≤ Real.log t/Real.log Z :=
        div_le_div_of_nonneg_right (Real.log_le_log hnm0 ht1) hLZ.le
      -- restrict the switch points to the sub-cell `[β_t, β_n]`
      have hnoSub : ∀ τ ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
          (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
          (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
          1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          (α + 2*(1/16-1/10^5) - ε)/2,
          (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
          (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
          2 - (2*(1/16-1/10^5) - ε) - 4*α,
          2 + (2*(1/16-1/10^5) - ε) - 4*α,
          (s - α)/2] : List ℝ).toFinset,
          ¬(Real.log t/Real.log Z ≤ τ ∧ τ ≤ Real.log (n:ℝ)/Real.log Z) := by
        intro τ hτ hc
        exact hnoCell τ hτ ⟨le_trans hβm_t hc.1, hc.2⟩
      have hreg0 := cell_region_const_beta (ε := ε) (α := α) (s := s) hβtn hnoSub
      -- the Buchstab argument case
      have hargTh := hnoCell _ (by simp : (s - α)/2 ∈ ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
          (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
          (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
          (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
          1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
          (α + 2*(1/16-1/10^5) - ε)/2,
          (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
          (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
          2 - (2*(1/16-1/10^5) - ε) - 4*α,
          2 + (2*(1/16-1/10^5) - ε) - 4*α,
          (s - α)/2] : List ℝ).toFinset)
      have hcase : 1 ≤ (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) ∨
          (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) < 1 := by
        by_contra hc
        push_neg at hc
        obtain ⟨h1, h2⟩ := hc
        have e1 : (s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z) =
            (s - α)/(Real.log (n:ℝ)/Real.log Z) - 1 := by
          rw [sub_div, div_self (ne_of_gt hβn0)]
        have e2 : (s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z) =
            (s - α)/(Real.log t/Real.log Z) - 1 := by
          rw [sub_div, div_self (ne_of_gt hβt0)]
        rw [e1] at h1
        rw [e2] at h2
        -- `2 β_t ≤ s - α < 2 β_n`, so `(s - α)/2` sits strictly between the two switch points
        have h2a : (2:ℝ) ≤ (s - α)/(Real.log t/Real.log Z) := by linarith
        have h1a : (s - α)/(Real.log (n:ℝ)/Real.log Z) < 2 := by linarith
        have h2ge : 2 * (Real.log t/Real.log Z) ≤ s - α := by
          have := (le_div_iff₀ hβt0).mp h2a
          linarith
        have h1lt : s - α < 2 * (Real.log (n:ℝ)/Real.log Z) := by
          have := (div_lt_iff₀ hβn0).mp h1a
          linarith
        refine hargTh ⟨?_, ?_⟩
        · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
          linarith
        · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
          linarith
      -- the cell oscillation of `Φ`
      have hΦosc : |(if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
        phi_cell_osc hω hz (ε := ε) (Z := Z) (s := s) (α := α) (n := n) hZ
          hn4n ht1 ht2 hα1 hα2 hs0 hs1 hreg0.symm hcase
      have hΦt : |(if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤ 10 :=
        phi_abs_le hω hz (ε := ε) (Z := Z) (s := s) (α := α) (β := Real.log t/Real.log Z) hα1
      -- split the difference of the two products
      have hsplit : (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
          (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) =
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            ((if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
             (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) +
          ((1/((n:ℝ) * Real.log (n:ℝ)^2)) - 1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) := by
        ring
      have h1 : |(1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            ((if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
             (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))| ≤
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) := by
        rw [abs_mul, abs_of_pos hWn0]
        exact mul_le_mul_of_nonneg_left hΦosc hWn0.le
      have hdrop0 : (0:ℝ) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) -
          1/((n:ℝ) * Real.log (n:ℝ)^2) := by
        have hm := weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
        linarith
      have h2 : |((1/((n:ℝ) * Real.log (n:ℝ)^2)) - 1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
          10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2)) := by
        rw [abs_mul]
        calc |1/((n:ℝ) * Real.log (n:ℝ)^2) - 1/(t * Real.log t^2)| *
              |(if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
                ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)|
            ≤ (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2)) * 10 :=
              mul_le_mul hWosc hΦt (abs_nonneg _) hdrop0
          _ = 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) -
                1/((n:ℝ) * Real.log (n:ℝ)^2)) := by ring
      have htri := abs_add_le ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            ((if lowerTwoDiscarded ε α (Real.log (n:ℝ)/Real.log Z) then
              ω ((s - α - Real.log (n:ℝ)/Real.log Z)/(Real.log (n:ℝ)/Real.log Z))/α else 0) -
             (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)))
          (((1/((n:ℝ) * Real.log (n:ℝ)^2)) - 1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))
      rw [hsplit, hthird, add_zero]
      linarith [h1, h2, htri]
  -- the cell by cell comparison of the sum and the integral over `(B0, B1]`
  have hcell : |(∑ n ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ)) -
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
      (∑ n ∈ Finset.Ioc B0 B1,
        ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
          + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
          + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0))) :=
    sum_sub_integral_le_of_cell _ _ B0 hδ0 hint hosc B1 hB0B1
  -- the number of cells carrying a jump
  have hTcard : T.card ≤ 15 := by
    rw [hT]
    have h := List.toFinset_card_le (l := ([α, (1+7*(2*(1/16-1/10^5)))/15-ε,
      (36*(2*(1/16-1/10^5))-2)/11-ε, (1-α)/2,
      (1/2 + (1+22*(2*(1/16-1/10^5)))/60 - 2*ε - α)/2,
      (2 + 2*(1/16-1/10^5) - ε - 4*α)/7,
      (2 + 2*(1/16-1/10^5) - ε - 4*α)/5,
      1/2 - ((2*(1/16-1/10^5)) + 3*((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
      1/2 - ((2*(1/16-1/10^5)) + ((1+7*(2*(1/16-1/10^5)))/15-ε))/4 + ε - α,
      (α + 2*(1/16-1/10^5) - ε)/2,
      (2 - (2*(1/16-1/10^5) - ε) - 4*α)/3,
      (2 + (2*(1/16-1/10^5) - ε) - 4*α)/3,
      2 - (2*(1/16-1/10^5) - ε) - 4*α,
      2 + (2*(1/16-1/10^5) - ε) - 4*α,
      (s - α)/2] : List ℝ))
    simpa using h
  have hbadcard : ((Finset.Ioc B0 B1).filter P).card ≤ 30 := by
    have h2T : ((Finset.Ioc B0 B1).filter P).card ≤ 2 * T.card := by
      set S : Finset ℕ := (T.image (fun τ => Nat.floor (Z ^ τ) + 1)) ∪
        (T.image (fun τ => Nat.floor (Z ^ τ))) with hS
      have hsub : (Finset.Ioc B0 B1).filter P ⊆ S := by
        intro n hn
        obtain ⟨hn1, hnP⟩ := Finset.mem_filter.mp hn
        obtain ⟨τ, hτT, hP1, hP2⟩ := hnP
        have hn2 : 2 ≤ n := by
          have := (Finset.mem_Ioc.mp hn1).1
          omega
        have hcast : (((n - 1 : ℕ) : ℝ)) = (n:ℝ) - 1 := by
          have h1n : 1 ≤ n := by omega
          rw [Nat.cast_sub h1n]
          simp
        have hn1' : 1 ≤ n - 1 := by omega
        have hlog1 : Real.log (((n - 1 : ℕ) : ℝ)) / Real.log Z ≤ τ := by
          rw [hcast]; exact hP1
        have hlog2 : τ ≤ Real.log ((((n - 1 : ℕ) : ℝ)) + 1) / Real.log Z := by
          rw [hcast]
          have e : ((n:ℝ) - 1) + 1 = (n:ℝ) := by ring
          rw [e]; exact hP2
        have hfl := switch_cell_floor hZ (a := n - 1) hn1' hlog1 hlog2
        rw [hS]
        simp only [Finset.mem_union, Finset.mem_image]
        have hpred : (n - 1) + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
        rcases hfl with h | h
        · refine Or.inl ⟨τ, hτT, ?_⟩
          rw [h, hpred]
        · refine Or.inr ⟨τ, hτT, ?_⟩
          rw [h, hpred]
      calc ((Finset.Ioc B0 B1).filter P).card ≤ S.card := Finset.card_le_card hsub
        _ ≤ (T.image (fun τ => Nat.floor (Z ^ τ) + 1)).card +
              (T.image (fun τ => Nat.floor (Z ^ τ))).card := Finset.card_union_le _ _
        _ ≤ T.card + T.card := by
            have h1 := Finset.card_image_le (s := T) (f := fun τ => Nat.floor (Z ^ τ) + 1)
            have h2 := Finset.card_image_le (s := T) (f := fun τ => Nat.floor (Z ^ τ))
            omega
        _ = 2 * T.card := by ring
    exact le_trans h2T (by omega)
  -- the sum of the allowances
  have hsumδ : (∑ n ∈ Finset.Ioc B0 B1,
        ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
          + 10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))
          + (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0))) ≤
      500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    have hB0_4 : 4 ≤ B0 := hB0ge
    have hB0R4'' : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0_4
    have hlogB0 : 0 < Real.log ((B0:ℝ) - 1) := Real.log_pos (by linarith)
    have hlogle1 : (1:ℝ) ≤ Real.log ((B0:ℝ) - 1) := by
      have h : Real.log 3 ≤ Real.log ((B0:ℝ) - 1) := by
        apply Real.log_le_log (by norm_num)
        linarith
      have h4 : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        linarith [Real.exp_one_lt_d9]
      linarith
    have hden : 0 < ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2 :=
      mul_pos (by linarith) (pow_pos hlogB0 2)
    have hden4 : 0 < ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^4 :=
      mul_pos (by linarith) (pow_pos hlogB0 4)
    have hWB0 : 0 ≤ 1/((B0:ℝ) * Real.log (B0:ℝ)^2) := by
      have hlogB : 0 < Real.log (B0:ℝ) := Real.log_pos (by linarith)
      positivity
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- the first piece: `∑ w(n) A(n) ≤ 200 log Z / ((B0-1) log^4 (B0-1))`
    have hshift : (∑ n ∈ Finset.Ioc B0 B1,
          1/(((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)^4)) =
        ∑ m ∈ Finset.Ioc (B0 - 1) (B1 - 1), 1/((m:ℝ)^2 * Real.log (m:ℝ)^4) := by
      refine Finset.sum_bij (fun n _ => n - 1) ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
      · intro n1 hn1 n2 hn2 he
        obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hn1
        obtain ⟨h3, _⟩ := Finset.mem_Ioc.mp hn2
        omega
      · intro m hm
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hm
        refine ⟨m + 1, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro n hn
        obtain ⟨h1, _⟩ := Finset.mem_Ioc.mp hn
        have e : (((n - 1 : ℕ)) : ℝ) = (n:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          simp
        rw [e]
    have hpiece1 : (∑ n ∈ Finset.Ioc B0 B1,
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) ≤
        200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^4) := by
      have hstep : ∀ n ∈ Finset.Ioc B0 B1,
          (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
            (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) ≤
          200 * Real.log Z * (1/(((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)^4)) := by
        intro n hn
        have hn2 : 2 ≤ n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        have hnR2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
        have hB0_5 : 4 ≤ B0 := hB0ge
        have hn5 : (5:ℝ) ≤ (n:ℝ) := by
          have h1 : (B0:ℝ) + 1 ≤ (n:ℝ) := by
            have h3 : B0 + 1 ≤ n := by
              have := (Finset.mem_Ioc.mp hn).1
              omega
            exact_mod_cast h3
          have h2 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0_4
          linarith
        have hnm1 : (1:ℝ) < (n:ℝ) - 1 := by linarith
        have hlogm : 0 < Real.log ((n:ℝ)-1) := Real.log_pos hnm1
        have hW : 1/((n:ℝ) * Real.log (n:ℝ)^2) ≤ 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) :=
          weight_mono hnm1 (by linarith : ((n:ℝ)-1) ≤ (n:ℝ))
        have hpos : 0 < 1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) := by positivity
        calc (1/((n:ℝ) * Real.log (n:ℝ)^2)) *
              (200 * Real.log Z / (((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))
            = 200 * Real.log Z * ((1/((n:ℝ) * Real.log (n:ℝ)^2)) *
                (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) := by ring
          _ ≤ 200 * Real.log Z * ((1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2)) *
                (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hW (le_of_lt hpos)
          _ = 200 * Real.log Z * (1/(((n:ℝ)-1)^2 * Real.log ((n:ℝ)-1)^4)) := by
              congr 1
              field_simp
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, hshift]
      have hsum := sum_inv_sq_log_pow_le (A := B0 - 1) (B := B1 - 1)
        (by omega : 2 ≤ B0 - 1) (k := 4) (by norm_num)
      have hcast1 : (((B0 - 1 : ℕ)) : ℝ) = (B0:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ B0)]
        simp
      rw [hcast1, one_div] at hsum
      have hfin : (0:ℝ) ≤ 200 * Real.log Z := by positivity
      exact mul_le_mul_of_nonneg_left hsum hfin
    -- the second piece: the telescoping weight drop
    have hpiece2 : (∑ n ∈ Finset.Ioc B0 B1,
          10 * (1/(((n:ℝ)-1) * Real.log ((n:ℝ)-1)^2) - 1/((n:ℝ) * Real.log (n:ℝ)^2))) ≤
        10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
      rw [← Finset.mul_sum]
      have htel := tel_weight (N := B0) (B := B1) (by omega : 4 ≤ B0)
      linarith
    -- the third piece: the cells carrying a jump
    have hpiece3 : (∑ n ∈ Finset.Ioc B0 B1,
          (if P n then 20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) else 0)) ≤
        600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
      have hc : ((Finset.Ioc B0 B1).filter P).card ≤ 30 := hbadcard
      have hcR : (((Finset.Ioc B0 B1).filter P).card : ℝ) ≤ 30 := by exact_mod_cast hc
      calc (((Finset.Ioc B0 B1).filter P).card : ℝ) *
            (20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)))
          ≤ 30 * (20 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2))) := by
            apply mul_le_mul_of_nonneg_right hcR
            positivity
        _ = 600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) := by ring
    -- the bookkeeping: `W(B0) ≤ 2/den` and `1/log^4 ≤ 1/log^2`
    have hWB0le : 1/((B0:ℝ) * Real.log (B0:ℝ)^2) ≤ 2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
      have hW1 : 1/((B0:ℝ) * Real.log (B0:ℝ)^2) ≤ 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) :=
        weight_mono (by linarith : (1:ℝ) < (B0:ℝ) - 1) (by linarith : ((B0:ℝ)-1) ≤ (B0:ℝ))
      have h2 : 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) ≤
          2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := by
        have hpos : (0:ℝ) < 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by positivity
        linarith
      calc 1/((B0:ℝ) * Real.log (B0:ℝ)^2)
          ≤ 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := hW1
        _ ≤ 2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := h2
        _ = 2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by rw [mul_one_div]
    have hlogle : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≤ ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^4 := by
      have h2 : Real.log ((B0:ℝ)-1)^2 ≤ Real.log ((B0:ℝ)-1)^4 :=
        pow_le_pow_right₀ hlogle1 (by norm_num : 2 ≤ 4)
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
    have hpiece1' : 200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^4) ≤
        200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) :=
      div_le_div_of_nonneg_left (by positivity) hden hlogle
    have htot : 200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
        + 20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
        + 1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) ≤
        500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
      have hlogZ0 : 0 ≤ Real.log Z := le_of_lt hLZ
      have hden0 : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≠ 0 := ne_of_gt hden
      have e : 200 * Real.log Z / (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          + 20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          + 1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          = (200 * Real.log Z + 1220)/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
        field_simp
        ring
      rw [e, div_le_div_iff₀ hden hden]
      have h1 : 200 * Real.log Z + 1220 ≤ 500000 * (1 + Real.log Z) := by linarith
      exact mul_le_mul_of_nonneg_right h1 hden.le
    have h10 : 10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) ≤
        20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
      have h := mul_le_mul_of_nonneg_left hWB0le (by norm_num : (0:ℝ) ≤ 10)
      calc 10 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2))
          ≤ 10 * (2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := h
        _ = 20/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by ring
    have h600 : 600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2)) ≤
        1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by
      have h := mul_le_mul_of_nonneg_left hWB0le (by norm_num : (0:ℝ) ≤ 600)
      calc 600 * (1/((B0:ℝ) * Real.log (B0:ℝ)^2))
          ≤ 600 * (2/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := h
        _ = 1200/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by ring
    linarith [hpiece1, hpiece1', hpiece2, hpiece3, h10, h600, htot]
  exact hcell.trans hsumδ



set_option maxHeartbeats 20000000 in
/-- The second passage of display 5.17 at one point `α`. -/
private theorem second_passage_pointwise {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε Z s : ℝ} (hε8 : ε ≤ 1/10^8)
    (hZ : 1 < Z) (hZbig : (2:ℝ)^20 ≤ Z)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    {α : ℝ} (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) :
    |(∑ b ∈ Finset.Ioc ⌊Z^(1/10:ℝ)⌋₊ ⌊Z^(1/2:ℝ)⌋₊,
        (1/((b:ℝ) * Real.log (b:ℝ)^2)) *
          (if lowerTwoDiscarded ε α (Real.log (b:ℝ)/Real.log Z) then
            ω ((s - α - Real.log (b:ℝ)/Real.log Z)/(Real.log (b:ℝ)/Real.log Z))/α else 0)) -
      (1/Real.log Z) * (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0))| ≤
      1000000 * (1 + Real.log Z) / (((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1) * Real.log ((⌊Z^(1/10:ℝ)⌋₊ : ℝ) - 1)^2) := by
  classical
  have hZ0 : (0:ℝ) < Z := by linarith
  have hLZ : (0:ℝ) < Real.log Z := Real.log_pos hZ
  set u : ℝ := Z^(1/10:ℝ) with hu
  set v : ℝ := Z^(1/2:ℝ) with hv
  set B0 : ℕ := ⌊u⌋₊ with hB0
  set B1 : ℕ := ⌊v⌋₊ with hB1
  have hu4 : (4:ℝ) ≤ u := by
    have h1 : ((2:ℝ)^20)^(1/10:ℝ) ≤ Z^(1/10:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/10:ℝ) = 4 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [hu]
    linarith
  have hu0 : (0:ℝ) < u := by linarith
  have huv : u ≤ v := by
    rw [hu, hv]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hB0ge : 4 ≤ B0 := by
    rw [hB0]
    exact Nat.le_floor (by push_cast; exact hu4)
  have hB0le : ((B0:ℝ)) ≤ u := by
    rw [hB0]; exact Nat.floor_le (by positivity)
  have hB1le : ((B1:ℝ)) ≤ v := by
    rw [hB1]; exact Nat.floor_le (by positivity)
  have hB0B1 : B0 ≤ B1 := by
    have h1 : (B0:ℝ) ≤ v := le_trans hB0le huv
    rw [hB1]
    exact Nat.le_floor h1
  have hB0w : (1:ℝ) ≤ (B0:ℝ) := by
    have : 1 ≤ B0 := by omega
    exact_mod_cast this
  have hB0R4 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0ge
  have huB1 : u ≤ (B1:ℝ) := by
    -- `u + 1 ≤ v` and `v - 1 ≤ B1`
    have hvpow : v = u^5 := by
      rw [hu, hv, ← Real.rpow_natCast]
      rw [show (1/2:ℝ) = (1/10:ℝ) * 5 by norm_num, Real.rpow_mul (le_of_lt hZ0)]
      norm_num
    have huv1 : u + 1 ≤ v := by
      rw [hvpow]
      have hpow : (4:ℝ)^4 ≤ u^4 := pow_le_pow_left₀ (by norm_num) hu4 4
      have hmul : u * 4^4 ≤ u^5 := by
        rw [show u^5 = u * u^4 by ring]
        exact mul_le_mul_of_nonneg_left hpow (by linarith)
      nlinarith [hmul, hu4]
    have hfl : v - 1 ≤ (B1:ℝ) := by
      rw [hB1]
      have := Nat.lt_floor_add_one v
      linarith
    linarith
  have hε8' : ε ≤ 1/8 := by linarith  -- the `α`-integrand is measurable, and bounded by `10 / (t log^2 t)`
  have hΦmeas : Measurable (fun t : ℝ => if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
      ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0) :=
    phi_measurable (measurable_buchstab_new hω hz) (Z := Z) (s := s) (α := α) (ε := ε)
  have hWmeas : Measurable (fun t : ℝ => 1/(t * Real.log t^2)) := by measurability
  have hphimeas : Measurable (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) :=
    hWmeas.mul hΦmeas
  have hphib : ∀ t : ℝ, 1 < t → |(1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)| ≤
        10 * (1/(t * Real.log t^2)) :=
    fun t ht => phi_weight_abs_le hω hz hα1 t ht
  -- the sum against the integral, from the extracted cell comparison
  have hcell0 : |(∑ b ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (b:ℝ)) -
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
      500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    have h := second_passage_cell (ω := ω) hω hz hε8 hZ hZbig hs0 hs1 hα1 hα2
    have e1 : (⌊Z^(1/10:ℝ)⌋₊ : ℕ) = B0 := by rw [hB0, hu]
    have e2 : (⌊Z^(1/2:ℝ)⌋₊ : ℕ) = B1 := by rw [hB1, hv]
    rw [e1, e2] at h
    exact h
  -- the change of variables `t = Z^β`
  have hsub : (1/Real.log Z) * (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0)) =
      ∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t := by
    have h := integral_log_subst (Z := Z) hZ
      (g := fun β : ℝ => if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0)
    rw [hu, hv, ← h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : (0:ℝ) < t := by
      rw [Set.uIcc_of_le huv] at ht
      linarith [ht.1, hu0]
    have hlt : 0 < Real.log t := Real.log_pos (by
      rw [Set.uIcc_of_le huv] at ht
      linarith [ht.1, hu4])
    have hβ0 : (0:ℝ) < Real.log t / Real.log Z := div_pos hlt hLZ
    by_cases hD : lowerTwoDiscarded ε α (Real.log t/Real.log Z)
    · rw [if_pos hD, if_pos hD]
      field_simp
    · rw [if_neg hD, if_neg hD]
      ring
  -- the two slivers
  have hsliver : |(∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
        (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
          ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
      500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    have hB0_1 : ((B0:ℝ)) ≤ u := hB0le
    have huB1' : u ≤ (B1:ℝ) := huB1
    have hB1v : ((B1:ℝ)) ≤ v := hB1le
    -- integrability of the pieces
    have hInt : ∀ p q : ℝ, (1:ℝ) < p → p ≤ q → IntervalIntegrable
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) volume p q := by
      intro p q hp hpq
      · rw [intervalIntegrable_iff]
        rw [Set.uIoc_of_le hpq]
        refine MeasureTheory.Integrable.of_bound hphimeas.aestronglyMeasurable.restrict
          (10 * (1/(p * Real.log p^2))) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        have hx1 : (1:ℝ) < x := lt_of_lt_of_le hp (le_of_lt hx.1)
        have hbx := hphib x hx1
        have hmono : 1/(x * Real.log x^2) ≤ 1/(p * Real.log p^2) :=
          weight_mono hp (le_of_lt hx.1)
        have hposx : (0:ℝ) < 1/(x * Real.log x^2) := by
          have : 0 < Real.log x := Real.log_pos hx1
          positivity
        rw [Real.norm_eq_abs]
        exact hbx.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
    have hsplit1 : (∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) =
        (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
        (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hInt u _ (by linarith) huB1')
        (hInt _ v (by linarith) hB1v)).symm
    have hsplit2 : (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) =
        (∫ t in (B0:ℝ)..u, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
        (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) :=
      (intervalIntegral.integral_add_adjacent_intervals (hInt _ _ (by linarith) hB0_1)
        (hInt _ _ (by linarith) huB1')).symm
    -- the lower sliver vanishes
    have hzero : (∫ t in (B0:ℝ)..u, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) = 0 := by
      apply integral_eq_zero_of_open hB0_1
      intro x hx1 hx2
      have hx0 : (0:ℝ) < x := by linarith
      have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
      have hxle : Real.log x / Real.log Z ≤ 1/10 := by
        rw [div_le_iff₀ hLZ]
        have h2 : Real.log x ≤ Real.log u := Real.log_le_log hx0 (le_of_lt hx2)
        rw [hu, Real.log_rpow hZ0] at h2
        nlinarith [h2, hLZ]
      by_cases hD : lowerTwoDiscarded ε α (Real.log x / Real.log Z)
      · rw [if_pos hD]
        obtain ⟨hc, -⟩ := hD
        have hc' : (1+7*(2*(1/16-1/10^5)))/15 - 1/8 ≤ 1/10 := by norm_num
        linarith
      · rw [if_neg hD, mul_zero]
    -- the upper sliver is short
    have hupper : |(∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
        10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by
      have hb1 : (1:ℝ) < (B1:ℝ) := by
        have : (4:ℝ) ≤ (B1:ℝ) := le_trans hB0R4 (by exact_mod_cast hB0B1)
        linarith
      have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (B1:ℝ)) (b := v) (C := 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)))
        (f := fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0))
        (by
          intro x hx
          rw [Set.uIoc_of_le hB1v] at hx
          have hx1 : (1:ℝ) < x := lt_of_lt_of_le hb1 (le_of_lt hx.1)
          have hbx := hphib x hx1
          have hmono : 1/(x * Real.log x^2) ≤ 1/((B1:ℝ) * Real.log (B1:ℝ)^2) :=
            weight_mono hb1 (le_of_lt hx.1)
          exact hbx.trans (mul_le_mul_of_nonneg_left hmono (by norm_num)))
      rw [Real.norm_eq_abs] at hbnd
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - (B1:ℝ))] at hbnd
      refine hbnd.trans ?_
      have hlen : v - (B1:ℝ) ≤ 1 := by
        rw [hB1]
        linarith [Nat.lt_floor_add_one v]
      have hpos : (0:ℝ) ≤ 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by
        have : (0:ℝ) < Real.log (B1:ℝ) := Real.log_pos hb1
        positivity
      calc 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) * (v - (B1:ℝ))
          ≤ 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) * 1 := by
            apply mul_le_mul_of_nonneg_left hlen
            positivity
        _ = 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by ring
    -- assemble
    rw [hsplit1, hsplit2, hzero, zero_add]
    have htri : |(∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
        (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
      (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| ≤
        10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) := by
      have e : (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) +
          (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
        (∫ t in u..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
            (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
              ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) =
        (∫ t in (B1:ℝ)..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) := by
        ring
      rw [e]
      exact hupper
    have hB1le' : (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) ≤
        2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)) := by
      have hB1_4 : (4:ℝ) ≤ (B1:ℝ) := le_trans hB0R4 (by exact_mod_cast hB0B1)
      have hlogB1 : (1:ℝ) < Real.log (B1:ℝ) := by
        have h : Real.log 3 < Real.log (B1:ℝ) := by
          apply Real.log_lt_log (by norm_num)
          linarith
        have h3 : (1:ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          linarith [Real.exp_one_lt_d9]
        linarith
      have hlogB0 : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by
        have : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast (by omega : 4 ≤ B0)
        linarith)
      have hden0 : 0 < ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 :=
        mul_pos (by linarith) (pow_pos hlogB0 2)
      have hcomp : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≤ (B1:ℝ) * Real.log (B1:ℝ)^2 := by
        have h1 : ((B0:ℝ)-1) ≤ (B1:ℝ) := by linarith
        have h2 : Real.log ((B0:ℝ)-1) ≤ Real.log (B1:ℝ) := by
          apply Real.log_le_log (by linarith); linarith
        have h3 : Real.log ((B0:ℝ)-1)^2 ≤ Real.log (B1:ℝ)^2 :=
          pow_le_pow_left₀ (le_of_lt hlogB0) h2 2
        exact mul_le_mul h1 h3 (by positivity) (by linarith)
      have h0 := one_div_le_one_div_of_le hden0 hcomp
      have hpos : (0:ℝ) < 1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) := by positivity
      linarith
    have hfin2 : 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) ≤
        500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
      have hlogB0' : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by
        have : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast (by omega : 4 ≤ B0)
        linarith)
      have hden0 : 0 < ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 :=
        mul_pos (by linarith) (pow_pos hlogB0' 2)
      have hlogle1 : (1:ℝ) ≤ Real.log ((B0:ℝ)-1) := by
        have h : Real.log 3 ≤ Real.log ((B0:ℝ)-1) := by
          apply Real.log_le_log (by norm_num)
          have : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast (by omega : 4 ≤ B0)
          linarith
        have h3 : (1:ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          linarith [Real.exp_one_lt_d9]
        linarith
      have hlogZ0 : 0 ≤ Real.log Z := le_of_lt hLZ
      rw [le_div_iff₀ hden0]
      have h10 := mul_le_mul_of_nonneg_left hB1le' (by norm_num : (0:ℝ) ≤ 10)
      have h20 : (10:ℝ) * (2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2))) *
          (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) = 20 := by
        have hB0m1 : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≠ 0 := by
          have h1 : (0:ℝ) < (B0:ℝ) - 1 := by linarith
          have h2 : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by linarith)
          exact ne_of_gt (mul_pos h1 (pow_pos h2 2))
        have hB0nz : (B0:ℝ) - 1 ≠ 0 := by linarith
        field_simp [hB0m1, hB0nz]
        ring
      calc 10 * (1/((B1:ℝ) * Real.log (B1:ℝ)^2)) * (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)
          ≤ (10 * (2 * (1/(((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2)))) *
              (((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2) :=
            mul_le_mul_of_nonneg_right h10 hden0.le
        _ = 20 := h20
        _ ≤ 500000 * (1 + Real.log Z) := by nlinarith [hlogZ0]
    exact htri.trans hfin2
  -- the final assembly
  have hassemble : |(∑ n ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ)) -
      (1/Real.log Z) * (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε α β then ω ((s - α - β)/β)/(α*β^2) else 0))| ≤
      1000000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    rw [hsub]
    have h1 := abs_sub_le ((∑ n ∈ Finset.Ioc B0 B1,
        (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) (n:ℝ)))
      (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)
      (∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)
    have h2 : |(∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
        (∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| =
        |(∫ t in u..v, (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t) -
        (∫ t in (B0:ℝ)..(B1:ℝ), (fun t : ℝ => (1/(t * Real.log t^2)) *
          (if lowerTwoDiscarded ε α (Real.log t/Real.log Z) then
            ω ((s - α - Real.log t/Real.log Z)/(Real.log t/Real.log Z))/α else 0)) t)| :=
      abs_sub_comm _ _
    rw [h2] at h1
    have hdbl : 500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)
        + 500000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)
        = 1000000 * (1 + Real.log Z) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
        have hB0m1 : ((B0:ℝ)-1) * Real.log ((B0:ℝ)-1)^2 ≠ 0 := by
          have h1 : (0:ℝ) < (B0:ℝ) - 1 := by linarith
          have h2 : 0 < Real.log ((B0:ℝ)-1) := Real.log_pos (by linarith)
          exact ne_of_gt (mul_pos h1 (pow_pos h2 2))
        have hB0nz : (B0:ℝ) - 1 ≠ 0 := by linarith
        field_simp [hB0m1, hB0nz]
        ring
    linarith [h1, hcell0, hsliver, hdbl]
  -- rewrite the range and the constant
  rw [hB0, hB1, hu]
  exact hassemble


/-! ### NEW: the tail of the sum vanishes, and the leaf -/

/-- The summand of the second passage vanishes outside `(Z^(1/10), Z^(1/2)]`. -/
private theorem second_passage_summand_zero {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    {ε x s : ℝ} (hZ1 : 1 < scaleZ ε x) (hε8 : ε ≤ 1/10^8)
    {α : ℝ} (hα1 : 1/10 ≤ α) (hα2 : α ≤ 1/2) {b : ℕ}
    (hb : expo ε x b ≤ 1/10 ∨ 1/2 < expo ε x b) :
    (1/((b:ℝ) * Real.log (b:ℝ)^2)) *
      (if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((s - α - expo ε x b) / expo ε x b) / α else 0) = 0 := by
  rw [expo] at hb ⊢
  have hzero : (if lowerTwoDiscarded ε α (Real.log (b:ℝ)/Real.log (scaleZ ε x)) then
      ω ((s - α - Real.log (b:ℝ)/Real.log (scaleZ ε x))/(Real.log (b:ℝ)/Real.log (scaleZ ε x)))/α
      else 0) = 0 := by
    rw [if_neg]
    intro hLT
    obtain ⟨hc, hba, ha, -⟩ := hLT
    rcases hb with hb | hb
    · have hcut : (1/10:ℝ) < (1+7*(2*(1/16-1/10^5)))/15 - 1/10^8 := by norm_num
      have hcut' : (1/10:ℝ) < (1+7*(2*(1/16-1/10^5)))/15 - ε := by linarith
      linarith
    · linarith
  rw [hzero, mul_zero]

/-- A negative power of `x` is at most a negative power of `log x`, times a constant. -/
private theorem rpow_neg_le_log_rpow {A c x : ℝ} (hA : 0 < A) (hc : 0 < c) (hx : 1 < x) :
    x ^ (-c) ≤ (A/c)^A * Real.log x ^ (-A) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hr : 0 < c/A := div_pos hc hA
  have hAc : 0 < A/c := div_pos hA hc
  have h1 : Real.log x ≤ x^(c/A)/(c/A) := log_le_rpow_div hx0 hr
  have h2 : Real.log x ^ A ≤ (x^(c/A)/(c/A))^A := Real.rpow_le_rpow hlog.le h1 hA.le
  have h3 : (x^(c/A)/(c/A))^A = x^c / (c/A)^A := by
    rw [Real.div_rpow (le_of_lt (Real.rpow_pos_of_pos hx0 _)) hr.le]
    congr 1
    rw [← Real.rpow_mul (le_of_lt hx0)]
    have e : c / A * A = c := by field_simp
    rw [e]
  have hmul : (A/c)^A * (c/A)^A = 1 := by
    have hm : (A/c) * (c/A) = 1 := by field_simp
    calc (A/c)^A * (c/A)^A = ((A/c) * (c/A))^A := (Real.mul_rpow hAc.le hr.le).symm
      _ = 1 := by rw [hm, Real.one_rpow]
  have h4 : ((c/A)^A)⁻¹ = (A/c)^A := inv_eq_of_mul_eq_one_left hmul
  have h5 : (x^(c/A)/(c/A))^A = x^c * (A/c)^A := by
    rw [h3, div_eq_mul_inv, h4]
  rw [h5] at h2
  rw [Real.rpow_neg (le_of_lt hx0), Real.rpow_neg hlog.le, inv_eq_one_div, inv_eq_one_div]
  have eR : (A/c)^A * (1 / Real.log x ^ A) = (A/c)^A / Real.log x ^ A := mul_one_div _ _
  rw [eR, div_le_div_iff₀ (Real.rpow_pos_of_pos hx0 c) (Real.rpow_pos_of_pos hlog A)]
  linarith [h2]


set_option maxHeartbeats 8000000 in
/-- P0069 page 51, display 5.17, "a straightforward consequence of the prime number
theorem", the outer primes `p1`, `p2` of the E2 sum of display 5.15 at one point `m` of J. The
sum over the prime pairs with exponents in E2 of `ω(log (m / (p1 p2)) / log p2) / log p2`
weighted by `1 / (p1 p2)` is `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at
`m = Z^s`, with every log power saved. CONDITIONAL ON `leaf_two_pair_riemann_first` and
`leaf_two_pair_riemann_second`. -/
private theorem two_pair_density_pointwise (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
            Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := two_pair_first_prime ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := two_pair_second_prime ω hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := two_pair_riemann ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx2 : C2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx3 : C3 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hC : |C1| + |C2| + |C3| + 1 ≤ max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hxone : (1 : ℝ) ≤ x := by
    have h1 := abs_nonneg C1
    have h2 := abs_nonneg C2
    have h3 := abs_nonneg C3
    linarith
  have hL : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hxone) _
  have b1 := hC1 x hx1 m hm1 hm2
  have b2 := hC2 x hx2 m hm1 hm2
  have b3 := hC3 x hx3 m hm1 hm2
  have hiter := two_pair_sum_iterated ⌊2 * x ^ (11 / 20 + ε)⌋₊
    (fun a b => lowerTwoDiscarded ε (expo ε x a) (expo ε x b))
    (fun a b => ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
      Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)))
  have hsplit := two_pair_sum_split ⌊2 * x ^ (11 / 20 + ε)⌋₊ primeWeight
    (fun n => 1 / Real.log (n : ℝ))
    (fun a b => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
      ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
        Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0)
  beta_reduce at hiter hsplit
  rw [hiter, hsplit]
  have a1 := abs_le.mp b1
  have a2 := abs_le.mp b2
  have a3 := abs_le.mp b3
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hL
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hL
  have k3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hL
  have k4 := mul_le_mul_of_nonneg_right hC hL
  have k5 : (|C1| + |C2| + |C3| + 1) * Real.log x ^ (-A) =
      |C1| * Real.log x ^ (-A) + |C2| * Real.log x ^ (-A) + |C3| * Real.log x ^ (-A) +
        Real.log x ^ (-A) := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17, the prime number theorem with partial summation for one outer prime of
display 5.15, at stretched exponential precision. -/
private theorem two_pair_pnt_harmonic_exp (N : ℝ) (hN : 0 < N) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, C ≤ X → ∀ L U : ℕ, L ≤ U → X ^ c ≤ (L : ℝ) → (U : ℝ) ≤ X →
      ∀ (G : ℕ → ℝ) (M V : ℝ), 0 ≤ M → (∀ n ∈ Finset.Ioc L U, |G n| ≤ M) →
        ∑ i ∈ Finset.Ico (L + 1) U, |G (i + 1) - G i| ≤ V →
        |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ)) * (G n / (n : ℝ))| ≤
          C * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨Cq, hCq, hp⟩ := prime_prefix_level_exp (c := c) hc (N + 2) (by linarith)
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 1
  refine ⟨3 * Cq + CL + 30, by positivity, fun X hX L U hLU hXL hUX G M V hM0 hG hV => ?_⟩
  have hCqX : Cq ≤ X := by
    have h1 : (0:ℝ) ≤ CL := hCL.le
    linarith
  have hCLX : CL ≤ X := by
    have h1 : (0:ℝ) ≤ Cq := hCq.le
    linarith
  have hX0 : 0 < X := by
    have h1 : (0:ℝ) ≤ 3 * Cq + CL := by positivity
    linarith
  have hlogX : 0 < Real.log X := by
    have h1 : (2:ℝ) ≤ X := by
      have h2 : (0:ℝ) ≤ 3 * Cq + CL := by positivity
      linarith
    exact Real.log_pos (by linarith)
  have hX30 : (30 : ℝ) ≤ X := by
    have h5 : (0:ℝ) ≤ 3 * Cq + CL := by positivity
    linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  set E := Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set Kl : ℝ := Cq * E with hKldef
  have hKl0 : 0 ≤ Kl := by positivity
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hV
  have hMV : 0 ≤ M + V := add_nonneg hM0 hV0
  have hpre : ∀ i : ℕ, L ≤ i → i ≤ U →
      |∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| ≤ Kl * (i : ℝ) := by
    intro i hLi hiU
    have hiL : (L : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr hLi
    have hiX : (i : ℝ) ≤ X := le_trans (by exact_mod_cast hiU) hUX
    have h := hp X hCqX (i : ℝ) (hXL.trans hiL) hiX L i hLi le_rfl
    calc |∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))|
        ≤ Cq * (i : ℝ) * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) := h
      _ = Kl * (i : ℝ) := by rw [hKldef]; ring
  rcases hLU.eq_or_lt with rfl | hlt
  · rw [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    have h1 : (0:ℝ) ≤ (3 * Cq + CL + 30) * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
      have h2 : (0:ℝ) ≤ 3 * Cq + CL + 30 := by positivity
      have h3 : (0:ℝ) ≤ Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg h2 hMV) h3
    exact h1
  have hU0 : (0 : ℝ) < (U : ℝ) := by
    have : (L : ℝ) < (U : ℝ) := Nat.cast_lt.mpr hlt
    have h1 : (0:ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  have hab := two_pair_abel (fun n => primeWeight n - 1 / Real.log (n : ℝ))
    (fun n => G n / (n : ℝ)) L hLU
  beta_reduce at hab
  rw [hab, Finset.sum_eq_sum_Ico_succ_bot hlt, Finset.Ioc_self, Finset.sum_empty, mul_zero,
    zero_add]
  have hend : |G U / (U : ℝ) * ∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ))| ≤
      M * Kl := by
    rw [abs_mul, abs_div, abs_of_pos hU0]
    have h1 : |G U| / (U : ℝ) ≤ M / (U : ℝ) :=
      div_le_div_of_nonneg_right (hG U (Finset.mem_Ioc.mpr ⟨hlt, le_rfl⟩)) hU0.le
    calc |G U| / (U : ℝ) * |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ))|
        ≤ M / (U : ℝ) * (Kl * (U : ℝ)) :=
          mul_le_mul h1 (hpre U hLU le_rfl) (abs_nonneg _) (div_nonneg hM0 hU0.le)
      _ = M * Kl := by field_simp
  have hmid : ∀ i ∈ Finset.Ico (L + 1) U,
      |(G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)) *
        ∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| ≤
        Kl * (|G (i + 1) - G i| + M * (1 / (i : ℝ))) := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hi0 : 0 < (i : ℝ) := by
      have : 0 < i := by omega
      exact_mod_cast this
    have hGi := hG i (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
    have hD : G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ) =
        (G (i + 1) - G i) / ((i : ℝ) + 1) - G i / ((i : ℝ) * ((i : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    have hDabs : |G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)| ≤
        (|G (i + 1) - G i| + M * (1 / (i : ℝ))) / (i : ℝ) := by
      rw [hD]
      have h1 : |(G (i + 1) - G i) / ((i : ℝ) + 1)| ≤ |G (i + 1) - G i| / (i : ℝ) := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (i : ℝ) + 1)]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hi0 (by linarith)
      have h2 : |G i / ((i : ℝ) * ((i : ℝ) + 1))| ≤ M * (1 / (i : ℝ)) / (i : ℝ) := by
        rw [abs_div, abs_of_pos (mul_pos hi0 (by linarith : (0 : ℝ) < (i : ℝ) + 1))]
        have h3 : |G i| / ((i : ℝ) * ((i : ℝ) + 1)) ≤ M / ((i : ℝ) * (i : ℝ)) :=
          div_le_div₀ hM0 hGi (mul_pos hi0 hi0)
            (mul_le_mul_of_nonneg_left (by linarith) hi0.le)
        have h4 : M / ((i : ℝ) * (i : ℝ)) = M * (1 / (i : ℝ)) / (i : ℝ) := by
          field_simp
        linarith
      have h5 := abs_sub (( G (i + 1) - G i) / ((i : ℝ) + 1)) (G i / ((i : ℝ) * ((i : ℝ) + 1)))
      have h6 : (|G (i + 1) - G i| + M * (1 / (i : ℝ))) / (i : ℝ) =
          |G (i + 1) - G i| / (i : ℝ) + M * (1 / (i : ℝ)) / (i : ℝ) := by ring
      linarith
    have hnum : 0 ≤ |G (i + 1) - G i| + M * (1 / (i : ℝ)) :=
      add_nonneg (abs_nonneg _) (mul_nonneg hM0 (by positivity))
    rw [abs_mul]
    calc |G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)| *
          |∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))|
        ≤ (|G (i + 1) - G i| + M * (1 / (i : ℝ))) / (i : ℝ) * (Kl * (i : ℝ)) :=
          mul_le_mul hDabs (hpre i (by omega) (by omega)) (abs_nonneg _)
            (div_nonneg hnum hi0.le)
      _ = Kl * (|G (i + 1) - G i| + M * (1 / (i : ℝ))) := by field_simp
  have hharm : ∑ i ∈ Finset.Ico (L + 1) U, (1 : ℝ) / (i : ℝ) ≤ 1 + Real.log X := by
    have hh : ∑ n ∈ Finset.Icc 1 U, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (U : ℝ) := by
      have h1 := harmonic_le_one_add_log U
      rw [harmonic_eq_sum_Icc] at h1
      push_cast at h1
      simpa [one_div] using h1
    have hsub : Finset.Ico (L + 1) U ⊆ Finset.Icc 1 U := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      rw [Finset.mem_Icc]
      omega
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) (fun _ _ _ => by positivity)
    have h3 : Real.log (U : ℝ) ≤ Real.log X := Real.log_le_log hU0 hUX
    linarith
  have hsum : |∑ i ∈ Finset.Ico (L + 1) U,
      (G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)) *
        ∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| ≤
      Kl * (V + M * (1 + Real.log X)) :=
    calc _ ≤ ∑ i ∈ Finset.Ico (L + 1) U,
          |(G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)) *
            ∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico (L + 1) U, Kl * (|G (i + 1) - G i| + M * (1 / (i : ℝ))) :=
          Finset.sum_le_sum hmid
      _ = Kl * (∑ i ∈ Finset.Ico (L + 1) U, |G (i + 1) - G i| +
            M * ∑ i ∈ Finset.Ico (L + 1) U, (1 : ℝ) / (i : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ Kl * (V + M * (1 + Real.log X)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add hV (mul_le_mul_of_nonneg_left hharm hM0)) hKl0
  have e1 := abs_le.mp hend
  have e2 := abs_le.mp hsum
  -- absorption of the `log X`
  have habs : Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ)) ≤
      Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have h := hLX X hCLX
    have he : (-(N + (1:ℕ) + 1) : ℝ) = -(N + 2) := by push_cast; ring
    rwa [pow_one, he] at h
  have hfin : M * Kl + Kl * (V + M * (1 + Real.log X)) ≤
      (3 * Cq + CL + 30) * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
    have hKlE : Kl = Cq * E := hKldef
    have hb1 : M * (1 + Real.log X) ≤ 2 * M * Real.log X := by nlinarith
    have hb2 : M * Kl + Kl * (V + M * (1 + Real.log X)) =
        Kl * (M + V + M * (1 + Real.log X)) := by ring
    rw [hb2]
    have hb3 : M + V + M * (1 + Real.log X) ≤ 3 * (M + V) * Real.log X := by nlinarith
    have hb4 : Kl * (M + V + M * (1 + Real.log X)) ≤ Kl * (3 * (M + V) * Real.log X) :=
      mul_le_mul_of_nonneg_left hb3 hKl0
    have hb5 : Kl * (3 * (M + V) * Real.log X) = 3 * Cq * (M + V) *
        (Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) := by
      rw [hKlE]; ring
    have hb6 : 3 * Cq * (M + V) * (Real.log X * Real.exp (-(N + 2) * Real.log X ^ (1 / 3 : ℝ))) ≤
        3 * Cq * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
      have h0 : (0:ℝ) ≤ 3 * Cq * (M + V) := by positivity
      exact mul_le_mul_of_nonneg_left habs h0
    have hb7 : 3 * Cq * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) ≤
        (3 * Cq + CL + 30) * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
      have h0 : (0:ℝ) ≤ (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by positivity
      have h1 : 3 * Cq ≤ 3 * Cq + CL + 30 := by linarith
      calc 3 * Cq * (M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))
          = 3 * Cq * ((M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) := by ring
        _ ≤ (3 * Cq + CL + 30) * ((M + V) * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_right h1 h0
        _ = _ := by ring
    linarith
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the first outer prime `p1` of the E2 sum, at stretched exponential
precision. -/
private theorem two_pair_first_prime_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, primeWeight b *
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ C * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨CH, hCH0, hH⟩ := two_pair_pnt_harmonic_exp (4 * N + 4) (by linarith) (1 / 20) (by norm_num)
  obtain ⟨K, CV, hV⟩ := two_pair_first_variation ω hω hz hε hε8
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 1
  set T : ℝ := max (max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)))
    (max (Real.exp 4) CL) with hTdef
  refine ⟨T + 8 * CH * (2 + |K|) + 4, fun x hx m hm1 hm2 => ?_⟩
  have hTA : max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) ≤ T := by
    rw [hTdef]; exact le_max_left _ _
  have hTB : max (Real.exp 4) CL ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hT1 : 4 * CH * (2 + |K|) * CL ≤ T :=
    (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hTA)
  have hT2 : CV ≤ T := by
    have h1 : CV ≤ max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) :=
      (le_max_right _ _).trans (le_max_left _ _)
    exact h1.trans hTA
  have hT3 : (2 : ℝ) ^ 40 ≤ T := by
    have h1 : (2 : ℝ) ^ 40 ≤ max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL) := le_max_left _ _
    have h2 : (2 : ℝ) ^ 40 ≤
        max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) :=
      h1.trans (le_max_right _ _)
    exact h2.trans hTA
  have hT4 : CH ^ 2 ≤ T := by
    have h1 : CH ^ 2 ≤ max (CH ^ 2) CL := le_max_left _ _
    have h2 : CH ^ 2 ≤ max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL) := h1.trans (le_max_right _ _)
    have h3 : CH ^ 2 ≤
        max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) :=
      h2.trans (le_max_right _ _)
    exact h3.trans hTA
  have hT5 : CL ≤ T := (le_max_right _ _).trans hTB
  have hT6 : Real.exp 4 ≤ T := (le_max_left _ _).trans hTB
  have hTx : T ≤ x := by
    have h0 : (0:ℝ) ≤ 8 * CH * (2 + |K|) := by
      have h1 : (0:ℝ) ≤ 2 + |K| := by positivity
      positivity
    linarith
  have hCle : 4 * CH * (2 + |K|) * CL ≤ x := le_trans hT1 hTx
  have hxCV : CV ≤ x := le_trans hT2 hTx
  have h40 : (2 : ℝ) ^ 40 ≤ x := le_trans hT3 hTx
  have hCH2 : CH ^ 2 ≤ x := le_trans hT4 hTx
  have hCLx : CL ≤ x := le_trans hT5 hTx
  have hexp4 : Real.exp 4 ≤ x := le_trans hT6 hTx
  obtain ⟨hY49, hCHX, ht2, htW, -, hlX1, hlX2⟩ :=
    two_pair_scale_facts (A := 1) hε hε8 (by norm_num) h40
      (by
        have h22 : (2:ℝ) ^ ((1:ℝ) + 1) = 4 := by norm_num
        rw [h22]; exact hexp4) hCH2
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hX1 : (1 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlog0 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_nonneg hX1
  have hlog1 : 1 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := by
    have h1 : (1:ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h3 : (2:ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
      linarith
    exact h1
  have hL0 : 0 < Real.log x := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
    exact Real.log_pos (by linarith)
  set E := Real.exp (-(N + 2) * Real.log x ^ (1 / 3 : ℝ)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set Ep := Real.exp (-(4 * N + 4) * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ)) with hEpdef
  have hEp0 : 0 < Ep := Real.exp_pos _
  have hEpE : Ep ≤ E := by
    rw [hEpdef, hEdef]
    apply Real.exp_le_exp.mpr
    have hlogx2 : Real.log x / 2 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := hlX1
    have hφ : (Real.log x / 2) ^ (1 / 3 : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hlogx2 (by norm_num)
    have hφ2 : Real.log x ^ (1 / 3 : ℝ) / 2 ≤ (Real.log x / 2) ^ (1 / 3 : ℝ) := by
      rw [Real.div_rpow hL0.le (by norm_num : (0:ℝ) ≤ 2)]
      have h1 : (2:ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
        calc (2:ℝ) ^ (1 / 3 : ℝ) ≤ (2:ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h2 : (0:ℝ) < (2:ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hL0.le _) h2 h1
    have hkey : (N + 2) * Real.log x ^ (1 / 3 : ℝ) ≤
        (4 * N + 4) * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ) := by
      have h1 : (0:ℝ) < Real.log x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hL0 _
      have h2 : (2:ℝ) * (Real.log x / 2) ^ (1 / 3 : ℝ) ≤
          2 * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ) := by linarith
      have h3 : Real.log x ^ (1 / 3 : ℝ) ≤ 2 * (Real.log x / 2) ^ (1 / 3 : ℝ) := by linarith
      nlinarith
    linarith
  have hB0 : 0 ≤ CH * (2 + |K|) * Ep := by
    have h1 : (0:ℝ) ≤ 2 + |K| := by positivity
    exact mul_nonneg (mul_nonneg hCH0 h1) hEp0.le
  have hpw : ∀ j ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, |primeWeight j| ≤ 2 := fun j _ => by
    unfold primeWeight
    split_ifs <;> norm_num
  have hTw : ∀ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
      |∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ CH * (2 + |K|) * Ep * (1 / (b : ℝ)) := by
    intro b hb
    have hb' := Finset.mem_Icc.mp hb
    have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb'.1
    by_cases hWb : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (b : ℝ)
    · have hb2 : 2 ≤ b := by
        have : (2 : ℝ) ≤ (b : ℝ) := by linarith
        exact_mod_cast this
      obtain ⟨hM, -, -⟩ := two_cofactor_density_props ω hω hz hb2
      have hcongr : ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) =
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              ((if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / (b : ℝ)
              else 0) / (a : ℝ)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b) <;>
          simp only [hE, ↓reduceIte] <;> ring
      rw [hcongr]
      have h := hH (2 * x ^ (11 / 20 + ε)) hCHX b ⌊2 * x ^ (11 / 20 + ε)⌋₊ hb'.2
        (by linarith) hNle
        (fun a : ℕ => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / (b : ℝ) else 0)
        (2 / (b : ℝ)) (K / (b : ℝ)) (by positivity)
        (fun a _ => by
          by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
          · simp only [hE, ↓reduceIte]
            rw [abs_div, abs_of_pos hb0]
            exact div_le_div_of_nonneg_right (hM _) hb0.le
          · simp only [hE, ↓reduceIte, abs_zero]
            positivity)
        (hV x hxCV m hm1 hm2 b hWb hb'.2)
      have heq : Real.exp (-(4 * N + 4) * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ)) = Ep :=
        hEpdef.symm
      rw [heq] at h
      refine h.trans ?_
      have e : CH * (2 / (b : ℝ) + K / (b : ℝ)) * Ep ≤ CH * (2 + |K|) * Ep * (1 / (b : ℝ)) := by
        have h1 : 2 / (b : ℝ) + K / (b : ℝ) ≤ (2 + |K|) * (1 / (b : ℝ)) := by
          have h2 : K ≤ |K| := le_abs_self K
          rw [mul_one_div, ← add_div]
          rw [div_le_div_iff_of_pos_right hb0]
          linarith
        calc CH * (2 / (b : ℝ) + K / (b : ℝ)) * Ep
            = CH * Ep * (2 / (b : ℝ) + K / (b : ℝ)) := by ring
          _ ≤ CH * Ep * ((2 + |K|) * (1 / (b : ℝ))) := by
              have h0 : (0:ℝ) ≤ CH * Ep := by positivity
              exact mul_le_mul_of_nonneg_left h1 h0
          _ = CH * (2 + |K|) * Ep * (1 / (b : ℝ)) := by ring
      exact e
    · rw [Finset.sum_eq_zero, abs_zero]
      · positivity
      · intro a _
        by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
        · exact absurd (two_pair_level_ge hε8 hY49 hb'.1 hE) hWb
        · simp [hE]
  have hout := two_pair_outer_sum ⌊2 * x ^ (11 / 20 + ε)⌋₊ primeWeight
    (fun b => ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (primeWeight a - 1 / Real.log (a : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)) hB0 hpw hTw
  refine hout.trans ?_
  have hb1 : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 4 * Real.log x := by
    have h1 : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) := hlogN
    have h2 : 1 + Real.log (2 * x ^ (11 / 20 + ε)) ≤ 2 * Real.log (2 * x ^ (11 / 20 + ε)) := by
      linarith
    have h3 : 2 * Real.log (2 * x ^ (11 / 20 + ε)) ≤ 4 * Real.log x := by linarith
    linarith
  have habs : Real.log x * E ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h := hLX x hCLx
    have he : (-(N + (1:ℕ) + 1) : ℝ) = -(N + 2) := by push_cast; ring
    rwa [pow_one, he] at h
  have hstep : 2 * (CH * (2 + |K|) * Ep) * (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ≤
      8 * CH * (2 + |K|) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h1 : 2 * (CH * (2 + |K|) * Ep) * (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ≤
        2 * (CH * (2 + |K|) * Ep) * (4 * Real.log x) := by
      have h2 : (0:ℝ) ≤ 2 * (CH * (2 + |K|) * Ep) := by positivity
      exact mul_le_mul_of_nonneg_left hb1 h2
    have h3 : 2 * (CH * (2 + |K|) * Ep) * (4 * Real.log x) =
        8 * CH * (2 + |K|) * (Real.log x * Ep) := by ring
    have h5 : (0:ℝ) ≤ 8 * CH * (2 + |K|) := by
      have h6 : (0:ℝ) ≤ 2 + |K| := by positivity
      positivity
    have h4 : 8 * CH * (2 + |K|) * (Real.log x * Ep) ≤
        8 * CH * (2 + |K|) * (Real.log x * E) := by
      have h6 : Real.log x * Ep ≤ Real.log x * E :=
        mul_le_mul_of_nonneg_left hEpE (by linarith)
      exact mul_le_mul_of_nonneg_left h6 h5
    have h7 : 8 * CH * (2 + |K|) * (Real.log x * E) ≤
        8 * CH * (2 + |K|) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left habs h5
    linarith
  refine hstep.trans ?_
  have hfin : 8 * CH * (2 + |K|) ≤ T + 8 * CH * (2 + |K|) + 4 := by linarith
  have h0 : (0:ℝ) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right hfin h0

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the second outer prime `p2` of the E2 sum, at stretched exponential
precision. -/
private theorem two_pair_second_prime_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ a ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / Real.log (a : ℝ) *
          ∑ b ∈ Finset.Ico 1 a,
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ C * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨CH, hCH0, hH⟩ := two_pair_pnt_harmonic_exp (4 * N + 4) (by linarith) (1 / 20) (by norm_num)
  obtain ⟨K, CV, hV⟩ := two_pair_second_variation ω hω hz hε hε8
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 1
  set T : ℝ := max (max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)))
    (max (Real.exp 4) CL) with hTdef
  refine ⟨T + 8 * CH * (2 + |K|) + 4, fun x hx m hm1 hm2 => ?_⟩
  have hTA : max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) ≤ T := by
    rw [hTdef]; exact le_max_left _ _
  have hTB : max (Real.exp 4) CL ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hT1 : 4 * CH * (2 + |K|) * CL ≤ T :=
    (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hTA)
  have hT2 : CV ≤ T := by
    have h1 : CV ≤ max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) :=
      (le_max_right _ _).trans (le_max_left _ _)
    exact h1.trans hTA
  have hT3 : (2 : ℝ) ^ 40 ≤ T := by
    have h1 : (2 : ℝ) ^ 40 ≤ max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL) := le_max_left _ _
    have h2 : (2 : ℝ) ^ 40 ≤
        max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) :=
      h1.trans (le_max_right _ _)
    exact h2.trans hTA
  have hT4 : CH ^ 2 ≤ T := by
    have h1 : CH ^ 2 ≤ max (CH ^ 2) CL := le_max_left _ _
    have h2 : CH ^ 2 ≤ max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL) := h1.trans (le_max_right _ _)
    have h3 : CH ^ 2 ≤
        max (max (4 * CH * (2 + |K|) * CL) CV) (max ((2 : ℝ) ^ 40) (max (CH ^ 2) CL)) :=
      h2.trans (le_max_right _ _)
    exact h3.trans hTA
  have hT5 : CL ≤ T := (le_max_right _ _).trans hTB
  have hT6 : Real.exp 4 ≤ T := (le_max_left _ _).trans hTB
  have hTx : T ≤ x := by
    have h0 : (0:ℝ) ≤ 8 * CH * (2 + |K|) := by
      have h1 : (0:ℝ) ≤ 2 + |K| := by positivity
      positivity
    linarith
  have hCle : 4 * CH * (2 + |K|) * CL ≤ x := le_trans hT1 hTx
  have hxCV : CV ≤ x := le_trans hT2 hTx
  have h40 : (2 : ℝ) ^ 40 ≤ x := le_trans hT3 hTx
  have hCH2 : CH ^ 2 ≤ x := le_trans hT4 hTx
  have hCLx : CL ≤ x := le_trans hT5 hTx
  have hexp4 : Real.exp 4 ≤ x := le_trans hT6 hTx
  obtain ⟨hY49, hCHX, ht2, htW, -, hlX1, hlX2⟩ :=
    two_pair_scale_facts (A := 1) hε hε8 (by norm_num) h40
      (by
        have h22 : (2:ℝ) ^ ((1:ℝ) + 1) = 4 := by norm_num
        rw [h22]; exact hexp4) hCH2
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hX1 : (1 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by linarith
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hL0 : 0 < Real.log x := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ 40 := by norm_num
    exact Real.log_pos (by linarith)
  set E := Real.exp (-(N + 2) * Real.log x ^ (1 / 3 : ℝ)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set Ep := Real.exp (-(4 * N + 4) * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ)) with hEpdef
  have hEp0 : 0 < Ep := Real.exp_pos _
  have hEpE : Ep ≤ E := by
    rw [hEpdef, hEdef]
    apply Real.exp_le_exp.mpr
    have hlogx2 : Real.log x / 2 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := hlX1
    have hφ : (Real.log x / 2) ^ (1 / 3 : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hlogx2 (by norm_num)
    have hφ2 : Real.log x ^ (1 / 3 : ℝ) / 2 ≤ (Real.log x / 2) ^ (1 / 3 : ℝ) := by
      rw [Real.div_rpow hL0.le (by norm_num : (0:ℝ) ≤ 2)]
      have h1 : (2:ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
        calc (2:ℝ) ^ (1 / 3 : ℝ) ≤ (2:ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h2 : (0:ℝ) < (2:ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hL0.le _) h2 h1
    have hkey : (N + 2) * Real.log x ^ (1 / 3 : ℝ) ≤
        (4 * N + 4) * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ) := by
      have h1 : (0:ℝ) < Real.log x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hL0 _
      nlinarith
    linarith
  have hB0 : 0 ≤ CH * (2 + |K|) * Ep := by
    have h1 : (0:ℝ) ≤ 2 + |K| := by positivity
    exact mul_nonneg (mul_nonneg hCH0 h1) hEp0.le
  have hlw : ∀ j ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, |1 / Real.log (j : ℝ)| ≤ 2 := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    rcases hj1.eq_or_lt with h1 | h2
    · rw [← h1]; simp
    · have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
      have hlj : (1 / 2 : ℝ) < Real.log (j : ℝ) := by
        have h3 := Real.log_two_gt_d9
        have h4 := Real.log_le_log (by norm_num) hj2
        linarith
      rw [abs_of_pos (by positivity), div_le_iff₀ (by linarith)]
      linarith
  have hWpos : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by linarith
  have hceil1 : 1 ≤ ⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ := Nat.ceil_pos.mpr hWpos
  have hLcast : (2 * x ^ (11 / 20 + ε)) ^ (1 / 20 : ℝ) ≤
      ((⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hceil1, Nat.cast_one]
    have := Nat.le_ceil ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ))
    linarith
  have hzero : ∀ a b : ℕ, 1 ≤ b → b ≤ ⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1 →
      (primeWeight b - 1 / Real.log (b : ℝ)) *
        (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
        else 0) = 0 := by
    intro a b hb1 hbL
    have hlt : (b : ℝ) < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
      Nat.lt_ceil.mp (by omega)
    by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
    · exact absurd (two_pair_level_ge hε8 hY49 hb1 hE) (not_le.mpr hlt)
    · simp [hE]
  have hTw : ∀ a ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
      |∑ b ∈ Finset.Ico 1 a,
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)| ≤ CH * (2 + |K|) * Ep * (1 / (a : ℝ)) := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha'.1
    have hIco : Finset.Ico 1 a = Finset.Ioc 0 (a - 1) := by
      ext b
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hIco]
    by_cases hc : ⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1 ≤ a - 1
    · rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hc,
        Finset.sum_eq_zero (fun b hb => hzero a b (Finset.mem_Ioc.mp hb).1
          (Finset.mem_Ioc.mp hb).2), zero_add]
      have hcongr : ∑ b ∈ Finset.Ioc (⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1) (a - 1),
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) =
          ∑ b ∈ Finset.Ioc (⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1) (a - 1),
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              ((if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / (a : ℝ)
              else 0) / (b : ℝ)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b) <;>
          simp only [hE, ↓reduceIte] <;> ring
      rw [hcongr]
      have haX : ((a - 1 : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
        have h1 : ((a - 1 : ℕ) : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr (Nat.sub_le a 1)
        have h2 : (a : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Nat.cast_le.mpr ha'.2
        linarith
      have h := hH (2 * x ^ (11 / 20 + ε)) hCHX
        (⌈(2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)⌉₊ - 1) (a - 1) hc hLcast haX
        (fun b : ℕ => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
          ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
            Real.log (b : ℝ) / (a : ℝ) else 0)
        (2 / (a : ℝ)) (K / (a : ℝ)) (by positivity)
        (fun b hb => by
          have hb' := Finset.mem_Ioc.mp hb
          have hbW : (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (b : ℝ) :=
            Nat.ceil_le.mp (by omega)
          have hb2 : 2 ≤ b := by
            have : (2 : ℝ) ≤ (b : ℝ) := by linarith
            exact_mod_cast this
          obtain ⟨hM, -, -⟩ := two_cofactor_density_props ω hω hz hb2
          by_cases hE : lowerTwoDiscarded ε (expo ε x a) (expo ε x b)
          · simp only [hE, ↓reduceIte]
            rw [abs_div, abs_of_pos ha0]
            exact div_le_div_of_nonneg_right (hM _) ha0.le
          · simp only [hE, ↓reduceIte, abs_zero]
            positivity)
        (hV x hxCV m hm1 hm2 a ha'.1 ha'.2 _ hLcast)
      have heq : Real.exp (-(4 * N + 4) * Real.log (2 * x ^ (11 / 20 + ε)) ^ (1 / 3 : ℝ)) = Ep :=
        hEpdef.symm
      rw [heq] at h
      refine h.trans ?_
      have e : CH * (2 / (a : ℝ) + K / (a : ℝ)) * Ep ≤
          CH * (2 + |K|) * Ep * (1 / (a : ℝ)) := by
        have h1 : 2 / (a : ℝ) + K / (a : ℝ) ≤ (2 + |K|) * (1 / (a : ℝ)) := by
          have h2 : K ≤ |K| := le_abs_self K
          rw [mul_one_div, ← add_div]
          rw [div_le_div_iff_of_pos_right ha0]
          linarith
        calc CH * (2 / (a : ℝ) + K / (a : ℝ)) * Ep
            = CH * Ep * (2 / (a : ℝ) + K / (a : ℝ)) := by ring
          _ ≤ CH * Ep * ((2 + |K|) * (1 / (a : ℝ))) := by
              have h0 : (0:ℝ) ≤ CH * Ep := by positivity
              exact mul_le_mul_of_nonneg_left h1 h0
          _ = CH * (2 + |K|) * Ep * (1 / (a : ℝ)) := by ring
      exact e
    · rw [Finset.sum_eq_zero, abs_zero]
      · positivity
      · intro b hb
        have hb' := Finset.mem_Ioc.mp hb
        exact hzero a b hb'.1 (by omega)
  have hout := two_pair_outer_sum ⌊2 * x ^ (11 / 20 + ε)⌋₊ (fun a => 1 / Real.log (a : ℝ))
    (fun a => ∑ b ∈ Finset.Ico 1 a,
            (primeWeight b - 1 / Real.log (b : ℝ)) *
              (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0)) hB0 hlw hTw
  refine hout.trans ?_
  have hlog1 : 1 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h2' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hb1 : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 4 * Real.log x := by
    have h1 : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) := hlogN
    have h2 : 1 + Real.log (2 * x ^ (11 / 20 + ε)) ≤ 2 * Real.log (2 * x ^ (11 / 20 + ε)) := by
      linarith
    have h3 : 2 * Real.log (2 * x ^ (11 / 20 + ε)) ≤ 4 * Real.log x := by linarith
    linarith
  have habs : Real.log x * E ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h := hLX x hCLx
    have he : (-(N + (1:ℕ) + 1) : ℝ) = -(N + 2) := by push_cast; ring
    rwa [pow_one, he] at h
  have hstep : 2 * (CH * (2 + |K|) * Ep) * (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ≤
      8 * CH * (2 + |K|) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h1 : 2 * (CH * (2 + |K|) * Ep) * (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ≤
        2 * (CH * (2 + |K|) * Ep) * (4 * Real.log x) := by
      have h2 : (0:ℝ) ≤ 2 * (CH * (2 + |K|) * Ep) := by positivity
      exact mul_le_mul_of_nonneg_left hb1 h2
    have h3 : 2 * (CH * (2 + |K|) * Ep) * (4 * Real.log x) =
        8 * CH * (2 + |K|) * (Real.log x * Ep) := by ring
    have h5 : (0:ℝ) ≤ 8 * CH * (2 + |K|) := by
      have h6 : (0:ℝ) ≤ 2 + |K| := by positivity
      positivity
    have h4 : 8 * CH * (2 + |K|) * (Real.log x * Ep) ≤
        8 * CH * (2 + |K|) * (Real.log x * E) := by
      have h6 : Real.log x * Ep ≤ Real.log x * E :=
        mul_le_mul_of_nonneg_left hEpE (by linarith)
      exact mul_le_mul_of_nonneg_left h6 h5
    have h7 : 8 * CH * (2 + |K|) * (Real.log x * E) ≤
        8 * CH * (2 + |K|) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left habs h5
    linarith
  refine hstep.trans ?_
  have hfin : 8 * CH * (2 + |K|) ≤ T + 8 * CH * (2 + |K|) + 4 := by linarith
  have h0 : (0:ℝ) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right hfin h0


set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17, the E2 sum at one point `m` of J, the passage from the sum over the
second outer variable to the integral, at stretched exponential precision. -/
private theorem two_pair_riemann_first_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)| ≤
        C * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  refine ⟨Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) + (2:ℝ) ^ 40 + 4,
    fun x hx m hm1 hm2 => ?_⟩
  have hXe : Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) ≤ x := by
    have h1 : (0:ℝ) ≤ (2:ℝ) ^ 40 + 4 := by positivity
    linarith
  have h40 : (2:ℝ) ^ 40 ≤ x := by
    have h1 : (0:ℝ) ≤ Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) := (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (4:ℝ) := by norm_num
    nlinarith
  have hx1 : (1:ℝ) ≤ x := le_trans (by norm_num) h40
  have hx0 : (0:ℝ) < x := by linarith
  have hexp4 : Real.exp 4 ≤ x := by
    have h1 : Real.exp 1 ≤ 3 := by
      have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      linarith
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 ^ 4 ≤ (3:ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
    have h4 : (3:ℝ) ^ 4 ≤ (2:ℝ) ^ 40 := by norm_num
    linarith
  obtain ⟨hY49, -, -, -, -, hlX1, hlx2⟩ :=
    two_pair_scale_facts (A := 1) hε hε8 (by norm_num) h40
      (by
        have h22 : (2:ℝ) ^ ((1:ℝ) + 1) = 4 := by norm_num
        rw [h22]; exact hexp4) (by nlinarith : (1:ℝ) ^ 2 ≤ x)
  have hy4 : (4:ℝ) ≤ x ^ (11/20 + ε) := le_trans (by norm_num) hY49
  have hy0 : (0:ℝ) < x ^ (11/20 + ε) := by linarith
  have hZ1 : 1 < scaleZ ε x := (scaleZ_rpow_ge hε hε8 hx1).2
  have hZ0 : (0:ℝ) < scaleZ ε x := by linarith
  have hY20 : (2:ℝ) ^ 20 ≤ x ^ (11/20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    rw [show ((2:ℝ) ^ 20) ^ 2 = (2:ℝ) ^ 40 by norm_num]
    exact h40
  have hZbig : (1048576:ℝ) ≤ scaleZ ε x := by
    unfold scaleZ shortY
    nlinarith [hY20]
  have hZlevel : (4:ℝ) ≤ (scaleZ ε x) ^ (12499/100000:ℝ) := rpow_level_ge_four hZbig
  have hz0x : x ^ (11/200:ℝ) ≤ (scaleZ ε x) ^ (12499/100000:ℝ) := by
    have hp : (11/200:ℝ) ≤ (11:ℝ)/20 * (12499/100000) := by norm_num
    have h1 : x ^ (11/200:ℝ) ≤ x ^ ((11:ℝ)/20 * (12499/100000)) :=
      Real.rpow_le_rpow_of_exponent_le hx1 hp
    have h2 : x ^ ((11:ℝ)/20 * (12499/100000)) =
        (x ^ ((11:ℝ)/20)) ^ (12499/100000:ℝ) := by
      rw [Real.rpow_mul (le_of_lt hx0)]
    have hbase : x ^ ((11:ℝ)/20) ≤ scaleZ ε x := by
      have hshort : x ^ ((11:ℝ)/20) ≤ x ^ (11/20 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      unfold scaleZ shortY
      nlinarith [hshort]
    have h3 : (x ^ ((11:ℝ)/20)) ^ (12499/100000:ℝ) ≤ (scaleZ ε x) ^ (12499/100000:ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hx0) _) hbase (by norm_num)
    rw [h2] at h1
    exact h1.trans h3
  have hYsq : (2:ℝ) ≤ (x ^ (11/20 + ε)) ^ (1/2:ℝ) := by
    have h := Real.sqrt_le_sqrt hy4
    have h4 : Real.sqrt 4 = (2:ℝ) := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4, Real.sqrt_eq_rpow] at h
    exact h
  have hYsq0 : (0:ℝ) ≤ (x ^ (11/20 + ε)) ^ (1/2:ℝ) := by positivity
  have hYsqsq : ((x ^ (11/20 + ε)) ^ (1/2:ℝ)) ^ 2 = x ^ (11/20 + ε) := by
    rw [pow_two, ← Real.rpow_add (by linarith)]
    norm_num
  have hZs : (scaleZ ε x) ^ (1/2:ℝ) = 2 * (x ^ (11/20 + ε)) ^ (1/2:ℝ) := by
    unfold scaleZ shortY
    rw [Real.mul_rpow (x := (4:ℝ)) (y := x ^ (11/20 + ε)) (z := (1/2:ℝ)) (by norm_num) (le_of_lt hy0)]
    have h4 : (4:ℝ) ^ (1/2:ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
  have hZB : (scaleZ ε x) ^ (1/2:ℝ) ≤ ((⌊2 * x ^ (11/20 + ε)⌋₊ : ℕ) : ℝ) := by
    rw [hZs]
    have hmain : 2 * (x ^ (11/20 + ε)) ^ (1/2:ℝ) ≤ 2 * x ^ (11/20 + ε) - 1 := by
      nlinarith [hYsq, hYsq0, hYsqsq, hy4]
    have hfloor : 2 * x ^ (11/20 + ε) - 1 ≤ ((⌊2 * x ^ (11/20 + ε)⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (2 * x ^ (11/20 + ε))
      linarith
    linarith
  have hB1 : 1 ≤ ⌊2 * x ^ (11/20 + ε)⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    nlinarith [hy4]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ b ∈ Finset.Icc 1 ⌊2 * x ^ (11/20 + ε)⌋₊,
      |(∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11/20 + ε)⌋₊,
          (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
              ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
            else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)|
      ≤ (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
            100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
    intro b hb
    exact two_pair_term_bound (ω := ω) hω hz hε hε8 hZ1 hZbig (by omega : 0 < m)
      (Finset.mem_Icc.mp hb).2 hZB
  refine (Finset.sum_le_sum hpt).trans ?_
  have hIcc : (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11/20 + ε)⌋₊,
      (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
        (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
          100 / ((b:ℝ) * Real.log (b : ℝ)) else 0))
      = ∑ b ∈ Finset.Ioc 1 ⌊2 * x ^ (11/20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (b:ℝ) then
            100 / ((b:ℝ) * Real.log (b:ℝ)) else 0) := by
    rw [Finset.Icc_eq_cons_Ioc hB1, Finset.sum_cons]
    have h1 : (1 / (((1:ℕ) : ℝ) * Real.log (((1:ℕ) : ℝ)) ^ 2)) *
        (if (scaleZ ε x) ^ (12499/100000:ℝ) ≤ (((1:ℕ) : ℝ)) then
          100 / ((((1:ℕ) : ℝ)) * Real.log (((1:ℕ) : ℝ))) else 0) = 0 := by
      simp
    rw [h1, zero_add]
  rw [hIcc]
  have hW := two_pair_weight_sum (x := x) (z0 := (scaleZ ε x) ^ (12499/100000:ℝ))
      (by linarith) hZlevel hz0x (B := ⌊2 * x ^ (11/20 + ε)⌋₊)
  refine hW.trans ?_
  -- the power saving beats the stretched exponential
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : (0:ℝ) ≤ Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) := (Real.exp_pos _).le
    linarith
  have hLbig : (N / (11/200) + 1) ^ 3 ≤ Real.log x := by
    have h1 : max 2 ((N / (11/200) + 1) ^ 3 + 1) ≤ Real.log x := by
      rw [← Real.log_exp (max 2 ((N / (11/200) + 1) ^ 3 + 1))]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have h2 : (N / (11/200) + 1) ^ 3 ≤ max 2 ((N / (11/200) + 1) ^ 3 + 1) := by
      have h3 : (N / (11/200) + 1) ^ 3 + 1 ≤ max 2 ((N / (11/200) + 1) ^ 3 + 1) :=
        le_max_right _ _
      linarith
    linarith
  have hpow : x ^ (-(11/200:ℝ)) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h1 : x ^ (-(11/200:ℝ)) = Real.exp (-(11/200) * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0]
      ring_nf
    have h3 : (N / (11/200) + 1) ≤ Real.log x ^ (1 / 3 : ℝ) := by
      have h4 : ((N / (11/200) + 1) ^ 3) ^ (1 / 3 : ℝ) ≤ Real.log x ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hLbig (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ N / (11/200) + 1),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h4
      exact h4
    have h2 : -(11/200) * Real.log x ≤ -N * Real.log x ^ (1 / 3 : ℝ) := by
      have h6 : N * Real.log x ^ (1 / 3 : ℝ) ≤ (11/200) * Real.log x := by
        have hsup : Real.log x ^ (1 / 3 : ℝ) * (N / (11/200) + 1) ≤ Real.log x := by
          have h7 : Real.log x ^ (1 / 3 : ℝ) * Real.log x ^ (1 / 3 : ℝ) ≤ Real.log x := by
            have h8 : Real.log x ^ (1 / 3 : ℝ) * Real.log x ^ (1 / 3 : ℝ) =
                Real.log x ^ (2 / 3 : ℝ) := by
              rw [← Real.rpow_add (by linarith)]; norm_num
            rw [h8]
            calc Real.log x ^ (2 / 3 : ℝ) ≤ Real.log x ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
              _ = Real.log x := Real.rpow_one _
          nlinarith
        have h9 : (11/200) * (Real.log x ^ (1 / 3 : ℝ) * (N / (11/200) + 1)) ≤
            (11/200) * Real.log x := by
          exact mul_le_mul_of_nonneg_left hsup (by norm_num)
        have h10 : (11/200) * (Real.log x ^ (1 / 3 : ℝ) * (N / (11/200) + 1)) =
            N * Real.log x ^ (1 / 3 : ℝ) + (11/200) * Real.log x ^ (1 / 3 : ℝ) := by
          field_simp
        have h11 : (0:ℝ) ≤ (11/200) * Real.log x ^ (1 / 3 : ℝ) := by positivity
        linarith
      linarith
    rw [h1]
    exact Real.exp_le_exp.mpr h2
  have hlog3 : (0:ℝ) < Real.log x ^ 3 := by positivity
  have hinv : 1 / Real.log x ^ 3 ≤ 1 := by
    rw [div_le_one hlog3]
    have h1 : Real.log x * Real.log x ≥ 1 := by nlinarith
    have h2 : Real.log x * Real.log x * Real.log x ≥ 1 := by nlinarith
    calc (1:ℝ) ≤ Real.log x * Real.log x * Real.log x := h2
      _ = Real.log x ^ 3 := by ring
  have hprod : x ^ (-(11/200:ℝ)) * (1 / Real.log x ^ 3) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    calc x ^ (-(11/200:ℝ)) * (1 / Real.log x ^ 3)
        ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) * 1 :=
          mul_le_mul hpow hinv (by positivity) (Real.exp_pos _).le
      _ = _ := by ring
  calc 20000000 * x ^ (-(11/200:ℝ)) / Real.log x ^ 3
      = 20000000 * (x ^ (-(11/200:ℝ)) * (1 / Real.log x ^ 3)) := by ring
    _ ≤ 20000000 * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ (Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) + (2:ℝ) ^ 40 + 4) *
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
        have h0 : (0:ℝ) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
        have h1 : (20000000 : ℝ) ≤
            Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) + (2:ℝ) ^ 40 + 4 := by
          have h2 : (0:ℝ) ≤ Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) := (Real.exp_pos _).le
          have h3 : (1:ℝ) ≤ (2:ℝ) ^ 40 := by norm_num
          linarith
        calc 20000000 * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))
            = 20000000 * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := rfl
          _ ≤ (Real.exp (max 2 ((N / (11/200) + 1) ^ 3 + 1)) + (2:ℝ) ^ 40 + 4) *
              Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 h0
set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17, the E2 sum at one point `m` of J, the passage from the sum over the
first outer variable to the integral, at stretched exponential precision. -/
private theorem two_pair_riemann_second_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (∫ α in (1/10:ℝ)..(1/2:ℝ),
            if lowerTwoDiscarded ε α (expo ε x b) then
              ω ((Real.log m / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
            else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 1
  refine ⟨Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) + (2:ℝ)^40 + CL + 8,
    fun x hx m hm1 hm2 => ?_⟩
  have hXe : Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) ≤ x := by
    have h1 : (0:ℝ) ≤ (2:ℝ)^40 + CL + 8 := by positivity
    linarith
  have hx40 : (2:ℝ)^40 ≤ x := by
    have h1 : (0:ℝ) ≤ Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) := (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ CL + 8 := by positivity
    linarith
  have hxCL : CL ≤ x := by
    have h1 : (0:ℝ) ≤ Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) := (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (2:ℝ)^40 := by positivity
    linarith
  have hexp4 : Real.exp 4 ≤ x := by
    have h1 : Real.exp 1 ≤ 3 := by
      have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      linarith
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 ^ 4 ≤ (3:ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
    have h4 : (3:ℝ) ^ 4 ≤ (2:ℝ) ^ 40 := by norm_num
    linarith
  obtain ⟨hY49, -, -, -, hl, hlX1, hlX2⟩ :=
    two_pair_scale_facts (A := 1) hε hε8 (by norm_num) hx40
      (by
        have h22 : (2:ℝ) ^ ((1:ℝ) + 1) = 4 := by norm_num
        rw [h22]; exact hexp4) (by nlinarith [hx40] : (0:ℝ) ^ 2 ≤ x)
  have hx1 : (1:ℝ) ≤ x := le_trans (by norm_num) hx40
  have hx0 : (0:ℝ) < x := by linarith
  have hY4 : (4:ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hY0 : (0:ℝ) < x ^ (11 / 20 + ε) := by linarith
  have hZval : scaleZ ε x = 4 * x ^ (11 / 20 + ε) := rfl
  have hZ4 : (4:ℝ) ≤ scaleZ ε x := by rw [hZval]; linarith
  have hZbig : (2:ℝ)^20 ≤ scaleZ ε x := by
    rw [hZval]; nlinarith [hY49]
  have hZ1 : 1 < scaleZ ε x := by linarith
  have hZ0 : (0:ℝ) < scaleZ ε x := by linarith
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos hZ1
  have hmR : (0:ℝ) < (m:ℝ) := by
    have h : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hm1
    exact_mod_cast h
  have hmGt : x ^ (11 / 20 + ε) < (m:ℝ) := by
    have h3 : x ^ (11 / 20 + ε) < (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
      exact_mod_cast this
    have h4 : (⌊x ^ (11 / 20 + ε)⌋₊ : ℝ) + 1 ≤ (m:ℝ) := by
      have h5 : ⌊x ^ (11 / 20 + ε)⌋₊ + 1 ≤ m := hm1
      exact_mod_cast h5
    linarith
  have hmLe : (m:ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
    have h2 : (m:ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hm2
    have h3 : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by positivity)
    linarith
  -- the exponent `s = log m / log Z`
  have hs0 : (1/2:ℝ) ≤ Real.log (m:ℝ) / Real.log (scaleZ ε x) := by
    rw [le_div_iff₀ hLZ]
    have h1 : Real.log (x ^ (11 / 20 + ε)) ≤ Real.log (m:ℝ) :=
      Real.log_le_log hY0 (le_of_lt hmGt)
    have h2 : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
      rw [hZval, Real.log_mul (by norm_num) (ne_of_gt hY0)]
    have h4 : Real.log 4 ≤ Real.log (x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by norm_num) hY4
    rw [h2]
    linarith
  have hs1 : Real.log (m:ℝ) / Real.log (scaleZ ε x) ≤ 1 := by
    rw [div_le_iff₀ hLZ]
    have h1 : Real.log (m:ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
      Real.log_le_log (by linarith) hmLe
    have h2 : Real.log (2 * x ^ (11 / 20 + ε)) ≤ Real.log (scaleZ ε x) := by
      apply Real.log_le_log (by linarith)
      rw [hZval]; linarith
    linarith
  -- the inner `α`-integrals are integrable
  have hαInt : ∀ b : ℕ, IntervalIntegrable
      (fun α : ℝ => if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) volume (1/10) (1/2) := by
    intro b
    have hmeas : Measurable (fun α : ℝ => if lowerTwoDiscarded ε α (expo ε x b) then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
        else 0) := by
      have hωm : Measurable ω := measurable_buchstab_new hω hz
      have hs1' : MeasurableSet {α : ℝ | lowerTwoDiscarded ε α (expo ε x b)} := by
        unfold lowerTwoDiscarded upperPairRegion
        measurability
      have hf : Measurable (fun α : ℝ =>
          ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α) := by
        measurability
      exact Measurable.ite hs1' hf measurable_const
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)]
    refine MeasureTheory.Integrable.of_bound hmeas.aestronglyMeasurable.restrict 10 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
    have ha1 : (1/10:ℝ) ≤ a := le_of_lt ha.1
    rw [Real.norm_eq_abs]
    exact phi_abs_le hω hz (ε := ε) (Z := scaleZ ε x) (s := Real.log (m:ℝ) / Real.log (scaleZ ε x))
      (α := a) (β := expo ε x b) ha1
  -- the sum over `b` and the `α`-integral commute
  have hexch : (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (∫ α in (1/10:ℝ)..(1/2:ℝ),
          if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) =
      ∫ α in (1/10:ℝ)..(1/2:ℝ), ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0) := by
    have hpt : ∀ b : ℕ, (∫ α in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0)) / ((b : ℝ) * Real.log (b : ℝ) ^ 2) =
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) * (∫ α in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε α (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α
          else 0)) := fun b => by ring
    simp_rw [hpt, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_finset_sum (fun b _ => (hαInt b).const_mul _)]
  -- the truncation of the `b`-sum to `(B0, B1]`
  set B0 : ℕ := ⌊(scaleZ ε x)^(1/10:ℝ)⌋₊ with hB0
  set B1 : ℕ := ⌊(scaleZ ε x)^(1/2:ℝ)⌋₊ with hB1
  have hZpow20 : (2:ℝ) ≤ (scaleZ ε x)^(1/20:ℝ) := by
    have h1 : ((2:ℝ)^20)^(1/20:ℝ) ≤ (scaleZ ε x)^(1/20:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/20:ℝ) = 2 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    linarith
  have hpow4 : (4:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) := by
    have h1 : ((2:ℝ)^20)^(1/10:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) :=
      Real.rpow_le_rpow (by positivity) hZbig (by norm_num)
    have h2 : ((2:ℝ)^20)^(1/10:ℝ) = 4 := by
      rw [← Real.rpow_natCast (2:ℝ) 20, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    linarith
  have hB0ge : 4 ≤ B0 := by
    rw [hB0]; exact Nat.le_floor (by push_cast; linarith)
  have hB0R4 : (4:ℝ) ≤ (B0:ℝ) := by exact_mod_cast hB0ge
  have hB0le : ((B0:ℝ)) ≤ (scaleZ ε x)^(1/10:ℝ) := Nat.floor_le (by positivity)
  have hB1le : ((B1:ℝ)) ≤ (scaleZ ε x)^(1/2:ℝ) := Nat.floor_le (by positivity)
  have hB0B1 : B0 ≤ B1 := by
    have h1 : (B0:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) := hB0le
    have h2 : (scaleZ ε x)^(1/10:ℝ) ≤ (scaleZ ε x)^(1/2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num)
    rw [hB1]
    exact Nat.le_floor (le_trans h1 h2)
  have hB1N : B1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := by
    apply Nat.le_floor
    push_cast
    have hB1z : (B1:ℝ) ≤ (scaleZ ε x)^(1/2:ℝ) := hB1le
    have h4 : (4:ℝ)^(1/2:ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow, show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hZval, Real.mul_rpow (by norm_num) (le_of_lt hY0), h4] at hB1z
    have hYh : (x ^ (11/20 + ε))^(1/2:ℝ) ≤ x ^ (11/20 + ε) := by
      have h1 : (x ^ (11/20 + ε))^(1/2:ℝ) ≤ (x ^ (11/20 + ε))^(1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      rwa [Real.rpow_one] at h1
    linarith
  -- each summand outside `(B0, B1]` vanishes
  have htrunc : ∀ a : ℝ, 1/10 ≤ a → a ≤ 1/2 →
      (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) =
      ∑ b ∈ Finset.Ioc B0 B1,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0) := by
    intro a ha1 ha2
    refine (Finset.sum_subset ?_ ?_).symm
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hb
      exact Finset.mem_Icc.mpr ⟨by omega, le_trans hb2 hB1N⟩
    · intro b hb hnb
      simp only [Finset.mem_Icc] at hb
      simp only [Finset.mem_Ioc, not_and, not_lt] at hnb
      have hb1 : 1 ≤ b := hb.1
      have hbR1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb1
      have hlogb : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg hbR1
      have hcase : b ≤ B0 ∨ B1 < b := by
        by_contra hc
        push_neg at hc
        exact hnb hc.1 hc.2
      rcases hcase with hble | hbgt
      · have hβ : Real.log (b:ℝ) / Real.log (scaleZ ε x) ≤ 1/10 := by
          rw [div_le_iff₀ hLZ]
          have h1 : Real.log (b:ℝ) ≤ Real.log (B0:ℝ) := by
            rcases Nat.eq_zero_or_pos b with h0 | hpos
            · omega
            · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hble)
          have h2 : Real.log (B0:ℝ) ≤ Real.log ((scaleZ ε x)^(1/10:ℝ)) :=
            Real.log_le_log (by linarith) hB0le
          rw [Real.log_rpow hZ0] at h2
          linarith
        have := second_passage_summand_zero (ω := ω) hω
          (x := x) (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) (ε := ε) hZ1 hε8
          (α := a) ha1 ha2 (b := b) (Or.inl hβ)
        exact this
      · have hβ : 1/2 < Real.log (b:ℝ) / Real.log (scaleZ ε x) := by
          rw [lt_div_iff₀ hLZ]
          have h1 : Real.log ((scaleZ ε x)^(1/2:ℝ)) < Real.log (b:ℝ) := by
            apply Real.log_lt_log (Real.rpow_pos_of_pos hZ0 _)
            have h3 : (B1:ℝ) + 1 ≤ (b:ℝ) := by
              have : B1 + 1 ≤ b := by omega
              exact_mod_cast this
            have hZlt : (scaleZ ε x)^(1/2:ℝ) < (B1:ℝ) + 1 := by
              rw [hB1]
              exact Nat.lt_floor_add_one _
            linarith
          rw [Real.log_rpow hZ0] at h1
          linarith
        have := second_passage_summand_zero (ω := ω) hω
          (x := x) (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) (ε := ε) hZ1 hε8
          (α := a) ha1 ha2 (b := b) (Or.inr hβ)
        exact this
  -- integrability of the two functions of `α`
  have hGbound : ∀ a : ℝ, 1/10 ≤ a → |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0))| ≤
      10 * (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
    intro a ha
    have hstep : ∀ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        |(1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)| ≤ 10 * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
      intro b hb
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hlogb : 0 ≤ Real.log (b:ℝ) := Real.log_nonneg (by exact_mod_cast hb1)
      have hw : 0 ≤ 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2) := by
        rcases eq_or_lt_of_le hb1 with h | h
        · simp [← h]
        · have h1 : (1:ℝ) < (b:ℝ) := by exact_mod_cast h
          have h2 : 0 < Real.log (b:ℝ) := Real.log_pos h1
          positivity
      have hone : |(if lowerTwoDiscarded ε a (expo ε x b) then
          ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)| ≤ 10 :=
        phi_abs_le hω hz (ε := ε) (Z := scaleZ ε x)
          (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) (α := a) (β := expo ε x b) ha
      calc |(1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            (if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0)|
          = (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            |(if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0)| := by rw [abs_mul, abs_of_nonneg hw]
        _ ≤ (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) * 10 := mul_le_mul_of_nonneg_left hone hw
        _ = 10 * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by ring
    calc |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            (if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0))|
        ≤ ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          |(1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
            (if lowerTwoDiscarded ε a (expo ε x b) then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
            else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 10 * (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) :=
          Finset.sum_le_sum hstep
      _ = 10 * (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
  have hGmeas : Measurable (fun a : ℝ => ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) := by
    have hωm : Measurable ω := measurable_buchstab_new hω hz
    apply Finset.measurable_sum
    intro b hb
    apply Measurable.mul measurable_const
    have hs1' : MeasurableSet {α : ℝ | lowerTwoDiscarded ε α (expo ε x b)} := by
      unfold lowerTwoDiscarded upperPairRegion
      measurability
    have hf : Measurable (fun α : ℝ =>
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - α - expo ε x b) / expo ε x b) / α) := by
      measurability
    exact Measurable.ite hs1' hf measurable_const
  have hGint : IntervalIntegrable (fun a : ℝ => ∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) volume (1/10) (1/2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)]
    refine MeasureTheory.Integrable.of_bound hGmeas.aestronglyMeasurable.restrict
      (10 * (∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊, 1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with aa haa
    rw [Real.norm_eq_abs]
    exact hGbound aa (le_of_lt haa.1)
  have hdens : lowerTwoDensityAt ω ε (Real.log (m:ℝ) / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) =
      ∫ a in (1/10:ℝ)..(1/2:ℝ), (1 / Real.log (scaleZ ε x)) *
        (∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)) := by
    unfold lowerTwoDensityAt
    rw [div_eq_inv_mul, ← intervalIntegral.integral_const_mul]
    simp only [one_div]
  -- the inner `β`-integral is integrable and bounded by `400`
  have hβb : ∀ a : ℝ, 1/10 ≤ a → |∫ β in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a β then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)| ≤ 400 := by
    intro a ha
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1/10:ℝ)) (b := (1/2:ℝ)) (C := 1000)
      (f := fun β : ℝ => if lowerTwoDiscarded ε a β then
        ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)
      (by
        intro b hb
        rw [Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)] at hb
        rw [Real.norm_eq_abs]
        by_cases hD : lowerTwoDiscarded ε a b
        · rw [if_pos hD, abs_div]
          have ha0 : (0:ℝ) < a := by linarith
          have hb0 : (0:ℝ) < b := by linarith [hb.1]
          have hnum : |ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - b) / b)| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith [Decomp514a.two_density_buchstab_nonneg hω hz ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - b) / b)],
              LeanLab.ChenDoubleSieve.Wu04Functional.extended_buchstab_le_one hω hz _⟩
          have hden : (1/1000:ℝ) ≤ a * b^2 := by nlinarith [ha, hb.1, ha0, hb0]
          rw [abs_of_pos (by positivity : (0:ℝ) < a * b^2)]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < a * b^2)]
          nlinarith [hnum]
        · rw [if_neg hD, abs_zero]; norm_num)
    rw [Real.norm_eq_abs] at hbnd
    refine hbnd.trans ?_
    norm_num
  have hDint : IntervalIntegrable (fun a : ℝ => (1 / Real.log (scaleZ ε x)) *
      (∫ β in (1/10:ℝ)..(1/2:ℝ),
        (if lowerTwoDiscarded ε a β then
          ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)))
      volume (1/10) (1/2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (1/10:ℝ) ≤ 1/2)]
    refine MeasureTheory.Integrable.of_bound ?_ 400 ?_
    ·
      -- measurability of the inner integral as a function of `α`
      have h2m : Measurable (fun p : ℝ × ℝ =>
            if lowerTwoDiscarded ε p.1 p.2 then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - p.1 - p.2) / p.2) / (p.1 * p.2 ^ 2)
            else 0) := by
        have hωm : Measurable ω := measurable_buchstab_new hω hz
        have hs1' : MeasurableSet {p : ℝ × ℝ | lowerTwoDiscarded ε p.1 p.2} := by
          unfold lowerTwoDiscarded upperPairRegion
          measurability
        have hf : Measurable (fun p : ℝ × ℝ =>
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - p.1 - p.2) / p.2) / (p.1 * p.2 ^ 2)) := by
          measurability
        exact Measurable.ite hs1' hf measurable_const
      have hraw : StronglyMeasurable (fun p : ℝ × ℝ =>
          (Set.Ioc (1/10:ℝ) (1/2)).indicator
            (fun q : ℝ => if lowerTwoDiscarded ε p.1 q then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - p.1 - q) / q) / (p.1 * q ^ 2)
            else 0) p.2) := by
        refine h2m.stronglyMeasurable.indicator ?_
        exact measurableSet_Ioc.preimage measurable_snd
      have hind : StronglyMeasurable (Function.uncurry (fun a q : ℝ =>
          (Set.Ioc (1/10:ℝ) (1/2)).indicator
            (fun q' : ℝ => if lowerTwoDiscarded ε a q' then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - q') / q') / (a * q' ^ 2)
            else 0) q)) := hraw
      have hsm := StronglyMeasurable.integral_prod_right (ν := volume) hind
      have e : (fun a : ℝ => ∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)) =
          (fun a : ℝ => ∫ β, (Set.Ioc (1/10:ℝ) (1/2)).indicator
            (fun q : ℝ => if lowerTwoDiscarded ε a q then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - q) / q) / (a * q ^ 2)
            else 0) β) := by
        funext a
        rw [intervalIntegral.integral_of_le (by norm_num : (1/10:ℝ) ≤ 1/2),
          ← MeasureTheory.integral_indicator measurableSet_Ioc]
      have hfin : AEStronglyMeasurable (fun a : ℝ => ∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))
          (volume.restrict (Set.Ioc (1/10:ℝ) (1/2))) := by
        rw [e]
        exact hsm.measurable.aestronglyMeasurable.restrict
      exact hfin.const_mul _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha
      rw [Real.norm_eq_abs]
      have hlogZ1 : (1:ℝ) ≤ Real.log (scaleZ ε x) := by
        have h : Real.log 4 ≤ Real.log (scaleZ ε x) := Real.log_le_log (by norm_num) hZ4
        have h2 : (1:ℝ) ≤ Real.log 4 := by
          have h4 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
          have h5 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
            push_cast
            ring
          linarith
        linarith
      calc |(1 / Real.log (scaleZ ε x)) *
            (∫ β in (1/10:ℝ)..(1/2:ℝ),
              (if lowerTwoDiscarded ε a β then
                ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))|
          = |1 / Real.log (scaleZ ε x)| *
            |∫ β in (1/10:ℝ)..(1/2:ℝ),
              (if lowerTwoDiscarded ε a β then
                ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0)| :=
            abs_mul _ _
        _ ≤ 1 * 400 := by
            apply mul_le_mul
            · rw [abs_of_pos (by positivity : (0:ℝ) < 1 / Real.log (scaleZ ε x))]
              rw [div_le_one (by linarith)]
              exact hlogZ1
            · exact hβb a (le_of_lt ha.1)
            · exact abs_nonneg _
            · norm_num
        _ = 400 := by norm_num
  -- the pointwise comparison
  have hpt : ∀ a : ℝ, 1/10 ≤ a → a ≤ 1/2 →
      |(∑ b ∈ Finset.Ioc B0 B1, (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (Real.log (b : ℝ) / Real.log (scaleZ ε x)) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - Real.log (b : ℝ) / Real.log (scaleZ ε x)) /
              (Real.log (b : ℝ) / Real.log (scaleZ ε x))) / a else 0)) -
        (1 / Real.log (scaleZ ε x)) *
          (∫ β in (1/10:ℝ)..(1/2:ℝ),
            (if lowerTwoDiscarded ε a β then
              ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))| ≤
        1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    intro a ha1 ha2
    have h := second_passage_pointwise (ω := ω) hω hz (ε := ε) (Z := scaleZ ε x)
      (s := Real.log (m:ℝ) / Real.log (scaleZ ε x)) hε8 hZ1 hZbig hs0 hs1 ha1 ha2
    rw [← hB0, ← hB1] at h
    simpa [expo] using h
  -- the integral of the difference
  rw [hexch, hdens]
  rw [← intervalIntegral.integral_sub hGint hDint]
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (1/10:ℝ) ≤ 1/2)).trans ?_
  have hpt' : ∀ a ∈ Set.Icc (1/10:ℝ) (1/2),
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        (1 / ((b : ℝ) * Real.log (b : ℝ) ^ 2)) *
          (if lowerTwoDiscarded ε a (expo ε x b) then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - expo ε x b) / expo ε x b) / a
          else 0)) -
        (1 / Real.log (scaleZ ε x)) *
        (∫ β in (1/10:ℝ)..(1/2:ℝ),
          (if lowerTwoDiscarded ε a β then
            ω ((Real.log (m:ℝ) / Real.log (scaleZ ε x) - a - β) / β) / (a * β ^ 2) else 0))| ≤
        1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) := by
    intro a ha
    rw [htrunc a ha.1 ha.2]
    exact hpt a ha.1 ha.2
  refine (intervalIntegral.integral_mono_on (by norm_num : (1/10:ℝ) ≤ 1/2) (hGint.sub hDint).abs
    intervalIntegrable_const hpt').trans ?_
  rw [intervalIntegral.integral_const, smul_eq_mul]
  -- the final numerical comparison
  have hx27 : (27:ℝ) ≤ Real.log x := by
    have h2 : Real.log ((2:ℝ)^40) ≤ Real.log x := Real.log_le_log (by norm_num) hx40
    have h3 : Real.log ((2:ℝ)^40) = 40 * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    have h4 : (0.693:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [h3] at h2
    linarith
  have hlogZ_le : (1 + Real.log (scaleZ ε x)) ≤ 4 * Real.log x := by
    have h1 : Real.log (scaleZ ε x) = Real.log 4 + Real.log (x ^ (11 / 20 + ε)) := by
      rw [hZval, Real.log_mul (by norm_num) (ne_of_gt hY0)]
    have h5 : Real.log (x ^ (11 / 20 + ε)) = (11/20 + ε) * Real.log x := Real.log_rpow hx0 _
    have h6 : (11/20 + ε) * Real.log x ≤ Real.log x := by
      have h7 : (11/20 + ε) ≤ 1 := by linarith
      nlinarith [Real.log_nonneg hx1]
    have h8 : Real.log 4 ≤ 4 := by
      have h9 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
      linarith
    have h10 : (1:ℝ) ≤ Real.log x := by linarith
    linarith
  -- `log^2 (B0-1) ≥ 1/4` and `(B0-1) ≥ Z^(1/20)`
  have hB0m1 : (scaleZ ε x)^(1/20:ℝ) ≤ (B0:ℝ) - 1 := by
    have h2 := hZpow20
    have h3 : (scaleZ ε x)^(1/10:ℝ) = (scaleZ ε x)^(1/20:ℝ) * (scaleZ ε x)^(1/20:ℝ) := by
      rw [← Real.rpow_add hZ0]; norm_num
    have h4 : ((B0:ℝ)) ≥ (scaleZ ε x)^(1/10:ℝ) - 1 := by
      have h5 := Nat.floor_le (show (0:ℝ) ≤ (scaleZ ε x)^(1/10:ℝ) by positivity)
      push_cast at h5
      have h6 := Nat.sub_one_lt_floor ((scaleZ ε x)^(1/10:ℝ))
      linarith
    rw [h3] at h4
    nlinarith [h2, h4]
  have hlogB0 : (1/2:ℝ) ≤ Real.log ((B0:ℝ) - 1) := by
    have h2 : (2:ℝ) ≤ (B0:ℝ) - 1 := by linarith [hB0R4]
    have h3 : Real.log 2 ≤ Real.log ((B0:ℝ) - 1) := Real.log_le_log (by norm_num) h2
    have h4 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hden : (scaleZ ε x)^(1/20:ℝ) / 4 ≤ ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2 := by
    have h2 : (1/4:ℝ) ≤ Real.log ((B0:ℝ) - 1)^2 := by nlinarith
    have h3 : (0:ℝ) < (scaleZ ε x)^(1/20:ℝ) := Real.rpow_pos_of_pos hZ0 _
    nlinarith [hB0m1, h2, h3]
  have hERR : 1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) ≤
      4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ)) := by
    have hpos : (0:ℝ) < ((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2 := by
      have h1 : (0:ℝ) < (B0:ℝ) - 1 := by linarith
      have h2 : (0:ℝ) < Real.log ((B0:ℝ) - 1) := by linarith
      positivity
    have hz0 : (0:ℝ) < (scaleZ ε x)^(1/20:ℝ) := Real.rpow_pos_of_pos hZ0 _
    have hstep : 1000000 * (1 + Real.log (scaleZ ε x)) / (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2) ≤
        1000000 * (1 + Real.log (scaleZ ε x)) / ((scaleZ ε x)^(1/20:ℝ) / 4) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have heq : 1000000 * (1 + Real.log (scaleZ ε x)) / ((scaleZ ε x)^(1/20:ℝ) / 4) =
        4000000 * (1 + Real.log (scaleZ ε x)) * ((scaleZ ε x)^(1/20:ℝ))⁻¹ := by
      field_simp
      norm_num
    rw [Real.rpow_neg (le_of_lt hZ0)]
    linarith [hstep, heq.le, heq.ge]
  have hZpow_le : (scaleZ ε x)^(-(1/20:ℝ)) ≤ x ^ (-(11/400:ℝ)) := by
    have h1 : x ^ (11/400:ℝ) ≤ (scaleZ ε x)^(1/20:ℝ) := by
      rw [hZval]
      have h2 : (4 * x ^ (11/20 + ε))^(1/20:ℝ) =
          4^(1/20:ℝ) * (x ^ (11/20 + ε))^(1/20:ℝ) := Real.mul_rpow (by norm_num) (le_of_lt hY0)
      rw [h2, ← Real.rpow_mul (le_of_lt hx0)]
      have h3 : x ^ (11/400:ℝ) ≤ x ^ ((11/20 + ε) * (1/20)) := by
        apply Real.rpow_le_rpow_of_exponent_le hx1
        nlinarith
      have h4 : (1:ℝ) ≤ 4^(1/20:ℝ) := by
        calc (1:ℝ) = 1^(1/20:ℝ) := by rw [Real.one_rpow]
          _ ≤ 4^(1/20:ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      have h5 : (0:ℝ) < x ^ ((11/20 + ε) * (1/20)) := Real.rpow_pos_of_pos hx0 _
      nlinarith [h3, h4, h5, Real.rpow_pos_of_pos hx0 (11/400:ℝ)]
    rw [Real.rpow_neg (le_of_lt hZ0), Real.rpow_neg (le_of_lt hx0)]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hx0 _)).mpr h1
  have hstep1 : (2/5:ℝ) * (1000000 * (1 + Real.log (scaleZ ε x)) /
      (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2)) ≤
      (2/5:ℝ) * (4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) :=
    mul_le_mul_of_nonneg_left hERR (by norm_num)
  have hstep2 : (2/5:ℝ) * (4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) ≤
      (2/5:ℝ) * (4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2/5)
    have h3 : (0:ℝ) ≤ (1 + Real.log (scaleZ ε x)) := by
      have h5 : 0 ≤ Real.log (scaleZ ε x) := Real.log_nonneg hZ1.le
      linarith
    have hz : (0:ℝ) ≤ (scaleZ ε x)^(-(1/20:ℝ)) := Real.rpow_nonneg hZ0.le _
    calc 4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))
        = 4000000 * ((1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) := by ring
      _ ≤ 4000000 * ((4 * Real.log x) * (scaleZ ε x)^(-(1/20:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hlogZ_le hz
      _ ≤ 4000000 * ((4 * Real.log x) * x ^ (-(11/400:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hZpow_le (by linarith)
      _ = 4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ)) := by ring
  -- the power saving and one logarithmic factor
  have hLbig : ((N + 2) / (11/400) + 1) ^ 3 ≤ Real.log x := by
    have h1 : max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1) ≤ Real.log x := by
      rw [← Real.log_exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1))]
      exact Real.log_le_log (Real.exp_pos _) hXe
    have h2 : ((N + 2) / (11/400) + 1) ^ 3 ≤ max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1) := by
      have h3 : ((N + 2) / (11/400) + 1) ^ 3 + 1 ≤ max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1) :=
        le_max_right _ _
      linarith
    linarith
  have hpow : x ^ (-(11/400:ℝ)) ≤ Real.exp (-(N + 2) * Real.log x ^ (1 / 3 : ℝ)) := by
    have h1 : x ^ (-(11/400:ℝ)) = Real.exp (-(11/400) * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0]; ring_nf
    set L13 := Real.log x ^ (1 / 3 : ℝ) with hL13
    have hL130 : 0 ≤ L13 := Real.rpow_nonneg (Real.log_nonneg hx1) _
    have hL13sq : L13 * L13 = Real.log x ^ (2 / 3 : ℝ) := by
      rw [hL13, ← Real.rpow_add (by linarith)]
      norm_num
    have hL23 : Real.log x ^ (2 / 3 : ℝ) ≤ Real.log x := by
      calc Real.log x ^ (2 / 3 : ℝ) ≤ Real.log x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = Real.log x := Real.rpow_one _
    have h3 : ((N + 2) / (11/400) + 1) ≤ L13 := by
      have h4 : (((N + 2) / (11/400) + 1) ^ 3) ^ (1 / 3 : ℝ) ≤ L13 := by
        rw [hL13]
        exact Real.rpow_le_rpow (by positivity) hLbig (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N + 2) / (11/400) + 1),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h4
      exact h4
    have h6 : (N + 2) * L13 ≤ (11/400) * Real.log x := by
      have h7 : (N + 2) ≤ (11/400) * L13 := by
        have h8 : (0:ℝ) < 11/400 := by norm_num
        have h9 : ((N + 2) / (11/400)) * (11/400) = N + 2 := by field_simp
        nlinarith
      have h10 : (N + 2) * L13 ≤ ((11/400) * L13) * L13 := by nlinarith
      have h11 : ((11/400) * L13) * L13 = (11/400) * (L13 * L13) := by ring
      rw [h11, hL13sq] at h10
      linarith
    have e1 : -(11/400) * Real.log x = -((11/400) * Real.log x) := by ring
    have e2 : -(N + 2) * Real.log x ^ (1 / 3 : ℝ) = -((N + 2) * L13) := by rw [hL13]; ring
    rw [h1, e1, e2]
    exact Real.exp_le_exp.mpr (by linarith)

  have habs : Real.log x * Real.exp (-(N + 2) * Real.log x ^ (1 / 3 : ℝ)) ≤
      Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h := hLX x hxCL
    rw [pow_one] at h
    have he : (-(N + (1:ℕ) + 1) : ℝ) = -(N + 2) := by push_cast; ring
    rwa [he] at h
  have hfac : (1/2:ℝ) - 1/10 = 2/5 := by norm_num
  rw [hfac]
  calc (2/5:ℝ) * (1000000 * (1 + Real.log (scaleZ ε x)) /
        (((B0:ℝ) - 1) * Real.log ((B0:ℝ) - 1)^2))
      ≤ (2/5:ℝ) * (4000000 * (1 + Real.log (scaleZ ε x)) * (scaleZ ε x)^(-(1/20:ℝ))) := hstep1
    _ ≤ (2/5:ℝ) * (4000000 * (4 * Real.log x) * x ^ (-(11/400:ℝ))) := hstep2
    _ ≤ (2/5:ℝ) * (4000000 * (4 * (Real.log x * Real.exp (-(N + 2) * Real.log x ^ (1 / 3 : ℝ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2/5)
        have h1 : Real.log x * x ^ (-(11/400:ℝ)) ≤
            Real.log x * Real.exp (-(N + 2) * Real.log x ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by linarith)
        nlinarith [h1]
    _ ≤ (2/5:ℝ) * (4000000 * (4 * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2/5)
        nlinarith [habs]
    _ ≤ (Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) + (2:ℝ)^40 + CL + 8) *
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
        have h0 : (0:ℝ) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
        have h1 : (6400000 : ℝ) ≤
            Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) + (2:ℝ)^40 + CL + 8 := by
          have h2 : (0:ℝ) ≤ Real.exp (max 2 (((N + 2) / (11/400) + 1) ^ 3 + 1)) := (Real.exp_pos _).le
          have h3 : (1:ℝ) ≤ (2:ℝ)^40 := by norm_num
          have h4 : (0:ℝ) ≤ CL := hCL.le
          linarith
        have h5 : (2/5:ℝ) * (4000000 * (4 * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)))) =
            6400000 * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by ring
        rw [h5]
        exact mul_le_mul_of_nonneg_right h1 h0

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the E2 passage from sums to the integral, exponential precision. -/
private theorem two_pair_riemann_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ b ∈ Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          ∑ a ∈ Finset.Ioc b ⌊2 * x ^ (11 / 20 + ε)⌋₊,
            (if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
                ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
                  Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ))
              else 0) * (1 / Real.log (a : ℝ) * (1 / Real.log (b : ℝ)))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨C1, hC1⟩ := two_pair_riemann_first_exp ω hω hz hε hε8 N hN
  obtain ⟨C2, hC2⟩ := two_pair_riemann_second_exp ω hω hz hε hε8 N hN
  refine ⟨max (max C1 C2) (|C1| + |C2| + 1), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hx2 : C2 ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hC : |C1| + |C2| + 1 ≤ max (max C1 C2) (|C1| + |C2| + 1) := le_max_right _ _
  have hE0 : (0:ℝ) < Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := Real.exp_pos _
  have b1 := abs_le.mp (hC1 x hx1 m hm1 hm2)
  have b2 := abs_le.mp (hC2 x hx2 m hm1 hm2)
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hE0.le
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hE0.le
  have k3 := mul_le_mul_of_nonneg_right hC hE0.le
  have k4 : (|C1| + |C2| + 1) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) =
      |C1| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) +
        |C2| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) +
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by ring
  rw [abs_le]
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, k1, k2, k3, k4]

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the E2 sum at one point of J, exponential precision. -/
private theorem two_pair_density_pointwise_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |(∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
            Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) -
        lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x)| ≤ C * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨C1, hC1⟩ := two_pair_first_prime_exp ω hω hz hε hε8 N hN
  obtain ⟨C2, hC2⟩ := two_pair_second_prime_exp ω hω hz hε hε8 N hN
  obtain ⟨C3, hC3⟩ := two_pair_riemann_exp ω hω hz hε hε8 N hN
  refine ⟨max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)), fun x hx m hm1 hm2 => ?_⟩
  have hx1 : C1 ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hx2 : C2 ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hx3 : C3 ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hC : |C1| + |C2| + |C3| + 1 ≤ max (max C1 C2) (max C3 (|C1| + |C2| + |C3| + 1)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hE0 : (0:ℝ) ≤ Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  have b1 := hC1 x hx1 m hm1 hm2
  have b2 := hC2 x hx2 m hm1 hm2
  have b3 := hC3 x hx3 m hm1 hm2
  have hiter := two_pair_sum_iterated ⌊2 * x ^ (11 / 20 + ε)⌋₊
    (fun a b => lowerTwoDiscarded ε (expo ε x a) (expo ε x b))
    (fun a b => ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
      Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)))
  have hsplit := two_pair_sum_split ⌊2 * x ^ (11 / 20 + ε)⌋₊ primeWeight
    (fun n => 1 / Real.log (n : ℝ))
    (fun a b => if lowerTwoDiscarded ε (expo ε x a) (expo ε x b) then
      ω (Real.log ((m : ℝ) / ((a : ℝ) * (b : ℝ))) / Real.log (b : ℝ)) /
        Real.log (b : ℝ) / ((a : ℝ) * (b : ℝ)) else 0)
  beta_reduce at hiter hsplit
  rw [hiter, hsplit]
  have a1 := abs_le.mp b1
  have a2 := abs_le.mp b2
  have a3 := abs_le.mp b3
  have hEpos : (0:ℝ) < Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := Real.exp_pos _
  have k1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hEpos.le
  have k2 := mul_le_mul_of_nonneg_right (le_abs_self C2) hEpos.le
  have k3 := mul_le_mul_of_nonneg_right (le_abs_self C3) hEpos.le
  have k4 := mul_le_mul_of_nonneg_right hC hEpos.le
  have k5 : (|C1| + |C2| + |C3| + 1) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) =
      |C1| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) +
        |C2| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) +
        |C3| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) +
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by ring
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, k1, k2, k3, k4, k5]

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the E2 cofactor variable, at stretched exponential precision. -/
private theorem two_cofactor_riemann_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
            (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
            i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
              lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
          ((∑ n ∈ Finset.Ioc (⌊x ^ (11 / 20 + ε)⌋₊ / (i.1 * i.2)) (U / (i.1 * i.2)),
              ω (Real.log (n : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)) -
            ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
              ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
                Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ)))| ≤
        C * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨CL, hCL, hLX⟩ := log_pow_mul_exp_le N 3
  set A1 : ℝ := max 57600 ((40 * N) ^ 2 + 1) with hA1def
  set A2 : ℝ := max 2 (((N + 4) / (11/200) + 1) ^ 3 + 1) with hA2def
  set Lx : ℝ := A1 + 2 + A2 with hLx
  refine ⟨Real.exp Lx + (2:ℝ)^36 + CL + 8, fun x hx U hU => ?_⟩
  have hCL0 : (0:ℝ) ≤ CL := hCL.le
  have hXe : Real.exp Lx ≤ x := by
    have h1 : (0:ℝ) ≤ (2:ℝ)^36 + CL + 8 := by positivity
    linarith
  have hx36 : (2:ℝ)^36 ≤ x := by
    have h1 : (0:ℝ) ≤ Real.exp Lx := (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ CL + 8 := by positivity
    linarith
  have hCLx : CL ≤ x := by
    have h1 : (0:ℝ) ≤ Real.exp Lx := (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (2:ℝ)^36 + 8 := by positivity
    linarith
  have hA20 : (0:ℝ) ≤ A2 := by rw [hA2def]; positivity
  have hA10 : (0:ℝ) ≤ A1 := by rw [hA1def]; positivity
  have hLexp : A2 ≤ Lx := by rw [hLx]; linarith
  have hLlow : A1 + 2 ≤ Lx := by rw [hLx]; linarith
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h1 := Real.exp_one_lt_d9
    have h2 : (3 : ℝ) ≤ 2 ^ 36 := by norm_num
    linarith
  have hlam0 : 0 < Real.log x := by linarith
  obtain ⟨-, hlX2⟩ := log_scale_bounds hε hε8 hxpos hl1
  have hl0 : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_nonneg (by linarith)
  have hW : 0 < (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hU).trans hNle
  have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log (by exact_mod_cast hN1) hNle
  have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_natCast_nonneg _
  have hR0 : 0 ≤ 8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8 := by linarith
  have hT0 : 0 ≤ 2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
    div_nonneg (by linarith) hW.le
  have hRT : 0 ≤ (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
      (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := mul_nonneg hR0 hT0
  refine (two_cofactor_sum_bound (Finset.filter_subset _ _) _ hRT (fun i hi => ?_)).trans ?_
  · obtain ⟨hp1, hp2, -, hE⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨-, hWp⟩ := lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hE
    exact two_cofactor_pair_term ω hω hz _ hp1 hp2 hW hWp hU' (by linarith)
  -- the final comparison of sizes
  have ha : 8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8 ≤ 32 * Real.log x := by linarith
  have hb : (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2 ≤ 9 * Real.log x ^ 2 := by
    have h1 : 1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 3 * Real.log x := by linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : (3 * Real.log x) ^ 2 = 9 * Real.log x ^ 2 := by ring
    linarith
  have hprod : (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
      (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
      (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2 ≤
      32 * Real.log x * (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (9 * Real.log x ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_right ha hT0) hb (sq_nonneg _)
      (mul_nonneg (by linarith) hT0)

  have hWge : x ^ (11 / 200 : ℝ) ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) := by
    have h1 : x ^ (11 / 20 : ℝ) ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc x ^ (11 / 200 : ℝ) = (x ^ (11 / 20 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hxpos.le _) (by linarith) (by norm_num)
  -- the power saving absorbs the logarithmic factor
  have hlogx1 : 1 ≤ Real.log x := by
    have h2 : Real.log ((2:ℝ)^36) ≤ Real.log x := Real.log_le_log (by norm_num) hx36
    have h3 : Real.log ((2:ℝ)^36) = 36 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have h4 : (0.693:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hlogLx : Lx ≤ Real.log x := by
    rw [← Real.log_exp Lx]
    exact Real.log_le_log (Real.exp_pos _) hXe
  have hLbig : (N + 4) / (11/200) + 1 ≤ Real.log x ^ (1 / 3 : ℝ) := by
    have h4 : (((N + 4) / (11/200) + 1) ^ 3) ^ (1 / 3 : ℝ) ≤ Real.log x ^ (1 / 3 : ℝ) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have h6 : ((N + 4) / (11/200) + 1) ^ 3 + 1 ≤ A2 := by rw [hA2def]; exact le_max_right _ _
      linarith
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (N + 4) / (11/200) + 1),
      show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at h4
    exact h4
  set L13 := Real.log x ^ (1 / 3 : ℝ) with hL13
  have hL130 : 0 ≤ L13 := Real.rpow_nonneg (by linarith) _
  have hL13sq : L13 * L13 = Real.log x ^ (2 / 3 : ℝ) := by
    rw [hL13, ← Real.rpow_add (by linarith)]; norm_num
  have hL23 : Real.log x ^ (2 / 3 : ℝ) ≤ Real.log x := by
    calc Real.log x ^ (2 / 3 : ℝ) ≤ Real.log x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = Real.log x := Real.rpow_one _
  have hpow : x ^ (-(11/200:ℝ)) ≤ Real.exp (-(N + 4) * L13) := by
    have h1 : x ^ (-(11/200:ℝ)) = Real.exp (-(11/200) * Real.log x) := by
      rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
    have h6 : (N + 4) * L13 ≤ (11/200) * Real.log x := by
      have h7 : (N + 4) ≤ (11/200) * L13 := by
        have h8 : (0:ℝ) < 11/200 := by norm_num
        have h9 : ((N + 4) / (11/200)) * (11/200) = N + 4 := by field_simp
        nlinarith
      have h10 : (N + 4) * L13 ≤ ((11/200) * L13) * L13 := by nlinarith
      have h11 : ((11/200) * L13) * L13 = (11/200) * (L13 * L13) := by ring
      rw [h11, hL13sq] at h10
      linarith
    rw [h1]
    apply Real.exp_le_exp.mpr
    have e1 : -(11/200) * Real.log x = -((11/200) * Real.log x) := by ring
    have e2 : (-(N + 4)) * L13 = -((N + 4) * L13) := by ring
    rw [e1, e2]
    linarith
  have habs : Real.log x ^ 3 * Real.exp (-(N + 4) * L13) ≤ Real.exp (-N * L13) := by
    have h := hLX x hCLx
    have he : (-(N + (3:ℕ) + 1) : ℝ) = -(N + 4) := by push_cast; ring
    rw [he] at h
    simpa [hL13] using h
  have hfin : Real.log x ^ 3 / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤
      Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    rw [div_eq_mul_inv]
    have h2 : (x ^ (11 / 200 : ℝ))⁻¹ ≤ Real.exp (-(N + 4) * L13) := by
      have e : (x ^ (11 / 200 : ℝ))⁻¹ = x ^ (-(11/200:ℝ)) :=
        (Real.rpow_neg hxpos.le (11/200)).symm
      rw [e]
      exact hpow
    calc Real.log x ^ 3 * ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ))⁻¹
        = Real.log x ^ 3 * ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ))⁻¹ := rfl
      _ ≤ Real.log x ^ 3 * (x ^ (11 / 200 : ℝ))⁻¹ := by
          have h3 : (0:ℝ) < Real.log x ^ 3 := by positivity
          have h4 : ((2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ))⁻¹ ≤ (x ^ (11 / 200 : ℝ))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hxpos _) hWge
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ Real.log x ^ 3 * Real.exp (-(N + 4) * L13) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ Real.exp (-N * L13) := habs
      _ = Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by rw [hL13]
  calc (8 * (1 + Real.log (2 * x ^ (11 / 20 + ε))) + 8) *
        (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (1 + Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ)) ^ 2
      ≤ 32 * Real.log x * (2 * x ^ (11 / 20 + ε) / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) *
        (9 * Real.log x ^ 2) := hprod
    _ = 576 * x ^ (11 / 20 + ε) *
        (Real.log x ^ 3 / (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ)) := by ring
    _ ≤ 576 * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ ≤ (Real.exp Lx + (2:ℝ)^36 + CL + 8) * x ^ (11 / 20 + ε) *
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
        have h1 : (576 : ℝ) ≤ Real.exp Lx + (2:ℝ)^36 + CL + 8 := by
          have h2 : (0:ℝ) ≤ Real.exp Lx := (Real.exp_pos _).le
          have h3 : (1:ℝ) ≤ (2:ℝ)^36 := by norm_num
          linarith
        have h0 : (0:ℝ) ≤ x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by positivity
        calc 576 * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))
            = 576 * (x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) := by ring
          _ ≤ (Real.exp Lx + (2:ℝ)^36 + CL + 8) *
              (x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) :=
              mul_le_mul_of_nonneg_right h1 h0
          _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- Page 51 display 5.17: the E2 density main term, exponential precision. -/
private theorem two_density_main_exp (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ U : ℕ, U ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ U,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
  obtain ⟨CA, hCA⟩ := two_pair_density_pointwise_exp ω hω hz hε hε8 N hN
  obtain ⟨CB, hCB⟩ := two_cofactor_riemann_exp ω hω hz hε hε8 N hN
  refine ⟨max (max CA CB) (2 * |CA| + |CB| + 1), fun x hx U hU => ?_⟩
  have hxA : CA ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hxB : CB ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hx1 : (1 : ℝ) ≤ x := by
    have h2 : max (max CA CB) (2 * |CA| + |CB| + 1) ≤ x := hx
    have h3 : (1:ℝ) ≤ 2 * |CA| + |CB| + 1 := by
      have h5 : (0:ℝ) ≤ |CA| := abs_nonneg CA
      have h6 : (0:ℝ) ≤ |CB| := abs_nonneg CB
      linarith
    have h4 : (2 * |CA| + |CB| + 1) ≤ max (max CA CB) (2 * |CA| + |CB| + 1) := le_max_right _ _
    linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hE0 : (0:ℝ) < Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := Real.exp_pos _
  have hU' : (U : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    (Nat.cast_le.mpr hU).trans (Nat.floor_le (by positivity))
  have hB' := hCB x hxB U hU
  have hmain := two_density_swap_combine
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
      (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
      i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
        lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (fun i : ℕ × ℕ => i.1 * i.2)
    (fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      exact Nat.mul_pos hi'.1.pos hi'.2.1.pos)
    (fun (i : ℕ × ℕ) (n : ℕ) => ω (Real.log (n : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ))
    (fun (i : ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ))) / Real.log (i.2 : ℝ)) /
        Real.log (i.2 : ℝ) / ((i.1 : ℝ) * (i.2 : ℝ)))
    (fun m : ℕ => lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
      Real.log (scaleZ ε x))
    ⌊x ^ (11 / 20 + ε)⌋₊ U (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)))
    (CB * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)))
    (mul_nonneg (abs_nonneg CA) hE0.le) hB'
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact (hCA x hxA m hm'.1 (hm'.2.trans hU)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self CA) hE0.le))
  refine hmain.trans ?_
  have h2 : (U : ℝ) * (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) ≤
      2 * |CA| * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h1 : (U : ℝ) * (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) ≤
        2 * x ^ (11 / 20 + ε) * (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_right hU' (mul_nonneg (abs_nonneg CA) hE0.le)
    calc (U : ℝ) * (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)))
        ≤ 2 * x ^ (11 / 20 + ε) * (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) := h1
      _ = 2 * |CA| * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by ring
  have hstep : CB * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) +
        (U : ℝ) * (|CA| * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) ≤
      (2 * |CA| + |CB| + 1) * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h3 : CB * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) ≤
        |CB| * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
      have h0 : (0:ℝ) ≤ x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by positivity
      calc CB * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))
          = CB * (x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) := by ring
        _ ≤ |CB| * (x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_abs_self CB) h0
        _ = |CB| * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by ring
    nlinarith [h2, h3]
  have h4 : (2 * |CA| + |CB| + 1) ≤ max (max CA CB) (2 * |CA| + |CB| + 1) := le_max_right _ _
  have h5 : (2 * |CA| + |CB| + 1) * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) ≤
      (max (max CA CB) (2 * |CA| + |CB| + 1)) * x ^ (11 / 20 + ε) *
        Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by
    have h0 : (0:ℝ) ≤ x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ)) := by positivity
    calc (2 * |CA| + |CB| + 1) * x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))
        = (2 * |CA| + |CB| + 1) * (x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) := by ring
      _ ≤ (max (max CA CB) (2 * |CA| + |CB| + 1)) *
          (x ^ (11 / 20 + ε) * Real.exp (-N * Real.log x ^ (1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_right h4 h0
      _ = _ := by ring
  linarith [hstep, h5]

/-! ### The three leaves -/

/-- LEAF: page 51 display 5.17, the prime number theorem for the primes of the rough cofactor
`n3` or `n5` of display 5.15. HARD. P0069: "a straightforward consequence of the prime number
theorem, with error term `Y exp(-ε L^(1/2))`". On every integer interval `(a, b]` below `X`,
numbers with no prime factor below `z ≥ X ^ c` have density `ω(log n / log z) / log z`, error
`b exp(-N (log X)^(1/3))` for every `N`. Strong error form of
`LowerShortC165.leaf_rough_interval_density`; route: Buchstab's identity with the error of
`DQ517StrongPNTInput.psi_error_stretched`. -/
theorem leaf_rough_window_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) :=
  rough_interval_density_exp ω hω hz hc N hN

/-- LEAF: page 51 display 5.17, the prime number theorem applied to the outer primes `p1`, `p2`
of the E2 sum of display 5.15. HARD. P0069: "a straightforward consequence of the prime number
theorem, with error term `Y exp(-ε L^(1/2))`". With the rough cofactor `n3 = m / (p1 p2)`
replaced by its Buchstab density at level `p2`, the sum over prime pairs with exponents in E2
has local density `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) / (β1 β2^2)` at `m = Z^s`, with
error `O(Y T0^(-5))` on every integer subinterval of J. The window form of
`LowerShortC165.leaf_two_density_main`. -/
theorem leaf_two_main_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C, hC⟩ := two_density_main_exp ω hω hz hε hε8 5 (by norm_num)
  refine ⟨max (2 * C) 8, fun x hx a b ha hb => ?_⟩
  have hxC : C ≤ x := by
    have h1 : 2 * C ≤ max (2 * C) 8 := le_max_left _ _
    have h3 : max (2 * C) 8 ≤ x := hx
    have h4 : (8:ℝ) ≤ x := le_trans (le_max_right _ _) hx
    rcases le_or_gt 0 C with h | h
    · nlinarith
    · linarith
  have hx8 : (8:ℝ) ≤ x := (le_max_right _ _).trans hx
  have hT : (perronT0 x ^ 5)⁻¹ = Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := by
    unfold LeanLab.BHP1997.DQLowerExceptionalMeanSquare.perronT0
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hM0 : (0:ℝ) ≤ max (2 * C) 8 := le_trans (by norm_num) (le_max_right _ _)
  have hE0 : (0:ℝ) ≤ Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
  have hkey : (0:ℝ) ≤ max (2 * C) 8 * x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) :=
    mul_nonneg (mul_nonneg hM0 hYpos.le) hE0
  rcases le_or_gt a b with hab | hab
  · have hsplit := Finset.sum_Ioc_consecutive
      (fun m => ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))) ha hab
    have ha' : a ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := le_trans hab hb
    have h1 := hC x hxC b hb
    have h2 := hC x hxC a ha'
    have heq : ∑ m ∈ Finset.Ioc a b,
          ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x)) =
        (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ b,
          ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))) -
        (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ a,
          ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))) := by
      linarith [hsplit]
    rw [heq, hT]
    refine (abs_sub _ _).trans ?_
    have h3 : |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ b,
          ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := h1
    have h4 : |∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ a,
          ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
              i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
                lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)),
            if i.1 * i.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ)
            else 0) -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := h2
    have h5 : (0:ℝ) ≤ x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := by positivity
    have h6 : 2 * C ≤ max (2 * C) 8 := le_max_left _ _
    calc _ ≤ C * x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) +
          C * x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := by linarith
      _ = (2 * C) * (x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ))) := by ring
      _ ≤ max (2 * C) 8 * (x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_right h6 h5
      _ = max (2 * C) 8 * x ^ (11 / 20 + ε) * Real.exp (-5 * Real.log x ^ (1 / 3 : ℝ)) := by ring
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero, hT]
    exact hkey


/-- LEAF: page 51 display 5.17, the prime number theorem applied to the outer primes `p1` to
`p4` of the E4 sum of display 5.15. HARD. P0069: "a straightforward consequence of the prime
number theorem, with error term `Y exp(-ε L^(1/2))`". With the rough cofactor
`n5 = m / (p1 p2 p3 p4)` replaced by its Buchstab density at level `p4`, the sum over prime
quadruples with exponents in E4 has local density the E4 integral of page 51 with `1` replaced
by `s`, over `log Z`, at `m = Z^s`, with error `O(Y T0^(-5))` on every integer subinterval of J.
The window form of `LowerShortC165.leaf_four_density_main`. -/
theorem leaf_four_main_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
            if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
                  Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)
            else 0) -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-! ### Proved steps -/

/-- Page 51 display 5.17. The summation of the rough density estimate over the outer primes of
a subtracted sum of display 5.15, as `LowerPrincipal517g.rough_family_density_sum`, for any
error factor `E ≥ 0` in place of a log power. -/
theorem rough_family_window_sum (ω : ℝ → ℝ) {c C E X : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hmain : ∀ z : ℕ, X ^ c ≤ (z : ℝ) → ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
      |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z)| ≤ C * b * E)
    {ι : Type} (I : Finset ι) (d z : ι → ℕ) (L U : ℕ) (M : ℝ)
    (hI : ∀ i ∈ I, 1 ≤ d i ∧ d i ≤ L ∧ X ^ c ≤ (z i : ℝ)) (hU : (U : ℝ) ≤ X)
    (hM : ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) ≤ M) :
    |∑ m ∈ Finset.Ioc L U, ∑ i ∈ I, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * M * U * E := by
  have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  rw [Finset.sum_comm]
  have hterm : ∀ i ∈ I, |∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * U * E * ((1 : ℝ) / (d i : ℝ)) := by
    intro i hi
    obtain ⟨hd1, hdL, hz⟩ := hI i hi
    have hd0 : 0 < d i := hd1
    rw [real_sum_dvd_reindex hd1 L U
      (fun m => Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))]
    have hre : ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
        (Task308.roughIndicator (d i * n / d i) (z i) -
          ω (Real.log ((d i * n / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) =
        ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.mul_div_cancel_left n hd0]
    rw [hre]
    have hcast : ((U / d i : ℕ) : ℝ) ≤ (U : ℝ) / (d i : ℝ) := Nat.cast_div_le
    have hUd : (U : ℝ) / (d i : ℝ) ≤ U :=
      div_le_self hUnn (by exact_mod_cast hd1)
    have hb := hmain (z i) hz (L / d i) (U / d i)
      (Nat.div_pos hdL hd0) (hcast.trans (hUd.trans hU))
    calc |∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))|
        ≤ C * ((U / d i : ℕ) : ℝ) * E := hb
      _ ≤ C * ((U : ℝ) / (d i : ℝ)) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hC) hE
      _ = C * U * E * ((1 : ℝ) / (d i : ℝ)) := by ring
  have hK : 0 ≤ C * U * E := mul_nonneg (mul_nonneg hC hUnn) hE
  calc |∑ i ∈ I, ∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)|
      ≤ ∑ i ∈ I, C * U * E * ((1 : ℝ) / (d i : ℝ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = C * U * E * ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C * U * E * M := mul_le_mul_of_nonneg_left hM hK
    _ = C * M * U * E := by ring

/-- `T0 = exp((log x)^(1/3))` written as a cube root: `T0 ^ k = exp(k l)` with `l ^ 3 = log x`. -/
theorem perronT0_pow (x : ℝ) (k : ℕ) :
    perronT0 x ^ k = Real.exp (k * Real.log x ^ (1 / 3 : ℝ)) := by
  rw [perronT0, ← Real.exp_nat_mul]

/-- Page 51 display 5.17, the log powers of the outer reciprocal sums are below `T0 ^ 5`:
`L ^ 4 ≤ 512 T0 ^ 5` once `0 ≤ L ≤ 4 log x`, from `l ^ 12 ≤ 12! / 5 ^ 12 · exp(5 l)`. -/
theorem pow_four_le_perronT0 {x L : ℝ} (hx : 1 ≤ x) (hL0 : 0 ≤ L) (hL : L ≤ 4 * Real.log x) :
    L ^ 4 ≤ 512 * perronT0 x ^ 5 := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set l := Real.log x ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log x := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have h1 : L ^ 4 ≤ (4 * l ^ 3) ^ 4 := pow_le_pow_left₀ hL0 (hl3 ▸ hL) 4
  have h2 := Real.pow_div_factorial_le_exp (5 * l) (by positivity) 12
  rw [perronT0_pow]
  push_cast
  have hfac : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hfac, mul_pow] at h2
  have h3 : (4 * l ^ 3) ^ 4 = 256 * l ^ 12 := by ring
  have hl12 : 0 ≤ l ^ 12 := by positivity
  nlinarith

/-- Page 51 display 5.17: the strong prime number theorem error at a scale `X` with
`log X ≥ log x / 8` is below `T0 ^ (-10)`, for `N = 20`. -/
theorem exp_decay_le_perronT0 {x X : ℝ} (hx : 1 ≤ x) (hX : Real.log x / 8 ≤ Real.log X) :
    Real.exp (-20 * Real.log X ^ (1 / 3 : ℝ)) ≤ (perronT0 x ^ 10)⁻¹ := by
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set l := Real.log x ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log x := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have hcube : (l / 2) ^ 3 ≤ Real.log X := by
    have : (l / 2) ^ 3 = Real.log x / 8 := by rw [div_pow, hl3]; norm_num
    rw [this]; exact hX
  have hroot : l / 2 ≤ Real.log X ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hcube (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by
      norm_num, Real.rpow_one] at h
  rw [perronT0_pow, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  push_cast
  linarith

/-- Page 51 display 5.17, the arithmetic of the final bound: the rough error summed over the
outer primes, `C0 M b E`, with `M ≤ 512 T0 ^ 5`, `b ≤ 2 Y` and `E ≤ T0 ^ (-10)`, is at most
`1024 C0 Y T0 ^ (-5)`. -/
theorem window_error_arith {C0 M b E Y T : ℝ} (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M) (hb0 : 0 ≤ b)
    (hE0 : 0 ≤ E) (hT : 0 < T) (hM : M ≤ 512 * T ^ 5) (hb : b ≤ 2 * Y)
    (hE : E ≤ (T ^ 10)⁻¹) :
    C0 * M * b * E ≤ 1024 * C0 * Y * (T ^ 5)⁻¹ := by
  have hT5 : 0 < T ^ 5 := pow_pos hT 5
  have hY0 : 0 ≤ Y := by linarith
  calc C0 * M * b * E ≤ C0 * (512 * T ^ 5) * (2 * Y) * (T ^ 10)⁻¹ :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hM hC0) hb hb0
          (mul_nonneg hC0 (by positivity))) hE hE0
          (mul_nonneg (mul_nonneg hC0 (by positivity)) (by linarith))
    _ = 1024 * C0 * Y * (T ^ 5)⁻¹ := by
        rw [show T ^ 10 = T ^ 5 * T ^ 5 by ring]
        field_simp
        ring

/-- Page 3 and page 51: the sizes of `Y = x ^ (11/20 + ε)` used in the assembly, for large `x`. -/
theorem window_scale_facts {ε x C0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hx36 : (2 : ℝ) ^ 36 ≤ x) (hxC : C0 ^ 2 ≤ x) :
    (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) ∧ C0 ≤ x ^ (11 / 20 + ε) ∧
      Real.log x / 8 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ∧
      1 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ∧
      2 * Real.log (2 * x ^ (11 / 20 + ε)) ≤ 4 * Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x :=
    Real.log_rpow hxpos _
  have hl2Y : Real.log (x ^ (11 / 20 + ε)) ≤ Real.log (2 * x ^ (11 / 20 + ε)) :=
    Real.log_le_log hYpos (by linarith)
  have hYx : x ^ (11 / 20 + ε) ≤ x := by
    calc x ^ (11 / 20 + ε) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num at hε8 ⊢; linarith)
      _ = x := Real.rpow_one x
  refine ⟨hY49, Decomp514a.shortY_ge_of_sq_le hε hx1 hxC, ?_, ?_, ?_⟩
  · rw [hlogY] at hl2Y
    nlinarith
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  · have h1 : Real.log (2 * x ^ (11 / 20 + ε)) ≤ Real.log (x ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith

/-- PROVED from the three leaves of this file: page 51 display 5.17, the E2 term, with exactly
the statement of `DQ517Window.leaf_two_window`. The E2 sum is the family sum over prime pairs,
`Decomp514a.lowerTwoTerms_eq_family`; the rough cofactor is replaced by its Buchstab density by
`leaf_rough_window_density` at the scale `2 Y` with `N = 20`, summed over the pairs with
`Decomp514a.pair_reciprocal_sum_le`; the rest is `leaf_two_main_window`. -/
theorem two_window_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C0, hC0, hbb⟩ := leaf_rough_window_density ω hω hz (c := 1 / 10) (by norm_num)
    20 (by norm_num)
  obtain ⟨C1, hmainleaf⟩ := leaf_two_main_window ω hω hz hε hε8
  refine ⟨max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)), ?_⟩
  intro x hx a b ha hb
  have hCm : 1024 * C0 + C1 ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) :=
    le_max_left _ _
  have hx36 : (2 : ℝ) ^ 36 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C0 ^ 2 ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hxC1 : C1 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  obtain ⟨hY49, hYC, hlog8, hL1, hL4⟩ := window_scale_facts hε hε8 hx36 hxC
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hbR : (b : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hb).trans hNle
  have hsp := family_density_split
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
          lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (Finset.Ioc a b)
    (lowerTwoTerms ε x)
    (fun m : ℕ => lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x))
    (fun (i : ℕ × ℕ) (m : ℕ) => Task308.roughIndicator (m / (i.1 * i.2)) i.2)
    (fun (i : ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ))
    (fun (i : ℕ × ℕ) (m : ℕ) => i.1 * i.2 ∣ m)
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact Decomp514a.lowerTwoTerms_eq_family ε x (by omega) (hm'.2.trans hb))
  have h1 := rough_family_window_sum ω hC0.le (Real.exp_pos _).le
    (hbb (2 * x ^ (11 / 20 + ε)) (by linarith))
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
        i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
          lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
    (fun i : ℕ × ℕ => i.1 * i.2) (fun i : ℕ × ℕ => i.2)
    a b ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2)
    (by
      intro i hi
      obtain ⟨-, hp1, hp2, -, hdisc⟩ := Finset.mem_filter.mp hi
      obtain ⟨hb1, hb2⟩ := Decomp514a.lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hdisc
      exact ⟨Nat.mul_pos hp1.pos hp2.pos, hb1.trans ha, hb2⟩)
    hbR
    (by
      refine le_trans (Decomp514a.pair_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
        (Finset.filter_subset _ _)) ?_
      have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
      have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
          Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have h2 := hmainleaf x hxC1 a b ha hb
  have hM : (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 ≤ 512 * perronT0 x ^ 5 :=
    (pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 4)).trans
      (pow_four_le_perronT0 hx1 (by linarith) hL4)
  have h3 := window_error_arith hC0.le (sq_nonneg _) (Nat.cast_nonneg b) (Real.exp_pos _).le
    (Real.exp_pos _) hM hbR (exp_decay_le_perronT0 hx1 hlog8)
  refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
    ((add_le_add (h1.trans h3) h2).trans ?_))
  have hT : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (Real.exp_pos _).le 5)
  calc 1024 * C0 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ +
        C1 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹
      = (1024 * C0 + C1) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
    _ ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) *
          (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right hCm (mul_nonneg hYpos.le hT)
    _ = _ := by ring

/-- PROVED from the three leaves of this file: page 51 display 5.17, the E4 term, with exactly
the statement of `DQ517Window.leaf_four_window`. The E4 sum is the family sum over prime
quadruples, `Decomp514a.four_terms_eq_family`; the rough cofactor is replaced by its Buchstab
density by `leaf_rough_window_density` at the scale `2 Y` with `N = 20`, summed over the
quadruples with `Decomp514a.four_reciprocal_sum_le`; the rest is `leaf_four_main_window`. -/
theorem four_window_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C0, hC0, hbb⟩ := leaf_rough_window_density ω hω hz (c := 1 / 10) (by norm_num)
    20 (by norm_num)
  obtain ⟨C1, hmainleaf⟩ := leaf_four_main_window ω hω hz hε hε8
  refine ⟨max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)), ?_⟩
  intro x hx a b ha hb
  have hCm : 1024 * C0 + C1 ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) :=
    le_max_left _ _
  have hx36 : (2 : ℝ) ^ 36 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C0 ^ 2 ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hxC1 : C1 ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  obtain ⟨hY49, hYC, hlog8, hL1, hL4⟩ := window_scale_facts hε hε8 hx36 hxC
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hYpos : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by norm_num) hY49
  have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by linarith)
  have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
    Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hbR : (b : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := (Nat.cast_le.mpr hb).trans hNle
  have hsp := family_density_split
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
        i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
          i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
          lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
            (expo ε x i.2.2.2)))
    (Finset.Ioc a b)
    (lowerFourTerms ε x)
    (fun m : ℕ => lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
          Real.log (scaleZ ε x))
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
      Task308.roughIndicator (m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)) i.2.2.2)
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
      ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
          Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ))
    (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) => i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m)
    (fun m hm => by
      have hm' := Finset.mem_Ioc.mp hm
      exact Decomp514a.four_terms_eq_family ε x (by omega) (hm'.2.trans hb))
  have h1 := rough_family_window_sum ω hC0.le (Real.exp_pos _).le
    (hbb (2 * x ^ (11 / 20 + ε)) (by linarith))
    (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
        (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
        i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
          i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
          lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
            (expo ε x i.2.2.2)))
    (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
    (fun i : ℕ × ℕ × ℕ × ℕ => i.2.2.2)
    a b ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4)
    (by
      intro i hi
      obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
      obtain ⟨hb1, hb2⟩ := Decomp514a.four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
      exact ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos,
        hb1.trans ha, hb2⟩)
    hbR
    (by
      refine le_trans (Decomp514a.four_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
        (Finset.filter_subset _ _)) ?_
      have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
      have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
      have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
          Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
      exact pow_le_pow_left₀ (by linarith) (by linarith) 4)
  have h2 := hmainleaf x hxC1 a b ha hb
  have hM : (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 ≤ 512 * perronT0 x ^ 5 :=
    pow_four_le_perronT0 hx1 (by linarith) hL4
  have h3 := window_error_arith hC0.le (by positivity) (Nat.cast_nonneg b) (Real.exp_pos _).le
    (Real.exp_pos _) hM hbR (exp_decay_le_perronT0 hx1 hlog8)
  refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
    ((add_le_add (h1.trans h3) h2).trans ?_))
  have hT : 0 ≤ (perronT0 x ^ 5)⁻¹ := inv_nonneg.mpr (pow_nonneg (Real.exp_pos _).le 5)
  calc 1024 * C0 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ +
        C1 * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹
      = (1024 * C0 + C1) * (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) := by ring
    _ ≤ max (1024 * C0 + C1) (max ((2 : ℝ) ^ 36) (max (C0 ^ 2) C1)) *
          (x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right hCm (mul_nonneg hYpos.le hT)
    _ = _ := by ring


end LeanLab.BHP1997.DQ517Window
