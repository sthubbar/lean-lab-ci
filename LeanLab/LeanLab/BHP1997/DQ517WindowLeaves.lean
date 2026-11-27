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
  sorry

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
