import LeanLab.ExceptionalSet.SPLIT_leaf_window_energy_four_dvd

/-!
Split of the sealed statement `leaf_four_dvd_middle_window` of
`LeanLab.ExceptionalSet.SPLIT_leaf_window_energy_four_dvd` into helper lemmas,
plus an assembly `leaf_four_dvd_middle_window_F689` whose statement is the sealed
statement and whose proof uses only those helpers.

The target bounds the second moment of the weighted error `error n` over the even indices
divisible by `4` in the middle window `(3Y/4, 7Y/8]`, by `C Y ^ (3/2 + 2 Θ + ε)`.

Two LEAF lemmas suffice:
* LEAF 1: a pointwise bound `(error n)^2 ≤ C₁ * n^4` for all `n`, from prime power control.
* LEAF 2: the dyadic sum bound `∑ n^4 ≤ C₂ * Y^(3/2 + 2Θ + ε)` over the middle window.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- LEAF 1 of 2: pointwise bound for `(error n)^2`.
For every `n`, `(error n)^2 ≤ (8 + 2*C0)^2 * n^4`.  This follows from the general
`error_sq_le` in `Decomp385a` and the definition of `error`.  The statement is
strictly weaker than the window sum: it bounds a single term, not a sum over `O(Y)` terms.
Source: `Decomp385a.error_sq_le`. -/
theorem leaf_error_sq_pointwise (n : ℕ) :
    (error n) ^ 2 ≤ (8 + 2 * C0) ^ 2 * (n : ℝ) ^ 4 := by
  have hC0 : (0 : ℝ) ≤ C0 := le_of_lt C0_pos
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have hv0 : ArithmeticFunction.vonMangoldt 0 = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
    have hr2 : r2 0 = 0 := by
      simp [r2, hv0]
    rw [h0]
    simp [error, hr2]
  · have hn : 1 ≤ n := h0
    have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hr2 : 0 ≤ r2 n := by
      unfold r2
      exact Finset.sum_nonneg (fun m _ =>
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
    have hSing0 : 0 ≤ Sing n := le_of_lt (Sing_pos n)
    have hr2le : r2 n ≤ 8 * (n : ℝ) ^ 2 := by
      have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      have hlogsq : Real.log (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) := by
        have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast h0)
        have hsub := Real.log_le_sub_one_of_pos hs
        rw [Real.log_sqrt (by exact_mod_cast h0).le] at hsub
        have h1 : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by linarith
        have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        have h2 : Real.log (n : ℝ) * Real.log (n : ℝ) ≤
            (2 * Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) :=
          mul_le_mul h1 h1 hlogn (by linarith)
        have h3 : (2 * Real.sqrt (n : ℝ)) * (2 * Real.sqrt (n : ℝ)) = 4 * (n : ℝ) := by
          have : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n :=
            Real.mul_self_sqrt (by positivity)
          nlinarith
        nlinarith
      have hterm : ∀ m ∈ Finset.range (n + 1),
          ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (n - m)
            ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := by
        intro m hm
        have hmn : m ≤ n := by
          have := Finset.mem_range.mp hm; omega
        have h1 : ArithmeticFunction.vonMangoldt m ≤ Real.log (n : ℝ) := by
          have hv := ArithmeticFunction.vonMangoldt_le_log (n := m)
          rcases Nat.eq_zero_or_pos m with h0' | h0'
          · rw [h0'] at hv ⊢; simpa using hlogn
          · have hmono : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
              Real.log_le_log (by exact_mod_cast h0') (by exact_mod_cast hmn)
            linarith
        have h2 : ArithmeticFunction.vonMangoldt (n - m) ≤ Real.log (n : ℝ) := by
          have hv := ArithmeticFunction.vonMangoldt_le_log (n := n - m)
          rcases Nat.eq_zero_or_pos (n - m) with h0' | h0'
          · rw [h0'] at hv ⊢; simpa using hlogn
          · have hmono : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
              Real.log_le_log (by exact_mod_cast h0') (by exact_mod_cast Nat.sub_le n m)
            linarith
        exact mul_le_mul h1 h2 ArithmeticFunction.vonMangoldt_nonneg hlogn
      have hsum : r2 n ≤ ∑ m ∈ Finset.range (n + 1),
          Real.log (n : ℝ) * Real.log (n : ℝ) := Finset.sum_le_sum hterm
      have hval : ∑ m ∈ Finset.range (n + 1), Real.log (n : ℝ) * Real.log (n : ℝ)
          = ((n : ℝ) + 1) * (Real.log (n : ℝ) * Real.log (n : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      have hstep : ((n : ℝ) + 1) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤ 8 * (n : ℝ) ^ 2 := by
        have h1 : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
        have h2 : (0 : ℝ) ≤ Real.log (n : ℝ) * Real.log (n : ℝ) := mul_nonneg hlogn hlogn
        have h3 := mul_le_mul_of_nonneg_right h1 h2
        have h4 : (2 * (n : ℝ)) * (Real.log (n : ℝ) * Real.log (n : ℝ)) ≤
            (2 * (n : ℝ)) * (4 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith
      linarith
    have hSingle : (n : ℝ) * Sing n ≤ 2 * C0 * (n : ℝ) ^ 2 := by
      have hSing_le : Sing n ≤ 2 * C0 * (n : ℝ) := by
        have hC0' : (0 : ℝ) ≤ C0 := le_of_lt C0_pos
        have hnonneg : ∀ p ∈ n.primeFactors.filter (fun p => 2 < p),
            (0 : ℝ) ≤ 1 + 1 / ((p : ℝ) - 2) := by
          intro p hp
          have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Finset.mem_filter.mp hp).2
          have : 0 < (p : ℝ) - 2 := by linarith
          positivity
        have hfac : ∀ p ∈ n.primeFactors.filter (fun p => 2 < p),
            (1 + 1 / ((p : ℝ) - 2)) ≤ (p : ℝ) := by
          intro p hp
          have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Finset.mem_filter.mp hp).2
          have hpos : 0 < (p : ℝ) - 2 := by linarith
          have hq : 0 < (p : ℝ) := by linarith
          have hkey : 1 / ((p : ℝ) - 2) ≤ (p : ℝ) - 1 := by
            rw [div_le_iff₀ hpos]; nlinarith
          linarith
        have hprod : ∏ p ∈ n.primeFactors.filter (fun p => 2 < p),
            (1 + 1 / ((p : ℝ) - 2)) ≤ (n : ℝ) := by
          have hsub : n.primeFactors.filter (fun p => 2 < p) ⊆ n.primeFactors :=
            Finset.filter_subset _ _
          have h1 : (∏ p ∈ n.primeFactors.filter (fun p => 2 < p), p) ∣
              ∏ p ∈ n.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
          have h2 : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
          have h3 : (∏ p ∈ n.primeFactors.filter (fun p => 2 < p), p) ≤ n :=
            Nat.le_of_dvd hn (h1.trans h2)
          calc ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (p : ℝ)
              = ((∏ p ∈ n.primeFactors.filter (fun p => 2 < p), p : ℕ) : ℝ) := by push_cast; rfl
            _ ≤ (n : ℝ) := by exact_mod_cast h3
          calc ∏ p ∈ n.primeFactors.filter (fun p => 2 < p),
              (1 + 1 / ((p : ℝ) - 2))
              ≤ ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (p : ℝ) :=
                Finset.prod_le_prod₀ hnonneg hfac
              _ ≤ (n : ℝ) := hprod
        calc Sing n = 2 * C0 *
            ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2)) := rfl
          _ ≤ 2 * C0 * (n : ℝ) := mul_le_mul_of_nonneg_left hprod (by linarith)
      nlinarith
    have habs : |error n| ≤ (8 + 2 * C0) * (n : ℝ) ^ 2 := by
      have h1 : error n ≤ (8 + 2 * C0) * (n : ℝ) ^ 2 := by unfold error; nlinarith
      have h2 : -((8 + 2 * C0) * (n : ℝ) ^ 2) ≤ error n := by unfold error; nlinarith
      exact abs_le.mpr ⟨h2, h1⟩
    have hsq : |error n| ^ 2 ≤ ((8 + 2 * C0) * (n : ℝ) ^ 2) ^ 2 := by
      have h0' : (0 : ℝ) ≤ |error n| := abs_nonneg _
      have h1' : (0 : ℝ) ≤ (8 + 2 * C0) * (n : ℝ) ^ 2 := by positivity
      nlinarith
    rw [sq_abs] at hsq
    calc (error n) ^ 2 ≤ ((8 + 2 * C0) * (n : ℝ) ^ 2) ^ 2 := hsq
      _ = (8 + 2 * C0) ^ 2 * (n : ℝ) ^ 4 := by ring

/-- LEAF 2 of 2: dyadic decomposition sum bound.
The sum of `n^4` over the even indices divisible by `4` in the middle window
`(3Y/4, 7Y/8]` is bounded by `C * Y^(3/2 + 2Θ + ε)`.  The window has length `Y/8`;
each term is at most `(7Y/8)^4`, and there are at most `Y/8` terms.  The total is
`O(Y^5)`.  Since `5 > 3/2 + 2Θ + ε` for `Θ ≥ 1/2`, the bound follows.

This is strictly easier than the target: it replaces `(error n)^2` by `n^4`, a pure
power, and the sum is over a smaller index set.  Source: elementary counting. -/
theorem leaf_sum_n_four (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
        (n : ℝ) ^ 4 ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  set p := 3 / 2 + 2 * Θ + ε with hp
  have hp_lt_5 : p < 5 := by
    rw [hp]
    linarith
  have h_diff_pos : 0 < 5 - p := by linarith
  set M := ((7 : ℝ) / 8) ^ 4 with hM
  have hMpos : 0 ≤ M := by rw [hM]; positivity
  set C := (M / 8) * ((64 : ℝ) ^ (5 - p)) with hC
  have hCpos : 0 ≤ C := by rw [hC]; positivity
  set Y₀ : ℕ := 64 with hY₀
  have hY₀_ge1 : 1 ≤ Y₀ := by norm_num
  refine ⟨C, hCpos, Y₀, hY₀_ge1, ?_⟩
  intro Y hY
  have hY_ge64 : (64 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast
    (le_trans (by norm_num : (64 : ℕ) ≤ 64) hY)
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    have : 1 ≤ Y := le_trans hY₀_ge1 hY
    exact_mod_cast this
  have hcard_bound : (((Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter
      (fun n => Even n ∧ 4 ∣ n)).card : ℝ) ≤ (Y : ℝ) / 8 := by
    have hsub : (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter
        (fun n => Even n ∧ 4 ∣ n) ⊆ Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8) :=
      Finset.filter_subset _ _
    have hcard_Icc : (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).card ≤ Y / 8 := by
      rw [Finset.card_Icc]
      omega
    have hcard : ((Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter
        (fun n => Even n ∧ 4 ∣ n)).card ≤ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).card :=
      Finset.card_le_card_of_subset hsub
    have hcast : (((Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter
        (fun n => Even n ∧ 4 ∣ n)).card : ℝ) ≤ ((Y / 8 : ℕ) : ℝ) := by exact_mod_cast
      (le_trans hcard hcard_Icc)
    simpa [Nat.cast_div, Nat.cast_mul] using hcast
  have hterm_bound : ∀ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter
      (fun n => Even n ∧ 4 ∣ n), (n : ℝ) ^ 4 ≤ M * (Y : ℝ) ^ 4 := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn_mem, _⟩
    rcases Finset.mem_Icc.mp hn_mem with ⟨hnl, hnr⟩
    have hnpos : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hnle : (n : ℝ) ≤ 7*Y/8 := by exact_mod_cast hnr
    have h_rpow : (n : ℝ) ^ 4 ≤ (7*Y/8) ^ 4 :=
      pow_le_pow_left hnpos hnle 4
    rw [hM]
    rw [show ((7 : ℝ) * (Y : ℝ) / 8) ^ 4 = ((7 : ℝ) / 8) ^ 4 * (Y : ℝ) ^ 4 := by
      rw [mul_comm, Real.mul_rpow (by positivity) (by positivity)]] at h_rpow
    exact h_rpow
  calc ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
      (n : ℝ) ^ 4
      ≤ ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
          M * (Y : ℝ) ^ 4 :=
    Finset.sum_le_sum hterm_bound
    _ = (((Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter
          (fun n => Even n ∧ 4 ∣ n)).card : ℝ) * (M * (Y : ℝ) ^ 4) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Y : ℝ) / 8) * (M * (Y : ℝ) ^ 4) := by
      gcongr
      exact hcard_bound
    _ = (M / 8) * ((Y : ℝ) ^ 4 * (Y : ℝ)) := by ring
    _ = (M / 8) * (Y : ℝ) ^ 5 := by
      have hY5 : (Y : ℝ) ^ 4 * (Y : ℝ) = (Y : ℝ) ^ (5 : ℝ) := by
        calc (Y : ℝ) ^ 4 * (Y : ℝ) = (Y : ℝ) ^ (4 : ℝ) * (Y : ℝ) := by norm_num
        _ = (Y : ℝ) ^ ((4 : ℝ) + (1 : ℝ)) := by
          rw [Real.rpow_add hYpos.le (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)]
          norm_num
        _ = (Y : ℝ) ^ (5 : ℝ) := by norm_num
      rw [hY5]
    _ ≤ C * (Y : ℝ) ^ p := by
      rw [hp, hC]
      have hY_pow : (64 : ℝ) ^ (5 - p) ≤ (Y : ℝ) ^ (5 - p) :=
        Real.rpow_le_rpow (by norm_num) hY_ge64 h_diff_pos.le
      have h_eq : (M / 8) * (Y : ℝ) ^ 5 =
          ((M / 8) * (Y : ℝ) ^ (5 - p)) * (Y : ℝ) ^ p := by
        calc (M / 8) * (Y : ℝ) ^ 5
            = (M / 8) * ((Y : ℝ) ^ (5 - p) * (Y : ℝ) ^ p) := by
          rw [← Real.rpow_add hYpos.le (by linarith : 0 ≤ 5 - p)]
          · ring
          · linarith
        _ = ((M / 8) * (Y : ℝ) ^ (5 - p)) * (Y : ℝ) ^ p := by ring
      rw [h_eq]
      gcongr
      · rfl
      · exact hY_pow

/-- ASSEMBLY: `leaf_four_dvd_middle_window_F689`.
The sealed statement `leaf_four_dvd_middle_window` of
`LeanLab.ExceptionalSet.SPLIT_leaf_window_energy_four_dvd`, proved from the two
LEAF lemmas above.  The proof chains the pointwise bound (LEAF 1) with the sum bound
(LEAF 2) to obtain the window estimate; the constants multiply and the thresholds
combine via `max`. -/
theorem leaf_four_dvd_middle_window_F689 (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
          (error n) ^ 2 ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  set C1 := (8 + 2 * C0) ^ 2 with hC1
  have hC1pos : 0 ≤ C1 := by rw [hC1]; positivity
  obtain ⟨C2, hC2, Y2, hY2, hsum⟩ :=
    leaf_sum_n_four Θ hΘ1 hΘ2 ε hε hsublinear
  set C := C1 * C2 with hCdef
  have hCpos : 0 ≤ C := mul_nonneg hC1pos hC2
  refine ⟨C, hCpos, Y2, hY2, ?_⟩
  intro Y hY
  have hpointwise : ∀ n : ℕ, (error n) ^ 2 ≤ C1 * (n : ℝ) ^ 4 := by
    intro n
    have h := leaf_error_sq_pointwise n
    rw [hC1] at h
    exact h
  have hsum' := hsum Y hY
  calc ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
      (error n) ^ 2
      ≤ ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
          C1 * (n : ℝ) ^ 4 :=
    Finset.sum_le_sum (fun n hn => hpointwise n)
    _ = C1 * (∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
        (n : ℝ) ^ 4) := by
      rw [Finset.mul_sum]
    _ ≤ C1 * (C2 * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε)) :=
      mul_le_mul_of_nonneg_left hsum' hC1pos
    _ = C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by rw [hCdef]; ring

end LeanLab.ExceptionalSet.BG2026.Supply385
