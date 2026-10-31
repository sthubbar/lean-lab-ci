/-
P0045 Languasco, Pintz, Zaccagnini 2007: the quoted bound `R(n) ≪ n log log n`, in the weak form
`RgUpper` used by `tail_of_rgUpper`, PROVED from the lab's own Selberg sieve.

Unit U-1226, T1 PROVE, PC run 20261020T1203Z-6833.

Route, all lab or Mathlib results:
* `Rg_le_T`: `R_X(n) ≤ T(n) = Σ_{m<n} Λ(m) Λ(n − m)`.
* `T_le`: `T(n) ≤ log² n · r(n) + 2 log n (ψ(n) − θ(n))`, prime pairs plus prime power terms, the
  second sum reflected by `m ↦ n − m`.
* `r(n) ≤ C N/log² N · ∏_{p ∣ n}(1 + 1/p)` for `1 ≤ n ≤ N`: the lab's `SchnirelmannGoldbach.S1u_holds`.
* `∏_{p ∣ n}(1 + 1/p) ≤ e^{13} log y` when `ω(n) ≤ y`: the lab's `Romanov.singProd_le_log`, with
  `y = max(⌊log₂ N⌋, 2)` since `2^{ω(n)} ≤ n`.
* `ψ(n) − θ(n) ≤ 2√n log n`: Mathlib's `Chebyshev.psi_sub_theta_le`; `log N ≤ 4 N^{1/4}`.
* `rgUpper : RgUpper`, PROVED unconditional. With Eq3Reduce, `eq3_proved : Eq3`, the cited (3) of
  P0045 is now a theorem, and `mainJ_twoC0_of_two_inputs`: the repaired P0045 Theorem is
  CONDITIONAL ON `MinorBound` and the repaired (25) only.

KNOWN mathematics. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN; this is an UPPER bound for the number of representations.
-/
import Mathlib
import LeanLab.LPZ2007.Eq3Reduce
import LeanLab.SchnirelmannGoldbach.S1.Final
import LeanLab.Romanov.SingProd

namespace LeanLab.LPZ2007.RgUpperProof

open Finset Real LeanLab.LPZ2007 LeanLab.LPZ2007.Eq3Reduce LeanLab.LPZ2007.MinorBessel
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- `T(n) = Σ_{m<n} Λ(m) Λ(n − m)`. -/
def T (n : ℕ) : ℝ := ∑ m ∈ range n, Λ m * Λ (n - m)

theorem vm_nonneg (j : ℕ) : 0 ≤ Λ j := ArithmeticFunction.vonMangoldt_nonneg

theorem vm_le_log {j n : ℕ} (hj : j ≤ n) : Λ j ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp only [ArithmeticFunction.map_zero]; exact Real.log_natCast_nonneg n
  · exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hj))

theorem Rg_le_T (X : ℝ) (n : ℕ) : Rg X n ≤ T n := by
  unfold Rg T
  have hg : ∀ m1 ∈ Icc 1 ⌊X⌋₊, (∑ m2 ∈ Icc 1 ⌊X⌋₊,
      if m1 + m2 = n then Λ m1 * Λ m2 else (0 : ℝ)) ≤
        if m1 < n then Λ m1 * Λ (n - m1) else 0 := by
    intro m1 _
    split_ifs with hlt
    · calc _ ≤ ∑ m2 ∈ Icc 1 ⌊X⌋₊, if m2 = n - m1 then Λ m1 * Λ (n - m1) else (0 : ℝ) := by
            refine sum_le_sum fun m2 _ => ?_
            by_cases h : m1 + m2 = n
            · rw [if_pos h, if_pos (by omega), show m2 = n - m1 by omega]
            · rw [if_neg h]
              split_ifs
              · exact mul_nonneg (vm_nonneg _) (vm_nonneg _)
              · exact le_refl 0
        _ ≤ Λ m1 * Λ (n - m1) := by
            rw [sum_ite_eq']
            split_ifs
            · exact le_refl _
            · exact mul_nonneg (vm_nonneg _) (vm_nonneg _)
    · apply le_of_eq
      refine sum_eq_zero fun m2 hm2 => ?_
      simp only [mem_Icc] at hm2
      rw [if_neg (by omega)]
  calc _ ≤ ∑ m1 ∈ Icc 1 ⌊X⌋₊, (if m1 < n then Λ m1 * Λ (n - m1) else 0) := sum_le_sum hg
    _ = ∑ m1 ∈ (Icc 1 ⌊X⌋₊).filter (· < n), Λ m1 * Λ (n - m1) := (sum_filter _ _).symm
    _ ≤ ∑ m ∈ range n, Λ m * Λ (n - m) :=
        sum_le_sum_of_subset_of_nonneg (fun m hm => by simp only [mem_filter] at hm; simp [hm.2])
          (fun _ _ _ => mul_nonneg (vm_nonneg _) (vm_nonneg _))

/-- The non-prime part `Σ_{1 ≤ j ≤ n, j not prime} Λ(j)` as `ψ(n) − θ(n)`. -/
theorem sum_notPrime_eq (n : ℕ) :
    ∑ j ∈ range (n + 1), (if ¬ j.Prime then Λ j else 0) = Chebyshev.psi n - Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter,
    sum_range_succ_eq_Icc _ (by simp), ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

theorem T_le (n : ℕ) : T n ≤ Real.log n ^ 2 * (SchnirelmannGoldbach.r n : ℝ) +
    2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n) := by
  set G : ℕ → ℝ := fun j => if ¬ j.Prime then Λ j else 0 with hG
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hpt : ∀ m ∈ range n, Λ m * Λ (n - m) ≤
      (if m.Prime ∧ (n - m).Prime then Real.log n ^ 2 else 0) + Real.log n * G m +
        Real.log n * G (n - m) := by
    intro m hm
    have hmn : m ≤ n := (mem_range.1 hm).le
    have h1 := vm_le_log hmn
    have h2 := vm_le_log (Nat.sub_le n m)
    have hG0 : ∀ j, 0 ≤ G j := fun j => by simp only [hG]; split_ifs <;> simp
    by_cases hp : m.Prime
    · by_cases hq : (n - m).Prime
      · rw [if_pos ⟨hp, hq⟩, sq]
        have := mul_le_mul h1 h2 (vm_nonneg _) hlog
        nlinarith [hG0 m, hG0 (n - m)]
      · rw [if_neg (fun h => hq h.2)]
        have hGq : G (n - m) = Λ (n - m) := by simp only [hG]; rw [if_pos hq]
        rw [hGq]
        have := mul_le_mul_of_nonneg_right h1 (vm_nonneg (n - m))
        nlinarith [hG0 m]
    · rw [if_neg (fun h => hp h.1)]
      have hGp : G m = Λ m := by simp only [hG]; rw [if_pos hp]
      rw [hGp]
      have := mul_le_mul_of_nonneg_left h2 (vm_nonneg m)
      nlinarith [hG0 (n - m)]
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  -- prime pairs
  have hpairs : ∑ m ∈ range n, (if m.Prime ∧ (n - m).Prime then Real.log n ^ 2 else 0) =
      Real.log n ^ 2 * (SchnirelmannGoldbach.r n : ℝ) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rfl
  -- the two prime power sums
  have hG1 : ∑ m ∈ range n, G m ≤ Chebyshev.psi n - Chebyshev.theta n := by
    rw [← sum_notPrime_eq, sum_range_succ]
    have : 0 ≤ G n := by simp only [hG]; split_ifs <;> simp
    linarith
  have hG2 : ∑ m ∈ range n, G (n - m) ≤ Chebyshev.psi n - Chebyshev.theta n := by
    have hrefl := Finset.sum_range_reflect (fun j => G (j + 1)) n
    have hcongr : ∑ j ∈ range n, G (n - 1 - j + 1) = ∑ m ∈ range n, G (n - m) :=
      sum_congr rfl fun j hj => by
        have := mem_range.1 hj
        congr 1; omega
    rw [hcongr] at hrefl
    rw [hrefl, ← sum_notPrime_eq, sum_range_succ']
    have h0 : (if ¬ Nat.Prime 0 then Λ 0 else (0 : ℝ)) = 0 := by simp
    rw [h0, add_zero]
  calc T n ≤ _ := hsum
    _ ≤ Real.log n ^ 2 * (SchnirelmannGoldbach.r n : ℝ) +
          Real.log n * (Chebyshev.psi n - Chebyshev.theta n) +
          Real.log n * (Chebyshev.psi n - Chebyshev.theta n) := by
        rw [hpairs]
        gcongr
    _ = _ := by ring

/-- `log log N ≥ 1` for `N ≥ 16`. -/
theorem loglog_ge_one {N : ℕ} (hN : 16 ≤ N) : 1 ≤ Real.log (Real.log N) := by
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have h16 : Real.exp 1 < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    have := Real.exp_one_lt_d9
    push_cast; linarith
  have hl : Real.exp 1 ≤ Real.log N := le_trans h16.le (Real.log_le_log (by norm_num) hNr)
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) hl

/-- **The quoted Goldbach upper bound, PROVED unconditional**: `R_X(n) ≤ C N log log N` for
`n ≤ N`, `N ≥ 16`. -/
theorem rgUpper : RgUpper := by
  obtain ⟨C, hC⟩ := SchnirelmannGoldbach.S1u_holds
  refine ⟨|C| * (Real.exp 13 * (Real.log 5 + 1)) + 64, fun X n N hn hN => ?_⟩
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hll1 := loglog_ge_one hN
  set LL := Real.log (Real.log N) with hLL
  have hRg := Rg_le_T X n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : T 0 = 0 := by simp [T]
    rw [this] at hRg
    have : 0 ≤ (|C| * (Real.exp 13 * (Real.log 5 + 1)) + 64) * N * LL := by
      have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
      have : 0 ≤ LL := by linarith
      positivity
    linarith
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnr
  have hlognN : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  -- the sieve part
  have hS := hC N (by omega) n (by simp only [mem_Icc]; omega)
  set sp := SchnirelmannGoldbach.singProd n with hsp
  have hr0 : (0 : ℝ) ≤ (SchnirelmannGoldbach.r n : ℝ) := Nat.cast_nonneg _
  have hpart1 : Real.log n ^ 2 * (SchnirelmannGoldbach.r n : ℝ) ≤ |C| * N * sp := by
    have hsp0 : 0 ≤ sp := by
      rw [hsp]; unfold SchnirelmannGoldbach.singProd
      exact prod_nonneg fun p _ => by positivity
    calc Real.log n ^ 2 * (SchnirelmannGoldbach.r n : ℝ)
        ≤ Real.log N ^ 2 * (SchnirelmannGoldbach.r n : ℝ) := by gcongr
      _ ≤ Real.log N ^ 2 * (C * N / Real.log N ^ 2 * sp) := by gcongr
      _ = C * N * sp := by field_simp
      _ ≤ |C| * N * sp := by gcongr; exact le_abs_self C
  -- the singular product
  set y : ℕ := max (Nat.log 2 N) 2 with hy
  have hω : n.primeFactors.card ≤ y := by
    have h1 : n.primeFactors.card ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by norm_num) (Romanov.two_pow_card_le n (by omega))
    exact h1.trans ((Nat.log_mono_right hn).trans (le_max_left _ _))
  have hsp_le : sp ≤ Real.exp 13 * Real.log y := Romanov.singProd_le_log n y (le_max_right _ _) hω
  have hy_le : (y : ℝ) ≤ 5 * Real.log N := by
    have hl2 : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
      have hp : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
      have : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N :=
        Real.log_le_log (by positivity) (by exact_mod_cast hp)
      rwa [Real.log_pow] at this
    have hlog2 := Real.log_two_gt_d9
    have hlog16 : 2 ≤ Real.log N := by
      have : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
      linarith
    have hNl : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    rw [hy]
    push_cast
    rcases le_total (Nat.log 2 N) 2 with h | h
    · rw [max_eq_right (by exact_mod_cast h)]; linarith
    · rw [max_eq_left (by exact_mod_cast h)]; linarith
  have hlogy : Real.log y ≤ (Real.log 5 + 1) * LL := by
    have hy0 : (0 : ℝ) < y := by
      have : 2 ≤ y := le_max_right _ _
      exact_mod_cast (show 0 < y by omega)
    have h1 : Real.log y ≤ Real.log (5 * Real.log N) := Real.log_le_log hy0 hy_le
    rw [Real.log_mul (by norm_num) hlogN.ne'] at h1
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    nlinarith
  -- the prime power part
  have hpt := Chebyshev.psi_sub_theta_le (x := (n : ℝ)) hnr
  have hlog4 : Real.log N ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith [show (N : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (N : ℝ) ^ (1 / 4 : ℝ) by ring]
  have hq : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hsqrtN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hpart2 : 2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n) ≤ 64 * N * LL := by
    have hsn : Real.sqrt n ≤ Real.sqrt N := Real.sqrt_le_sqrt hnN
    have hpt' : Chebyshev.psi n - Chebyshev.theta n ≤ 2 * Real.sqrt N * Real.log N := by
      calc _ ≤ 2 * Real.sqrt n * Real.log n := hpt
        _ ≤ 2 * Real.sqrt N * Real.log N := by gcongr
    have hl2 : Real.log N ^ 2 ≤ 16 * Real.sqrt N := by
      calc Real.log N ^ 2 ≤ (4 * (N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hlogN.le hlog4 2
        _ = 16 * Real.sqrt N := by rw [mul_pow, hq]; norm_num
    have hd0 : 0 ≤ Chebyshev.psi n - Chebyshev.theta n := by
      have := Chebyshev.theta_le_psi (n : ℝ); linarith
    calc 2 * Real.log n * (Chebyshev.psi n - Chebyshev.theta n)
        ≤ 2 * Real.log N * (2 * Real.sqrt N * Real.log N) := by gcongr
      _ = 4 * Real.sqrt N * Real.log N ^ 2 := by ring
      _ ≤ 4 * Real.sqrt N * (16 * Real.sqrt N) := by gcongr
      _ = 64 * N := by rw [show 4 * Real.sqrt N * (16 * Real.sqrt N) = 64 * (Real.sqrt N * Real.sqrt N) by ring, hsqrtN]
      _ ≤ 64 * N * LL := by nlinarith
  have hC0 : 0 ≤ |C| := abs_nonneg C
  have hspLL : sp ≤ Real.exp 13 * ((Real.log 5 + 1) * LL) :=
    hsp_le.trans (mul_le_mul_of_nonneg_left hlogy (Real.exp_pos 13).le)
  calc Rg X n ≤ T n := hRg
    _ ≤ _ := T_le n
    _ ≤ |C| * N * sp + 64 * N * LL := add_le_add hpart1 hpart2
    _ ≤ |C| * N * (Real.exp 13 * ((Real.log 5 + 1) * LL)) + 64 * N * LL := by gcongr
    _ = (|C| * (Real.exp 13 * (Real.log 5 + 1)) + 64) * N * LL := by ring

/-- **(3) of P0045, PROVED unconditional.** -/
theorem eq3_proved : Eq3 := eq3_of_rgUpper rgUpper

/-- **The repaired P0045 Theorem on `J(X)`**, constant `2c₀ C(k, N)`, CONDITIONAL ON two inputs
only: the minor arc sup bound `MinorBound`, from the paper's Lemma 6.3, and the repaired (25),
the major arc analysis. -/
theorem mainJ_twoC0_of_two_inputs (hm : MinorBound)
    (h25 : Eq25C (fun k N => twoC0 * Ckn k N)) : MainJ_twoC0 :=
  mainJ_twoC0_of_inputs rgUpper hm h25

end

end LeanLab.LPZ2007.RgUpperProof
