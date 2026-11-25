import LeanLab.Halupczok2012.Statements
import LeanLab.PNTPort.LargeSieve.MontgomeryBT

/-!
# Proof of the leaf `Split398aMinor.leaf_B1_bt`

Source: A. Perelli and J. Pintz, On the exceptional set for Goldbach's problem in short
intervals, J. London Math. Soc. 47, 1993, page 44 display 3, here PP1993. Display 3 uses
the short interval bound `∑_{N-Y<h≤N} Λ(h) ≪ Y` for `Y ≥ N^(7/12+ε)` and Chebyshev's bound
`∑_{j≤Y} Λ(j) ≪ Y` for the second polynomial.

Route, with no cited input left:
* Chebyshev's bound is `Chebyshev.psi_le_const_mul_self` of Mathlib.
* In the short interval the primes contribute at most `log N` times their number, and the
  number of primes is bounded by the lab's proved Brun Titchmarsh inequality from Montgomery's
  sieve, `PNTPort.LargeSieve.brun_titchmarsh_montgomery`, with `Q = ⌊√Y⌋`. Since
  `Y ≥ N^(7/12)`, `log N ≤ (12/7) log Y`, so this part is `≪ Y`.
* The prime powers contribute at most `ψ(N) - θ(N) ≤ 2 √N log N` by
  `Chebyshev.psi_sub_theta_le`, and `√N log N ≤ 12 N^(7/12) ≤ 12 Y`.
The constant `c` does not depend on `ε`, as the leaf requires.

Session S135 burst-20261122. AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.B1btChebyshev

open Finset Real Chebyshev
open scoped Classical ArithmeticFunction.vonMangoldt

/-- For `X ≥ 0`, the paper's integer interval `]X, X+R]` lies in `Ioc ⌊X⌋ ⌊X+R⌋`. -/
theorem kRange_subset_Ioc {X R : ℝ} (hX : 0 ≤ X) :
    LeanLab.Halupczok2012.kRange X R ⊆ Ioc ⌊X⌋₊ ⌊X + R⌋₊ := by
  intro k hk
  simp only [LeanLab.Halupczok2012.kRange, mem_filter] at hk
  obtain ⟨-, h1, h2⟩ := hk
  refine mem_Ioc.2 ⟨?_, Nat.le_floor h2⟩
  by_contra hle
  push_neg at hle
  have : (k : ℝ) ≤ X := le_trans (by exact_mod_cast hle) (Nat.floor_le hX)
  linarith

/-- The sum of `Λ` over the paper's interval `]X, X+R]` is at most the sum over
`Ioc ⌊X⌋ ⌊X+R⌋`, as `Λ ≥ 0`. -/
theorem sum_kRange_le {X R : ℝ} (hX : 0 ≤ X) :
    ∑ h ∈ LeanLab.Halupczok2012.kRange X R, Λ h ≤ ∑ h ∈ Ioc ⌊X⌋₊ ⌊X + R⌋₊, Λ h :=
  sum_le_sum_of_subset_of_nonneg (kRange_subset_Ioc hX)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- PP1993 p. 44 display 3, Chebyshev's bound for the second polynomial:
`∑_{0<j≤Y} Λ(j) ≤ (log 4 + 4) Y`. -/
theorem sum_kRange_zero_le {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ j ∈ LeanLab.Halupczok2012.kRange 0 Y, Λ j ≤ (Real.log 4 + 4) * Y := by
  have h := sum_kRange_le (X := 0) (R := Y) le_rfl
  simp only [Nat.floor_zero, zero_add] at h
  exact h.trans (psi_le_const_mul_self hY)

/-- Prime powers in a sub interval of `]0, N]`: the sum of `Λ` over non primes of
`Ioc a b` with `b = ⌊N⌋` is at most `ψ(N) - θ(N) ≤ 2 √N log N`. -/
theorem sum_Ioc_not_prime_le {N : ℝ} (hN : 1 ≤ N) (a : ℕ) :
    ∑ h ∈ (Ioc a ⌊N⌋₊).filter (fun h => ¬ h.Prime), Λ h ≤ 2 * √N * Real.log N := by
  calc ∑ h ∈ (Ioc a ⌊N⌋₊).filter (fun h => ¬ h.Prime), Λ h
      ≤ ∑ h ∈ (Ioc 0 ⌊N⌋₊).filter (fun h => ¬ h.Prime), Λ h := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro h hh
          simp only [mem_filter, mem_Ioc] at hh ⊢
          exact ⟨⟨by omega, hh.1.2⟩, hh.2⟩
        · exact fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ψ N - θ N := (psi_sub_theta_eq_sum_not_prime N).symm
    _ ≤ 2 * √N * Real.log N := psi_sub_theta_le hN

/-- The primes of `Ioc a ⌊N⌋` contribute at most `log N` times their number. -/
theorem sum_Ioc_prime_le {N : ℝ} (hN : 1 ≤ N) (a : ℕ) :
    ∑ h ∈ (Ioc a ⌊N⌋₊).filter Nat.Prime, Λ h ≤
      (((Ioc a ⌊N⌋₊).filter Nat.Prime).card : ℝ) * Real.log N := by
  rw [← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro p hp
  simp only [mem_filter, mem_Ioc] at hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
  have hpN : (p : ℝ) ≤ N := (Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by linarith))
  exact Real.log_le_log hp0 hpN

/-- Brun Titchmarsh with `Q = ⌊√Y⌋`, from the lab's proved Montgomery sieve bound: the number
of primes in `Ioc a b` with `b - a ≤ Y + 1` and `Y > 1` is at most
`√Y + 2 (3 Y + 1) / log Y`. -/
theorem card_primes_le {Y : ℝ} (hY : 1 < Y) (a b : ℕ) (hab : a ≤ b)
    (hlen : ((b - a : ℕ) : ℝ) ≤ Y + 1) :
    (((Ioc a b).filter Nat.Prime).card : ℝ) ≤ √Y + 2 * (3 * Y + 1) / Real.log Y := by
  set Q : ℕ := ⌊√Y⌋₊ with hQdef
  have hsY : 1 < √Y := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one hY
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hsY.le)
  have hQle : (Q : ℝ) ≤ √Y := Nat.floor_le (Real.sqrt_nonneg _)
  have hQlt : √Y < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hBT := LeanLab.PNTPort.LargeSieve.brun_titchmarsh_montgomery a (b - a) Q hQ1
  rw [Nat.add_sub_cancel' hab] at hBT
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hQ2 : (Q : ℝ) ^ 2 ≤ Y := by
    calc (Q : ℝ) ^ 2 ≤ √Y ^ 2 := by gcongr
      _ = Y := Real.sq_sqrt (by linarith)
  -- log (Q + 1) ≥ log √Y = log Y / 2
  have hlogQ : Real.log Y / 2 ≤ Real.log ((Q : ℝ) + 1) := by
    have : Real.log √Y = Real.log Y / 2 := by
      rw [Real.log_sqrt (by linarith)]
    rw [← this]
    exact Real.log_le_log (by linarith) hQlt.le
  have hnum : 0 ≤ ((b - a : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2 := by positivity
  have hfrac : (((b - a : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1) ≤
      2 * (3 * Y + 1) / Real.log Y := by
    calc (((b - a : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2) / Real.log ((Q : ℝ) + 1)
        ≤ (((b - a : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2) / (Real.log Y / 2) :=
          div_le_div_of_nonneg_left hnum (by positivity) hlogQ
      _ = 2 * (((b - a : ℕ) : ℝ) + 2 * (Q : ℝ) ^ 2) / Real.log Y := by
          field_simp
      _ ≤ 2 * (3 * Y + 1) / Real.log Y := by
          apply div_le_div_of_nonneg_right _ hlogY.le
          linarith
  linarith

/-- The statement of `Split398aMinor.leaf_B1_bt`, PP1993 p. 44 display 3, PROVED with
`c = 50`: the short interval bound from Brun Titchmarsh and the prime power estimate, and
Chebyshev's bound for the second sum. -/
theorem leaf_B1_bt : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N0 : ℝ, ∀ N Y : ℝ,
    N0 ≤ N → N ^ (7 / 12 + ε) ≤ Y → Y ≤ N →
    (∑ h ∈ LeanLab.Halupczok2012.kRange (N - Y) Y, Λ h) ≤ c * Y ∧
      (∑ j ∈ LeanLab.Halupczok2012.kRange 0 Y, Λ j) ≤ c * Y := by
  refine ⟨50, by norm_num, fun ε hε => ⟨2, fun N Y hN hY hYN => ?_⟩⟩
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  -- Y ≥ N^(7/12)
  have hY712 : N ^ (7 / 12 : ℝ) ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hY
  have hY1 : 1 < Y := by
    have : (1 : ℝ) < N ^ (7 / 12 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
    linarith
  have hY0 : 0 ≤ Y := by linarith
  have hlog4 : Real.log 4 < 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  refine ⟨?_, ?_⟩
  swap
  · calc _ ≤ (Real.log 4 + 4) * Y := sum_kRange_zero_le hY0
      _ ≤ 50 * Y := by nlinarith
  -- the short interval
  have hNY : 0 ≤ N - Y := by linarith
  have hsub := sum_kRange_le (X := N - Y) (R := Y) hNY
  rw [show N - Y + Y = N by ring] at hsub
  set a := ⌊N - Y⌋₊
  set b := ⌊N⌋₊
  have hab : a ≤ b := Nat.floor_le_floor (by linarith)
  have hsplit := (sum_filter_add_sum_filter_not (Ioc a b) Nat.Prime (fun h => Λ h)).symm
  have hP := sum_Ioc_prime_le hN1 a
  have hNP := sum_Ioc_not_prime_le hN1 a
  -- length of the interval
  have hlen : ((b - a : ℕ) : ℝ) ≤ Y + 1 := by
    rw [Nat.cast_sub hab]
    have h1 : (b : ℝ) ≤ N := Nat.floor_le (by linarith)
    have h2 : N - Y < (a : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hcard := card_primes_le hY1 a b hab hlen
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  -- log N ≤ (12/7) log Y
  have hlogNY : Real.log N ≤ 12 / 7 * Real.log Y := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hY712
    rw [Real.log_rpow hN0] at this
    linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  -- log N ≤ (24/7) N^(7/24) ≤ (24/7) √Y
  have hlogN_sqrtY : Real.log N ≤ 24 / 7 * √Y := by
    have h1 := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 7 / 24 by norm_num)
    have h2 : N ^ (7 / 24 : ℝ) ≤ √Y := by
      rw [show (7 / 24 : ℝ) = (7 / 12) * (1 / 2) by norm_num, Real.rpow_mul hN0.le,
        Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow (by positivity) hY712 (by norm_num)
    calc Real.log N ≤ N ^ (7 / 24 : ℝ) / (7 / 24) := h1
      _ = 24 / 7 * N ^ (7 / 24 : ℝ) := by ring
      _ ≤ 24 / 7 * √Y := by gcongr
  -- √N log N ≤ 12 N^(7/12) ≤ 12 Y
  have hsqrtN : √N * Real.log N ≤ 12 * Y := by
    have h1 := Real.log_le_rpow_div hN0.le (show (0 : ℝ) < 1 / 12 by norm_num)
    have h2 : √N * N ^ (1 / 12 : ℝ) = N ^ (7 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]; norm_num
    calc √N * Real.log N ≤ √N * (N ^ (1 / 12 : ℝ) / (1 / 12)) := by
          gcongr
      _ = 12 * (√N * N ^ (1 / 12 : ℝ)) := by ring
      _ = 12 * N ^ (7 / 12 : ℝ) := by rw [h2]
      _ ≤ 12 * Y := by gcongr
  have hsY : √Y ≤ Y := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsqrtY0 : 0 ≤ √Y := Real.sqrt_nonneg _
  -- the prime part: card * log N ≤ (√Y + 2(3Y+1)/log Y) log N ≤ (24/7) Y + (24/7)(3Y+1)
  have hprime : (((Ioc a b).filter Nat.Prime).card : ℝ) * Real.log N ≤ 24 / 7 * Y +
      24 / 7 * (3 * Y + 1) := by
    calc (((Ioc a b).filter Nat.Prime).card : ℝ) * Real.log N
        ≤ (√Y + 2 * (3 * Y + 1) / Real.log Y) * Real.log N := by gcongr
      _ = √Y * Real.log N + 2 * (3 * Y + 1) * (Real.log N / Real.log Y) := by ring
      _ ≤ √Y * (24 / 7 * √Y) + 2 * (3 * Y + 1) * (12 / 7) := by
          have hq : Real.log N / Real.log Y ≤ 12 / 7 := by
            rw [div_le_iff₀ hlogY]; linarith
          have h1 : √Y * Real.log N ≤ √Y * (24 / 7 * √Y) :=
            mul_le_mul_of_nonneg_left hlogN_sqrtY hsqrtY0
          have h2 : 2 * (3 * Y + 1) * (Real.log N / Real.log Y) ≤ 2 * (3 * Y + 1) * (12 / 7) :=
            mul_le_mul_of_nonneg_left hq (by linarith)
          linarith
      _ = 24 / 7 * Y + 24 / 7 * (3 * Y + 1) := by
          rw [show √Y * (24 / 7 * √Y) = 24 / 7 * (√Y * √Y) by ring,
            Real.mul_self_sqrt hY0]
          ring
  calc ∑ h ∈ LeanLab.Halupczok2012.kRange (N - Y) Y, Λ h
      ≤ ∑ h ∈ Ioc a b, Λ h := hsub
    _ = ∑ h ∈ (Ioc a b).filter Nat.Prime, Λ h +
          ∑ h ∈ (Ioc a b).filter (fun h => ¬ h.Prime), Λ h := hsplit
    _ ≤ (24 / 7 * Y + 24 / 7 * (3 * Y + 1)) + 2 * (12 * Y) := by
        have : 2 * √N * Real.log N ≤ 2 * (12 * Y) := by nlinarith
        linarith
    _ ≤ 50 * Y := by nlinarith

end LeanLab.Halupczok2012.B1btChebyshev
