import LeanLab.LZCesaroShort.Sec5Envelope
import LeanLab.PNTPort.StrongPNT.Bridge

/-!
# An unconditional Section 5 bound from the available PNT

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, page 11, Section 5.
The printed rate uses the Vinogradov Korobov error term.
This new name uses the weaker de la Vallee Poussin rate already proved in the lab.
It does not prove the stronger Section 5 rate recorded in STATEMENTS.md.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped Chebyshev

/-- The strong PNT error is uniform over all natural arguments at most twice N. -/
theorem psi_uniform_up_to_twice : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, n ≤ 2 * N →
      |ψ (n : ℝ) - n| ≤ C * N * Real.exp (-c * Real.sqrt (Real.log N)) := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  let N₀ : ℕ := max 4 ⌈Real.exp (c ^ 2)⌉₊
  let C₀ : ℝ := Real.log 4 + 5
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨c / 2, by positivity, C₀ + 2 * |K|, by positivity,
    N₀, fun N hN n hn => ?_⟩
  have hN4 : 4 ≤ N := le_trans (le_max_left _ _) hN
  have hN4r : (4 : ℝ) ≤ N := by exact_mod_cast hN4
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2N : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn
  have hSpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hS2 : 2 ≤ Real.sqrt (N : ℝ) := by
    have := Real.sqrt_le_sqrt hN4r
    norm_num at this
    exact this
  let L := Real.sqrt (Real.log N)
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hLsq : L ^ 2 = Real.log N := Real.sq_sqrt hlog0
  have hexpN : Real.exp (c ^ 2) ≤ N := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast le_trans (le_max_right _ _) hN
  have hc2 : c ^ 2 ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr hexpN
  have hcL : c ≤ L := by
    calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc.le).symm
      _ ≤ L := Real.sqrt_le_sqrt hc2
  have hsmall : Real.sqrt (N : ℝ) ≤ N * Real.exp (-(c / 2) * L) := by
    calc
      Real.sqrt (N : ℝ) = Real.exp (Real.log N / 2) := by
        rw [← Real.log_sqrt hN0.le, Real.exp_log hSpos]
      _ ≤ Real.exp (Real.log N - c / 2 * L) := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right hcL hL0
        nlinarith
      _ = N * Real.exp (-(c / 2) * L) := by
        rw [show Real.log N - c / 2 * L = Real.log N + (-(c / 2) * L) by ring,
          Real.exp_add, Real.exp_log hN0]
  have hNe : 0 ≤ (N : ℝ) * Real.exp (-(c / 2) * L) := by positivity
  rcases le_or_gt (n : ℝ) (Real.sqrt (N : ℝ)) with hns | hns
  · have hpsi := Chebyshev.psi_le_const_mul_self hn0
    have hpsi0 := Chebyshev.psi_nonneg (n : ℝ)
    have hlin : |ψ (n : ℝ) - n| ≤ C₀ * n := by
      rw [abs_le]
      dsimp [C₀]
      have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      constructor <;> nlinarith
    calc
      |ψ (n : ℝ) - n| ≤ C₀ * n := hlin
      _ ≤ C₀ * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_left hns hC₀
      _ ≤ C₀ * (N * Real.exp (-(c / 2) * L)) := mul_le_mul_of_nonneg_left hsmall hC₀
      _ ≤ (C₀ + 2 * |K|) * N * Real.exp (-(c / 2) * L) := by
        nlinarith [mul_nonneg (abs_nonneg K) hNe]
  · have hn2 : (2 : ℝ) ≤ n := le_trans hS2 hns.le
    have hnp : (0 : ℝ) < n := by linarith
    have hlogn := Real.log_le_log hSpos hns.le
    rw [Real.log_sqrt hN0.le] at hlogn
    have hroot : L / 2 ≤ Real.sqrt (Real.log n) := by
      calc L / 2 = Real.sqrt ((L / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log n) := Real.sqrt_le_sqrt (by nlinarith)
    have he : Real.exp (-c * Real.sqrt (Real.log n)) ≤ Real.exp (-(c / 2) * L) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hroot hc.le
      nlinarith
    have hb := hK n hn2
    have hKa : K * n * Real.exp (-c * Real.sqrt (Real.log n))
        ≤ |K| * n * Real.exp (-c * Real.sqrt (Real.log n)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self K) hn0) (Real.exp_pos _).le
    calc
      |ψ (n : ℝ) - n| ≤ |K| * n * Real.exp (-c * Real.sqrt (Real.log n)) := hb.trans hKa
      _ ≤ |K| * (2 * N) * Real.exp (-(c / 2) * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn2N (abs_nonneg K)) he
          (Real.exp_pos _).le (by positivity)
      _ ≤ (C₀ + 2 * |K|) * N * Real.exp (-(c / 2) * L) := by
        nlinarith [mul_nonneg hC₀ hNe]

/-- An unconditional Section 5 variant with the available square root logarithm decay. -/
theorem sec5_weak_pnt : ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, ∃ N₀ : ℕ,
    ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → H ≤ N →
      ‖ZH N H / (H : ℂ)‖ ≤ K *
        (H * N * Real.exp (-c * Real.sqrt (Real.log N)) + N) := by
  obtain ⟨c, hc, C, hC, Np, hp⟩ := psi_uniform_up_to_twice
  obtain ⟨Nz, K, hK, hz⟩ := zero_term_bound_of_psi_window
  refine ⟨c, hc, C + K, max Np Nz, fun N H hN hH hHN => ?_⟩
  have hpN := hp N (le_trans (le_max_left _ _) hN)
  have hwin : ∀ n ∈ Icc (N - H) (N + H),
      |ψ (n : ℝ) - n| ≤ C * N * Real.exp (-c * Real.sqrt (Real.log N)) := by
    intro n hn
    exact hpN n (by have := (mem_Icc.mp hn).2; omega)
  have hb := hz N H (le_trans (le_max_right _ _) hN) hH hHN
    (C * N * Real.exp (-c * Real.sqrt (Real.log N))) (by positivity) hwin
  have hA : 0 ≤ (H : ℝ) * N * Real.exp (-c * Real.sqrt (Real.log N)) := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show C ≤ C + K by linarith) hA
  have h2 := mul_le_mul_of_nonneg_right (show K ≤ C + K by linarith) (Nat.cast_nonneg (α := ℝ) N)
  nlinarith

end LeanLab.LZCesaroShort
