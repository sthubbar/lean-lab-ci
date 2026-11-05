import LeanLab.HardyLittlewood1923.Decomp354d
import LeanLab.HardyLittlewood1923.Decomp354g
import LeanLab.HardyLittlewood1923.Decomp354h

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 23 equation 3.123.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354e

open Real
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

/-- P0004 page 23 equation 3.123, before the Farey width substitution.
For eta less than abs theta and abs theta at most two pi, the angular factor
is bounded by a constant times sqrt q times sqrt abs theta times
n to Theta plus one half times log n. This is the displayed cancellation
of the powers of abs theta. No Farey membership is assumed. -/
theorem large_angle_factor {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ q : ℕ, 1 ≤ q →
      ∀ θ : ℝ, 1 / (n : ℝ) < |θ| → |θ| ≤ 2 * π →
        angularTerm Θ n q θ ≤
          C * (Real.sqrt q * Real.sqrt |θ|) * (n : ℝ) ^ (Θ + 1 / 2) * Real.log n := by
  let K : ℝ := Real.log (4 * π + 2) + 1
  have hK : 0 ≤ K := by
    have : 0 ≤ Real.log (4 * π + 2) := Real.log_nonneg (by linarith [Real.pi_pos])
    dsimp [K]
    linarith
  refine ⟨(2 : ℝ) ^ (Θ + 1 / 2) * K, by positivity, fun n hn q hq θ hθ hθbound => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht : 0 < |θ| := lt_trans (by positivity) hθ
  have hg0 := angularGap_pos (by omega : 0 < n) θ
  have hg := Decomp354g.large_gap_lower (by omega : 0 < n) hθ
  have hy := Decomp354g.localY_abs_theta_le n θ
  have hp : ‖localY n θ‖ ^ (-Θ) ≤ |θ| ^ (-Θ) :=
    Real.rpow_le_rpow_of_nonpos ht hy (by linarith)
  have hgap : (angularGap n θ) ^ (-Θ - 1 / 2) ≤
      (2 * (n : ℝ) * |θ|) ^ (Θ + 1 / 2) := by
    calc
      _ ≤ (1 / (2 * (n : ℝ) * |θ|)) ^ (-Θ - 1 / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hg (by linarith)
      _ = _ := by
        rw [show -Θ - 1 / 2 = -(Θ + 1 / 2) by ring, one_div,
          ← Real.rpow_neg_eq_inv_rpow]
        simp
  have hinv : 1 / angularGap n θ ≤ 2 * (n : ℝ) * |θ| := by
    have := one_div_le_one_div_of_le (by positivity : 0 < 1 / (2 * (n : ℝ) * |θ|)) hg
    simpa using this
  have hlog : Real.log (1 / angularGap n θ + 2) ≤ K * Real.log n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hlogn : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
    have harg : 1 / angularGap n θ + 2 ≤ (4 * π + 2) * n := by
      have hm := mul_le_mul_of_nonneg_left hθbound (show 0 ≤ 2 * (n : ℝ) by positivity)
      nlinarith
    calc
      _ ≤ Real.log ((4 * π + 2) * n) := Real.log_le_log (by positivity) harg
      _ = Real.log (4 * π + 2) + Real.log n := Real.log_mul (by positivity) hnR.ne'
      _ ≤ K * Real.log n := by
        have hL : 0 ≤ Real.log (4 * π + 2) := Real.log_nonneg (by linarith [Real.pi_pos])
        have := mul_le_mul_of_nonneg_left hlogn hL
        dsimp [K]
        nlinarith
  have hlog0 : 0 ≤ Real.log (1 / angularGap n θ + 2) := Real.log_nonneg (by
    have : 0 < 1 / angularGap n θ := by positivity
    linarith)
  have hpower : |θ| ^ (-Θ) * (2 * (n : ℝ) * |θ|) ^ (Θ + 1 / 2) =
      (2 : ℝ) ^ (Θ + 1 / 2) * (n : ℝ) ^ (Θ + 1 / 2) * Real.sqrt |θ| := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2 * (n : ℝ)) ht.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnR.le]
    calc
      _ = (2 : ℝ) ^ (Θ + 1 / 2) * (n : ℝ) ^ (Θ + 1 / 2) *
          (|θ| ^ (-Θ) * |θ| ^ (Θ + 1 / 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add ht]
        rw [show -Θ + (Θ + 1 / 2) = (1 / 2 : ℝ) by ring, ← Real.sqrt_eq_rpow]
  unfold angularTerm
  calc
    _ ≤ Real.sqrt q * |θ| ^ (-Θ) * (2 * (n : ℝ) * |θ|) ^ (Θ + 1 / 2) *
        (K * Real.log n) := by
      apply mul_le_mul _ hlog hlog0 (by positivity)
      apply mul_le_mul _ hgap (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
    _ = _ := by
      calc
        _ = Real.sqrt q * (|θ| ^ (-Θ) * (2 * (n : ℝ) * |θ|) ^ (Θ + 1 / 2)) *
            (K * Real.log n) := by ring
        _ = _ := by rw [hpower]; ring

/-- P0004 page 5 section 1.4 and page 23 after equation 3.123.
The upper Farey width gives the square root saving n to minus one quarter.
The bound on abs theta also permits the compact angular range in
large_angle_factor. These are geometric bounds with no analytic error term. -/
theorem farey_upper_width :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        |θ| ≤ 2 * π ∧ Real.sqrt q * Real.sqrt |θ| ≤ D * (n : ℝ) ^ (-1 / 4 : ℝ) := by
  exact Decomp354h.farey_upper_width

/-- P0004 page 23 equation 3.123.
The exact large angle target follows from the angular cancellation and the
independently proved upper Farey width. No cited input is used. -/
theorem angular_large {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
      1 / (n : ℝ) < |θ| →
        angularTerm Θ n q θ ≤ E * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
  obtain ⟨C, hC, hc⟩ := large_angle_factor hΘ0 hΘ1
  obtain ⟨D, hD, hd⟩ := farey_upper_width
  refine ⟨C * D, mul_nonneg hC hD, fun n hn q hq hqN p hp hpq θ hθ hlarge => ?_⟩
  obtain ⟨hθbound, hwidth⟩ := hd n hn q hq hqN p hp hpq θ hθ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 ≤ Real.log n := (U1463.one_le_log_of_three (by omega)).trans' (by norm_num)
  have he : (n : ℝ) ^ (-1 / 4 : ℝ) * (n : ℝ) ^ (Θ + 1 / 2) =
      (n : ℝ) ^ (Θ + 1 / 4) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  calc
    _ ≤ C * (Real.sqrt q * Real.sqrt |θ|) * (n : ℝ) ^ (Θ + 1 / 2) * Real.log n :=
      hc n hn q hq θ hlarge hθbound
    _ ≤ C * (D * (n : ℝ) ^ (-1 / 4 : ℝ)) * (n : ℝ) ^ (Θ + 1 / 2) * Real.log n := by
      gcongr
    _ = C * D * ((n : ℝ) ^ (-1 / 4 : ℝ) * (n : ℝ) ^ (Θ + 1 / 2)) * Real.log n := by ring
    _ = _ := by rw [he]

#print axioms large_angle_factor
#print axioms farey_upper_width
#print axioms angular_large

end LeanLab.HardyLittlewood1923.Decomp354e
