import LeanLab.PNTPort.StrongPNT.Bridge
import LeanLab.PNTPort.BV.Helpers

/-!
AI wrote this Lean code for CODEX task703. Goldbach is open.
Derived theta error input for the Abel identity in BJS p. 17 equation 50
and the prime counting steps on pp. 43 and 57.
The proof uses the proved strong prime number theorem. It does not assume
any explicit Rosser or Dusart estimate or its printed threshold.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Prime703

open Real Filter Topology

/-- The strong prime number theorem gives an eventual theta error
bounded by a constant times x over log squared x. -/
theorem theta_error_log_sq703 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ C * x / log x ^ 2 := by
  obtain ⟨c, hc, K, hK⟩ := LeanLab.PNTPort.psi_explicit_strong
  obtain ⟨L, hL, hLe⟩ := LeanLab.PNTPort.BV.exp_neg_sqrt_log_le c hc 2
  let C : ℝ := (|K| + 1) * L
  have hC : 0 < C := by dsimp [C]; positivity
  have hroot : Tendsto (fun x : ℝ => 2 * log x ^ 3 / sqrt x) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [rpow_ofNat, sqrt_eq_rpow, mul_div_assoc, mul_zero] using hh.const_mul 2
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    hroot.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx hxroot
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 < sqrt x := sqrt_pos.mpr hx0
  have he := hLe x hx
  rw [rpow_two] at he
  have hpsi : |Chebyshev.psi x - x| ≤ C * x / log x ^ 2 := by
    calc |Chebyshev.psi x - x| ≤ K * x * exp (-c * sqrt (log x)) := hK x hx
      _ ≤ (|K| + 1) * x * exp (-c * sqrt (log x)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) hx0.le) (exp_pos _).le
      _ ≤ (|K| + 1) * x * (L / log x ^ 2) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = C * x / log x ^ 2 := by dsimp [C]; ring
  have hxdiv : x / sqrt x = sqrt x := by
    rw [div_eq_iff hs.ne']
    nlinarith [sq_sqrt hx0.le]
  have hsmall : 2 * sqrt x * log x ≤ x / log x ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hxroot.le
      (by positivity : 0 ≤ x / log x ^ 2)
    have heq : (2 * log x ^ 3 / sqrt x) * (x / log x ^ 2) =
        2 * log x * (x / sqrt x) := by
      field_simp [hl.ne', hs.ne']
    rw [heq, hxdiv, one_mul] at hh
    nlinarith only [hh]
  have hgap := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : (1 : ℝ) ≤ x)
  calc |Chebyshev.theta x - x| =
      |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by
        congr 1
        ring
    _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
    _ ≤ C * x / log x ^ 2 + x / log x ^ 2 := add_le_add hpsi (hgap.trans hsmall)
    _ = (C + 1) * x / log x ^ 2 := by ring

end LeanLab.AlmostPrimeSums.Prime703
