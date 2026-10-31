/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The elementary discrete logarithmic integral bound requested by U1436.
The proof uses a finite split and logarithms dominated by positive powers.
No prime number theorem or cited analytic input is used.
-/
import LeanLab.Routes.Task59LiNSplit

namespace LeanLab.Routes.Task59

open Finset Real Filter Topology LeanLab.PNTPort.BVMax

/-- For every positive epsilon the discrete logarithmic integral is eventually
at most one plus epsilon times N over log N. -/
theorem eventually_liN_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, liN N ≤ (1 + ε) * (N : ℝ) / log N := by
  let a : ℝ := (1 + ε / 2)⁻¹
  have ha0 : 0 < a := inv_pos.mpr (by linarith)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  let c : ℝ := ε * log 2 / 4
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall1 : ∀ᶠ N : ℕ in atTop,
      ‖log (N : ℝ)‖ ≤ c * ‖(N : ℝ) ^ (1 - a)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by linarith : 0 < 1 - a)).bound hc)
  have hsmall2 : ∀ᶠ N : ℕ in atTop,
      ‖log (N : ℝ)‖ ≤ c * ‖(N : ℝ) ^ (1 : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound hc)
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha0).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsmall1, hsmall2, hlarge, eventually_ge_atTop 2] with N h1 h2 hlarge hN
  let x : ℝ := N
  have hx2 : 2 ≤ x := by
    change (2 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < log x := log_pos (by linarith)
  change ‖log x‖ ≤ c * ‖x ^ (1 - a)‖ at h1
  change ‖log x‖ ≤ c * ‖x ^ (1 : ℝ)‖ at h2
  change 2 ≤ x ^ a at hlarge
  rw [Real.norm_eq_abs, abs_of_pos hlogx, Real.norm_eq_abs,
    abs_of_pos (rpow_pos_of_pos hx0 _)] at h1
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_pos hlogx, abs_of_pos hx0] at h2
  let M : ℕ := ⌈x ^ a⌉₊
  have hceil : x ^ a ≤ (M : ℝ) := Nat.le_ceil _
  have hM2 : 2 ≤ M := by exact_mod_cast hlarge.trans hceil
  have hMle : (M : ℝ) ≤ x ^ a + 1 :=
    (Nat.ceil_lt_add_one (rpow_nonneg hx0.le _)).le
  have hLM : a * log x ≤ log (M : ℝ) := by
    calc a * log x = log (x ^ a) := (Real.log_rpow hx0 _).symm
      _ ≤ log (M : ℝ) := log_le_log (rpow_pos_of_pos hx0 _) hceil
  have hprod : x ^ a * log x ≤ c * x := by
    calc x ^ a * log x ≤ x ^ a * (c * x ^ (1 - a)) :=
          mul_le_mul_of_nonneg_left h1 (rpow_nonneg hx0.le _)
      _ = c * (x ^ a * x ^ (1 - a)) := by ring
      _ = c * x := by
          rw [← Real.rpow_add hx0, show a + (1 - a) = 1 by ring, Real.rpow_one]
  have hheadNum : (M : ℝ) * log x ≤ (ε / 2 * x) * log 2 := by
    calc (M : ℝ) * log x ≤ (x ^ a + 1) * log x :=
          mul_le_mul_of_nonneg_right hMle hlogx.le
      _ = x ^ a * log x + log x := by ring
      _ ≤ c * x + c * x := add_le_add hprod h2
      _ = (ε / 2 * x) * log 2 := by dsimp [c]; ring
  have hhead : (M : ℝ) / log 2 ≤ (ε / 2 * x) / log x :=
    (div_le_div_iff₀ hlog2 hlogx).mpr hheadNum
  have htail : x / log (M : ℝ) ≤ (1 + ε / 2) * x / log x := by
    calc x / log (M : ℝ) ≤ x / (a * log x) :=
          div_le_div_of_nonneg_left hx0.le (mul_pos ha0 hlogx) hLM
      _ = (1 + ε / 2) * x / log x := by
          have hd : 1 + ε / 2 ≠ 0 := by linarith
          dsimp [a]
          field_simp [hd, hlogx.ne'] <;> ring
  change liN N ≤ (1 + ε) * x / log x
  calc liN N ≤ (M : ℝ) / log 2 + x / log (M : ℝ) := liN_le_split N M hM2
    _ ≤ (ε / 2 * x) / log x + (1 + ε / 2) * x / log x := add_le_add hhead htail
    _ = (1 + ε) * x / log x := by ring

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.eventually_liN_le
