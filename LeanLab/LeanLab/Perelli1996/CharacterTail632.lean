/-
Perelli 1996, page 480 and page 485 equations 23 and 24.
Elementary bad character energy absorption using the existing totient ratio.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.TotientRatio320
import LeanLab.Perelli1996.Character632
namespace LeanLab.Perelli1996.Decomp88
open Real
/-- Page 485 equations 23 and 24. The totient prefactor has one inverse modulus. -/
theorem bad_character_totient_factor (q : ℕ) (hq : 0 < q) (L : ℝ)
    (hL : 1 ≤ L) (hlogq : Real.log q ≤ L) :
    (q : ℝ) / (q.totient : ℝ) ^ 2 ≤ 16 * L ^ 2 / q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hr : (q : ℝ) / q.totient ≤ 4 * L :=
    (TotientRatio320.ratio_le_log q hq).trans (by linarith)
  have hs := pow_le_pow_left₀ (div_nonneg hq0.le hφ.le) hr 2
  calc
    _ = ((q : ℝ) / q.totient) ^ 2 / q := by field_simp
    _ ≤ (4 * L) ^ 2 / q := div_le_div_of_nonneg_right hs hq0.le
    _ = _ := by ring

/-- Page 485 equation 24. The large bad modulus absorbs the character count
and a full period energy of size C N L. This is only numerical bookkeeping. -/
theorem bad_character_energy_saving (N L C B ε : ℝ) (q : ℕ)
    (hN : 0 ≤ N) (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q)
    (hlogq : Real.log q ≤ L) (hlarge : L ^ (100 * B / ε) ≤ (q : ℝ)) :
    ((q : ℝ) / (q.totient : ℝ) ^ 2) * L ^ (50 * B / ε) * (C * N * L) ≤
      16 * C * N * L ^ (-B) := by
  have hL0 : 0 < L := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hfac := bad_character_totient_factor q hq L hL hlogq
  have hpow0 : 0 < L ^ (100 * B / ε) := Real.rpow_pos_of_pos hL0 _
  have hratio : L ^ (50 * B / ε + 3) / (q : ℝ) ≤
      L ^ (3 - 50 * B / ε) := by
    calc
      _ ≤ L ^ (50 * B / ε + 3) / L ^ (100 * B / ε) :=
        div_le_div_of_nonneg_left (by positivity) hpow0 hlarge
      _ = _ := by rw [← Real.rpow_sub hL0]; congr 1; ring
  have hBε : 50 * B ≤ 50 * B / ε := by
    apply (le_div_iff₀ hε).mpr
    exact mul_le_of_le_one_right (by linarith : 0 ≤ 50 * B) hε1
  have hs : L ^ (3 - 50 * B / ε) ≤ L ^ (-B) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc
    _ ≤ (16 * L ^ 2 / q) * L ^ (50 * B / ε) * (C * N * L) := by gcongr
    _ = 16 * C * N * (L ^ (50 * B / ε + 3) / q) := by
      rw [Real.rpow_add hL0, Real.rpow_ofNat]
      ring
    _ ≤ 16 * C * N * L ^ (3 - 50 * B / ε) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
/-- Pages 478 and 480 window orders. A nonempty Theorem 1 range forces epsilon at most one. -/
theorem nonempty_window_epsilon_le (N H k ε : ℝ) (hN : 1 < N) (hk : 1 ≤ k)
    (hlo : N ^ (1 / (3 * k) + ε) ≤ H) (hhi : H ≤ N ^ (1 / k)) :
    ε ≤ 2 / (3 * k) ∧ ε ≤ 1 := by
  have hk0 : 0 < k := by linarith
  have he := (Real.rpow_le_rpow_left_iff hN).mp (hlo.trans hhi)
  have hid : 1 / k - 1 / (3 * k) = 2 / (3 * k) := by
    field_simp
    ring
  have hε : ε ≤ 2 / (3 * k) := by linarith
  refine ⟨hε, hε.trans ?_⟩
  apply (div_le_iff₀ (show 0 < 3 * k by positivity)).mpr
  linarith
end LeanLab.Perelli1996.Decomp88
