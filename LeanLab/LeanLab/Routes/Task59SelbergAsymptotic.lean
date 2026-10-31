/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The U1436 eventual upper bound in its totient form.
The corrected choice A equal to 15 absorbs the square root error.
-/
import LeanLab.Routes.Task59SelbergLi
import LeanLab.Routes.Task59SelbergError15
import LeanLab.Routes.Task59ErrorVanishing

namespace LeanLab.Routes.Task59

open Real Filter Topology LeanLab.PNTPort.BVMax LeanLab.Routes.U1431

/-- The elementary Selberg assembly gives coefficient 4 in the totient form. -/
theorem eventually_rG_le_four_totient (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 2 ∣ N →
      (rG N : ℝ) ≤ (4 + ε) * ((N : ℝ) / N.totient) * (N : ℝ) / log N ^ 2 := by
  let δ : ℝ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let a : ℝ := 2 * (1 + δ) / (4 + ε / 2)
  have hd : 0 < 4 + ε / 2 := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have haHalf : a < 1 / 2 := by
    dsimp [a, δ]
    rw [div_lt_iff₀ hd]
    linarith
  have hcoef : 2 * (1 + δ) = (4 + ε / 2) * a := by
    dsimp [a]
    field_simp [hd.ne']
  obtain ⟨B, hB, K, hK0, hK⟩ := U1436.rG_le_main_bv_mertens 15 (by norm_num)
  let C : ℝ := sqrt (2 * exp 126 * K)
  have hlevel : ∀ᶠ N : ℕ in atTop,
      ‖log (N : ℝ) ^ B‖ ≤ ‖(N : ℝ) ^ (1 / 2 - a)‖ := by
    simpa only [one_mul] using tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_rpow_atTop B (by linarith : 0 < 1 / 2 - a)).bound one_pos)
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hloglarge : ∀ᶠ N : ℕ in atTop, 1 + δ ≤ log (N : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [eventually_liD_pred_le δ hδ, hlevel, hlarge, hloglarge,
    eventually_error15_small C (ε / 2) (sqrt_nonneg _) (by positivity),
    eventually_ge_atTop 2] with N hli hl h4 hll hs hN
  intro hev
  let x : ℝ := N
  let L : ℝ := log x
  let u : ℝ := liD ((N - 1 : ℕ) : ℝ)
  let y : ℝ := x ^ a
  let z : ℕ := ⌈sqrt y⌉₊
  have hx2 : 2 ≤ x := by
    change (2 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL : 0 < L := log_pos (by linarith)
  have hy0 : 0 < y := rpow_pos_of_pos hx0 _
  change 4 ≤ y at h4
  have hy1 : 1 < y := by linarith
  have hyx : y ≤ x := by
    calc x ^ a ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one _
  have hceil : sqrt y ≤ (z : ℝ) := Nat.le_ceil _
  have hsq2 : (2 : ℝ) ≤ sqrt y := by
    have hh := Real.sqrt_le_sqrt h4
    norm_num at hh
    exact hh
  have hz : 2 ≤ z := by exact_mod_cast hsq2.trans hceil
  have hyz : y ≤ (z : ℝ) ^ 2 := (Real.sqrt_le_iff.mp hceil).2
  have hsqrtx : sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx1)
  have hzN : z ≤ N := Nat.ceil_le.mpr ((Real.sqrt_le_sqrt hyx).trans hsqrtx)
  have hv0 : 0 ≤ log (z : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ z by omega))
  have hvL : log (z : ℝ) ≤ L :=
    log_le_log (by exact_mod_cast (show 0 < z by omega))
      (show (z : ℝ) ≤ (N : ℝ) by exact_mod_cast hzN)
  have hcut : (z : ℝ) + 1 ≤ sqrt x + 2 := by
    have hh := (Nat.ceil_lt_add_one (sqrt_nonneg y)).le
    change (z : ℝ) ≤ sqrt y + 1 at hh
    linarith [Real.sqrt_le_sqrt hyx]
  change ‖L ^ B‖ ≤ ‖x ^ (1 / 2 - a)‖ at hl
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (rpow_pos_of_pos hL _), abs_of_pos (rpow_pos_of_pos hx0 _)] at hl
  have hyB : y ≤ sqrt x / L ^ B := by
    rw [le_div_iff₀ (rpow_pos_of_pos hL B), Real.sqrt_eq_rpow]
    calc x ^ a * L ^ B ≤ x ^ a * x ^ (1 / 2 - a) :=
          mul_le_mul_of_nonneg_left hl (rpow_nonneg hx0.le _)
      _ = x ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hx0, show a + (1 / 2 - a) = (1 / 2 : ℝ) by ring]
  change u ≤ (1 + δ) * x / L at hli
  change 1 + δ ≤ L at hll
  have hu : u ≤ x := hli.trans (by
    rw [div_le_iff₀ hL]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hll hx0.le)
  have hφ : (0 : ℝ) < N.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < N)
  have hφx : (N.totient : ℝ) ≤ x := by
    change (N.totient : ℝ) ≤ (N : ℝ)
    exact_mod_cast Nat.totient_le N
  have hP : 1 ≤ x / N.totient := (one_le_div hφ).mpr hφx
  have hmain : 2 * (x / N.totient) * u / log y ≤
      (4 + ε / 2) * (x / N.totient) * x / L ^ 2 := by
    have hlogy : log y = a * L := Real.log_rpow hx0 a
    have heq (P : ℝ) : 2 * P * ((1 + δ) * x / L) / (a * L) =
        (4 + ε / 2) * P * x / L ^ 2 := by
      calc _ = (2 * (1 + δ)) * P * x / (a * L ^ 2) := by
            field_simp [hL.ne', ha.ne'] <;> ring
        _ = ((4 + ε / 2) * a) * P * x / (a * L ^ 2) := by rw [hcoef]
        _ = _ := by field_simp [hL.ne', ha.ne'] <;> ring
    calc _ ≤ 2 * (x / N.totient) * ((1 + δ) * x / L) / log y :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hli (by positivity)) (log_pos hy1).le
      _ = _ := by rw [hlogy]; exact heq _
  have he : sqrt ((x + u) * (exp 126 * log (z : ℝ) ^ 9) * (K * x / L ^ 15)) ≤
      C * x / L ^ 3 := selberg_error15_le x L u (log z) K hx0.le hL hu hv0 hvL hK0
  have h := hK N hN hev z hz y hy1 hyz hyB
  change (rG N : ℝ) ≤ 2 * (x / N.totient) * u / log y +
    sqrt ((x + u) * (exp 126 * log (z : ℝ) ^ 9) * (K * x / L ^ (15 : ℝ))) +
      ((z : ℝ) + 1) at h
  have h15 : L ^ (15 : ℝ) = L ^ (15 : ℕ) := by
    rw [show (15 : ℝ) = ((15 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h15] at h
  change C * x / L ^ 3 + sqrt x + 2 ≤ (ε / 2) * x / L ^ 2 at hs
  have hm : (ε / 2) * x / L ^ 2 ≤ (ε / 2) * (x / N.totient) * x / L ^ 2 := by
    calc _ = ((ε / 2) * x / L ^ 2) * 1 := by ring
      _ ≤ ((ε / 2) * x / L ^ 2) * (x / N.totient) :=
          mul_le_mul_of_nonneg_left hP (by positivity)
      _ = _ := by ring
  change (rG N : ℝ) ≤ (4 + ε) * (x / N.totient) * x / L ^ 2
  calc _ ≤ (4 + ε / 2) * (x / N.totient) * x / L ^ 2 + (ε / 2) * x / L ^ 2 := by
        linarith only [h, hmain, he, hcut, hs]
    _ ≤ (4 + ε / 2) * (x / N.totient) * x / L ^ 2 +
        (ε / 2) * (x / N.totient) * x / L ^ 2 := add_le_add le_rfl hm
    _ = _ := by ring

end LeanLab.Routes.Task59

#print axioms LeanLab.Routes.Task59.eventually_rG_le_four_totient
