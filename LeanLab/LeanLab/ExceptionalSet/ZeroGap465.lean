import LeanLab.ExceptionalSet.Conductor465

/-!
Scalar consequences of the zero gap input in P0082 page364 case ii d.
The zero free estimate itself remains an explicit input.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Supply465
open Real Filter Topology
open LeanLab.ExceptionalSet.U1539 (calE)

/-- P0082 page364 last displayed zero gap estimate. A conductor at most
E to one seventh turns the printed inverse square root conductor bound
into inverse fourteenth E divided by log E squared. CONDITIONAL ON the
explicit zero gap lower bound. -/
theorem small_conductor_gap_lower (r E g : ℝ) (hr : 2 ≤ r) (hE : 1 ≤ E)
    (hrE : r ≤ E ^ (1 / 7 : ℝ)) (hg : r ^ (-(1 / 2 : ℝ)) / (Real.log r) ^ 2 ≤ g) :
    E ^ (-(1 / 14 : ℝ)) / (Real.log E) ^ 2 ≤ g := by
  have hr0 : 0 < r := by linarith
  have hE0 : 0 < E := by linarith
  have hpow : E ^ (1 / 7 : ℝ) ≤ E := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hE (by norm_num : (1 / 7 : ℝ) ≤ 1))
  have hrEE : r ≤ E := hrE.trans hpow
  have hlr : 0 < Real.log r := Real.log_pos (by linarith)
  have hl : Real.log r ≤ Real.log E := Real.log_le_log hr0 hrEE
  have hnum := Real.rpow_le_rpow_of_nonpos hr0 hrE (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)
  rw [← Real.rpow_mul hE0.le] at hnum
  norm_num at hnum
  calc
    _ ≤ r ^ (-(1 / 2 : ℝ)) / (Real.log E) ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ r ^ (-(1 / 2 : ℝ)) / (Real.log r) ^ 2 := div_le_div_of_nonneg_left
      (Real.rpow_nonneg hr0.le _) (sq_pos_of_pos hlr) (pow_le_pow_left₀ hlr.le hl 2)
    _ ≤ g := hg

/-- P0082 page364 conclusion of case ii d. The logarithmic loss in the
small conductor zero gap is eventually absorbed by the margin between
one fourteenth and one tenth. -/
theorem zero_gap_scale_absorbed (γ κ : ℝ) (hγ : γ < 3 / 2) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
        calE γ κ N ^ (-(1 / 14 : ℝ)) / (Real.log (calE γ κ N)) ^ 2 := by
  let a := 3 - 2 * γ
  have ha : 0 < a := by dsimp [a]; linarith
  have ht : Tendsto (fun N : ℕ => κ * Real.log (N : ℝ) ^ a) atTop atTop :=
    ((tendsto_rpow_atTop ha).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hκ
  have hp := (isLittleO_rpow_exp_pos_mul_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 35)).bound
    (by norm_num : (0 : ℝ) < 1)
  apply eventually_atTop.mp
  filter_upwards [ht.eventually hp, ht.eventually_ge_atTop 1] with N hbound hlarge
  have hE0 : 0 < calE γ κ N := Real.exp_pos _
  have hlog : Real.log (calE γ κ N) = κ * Real.log (N : ℝ) ^ a := by rw [calE, Real.log_exp]
  have hlogpos : 0 < Real.log (calE γ κ N) := by rw [hlog]; linarith
  have hsq : (Real.log (calE γ κ N)) ^ 2 ≤ calE γ κ N ^ (1 / 35 : ℝ) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two,
      abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _), one_mul] at hbound
    rw [hlog, calE, ← Real.exp_mul]
    convert hbound using 1 <;> dsimp [a] <;> congr 1 <;> ring
  apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).mpr
  calc
    _ ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) * calE γ κ N ^ (1 / 35 : ℝ) :=
      mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hE0.le _)
    _ = _ := by rw [← Real.rpow_add hE0]; congr 1; norm_num
end LeanLab.ExceptionalSet.Supply465
