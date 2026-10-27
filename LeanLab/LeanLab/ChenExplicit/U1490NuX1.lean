/-
AI-written Lean code, Claude, Lean Lab run 20261022T1603Z-23862, unit U-1490, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, arXiv 2207.09452, idea I-0105.

nu of x1 in the X2-only chains at the MODEL floor, with the plus-4 Siegel constant of
U1490SiegelPlus.lean.  The lab chains BJSpX2At3215, BJSc2X2At3215, BJSl1X2At3215, BJSaX2At3215
use the Siegel input nu(x1) of BJS eq (81) only through `Good nu`: 1e-12 <= nu <= 1/2 and
nu log x1 >= 125, with log x1 = log X2 - 5 log log X2 by eq (75), K = log^delta1 x1, Q1 = log^10 x1
by eq (76).  The model of numerics/model_U1490.py puts the MODEL floor of the BJS Section 9 framework
at log log X2 = 31.5665 with the plus-4 constant, pbar1 = 59, pbar2 = 53, delta1 = 1.53058.

Here, at log log X2 = 31.567, delta1 = 1.5306 >= the model's 1.53055 at this point, PROVED:
* `nuP_good`: the plus-4 nu(x1), nuP = min(4/(sqrt K log K), 1/(2 R1 log Q1)), satisfies the lab's
  `Good` conditions with 136 in place of 125: nuP log x1 >= 136.
  With Bordignon's 100 in place of 4 log K the same quantity is about 70.7 in the model, far below
  125, so at this point the X2-only chains need the new constant.
* `siegel87_le`: the Siegel term of eq (87), L^2/e^L * 1.1 log(L^10) e^{(1-nu)L}/(1-nu), is at most
  1e-28 for every L >= log x1 and every nu with nu log x1 >= 136, nu <= 1/2; the 32.15 chain had 1e-23.
CONDITIONAL ON ClassNumberPlus4, MeanValueStep, BordignonEq9, BordignonThm13, `nuP_siegel`:
every real zero of an even primitive real L(s, chi) mod q, 4e5 < q <= K, is at most 1 - nuP.
The odd-character term of eq (91) and the remaining X2-only chains p, c4, l, l1, a(X2) at 31.567
are NOT ported here: the lab's 9e13 floor lemmas, Section9F9, do not reach e^31.567 = 5.12e13.
So no Chen threshold is claimed.  Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ChenExplicit.U1490SiegelPlus

open Real

noncomputable section
namespace LeanLab.ChenExplicit.U1490NuX1

/-- `δ₁` at the model floor. -/
def δ : ℝ := 1.5306
def R1 : ℝ := 2.0452
/-- log X₂ with log log X₂ = 31.567. -/
def LX : ℝ := exp 31.567
/-- log x₁(X₂) = log X₂ - 5 log log X₂, eq (75). -/
def Lx : ℝ := exp 31.567 - 5 * 31.567
/-- `K_δ(x₁) = log^δ x₁`, eq (76). -/
def K1 : ℝ := Lx ^ δ
/-- the plus-4 `ν(x₁)` of eq (81). -/
def nuP : ℝ := min (4 / (√K1 * log K1)) (1 / (2 * R1 * log (Lx ^ 10)))

/-- the lab's `Good` predicate of BJSpX2At3215 with the threshold `B` in place of 125. -/
def GoodB (B ν : ℝ) : Prop := 1e-12 ≤ ν ∧ ν ≤ 1 / 2 ∧ B / Lx ≤ ν

lemma LX_le : LX ≤ 8e13 := by
  unfold LX
  have h1 : exp (31.567 : ℝ) ≤ exp 32 := exp_le_exp.mpr (by norm_num)
  have e : exp (32 : ℝ) = exp 1 ^ 32 := by rw [← exp_nat_mul]; norm_num
  have h2 : exp 1 ^ 32 ≤ (2.7182818286 : ℝ) ^ 32 :=
    pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 32
  have h3 : (2.7182818286 : ℝ) ^ 32 ≤ 8e13 := by norm_num
  linarith

lemma exp3156_ge : (41336 : ℝ) ≤ exp 31.56 := by
  have := pow_div_factorial_le_exp (x := (31.56 : ℝ)) (by norm_num) 4
  simp [Nat.factorial] at this; norm_num at this ⊢; linarith

lemma exp3156_ge' : (1e6 : ℝ) ≤ exp 31.56 := by
  have := pow_div_factorial_le_exp (x := (31.56 : ℝ)) (by norm_num) 6
  simp [Nat.factorial] at this; norm_num at this ⊢; linarith

lemma Lx_ge : exp 31.56 ≤ Lx := by
  unfold Lx
  have e : exp (31.567 : ℝ) = exp 31.56 * exp 0.007 := by rw [← exp_add]; norm_num
  have h1 : (1.007 : ℝ) ≤ exp 0.007 := by have := add_one_le_exp (0.007 : ℝ); linarith
  have h2 := exp3156_ge
  have h3 : exp 31.56 * 1.007 ≤ exp 31.56 * exp 0.007 :=
    mul_le_mul_of_nonneg_left h1 (exp_pos _).le
  rw [e]; nlinarith

lemma Lx_pos : 0 < Lx := lt_of_lt_of_le (exp_pos _) Lx_ge
lemma Lx_ge' : (1e6 : ℝ) ≤ Lx := exp3156_ge'.trans Lx_ge
lemma Lx_le : Lx ≤ 8e13 := by have := LX_le; unfold LX at this; unfold Lx; linarith

lemma logLx_ge : 31.56 ≤ log Lx := by
  rw [le_log_iff_exp_le Lx_pos]; exact Lx_ge

lemma logLx_le : log Lx ≤ 31.567 := by
  rw [log_le_iff_le_exp Lx_pos]; unfold Lx; linarith

lemma exp7407_ge : (1647 : ℝ) ≤ exp 7.407 := by
  have h := sum_le_exp_of_nonneg (x := (7.407 : ℝ)) (by norm_num) 24
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h; linarith

/-- the even-character branch: `4/(√K log K) · log x₁ ≥ 136`. -/
lemma b1_ge : 136 / Lx ≤ 4 / (√K1 * log K1) := by
  have h1 := logLx_le; have h2 := logLx_ge
  have hsK : √K1 = exp (δ * log Lx / 2) := by
    unfold K1; rw [rpow_def_of_pos Lx_pos, ← exp_half]; ring_nf
  have hlK : log K1 = δ * log Lx := by unfold K1; rw [log_rpow Lx_pos]
  rw [hsK, hlK]
  have hE : Lx = exp (δ * log Lx / 2) * exp ((1 - δ / 2) * log Lx) := by
    rw [← exp_add, ← exp_log Lx_pos]; congr 1; rw [log_exp]; ring
  have hk : (7.407 : ℝ) ≤ (1 - δ / 2) * log Lx := by unfold δ; nlinarith
  have hx : (1647 : ℝ) ≤ exp ((1 - δ / 2) * log Lx) := exp7407_ge.trans (exp_le_exp.mpr hk)
  have hq : δ * log Lx ≤ 48.3165 := by unfold δ; nlinarith
  have hq0 : 0 < δ * log Lx := by unfold δ; nlinarith
  have ha := exp_pos (δ * log Lx / 2)
  rw [div_le_div_iff₀ Lx_pos (by positivity)]
  have hAB0 : exp (δ * log Lx / 2) * 1647 ≤ Lx :=
    calc exp (δ * log Lx / 2) * 1647 ≤ exp (δ * log Lx / 2) * exp ((1 - δ / 2) * log Lx) :=
          mul_le_mul_of_nonneg_left hx ha.le
      _ = Lx := hE.symm
  have : 136 * (exp (δ * log Lx / 2) * (δ * log Lx)) ≤
      136 * (exp (δ * log Lx / 2) * 48.3165) := by gcongr
  nlinarith

/-- the second branch, `1/(2 R₁ log Q₁)`: at least `136/log x₁` and at most `1/2`. -/
lemma b2_bounds : 136 / Lx ≤ 1 / (2 * R1 * log (Lx ^ 10)) ∧
    1 / (2 * R1 * log (Lx ^ 10)) ≤ 1 / 2 := by
  have h1 := logLx_le; have h2 := logLx_ge; have h3 := Lx_ge'
  have hd : 1 / (2 * R1 * log (Lx ^ 10)) = 1 / (40.904 * log Lx) := by
    unfold R1; rw [log_pow]; push_cast; ring
  have hp : 0 < 40.904 * log Lx := by nlinarith
  rw [hd]
  constructor
  · rw [div_le_div_iff₀ Lx_pos hp]; nlinarith
  · rw [div_le_div_iff₀ hp (by norm_num)]; nlinarith

/-- **`ν(x₁)` with the plus-4 constant is `Good` with threshold 136**, PROVED. -/
theorem nuP_good : GoodB 136 nuP := by
  obtain ⟨s3, s2⟩ := b2_bounds
  have hb := b1_ge
  have h200 : (1e-12 : ℝ) ≤ 136 / Lx := by
    rw [le_div_iff₀ Lx_pos]; have := Lx_le; nlinarith
  exact ⟨le_min (h200.trans hb) (h200.trans s3), (min_le_right _ _).trans s2, le_min hb s3⟩

/-- `ν(x₁) log x₁ ≥ 136`. -/
theorem nuP_mul_ge : 136 ≤ nuP * Lx := by
  have := nuP_good.2.2
  rw [div_le_iff₀ Lx_pos] at this; linarith

/-- GoodB 136 implies the lab's `Good` threshold 125. -/
theorem good125 {ν : ℝ} (h : GoodB 136 ν) : GoodB 125 ν :=
  ⟨h.1, h.2.1, le_trans (div_le_div_of_nonneg_right (by norm_num) Lx_pos.le) h.2.2⟩

/-- **The Siegel term of eq (87)**, PROVED: for `L ≥ log x₁` and `ν` with `GoodB 136 ν`,
`L²/e^L · 1.1 log(L¹⁰) e^{(1-ν)L}/(1-ν) ≤ 10⁻²⁸`. -/
theorem siegel87_le {ν L : ℝ} (hν : GoodB 136 ν) (hL : Lx ≤ L) :
    L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp ((1 - ν) * L) / (1 - ν))) ≤ 1e-28 := by
  obtain ⟨g1, g2, g3⟩ := hν
  have hxp := Lx_pos
  have hp : 0 < L := by linarith
  have hν0 : 0 < ν := by linarith
  have hb : 0 < 1 - ν := by linarith
  have eL : exp L = exp ((1 - ν) * L) * exp (ν * L) := by rw [← exp_add]; ring_nf
  have e : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp ((1 - ν) * L) / (1 - ν))) =
      11 * log L * L ^ 2 / ((1 - ν) * exp (ν * L)) := by
    rw [log_pow, eL]; field_simp; ring
  rw [e]
  have hu : 136 ≤ ν * Lx := by
    have := mul_le_mul_of_nonneg_right g3 hxp.le
    rwa [div_mul_cancel₀ _ Lx_pos.ne'] at this
  have hlx := logLx_le; have hlx2 := logLx_ge
  set t := L / Lx with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hxp]; linarith
  have hLt : L = Lx * t := by rw [ht]; field_simp
  have hlog : log L ≤ t * log Lx := by
    have h1 : log L = log Lx + log t := by rw [hLt, log_mul hxp.ne' (by linarith)]
    have h2 := log_le_sub_one_of_pos (show 0 < t by linarith)
    have : (t - 1) * 1 ≤ (t - 1) * log Lx := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have ht3 : t ^ 3 ≤ exp (ν * (L - Lx)) := by
    have h1 : t ≤ exp (t - 1) := by have := add_one_le_exp (t - 1); linarith
    have h2 : t ^ 3 ≤ exp (t - 1) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
    rw [← exp_nat_mul] at h2
    refine h2.trans (exp_le_exp.mpr ?_)
    have : ν * (L - Lx) = ν * Lx * (t - 1) := by rw [hLt]; ring
    rw [this]; push_cast; nlinarith
  have hnum : 11 * log L * L ^ 2 ≤ 11 * log Lx * Lx ^ 2 * exp (ν * (L - Lx)) := by
    have hl0 : 0 ≤ log L := log_nonneg (by nlinarith [Lx_ge'])
    have hm : log L * L ^ 2 ≤ (t * log Lx) * L ^ 2 := mul_le_mul_of_nonneg_right hlog (by positivity)
    have e2 : (t * log Lx) * L ^ 2 = log Lx * Lx ^ 2 * t ^ 3 := by rw [hLt]; ring
    have hlx0 : 0 ≤ log Lx * Lx ^ 2 := by
      have : 0 ≤ log Lx := by linarith
      positivity
    have := mul_le_mul_of_nonneg_left ht3 hlx0
    nlinarith
  have eE : exp (ν * L) = exp (ν * (L - Lx)) * exp (ν * Lx) := by rw [← exp_add]; ring_nf
  have hE : (1e59 : ℝ) ≤ exp (ν * Lx) := by
    have e : exp (136 : ℝ) = exp 1 ^ 136 := by rw [← exp_nat_mul]; norm_num
    have h1 : (2.718 : ℝ) ^ 136 ≤ exp 1 ^ 136 :=
      pow_le_pow_left₀ (by norm_num) (by have := exp_one_gt_d9; linarith) 136
    have h2 : (1e59 : ℝ) ≤ (2.718 : ℝ) ^ 136 := by norm_num
    have h3 : exp (136 : ℝ) ≤ exp (ν * Lx) := exp_le_exp.mpr hu
    rw [e] at h3; linarith
  have hLx2 : Lx ^ 2 ≤ (8e13 : ℝ) ^ 2 := pow_le_pow_left₀ hxp.le Lx_le 2
  have hD0 : 0 < exp (ν * (L - Lx)) := exp_pos _
  rw [div_le_iff₀ (by positivity), eE]
  have hb2 : (1 / 2 : ℝ) ≤ 1 - ν := by linarith
  have hk : 11 * log Lx * Lx ^ 2 ≤ 1e-28 * ((1 / 2) * 1e59) := by
    have : 11 * log Lx * Lx ^ 2 ≤ 11 * 31.567 * (8e13 : ℝ) ^ 2 := by
      have : 0 ≤ Lx ^ 2 := by positivity
      nlinarith
    norm_num at this ⊢; linarith
  have hprod : (1 / 2) * 1e59 ≤ (1 - ν) * exp (ν * Lx) :=
    mul_le_mul hb2 hE (by norm_num) (by linarith)
  have : 11 * log Lx * Lx ^ 2 * exp (ν * (L - Lx)) ≤
      1e-28 * ((1 - ν) * exp (ν * Lx)) * exp (ν * (L - Lx)) := by
    apply mul_le_mul_of_nonneg_right _ hD0.le
    nlinarith
  nlinarith

/-- `log K₁ ≤ 250`. -/
lemma logK1_le : log K1 ≤ 250 := by
  have := logLx_le; have := logLx_ge
  unfold K1; rw [log_rpow Lx_pos]; unfold δ; nlinarith

open LeanLab.ChenExplicit.U1483 LeanLab.ChenExplicit.U1486 LeanLab.ChenExplicit.U1490 in
/-- **CONDITIONAL ON `ClassNumberPlus4`, `MeanValueStep`, `BordignonEq9`, `BordignonThm13`**:
every real zero of an even primitive real `L(s, χ)` mod `q`, `4·10⁵ < q ≤ K₁ = log^δ₁ x₁`, is at
most `1 - ν_P(x₁)`; so `ν_P` is a legitimate even-character Siegel input of eq (81) at this point. -/
theorem nuP_siegel (hC : ClassNumberPlus4) (hM : MeanValueStep) (h9 : BordignonEq9)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K1) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - nuP := by
  have h := siegel_even_upto_K_plus hC hM h9 h13 logK1_le q χ hχ hq hqK β hβ
  have : nuP ≤ 4 / (√K1 * log K1) := min_le_left _ _
  linarith

/-- Vacuity: `GoodB 136` is inhabited, by `nuP` itself, and `siegel87_le` applies at `L = log x₁`. -/
example : Lx ^ 2 / exp Lx * (1.1 * log (Lx ^ 10) *
    (exp ((1 - nuP) * Lx) / (1 - nuP))) ≤ 1e-28 :=
  siegel87_le nuP_good le_rfl

end LeanLab.ChenExplicit.U1490NuX1
