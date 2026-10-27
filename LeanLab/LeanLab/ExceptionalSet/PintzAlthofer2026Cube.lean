/-
# Pintz and Althöfer 2026, Theorem 3 at the paper's own truncation `P = X^{1/3}`

Unit U-1199, T2 FRONTIER, idea I-0080, PC run 20261020T0902Z-22676.

FAITHFULNESS FIX. arXiv 2610.15559v1, Section 4.3, read in Chrome this run: "Take P = X^{1/3}.
On ℝ/ℤ, let 𝔐 be the union of the arcs |α − a/q| ≤ P/(qX), q ≤ P, (a, q) = 1. These arcs are
disjoint for all sufficiently large X, since 2P² < X." The lab's `Split.model` used
`P = ⌊2√x⌋`, which is the range `q ≤ 2√X` of Lemma 4, not the model's `P`. At `2√x` the arcs
overlap; at `x^{1/3}` they are disjoint, so the sum of arc profiles `Vfun` IS the paper's `V_X²`.

What is here, all PROVED unconditional:
* `P3 x = ⌊x^{1/3}⌋`, with `P3_ge`, `P3_le`, `two_P3_le`, `two_P3_sq_lt`, the paper's `2P² < X`.
* `coef_lower_cube`: for large `x`, every `P` with `x^{1/3}/2 ≤ P ≤ x` and every even
  `n ∈ (x/2, x]`, `‖v_X(n)‖ ≥ x/(8e)`, the paper's (4.16) to (4.18) at its own `P`.
* `coef_window3`: `‖R_Λ(n)e^{−n/x} − v_X(n)‖ ≥ x/(16e)` at every bad even `n ∈ (x/2, x]`.
* `UpperHalfModel3 θ`, NOT proved: `∫_{ℝ/ℤ} |F_{x,x²}² − V_x|² ≤ K x^{2a(θ)+1+2η} log x`,
  `V_x = Vfun x P P`, `P = ⌊x^{1/3}⌋`. This is the paper's (4.13), now at the paper's `P`.
* `bessel_of_model3`, `theorem3_of_model3`, `five_eighths_of_model3`: Theorem 3 CONDITIONAL ON
  `UpperHalfModel3 θ` only.

KNOWN mathematics, the paper's route. AI wrote this Lean code. Binary Goldbach is OPEN.
TRUNCATION FIX, same run, after U-1200: every L² Prop here uses `F_{x,x²} = Σ_{m≤x²}`, not
`Σ_{m≤x}`. With the cut at `x`, the coefficients of `F²` at `n ∈ (x, 2x]` miss the pairs with a
part above `x` and differ from the model's by about `2(n − x)𝔖(n)e^{−n/x}`, so the integral is
`≫ x³` and the Prop would be FALSE for large `x`, since `2a(θ) + 1 < 3`. With the cut at `x²` the
omitted tail `Σ_{m>x²} Λ(m)e^{−m/x}` is `O(x² e^{−x})`, so the Prop is the paper's statement up to
a negligible error; the coefficients on the window are unchanged, `n ≤ x ≤ x²`.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026Model

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Cube

open Finset Real MeasureTheory AddCircle LeanLab.ExceptionalSet.PintzAlthofer2026
open LeanLab.ExceptionalSet.PintzAlthofer2026Split LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model LeanLab.Routes.R5060

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### The truncation `P = ⌊x^{1/3}⌋` -/

/-- The paper's `P = X^{1/3}`, floored. -/
def P3 (x : ℕ) : ℕ := ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊

theorem cube_rt (x : ℕ) : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x)]; norm_num

theorem cube_rt_ge_two (x : ℕ) (hx : 8 ≤ x) : 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
  LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 3) (by norm_num)
    (by positivity) (by norm_num) (cube_rt x) (by norm_num; exact_mod_cast hx)

theorem P3_ge (x : ℕ) (hx : 8 ≤ x) : (x : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ P3 x := by
  have hy := cube_rt_ge_two x hx
  have h1 := Nat.lt_floor_add_one ((x : ℝ) ^ ((1 : ℝ) / 3))
  unfold P3; linarith

theorem P3_real_le (x : ℕ) : (P3 x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
  Nat.floor_le (by positivity)

theorem two_P3_le (x : ℕ) (hx : 8 ≤ x) : 2 * P3 x ≤ x := by
  have hy := cube_rt_ge_two x hx
  have hc := cube_rt x
  have hP := P3_real_le x
  set y := (x : ℝ) ^ ((1 : ℝ) / 3)
  have hy0 : 0 ≤ y := by linarith
  have hsq : 4 ≤ y ^ 2 := by nlinarith
  have h3 : y ^ 3 = y * y ^ 2 := by ring
  have h4 : y * 4 ≤ y * y ^ 2 := mul_le_mul_of_nonneg_left hsq hy0
  have : (2 * P3 x : ℝ) ≤ x := by linarith
  exact_mod_cast this

theorem P3_le (x : ℕ) (hx : 8 ≤ x) : P3 x ≤ x := le_trans (by omega) (two_P3_le x hx)

/-- The paper's disjointness condition `2P² < X`, for `x ≥ 9`. -/
theorem two_P3_sq_lt (x : ℕ) (hx : 9 ≤ x) : 2 * (P3 x : ℝ) ^ 2 < x := by
  have hy := cube_rt_ge_two x (by omega)
  have hc := cube_rt x
  have hP := P3_real_le x
  set y := (x : ℝ) ^ ((1 : ℝ) / 3)
  have hy2 : 2 < y := by
    by_contra h; push_neg at h
    have hy' : y = 2 := le_antisymm h hy
    have : (9 : ℝ) ≤ x := by exact_mod_cast hx
    rw [hy'] at hc; norm_num at hc; linarith
  have hP0 : (0 : ℝ) ≤ P3 x := Nat.cast_nonneg _
  have : (P3 x : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hP0 hP 2
  have hpos : 0 < y ^ 2 * (y - 2) := mul_pos (by positivity) (sub_pos.2 hy2)
  have h3 : y ^ 3 = y ^ 2 * (y - 2) + 2 * y ^ 2 := by ring
  linarith

/-! ### The lower half at `P ≥ x^{1/3}/2` -/

set_option maxHeartbeats 2000000 in
theorem coef_lower_cube : ∃ X0 : ℝ, ∀ x : ℕ, X0 ≤ x → ∀ P : ℕ,
    (x : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ P → P ≤ x →
    ∀ n : ℕ, Even n → x / 2 < n → n ≤ x →
    (x : ℝ) / (8 * Real.exp 1) ≤ ‖LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc x
      P P (fun q => ((bS n q : ℝ) : ℂ)) n‖ := by
  obtain ⟨C0, hC0, hcoef⟩ := LeanLab.ExceptionalSet.PintzAlthofer2026CoefHalf.coef418_half
  obtain ⟨C, hC, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 48 (by norm_num)
  set e := Real.exp 1
  have he : 0 < e := Real.exp_pos 1
  set K := 3479 * e * C0 * C ^ 2
  have hK : 0 < K := by positivity
  refine ⟨max (2 ^ 48) (max ((48 * C ^ 2) ^ 8) ((8 * e * K) ^ 4)),
    fun x hx P hPlo hPle' n hn hxn hnx => ?_⟩
  have hx1 : (2 ^ 48 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hxA : (48 * C ^ 2) ^ 8 ≤ (x : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxB : (8 * e * K) ^ 4 ≤ (x : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx1
  set t := (x : ℝ) ^ ((1 : ℝ) / 48) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht48 : t ^ 48 = (x : ℝ) := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht2 : 2 ≤ t := LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 48)
    (by norm_num) ht0 (by norm_num) ht48 hx1
  have hCt6 : 48 * C ^ 2 ≤ t ^ 6 :=
    LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 8) (by norm_num)
      (by positivity) (by positivity) (by rw [← pow_mul]; exact ht48) hxA
  have hKt12 : 8 * e * K ≤ t ^ 12 :=
    LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 4) (by norm_num)
      (by positivity) (by positivity) (by rw [← pow_mul]; exact ht48) hxB
  have hcube : (x : ℝ) ^ ((1 : ℝ) / 3) = t ^ 16 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hP16 : t ^ 16 / 2 ≤ (P : ℝ) := by rw [← hcube]; exact hPlo
  have hn2 : 2 ≤ n := by
    have : 2 ≤ x / 2 := by
      have : (2 ^ 48 : ℕ) ≤ x := by exact_mod_cast hx1
      omega
    omega
  have hn1 : 1 ≤ n := by omega
  have hnr : (n : ℝ) ≤ x := by exact_mod_cast hnx
  have hτn := hτ n hn1
  have hn48 : (n : ℝ) ^ ((48 : ℕ) : ℝ)⁻¹ ≤ t := by
    rw [ht_def]; norm_num
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) hnr (by norm_num)
  have hτt : (n.divisors.card : ℝ) ≤ C * t := hτn.trans (mul_le_mul_of_nonneg_left hn48 hC.le)
  have hτ0 : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
  have hτ2 : (n.divisors.card : ℝ) ^ 2 ≤ C ^ 2 * t ^ 2 := by
    have := pow_le_pow_left₀ hτ0 hτt 2; nlinarith
  have ht16big : (4 : ℝ) ≤ t ^ 16 / 2 := by
    have : (2 : ℝ) ^ 16 ≤ t ^ 16 := pow_le_pow_left₀ (by norm_num) ht2 16
    linarith
  have hP2 : 2 ≤ P := by
    have : (2 : ℝ) ≤ P := by linarith
    exact_mod_cast this
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPle : (P : ℝ) ≤ x := by exact_mod_cast hPle'
  have hsqP : t ^ 8 / 2 ≤ Real.sqrt P := by
    apply Real.le_sqrt_of_sq_le
    have : (t ^ 8 / 2) ^ 2 = t ^ 16 / 4 := by ring
    rw [this]; have : 0 ≤ t ^ 16 := by positivity
    linarith
  have hlogt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < t by linarith); linarith
  have hlogx : Real.log x = 48 * Real.log t := by
    rw [← ht48, Real.log_pow]; norm_num
  have hlogP : Real.log P ≤ 48 * t := by
    have := Real.log_le_log hPr hPle; rw [hlogx] at this; linarith
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hb1 : 1 + Real.log P / Real.log 2 ≤ 71 * t := by
    have : Real.log P / Real.log 2 ≤ 48 * t / 0.69 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have : 48 * t / 0.69 ≤ 70 * t := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hb2 : 1 + Real.log P ≤ 49 * t := by linarith
  have hmain := hcoef n P x hn hn2 hP2 hx0
  have hexp : Real.exp (-1) ≤ Real.exp (-(n : ℝ) / x) := by
    apply Real.exp_le_exp.2
    rw [neg_div, neg_le_neg_iff, div_le_one hx0]; exact hnr
  have hnhalf : (x : ℝ) / 2 ≤ n := by
    have : ((x / 2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hxn
    have h2 : (x : ℝ) / 2 ≤ ((x / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.lt_div_mul_add (a := x) (show 0 < 2 by norm_num)
      have : ((x : ℕ) : ℝ) < ((x / 2 * 2 + 2 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    linarith
  have hemi : Real.exp (-1) = 1 / e := by rw [Real.exp_neg]; simp [e]
  have hA : (x : ℝ) / (2 * e) ≤ n * Real.exp (-(n : ℝ) / x) := by
    calc (x : ℝ) / (2 * e) = (x / 2) * Real.exp (-1) := by rw [hemi]; field_simp
      _ ≤ n * Real.exp (-(n : ℝ) / x) :=
          mul_le_mul hnhalf hexp (by positivity) (Nat.cast_nonneg n)
  have hbr : (1 / 2 : ℝ) ≤ 1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P := by
    have hs : 0 < Real.sqrt P := Real.sqrt_pos.2 hPr
    have : 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P ≤ 1 / 2 := by
      rw [div_le_iff₀ hs]
      have ht2' : 0 ≤ t ^ 2 := by positivity
      have h48 : 48 * C ^ 2 * t ^ 2 ≤ t ^ 6 * t ^ 2 := mul_le_mul_of_nonneg_right hCt6 ht2'
      have h44 : t ^ 6 * t ^ 2 = t ^ 8 := by ring
      have hτ12 : 12 * (n.divisors.card : ℝ) ^ 2 ≤ 12 * (C ^ 2 * t ^ 2) := by linarith
      linarith
    linarith
  have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hXP : (x : ℝ) / (2 * π ^ 2 * P) ≤ t ^ 32 := by
    rw [div_le_iff₀ (by positivity)]
    have : (x : ℝ) = t ^ 16 * t ^ 32 := by rw [← pow_add]; exact ht48.symm
    rw [this]
    have h32 : 0 ≤ t ^ 32 := by positivity
    have hPP : (P : ℝ) ≤ π ^ 2 * P := by
      have := mul_le_mul_of_nonneg_right hpi hPr.le; linarith
    have h2P : t ^ 16 ≤ 2 * π ^ 2 * P := by linarith
    calc t ^ 16 * t ^ 32 ≤ (2 * π ^ 2 * P) * t ^ 32 := mul_le_mul_of_nonneg_right h2P h32
      _ = t ^ 32 * (2 * π ^ 2 * P) := by ring
  have herr : (x : ℝ) / (2 * π ^ 2 * P) * (C0 * (e * (1 + Real.log P / Real.log 2)) *
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P)) ≤ K * t ^ 36 := by
    have h1 : 0 ≤ 1 + Real.log P / Real.log 2 := by positivity
    have h2 : 0 ≤ 1 + Real.log P := by linarith
    calc (x : ℝ) / (2 * π ^ 2 * P) * (C0 * (e * (1 + Real.log P / Real.log 2)) *
          (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P))
        ≤ t ^ 32 * (C0 * (e * (71 * t)) * (C ^ 2 * t ^ 2) * (49 * t)) := by
          apply mul_le_mul hXP _ (by positivity) (by positivity)
          apply mul_le_mul _ hb2 h2 (by positivity)
          apply mul_le_mul _ hτ2 (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hC0.le
          exact mul_le_mul_of_nonneg_left hb1 he.le
      _ = K * t ^ 36 := by simp only [K]; ring
  have hKt : K * t ^ 36 ≤ (x : ℝ) / (8 * e) := by
    rw [le_div_iff₀ (by positivity), ← ht48]
    have h36 : 0 ≤ t ^ 36 := by positivity
    have : K * t ^ 36 * (8 * e) = (8 * e * K) * t ^ 36 := by ring
    rw [this]
    calc (8 * e * K) * t ^ 36 ≤ t ^ 12 * t ^ 36 := mul_le_mul_of_nonneg_right hKt12 h36
      _ = t ^ 48 := by ring
  have hmt : (x : ℝ) / (2 * e) * (1 / 2) ≤
      (n * Real.exp (-(n : ℝ) / x)) * (1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) :=
    mul_le_mul hA hbr (by norm_num) (by positivity)
  have hfin : (x : ℝ) / (2 * e) * (1 / 2) - (x : ℝ) / (8 * e) = (x : ℝ) / (8 * e) := by
    field_simp; ring
  linarith

/-! ### The coefficient of `F_X² − V_X²` at `P = ⌊x^{1/3}⌋` -/

/-- `v_X(n)` of (4.14) at the paper's `P = ⌊x^{1/3}⌋`. -/
def model3 (x n : ℕ) : ℂ :=
  LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc x (P3 x) (P3 x)
    (fun q => ((bS n q : ℝ) : ℂ)) n

/-- `R_Λ(n) e^{−n/x} − v_X(n)` at `P = ⌊x^{1/3}⌋`. -/
def coefF3 (x n : ℕ) : ℂ := ((RΛ n * Real.exp (-(n : ℝ) / x) : ℝ) : ℂ) - model3 x n

theorem coef_window3 : ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → ∀ n ∈ windowSet x,
    (x : ℝ) / (16 * Real.exp 1) ≤ ‖coefF3 x n‖ := by
  obtain ⟨X1, hX1⟩ := coef_lower_cube
  obtain ⟨X2, hX2⟩ := RΛ_small
  refine ⟨max 8 (max ⌈X1⌉₊ ⌈X2⌉₊), fun x hx n hn => ?_⟩
  have hx8 : 8 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : X1 ≤ x := by
    have : ⌈X1⌉₊ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    exact (Nat.le_ceil X1).trans (by exact_mod_cast this)
  have hx2 : X2 ≤ x := by
    have : ⌈X2⌉₊ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    exact (Nat.le_ceil X2).trans (by exact_mod_cast this)
  simp only [windowSet, Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hlo, hhi⟩, hev, hng⟩ := hn
  have hxn : x / 2 < n := by omega
  have hm := hX1 x hx1 (P3 x) (P3_ge x hx8) (P3_le x hx8) n hev hxn hhi
  have hr := hX2 x hx2 n (by omega) hhi hng
  set r := RΛ n * Real.exp (-(n : ℝ) / x)
  have hr0 : 0 ≤ r := mul_nonneg (RΛ_nonneg n) (Real.exp_pos _).le
  have hrle : r ≤ RΛ n := by
    apply mul_le_of_le_one_right (RΛ_nonneg n)
    apply Real.exp_le_one_iff.2
    have : (0 : ℝ) ≤ n / x := by positivity
    rw [neg_div]; linarith
  have hnr : ‖((r : ℝ) : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have htri : ‖model3 x n‖ - ‖((r : ℝ) : ℂ)‖ ≤ ‖coefF3 x n‖ := by
    have := norm_sub_norm_le (model3 x n) ((r : ℝ) : ℂ)
    rw [norm_sub_rev] at this
    exact this
  have hep : 0 < Real.exp 1 := Real.exp_pos 1
  have hhalf : (x : ℝ) / (8 * Real.exp 1) - x / (16 * Real.exp 1) = x / (16 * Real.exp 1) := by
    field_simp; ring
  unfold model3 at htri
  linarith

/-! ### Theorem 3 from the paper's (4.13) at `P = ⌊x^{1/3}⌋` -/

/-- **The paper's (4.13)**, as a Prop, NOT proved: with `V_x = Vfun x P P`, `P = ⌊x^{1/3}⌋`,
which is exactly `V_X²` since the arcs are disjoint, `two_P3_sq_lt`,
`∫_{ℝ/ℤ} |F_{x,x²}² − V_x|² ≤ K x^{2a(θ)+1+2η} log x` for every `η > 0` and large `x`. -/
def UpperHalfModel3 (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x →
    ∫ t, ‖FX x (x ^ 2) t ^ 2 - Vfun x (P3 x) (P3 x) t‖ ^ 2 ∂haarAddCircle ≤
      K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x

/-- The squares of `coefF3` over the bad window are bounded by the integral, by Bessel. -/
theorem window_sum_le (x : ℕ) (hx : 8 ≤ x) :
    ∑ n ∈ windowSet x, ‖coefF3 x n‖ ^ 2 ≤
      ∫ t, ‖FX x (x ^ 2) t ^ 2 - Vfun x (P3 x) (P3 x) t‖ ^ 2 ∂haarAddCircle := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  set W := Vfun x (P3 x) (P3 x)
  have hW : MemLp W 2 haarAddCircle := memLp_Vfun hx0 _ _
  set G : AddCircle (1 : ℝ) → ℂ := fun t => FX x (x ^ 2) t ^ 2 - W t
  have hG : MemLp G 2 haarAddCircle := (memLp_FX_sq (x : ℝ) (x ^ 2)).sub hW
  have h2 : 2 * (P3 x : ℝ) ≤ x := by exact_mod_cast two_P3_le x hx
  have hcoefG : ∀ n ∈ windowSet x, fourierCoeff G n = coefF3 x n := by
    intro n hn
    have hsub : fourierCoeff G = fourierCoeff (fun t => FX x (x ^ 2) t ^ 2) - fourierCoeff W := by
      have h := fourierCoeff.add (T := (1 : ℝ)) (f := fun t => FX x (x ^ 2) t ^ 2) (g := -W)
        ((memLp_FX_sq (x : ℝ) (x ^ 2)).integrable one_le_two) (hW.integrable one_le_two).neg
      have hneg : fourierCoeff (-W) = -fourierCoeff W := by
        ext m
        have := fourierCoeff.const_smul (T := (1 : ℝ)) W (-1) m
        simpa [neg_smul, one_smul] using this
      rw [hneg] at h
      have hG' : G = (fun t => FX x (x ^ 2) t ^ 2) + -W := by
        ext t; simp [G, sub_eq_add_neg]
      rw [hG', h, sub_eq_add_neg]
    rw [hsub, Pi.sub_apply, fourierCoeff_FX_sq (x : ℝ) (x ^ 2) n ((window_le x n hn).trans (Nat.le_self_pow two_ne_zero x)),
      fourierCoeff_Vfun hx0 (Nat.cast_nonneg _) h2]
    rfl
  have hb := bessel_finset hG ((windowSet x).image (fun n : ℕ => (n : ℤ)))
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)] at hb
  calc ∑ n ∈ windowSet x, ‖coefF3 x n‖ ^ 2
      = ∑ n ∈ windowSet x, ‖fourierCoeff G n‖ ^ 2 :=
        Finset.sum_congr rfl fun n hn => by rw [hcoefG n hn]
    _ ≤ _ := hb

/-- **`bessel_of_model3`**: the paper's (4.13) at its own `P` gives `BesselInput`. -/
theorem bessel_of_model3 {θ : ℝ} (hM : UpperHalfModel3 θ) : BesselInput θ := by
  intro η hη
  obtain ⟨K, X0, hK⟩ := hM η hη
  obtain ⟨X1, hX1⟩ := coef_window3
  refine ⟨K, 1 / (16 * Real.exp 1), max 8 (max X0 X1), by positivity, fun x hx =>
    ⟨fun n => ‖coefF3 x n‖, ?_, ?_⟩⟩
  · intro n hn
    rw [abs_norm]
    have := hX1 x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) n hn
    calc 1 / (16 * Real.exp 1) * (x : ℝ) = x / (16 * Real.exp 1) := by ring
      _ ≤ _ := this
  · exact (window_sum_le x (le_trans (le_max_left _ _) hx)).trans
      (hK x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx))

/-- Theorem 3 of Pintz-Althöfer, CONDITIONAL ON the paper's (4.13), `UpperHalfModel3 θ`, only. -/
theorem theorem3_of_model3 {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hM : UpperHalfModel3 θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) :=
  theorem3_of_bessel h1 h2 (bessel_of_model3 hM)

/-- θ = 5/8, CONDITIONAL ON `UpperHalfModel3 (5/8)` only: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_model3 (hM : UpperHalfModel3 (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) :=
  five_eighths_of_bessel (bessel_of_model3 hM)

/-! ### Vacuity -/

/-- `P3 1000 = 10`, and the disjointness condition `2P² < X` holds there. -/
example : 2 * (P3 1000 : ℝ) ^ 2 < 1000 := two_P3_sq_lt 1000 (by norm_num)

end

end LeanLab.ExceptionalSet.PintzAlthofer2026Cube
