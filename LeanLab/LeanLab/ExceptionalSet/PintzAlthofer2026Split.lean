/-
# Pintz and Althöfer 2026, Theorem 3: `BesselInput` reduced to its L² upper half

Unit U-1186, T2 FRONTIER, idea I-0080, PC run 20261020T0703Z-22071.

Source: Pintz and Althöfer, arXiv 2610.15559v1, Section 4.3 and 4.4. The paper writes
`F_X(α) = Σ Λ(m) e^{−m/X} e(mα)` and the major arc model `V_X` with Fourier coefficient
`v_X(n)`, (4.14), for `q ≤ P`, `|β| ≤ P/(qX)`, and, from its Lemma 4, `P = 2√X`.
The `n`-th Fourier coefficient of `F_X² − V_X²` is `R_Λ(n) e^{−n/X} − v_X(n)`.

What is here, all PROVED unconditional except where a Prop is named as a hypothesis:
* `coef_lower_gen`: `coef_lower` for every truncation `P` with `⌊√x⌋ ≤ P ≤ x`, in particular the
  paper's `P = ⌊2√x⌋`.
* `RΛ_small`: for large `x`, every non-Goldbach `n ≤ x` has `R_Λ(n) ≤ x/(16e)`, from (4.19).
* `coef_window`: at every bad even `n` in `(x/2, x]` the coefficient of `F_X² − V_X²` has size
  at least `x/(16e)`. This is (4.18) with (4.19), the whole lower half of `BesselInput`.
* `UpperHalf θ`: the L² upper half ALONE, as a Prop: the squares of those coefficients over the
  bad set sum to `≪ x^{2a(θ)+1+2η} log x`. In the paper this is Bessel's inequality plus (4.13),
  that is Lemma 4, the zero sum. It is NOT proved here.
* `bessel_of_upperHalf`: `UpperHalf θ → BesselInput θ`.
* `theorem3_of_upperHalf`, `five_eighths_of_upperHalf`: Theorem 3, CONDITIONAL ON `UpperHalf θ`
  only, and the case θ = 5/8, `E(X) ≪ X^{25/44+ε}`.

Vacuity note: for `8 ≤ x ≤ 4·10^18` the bad set is empty by the Oliveira e Silva check, so
`UpperHalf` has content only for larger `x`; that is expected, the statement is asymptotic.
KNOWN mathematics, the paper's own route. AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower
import LeanLab.ExceptionalSet.PintzAlthofer2026Major

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Split

open Finset Real LeanLab.Routes.R5060 LeanLab.ExceptionalSet.PintzAlthofer2026

attribute [local instance] Classical.propDecidable

/-- The paper's truncation `P = ⌊2√x⌋ = ⌊√(4x)⌋`. -/
def Ppaper (x : ℕ) : ℕ := Nat.sqrt (4 * x)

theorem sqrt_le_Ppaper (x : ℕ) : Nat.sqrt x ≤ Ppaper x := Nat.sqrt_le_sqrt (by omega)

theorem Ppaper_le (x : ℕ) (hx : 4 ≤ x) : Ppaper x ≤ x := by
  unfold Ppaper
  by_contra h
  push_neg at h
  have h1 := Nat.sqrt_le' (4 * x)
  have h2 : (x + 1) * (x + 1) ≤ Nat.sqrt (4 * x) * Nat.sqrt (4 * x) := Nat.mul_le_mul h h
  have h3 : Nat.sqrt (4 * x) * Nat.sqrt (4 * x) = Nat.sqrt (4 * x) ^ 2 := by ring
  nlinarith

set_option maxHeartbeats 1000000 in
/-- `coef_lower` for every truncation `⌊√x⌋ ≤ P ≤ x`. Same proof, `P` a parameter. -/
theorem coef_lower_gen : ∃ X0 : ℝ, ∀ x : ℕ, X0 ≤ x → ∀ P : ℕ, Nat.sqrt x ≤ P → P ≤ x →
    ∀ n : ℕ, Even n → x / 2 < n → n ≤ x →
    (x : ℝ) / (8 * Real.exp 1) ≤ ‖LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc x
      P P (fun q => ((bS n q : ℝ) : ℂ)) n‖ := by
  obtain ⟨C0, hC0, hcoef⟩ := LeanLab.ExceptionalSet.PintzAlthofer2026CoefHalf.coef418_half
  obtain ⟨C, hC, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 16 (by norm_num)
  set e := Real.exp 1
  have he : 0 < e := Real.exp_pos 1
  set K := 425 * e * C0 * C ^ 2
  have hK : 0 < K := by positivity
  refine ⟨max 65536 (max ((48 * C ^ 2) ^ 8) ((8 * e * K) ^ 4)),
    fun x hx P hSP hPle' n hn hxn hnx => ?_⟩
  have hx1 : (65536 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hxA : (48 * C ^ 2) ^ 8 ≤ (x : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxB : (8 * e * K) ^ 4 ≤ (x : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : (0 : ℝ) < x := by linarith
  set t := (x : ℝ) ^ ((1 : ℝ) / 16) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht16 : t ^ 16 = (x : ℝ) := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht2 : 2 ≤ t := LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 16)
    (by norm_num) ht0 (by norm_num) ht16 (by norm_num at hx1 ⊢; linarith)
  have hCt2 : 48 * C ^ 2 ≤ t ^ 2 :=
    LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 8) (by norm_num)
      (by positivity) (by positivity) (by rw [← pow_mul]; exact ht16) hxA
  have hKt4 : 8 * e * K ≤ t ^ 4 :=
    LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 4) (by norm_num)
      (by positivity) (by positivity) (by rw [← pow_mul]; exact ht16) hxB
  have hx65 : (65536 : ℕ) ≤ x := by exact_mod_cast hx1
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnr : (n : ℝ) ≤ x := by exact_mod_cast hnx
  have hτn := hτ n hn1
  have hn16 : (n : ℝ) ^ ((16 : ℕ) : ℝ)⁻¹ ≤ t := by
    rw [ht_def]; norm_num
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) hnr (by norm_num)
  have hτt : (n.divisors.card : ℝ) ≤ C * t := hτn.trans (mul_le_mul_of_nonneg_left hn16 hC.le)
  have hτ0 : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
  have hτ2 : (n.divisors.card : ℝ) ^ 2 ≤ C ^ 2 * t ^ 2 := by
    have := pow_le_pow_left₀ hτ0 hτt 2; nlinarith
  -- the floor square root S, then P ≥ S
  set S := Nat.sqrt x
  have hSx : x < (S + 1) * (S + 1) := Nat.lt_succ_sqrt x
  have hS8 : t ^ 8 / 2 ≤ (S : ℝ) := by
    have h : (x : ℝ) < ((S : ℝ) + 1) ^ 2 := by
      have : ((x : ℕ) : ℝ) < (((S + 1) * (S + 1) : ℕ) : ℝ) := by exact_mod_cast hSx
      push_cast at this; nlinarith
    have h2 : t ^ 8 < (S : ℝ) + 1 := by
      by_contra hc; push_neg at hc
      have hsq := pow_le_pow_left₀ (by positivity) hc 2
      have h16 : (t ^ 8) ^ 2 = (x : ℝ) := by rw [← pow_mul]; exact ht16
      linarith
    have : 2 ≤ t ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 8]
    linarith
  have hSPr : (S : ℝ) ≤ P := by exact_mod_cast hSP
  have hP8 : t ^ 8 / 2 ≤ (P : ℝ) := hS8.trans hSPr
  have hP2 : 2 ≤ P := by
    have : (2 : ℝ) ≤ P := by nlinarith [pow_le_pow_left₀ (by norm_num) ht2 8]
    exact_mod_cast this
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hPle : (P : ℝ) ≤ x := by exact_mod_cast hPle'
  have hsqP : t ^ 4 / 2 ≤ Real.sqrt P := by
    apply Real.le_sqrt_of_sq_le
    have : (t ^ 4 / 2) ^ 2 = t ^ 8 / 4 := by ring
    rw [this]; have : 0 ≤ t ^ 8 := by positivity
    linarith
  have hlogt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < t by linarith); linarith
  have hlogx : Real.log x = 16 * Real.log t := by
    rw [← ht16, Real.log_pow]; norm_num
  have hlogP : Real.log P ≤ 16 * t := by
    have := Real.log_le_log hPr hPle; rw [hlogx] at this; linarith
  have hlogP0 : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hb1 : 1 + Real.log P / Real.log 2 ≤ 25 * t := by
    have : Real.log P / Real.log 2 ≤ 16 * t / 0.69 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have : 16 * t / 0.69 ≤ 24 * t := by rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hb2 : 1 + Real.log P ≤ 17 * t := by linarith
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
      have h48 : 48 * C ^ 2 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right hCt2 ht2'
      have h44 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      have hτ12 : 12 * (n.divisors.card : ℝ) ^ 2 ≤ 12 * (C ^ 2 * t ^ 2) := by linarith
      linarith
    linarith
  have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hXP : (x : ℝ) / (2 * π ^ 2 * P) ≤ t ^ 8 := by
    rw [div_le_iff₀ (by positivity)]
    have : (x : ℝ) = t ^ 8 * t ^ 8 := by rw [← pow_add]; exact ht16.symm
    rw [this]
    have h8 : 0 ≤ t ^ 8 := by positivity
    have hPP : (P : ℝ) ≤ π ^ 2 * P := by
      have := mul_le_mul_of_nonneg_right hpi hPr.le; linarith
    have h2P : t ^ 8 ≤ 2 * π ^ 2 * P := by linarith
    exact mul_le_mul_of_nonneg_left h2P h8
  have herr : (x : ℝ) / (2 * π ^ 2 * P) * (C0 * (e * (1 + Real.log P / Real.log 2)) *
      (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P)) ≤ K * t ^ 12 := by
    have h1 : 0 ≤ 1 + Real.log P / Real.log 2 := by positivity
    have h2 : 0 ≤ 1 + Real.log P := by linarith
    calc (x : ℝ) / (2 * π ^ 2 * P) * (C0 * (e * (1 + Real.log P / Real.log 2)) *
          (n.divisors.card : ℝ) ^ 2 * (1 + Real.log P))
        ≤ t ^ 8 * (C0 * (e * (25 * t)) * (C ^ 2 * t ^ 2) * (17 * t)) := by
          apply mul_le_mul hXP _ (by positivity) (by positivity)
          apply mul_le_mul _ hb2 h2 (by positivity)
          apply mul_le_mul _ hτ2 (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ hC0.le
          exact mul_le_mul_of_nonneg_left hb1 he.le
      _ = K * t ^ 12 := by simp only [K]; ring
  have hKt : K * t ^ 12 ≤ (x : ℝ) / (8 * e) := by
    rw [le_div_iff₀ (by positivity), ← ht16]
    have h12 : 0 ≤ t ^ 12 := by positivity
    have : K * t ^ 12 * (8 * e) = (8 * e * K) * t ^ 12 := by ring
    rw [this]
    calc (8 * e * K) * t ^ 12 ≤ t ^ 4 * t ^ 12 := mul_le_mul_of_nonneg_right hKt4 h12
      _ = t ^ 16 := by ring
  have hmt : (x : ℝ) / (2 * e) * (1 / 2) ≤
      (n * Real.exp (-(n : ℝ) / x)) * (1 - 12 * (n.divisors.card : ℝ) ^ 2 / Real.sqrt P) :=
    mul_le_mul hA hbr (by norm_num) (by positivity)
  have hfin : (x : ℝ) / (2 * e) * (1 / 2) - (x : ℝ) / (8 * e) = (x : ℝ) / (8 * e) := by
    field_simp; ring
  linarith

/-! ### (4.19) is o(x) -/

theorem RΛ_nonneg (n : ℕ) : 0 ≤ RΛ n :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

/-- For `x ≥ 20^16`, every non-Goldbach `1 ≤ n ≤ x` has `R_Λ(n) ≤ x/(16e)`. -/
theorem RΛ_small : ∃ X0 : ℝ, ∀ x : ℕ, X0 ≤ x → ∀ n : ℕ, 1 ≤ n → n ≤ x →
    ¬ IsGoldbachSum n → RΛ n ≤ x / (16 * Real.exp 1) := by
  refine ⟨20 ^ 16, fun x hx n hn1 hnx hng => ?_⟩
  have hx0 : (0 : ℝ) < x := by
    have : (0 : ℝ) < 20 ^ 16 := by norm_num
    linarith
  set t := (x : ℝ) ^ ((1 : ℝ) / 16) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht16 : t ^ 16 = (x : ℝ) := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht20 : 20 ≤ t := LeanLab.ExceptionalSet.PintzAlthofer2026CoefLower.le_of_pow_le (m := 16)
    (by norm_num) ht0 (by norm_num) ht16 hx
  have hsx : Real.sqrt x = t ^ 8 := by
    rw [← ht16, show t ^ 16 = (t ^ 8) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hnr : (n : ℝ) ≤ x := by exact_mod_cast hnx
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1r
  have hlognx : Real.log n ≤ Real.log x := Real.log_le_log (by linarith) hnr
  have hlogt : Real.log t ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < t by linarith); linarith
  have hlogx : Real.log x = 16 * Real.log t := by
    rw [← ht16, Real.log_pow]; norm_num
  have hL : Real.log x ≤ 16 * t := by rw [hlogx]; linarith
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hsn : Real.sqrt n ≤ t ^ 8 := hsx ▸ Real.sqrt_le_sqrt hnr
  have h1 := RΛ_le_real hng hn1
  have hdiv : Real.log n / Real.log 2 ≤ 24 * t := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hsq : Real.log n ^ 2 ≤ 256 * t ^ 2 := by nlinarith
  have ht8 : 1 ≤ t ^ 8 := one_le_pow₀ (by linarith)
  have h2 : 2 * (Real.sqrt n + 1) * (Real.log n / Real.log 2) * Real.log n ^ 2
      ≤ 2 * (2 * t ^ 8) * (24 * t) * (256 * t ^ 2) := by
    have hd0 : 0 ≤ Real.log n / Real.log 2 := div_nonneg hlogn0 (by linarith)
    apply mul_le_mul _ hsq (by positivity) (by positivity)
    apply mul_le_mul _ hdiv hd0 (by positivity)
    linarith
  have he : Real.exp 1 < 2.72 := by
    have := Real.exp_one_lt_d9; linarith
  have ht5 : (24576 * 16 * 2.72 : ℝ) ≤ t ^ 5 := by
    have : (20 : ℝ) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by norm_num) ht20 5
    nlinarith
  have h3 : 2 * (2 * t ^ 8) * (24 * t) * (256 * t ^ 2) ≤ x / (16 * Real.exp 1) := by
    rw [le_div_iff₀ (by positivity), ← ht16]
    have hep : 0 < Real.exp 1 := Real.exp_pos 1
    have h11 : 0 ≤ t ^ 11 := by positivity
    have : 2 * (2 * t ^ 8) * (24 * t) * (256 * t ^ 2) * (16 * Real.exp 1)
        = (24576 * 16 * Real.exp 1) * t ^ 11 := by ring
    rw [this, show t ^ 16 = t ^ 5 * t ^ 11 by ring]
    apply mul_le_mul_of_nonneg_right _ h11
    nlinarith
  linarith

/-! ### The coefficient of `F_X² − V_X²` and the lower half -/

/-- The major arc model coefficient `v_X(n)`, (4.14), at the paper's truncation `P = ⌊2√x⌋`. -/
noncomputable def model (x n : ℕ) : ℂ :=
  LeanLab.ExceptionalSet.PintzAlthofer2026Beta.vTrunc x (Ppaper x) (Ppaper x)
    (fun q => ((bS n q : ℝ) : ℂ)) n

/-- The `n`-th Fourier coefficient of `F_X² − V_X²`: `R_Λ(n) e^{−n/x} − v_X(n)`. -/
noncomputable def coefF (x n : ℕ) : ℂ :=
  ((RΛ n * Real.exp (-(n : ℝ) / x) : ℝ) : ℂ) - model x n

/-- (4.18) with (4.19): for large `x`, at every bad even `n ∈ (x/2, x]`, `‖coefF x n‖ ≥ x/(16e)`. -/
theorem coef_window : ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x → ∀ n ∈ windowSet x,
    (x : ℝ) / (16 * Real.exp 1) ≤ ‖coefF x n‖ := by
  obtain ⟨X1, hX1⟩ := coef_lower_gen
  obtain ⟨X2, hX2⟩ := RΛ_small
  refine ⟨max 4 (max ⌈X1⌉₊ ⌈X2⌉₊), fun x hx n hn => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : X1 ≤ x := by
    have : ⌈X1⌉₊ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    exact (Nat.le_ceil X1).trans (by exact_mod_cast this)
  have hx2 : X2 ≤ x := by
    have : ⌈X2⌉₊ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    exact (Nat.le_ceil X2).trans (by exact_mod_cast this)
  simp only [windowSet, Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hlo, hhi⟩, hev, hng⟩ := hn
  have hxn : x / 2 < n := by omega
  have hm := hX1 x hx1 (Ppaper x) (sqrt_le_Ppaper x) (Ppaper_le x hx4) n hev hxn hhi
  have hr := hX2 x hx2 n (by omega) hhi hng
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  set r := RΛ n * Real.exp (-(n : ℝ) / x)
  have hr0 : 0 ≤ r := mul_nonneg (RΛ_nonneg n) (Real.exp_pos _).le
  have hrle : r ≤ RΛ n := by
    apply mul_le_of_le_one_right (RΛ_nonneg n)
    apply Real.exp_le_one_iff.2
    have : (0 : ℝ) ≤ n / x := by positivity
    rw [neg_div]; linarith
  have hnr : ‖((r : ℝ) : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have htri : ‖model x n‖ - ‖((r : ℝ) : ℂ)‖ ≤ ‖coefF x n‖ := by
    have := norm_sub_norm_le (model x n) ((r : ℝ) : ℂ)
    rw [norm_sub_rev] at this
    exact this
  have hep : 0 < Real.exp 1 := Real.exp_pos 1
  have hhalf : (x : ℝ) / (8 * Real.exp 1) - x / (16 * Real.exp 1) = x / (16 * Real.exp 1) := by
    field_simp; ring
  unfold model at htri
  linarith

/-! ### The upper half, the only input left -/

/-- The L² upper half of Section 4.4, ALONE, as a Prop, NOT proved: for every `η > 0`, for large
`x`, the squares of the coefficients of `F_X² − V_X²` over the bad even `n ∈ (x/2, x]` sum to at
most `K x^{2a(θ)+1+2η} log x`. The paper gets it from Bessel's inequality and (4.13), Lemma 4. -/
def UpperHalf (θ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∃ X0 : ℕ, ∀ x : ℕ, X0 ≤ x →
    ∑ n ∈ windowSet x, ‖coefF x n‖ ^ 2 ≤ K * (x : ℝ) ^ (2 * a θ + 1 + 2 * η) * Real.log x

/-- The split: the upper half alone gives `BesselInput`, the lower half is `coef_window`. -/
theorem bessel_of_upperHalf {θ : ℝ} (hU : UpperHalf θ) : BesselInput θ := by
  intro η hη
  obtain ⟨K, X0, hK⟩ := hU η hη
  obtain ⟨X1, hX1⟩ := coef_window
  refine ⟨K, 1 / (16 * Real.exp 1), max X0 X1, by positivity, fun x hx =>
    ⟨fun n => ‖coefF x n‖, ?_, ?_⟩⟩
  · intro n hn
    rw [abs_norm]
    have := hX1 x (le_trans (le_max_right _ _) hx) n hn
    calc 1 / (16 * Real.exp 1) * (x : ℝ) = x / (16 * Real.exp 1) := by ring
      _ ≤ _ := this
  · exact hK x (le_trans (le_max_left _ _) hx)

/-- Theorem 3 of Pintz-Althöfer, CONDITIONAL ON `UpperHalf θ` only. -/
theorem theorem3_of_upperHalf {θ : ℝ} (h1 : 1 / 2 ≤ θ) (h2 : θ ≤ 2 / 3) (hU : UpperHalf θ) :
    ∀ ε : ℝ, 0 < ε → PowerBound (g θ + ε) :=
  theorem3_of_bessel h1 h2 (bessel_of_upperHalf hU)

/-- θ = 5/8, CONDITIONAL ON `UpperHalf (5/8)` only: `E(X) ≪ X^{25/44+ε}`. -/
theorem five_eighths_of_upperHalf (hU : UpperHalf (5 / 8)) :
    ∀ ε : ℝ, 0 < ε → PowerBound (25 / 44 + ε) :=
  five_eighths_of_bessel (bessel_of_upperHalf hU)

/-- Vacuity for `coef_window`'s range: `Ppaper` is the paper's `2√x`, e.g. `Ppaper 100 = 20`. -/
example : Ppaper 100 = 20 := by
  show Nat.sqrt (20 ^ 2) = 20
  exact Nat.sqrt_eq' 20

end LeanLab.ExceptionalSet.PintzAlthofer2026Split
