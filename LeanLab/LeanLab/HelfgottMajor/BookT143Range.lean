import Mathlib
import LeanLab.HelfgottMajor.BookL1523

/-!
# Helfgott's book, Part IV of 2020-04-01, Theorem 14.3: the bisection maxima for `r ≤ r₀`

Unit U-1427, PC run 20261021T1303Z-13145, P0014. AI wrote this file.

`E` is `BookE.E`, the function of (15.2) of the book. The exponential term of the proofs of
Theorem 14.3 on book pp. 448 to 451 is, for `r ≤ r₀`,
`max(1.05, 2.72/√r) · exp(-E(r)/(rπ²) · K²)`, with `K = 1375/32`, `r₀ = 1375/(128π²)` in part 1
and `K = 125/2`, `r₀ = 125/(8π²)` in part 2. On `r ≤ r₀ < 1.6` the max is `2.72/√r`.

Method, interval bounds: on `[a, b]`, `E(r)/r ≥ E(b)/b` by `lemma_15_23` and `1/√r ≤ 1/√a`, so
the term is at most `2.72 s/M` with `s² a ≥ 1` and `M ≤ exp Y`, `Y ≤ E(b)/(bπ²)K²`: `piece`.
`E(b)` is bounded below by `E_lower` of BookE with 20 digit witnesses, the arctan through
`π/4 - P17((1 - X)/(1 + X))` or the degree 19 alternating polynomial `P19_le_arctan`.
At `b = r₀` the inputs are `BookE.E_p1` and `BookE.E_c4`. The pieces were chosen greedily and
checked in exact rational arithmetic by scratch scripts u1427_gen.py, u1427_plan.py,
u1427_lean.py. Python, 30 digits: the part 1 maximum on `[0.1, r₀]` is 1.5929817·10⁻⁹ at `r₀`,
on `[0.001, 0.1]` it is 6.0131242·10⁻⁹ at `r = 0.001`; the part 2 maximum on `[0.1, r₀]` is
1.8018503·10⁻¹⁸ at `r₀`.

PROVED:
* tools `P19_le_arctan`, `atanA_19`, `atanA_17`, `E_at`, `E_upper`, `y_of_E`, `y_upper`, `piece`;
* `bisect_p1`: part 1 term `≤ 1.59299·10⁻⁹` on `0.1 ≤ r ≤ r₀`, eight pieces;
* `mid_p1`: part 1 term `≤ 6.02·10⁻⁹` on `0.001 ≤ r ≤ 0.1`, two pieces;
* `mid_p1_gap`: at `r = 0.001` the part 1 term exceeds `6.01·10⁻⁹`, so `1.59299·10⁻⁹` is not a
  bound on all of `[0.001, r₀]`; the book's `ε₊` uses the larger `1.15275·10⁻⁷`, so no harm;
* `bisect_p2`: part 2 term `≤ 1.80186·10⁻¹⁸` on `0.1 ≤ r ≤ r₀`, six pieces;
* `range_p1`: for `0 < r ≤ r₀` with `1/√r ≤ 606.225`, the part 1 term is `≤ 1.15275·10⁻⁷`;
  `range_p1_mid`: `≤ 6.02·10⁻⁹` for `0.001 ≤ r ≤ r₀`;
* `range_p2`: for `0 < r ≤ r₀` with `1/√r ≤ 584.033`, the part 2 term is `≤ 1.80186·10⁻¹⁸`,
  which confirms the printed bisection value `1.8019·10⁻¹⁸` of p. 450;
* `eps_p1_range`, `eps_p2_range`: the resulting `ε₊ ≤ 1.93·10⁻⁶` of part 1, and for part 2 the
  product with `log(1.35·10⁸/2π)` lies in `(1.81·10⁻¹⁸, 3.05·10⁻¹⁷]`, so the corrected
  `ε'₊ = 3.05·10⁻¹⁷` is needed, not the printed `1.81·10⁻¹⁸`.

Ternary Goldbach is Helfgott's theorem; binary Goldbach is OPEN. AI-written Lean code,
Claude, 2026-10-21.
-/

namespace LeanLab.HelfgottMajor.BookT143Range
open Real Set Finset
open LeanLab.HelfgottMajor.BookE LeanLab.HelfgottMajor.BookL1523

/-- The alternating Taylor polynomial of `arctan` of degree 19. -/
noncomputable def P19 (w : ℝ) : ℝ :=
  w - w ^ 3 / 3 + w ^ 5 / 5 - w ^ 7 / 7 + w ^ 9 / 9 - w ^ 11 / 11 + w ^ 13 / 13 - w ^ 15 / 15 +
    w ^ 17 / 17 - w ^ 19 / 19

/-- **`P19 w ≤ arctan w` for `w ≥ 0`**: the derivative of `P19 - arctan` is `-w²⁰/(1 + w²)`. -/
theorem P19_le_arctan {w : ℝ} (hw : 0 ≤ w) : P19 w ≤ arctan w := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => P19 x - arctan x)
      (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 + x ^ 16 - x ^ 18 -
        1 / (1 + x ^ 2)) x := by
    intro x
    have h := (((((((((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 5)).sub ((hasDerivAt_pow 7 x).div_const 7)).add
      ((hasDerivAt_pow 9 x).div_const 9)).sub ((hasDerivAt_pow 11 x).div_const 11)).add
      ((hasDerivAt_pow 13 x).div_const 13)).sub ((hasDerivAt_pow 15 x).div_const 15)).add
      ((hasDerivAt_pow 17 x).div_const 17)).sub ((hasDerivAt_pow 19 x).div_const 19)).sub
      (hasDerivAt_arctan x))
    convert h using 1
    · funext y; simp [P19]
    · push_cast; ring
  have hanti : Antitone (fun x => P19 x - arctan x) := by
    apply antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have : 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 + x ^ 16 - x ^ 18 -
        1 / (1 + x ^ 2) = -(x ^ 20 / (1 + x ^ 2)) := by
      field_simp; ring
    rw [this]
    have : 0 ≤ x ^ 20 / (1 + x ^ 2) := by positivity
    linarith
  have := hanti hw
  simp [P19] at this
  simp only [P19]; linarith

lemma atanA_19 {X A : ℝ} (h0 : 0 ≤ X) (h : A ≤ P19 X) : A ≤ arctan X :=
  h.trans (P19_le_arctan h0)

lemma atanA_17 {X A : ℝ} (h0 : 0 ≤ X) (h1 : X < 1)
    (h : A ≤ 3.14159265358979323846 / 4 - P17 ((1 - X) / (1 + X))) : A ≤ arctan X := by
  have := arctan_ge_of_lt_one h0 h1
  have := pi_lo
  linarith

/-- `E(b) ≥ A/2 - (uU - 1)/b` from square witnesses and `A ≤ arctan XL`. -/
theorem E_at {b sL sU XL uU A : ℝ} (hb : 0 < b) (hsL : sL ^ 2 ≤ 1 + b ^ 2) (hsU0 : 0 ≤ sU)
    (hsU : 1 + b ^ 2 ≤ sU ^ 2) (hXL : XL ^ 2 ≤ (sL - 1) / 2) (huU0 : 0 ≤ uU)
    (huU : (1 + sU) / 2 ≤ uU ^ 2) (hA : A ≤ arctan XL) : A / 2 - (uU - 1) / b ≤ E b := by
  have := E_lower hb le_rfl le_rfl hsL hsU0 hsU hXL huU0 huU
  linarith

/-- `E(b) ≤ P17(XU)/2 - (uL - 1)/b` from square witnesses. -/
theorem E_upper {b sL sU XU uL : ℝ} (hb : 0 < b) (hsL : sL ^ 2 ≤ 1 + b ^ 2) (hsU0 : 0 ≤ sU)
    (hsU : 1 + b ^ 2 ≤ sU ^ 2) (hXU0 : 0 ≤ XU) (hXU : (sU - 1) / 2 ≤ XU ^ 2)
    (huL : uL ^ 2 ≤ (1 + sL) / 2) : E b ≤ P17 XU / 2 - (uL - 1) / b := by
  set s := √(1 + b ^ 2) with hs
  have hsL' : sL ≤ s := Real.le_sqrt_of_sq_le hsL
  have hsU' : s ≤ sU := (sqrt_le_sqrt hsU).trans_eq (sqrt_sq hsU0)
  have hs1 : 1 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg b])
  have hud : ups b = √((1 + s) / 2) := rfl
  have hu2 : ups b ^ 2 = (1 + s) / 2 := by rw [hud, sq_sqrt (by linarith)]
  have hu1 : 1 ≤ ups b := by rw [hud]; exact Real.le_sqrt_of_sq_le (by linarith)
  have huL' : uL ≤ ups b := by rw [hud]; exact Real.le_sqrt_of_sq_le (by linarith)
  have hX : √(ups b ^ 2 - 1) ≤ XU := by
    rw [hu2]; exact (sqrt_le_sqrt (by linarith)).trans_eq (sqrt_sq hXU0)
  have hat : arctan √(ups b ^ 2 - 1) ≤ arctan XU := arctan_strictMono.monotone hX
  have hP := arctan_le_poly17 hXU0
  have hfrac : (uL - 1) / b ≤ (ups b - 1) / b := by gcongr
  unfold E
  rw [arccos_inv hu1]
  linarith

/-- The exponent `E(b)/(bπ²)·K²` from a lower bound `eL` of `E(b)`. -/
lemma y_of_E {b K eL Y : ℝ} (hb : 0 < b) (hY0 : 0 ≤ Y) (hE : eL ≤ E b)
    (hY : Y * (b * (3.14159265358979323847 : ℝ) ^ 2) ≤ eL * K ^ 2) :
    Y ≤ E b / (b * π ^ 2) * K ^ 2 := by
  have hp := pi_sq_hi
  have hp0 : 0 < π ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h1 : Y * (b * π ^ 2) ≤ Y * (b * (3.14159265358979323847 : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp.le hb.le) hY0
  have h2 : eL * K ^ 2 ≤ E b * K ^ 2 := mul_le_mul_of_nonneg_right hE (sq_nonneg K)
  linarith

/-- The exponent `E(b)/(bπ²)·K²` from an upper bound `eU ≥ 0` of `E(b)`. -/
lemma y_upper {b K eU Y : ℝ} (hb : 0 < b) (heU : 0 ≤ eU) (hE : E b ≤ eU)
    (hY : eU * K ^ 2 ≤ Y * (b * (3.14159265358979323846 : ℝ) ^ 2)) :
    E b / (b * π ^ 2) * K ^ 2 ≤ Y := by
  have hp := pi_sq_lo
  have hp0 : 0 < π ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h2 : E b * K ^ 2 ≤ eU * K ^ 2 := mul_le_mul_of_nonneg_right hE (sq_nonneg K)
  have hK : eU * K ^ 2 * (b * (3.14159265358979323846 : ℝ) ^ 2) ≤ eU * K ^ 2 * (b * π ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp.le hb.le)
      (mul_nonneg heU (sq_nonneg K))
  have hY0 : 0 ≤ Y := by
    by_contra h; push Not at h
    have : Y * (b * (3.14159265358979323846 : ℝ) ^ 2) < 0 :=
      mul_neg_of_neg_of_pos h (by positivity)
    nlinarith [mul_nonneg heU (sq_nonneg K)]
  have h3 : Y * (b * (3.14159265358979323846 : ℝ) ^ 2) ≤ Y * (b * π ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp.le hb.le) hY0
  linarith

/-- **One interval `[a, b]`**: `E(r)/r ≥ E(b)/b` by `lemma_15_23` and `1/√r ≤ 1/√a ≤ s`. -/
theorem piece {a b K Y M s T r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hy : Y ≤ E b / (b * π ^ 2) * K ^ 2) (hM0 : 0 < M) (hM : M ≤ exp Y) (hs0 : 0 ≤ s)
    (hs : 1 ≤ s ^ 2 * a) (hT : 2.72 * s / M ≤ T) (h1 : a ≤ r) (h2 : r ≤ b) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * K ^ 2)) ≤ T := by
  have hr0 : 0 < r := by linarith
  have hb0 : 0 < b := by linarith
  have hG : E b / b ≤ E r / r :=
    lemma_15_23 (show r ∈ Set.Ioi (0 : ℝ) from hr0) (show b ∈ Set.Ioi (0 : ℝ) from hb0) h2
  have hp0 : 0 < π ^ 2 := by positivity
  have hyr : Y ≤ E r / (r * π ^ 2) * K ^ 2 := by
    refine hy.trans ?_
    rw [← div_div, ← div_div]
    gcongr
  have hexp : exp (-(E r / (r * π ^ 2) * K ^ 2)) ≤ 1 / M := by
    calc exp (-(E r / (r * π ^ 2) * K ^ 2)) ≤ exp (-Y) := exp_le_exp.mpr (by linarith)
      _ = 1 / exp Y := by rw [exp_neg, inv_eq_one_div]
      _ ≤ 1 / M := one_div_le_one_div_of_le hM0 hM
  have hsq : 1 / √r ≤ s := by
    have hsa : 1 ≤ s * √a := by
      have e : √(s ^ 2 * a) = s * √a := by
        rw [sqrt_mul (sq_nonneg s), sqrt_sq hs0]
      rw [← e]; exact Real.le_sqrt_of_sq_le (by linarith)
    have hra : √a ≤ √r := sqrt_le_sqrt h1
    have hr' : 0 < √r := sqrt_pos.mpr hr0
    rw [div_le_iff₀ hr']
    nlinarith
  calc 2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * K ^ 2))
      ≤ 2.72 * s * (1 / M) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hexp (exp_pos _).le
          (by positivity)
    _ = 2.72 * s / M := by ring
    _ ≤ T := hT

/-! ## The radii `r₀` -/

lemma r0_p1_bds : (1.0884111524079252 : ℝ) ≤ 1375 / (128 * π ^ 2) ∧
    1375 / (128 * π ^ 2) ≤ (1.0884111524079253 : ℝ) :=
  r_bounds (a := 1375) (b := 128) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma r0_p2_bds : (1.5831434944115276 : ℝ) ≤ 125 / (8 * π ^ 2) ∧
    125 / (8 * π ^ 2) ≤ (1.5831434944115277 : ℝ) :=
  r_bounds (a := 125) (b := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma a_top_p1 : (1.0884014 : ℝ) ≤ 1375 / (128 * π ^ 2) := by
  have := r0_p1_bds.1; linarith

lemma a_top_p2 : (1.5831368 : ℝ) ≤ 125 / (8 * π ^ 2) := by
  have := r0_p2_bds.1; linarith

/-- At `r₀` of part 1 the exponent is `E(r₀)·1375/8 ≥ 21.21593`, `BookE.E_p1`. -/
lemma y_top_p1 : (21.21593 : ℝ) ≤
    E (1375 / (128 * π ^ 2)) / (1375 / (128 * π ^ 2) * π ^ 2) * (1375 / 32 : ℝ) ^ 2 := by
  have h := E_p1
  have hp : π ^ 2 ≠ 0 := by positivity
  have e : ∀ x : ℝ, x / (1375 / (128 * π ^ 2) * π ^ 2) * (1375 / 32 : ℝ) ^ 2 =
      x * 1375 / 8 := by
    intro x; field_simp; ring
  rw [e]; exact h

/-- At `r₀` of part 2 the exponent is `250 E(r₀) ≥ 41.62864`, `BookE.E_c4`. -/
lemma y_top_p2 : (41.62864 : ℝ) ≤
    E (125 / (8 * π ^ 2)) / (125 / (8 * π ^ 2) * π ^ 2) * (125 / 2 : ℝ) ^ 2 := by
  have h := E_c4
  have hp : π ^ 2 ≠ 0 := by positivity
  have e : ∀ x : ℝ, x / (125 / (8 * π ^ 2) * π ^ 2) * (125 / 2 : ℝ) ^ 2 = x * 250 := by
    intro x; field_simp; ring
  rw [e]; exact h

/-! ## The pieces, generated by u1427_lean.py -/

/-- Piece `[1.0884014, r₀]` with target `1.59299e-9`. -/
theorem p1_piece1 {r : ℝ} (h1 : 1.0884014 ≤ r) (h2 : r ≤ 1375 / (128 * π ^ 2)) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hy := y_top_p1
  have hab := a_top_p1
  have hM : (1.636670772e9 : ℝ) ≤ exp 21.21593 := by
    have h := BookT141.exp_lower 21 (r := 0.21593) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.9585294354) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.0883344, 1.0884014]` with target `1.59299e-9`. -/
theorem p1_piece2 {r : ℝ} (h1 : 1.0883344 ≤ r) (h2 : r ≤ 1.0884014) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 1.0884014) (sL := 1.47804519806464646556) (sU := 1.47804519806464646557)
    (XL := 0.48889937516049581547) (uU := 1.11311392006044162703) (A := 0.45472773812614336237)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 21.21596075) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.0883344 : ℝ) ≤ 1.0884014 := by norm_num
  have hM : (1.636721100e9 : ℝ) ≤ exp 21.21596075 := by
    have h := BookT141.exp_lower 21 (r := 0.21596075) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.9585589395) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.0878852, 1.0883344]` with target `1.59299e-9`. -/
theorem p1_piece3 {r : ℝ} (h1 : 1.0878852 ≤ r) (h2 : r ≤ 1.0883344) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 1.0883344) (sL := 1.47799586136881993638) (sU := 1.47799586136881993639)
    (XL := 0.48887414605848197604) (uU := 1.11310283922214930635) (A := 0.45470737582339012172)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 21.21616718) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.0878852 : ℝ) ≤ 1.0883344 := by norm_num
  have hM : (1.637059004e9 : ℝ) ≤ exp 21.21616718 := by
    have h := BookT141.exp_lower 21 (r := 0.21616718) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.9587568189) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.0848782, 1.0878852]` with target `1.59299e-9`. -/
theorem p1_piece4 {r : ℝ} (h1 : 1.0848782 ≤ r) (h2 : r ≤ 1.0878852) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 1.0878852) (sL := 1.47766512051243870456) (sU := 1.47766512051243870457)
    (XL := 0.48870498284365727580) (uU := 1.11302855320796660697) (A := 0.45457083442793108870)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 21.21755111) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.0848782 : ℝ) ≤ 1.0878852 := by norm_num
  have hM : (1.639326147e9 : ℝ) ≤ exp 21.21755111 := by
    have h := BookT141.exp_lower 21 (r := 0.21755111) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.9600846117) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.0649677, 1.0848782]` with target `1.59299e-9`. -/
theorem p1_piece5 {r : ℝ} (h1 : 1.0649677 ≤ r) (h2 : r ≤ 1.0848782) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 1.0848782) (sL := 1.47545271318170003899) (sU := 1.47545271318170003900)
    (XL := 0.48757189889374266469) (uU := 1.11253150813397191601) (A := 0.45365578716738759988)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 21.22681274) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.0649677 : ℝ) ≤ 1.0848782 := by norm_num
  have hM : (1.654579506e9 : ℝ) ≤ exp 21.22681274 := by
    have h := BookT141.exp_lower 21 (r := 0.22681274) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.9690178609) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[0.9422686, 1.0649677]` with target `1.59299e-9`. -/
theorem p1_piece6 {r : ℝ} (h1 : 0.9422686 ≤ r) (h2 : r ≤ 1.0649677) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 1.0649677) (sL := 1.46087514936879188464) (sU := 1.46087514936879188465)
    (XL := 0.48003913870058131159) (uU := 1.10925090700183605590) (A := 0.44755178429806629273)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 21.28801747) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.9422686 : ℝ) ≤ 1.0649677 := by norm_num
  have hM : (1.759010846e9 : ℝ) ≤ exp 21.28801747 := by
    have h := BookT141.exp_lower 21 (r := 0.28801747) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 1.0301788764) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[0.4484321, 0.9422686]` with target `1.59299e-9`. -/
theorem p1_piece7 {r : ℝ} (h1 : 0.4484321 ≤ r) (h2 : r ≤ 0.9422686) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 0.9422686) (sL := 1.37399785827560881245) (sU := 1.37399785827560881246)
    (XL := 0.43243372802986171123) (uU := 1.08949480454833028370) (A := 0.40815019432575620727)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_19 (by norm_num) (by simp only [P19]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 21.65928403) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.4484321 : ℝ) ≤ 0.9422686 := by norm_num
  have hM : (2.549808330e9 : ℝ) ≤ exp 21.65928403 := by
    have h := BookT141.exp_lower 21 (r := 0.65928403) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 1.4933157771) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[0.1, 0.4484321]` with target `1.59299e-9`. -/
theorem p1_piece8 {r : ℝ} (h1 : 0.1 ≤ r) (h2 : r ≤ 0.4484321) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  have hE := E_at (b := 0.4484321) (sL := 1.09594313187793188523) (sU := 1.09594313187793188524)
    (XL := 0.21902412181987157237) (uU := 1.02370482363763722896) (A := 0.21561928839740157911)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_19 (by norm_num) (by simp only [P19]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 22.92247451) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.1 : ℝ) ≤ 0.4484321 := by norm_num
  have hM : (9.017874576e9 : ℝ) ≤ exp 22.92247451 := by
    have h := BookT141.exp_lower 22 (r := 0.92247451) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 3.1622776602) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2
/-- Piece `[1.5831368, r₀]` with target `1.80186e-18`. -/
theorem p2_piece1 {r : ℝ} (h1 : 1.5831368 ≤ r) (h2 : r ≤ 125 / (8 * π ^ 2)) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  have hy := y_top_p2
  have hab := a_top_p2
  have hM : (1.199744147e18 : ℝ) ≤ exp 41.62864 := by
    have h := BookT141.exp_lower 41 (r := 0.62864) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.7947687417) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.5829888, 1.5831368]` with target `1.80186e-18`. -/
theorem p2_piece2 {r : ℝ} (h1 : 1.5829888 ≤ r) (h2 : r ≤ 1.5831368) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  have hE := E_at (b := 1.5831368) (sL := 1.87251759070889371445) (sU := 1.87251759070889371446)
    (XL := 0.66049889882909483714) (uU := 1.19844015092721541263) (A := 0.58372044667512452217)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (125 / 2 : ℝ)) (Y := 41.62868676) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.5829888 : ℝ) ≤ 1.5831368 := by norm_num
  have hM : (1.199800248e18 : ℝ) ≤ exp 41.62868676 := by
    have h := BookT141.exp_lower 41 (r := 0.62868676) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.7948058939) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.5799455, 1.5829888]` with target `1.80186e-18`. -/
theorem p2_piece3 {r : ℝ} (h1 : 1.5799455 ≤ r) (h2 : r ≤ 1.5829888) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  have hE := E_at (b := 1.5829888) (sL := 1.87239246444901075392) (sU := 1.87239246444901075393)
    (XL := 0.66045153662059518063) (uU := 1.19841404874296486903) (A := 0.58368746986047311066)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (125 / 2 : ℝ)) (Y := 41.62964892) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.5799455 : ℝ) ≤ 1.5829888 := by norm_num
  have hM : (1.200955204e18 : ℝ) ≤ exp 41.62964892 := by
    have h := BookT141.exp_lower 41 (r := 0.62964892) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.7955710054) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[1.5186369, 1.5799455]` with target `1.80186e-18`. -/
theorem p2_piece4 {r : ℝ} (h1 : 1.5186369 ≤ r) (h2 : r ≤ 1.5799455) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  have hE := E_at (b := 1.5799455) (sL := 1.86982025418761843082) (sU := 1.86982025418761843083)
    (XL := 0.65947716191981145467) (uU := 1.19787734225746553079) (A := 0.58300872463029780154)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (125 / 2 : ℝ)) (Y := 41.64943753) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (1.5186369 : ℝ) ≤ 1.5799455 := by norm_num
  have hM : (1.224957137e18 : ℝ) ≤ exp 41.64943753 := by
    have h := BookT141.exp_lower 41 (r := 0.64943753) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 0.8114710413) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[0.6821859, 1.5186369]` with target `1.80186e-18`. -/
theorem p2_piece5 {r : ℝ} (h1 : 0.6821859 ≤ r) (h2 : r ≤ 1.5186369) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  have hE := E_at (b := 1.5186369) (sL := 1.81831186380158945494) (sU := 1.81831186380158945495)
    (XL := 0.63965297771588207269) (uU := 1.18707873871146168696) (A := 0.56906696737619840145)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_17 (by norm_num) (by norm_num) (by simp only [P17]; norm_num))
  have hy := y_of_E (K := (125 / 2 : ℝ)) (Y := 42.04957065) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.6821859 : ℝ) ≤ 1.5186369 := by norm_num
  have hM : (1.827664593e18 : ℝ) ≤ exp 42.04957065 := by
    have h := BookT141.exp_lower 42 (r := 0.04957065) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 1.2107336992) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[0.1, 0.6821859]` with target `1.80186e-18`. -/
theorem p2_piece6 {r : ℝ} (h1 : 0.1 ≤ r) (h2 : r ≤ 0.6821859) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  have hE := E_at (b := 0.6821859) (sL := 1.21052781965505030684) (sU := 1.21052781965505030685)
    (XL := 0.32444400106570803017) (uU := 1.05131532369100620536) (A := 0.31372893490076413170)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_19 (by norm_num) (by simp only [P19]; norm_num))
  have hy := y_of_E (K := (125 / 2 : ℝ)) (Y := 47.36681376) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.1 : ℝ) ≤ 0.6821859 := by norm_num
  have hM : (3.725167798e20 : ℝ) ≤ exp 47.36681376 := by
    have h := BookT141.exp_lower 47 (r := 0.36681376) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 3.1622776602) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2
/-- Piece `[0.0011, 0.1]` with target `6.02e-9`. -/
theorem m1_piece1 {r : ℝ} (h1 : 0.0011 ≤ r) (h2 : r ≤ 0.1) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 6.02e-9 := by
  have hE := E_at (b := 0.1) (sL := 1.00498756211208902702) (sU := 1.00498756211208902703)
    (XL := 0.04993777183700243458) (uU := 1.00124611412781248982) (A := 0.04989632254882294214)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_19 (by norm_num) (by simp only [P19]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 23.35955157) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.0011 : ℝ) ≤ 0.1 := by norm_num
  have hM : (1.396125135e10 : ℝ) ≤ exp 23.35955157 := by
    have h := BookT141.exp_lower 23 (r := 0.35955157) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 30.1511344578) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2

/-- Piece `[0.001, 0.0011]` with target `6.02e-9`. -/
theorem m1_piece2 {r : ℝ} (h1 : 0.001 ≤ r) (h2 : r ≤ 0.0011) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 6.02e-9 := by
  have hE := E_at (b := 0.0011) (sL := 1.00000060499981698761) (sU := 1.00000060499981698762)
    (XL := 0.00054999991681254370) (uU := 1.00000015124994280864) (A := 0.00054999986135424559)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (atanA_19 (by norm_num) (by simp only [P19]; norm_num))
  have hy := y_of_E (K := (1375 / 32 : ℝ)) (Y := 23.38383040) (by norm_num) (by norm_num) hE (by norm_num)
  have hab : (0.001 : ℝ) ≤ 0.0011 := by norm_num
  have hM : (1.430436251e10 : ℝ) ≤ exp 23.38383040 := by
    have h := BookT141.exp_lower 23 (r := 0.38383040) (by norm_num) 14
    simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
    norm_num at h ⊢; linarith
  exact piece (s := 31.6227766017) (by norm_num) hab hy (by norm_num) hM (by norm_num) (by norm_num)
    (by norm_num) h1 h2
/-- **Part 1 bisection on `[0.1, r₀]`**, `r₀ = 1375/(128π²)`: eight pieces. -/
theorem bisect_p1 {r : ℝ} (hlo : 0.1 ≤ r) (hhi : r ≤ 1375 / (128 * π ^ 2)) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 1.59299e-9 := by
  rcases le_total r 0.4484321 with k0 | k0
  · exact p1_piece8 hlo k0
  rcases le_total r 0.9422686 with k1 | k1
  · exact p1_piece7 k0 k1
  rcases le_total r 1.0649677 with k2 | k2
  · exact p1_piece6 k1 k2
  rcases le_total r 1.0848782 with k3 | k3
  · exact p1_piece5 k2 k3
  rcases le_total r 1.0878852 with k4 | k4
  · exact p1_piece4 k3 k4
  rcases le_total r 1.0883344 with k5 | k5
  · exact p1_piece3 k4 k5
  rcases le_total r 1.0884014 with k6 | k6
  · exact p1_piece2 k5 k6
  exact p1_piece1 k6 hhi

/-- **Part 2 bisection on `[0.1, r₀]`**, `r₀ = 125/(8π²)`: six pieces. -/
theorem bisect_p2 {r : ℝ} (hlo : 0.1 ≤ r) (hhi : r ≤ 125 / (8 * π ^ 2)) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤ 1.80186e-18 := by
  rcases le_total r 0.6821859 with k0 | k0
  · exact p2_piece6 hlo k0
  rcases le_total r 1.5186369 with k1 | k1
  · exact p2_piece5 k0 k1
  rcases le_total r 1.5799455 with k2 | k2
  · exact p2_piece4 k1 k2
  rcases le_total r 1.5829888 with k3 | k3
  · exact p2_piece3 k2 k3
  rcases le_total r 1.5831368 with k4 | k4
  · exact p2_piece2 k3 k4
  exact p2_piece1 k4 hhi

/-- **Part 1 on `[0.001, 0.1]`**: two pieces. -/
theorem mid_p1 {r : ℝ} (hlo : 0.001 ≤ r) (hhi : r ≤ 0.1) :
    2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 6.02e-9 := by
  rcases le_total r 0.0011 with k0 | k0
  · exact m1_piece2 hlo k0
  exact m1_piece1 k0 hhi

/-! ## The gap at `r = 0.001` for part 1 -/

/-- **At `r = 0.001` the part 1 term exceeds `6.01·10⁻⁹`**; value 6.0131242·10⁻⁹. So the
`1.59299·10⁻⁹` of `r ≥ r₀` is not a bound of the part 1 term on all of `[0.001, r₀]`. -/
theorem mid_p1_gap :
    6.01e-9 < 2.72 * (1 / √0.001) * exp (-(E 0.001 / (0.001 * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) := by
  have hE := E_upper (b := 0.001) (sL := 1.00000049999987500006) (sU := 1.00000049999987500007)
    (XU := 0.00049999993750003110) (uL := 1.00000012499996093751)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have hy := y_upper (K := (1375 / 32 : ℝ)) (Y := 23.38383092) (by norm_num)
    (by simp only [P17]; norm_num) hE (by simp only [P17]; norm_num)
  have he23 : exp (23 : ℝ) ≤ 2.7182818286 ^ 23 := by
    have e : exp (23 : ℝ) = exp 1 ^ 23 := by rw [← exp_nat_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 23
  have hr : exp (0.38383092 : ℝ) ≤ ∑ i ∈ range 12, (0.38383092 : ℝ) ^ i / i.factorial +
      0.38383092 ^ 12 * (12 + 1) / (Nat.factorial 12 * 12) :=
    exp_bound' (by norm_num) (by norm_num) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at hr
  norm_num at hr
  have hM : exp (23.38383092 : ℝ) ≤ 1.430437e10 := by
    have e : exp (23.38383092 : ℝ) = exp 23 * exp 0.38383092 := by rw [← exp_add]; norm_num
    rw [e]
    calc exp 23 * exp 0.38383092 ≤ 2.7182818286 ^ 23 * exp 0.38383092 :=
          mul_le_mul_of_nonneg_right he23 (exp_pos _).le
      _ ≤ 2.7182818286 ^ 23 * (1 + 0.38383092 + 0.38383092 ^ 2 / 2 + 0.38383092 ^ 3 / 6 +
          0.38383092 ^ 4 / 24 + 0.38383092 ^ 5 / 120 + 0.38383092 ^ 6 / 720 +
          0.38383092 ^ 7 / 5040 + 0.38383092 ^ 8 / 40320 + 0.38383092 ^ 9 / 362880 +
          0.38383092 ^ 10 / 3628800 + 0.38383092 ^ 11 / 39916800 +
          0.38383092 ^ 12 * 13 / (479001600 * 12)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          norm_num; linarith
      _ ≤ 1.430437e10 := by norm_num
  have hexp : 1 / 1.430437e10 ≤ exp (-(E 0.001 / (0.001 * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) := by
    calc (1 : ℝ) / 1.430437e10 ≤ 1 / exp 23.38383092 :=
          one_div_le_one_div_of_le (exp_pos _) hM
      _ = exp (-23.38383092) := by rw [exp_neg, inv_eq_one_div]
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hs : √(0.001 : ℝ) ≤ 0.0316227767 := by
    rw [show (0.0316227767 : ℝ) = √(0.0316227767 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num)
  have hs0 : 0 < √(0.001 : ℝ) := sqrt_pos.mpr (by norm_num)
  have hinv : 1 / 0.0316227767 ≤ 1 / √(0.001 : ℝ) := one_div_le_one_div_of_le hs0 hs
  calc (6.01e-9 : ℝ) < 2.72 * (1 / 0.0316227767) * (1 / 1.430437e10) := by norm_num
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hinv (by norm_num)) hexp (by norm_num)
          (by positivity)

/-! ## Theorem 14.3 on all of `0 < r ≤ r₀` -/

lemma max_eq {r : ℝ} (h0 : 0 < r) (h : r ≤ 1.6) :
    max 1.05 (2.72 * (1 / √r)) = 2.72 * (1 / √r) := by
  apply max_eq_right
  have hs : √r ≤ 1.3 := by
    rw [show (1.3 : ℝ) = √(1.3 ^ 2) by rw [sqrt_sq (by norm_num)]]
    exact sqrt_le_sqrt (by norm_num; linarith)
  have hinv : 1 / 1.3 ≤ 1 / √r := one_div_le_one_div_of_le (sqrt_pos.mpr h0) hs
  have : (1.05 : ℝ) ≤ 2.72 * (1 / 1.3) := by norm_num
  linarith

/-- **Part 1 on `0.001 ≤ r ≤ r₀`**: `max(1.05, 2.72/√r) e^{-E(r)/(rπ²)(1375/32)²} ≤ 6.02·10⁻⁹`. -/
theorem range_p1_mid {r : ℝ} (h1 : 0.001 ≤ r) (h2 : r ≤ 1375 / (128 * π ^ 2)) :
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤ 6.02e-9 := by
  have hr0 : 0 < r := by linarith
  have := r0_p1_bds.2
  rw [max_eq hr0 (by linarith)]
  rcases le_total r 0.1 with h | h
  · exact mid_p1 h1 h
  · exact (bisect_p1 h h2).trans (by norm_num)

/-- **Part 1 on `0 < r ≤ r₀`**, with `1/√r ≤ 606.225` as on book p. 449: the term is at most
`1.15275·10⁻⁷`, the value the book multiplies by `log(1.0875·10⁸/2π)` to get `ε₊`. -/
theorem range_p1 {r : ℝ} (h0 : 0 < r) (h2 : r ≤ 1375 / (128 * π ^ 2)) (hs : 1 / √r ≤ 606.225) :
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) ≤
      1.15275e-7 := by
  rcases le_total r 0.001 with h | h
  · have := r0_p1_bds.2
    rw [max_eq h0 (by linarith)]
    calc 2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2))
        ≤ 2.72 * 606.225 * exp (-(E r / (r * π ^ 2) * (1375 / 32 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
            (exp_pos _).le
      _ ≤ 1.15275e-7 := small_p1_all h0 h
  · exact (range_p1_mid h h2).trans (by norm_num)

/-- **Part 2 on `0 < r ≤ r₀`**, with `1/√r ≤ 584.033` as on book p. 450: the term is at most
`1.80186·10⁻¹⁸ ≤ 1.8019·10⁻¹⁸`, the printed bisection value; `0.001 < r < 0.1` by `mid_p2`. -/
theorem range_p2 {r : ℝ} (h0 : 0 < r) (h2 : r ≤ 125 / (8 * π ^ 2)) (hs : 1 / √r ≤ 584.033) :
    max 1.05 (2.72 * (1 / √r)) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) ≤
      1.80186e-18 := by
  have := r0_p2_bds.2
  rw [max_eq h0 (by linarith)]
  rcases le_total r 0.001 with h | h
  · calc 2.72 * (1 / √r) * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2))
        ≤ 2.72 * 584.033 * exp (-(E r / (r * π ^ 2) * (125 / 2 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num))
            (exp_pos _).le
      _ ≤ 5.46217e-19 := small_p2_all h0 h
      _ ≤ 1.80186e-18 := by norm_num
  rcases le_total r 0.1 with h' | h'
  · exact (mid_p2 h h').trans (by norm_num)
  · exact bisect_p2 h' h2

/-- **`ε₊` of part 1 from `range_p1`**: `(1.15275·10⁻⁷ + 1.7763·10⁻⁵⁹) log(1.0875·10⁸/2π) ≤
1.93·10⁻⁶`, `BookT143.eps_p1`, the printed `ε₊`, MATCH. -/
theorem eps_p1_range :
    (1.15275e-7 + 1.7763e-59) * log (108750000 / (2 * π)) ≤ 1.93e-6 := by
  have h := BookT143.eps_p1; linarith [h.1, h.2]

/-- **`ε'₊` of part 2 from `range_p2`**: the product with `log(1.35·10⁸/2π)` is at most
`3.05·10⁻¹⁷` and exceeds the printed `ε'₊ = 1.81·10⁻¹⁸`. -/
theorem eps_p2_range :
    (1.81e-18 : ℝ) < (1.80186e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) ∧
    (1.80186e-18 + 3.9953e-86) * log (1.35e8 / (2 * π)) ≤ 3.05e-17 := by
  obtain ⟨h1, h2⟩ := BookT143.LB_bds
  constructor
  · calc (1.81e-18 : ℝ) < (1.80186e-18 + 3.9953e-86) * 16.8828 := by norm_num
      _ < _ := mul_lt_mul_of_pos_left h1 (by norm_num)
  · calc _ ≤ (1.80186e-18 + 3.9953e-86) * 16.882909 :=
          mul_le_mul_of_nonneg_left h2.le (by norm_num)
      _ ≤ 3.05e-17 := by norm_num

end LeanLab.HelfgottMajor.BookT143Range
