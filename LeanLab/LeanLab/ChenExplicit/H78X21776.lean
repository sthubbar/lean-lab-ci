/-
Lean Lab, ChenExplicit, unit U-6725, track T2 FRONTIER, session 20261020T1914Z-cloud49.
Port of H78X2.lean, PC unit U-1238, from log log X₂ = 18 to 17.76, by gen/port_h78_U6725.py.
P0009 BJS 2022, arXiv 2207.09452: the X₂-only constants c₄(X₂) (134), l(X₂) (156), l₁(X₂) (158)
and p(X₂) of Lemma 31, (87), at log log X₂ = 17.76, with the Siegel term y^{β₀}/β₀ of (79) replaced
by y^{7/8}/(7/8). Forms as in H78X2.lean with 18 replaced by 17.76, and in l₁ the α and ε of
H78Margin1776.lean.

PROVED, 0 sorry: `br_le`, `p_bounds`, `c4_bounds`, `l_bounds`, `l1_bounds`, each of c₄, l, l₁ in
[0, 10⁻¹²]; then `chenPos_1776`: every even N > exp(exp 17.76) is a prime plus a number with at most
two prime factors, CONDITIONAL ON BJS Theorems 44 (a), 50 (a), 51 at u₀ = 5·10⁴, α = 989·10⁻⁶,
ε = 6.1·10⁻⁵, ε₂ = 0 as cited sieve bounds; through them on Hθ 7/8, an unrefereed claim, and the
paper's Lemma 17. AI wrote this Lean code. Chen's theorem is not in doubt; binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.H78Margin1776

open Real

noncomputable section
namespace LeanLab.ChenExplicit.H78X21776

open LeanLab.ChenExplicit LeanLab.ChenExplicit.H781776

/-- `log X₂ = e¹⁸`. -/
def LX : ℝ := exp 17.76
/-- `log x₁(X₂) = log X₂ − 5 log log X₂`. -/
def Lx : ℝ := exp 17.76 - 5 * 17.76

/-- (80) `𝓔(y)` at `y = exp L`, as BJSp.EE. -/
def EE (L : ℝ) : ℝ :=
  4 * exp L * (L ^ 4 * √L) / (L - 5 * log L) ^ 10 + 4 * exp L / (L ^ 5 * √L) +
    18 * exp (11 / 12 * L) / √L + 5 / 2 * exp (5 / 6 * L) * (L ^ 5 * √L)

/-- (87)'s bracket at `y = exp L`, BJSp.br with `β₀ = 7/8`. -/
def br (L : ℝ) : ℝ :=
  L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8 + exp (7 / 8 * L) / (7 / 8))
    + 27 * EE L + √(exp L) / (2 * log 2 * L ^ 8) + 0.4 * L ^ 3)

/-- `p₂(X₂)`, the supremum over `y ≥ x₁(X₂)`. -/
def p2 : ℝ := ⨆ L : Set.Ici Lx, br L
/-- Lemma 31, `p₁(X₂)`. -/
def p1 : ℝ := p2 + 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6))
/-- Lemma 31, `p(X₂)`. -/
def p : ℝ := p1 * (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) + 2.2 / LX ^ 2
/-- (134) `c₄(X₂)`. -/
def c4 : ℝ := p + 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 17.76)
/-- (156) `l(X₂)`. -/
def l : ℝ :=
  p * (1 / LX + 0.55) +
    1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 / (exp LX * 17.76 * Lx ^ 10)
/-- (158) `l₁(X₂)`, `g = e^γ`, `C₁ = 106`, α and ε of H78Margin. -/
def l1 (g : ℝ) : ℝ :=
  LX ^ 2 / exp LX * (2 * g / H781776.kα + H781776.ε * 106 * exp 2 * Section9.h H781776.kα) *
    (exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 17.76) +
      p * exp LX / LX ^ 4)

lemma Lx_ge : (5.13 * 10 ^ 7 : ℝ) ≤ Lx := by unfold Lx; have := expT_ge; linarith
lemma LX_ge : (5.13 * 10 ^ 7 : ℝ) ≤ LX := by unfold LX; have := expT_ge; linarith
lemma Lx_le_LX : Lx ≤ LX := by unfold Lx LX; linarith

/-- `x^k/exp(c x) ≤ n! c^{-n} x^{k−n}`, in the shape used below. -/
lemma decay (x c B : ℝ) (k n : ℕ) (hx : 0 < x) (hc : 0 < c)
    (hB : (Nat.factorial n : ℝ) / c ^ n * x ^ k / x ^ n ≤ B) : x ^ k / exp (c * x) ≤ B :=
  le_trans (pow_div_exp_le x c k n hx hc) hB

/-- `L − 5 log L ≥ L/2` for `L ≥ 6.5·10⁷`. -/
lemma half_le (L : ℝ) (hL : 5.13 * 10 ^ 7 ≤ L) : L / 2 ≤ L - 5 * log L := by
  have := log_le_lin L (by linarith); nlinarith

lemma br_nonneg (L : ℝ) (hL : 5.13 * 10 ^ 7 ≤ L) : 0 ≤ br L := by
  unfold br EE
  have hL0 : 0 < L := by linarith
  have h1 : 0 ≤ log (L ^ 10) := log_nonneg (one_le_pow₀ (by linarith))
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have h3 : 0 < L - 5 * log L := by have := half_le L hL; linarith
  positivity

set_option maxHeartbeats 2000000 in
/-- **(87)'s bracket under 7/8 is at most 10⁻¹⁵ for `log y ≥ 6.5·10⁷`.** -/
theorem br_le (L : ℝ) (hL : 5.13 * 10 ^ 7 ≤ L) : br L ≤ 1 / 10 ^ 15 := by
  have hL0 : 0 < L := by linarith
  have hE : 0 < exp L := exp_pos L
  have hsq : √L ≤ L := by
    rw [sqrt_le_left (by linarith)]; nlinarith
  have hsq1 : 1 ≤ √L := by rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have hlog10 : log (L ^ 10) ≤ 10 * L := by
    rw [log_pow]; push_cast; have := log_le_sub_one_of_pos hL0; linarith
  have hlog0 : 0 ≤ log (L ^ 10) := log_nonneg (one_le_pow₀ (by linarith))
  have hhalf := half_le L hL
  have hL3 : (1.3 * 10 ^ 23 : ℝ) ≤ L ^ 3 := by
    have : (5.13 * 10 ^ 7 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at this ⊢; linarith
  have hL5 : (3.5 * 10 ^ 38 : ℝ) ≤ L ^ 5 := by
    have : (5.13 * 10 ^ 7 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
    norm_num at this ⊢; linarith
  have hL6 : (1.8 * 10 ^ 46 : ℝ) ≤ L ^ 6 := by
    have : (5.13 * 10 ^ 7 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL 6
    norm_num at this ⊢; linarith
  -- split the bracket
  have e : br L =
      3.52e-8 * log (L ^ 10) / L ^ 6 +
      1.1 * log (L ^ 10) * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)) +
      108 * (L ^ 6 * √L) / (L - 5 * log L) ^ 10 +
      108 / (L ^ 3 * √L) +
      486 * (L ^ 2 / exp (1 / 12 * L)) / √L +
      67.5 * √L * (L ^ 7 / exp (1 / 6 * L)) +
      L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) +
      0.4 * (L ^ 5 / exp (1 * L)) := by
    unfold br EE
    have hs : √(exp L) * √(exp L) = exp L := mul_self_sqrt hE.le
    have hsp : 0 < √(exp L) := sqrt_pos.mpr hE
    have e1 : exp L = exp (7 / 8 * L) * exp (1 / 8 * L) := by rw [← exp_add]; ring_nf
    have e2 : exp L = exp (11 / 12 * L) * exp (1 / 12 * L) := by rw [← exp_add]; ring_nf
    have e3 : exp L = exp (5 / 6 * L) * exp (1 / 6 * L) := by rw [← exp_add]; ring_nf
    have h0 : (0 : ℝ) < L - 5 * log L := by linarith
    have hsL : 0 < √L := by linarith
    have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have ha : 0 < exp (7 / 8 * L) := exp_pos _
    have hb : 0 < exp (1 / 8 * L) := exp_pos _
    have hc : 0 < exp (11 / 12 * L) := exp_pos _
    have hd : 0 < exp (1 / 12 * L) := exp_pos _
    have hf : 0 < exp (5 / 6 * L) := exp_pos _
    have hg : 0 < exp (1 / 6 * L) := exp_pos _
    rw [one_mul]
    have key : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8 + exp (7 / 8 * L) / (7 / 8)) +
        27 * (4 * exp L * (L ^ 4 * √L) / (L - 5 * log L) ^ 10 + 4 * exp L / (L ^ 5 * √L) +
          18 * exp (11 / 12 * L) / √L + 5 / 2 * exp (5 / 6 * L) * (L ^ 5 * √L)) +
        √(exp L) / (2 * log 2 * L ^ 8) + 0.4 * L ^ 3) =
      L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8)) +
      L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp (7 / 8 * L) / (7 / 8))) +
      L ^ 2 / exp L * (27 * (4 * exp L * (L ^ 4 * √L) / (L - 5 * log L) ^ 10)) +
      L ^ 2 / exp L * (27 * (4 * exp L / (L ^ 5 * √L))) +
      L ^ 2 / exp L * (27 * (18 * exp (11 / 12 * L) / √L)) +
      L ^ 2 / exp L * (27 * (5 / 2 * exp (5 / 6 * L) * (L ^ 5 * √L))) +
      L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) +
      L ^ 2 / exp L * (0.4 * L ^ 3) := by ring
    rw [key]
    have k1 : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (3.2e-8 * exp L / L ^ 8)) =
        3.52e-8 * log (L ^ 10) / L ^ 6 := by field_simp; try ring
    have k2 : L ^ 2 / exp L * (1.1 * log (L ^ 10) * (exp (7 / 8 * L) / (7 / 8))) =
        1.1 * log (L ^ 10) * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)) := by
      rw [e1]; field_simp; try ring
    have k3 : L ^ 2 / exp L * (27 * (4 * exp L * (L ^ 4 * √L) / (L - 5 * log L) ^ 10)) =
        108 * (L ^ 6 * √L) / (L - 5 * log L) ^ 10 := by field_simp; try ring
    have k4 : L ^ 2 / exp L * (27 * (4 * exp L / (L ^ 5 * √L))) = 108 / (L ^ 3 * √L) := by
      field_simp; try ring
    have k5 : L ^ 2 / exp L * (27 * (18 * exp (11 / 12 * L) / √L)) =
        486 * (L ^ 2 / exp (1 / 12 * L)) / √L := by rw [e2]; field_simp; try ring
    have k6 : L ^ 2 / exp L * (27 * (5 / 2 * exp (5 / 6 * L) * (L ^ 5 * √L))) =
        67.5 * √L * (L ^ 7 / exp (1 / 6 * L)) := by rw [e3]; field_simp; try ring
    have k8 : L ^ 2 / exp L * (0.4 * L ^ 3) = 0.4 * (L ^ 5 / exp L) := by ring
    rw [k1, k2, k3, k4, k5, k6, k8]
  rw [e]
  -- bound each
  have b1 : 3.52e-8 * log (L ^ 10) / L ^ 6 ≤ 1 / 10 ^ 30 := by
    rw [div_le_iff₀ (by positivity)]
    have : 3.52e-8 * log (L ^ 10) ≤ 3.52e-8 * (10 * L) := by nlinarith
    have hL5' : 0 ≤ L ^ 5 := by positivity
    have : L ^ 6 = L * L ^ 5 := by ring
    norm_num at * ; nlinarith
  have b2 : 1.1 * log (L ^ 10) * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)) ≤ 1 / 10 ^ 20 := by
    have hd := pow_div_exp_le L (1 / 8) 3 8 hL0 (by norm_num)
    have hf : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
    rw [hf] at hd
    have hq : (40320 : ℝ) / (1 / 8) ^ 8 * L ^ 3 / L ^ 8 = 40320 * 8 ^ 8 / L ^ 5 := by
      field_simp; try ring
    rw [hq] at hd
    have hd2 : L ^ 3 / exp (1 / 8 * L) ≤ 40320 * 8 ^ 8 / (3.5 * 10 ^ 38) :=
      le_trans hd (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL5)
    have e' : 1.1 * log (L ^ 10) * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)) ≤
        1.1 * (10 * L) * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)) := by
      have : 0 ≤ L ^ 2 / exp (1 / 8 * L) := by positivity
      have := mul_le_mul_of_nonneg_right hlog10 (by positivity : (0:ℝ) ≤ 1.1 * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)))
      nlinarith
    have e'' : 1.1 * (10 * L) * (8 / 7) * (L ^ 2 / exp (1 / 8 * L)) =
        1.1 * 10 * (8 / 7) * (L ^ 3 / exp (1 / 8 * L)) := by ring
    rw [e''] at e'
    have : 1.1 * 10 * (8 / 7) * (L ^ 3 / exp (1 / 8 * L)) ≤
        1.1 * 10 * (8 / 7) * (40320 * 8 ^ 8 / (3.5 * 10 ^ 38)) :=
      mul_le_mul_of_nonneg_left hd2 (by norm_num)
    norm_num at this e' ⊢; linarith
  have b3 : 108 * (L ^ 6 * √L) / (L - 5 * log L) ^ 10 ≤ 1 / 10 ^ 16 := by
    have hh : (L / 2) ^ 10 ≤ (L - 5 * log L) ^ 10 := pow_le_pow_left₀ (by positivity) hhalf 10
    have hpos : 0 < (L / 2) ^ 10 := by positivity
    have h1 : 108 * (L ^ 6 * √L) / (L - 5 * log L) ^ 10 ≤ 108 * (L ^ 6 * √L) / (L / 2) ^ 10 :=
      div_le_div_of_nonneg_left (by positivity) hpos hh
    have h2 : 108 * (L ^ 6 * √L) / (L / 2) ^ 10 ≤ 108 * 1024 / L ^ 3 := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      have : L ^ 6 * √L ≤ L ^ 7 := by
        have : L ^ 7 = L ^ 6 * L := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hsq (by positivity)
      have e : (L / 2) ^ 10 = L ^ 10 / 1024 := by ring
      rw [e]
      have : 108 * (L ^ 6 * √L) * L ^ 3 ≤ 108 * L ^ 7 * L ^ 3 := by
        have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ L ^ 3); nlinarith
      have e2 : 108 * 1024 * (L ^ 10 / 1024) = 108 * L ^ 7 * L ^ 3 := by ring
      linarith
    have h3 : (108 * 1024 : ℝ) / L ^ 3 ≤ 108 * 1024 / (1.3 * 10 ^ 23) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL3
    norm_num at h3 ⊢; linarith
  have b4 : 108 / (L ^ 3 * √L) ≤ 1 / 10 ^ 20 := by
    have : L ^ 3 ≤ L ^ 3 * √L := le_mul_of_one_le_right (by positivity) hsq1
    have h1 : 108 / (L ^ 3 * √L) ≤ 108 / L ^ 3 := div_le_div_of_nonneg_left (by norm_num) (by positivity) this
    have h3 : (108 : ℝ) / L ^ 3 ≤ 108 / (1.3 * 10 ^ 23) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL3
    norm_num at h3 ⊢; linarith
  have b5 : 486 * (L ^ 2 / exp (1 / 12 * L)) / √L ≤ 1 / 10 ^ 20 := by
    have hd := pow_div_exp_le L (1 / 12) 2 8 hL0 (by norm_num)
    have hf : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
    rw [hf] at hd
    have hq : (40320 : ℝ) / (1 / 12) ^ 8 * L ^ 2 / L ^ 8 = 40320 * 12 ^ 8 / L ^ 6 := by
      field_simp; try ring
    rw [hq] at hd
    have hd2 : L ^ 2 / exp (1 / 12 * L) ≤ 40320 * 12 ^ 8 / (1.8 * 10 ^ 46) :=
      le_trans hd (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL6)
    have h1 : 486 * (L ^ 2 / exp (1 / 12 * L)) / √L ≤ 486 * (L ^ 2 / exp (1 / 12 * L)) :=
      div_le_self (by positivity) hsq1
    have : 486 * (L ^ 2 / exp (1 / 12 * L)) ≤ 486 * (40320 * 12 ^ 8 / (1.8 * 10 ^ 46)) :=
      mul_le_mul_of_nonneg_left hd2 (by norm_num)
    norm_num at this ⊢; linarith
  have b6 : 67.5 * √L * (L ^ 7 / exp (1 / 6 * L)) ≤ 1 / 10 ^ 20 := by
    have hd := pow_div_exp_le L (1 / 6) 8 14 hL0 (by norm_num)
    have hf : (Nat.factorial 14 : ℝ) = 87178291200 := by norm_num [Nat.factorial]
    rw [hf] at hd
    have hq : (87178291200 : ℝ) / (1 / 6) ^ 14 * L ^ 8 / L ^ 14 = 87178291200 * 6 ^ 14 / L ^ 6 := by
      field_simp; try ring
    rw [hq] at hd
    have hd2 : L ^ 8 / exp (1 / 6 * L) ≤ 87178291200 * 6 ^ 14 / (1.8 * 10 ^ 46) :=
      le_trans hd (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL6)
    have h1 : 67.5 * √L * (L ^ 7 / exp (1 / 6 * L)) ≤ 67.5 * (L ^ 8 / exp (1 / 6 * L)) := by
      have : √L * (L ^ 7 / exp (1 / 6 * L)) ≤ L * (L ^ 7 / exp (1 / 6 * L)) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      have e : L * (L ^ 7 / exp (1 / 6 * L)) = L ^ 8 / exp (1 / 6 * L) := by ring
      nlinarith
    have : 67.5 * (L ^ 8 / exp (1 / 6 * L)) ≤ 67.5 * (87178291200 * 6 ^ 14 / (1.8 * 10 ^ 46)) :=
      mul_le_mul_of_nonneg_left hd2 (by norm_num)
    norm_num at this ⊢; linarith
  have b7 : L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) ≤ 1 / 10 ^ 40 := by
    have hl2 : 0.69 ≤ log (2 : ℝ) := by have := log_two_gt_d9; linarith
    have hse : √(exp L) ≤ exp L := by
      rw [sqrt_le_left hE.le]; have := add_one_le_exp L; nlinarith
    have h1 : √(exp L) / (2 * log 2 * L ^ 8) ≤ exp L / (2 * log 2 * L ^ 8) :=
      div_le_div_of_nonneg_right hse (by positivity)
    have h2 : L ^ 2 / exp L * (exp L / (2 * log 2 * L ^ 8)) = 1 / (2 * log 2 * L ^ 6) := by
      field_simp; try ring
    have h3 : L ^ 2 / exp L * (√(exp L) / (2 * log 2 * L ^ 8)) ≤
        L ^ 2 / exp L * (exp L / (2 * log 2 * L ^ 8)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [h2] at h3
    have h4 : 1 / (2 * log 2 * L ^ 6) ≤ 1 / 10 ^ 40 := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    linarith
  have b8 : 0.4 * (L ^ 5 / exp (1 * L)) ≤ 1 / 10 ^ 18 := by
    have hd := pow_div_exp_le L 1 5 8 hL0 (by norm_num)
    have hf : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
    rw [hf] at hd
    have hq : (40320 : ℝ) / 1 ^ 8 * L ^ 5 / L ^ 8 = 40320 / L ^ 3 := by field_simp; try ring
    rw [hq] at hd
    have hd2 : L ^ 5 / exp (1 * L) ≤ 40320 / (1.3 * 10 ^ 23) :=
      le_trans hd (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL3)
    have : 0.4 * (L ^ 5 / exp (1 * L)) ≤ 0.4 * (40320 / (1.3 * 10 ^ 23)) :=
      mul_le_mul_of_nonneg_left hd2 (by norm_num)
    norm_num at this ⊢; linarith
  linarith

lemma bdd : BddAbove (Set.range fun L : Set.Ici Lx => br L) := by
  refine ⟨1 / 10 ^ 15, ?_⟩
  rintro _ ⟨⟨L, hL⟩, rfl⟩
  exact br_le L (le_trans Lx_ge hL)

lemma p2_bounds : 0 ≤ p2 ∧ p2 ≤ 1 / 10 ^ 15 := by
  have hne : Nonempty (Set.Ici Lx) := ⟨⟨Lx, (Set.mem_Ici.mpr le_rfl)⟩⟩
  constructor
  · have := le_ciSup bdd ⟨Lx, (Set.mem_Ici.mpr le_rfl)⟩
    have h0 := br_nonneg Lx Lx_ge
    unfold p2; linarith
  · unfold p2
    exact ciSup_le fun ⟨L, hL⟩ => br_le L (le_trans Lx_ge hL)

lemma p_bounds : 0 ≤ p ∧ p ≤ 1 / 10 ^ 14 := by
  obtain ⟨q0, q1⟩ := p2_bounds
  have hx := Lx_ge
  have hX := LX_ge
  have hx8 : (10 ^ 40 : ℝ) ≤ Lx ^ 8 := by
    have : (5.13 * 10 ^ 7 : ℝ) ^ 8 ≤ Lx ^ 8 := pow_le_pow_left₀ (by norm_num) hx 8
    norm_num at this ⊢; linarith
  have he : 0 < exp (Lx / 6) := exp_pos _
  have he2 : 2 / exp (Lx / 6) ≤ 2 := by
    apply div_le_self (by norm_num); have := add_one_le_exp (Lx / 6); linarith
  have hp1a : 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6)) ≤ 3 / 10 ^ 40 := by
    have : 1 / Lx ^ 8 ≤ 1 / 10 ^ 40 := one_div_le_one_div_of_le (by norm_num) hx8
    have h0 : 0 ≤ 0.67 + 2 / exp (Lx / 6) := by positivity
    calc 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6)) ≤ 1 / 10 ^ 40 * (0.67 + 2 / exp (Lx / 6)) :=
          mul_le_mul_of_nonneg_right this h0
      _ ≤ 1 / 10 ^ 40 * 3 := by apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
      _ = 3 / 10 ^ 40 := by ring
  have hp1b : 0 ≤ 1 / Lx ^ 8 * (0.67 + 2 / exp (Lx / 6)) := by positivity
  have hp1 : 0 ≤ p1 ∧ p1 ≤ 1 / 10 ^ 15 + 3 / 10 ^ 40 := by unfold p1; constructor <;> linarith
  have hf1 : 1 / (LX ^ 2 * Lx ^ 3) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 1 ≤ LX ^ 2 := one_le_pow₀ (by linarith)
    have : 1 ≤ Lx ^ 3 := one_le_pow₀ (by linarith)
    nlinarith
  have hf2 : 1 / ((1 - 4 / Lx) * LX) ≤ 1 := by
    have h4 : 4 / Lx ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    rw [div_le_one (by apply mul_pos (by linarith) (by linarith))]; nlinarith
  have hf1' : 0 ≤ 1 / (LX ^ 2 * Lx ^ 3) := by positivity
  have hf2' : 0 ≤ 1 / ((1 - 4 / Lx) * LX) := by
    have h4 : 4 / Lx ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    apply div_nonneg one_pos.le; apply mul_nonneg (by linarith) (by linarith)
  have hX2 : 2.2 / LX ^ 2 ≤ 1 / 10 ^ 15 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hX20 : 0 ≤ 2.2 / LX ^ 2 := by positivity
  unfold p
  constructor
  · have : 0 ≤ p1 * (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) :=
      mul_nonneg hp1.1 (by linarith)
    linarith
  · have : p1 * (1 + 1 / (LX ^ 2 * Lx ^ 3) + 1 / ((1 - 4 / Lx) * LX)) ≤ (1 / 10 ^ 15 + 3 / 10 ^ 40) * 3 :=
      mul_le_mul hp1.2 (by linarith) (by linarith) (by norm_num)
    norm_num at this hX2 ⊢; linarith

/-- `√(exp Lx)/exp LX` is at most `exp(−LX/2)`. -/
lemma sqrt_ratio : √(exp Lx) / exp LX ≤ exp (-(LX / 2)) := by
  have h : √(exp Lx) = exp (Lx / 2) := by
    have : exp Lx = exp (Lx / 2) * exp (Lx / 2) := by rw [← exp_add]; ring_nf
    rw [this, sqrt_mul_self (exp_pos _).le]
  rw [h, ← exp_sub]; apply exp_le_exp.mpr; have := Lx_le_LX; linarith

lemma tiny_exp : LX ^ 4 * exp (-(LX / 2)) ≤ 1 / 10 ^ 30 := by
  have hX := LX_ge
  have hX0 : 0 < LX := by linarith
  have hd := pow_div_exp_le LX (1 / 2) 4 12 hX0 (by norm_num)
  have hf : (Nat.factorial 12 : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at hd
  have hq : (479001600 : ℝ) / (1 / 2) ^ 12 * LX ^ 4 / LX ^ 12 = 479001600 * 2 ^ 12 / LX ^ 8 := by
    field_simp; try ring
  rw [hq] at hd
  have hX8 : (4 * 10 ^ 61 : ℝ) ≤ LX ^ 8 := by
    have : (5.13 * 10 ^ 7 : ℝ) ^ 8 ≤ LX ^ 8 := pow_le_pow_left₀ (by norm_num) hX 8
    norm_num at this ⊢; linarith
  have hd2 : LX ^ 4 / exp (1 / 2 * LX) ≤ 479001600 * 2 ^ 12 / (4 * 10 ^ 61) :=
    le_trans hd (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX8)
  have e : LX ^ 4 * exp (-(LX / 2)) = LX ^ 4 / exp (1 / 2 * LX) := by
    rw [exp_neg, div_eq_mul_inv]; ring_nf
  rw [e]; norm_num at hd2 ⊢; linarith

theorem c4_bounds : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 12 := by
  obtain ⟨p0, p1'⟩ := p_bounds
  have hx := Lx_ge
  have hX := LX_ge
  have hx10 : 1 ≤ Lx ^ 10 := one_le_pow₀ (by linarith)
  have hs := sqrt_ratio
  have ht := tiny_exp
  have hEX : 0 < exp LX := exp_pos _
  have hterm : 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 17.76) ≤ 1 / 10 ^ 30 := by
    have e : 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 17.76) =
        0.9 / (Lx ^ 10 * 17.76) * (LX ^ 4 * (√(exp Lx) / exp LX)) := by field_simp
    rw [e]
    have h1 : 0.9 / (Lx ^ 10 * 17.76) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have h2 : LX ^ 4 * (√(exp Lx) / exp LX) ≤ 1 / 10 ^ 30 := by
      have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ LX ^ 4); linarith
    have h3 : 0 ≤ LX ^ 4 * (√(exp Lx) / exp LX) := by positivity
    calc 0.9 / (Lx ^ 10 * 17.76) * (LX ^ 4 * (√(exp Lx) / exp LX)) ≤ 1 * (1 / 10 ^ 30) :=
          mul_le_mul h1 h2 h3 (by norm_num)
      _ = 1 / 10 ^ 30 := one_mul _
  have hterm0 : 0 ≤ 0.9 * √(exp Lx) * LX ^ 4 / (exp LX * Lx ^ 10 * 17.76) := by positivity
  unfold c4; constructor <;> norm_num at * <;> linarith

theorem l_bounds : 0 ≤ l ∧ l ≤ 1 / 10 ^ 12 := by
  obtain ⟨p0, p1'⟩ := p_bounds
  have hx := Lx_ge
  have hX := LX_ge
  have hx10 : 1 ≤ Lx ^ 10 := one_le_pow₀ (by linarith)
  have hs := sqrt_ratio
  have ht := tiny_exp
  have h8 := Section9.log83_le
  have h80 := Section9.log83_nonneg
  have hEX : 0 < exp LX := exp_pos _
  have hX3 : LX ^ 3 ≤ LX ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hfac : 1 / LX + 0.55 ≤ 1 := by
    have : 1 / LX ≤ 1 / 10 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hfac0 : 0 ≤ 1 / LX + 0.55 := by positivity
  have hs64 : 64 / LX ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hterm : 1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 / (exp LX * 17.76 * Lx ^ 10) ≤
      1 / 10 ^ 29 := by
    have e : 1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 / (exp LX * 17.76 * Lx ^ 10) =
        1.3841 * (log (8 / 3) + 64 / LX ^ 2) / (17.76 * Lx ^ 10) * (LX ^ 3 * (√(exp Lx) / exp LX)) := by
      field_simp
    rw [e]
    have h1 : 1.3841 * (log (8 / 3) + 64 / LX ^ 2) / (17.76 * Lx ^ 10) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have h1' : 0 ≤ 1.3841 * (log (8 / 3) + 64 / LX ^ 2) / (17.76 * Lx ^ 10) := by positivity
    have hr0 : 0 ≤ √(exp Lx) / exp LX := by positivity
    have h2 : LX ^ 3 * (√(exp Lx) / exp LX) ≤ 1 / 10 ^ 30 := by
      have a := mul_le_mul_of_nonneg_right hX3 hr0
      have b := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ LX ^ 4)
      linarith
    have h3 : 0 ≤ LX ^ 3 * (√(exp Lx) / exp LX) := by positivity
    calc 1.3841 * (log (8 / 3) + 64 / LX ^ 2) / (17.76 * Lx ^ 10) * (LX ^ 3 * (√(exp Lx) / exp LX))
        ≤ 1 * (1 / 10 ^ 30) := mul_le_mul h1 h2 h3 (by norm_num)
      _ ≤ 1 / 10 ^ 29 := by norm_num
  have hterm0 : 0 ≤ 1.3841 * (log (8 / 3) + 64 / LX ^ 2) * √(exp Lx) * LX ^ 3 / (exp LX * 17.76 * Lx ^ 10) := by
    positivity
  have hpm : p * (1 / LX + 0.55) ≤ 1 / 10 ^ 14 :=
    le_trans (mul_le_of_le_one_right p0 hfac) p1'
  have hpm0 : 0 ≤ p * (1 / LX + 0.55) := mul_nonneg p0 hfac0
  unfold l; constructor <;> norm_num at * <;> linarith

theorem l1_bounds : 0 ≤ l1 gE ∧ l1 gE ≤ 1 / 10 ^ 12 := by
  obtain ⟨p0, p1'⟩ := p_bounds
  have hX := LX_ge
  have hX0 : 0 < LX := by linarith
  have hg1 := Section9.g_ge
  have hg2 := Section9.g_le
  have hk : exp 2 * Section9.h H781776.kα = 1 := Section9.h_low _ (by norm_num) (by norm_num)
  have hA : 2 * gE / H781776.kα + H781776.ε * 106 * exp 2 * Section9.h H781776.kα ≤ 3 := by
    have e : H781776.ε * 106 * exp 2 * Section9.h H781776.kα = H781776.ε * 106 * (exp 2 * Section9.h H781776.kα) := by ring
    rw [e, hk, mul_one]
    have : 2 * gE / H781776.kα ≤ 2.7 := by rw [div_le_iff₀ (by norm_num)]; norm_num; linarith
    norm_num at this ⊢; linarith
  have hA0 : 0 ≤ 2 * gE / H781776.kα + H781776.ε * 106 * exp 2 * Section9.h H781776.kα := by
    have : 0 ≤ Section9.h H781776.kα := Section9.h_nonneg _ (by norm_num)
    have : 0 ≤ 2 * gE / H781776.kα := div_nonneg (by linarith) (by norm_num)
    positivity
  have hE8 : 2 ≤ exp (LX / 8) := by have := add_one_le_exp (LX / 8); linarith
  have hr : exp (LX / 8) / (exp (LX / 8) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hr0 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
  have h8 := Section9.log83_le
  have h80 := Section9.log83_nonneg
  have hs64 : 64 / LX ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have hB : exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 17.76) ≤ 1 := by
    have : (log (8 / 3) + 64 / LX ^ 2) ≤ 2 := by linarith
    have := mul_le_mul hr this (by positivity) (by norm_num)
    nlinarith
  have hB0 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 17.76) := by
    positivity
  have hEX : 0 < exp LX := exp_pos _
  -- LX²/exp LX ≤ 1/10^20
  have hq : LX ^ 2 / exp LX ≤ 1 / 10 ^ 20 := by
    have hd := pow_div_exp_le LX 1 2 6 hX0 (by norm_num)
    have hf : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hf] at hd
    have hq' : (720 : ℝ) / 1 ^ 6 * LX ^ 2 / LX ^ 6 = 720 / LX ^ 4 := by field_simp; try ring
    rw [hq', one_mul] at hd
    have hX4 : (6.9 * 10 ^ 30 : ℝ) ≤ LX ^ 4 := by
      have : (5.13 * 10 ^ 7 : ℝ) ^ 4 ≤ LX ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
      norm_num at this ⊢; linarith
    have := le_trans hd (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX4)
    norm_num at this ⊢; linarith
  have hq0 : 0 ≤ LX ^ 2 / exp LX := by positivity
  -- the p part: LX²/exp LX · p · exp LX/LX⁴ = p/LX²
  have hpp : p * exp LX / LX ^ 4 ≤ exp LX / LX ^ 2 * (1 / 10 ^ 14) := by
    have e : p * exp LX / LX ^ 4 = exp LX / LX ^ 2 * (p / LX ^ 2) := by field_simp
    rw [e]
    have : p / LX ^ 2 ≤ 1 / 10 ^ 14 := le_trans (div_le_self p0 (one_le_pow₀ (by linarith))) p1'
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hpp0 : 0 ≤ p * exp LX / LX ^ 4 := by positivity
  unfold l1
  constructor
  · positivity
  · have hsum : exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 17.76) +
        p * exp LX / LX ^ 4 ≤ 1 + exp LX / LX ^ 2 * (1 / 10 ^ 14) := by linarith
    have hsum0 : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 17.76) +
        p * exp LX / LX ^ 4 := by linarith
    calc LX ^ 2 / exp LX * (2 * gE / H781776.kα + H781776.ε * 106 * exp 2 * Section9.h H781776.kα) *
          (exp (LX / 8) / (exp (LX / 8) - 1) * (log (8 / 3) + 64 / LX ^ 2) * (1.3841 / 17.76) +
            p * exp LX / LX ^ 4)
        ≤ LX ^ 2 / exp LX * 3 * (1 + exp LX / LX ^ 2 * (1 / 10 ^ 14)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hA hq0) hsum hsum0 (by positivity)
      _ = 3 * (LX ^ 2 / exp LX) + 3 / 10 ^ 14 := by field_simp
      _ ≤ 3 * (1 / 10 ^ 20) + 3 / 10 ^ 14 := by linarith
      _ ≤ 1 / 10 ^ 12 := by norm_num

/-- **Chen's theorem above exp(exp 17.76) in the 7/8 setting, the X₂-only constants PROVED.**
CONDITIONAL ON the three cited sieve bounds at u₀ = 5·10⁴, α = 989/10⁶, ε = 6.1·10⁻⁵, ε₂ = 0,
with c₄, l₁, l the paper's own (134), (158), (156) at the 7/8 Siegel term. -/
theorem chenPos_1776 (hA : Thm44At 17.76 (cA1776 c4)) (hQ : Thm50At 17.76 (cQ1776 (l1 gE) l))
    (hB : Thm51At 17.76 cB1776) : ChenPosAt 17.76 :=
  chenPos1776_of_sieveBounds c4 (l1 gE) l c4_bounds l1_bounds l_bounds hA hQ hB

end LeanLab.ChenExplicit.H78X21776

#print axioms LeanLab.ChenExplicit.H78X21776.br_le
#print axioms LeanLab.ChenExplicit.H78X21776.p_bounds
#print axioms LeanLab.ChenExplicit.H78X21776.c4_bounds
#print axioms LeanLab.ChenExplicit.H78X21776.l_bounds
#print axioms LeanLab.ChenExplicit.H78X21776.l1_bounds
#print axioms LeanLab.ChenExplicit.H78X21776.chenPos_1776
