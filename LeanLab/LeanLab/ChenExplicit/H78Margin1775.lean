/-
Lean Lab, ChenExplicit, unit U-6725, track T2 FRONTIER, session 20261020T1914Z-cloud49.
Port of H78Margin.lean, PC unit U-1236, from log log X₂ = 18 to log log X₂ = 17.75, written by
gen/port_h78_U6725.py; model numerics/h78_below18_U6725.py. P0009, Bordignon, Johnston, Starichkova,
arXiv 2207.09452, Section 9 case (a) only, corrected constants of Section9.lean, F-0020 to F-0022,
under the zero-free half-plane Re s > 7/8: no exceptional zero, so k₁ = k₂ = 0 and ε₂ = 0, and the
Siegel term of Lemma 32's v₀ is at most (8/7) y^{−1/8}.

Changes from the 18 file: log log X₂ = 17.75, the L floor 5.09·10⁷ ≤ e^{17.75}; α₁ = α₂ = α₃ = 987·10⁻⁶,
at the u₀ = 5·10⁴ floor; ε₀ = 0.032; log(1 + ε₀) ≥ 0.031435 through 1.003945⁸ ≤ 1.032; the bound
g/(2T) ≤ 1.3618 in Theorem 51's m term; m(X₃) ≤ 1.839·10⁻⁵; the margin κ = 4·10⁻⁴. u₀ = 5·10⁴,
ε = 6.1·10⁻⁵, C₁ = 106, C₂ = 108 unchanged.

PROVED here, 0 sorry: `margin_a1775`, cA − cQ/2 − cB/2 ≥ 4·10⁻⁴ + 10⁻¹² for every log N ≥ e^{17.75};
`m_le1775`; `phi78_le`; `u0cond_44_50`, `u0cond_51`, `ranges1775`, the range hypotheses of Theorems
44, 50, 51 at these parameters; `chenPos1775_of_sieveBounds`: every even N > exp(exp 17.75) is a
prime plus a number with at most two prime factors, CONDITIONAL ON Theorems 44 (a), 50 (a), 51 as
cited sieve bounds Thm44At Thm50At Thm51At at t = 17.75 and on c₄, l₁, l ≤ 10⁻¹². Hθ 7/8 is an
unrefereed claim and enters through those cited bounds. Inner docstrings are inherited from the 18
file with numbers updated where the generator substituted. Chen's theorem itself is not in doubt;
binary Goldbach is OPEN. AI wrote this Lean code.

Stage 2 of gen/port_h78_U6725.py, from the 17.76 file to 17.75: twinC ≥ 0.654, `twinC_ge_0654`,
so g/(2T) ≤ 1.3618 in Theorem 51's m term; log x ≤ x/10⁸ + 17.44, `log_le_lin8`, in the u₀ conditions,
so α = 987·10⁻⁶; the L floor 5.09·10⁷ ≤ e^{17.75}; m(X₃) ≤ 1.839·10⁻⁵; κ = 4·10⁻⁴.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.Section9Link

open Real Finset

noncomputable section
namespace LeanLab.ChenExplicit.H781775

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9

/-- `α₁ = α₂ = α₃ = 987/10⁶`. -/
abbrev α : ℝ := 987 / 10 ^ 6
/-- `ε = 6.1·10⁻⁵ ≥ ε(5·10⁴)`. -/
abbrev ε : ℝ := 61 / 10 ^ 6
/-- `ε₀ = 0.032`. -/
abbrev e0 : ℝ := 32 / 1000
/-- `k_{α₂} = 8(1/6 − α₂)`. -/
abbrev kα : ℝ := 8 * (1 / 6 - α)

/-- `l₂(X₂)`, (160), as Section9.l2 at the new α, ε, C₁ = 106. -/
def l2 (g LX : ℝ) : ℝ :=
  exp (LX / 8) / (exp (LX / 8) - 1) *
    (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + 512 / (kα * LX ^ 2)) +
      (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα)

/-- Theorem 44 (a), corrected, C₂ = 108. -/
def cAa (g T c4 L : ℝ) : ℝ :=
  8 * (1 - 32.02 / L ^ 2) * (fS g (4 - 8 * α) - 108 * ε * exp 2 * h (4 - 8 * α) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L))

/-- Theorem 50 (a), corrected. -/
def cQa (g T l1 l L LX : ℝ) : ℝ := 8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2 g LX) + l * (g / (2 * T))

/-- Theorem 51, corrected, ε₂ = e2, C₁ = 106. -/
def cB (g T e2 cb m L : ℝ) : ℝ :=
  1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) *
      (2 / (1 / 2 - α) * g + 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α)) * (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) +
    g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)))

/-! ### exp 17.75 -/

lemma expT_ge : (5.09 * 10 ^ 7 : ℝ) ≤ exp 17.75 := by
  have he := exp_one_gt_d9
  have h : exp (17.75 : ℝ) = exp 1 ^ 17 * exp 0.1875 ^ 4 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]; congr 1; norm_num
  rw [h]
  have h1 : (2.7182818283 : ℝ) ^ 17 ≤ exp 1 ^ 17 := pow_le_pow_left₀ (by norm_num) he.le 17
  have hq := quadratic_le_exp_of_nonneg (x := (0.1875 : ℝ)) (by norm_num)
  have h2 : ((1 : ℝ) + 0.1875 + 0.1875 ^ 2 / 2) ^ 4 ≤ exp 0.1875 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hq 4
  have h3 : (5.09 * 10 ^ 7 : ℝ) ≤ 2.7182818283 ^ 17 * ((1 : ℝ) + 0.1875 + 0.1875 ^ 2 / 2) ^ 4 := by
    norm_num
  calc (5.09 * 10 ^ 7 : ℝ) ≤ 2.7182818283 ^ 17 * ((1 : ℝ) + 0.1875 + 0.1875 ^ 2 / 2) ^ 4 := h3
    _ ≤ exp 1 ^ 17 * exp 0.1875 ^ 4 := mul_le_mul h1 h2 (by norm_num) (by positivity)

/-! ### numeric facts, `L ≥ 6.5·10⁷` -/

lemma fS_a_ge (g : ℝ) (hg : 0 ≤ g) : g * 0.5490705 ≤ fS g (4 - 8 * α) := by
  unfold fS
  have e : (4 - 8 * α - 1 : ℝ) = 3 * (1 - 8 * α / 3) := by ring
  rw [e, log_mul (by norm_num) (by norm_num)]
  have h1 := Real.one_sub_inv_le_log_of_pos (x := (1 - 8 * α / 3 : ℝ)) (by norm_num)
  have l3 := log_three_gt_d9
  norm_num at h1 l3 ⊢
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma h_le (s : ℝ) (hs : 3.992 ≤ s) : exp 2 * h s ≤ 0.10253 := by
  unfold h
  rw [if_neg (by linarith), if_neg (by linarith)]
  have e : exp 2 * (3 / s * exp (-s)) = 3 / s * (exp (s - 2))⁻¹ := by
    rw [← exp_neg, show -(s - 2) = 2 + -s by ring, exp_add]; ring
  rw [e]
  have e2 : exp (s - 2) = exp 1 * exp 1 * exp (s - 4) := by
    rw [← exp_add, ← exp_add]; ring_nf
  have he := exp_one_gt_d9
  have h4 := add_one_le_exp (s - 4)
  have h1 : (7.32994 : ℝ) ≤ exp (s - 2) := by
    rw [e2]
    have : (2.7182818283 : ℝ) * 2.7182818283 ≤ exp 1 * exp 1 := by
      apply mul_le_mul he.le he.le (by norm_num) (exp_pos 1).le
    have h5 : 0.992 ≤ exp (s - 4) := by linarith
    have : (2.7182818283 : ℝ) * 2.7182818283 * 0.992 ≤ exp 1 * exp 1 * exp (s - 4) := by
      apply mul_le_mul this h5 (by norm_num) (by positivity)
    norm_num at this ⊢; linarith
  have h2 : 3 / s ≤ 3 / 3.992 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h3 : (exp (s - 2))⁻¹ ≤ 1 / 7.32994 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h1
  calc 3 / s * (exp (s - 2))⁻¹ ≤ 3 / 3.992 * (1 / 7.32994) := by
        apply mul_le_mul h2 h3 (by positivity) (by norm_num)
    _ ≤ 0.10253 := by norm_num

lemma Lam_le : (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) ≤ 3.59724 := by
  have h6 : log 6 = log 2 + log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  have hr := log_le_sub_one_of_pos (x := (3 - 8 * α) / (3 - 18 * α)) (by norm_num)
  have := log_two_lt_d9; have := log_three_lt_d9
  rw [h6, div_le_iff₀ (by norm_num)]
  norm_num at *; linarith

lemma r8_le (LX : ℝ) (hLX : 5.09 * 10 ^ 7 ≤ LX) :
    exp (LX / 8) / (exp (LX / 8) - 1) ≤ 1 + 1 / 10 ^ 6 := by
  have h := add_one_le_exp (LX / 8)
  have hE : 6 * 10 ^ 6 ≤ exp (LX / 8) := by linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma l2_le (g LX : ℝ) (hg : 0 ≤ g) (hLX : 5.09 * 10 ^ 7 ≤ LX) :
    l2 g LX ≤ (1 + 1 / 10 ^ 6) * (g / 4 * 3.597241 + 0.98084 * ε * 106) := by
  unfold l2
  have hk : exp 2 * h kα = 1 := h_low kα (by norm_num) (by norm_num)
  have e : (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα =
      (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * (exp 2 * h kα) := by ring
  rw [e, hk, mul_one]
  have hs1 : 512 / (kα * LX ^ 2) ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hs2 : 64 / LX ^ 2 ≤ 1 / 10 ^ 7 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hL := Lam_le
  have h8 := log83_le
  have hr := r8_le LX hLX
  have hpos : 0 ≤ g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
      512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106 := by
    have : 0 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) := by
      apply div_nonneg _ (by norm_num)
      have : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
        log_nonneg (by rw [le_div_iff₀ (by norm_num)]; norm_num)
      have : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
      linarith
    have := log83_nonneg
    positivity
  have hin : g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
      512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106 ≤
      g / 4 * 3.597241 + 0.98084 * ε * 106 := by
    have a1 : g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
        512 / (kα * LX ^ 2)) ≤ g / 4 * 3.597241 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); norm_num at hs1 hL ⊢; linarith
    have a2 : (log (8 / 3) + 64 / LX ^ 2) * ε * 106 ≤ 0.98084 * ε * 106 := by
      have : log (8 / 3) + 64 / LX ^ 2 ≤ 0.98084 := by norm_num at hs2 h8 ⊢; linarith
      have := mul_le_mul_of_nonneg_right this (by norm_num : (0:ℝ) ≤ ε * 106)
      linarith
    linarith
  calc exp (LX / 8) / (exp (LX / 8) - 1) * _ ≤ (1 + 1 / 10 ^ 6) *
        (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
        512 / (kα * LX ^ 2)) + (log (8 / 3) + 64 / LX ^ 2) * ε * 106) :=
        mul_le_mul_of_nonneg_right hr hpos
    _ ≤ _ := mul_le_mul_of_nonneg_left hin (by norm_num)

lemma log1e0_ge : (0.031435 : ℝ) ≤ log (1 + e0) := by
  have hr : (1.003945 : ℝ) ^ 8 ≤ 1 + e0 := by norm_num
  have h1 : log ((1.003945 : ℝ) ^ 8) ≤ log (1 + e0) := log_le_log (by norm_num) hr
  rw [log_pow] at h1
  have h2 := Real.one_sub_inv_le_log_of_pos (x := (1.003945 : ℝ)) (by norm_num)
  push_cast at h1
  norm_num at h2
  linarith

lemma log1e0_le : log (1 + e0) ≤ 32 / 1000 := by
  have := log_le_sub_one_of_pos (x := 1 + e0) (by norm_num); norm_num at this ⊢; linarith

lemma tail_le (L : ℝ) (hL : 5.09 * 10 ^ 7 ≤ L) :
    0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)) ≤ 1 / 10 ^ 12 := by
  have hE := pow_div_factorial_le_exp (x := L / 8) (by positivity) 9
  have hf : (Nat.factorial 9 : ℝ) = 362880 := by norm_num [Nat.factorial]
  rw [hf] at hE
  have hlg := log1e0_ge
  have hq : (0:ℝ) < 0.031435 := by norm_num
  have hlg0 : 0 < log (1 + e0) := lt_of_lt_of_le hq hlg
  have hEp : 0 < exp (L / 8) := exp_pos _
  rw [div_le_iff₀ (by positivity)]
  have h1 : (L / 8) ^ 9 / 362880 * (0.031435) ≤ exp (L / 8) * log (1 + e0) :=
    mul_le_mul hE hlg (by positivity) hEp.le
  have h2 : 0.13 * (1 + e0) * L ^ 5 ≤
      1 / 10 ^ 12 * ((L / 8) ^ 9 / 362880 * (0.031435)) := by
    have hL4 : (6.7 * 10 ^ 30 : ℝ) ≤ L ^ 4 := by
      have : (5.09 * 10 ^ 7 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
      norm_num at this ⊢; linarith
    have : (L / 8) ^ 9 / 362880 * (0.031435) =
        L ^ 5 * L ^ 4 * (1 / (8 ^ 9 * 362880) * (0.031435)) := by ring
    rw [this]
    have hL5 : 0 ≤ L ^ 5 := by positivity
    norm_num
    nlinarith [mul_le_mul_of_nonneg_left hL4 hL5]
  nlinarith

lemma small_div (c L : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 100) (hL : 5.09 * 10 ^ 7 ≤ L) :
    c / L ≤ 1 / 10 ^ 5 := by
  rw [div_le_iff₀ (by linarith)]; nlinarith

lemma small_div2 (c L : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 100) (hL : 5.09 * 10 ^ 7 ≤ L) :
    c / L ^ 2 ≤ 1 / 10 ^ 13 := by
  rw [div_le_iff₀ (by positivity)]; nlinarith

/-- Theorem 44 (a), lower bound. -/
lemma cAa_ge (g T c4 L : ℝ) (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.654 ≤ T)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 12) (hL : 5.09 * 10 ^ 7 ≤ L) :
    8 * (1 - 1 / 10 ^ 13) * (0.5490705 * g - 108 * ε * 0.10253 - 1 / 10 ^ 11) ≤ cAa g T c4 L := by
  unfold cAa
  have hX := fS_a_ge g (by linarith)
  have hH1 : exp 2 * h (4 - 8 * α) ≤ 0.10253 := h_le _ (by norm_num)
  have s2 := small_div2 32.02 L (by norm_num) (by norm_num) hL
  have hd0 : 0 ≤ 32.02 / L ^ 2 := by positivity
  have hL0 : 0 < L := by linarith
  have e : 108 * ε * exp 2 * h (4 - 8 * α) = 108 * ε * (exp 2 * h (4 - 8 * α)) := by ring
  rw [e]
  have t4 : 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) ≤ 1 / 10 ^ 11 := by
    have i1 : (1 - 32.02 / L ^ 2)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by norm_num at s2 ⊢; linarith) (by norm_num)]; norm_num at s2 ⊢; linarith
    have i2 : g / (2 * T) ≤ 1.4 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have i20 : 0 ≤ g / (2 * T) := div_nonneg (by linarith) (by linarith)
    have i3 : c4 / L ≤ 1 / 10 ^ 12 := by
      have : c4 / L ≤ c4 := div_le_self hc4.1 (by linarith)
      linarith [hc4.2]
    have i30 : 0 ≤ c4 / L := div_nonneg hc4.1 hL0.le
    have : (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) ≤ 2 * 1.4 := mul_le_mul i1 i2 i20 (by norm_num)
    have : (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) ≤ 2.8 * (1 / 10 ^ 12) :=
      mul_le_mul (by linarith) i3 i30 (by norm_num)
    have e : 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) =
        1 / 8 * ((1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L)) := by ring
    rw [e]; nlinarith
  set B := fS g (4 - 8 * α) - 108 * ε * (exp 2 * h (4 - 8 * α)) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L) with hB
  have hBl : 0.5490705 * g - 108 * ε * 0.10253 - 1 / 10 ^ 11 ≤ B := by
    rw [hB]
    have := mul_le_mul_of_nonneg_left hH1 (by norm_num : (0:ℝ) ≤ 108 * ε)
    linarith
  have hB0 : 0 ≤ 0.5490705 * g - 108 * ε * 0.10253 - 1 / 10 ^ 11 := by norm_num; linarith
  calc 8 * (1 - 1 / 10 ^ 13) * (0.5490705 * g - 108 * ε * 0.10253 - 1 / 10 ^ 11)
      ≤ 8 * (1 - 32.02 / L ^ 2) * (0.5490705 * g - 108 * ε * 0.10253 - 1 / 10 ^ 11) := by
        apply mul_le_mul_of_nonneg_right _ hB0; norm_num at s2 ⊢; linarith
    _ ≤ 8 * (1 - 32.02 / L ^ 2) * B := by
        apply mul_le_mul_of_nonneg_left hBl; norm_num at s2 ⊢; linarith

/-- Theorem 50 (a), upper bound. -/
lemma cQa_le (g T l1 l L LX : ℝ) (hg : 0 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.654 ≤ T)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 12) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 12)
    (hLX : 5.09 * 10 ^ 7 ≤ LX) (hL : LX ≤ L) :
    cQa g T l1 l L LX ≤
      8.0004 * (1 + 1 / 10 ^ 13) * (1 / 10 ^ 12 + (1 + 1 / 10 ^ 6) * (g / 4 * 3.597241 +
        0.98084 * ε * 106)) + 1.4 / 10 ^ 12 := by
  unfold cQa
  have hl2 := l2_le g LX hg hLX
  have s2 := small_div2 32.02 L (by norm_num) (by norm_num) (hLX.trans hL)
  have hl20 : 0 ≤ l2 g LX := by
    unfold l2
    have hE : 1 < exp (LX / 8) := by have := add_one_le_exp (LX / 8); linarith
    have hr : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := div_nonneg (exp_pos _).le (by linarith)
    have hk : exp 2 * h kα = 1 := h_low kα (by norm_num) (by norm_num)
    have e : (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * exp 2 * h kα =
        (log (8 / 3) + 64 / LX ^ 2) * ε * 106 * (exp 2 * h kα) := by ring
    rw [e, hk, mul_one]
    have : 0 ≤ (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) := by
      apply div_nonneg _ (by norm_num)
      have : 0 ≤ log ((3 - 8 * α) / (3 - 18 * α)) :=
        log_nonneg (by rw [le_div_iff₀ (by norm_num)]; norm_num)
      have : 0 ≤ log (6 : ℝ) := log_nonneg (by norm_num)
      linarith
    have := log83_nonneg
    positivity
  have i2 : g / (2 * T) ≤ 1.4 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have i20 : 0 ≤ g / (2 * T) := div_nonneg hg (by linarith)
  have hlt : l * (g / (2 * T)) ≤ 1 / 10 ^ 12 * 1.4 := mul_le_mul hls.2 i2 i20 (by norm_num)
  have hf : 1 + 32.02 / L ^ 2 ≤ 1 + 1 / 10 ^ 13 := by linarith
  have hin : l1 + l2 g LX ≤ 1 / 10 ^ 12 + (1 + 1 / 10 ^ 6) * (g / 4 * 3.597241 + 0.98084 * ε * 106) := by
    linarith [hl1.2]
  have h0 : 0 ≤ l1 + l2 g LX := by linarith [hl1.1]
  have h1 : 8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2 g LX) ≤
      8.0004 * (1 + 1 / 10 ^ 13) * (1 / 10 ^ 12 + (1 + 1 / 10 ^ 6) * (g / 4 * 3.597241 +
        0.98084 * ε * 106)) := by
    have hp : (0 : ℝ) ≤ 8.0004 * (1 + 32.02 / L ^ 2) := by positivity
    calc 8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2 g LX)
        ≤ 8.0004 * (1 + 32.02 / L ^ 2) * (1 / 10 ^ 12 + (1 + 1 / 10 ^ 6) * (g / 4 * 3.597241 +
          0.98084 * ε * 106)) := mul_le_mul_of_nonneg_left hin hp
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
  norm_num at hlt ⊢; linarith

/-- Theorem 51, upper bound, `ε₂ = 0`. -/
lemma cB_le (g T cb m L : ℝ) (hg : 0 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.654 ≤ T)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 1.839 / 10 ^ 5) (hL : 5.09 * 10 ^ 7 ≤ L) :
    cB g T 0 cb m L ≤
      1.00005 * (1 + 1 / 10 ^ 13) * (2 / (1 / 2 - α) * g + 3 * ε * 106) * (1 + e0 + 1 / 10 ^ 5) *
        (0.363084 + 1 / 10 ^ 13 + 0.98084 * (1 / 10 ^ 5 * (10 * (32 / 1000)) / 100 + 1 / 10 ^ 13)) +
      1.3618 * (320 * (1.839 / 10 ^ 5) * (1 + e0) / (3 * (0.031435)) + 1 / 10 ^ 12) := by
  unfold cB
  have hk : exp 2 * h (3 / 2 - 3 * α) = 1 := h_low _ (by norm_num) (by norm_num)
  have e : 3 * ε * 106 * exp 2 * h (3 / 2 - 3 * α) = 3 * ε * 106 * (exp 2 * h (3 / 2 - 3 * α)) := by ring
  rw [e, hk, mul_one, add_zero, mul_one]
  have hL0 : 0 < L := by linarith
  have s1 : 4.51 / L ^ 2 ≤ 1 / 10 ^ 13 := small_div2 _ _ (by norm_num) (by norm_num) hL
  have s2 : 9 / L ≤ 1 / 10 ^ 5 := small_div _ _ (by norm_num) (by norm_num) hL
  have s3 : 36 / L ^ 2 ≤ 1 / 10 ^ 13 := small_div2 _ _ (by norm_num) (by norm_num) hL
  have s4 : 64 / L ^ 2 ≤ 1 / 10 ^ 13 := small_div2 _ _ (by norm_num) (by norm_num) hL
  have s5 : 27 / L ^ 2 ≤ 1 / 10 ^ 13 := small_div2 _ _ (by norm_num) (by norm_num) hL
  have hl0 := log1e0_le
  have hlg := log1e0_ge
  have hlpos : 0 < log (1 + e0) := lt_of_lt_of_le (by norm_num) hlg
  have s6 : 10 * log (1 + e0) / L ≤ 1 / 10 ^ 5 * (10 * (32 / 1000)) / 100 := by
    rw [div_le_iff₀ hL0]
    have : 10 * log (1 + e0) ≤ 10 * (32 / 1000) := by linarith
    nlinarith
  have h8 := log83_le
  have h80 := log83_nonneg
  -- first summand
  have f1 : 1.00005 * (1 + 4.51 / L ^ 2) ≤ 1.00005 * (1 + 1 / 10 ^ 13) := by linarith
  have f2 : 1 + e0 + 9 / L ≤ 1 + e0 + 1 / 10 ^ 5 := by linarith
  have f3 : cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) ≤
      0.363084 + 1 / 10 ^ 13 + 0.98084 * (1 / 10 ^ 5 * (10 * (32 / 1000)) / 100 + 1 / 10 ^ 13) := by
    have a : log (8 / 3) + 64 / L ^ 2 ≤ 0.98084 := by norm_num at s4 h8 ⊢; linarith
    have b : 10 * log (1 + e0) / L + 27 / L ^ 2 ≤ 1 / 10 ^ 5 * (10 * (32 / 1000)) / 100 + 1 / 10 ^ 13 := by
      linarith
    have b0 : 0 ≤ 10 * log (1 + e0) / L + 27 / L ^ 2 := by positivity
    have : (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) ≤
        0.98084 * (1 / 10 ^ 5 * (10 * (32 / 1000)) / 100 + 1 / 10 ^ 13) :=
      mul_le_mul a b b0 (by norm_num)
    linarith [hcb.2]
  have p1 : 0 ≤ 1.00005 * (1 + 4.51 / L ^ 2) := by positivity
  have p2 : 0 ≤ 2 / (1 / 2 - α) * g + 3 * ε * 106 := by positivity
  have p3 : 0 ≤ 1 + e0 + 9 / L := by positivity
  have p4 : 0 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) := by
    have := hcb.1; positivity
  have first : 1.00005 * (1 + 4.51 / L ^ 2) * (2 / (1 / 2 - α) * g + 3 * ε * 106) * (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) ≤
      1.00005 * (1 + 1 / 10 ^ 13) * (2 / (1 / 2 - α) * g + 3 * ε * 106) * (1 + e0 + 1 / 10 ^ 5) *
        (0.363084 + 1 / 10 ^ 13 + 0.98084 * (1 / 10 ^ 5 * (10 * (32 / 1000)) / 100 + 1 / 10 ^ 13)) := by
    gcongr
  -- second summand
  have i2 : g / (2 * T) ≤ 1.3618 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have i20 : 0 ≤ g / (2 * T) := div_nonneg hg (by linarith)
  have hmt : 320 * m * (1 + e0) / (3 * log (1 + e0)) ≤
      320 * (1.839 / 10 ^ 5) * (1 + e0) / (3 * (0.031435)) := by
    apply div_le_div₀ (by positivity) _ (by norm_num) (by linarith)
    have := hm.2; gcongr
  have htl := tail_le L hL
  have hsec0 : 0 ≤ 320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)) := by
    have := hm.1; positivity
  have second : g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0))) ≤
      1.3618 * (320 * (1.839 / 10 ^ 5) * (1 + e0) / (3 * (0.031435)) + 1 / 10 ^ 12) :=
    mul_le_mul i2 (by linarith) hsec0 (by norm_num)
  linarith

/-- **Section 9 case (a) under 7/8 at log log X₂ = 17.75, u₀ = 5·10⁴: PROVED from the stated
inputs.** `cA − cQ/2 − cB/2 ≥ 4·10⁻⁴ + 10⁻¹²`; with these input bounds about 0.0088. -/
theorem margin_a1775 (g T cb m c4 l1 l L LX : ℝ)
    (hg1 : 1.781 ≤ g) (hg2 : g ≤ 1.7812) (hT : 0.654 ≤ T)
    (hcb : 0 ≤ cb ∧ cb ≤ 0.363084) (hm : 0 ≤ m ∧ m ≤ 1.839 / 10 ^ 5)
    (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 12)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 12) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 12)
    (hLX : 5.09 * 10 ^ 7 ≤ LX) (hL : LX ≤ L) :
    4 / 10 ^ 4 + 1 / 10 ^ 12 ≤ cAa g T c4 L - cQa g T l1 l L LX / 2 - cB g T 0 cb m L / 2 := by
  have hA := cAa_ge g T c4 L hg1 hg2 hT hc4 (hLX.trans hL)
  have hQ := cQa_le g T l1 l L LX (by linarith) hg2 hT hl1 hls hLX hL
  have hB := cB_le g T cb m L (by linarith) hg2 hT hcb hm (hLX.trans hL)
  norm_num at hA hQ hB ⊢
  nlinarith

/-! ### Lemma 32's `m(X₃)` under 7/8, `log log X₂ = 17.75`, `X₃ = X₂^{1/8}` -/

/-- `log X₃ = e^{17.75}/8`. -/
def Λ3 : ℝ := exp 17.75 / 8
/-- `log x₂(X₃)`, (75). -/
def ℓ : ℝ := Λ3 - 15 * log Λ3
/-- The bracket of (72) at `Y = log y` with the Siegel term `y^{β−1}/β` at `β = 7/8`. -/
def φ78 (Y : ℝ) : ℝ :=
  3.2e-8 / Y ^ 4 + Y ^ 4 * (exp (-(Y / 8)) / (7 / 8) + 1.02 * Y ^ 10 / exp (Y / 2) +
    3 * Y ^ 10 / exp (2 * Y / 3))
/-- `v₀(X₃)` of Lemma 29, (71), with `v'₀ = v`. -/
def v0 (v : ℝ) : ℝ := v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) + 3 / Λ3
/-- `m(X₃)`, Lemma 32, as F0023.mX3P. -/
def mX3 (v : ℝ) : ℝ :=
  39 * v0 v + 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) + 26 * Λ3 ^ 5 / ℓ ^ 10 +
    88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) + 106 / Λ3 ^ 6

lemma Λ3_ge : (6.3625 * 10 ^ 6 : ℝ) ≤ Λ3 := by unfold Λ3; have := expT_ge; linarith

lemma log_le_lin (x : ℝ) (hx : 0 < x) : log x ≤ x / 1000000 + 13 := by
  have h1 := log_le_sub_one_of_pos (x := x / 1000000) (by positivity)
  rw [log_div hx.ne' (by norm_num)] at h1
  have h2 : log (1000000 : ℝ) ≤ 14 := by
    rw [log_le_iff_le_exp (by norm_num)]
    have h14 : exp (14 : ℝ) = exp 1 ^ 14 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    have : (2.7182818283 : ℝ) ^ 14 ≤ exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) he.le 14
    have : (1000000 : ℝ) ≤ 2.7182818283 ^ 14 := by norm_num
    rw [h14]; linarith
  linarith

lemma ℓ_ge : 0.998 * Λ3 ≤ ℓ := by
  unfold ℓ
  have h := log_le_lin Λ3 (by linarith [Λ3_ge])
  have := Λ3_ge
  nlinarith

lemma ℓ_ge' : (6.34 * 10 ^ 6 : ℝ) ≤ ℓ := by have := ℓ_ge; have := Λ3_ge; nlinarith

lemma ℓ_pos : 0 < ℓ := by have := ℓ_ge'; linarith

/-- `x^k e^{−c x}`-type decay through `x^n/n! ≤ exp x`. -/
lemma pow_div_exp_le (x c : ℝ) (k n : ℕ) (hx : 0 < x) (hc : 0 < c) :
    x ^ k / exp (c * x) ≤ (Nat.factorial n : ℝ) / c ^ n * x ^ k / x ^ n := by
  have hxpos := hx
  have hE := pow_div_factorial_le_exp (x := c * x) (by positivity) n
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  have hEp : 0 < exp (c * x) := exp_pos _
  rw [div_le_div_iff₀ hEp (by positivity)]
  have : (c * x) ^ n ≤ exp (c * x) * (Nat.factorial n) := by
    rw [div_le_iff₀ hf] at hE; linarith
  have e : (Nat.factorial n : ℝ) / c ^ n * x ^ k * exp (c * x) =
      x ^ k * (exp (c * x) * Nat.factorial n) / c ^ n := by ring
  rw [e, le_div_iff₀ (by positivity)]
  have hxk : 0 ≤ x ^ k := by positivity
  calc x ^ k * x ^ n * c ^ n = x ^ k * (c * x) ^ n := by ring
    _ ≤ x ^ k * (exp (c * x) * Nat.factorial n) := mul_le_mul_of_nonneg_left this hxk

/-- `φ78 Y ≤ 10⁻¹⁵` for `Y ≥ 8·10⁶`. -/
theorem phi78_le (Y : ℝ) (hY : 6.34 * 10 ^ 6 ≤ Y) : φ78 Y ≤ 1 / 10 ^ 15 := by
  unfold φ78
  have hY0 : 0 < Y := by linarith
  have hY4 : (1.6 * 10 ^ 27 : ℝ) ≤ Y ^ 4 := by
    have : (6.34 * 10 ^ 6 : ℝ) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (by norm_num) hY 4
    norm_num at this ⊢; linarith
  -- term 1
  have t1 : 3.2e-8 / Y ^ 4 ≤ 1 / 10 ^ 30 := by
    rw [div_le_iff₀ (by positivity)]; norm_num; nlinarith
  -- term 2: Y^4 exp(-Y/8) ≤ 8! 8^8 / Y^4
  have t2 : Y ^ 4 * (exp (-(Y / 8)) / (7 / 8)) ≤ 2 / 10 ^ 16 := by
    have h := pow_div_exp_le Y (1 / 8) 4 10 hY0 (by norm_num)
    have e : Y ^ 4 * (exp (-(Y / 8)) / (7 / 8)) = 8 / 7 * (Y ^ 4 / exp (1 / 8 * Y)) := by
      rw [exp_neg, show Y / 8 = 1 / 8 * Y by ring]; field_simp
    rw [e]
    have hY6' : (6.4 * 10 ^ 40 : ℝ) ≤ Y ^ 6 := by
      have : (6.34 * 10 ^ 6 : ℝ) ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ (by norm_num) hY 6
      norm_num at this ⊢; linarith
    have hf : (Nat.factorial 10 : ℝ) = 3628800 := by norm_num [Nat.factorial]
    rw [hf] at h
    have h2 : (3628800 : ℝ) / (1 / 8) ^ 10 * Y ^ 4 / Y ^ 10 = 3628800 * 8 ^ 10 / Y ^ 6 := by
      field_simp; try ring
    rw [h2] at h
    have h3 : (3628800 : ℝ) * 8 ^ 10 / Y ^ 6 ≤ 3628800 * 8 ^ 10 / (6.4 * 10 ^ 40) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hY6'
    have : 8 / 7 * (Y ^ 4 / exp (1 / 8 * Y)) ≤ 8 / 7 * (3628800 * 8 ^ 10 / (6.4 * 10 ^ 40)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    norm_num at this ⊢; linarith
  -- terms 3 and 4: Y^14 / exp(c Y) with n = 20
  have hY6 : (6.4 * 10 ^ 40 : ℝ) ≤ Y ^ 6 := by
    have : (6.34 * 10 ^ 6 : ℝ) ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ (by norm_num) hY 6
    norm_num at this ⊢; linarith
  have hf20 : (Nat.factorial 20 : ℝ) = 2432902008176640000 := by norm_num [Nat.factorial]
  have t3 : Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) ≤ 1 / 10 ^ 16 := by
    have h := pow_div_exp_le Y (1 / 2) 14 20 hY0 (by norm_num)
    rw [hf20] at h
    have e : Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) = 1.02 * (Y ^ 14 / exp (1 / 2 * Y)) := by
      rw [show Y / 2 = 1 / 2 * Y by ring]; ring
    rw [e]
    have h2 : (2432902008176640000 : ℝ) / (1 / 2) ^ 20 * Y ^ 14 / Y ^ 20 =
        2432902008176640000 * 2 ^ 20 / Y ^ 6 := by field_simp; try ring
    rw [h2] at h
    have h3 : (2432902008176640000 : ℝ) * 2 ^ 20 / Y ^ 6 ≤ 2432902008176640000 * 2 ^ 20 / (6.4 * 10 ^ 40) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hY6
    have : 1.02 * (Y ^ 14 / exp (1 / 2 * Y)) ≤ 1.02 * (2432902008176640000 * 2 ^ 20 / (6.4 * 10 ^ 40)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    norm_num at this ⊢; linarith
  have t4 : Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) ≤ 1 / 10 ^ 16 := by
    have h := pow_div_exp_le Y (2 / 3) 14 20 hY0 (by norm_num)
    rw [hf20] at h
    have e : Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) = 3 * (Y ^ 14 / exp (2 / 3 * Y)) := by
      rw [show 2 * Y / 3 = 2 / 3 * Y by ring]; ring
    rw [e]
    have h2 : (2432902008176640000 : ℝ) / (2 / 3) ^ 20 * Y ^ 14 / Y ^ 20 =
        2432902008176640000 * (3 / 2) ^ 20 / Y ^ 6 := by field_simp; try ring
    rw [h2] at h
    have h3 : (2432902008176640000 : ℝ) * (3 / 2) ^ 20 / Y ^ 6 ≤
        2432902008176640000 * (3 / 2) ^ 20 / (6.4 * 10 ^ 40) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hY6
    have : 3 * (Y ^ 14 / exp (2 / 3 * Y)) ≤ 3 * (2432902008176640000 * (3 / 2) ^ 20 / (6.4 * 10 ^ 40)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    norm_num at this ⊢; linarith
  have e : Y ^ 4 * (exp (-(Y / 8)) / (7 / 8) + 1.02 * Y ^ 10 / exp (Y / 2) + 3 * Y ^ 10 / exp (2 * Y / 3)) =
      Y ^ 4 * (exp (-(Y / 8)) / (7 / 8)) + Y ^ 4 * (1.02 * Y ^ 10 / exp (Y / 2)) +
        Y ^ 4 * (3 * Y ^ 10 / exp (2 * Y / 3)) := by ring
  rw [e]
  norm_num at t1 t2 t3 t4 ⊢
  linarith

/-- `v'₀ = sup_{y ≥ x₂(X₃)} φ78 ≤ vS := 10⁻¹⁵`. -/
abbrev vS : ℝ := 1 / 10 ^ 15

theorem phi78_le_vS (Y : ℝ) (hY : ℓ ≤ Y) : φ78 Y ≤ vS := phi78_le Y (le_trans ℓ_ge' hY)

/-- **`m(X₃) ≤ 1.839·10⁻⁵`** with `v'₀ ≤ 10⁻¹⁵`. The main part is `39·3/log X₃ ≤ 1.4268·10⁻⁵`. -/
theorem m_le1775 (v : ℝ) (hv0 : 0 ≤ v) (hv : v ≤ vS) : 0 ≤ mX3 v ∧ mX3 v ≤ 1.839 / 10 ^ 5 := by
  have hΛ := Λ3_ge
  have hΛ0 : 0 < Λ3 := by linarith
  have hℓ := ℓ_ge'
  have hℓΛ := ℓ_ge
  have hℓ0 : 0 < ℓ := by linarith
  have hlogΛ : 1 ≤ log Λ3 := by
    rw [le_log_iff_exp_le hΛ0]
    have := exp_one_lt_d9; linarith
  -- v₀
  have hA : 1 / (Λ3 ^ 10 * ℓ ^ 5) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 1 ≤ Λ3 ^ 10 := one_le_pow₀ (by linarith)
    have : 1 ≤ ℓ ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hB : 1 / ((1 - 6 / ℓ) * Λ3) ≤ 1 := by
    have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith
    rw [div_le_one (by apply mul_pos (by linarith) hΛ0)]
    nlinarith
  have hv0' : v0 v ≤ 3 * vS + 3 / Λ3 := by
    unfold v0
    have hp : 0 ≤ 1 / (Λ3 ^ 10 * ℓ ^ 5) := by positivity
    have hq : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) := by
      have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith
      apply div_nonneg one_pos.le; apply mul_nonneg (by linarith) hΛ0.le
    have : v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) ≤ vS * 3 :=
      mul_le_mul hv (by linarith) (by linarith) (by norm_num)
    linarith
  have hv00 : 0 ≤ v0 v := by
    unfold v0
    have hp : 0 ≤ 1 / (Λ3 ^ 10 * ℓ ^ 5) := by positivity
    have hq : 0 ≤ 1 / ((1 - 6 / ℓ) * Λ3) := by
      have h6 : 6 / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ0]; linarith
      apply div_nonneg one_pos.le; apply mul_nonneg (by linarith) hΛ0.le
    have : 0 ≤ v * (1 + 1 / (Λ3 ^ 10 * ℓ ^ 5) + 1 / ((1 - 6 / ℓ) * Λ3)) := by positivity
    have : 0 ≤ 3 / Λ3 := by positivity
    linarith
  have h3 : 3 / Λ3 ≤ 3 / (6.3625 * 10 ^ 6) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ
  -- the tiny terms
  have hf24 : (Nat.factorial 24 : ℝ) = 620448401733239439360000 := by norm_num [Nat.factorial]
  have hΛ8 : (2 * 10 ^ 54 : ℝ) ≤ Λ3 ^ 8 := by
    have : (6.3625 * 10 ^ 6 : ℝ) ^ 8 ≤ Λ3 ^ 8 := pow_le_pow_left₀ (by norm_num) hΛ 8
    norm_num at this ⊢; linarith
  have k1 : 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) ≤ 1 / 10 ^ 20 := by
    have h := pow_div_exp_le Λ3 1 16 24 hΛ0 (by norm_num)
    rw [hf24, one_mul] at h
    have h2 : (620448401733239439360000 : ℝ) / 1 ^ 24 * Λ3 ^ 16 / Λ3 ^ 24 =
        620448401733239439360000 / Λ3 ^ 8 := by field_simp; try ring
    rw [h2] at h
    have h3 : (620448401733239439360000 : ℝ) / Λ3 ^ 8 ≤ 620448401733239439360000 / (2 * 10 ^ 54) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ8
    have hE : 0 < exp Λ3 := exp_pos _
    have : 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) ≤ 108 * (Λ3 ^ 16 / exp Λ3) := by
      rw [div_le_iff₀ (by positivity)]
      have : 108 * (Λ3 ^ 16 / exp Λ3) * (exp Λ3 * log Λ3) = 108 * Λ3 ^ 16 * log Λ3 := by
        field_simp
      rw [this]
      have : 0 ≤ 108 * Λ3 ^ 16 := by positivity
      nlinarith
    have : 108 * (Λ3 ^ 16 / exp Λ3) ≤ 108 * (620448401733239439360000 / (2 * 10 ^ 54)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    norm_num at this ⊢; linarith
  have k2 : 26 * Λ3 ^ 5 / ℓ ^ 10 ≤ 1 / 10 ^ 20 := by
    have hl10 : (0.998 * Λ3) ^ 10 ≤ ℓ ^ 10 := pow_le_pow_left₀ (by positivity) hℓΛ 10
    have hΛ5 : (1.04 * 10 ^ 34 : ℝ) ≤ Λ3 ^ 5 := by
      have : (6.3625 * 10 ^ 6 : ℝ) ^ 5 ≤ Λ3 ^ 5 := pow_le_pow_left₀ (by norm_num) hΛ 5
      norm_num at this ⊢; linarith
    rw [div_le_iff₀ (by positivity)]
    have e : (0.998 * Λ3) ^ 10 = 0.998 ^ 10 * (Λ3 ^ 5 * Λ3 ^ 5) := by ring
    rw [e] at hl10
    have : 26 * Λ3 ^ 5 ≤ 1 / 10 ^ 20 * (0.998 ^ 10 * (Λ3 ^ 5 * Λ3 ^ 5)) := by
      have h5 : (0 : ℝ) ≤ Λ3 ^ 5 := by positivity
      norm_num
      nlinarith
    linarith
  have hf10 : (Nat.factorial 10 : ℝ) = 3628800 := by norm_num [Nat.factorial]
  have k3 : 88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) ≤ 1 / 10 ^ 20 := by
    have hle : exp (-(8 / 3 * Λ3)) ≤ exp (-(Λ3 / 2)) := exp_le_exp.mpr (by linarith)
    have h := pow_div_exp_le Λ3 (1 / 2) 5 10 hΛ0 (by norm_num)
    rw [hf10] at h
    have h2 : (3628800 : ℝ) / (1 / 2) ^ 10 * Λ3 ^ 5 / Λ3 ^ 10 = 3628800 * 2 ^ 10 / Λ3 ^ 5 := by
      field_simp; try ring
    rw [h2] at h
    have hΛ5 : (1.04 * 10 ^ 34 : ℝ) ≤ Λ3 ^ 5 := by
      have : (6.3625 * 10 ^ 6 : ℝ) ^ 5 ≤ Λ3 ^ 5 := pow_le_pow_left₀ (by norm_num) hΛ 5
      norm_num at this ⊢; linarith
    have h3 : (3628800 : ℝ) * 2 ^ 10 / Λ3 ^ 5 ≤ 3628800 * 2 ^ 10 / (1.04 * 10 ^ 34) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hΛ5
    have e : 88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) ≤ 176 * (Λ3 ^ 5 / exp (1 / 2 * Λ3)) := by
      have : exp (-(Λ3 / 2)) = (exp (1 / 2 * Λ3))⁻¹ := by
        rw [← exp_neg]; ring_nf
      have h5 : (0 : ℝ) ≤ Λ3 ^ 5 := by positivity
      have hx : Λ3 ^ 5 / exp (1 / 2 * Λ3) = Λ3 ^ 5 * exp (-(Λ3 / 2)) := by
        rw [this, div_eq_mul_inv]
      rw [hx]
      have h8 : 0 ≤ exp (-(8 / 3 * Λ3)) := (exp_pos _).le
      nlinarith
    have : 176 * (Λ3 ^ 5 / exp (1 / 2 * Λ3)) ≤ 176 * (3628800 * 2 ^ 10 / (1.04 * 10 ^ 34)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    norm_num at this ⊢; linarith
  have k4 : 106 / Λ3 ^ 6 ≤ 1 / 10 ^ 20 := by
    have hΛ6 : (6.6 * 10 ^ 40 : ℝ) ≤ Λ3 ^ 6 := by
      have : (6.3625 * 10 ^ 6 : ℝ) ^ 6 ≤ Λ3 ^ 6 := pow_le_pow_left₀ (by norm_num) hΛ 6
      norm_num at this ⊢; linarith
    rw [div_le_iff₀ (by positivity)]; norm_num; nlinarith
  have k0 : 0 ≤ 108 * Λ3 ^ 16 / (exp Λ3 * log Λ3) + 26 * Λ3 ^ 5 / ℓ ^ 10 +
      88 * Λ3 ^ 5 * (exp (-(8 / 3 * Λ3)) + exp (-(Λ3 / 2))) + 106 / Λ3 ^ 6 := by
    have : 0 < log Λ3 := by linarith
    positivity
  unfold mX3
  constructor
  · linarith
  · norm_num at hv0' h3 k1 k2 k3 k4 ⊢; linarith

/-! ### The hypotheses of Theorems 44, 50, 51 at these parameters -/

/-- `log x ≤ x/10⁸ + 17.44`, from `log 10⁸ ≤ 18.44`. -/
lemma log_le_lin8 (x : ℝ) (hx : 0 < x) : log x ≤ x / 100000000 + 17.44 := by
  have h1 := log_le_sub_one_of_pos (x := x / 100000000) (by positivity)
  rw [log_div hx.ne' (by norm_num)] at h1
  have h2 : log (100000000 : ℝ) ≤ 18.44 := by
    rw [log_le_iff_le_exp (by norm_num)]
    have h18 : exp (18.44 : ℝ) = exp 1 ^ 18 * exp 0.44 := by
      rw [← exp_nat_mul, ← exp_add]; congr 1; norm_num
    have he := exp_one_gt_d9
    have ha : (2.7182818283 : ℝ) ^ 18 ≤ exp 1 ^ 18 := pow_le_pow_left₀ (by norm_num) he.le 18
    have hq := quadratic_le_exp_of_nonneg (x := (0.44 : ℝ)) (by norm_num)
    have hb : (100000000 : ℝ) ≤ 2.7182818283 ^ 18 * (1 + 0.44 + 0.44 ^ 2 / 2) := by norm_num
    rw [h18]
    calc (100000000 : ℝ) ≤ 2.7182818283 ^ 18 * (1 + 0.44 + 0.44 ^ 2 / 2) := hb
      _ ≤ exp 1 ^ 18 * exp 0.44 := mul_le_mul ha hq (by norm_num) (by positivity)
  linarith

/-- Theorems 44 and 50, the u₀ condition in logs, `u₀ = 5·10⁴`, `α = 987/10⁶`, for every
`log N = L ≥ 6.5·10⁷` and `1 ≤ lx₁ ≤ L`: `α L − 10 log lx₁ − 2.5 log L ≥ u₀(1 + 9·10⁻⁷/log u₀)`. -/
theorem u0cond_44_50 (L lx1 : ℝ) (hL : 5.09 * 10 ^ 7 ≤ L) (hx1 : 1 ≤ lx1) (hx1L : lx1 ≤ L) :
    50000 * (1 + 9e-7 / log 50000) ≤ α * L - 10 * log lx1 - 2.5 * log L := by
  have hL0 : 0 < L := by linarith
  have h1 : log lx1 ≤ log L := log_le_log (by linarith) hx1L
  have h2 := log_le_lin8 L hL0
  have h5 : (1 : ℝ) ≤ log 50000 := by
    rw [le_log_iff_exp_le (by norm_num)]; have := exp_one_lt_d9; linarith
  have h6 : 9e-7 / log (50000 : ℝ) ≤ 9e-7 := div_le_self (by norm_num) h5
  have hm : (50000 : ℝ) * (1 + 9e-7 / log 50000) ≤ 50000 * (1 + 9e-7) := by gcongr
  norm_num at hm h6 ⊢
  nlinarith

/-- Theorem 51's condition in logs: `log 310 + α L − 10 log L ≥ u₀(1 + 9·10⁻⁷/log u₀)`. -/
theorem u0cond_51 (L : ℝ) (hL : 5.09 * 10 ^ 7 ≤ L) :
    50000 * (1 + 9e-7 / log 50000) ≤ log 310 + α * L - 10 * log L := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin8 L hL0
  have h3 : 0 ≤ log (310 : ℝ) := log_nonneg (by norm_num)
  have h5 : (1 : ℝ) ≤ log 50000 := by
    rw [le_log_iff_exp_le (by norm_num)]; have := exp_one_lt_d9; linarith
  have h6 : 9e-7 / log (50000 : ℝ) ≤ 9e-7 := div_le_self (by norm_num) h5
  have hm : (50000 : ℝ) * (1 + 9e-7 / log 50000) ≤ 50000 * (1 + 9e-7) := by gcongr
  norm_num at hm h6 ⊢
  nlinarith

/-- The other ranges at `L = log N ≥ 6.5·10⁷`: (140) `8α + 160 log L/L < 1`, `α < 1/24`,
`α < 1/6`, the D ≥ z² condition `(1/2 − α)L − 20 log L ≥ L/4`, Lemma 18's `log z = L/8 > 4000`,
and `ε ≤ 1/74`. -/
theorem ranges1775 (L : ℝ) (hL : 5.09 * 10 ^ 7 ≤ L) :
    8 * α + 160 * log L / L < 1 ∧ α < 1 / 24 ∧ α < 1 / 6 ∧
      L / 4 ≤ (1 / 2 - α) * L - 20 * log L ∧ 4000 < L / 8 ∧ ε ≤ 1 / 74 := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin L hL0
  refine ⟨?_, by norm_num, by norm_num, by nlinarith, by linarith, by norm_num⟩
  rw [show 8 * α + 160 * log L / L = 8 * α + 160 * (log L / L) by ring]
  have : log L / L ≤ 1 / 10 ^ 4 + 10 / L := by
    rw [div_le_iff₀ hL0]
    have : (1 / 10 ^ 4 + 10 / L) * L = L / 10 ^ 4 + 10 := by field_simp
    linarith
  have : 10 / L ≤ 1 / 10 ^ 5 := small_div 10 L (by norm_num) (by norm_num) hL
  norm_num at * ; nlinarith

/-- log log x₁(X₂) ≥ 10.4 and log log x₂(X₃) ≥ 10.4, the range of Lemmas 29, 30 and Theorems 44,
50, 51: `log x₁(X₂) = e^{17.75} − 90` and `log x₂(X₃) = ℓ`, both above `e^{10.4}`. -/
theorem loglog_ranges : 10.4 ≤ log (exp 17.75 - 5 * 17.75) ∧ 10.4 ≤ log ℓ := by
  have h104 : exp (10.4 : ℝ) ≤ 10 ^ 6 := by
    have h1 : exp (10.4 : ℝ) ≤ exp 11 := exp_le_exp.mpr (by norm_num)
    have h11 : exp (11 : ℝ) = exp 1 ^ 11 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_lt_d9
    have : exp (1 : ℝ) ^ 11 ≤ 2.7182818286 ^ 11 := pow_le_pow_left₀ (exp_pos 1).le he.le 11
    have : (2.7182818286 : ℝ) ^ 11 ≤ 10 ^ 6 := by norm_num
    rw [h11] at h1; linarith
  have := expT_ge
  have := ℓ_ge'
  constructor
  · rw [le_log_iff_exp_le (by linarith)]; linarith
  · rw [le_log_iff_exp_le (by linarith)]; linarith

/-- (140)'s `K_δ(x₁(X₂)) ≥ 3022` at `δ = 1`: `log x₁(X₂) = e^{17.75} − 90 ≥ 3022`. Case (a) uses δ only here,
since `k₁ = 0 < K_δ` for every δ. -/
theorem kdelta_range : (3022 : ℝ) ≤ exp 17.75 - 5 * 17.75 := by have := expT_ge; linarith

/-- `twinC ≥ 0.654`: TwinCNumeric.lean's proof of `twinC_ge_065` with its last step sharpened,
0.6613·(1 − 1.01/98) = 0.65448. -/
theorem twinC_ge_0654 : (0.654 : ℝ) ≤ twinC := by
  rw [twinC_eq_exp, ← summable_aT.sum_add_tsum_nat_add 100, Real.exp_add, exp_head]
  have htail : -(101 / 100) * (1 / 98 : ℝ) ≤ ∑' n, aT (n + 100) := by
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 99) ^ 2) := by
      have := (summable_nat_add_iff 100).mpr summable_inv_sub_one_sq
      refine this.congr fun n => ?_
      push_cast; ring_nf
    have h1 : ∑' n : ℕ, -(101 / 100) * (1 / ((n : ℝ) + 99) ^ 2) ≤ ∑' n, aT (n + 100) :=
      Summable.tsum_le_tsum aT_tail_ge (hs.mul_left _)
        ((summable_nat_add_iff 100).mpr summable_aT)
    rw [tsum_mul_left] at h1
    have h2 := tsum_tail_sq_le
    nlinarith
  have he : 1 + (-(101 / 100) * (1 / 98 : ℝ)) ≤ Real.exp (∑' n, aT (n + 100)) := by
    have := Real.add_one_le_exp (∑' n, aT (n + 100))
    linarith
  have hP := head_prod_ge
  have hP0 : (0 : ℝ) ≤ 6613 / 10000 := by norm_num
  calc (0.654 : ℝ) ≤ 6613 / 10000 * (1 + (-(101 / 100) * (1 / 98 : ℝ))) := by norm_num
    _ ≤ _ := mul_le_mul hP he (by norm_num) (hP0.trans hP)

/-! ### Assembly at t = 17.75 -/

/-- Chen's theorem above exp(exp t). -/
def ChenPosAt (t : ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → 0 < chenCount N

lemma big_exp1775 (L : ℝ) (hL : 5.09 * 10 ^ 7 ≤ L) : 3 * 10 ^ 15 * L ^ 2 ≤ exp (L / 8) := by
  have hL0 : 0 ≤ L := by linarith
  have h := Real.pow_div_factorial_le_exp (L / 8) (by positivity) 6
  have hf : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hL4 : (6.7 * 10 ^ 30 : ℝ) ≤ L ^ 4 := by
    have : (5.09 * 10 ^ 7 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
    norm_num at this ⊢; linarith
  have e : (L / 8) ^ 6 / 720 = L ^ 2 * L ^ 4 / (8 ^ 6 * 720) := by ring
  rw [e] at h
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have : 3 * 10 ^ 15 * L ^ 2 ≤ L ^ 2 * L ^ 4 / (8 ^ 6 * 720) := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hL4 hL2]
  linarith

/-- The margin with constant κ, as ChenPos.lean's MarginKAt. -/
def MarginKAt (t κ : ℝ) (cA cQ cB : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, Even N → exp (exp t) < N → κ + 1 / 10 ^ 12 ≤ cA N - cQ N / 2 - cB N / 2

/-- ChenPos.lean's `chenCount_gt_of_sieveBounds` with the threshold `t ≥ 17.75`, proof copied with
`big_exp` replaced by `big_exp1775`. -/
theorem chenCount_gt1775 (t : ℝ) (ht : 17.75 ≤ t) (κ : ℝ) (cA cQ cB : ℕ → ℝ)
    (hA : Thm44At t cA) (hQ : Thm50At t cQ) (hB : Thm51At t cB) (hm : MarginKAt t κ cA cQ cB) :
    ∀ N : ℕ, Even N → exp (exp t) < N → κ * mainTerm N < chenCount N := by
  intro N hEven hNt
  have hN : exp (exp 17.75) < (N : ℝ) :=
    lt_of_le_of_lt (exp_le_exp.mpr (exp_le_exp.mpr ht)) hNt
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  set L := Real.log N with hLdef
  have hL : exp 17.75 < L := (Real.lt_log_iff_exp_lt hpos).mpr hN
  have hL6 := expT_ge
  have hL0 : 0 < L := by linarith
  have hNe : (N : ℝ) = exp L := (exp_log hpos).symm
  have hz : zN N = exp (L / 8) := by
    simp only [zN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hy : yN N = exp (L / 3) := by
    simp only [yN]; rw [rpow_def_of_pos hpos, ← hLdef]; ring_nf
  have hz2 : 2 ≤ zN N := by
    rw [hz]; have := add_one_le_exp (L / 8); linarith
  have hy0 : 0 < yN N := by rw [hy]; exact exp_pos _
  have hy3 : (N : ℝ) ≤ yN N ^ 3 := by
    rw [hy, ← exp_nat_mul, hNe]; apply exp_le_exp.mpr; push_cast; linarith
  have hchen := chen_inequality N (zN N) (yN N) hz2 hy0 hy3
  have h1 := hA N hEven hNt
  have h2 := hQ N hEven hNt
  have h3 := hB N hEven hNt
  have hmN := hm N hEven hNt
  have hU := U_ge N
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 < mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  have hE : 2 * (N : ℝ) / zN N + yN N ≤ 1 / 10 ^ 12 * mainTerm N := by
    have hbig := big_exp1775 L (by linarith)
    have e1 : 2 * (N : ℝ) / zN N = 2 * exp (7 * L / 8) := by
      rw [hz, hNe, mul_div_assoc, ← exp_sub]; ring_nf
    have e2 : yN N ≤ exp (7 * L / 8) := by rw [hy]; exact exp_le_exp.mpr (by linarith)
    have e3 : exp L = exp (7 * L / 8) * exp (L / 8) := by rw [← exp_add]; ring_nf
    have hM : 1 / 1000 * exp L / L ^ 2 ≤ mainTerm N := by
      simp only [mainTerm]; rw [← hLdef, ← hNe]
      apply div_le_div_of_nonneg_right _ hL2.le
      rw [hNe]; exact mul_le_mul_of_nonneg_right hU (exp_pos _).le
    have h7 := exp_pos (7 * L / 8)
    have : 3 * exp (7 * L / 8) ≤ 1 / 10 ^ 12 * (1 / 1000 * exp L / L ^ 2) := by
      rw [e3, show 1 / 10 ^ 12 * (1 / 1000 * (exp (7 * L / 8) * exp (L / 8)) / L ^ 2) =
        exp (7 * L / 8) * exp (L / 8) / (10 ^ 15 * L ^ 2) by ring, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hbig h7.le]
    linarith
  have hfin := mul_le_mul_of_nonneg_right hmN hM0.le
  nlinarith

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant

/-- Theorem 44 (a) constant at these parameters, `c₄ = c₄(X₂)`. -/
def cA1775 (c4 : ℝ) (N : ℕ) : ℝ := cAa gE twinC c4 (Real.log N)
/-- Theorem 50 (a) constant. -/
def cQ1775 (l1 l : ℝ) (N : ℕ) : ℝ := cQa gE twinC l1 l (Real.log N) (exp 17.75)
/-- Theorem 51 constant, `ε₂ = 0`, `m = m(X₃)` with the 7/8 Siegel term. -/
def cB1775 (N : ℕ) : ℝ := cB gE twinC 0 BJS.cbar (mX3 vS) (Real.log N)

theorem margin1775 (c4 l1 l : ℝ) (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 12)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 12) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 12) :
    MarginKAt 17.75 (4 / 10 ^ 4) (cA1775 c4) (cQ1775 l1 l) cB1775 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : exp 17.75 ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  have hT : (0.654 : ℝ) ≤ twinC := twinC_ge_0654
  have hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
    have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
    constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  have hm := m_le1775 vS (by norm_num) le_rfl
  have hLX : (5.09 * 10 ^ 7 : ℝ) ≤ exp 17.75 := by have := expT_ge; linarith
  unfold cA1775 cQ1775 cB1775
  exact margin_a1775 gE twinC BJS.cbar (mX3 vS) c4 l1 l (Real.log N) (exp 17.75) g_ge g_le hT hcb hm
    hc4 hl1 hls hLX hL

/-- **Chen's theorem above exp(exp 17.75) under the 7/8 setting**, CONDITIONAL ON BJS Theorems
44 (a), 50 (a), 51 with u₀ = 5·10⁴, α = 987/10⁶, ε = 6.1·10⁻⁵, ε₂ = 0, as the cited bounds hA hQ hB,
and on c₄(X₂), l₁(X₂), l(X₂) ≤ 10⁻¹²; the VERIFY subagent puts the paper's c₄ and l near 5·10⁻¹⁶ and 3·10⁻¹⁶ here, from the 2.2/log² X₂ term of p(X₂). Every numeric step between them and the conclusion is PROVED. -/
theorem chenPos1775_of_sieveBounds (c4 l1 l : ℝ) (hc4 : 0 ≤ c4 ∧ c4 ≤ 1 / 10 ^ 12)
    (hl1 : 0 ≤ l1 ∧ l1 ≤ 1 / 10 ^ 12) (hls : 0 ≤ l ∧ l ≤ 1 / 10 ^ 12)
    (hA : Thm44At 17.75 (cA1775 c4)) (hQ : Thm50At 17.75 (cQ1775 l1 l)) (hB : Thm51At 17.75 cB1775) :
    ChenPosAt 17.75 := by
  intro N hEven hNt
  have h := chenCount_gt1775 17.75 le_rfl (4 / 10 ^ 4) _ _ _ hA hQ hB (margin1775 c4 l1 l hc4 hl1 hls)
    N hEven hNt
  have hM0 : 0 ≤ mainTerm N := by
    have := U_pos N
    simp only [mainTerm]; positivity
  have : (0 : ℝ) < chenCount N := lt_of_le_of_lt (mul_nonneg (by norm_num) hM0) h
  exact_mod_cast this

/-! ### Vacuity -/

/-- `margin_a1775`'s hypotheses hold together: `g = e^γ`, `T = 0.66`, `c̄ = 0.363`, `m = 10⁻⁵`,
`c₄ = l₁ = l = 0`, `L = LX = e^{17.75}`. -/
example : (1.781 : ℝ) ≤ gE ∧ gE ≤ 1.7812 ∧ (0.65 : ℝ) ≤ 0.66 ∧ (5.09 * 10 ^ 7 : ℝ) ≤ exp 17.75 :=
  ⟨g_ge, g_le, by norm_num, by have := expT_ge; linarith⟩

end LeanLab.ChenExplicit.H781775

#print axioms LeanLab.ChenExplicit.H781775.margin_a1775
#print axioms LeanLab.ChenExplicit.H781775.m_le1775
#print axioms LeanLab.ChenExplicit.H781775.phi78_le
#print axioms LeanLab.ChenExplicit.H781775.u0cond_44_50
#print axioms LeanLab.ChenExplicit.H781775.u0cond_51
#print axioms LeanLab.ChenExplicit.H781775.ranges1775
#print axioms LeanLab.ChenExplicit.H781775.loglog_ranges
#print axioms LeanLab.ChenExplicit.H781775.kdelta_range
#print axioms LeanLab.ChenExplicit.H781775.margin1775
#print axioms LeanLab.ChenExplicit.H781775.chenCount_gt1775
#print axioms LeanLab.ChenExplicit.H781775.chenPos1775_of_sieveBounds
#print axioms LeanLab.ChenExplicit.H781775.twinC_ge_0654
#print axioms LeanLab.ChenExplicit.H781775.log_le_lin8
#print axioms LeanLab.ChenExplicit.H781775.expT_ge
