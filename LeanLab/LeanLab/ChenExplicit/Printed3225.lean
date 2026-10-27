/-
AI-written Lean code, Claude, 2026-10-20, PC run 20261020T2203Z-17931, unit U-1298, track T2.
P0009 BJS 2022, arXiv 2207.09452 v6, copies/P0009.txt: chen_3225 at log log X₂ = 32.25 from the
PRINTED ε of Theorems 44, 50, 51.

AssemblyT3225.chen_3225 of cloud U-6713 takes Thm44At, Thm50At, Thm51At at t = 32.25 with the
constants of Section9U8.lean, which carry ε = εU = 1.91·10⁻⁷, the value of Lemma 18 at u₀ = 10⁸.
BJS state Theorems 44, 50, 51 only at u₀ = 10⁹ with ε = 1.452·10⁻⁷, p. 42, p. 51, p. 56, and
C₁(ε) = 106, C₂(ε) = 107 printed in Theorem 44 on p. 42. This file shows the printed-ε forms imply
the εU forms, so chen_3225 follows from Theorems 44, 50, 51 at their printed u₀ and ε.

* `l2E`, `l1E`, `cAaE`, `cAbPE`, `cQaE`, `cQbE`, `cBPE`: the corrected Section 9 constants with ε as
  an argument e. `*_eqU` and `*_eqP`: at e = εU they are the Section9U8 and BJSl3225 constants, at
  e = Section9.ε = 1.452·10⁻⁷ they are the Section9 and F0023 constants, all by rfl.
* Monotonicity in e, PROVED: `cAaE_anti`, `cAbPE_anti`, Theorem 44's constants decrease in e;
  `l2E_mono`, `l1E_mono`, `cQaE_mono`, `cQbE_mono`, `cBPE_mono`, Theorems 50 and 51's increase.
  So a smaller ε gives a larger lower bound and smaller upper bounds, a stronger statement.
* `cA_le_P`, `cQP_le`, `cBP_le` and `thm44_of_P`, `thm50_of_P`, `thm51_of_P`: pointwise for
  N > exp exp 32.25, then for the cited statements.
* `u0cond_44_50_1e9`, `u0cond_51_1e9`, `ranges_1e9`: the range conditions of Theorems 44, 50, 51 at
  the printed u₀ = 10⁹, α = 10⁻⁵, every log N ≥ 1.01·10¹⁴, PROVED.
* `margin_3225_printed`: the Section 9 margin also holds with the printed constants, PROVED.
* `chen_3225_printed`: CONDITIONAL ON Thm44At, Thm50At, Thm51At at t = 32.25 with ε = 1.452·10⁻⁷,
  u₀ = 10⁹, α = 10⁻⁵, C₁ = 106, C₂ = 107, corrected per F-0020 to F-0022, δ₁ = 1.4985 for 44 and 50,
  δ₂ = 1.4665 and ε₀ = 2·10⁻⁵ for 51. No Lemma 17 input: Lemma 18 at u₀ = 10⁹ is printed, p. 18.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT3225

open Real

noncomputable section
namespace LeanLab.ChenExplicit.Printed3225

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.Section9U8 LeanLab.ChenExplicit.At3225 LeanLab.ChenExplicit.AT3225

/-- The printed ε is below the εU of Section9U8. -/
lemma eps_le : Section9.ε ≤ εU := by norm_num

/-- h of (7) is nonnegative everywhere. -/
lemma h_nonneg_all (s : ℝ) : 0 ≤ Section9.h s := by
  unfold Section9.h
  split_ifs with h1 h2
  · exact (exp_pos _).le
  · exact (exp_pos _).le
  · have : 0 < s := by linarith
    positivity

lemma ratio_nonneg (LX : ℝ) (hLX : 0 ≤ LX) : 0 ≤ exp (LX / 8) / (exp (LX / 8) - 1) := by
  have := add_one_le_exp (LX / 8)
  exact div_nonneg (exp_pos _).le (by linarith)

/-! ### The constants with ε as an argument -/

def l2E (e g LX : ℝ) : ℝ :=
  exp (LX / 8) / (exp (LX / 8) - 1) *
    (g / 4 * ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) + 512 / (kα * LX ^ 2)) +
      (log (8 / 3) + 64 / LX ^ 2) * e * 106 * exp 2 * h kα)

def l1E (e g C1 ν : ℝ) : ℝ :=
  BJSp3225.LX ^ 2 / exp BJSp3225.LX * (2 * g / Section9.kα + e * C1 * exp 2 * Section9.h Section9.kα) *
    (exp (BJSp3225.LX / 8) / (exp (BJSp3225.LX / 8) - 1) * (log (8 / 3) + 64 / BJSp3225.LX ^ 2) *
      (1.3841 / 32.25) + BJSp3225.p ν * exp BJSp3225.LX / BJSp3225.LX ^ 4)

def cAaE (e g T c4 L : ℝ) : ℝ :=
  8 * (1 - 32.02 / L ^ 2) * (fS g (4 - 8 * α) - 107 * e * exp 2 * h (4 - 8 * α) -
    1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L))

def cAbPE (e ll g T e1 a c4s w L LX : ℝ) : ℝ :=
  8 * (1 + 32.02 / L ^ 2) * (fS g (ccP ll LX) - e1 * (1 - fS g (ccP ll LX)) -
    (1 + e1) * e * 107 * exp 2 * h (ccP ll LX) -
    (3 * e1 + a) * (max (1 - fS g (ccP ll LX)) (FS g (ccP ll LX) - 1) +
      e * 107 * exp 2 * h (ccP ll LX)) -
    a - 64.04 / L ^ 2 - 1 / 8 * (1 + 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4s / L) * w)

def cQaE (e g T l1 l L LX : ℝ) : ℝ :=
  8.0004 * (1 + 32.02 / L ^ 2) * (l1 + l2E e g LX) + l * (g / (2 * T))

def cQbE (e g T e1 l1s ls L LX : ℝ) : ℝ :=
  8.0004 * (1 + 32.02 / L ^ 2) * (1 + e1) * (l1s + l2E e g LX) + ls * (g / (2 * T))

def cBPE (e e0 g T e2 cb m L : ℝ) : ℝ :=
  1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) *
      (2 / (1 / 2 - α) * g + 3 * e * 106 * exp 2 * h (3 / 2 - 3 * α)) * (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)) +
    g / (2 * T) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)))

/-! ### At e = εU and at the printed e = 1.452·10⁻⁷ they are the chain's constants -/

theorem l2_eqU (g LX : ℝ) : l2U g LX = l2E εU g LX := rfl
theorem l2_eqP (g LX : ℝ) : Section9.l2 g LX = l2E Section9.ε g LX := rfl
theorem l1_eqU (g C1 ν : ℝ) : BJSl3225.l1 g C1 ν = l1E εU g C1 ν := rfl
theorem cAa_eqU (g T c4 L : ℝ) : cAaU g T c4 L = cAaE εU g T c4 L := rfl
theorem cAa_eqP (g T c4 L : ℝ) : Section9.cAa g T c4 L = cAaE Section9.ε g T c4 L := rfl
theorem cAbP_eqU (ll g T e1 a c4s w L LX : ℝ) :
    cAbPU ll g T e1 a c4s w L LX = cAbPE εU ll g T e1 a c4s w L LX := rfl
theorem cAbP_eqP (ll g T e1 a c4s w L LX : ℝ) :
    F0023.cAbP ll g T e1 a c4s w L LX = cAbPE Section9.ε ll g T e1 a c4s w L LX := rfl
theorem cQa_eqU (g T l1 l L LX : ℝ) : cQaU g T l1 l L LX = cQaE εU g T l1 l L LX := rfl
theorem cQa_eqP (g T l1 l L LX : ℝ) : Section9.cQa g T l1 l L LX = cQaE Section9.ε g T l1 l L LX := rfl
theorem cQb_eqU (g T e1 l1s ls L LX : ℝ) : cQbU g T e1 l1s ls L LX = cQbE εU g T e1 l1s ls L LX := rfl
theorem cQb_eqP (g T e1 l1s ls L LX : ℝ) :
    Section9.cQb g T e1 l1s ls L LX = cQbE Section9.ε g T e1 l1s ls L LX := rfl
theorem cBP_eqU (e0 g T e2 cb m L : ℝ) : cBPU e0 g T e2 cb m L = cBPE εU e0 g T e2 cb m L := rfl
theorem cBP_eqP (e0 g T e2 cb m L : ℝ) :
    F0023.cBP e0 g T e2 cb m L = cBPE Section9.ε e0 g T e2 cb m L := rfl

/-! ### Monotonicity in ε -/

/-- Theorem 44 (a)'s constant decreases in ε, for log N ≥ 10¹⁴. -/
theorem cAaE_anti {e e' : ℝ} (he : e ≤ e') (g T c4 L : ℝ) (hL : 10 ^ 14 ≤ L) :
    cAaE e' g T c4 L ≤ cAaE e g T c4 L := by
  unfold cAaE
  have s := small_div2 32.02 L (by norm_num) (by norm_num) hL
  have hp : 0 ≤ 8 * (1 - 32.02 / L ^ 2) := by norm_num at s ⊢; linarith
  have h0 : 0 ≤ exp 2 * h (4 - 8 * α) := mul_nonneg (exp_pos _).le (h_nonneg_all _)
  have k : 107 * e * exp 2 * h (4 - 8 * α) ≤ 107 * e' * exp 2 * h (4 - 8 * α) := by
    have := mul_le_mul_of_nonneg_right he h0
    nlinarith
  apply mul_le_mul_of_nonneg_left _ hp
  set H := exp 2 * h (4 - 8 * α)
  set Y := 1 / 8 * (1 - 32.02 / L ^ 2)⁻¹ * (g / (2 * T)) * (c4 / L)
  linarith

/-- Theorem 44 (b)'s constant decreases in ε, for e₁ ≥ 0, a ≥ 0. -/
theorem cAbPE_anti {e e' : ℝ} (he : e ≤ e') (ll g T e1 a c4s w L LX : ℝ)
    (he1 : 0 ≤ e1) (ha : 0 ≤ a) :
    cAbPE e' ll g T e1 a c4s w L LX ≤ cAbPE e ll g T e1 a c4s w L LX := by
  unfold cAbPE
  have hp : 0 ≤ 8 * (1 + 32.02 / L ^ 2) := by positivity
  set H := exp 2 * h (ccP ll LX) with hH
  have h0 : 0 ≤ H := mul_nonneg (exp_pos _).le (h_nonneg_all _)
  have k0 : e * H ≤ e' * H := mul_le_mul_of_nonneg_right he h0
  have k1 : (1 + e1) * e * 107 * exp 2 * h (ccP ll LX) ≤ (1 + e1) * e' * 107 * exp 2 * h (ccP ll LX) := by
    have : (1 + e1) * 107 * (e * H) ≤ (1 + e1) * 107 * (e' * H) :=
      mul_le_mul_of_nonneg_left k0 (by positivity)
    rw [hH] at this; linarith
  have k2 : (3 * e1 + a) * (max (1 - fS g (ccP ll LX)) (FS g (ccP ll LX) - 1) + e * 107 * exp 2 * h (ccP ll LX)) ≤
      (3 * e1 + a) * (max (1 - fS g (ccP ll LX)) (FS g (ccP ll LX) - 1) + e' * 107 * exp 2 * h (ccP ll LX)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hH] at k0; linarith
  apply mul_le_mul_of_nonneg_left _ hp
  linarith

/-- l₂(X₂), (160), increases in ε. -/
theorem l2E_mono {e e' : ℝ} (he : e ≤ e') (g LX : ℝ) (hLX : 0 ≤ LX) : l2E e g LX ≤ l2E e' g LX := by
  unfold l2E
  have hr := ratio_nonneg LX hLX
  have hq : 0 ≤ (log (8 / 3) + 64 / LX ^ 2) * 106 * exp 2 * h kα := by
    have := log83_nonneg; have := h_nonneg_all kα; positivity
  apply mul_le_mul_of_nonneg_left _ hr
  have := mul_le_mul_of_nonneg_right he hq
  nlinarith

/-- l₁(X₂), (158), (159), increases in ε, for 0 ≤ C₁ and ν in Good. -/
theorem l1E_mono {e e' : ℝ} (he : e ≤ e') (g C1 ν : ℝ) (hC : 0 ≤ C1) (hν : BJSp3225.Good ν) :
    l1E e g C1 ν ≤ l1E e' g C1 ν := by
  unfold l1E
  have hX : 0 ≤ BJSp3225.LX := (exp_pos _).le
  have hr := ratio_nonneg _ hX
  have hpν := BJSp3225.p_nonneg hν
  have hD : 0 ≤ exp (BJSp3225.LX / 8) / (exp (BJSp3225.LX / 8) - 1) *
      (log (8 / 3) + 64 / BJSp3225.LX ^ 2) * (1.3841 / 32.25) +
      BJSp3225.p ν * exp BJSp3225.LX / BJSp3225.LX ^ 4 := by
    have := log83_nonneg; positivity
  have hA : 0 ≤ BJSp3225.LX ^ 2 / exp BJSp3225.LX := by positivity
  have hq : 0 ≤ C1 * exp 2 * Section9.h Section9.kα := by
    have := h_nonneg_all Section9.kα; positivity
  have hm : 2 * g / Section9.kα + e * C1 * exp 2 * Section9.h Section9.kα ≤
      2 * g / Section9.kα + e' * C1 * exp 2 * Section9.h Section9.kα := by
    have := mul_le_mul_of_nonneg_right he hq
    have r1 : e * C1 * exp 2 * Section9.h Section9.kα = e * (C1 * exp 2 * Section9.h Section9.kα) := by ring
    have r2 : e' * C1 * exp 2 * Section9.h Section9.kα = e' * (C1 * exp 2 * Section9.h Section9.kα) := by
      ring
    rw [r1, r2]; exact add_le_add le_rfl this
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hA) hD

/-- Theorem 50 (a)'s constant increases in ε and in l₁. -/
theorem cQaE_mono {e e' l1 l1' : ℝ} (he : e ≤ e') (hl : l1 ≤ l1') (g T l L LX : ℝ) (hLX : 0 ≤ LX) :
    cQaE e g T l1 l L LX ≤ cQaE e' g T l1' l L LX := by
  unfold cQaE
  have h2 := l2E_mono he g LX hLX
  have hp : 0 ≤ 8.0004 * (1 + 32.02 / L ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add hl h2) hp
  linarith

/-- Theorem 50 (b)'s constant increases in ε and in l₁*, for e₁ ≥ 0. -/
theorem cQbE_mono {e e' l1 l1' : ℝ} (he : e ≤ e') (hl : l1 ≤ l1') (g T e1 ls L LX : ℝ)
    (he1 : 0 ≤ e1) (hLX : 0 ≤ LX) :
    cQbE e g T e1 l1 ls L LX ≤ cQbE e' g T e1 l1' ls L LX := by
  unfold cQbE
  have h2 := l2E_mono he g LX hLX
  have hp : 0 ≤ 8.0004 * (1 + 32.02 / L ^ 2) * (1 + e1) := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add hl h2) hp
  linarith

/-- Theorem 51's constant increases in ε, for e₂ ≥ 0, c̄ ≥ 0, ε₀ ≥ 0, L > 0. -/
theorem cBPE_mono {e e' : ℝ} (he : e ≤ e') (e0 g T e2 cb m L : ℝ)
    (he0 : 0 ≤ e0) (he2 : 0 ≤ e2) (hcb : 0 ≤ cb) (hL : 0 < L) :
    cBPE e e0 g T e2 cb m L ≤ cBPE e' e0 g T e2 cb m L := by
  unfold cBPE
  have hP1 : 0 ≤ 1.00005 * (1 + e2) * (1 + 4.51 / L ^ 2) := by positivity
  have hP2 : 0 ≤ 1 + e0 + 9 / L := by positivity
  have hlg : 0 ≤ log (1 + e0) := log_nonneg (by linarith)
  have h83 := log83_nonneg
  have hP3 : 0 ≤ cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2) := by
    positivity
  have hq : 0 ≤ 3 * 106 * exp 2 * h (3 / 2 - 3 * α) := by
    have := h_nonneg_all (3 / 2 - 3 * α); positivity
  have hM : 2 / (1 / 2 - α) * g + 3 * e * 106 * exp 2 * h (3 / 2 - 3 * α) ≤
      2 / (1 / 2 - α) * g + 3 * e' * 106 * exp 2 * h (3 / 2 - 3 * α) := by
    have := mul_le_mul_of_nonneg_right he hq; nlinarith
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hP1) hP2) hP3
  linarith

/-! ### The printed-ε constants at X₂ = exp(exp 32.25) -/

/-- l₁ and l₁* at the printed ε. -/
abbrev l1aP : ℝ := l1E Section9.ε gE 106 BJSp3225.nu
abbrev l1SP : ℝ := l1E Section9.ε gE 106 BJSp3225.nuS

open Classical in
/-- Theorem 44's corrected constant at the printed ε = 1.452·10⁻⁷, X₂ = exp(exp 32.25). -/
def cA3225P (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then Section9.cAa gE twinC c4a (Real.log N)
  else F0023.cAbP (3225 / 100) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at the printed ε. -/
def cQ3225P (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then Section9.cQa gE twinC l1aP la (Real.log N) LX
  else Section9.cQb gE twinC e1 l1SP lS (Real.log N) LX

/-- Theorem 51's corrected constant at the printed ε, ε₀ = 2·10⁻⁵. -/
def cB3225P (N : ℕ) : ℝ := F0023.cBP ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma logN_ge {N : ℕ} (hN : exp (exp (3225 / 100)) < (N : ℝ)) : LX ≤ Real.log N := by
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  exact ((Real.lt_log_iff_exp_lt hpos).mpr hN).le

lemma l1a_le : l1aP ≤ l1a :=
  (l1E_mono eps_le gE 106 BJSp3225.nu (by norm_num) BJSp3225.nu_good).trans (le_of_eq (l1_eqU _ _ _).symm)

lemma l1S_le : l1SP ≤ l1S :=
  (l1E_mono eps_le gE 106 BJSp3225.nuS (by norm_num) BJSp3225.nuS_good).trans (le_of_eq (l1_eqU _ _ _).symm)

theorem cA_le_P (caseA : ℕ → Prop) (w : ℕ → ℝ) {N : ℕ} (hN : exp (exp (3225 / 100)) < (N : ℝ)) :
    cA3225 caseA w N ≤ cA3225P caseA w N := by
  have hL := logN_ge hN
  have hL14 : (10 : ℝ) ^ 14 ≤ Real.log N := LX_ge.trans hL
  unfold cA3225 cA3225P
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    rw [cAa_eqU, cAa_eqP]; exact cAaE_anti eps_le _ _ _ _ hL14
  · simp only [hc, ite_false]
    rw [cAbP_eqU, cAbP_eqP]; exact cAbPE_anti eps_le _ _ _ _ _ _ _ _ _ he1.1 ha.1

theorem cQP_le (caseA : ℕ → Prop) {N : ℕ} (_hN : exp (exp (3225 / 100)) < (N : ℝ)) :
    cQ3225P caseA N ≤ cQ3225 caseA N := by
  have hLX : (0 : ℝ) ≤ LX := (exp_pos _).le
  unfold cQ3225 cQ3225P
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    rw [cQa_eqU, cQa_eqP]; exact cQaE_mono eps_le l1a_le _ _ _ _ _ hLX
  · simp only [hc, ite_false]
    rw [cQb_eqU, cQb_eqP]; exact cQbE_mono eps_le l1S_le _ _ _ _ _ _ he1.1 hLX

theorem cBP_le {N : ℕ} (hN : exp (exp (3225 / 100)) < (N : ℝ)) : cB3225P N ≤ cB3225 N := by
  have hL := logN_ge hN
  have hL0 : (0 : ℝ) < Real.log N := lt_of_lt_of_le (exp_pos _) hL
  unfold cB3225 cB3225P
  rw [cBP_eqU, cBP_eqP]
  exact cBPE_mono eps_le _ _ _ _ _ _ _ (by norm_num) he2.1 hcb.1 hL0

lemma mainTerm_nonneg (N : ℕ) : 0 ≤ mainTerm N := by
  have := U_pos N; simp only [mainTerm]; positivity

/-- The printed Theorem 44 implies the εU form chen_3225 takes. -/
theorem thm44_of_P (caseA : ℕ → Prop) (w : ℕ → ℝ) (hA : Thm44At (3225 / 100) (cA3225P caseA w)) :
    Thm44At (3225 / 100) (cA3225 caseA w) := by
  intro N hE hN
  have := hA N hE hN
  have := mul_le_mul_of_nonneg_right (cA_le_P caseA w hN) (mainTerm_nonneg N)
  linarith

/-- The printed Theorem 50 implies the εU form. -/
theorem thm50_of_P (caseA : ℕ → Prop) (hQ : Thm50At (3225 / 100) (cQ3225P caseA)) :
    Thm50At (3225 / 100) (cQ3225 caseA) := by
  intro N hE hN
  have := hQ N hE hN
  have := mul_le_mul_of_nonneg_right (cQP_le caseA (N := N) hN) (mainTerm_nonneg N)
  linarith

/-- The printed Theorem 51 implies the εU form. -/
theorem thm51_of_P (hB : Thm51At (3225 / 100) cB3225P) : Thm51At (3225 / 100) cB3225 := by
  intro N hE hN
  have := hB N hE hN
  have := mul_le_mul_of_nonneg_right (cBP_le hN) (mainTerm_nonneg N)
  linarith

/-- **The Section 9 margin with the printed constants**, PROVED. -/
theorem margin_3225_printed (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (3225 / 100) (cA3225P caseA w) (cQ3225P caseA) cB3225P := by
  intro N hE hN
  have := margin_3225 caseA w hw N hE hN
  have := cA_le_P caseA w hN
  have := cQP_le caseA hN
  have := cBP_le hN
  linarith

/-! ### The range conditions at the printed u₀ = 10⁹ -/

lemma log1e9_ge1 : (1 : ℝ) ≤ log 1000000000 := by
  have he : exp 1 ≤ (1000000000 : ℝ) := by have := exp_one_lt_d9; linarith
  have := Real.log_le_log (exp_pos 1) he
  rwa [Real.log_exp] at this

lemma log1e14_le : log ((10 : ℝ) ^ 14) ≤ 33 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have e : exp (33 : ℝ) = exp 1 ^ 33 := by rw [← exp_nat_mul]; norm_num
  have he := exp_one_gt_d9
  have : (2.7182818283 : ℝ) ^ 33 ≤ exp 1 ^ 33 := pow_le_pow_left₀ (by norm_num) he.le 33
  have : (10 : ℝ) ^ 14 ≤ 2.7182818283 ^ 33 := by norm_num
  rw [e]; linarith

lemma log_le_lin14 (L : ℝ) (hL : 0 < L) : log L ≤ 33 + L / 10 ^ 14 := by
  have hc : (0 : ℝ) < 10 ^ 14 := by positivity
  have h1 : log (L / 10 ^ 14) ≤ L / 10 ^ 14 - 1 := log_le_sub_one_of_pos (div_pos hL hc)
  have h2 : log (L / 10 ^ 14) = log L - log ((10 : ℝ) ^ 14) := log_div hL.ne' hc.ne'
  have h3 := log1e14_le
  rw [h2] at h1
  generalize log ((10 : ℝ) ^ 14) = a at h1 h3
  linarith

lemma rhs_le9 : (1000000000 : ℝ) * (1 + 9e-7 / log 1000000000) ≤ 1000000000 + 900 := by
  have h6 : 9e-7 / log (1000000000 : ℝ) ≤ 9e-7 := div_le_self (by norm_num) log1e9_ge1
  nlinarith

/-- **Theorems 44 and 50, the u₀ condition at the printed u₀ = 10⁹, α = 10⁻⁵**, in logs,
every `L = log N ≥ 1.01·10¹⁴` and `1 ≤ lx₁ ≤ L`, pp. 42, 51. -/
theorem u0cond_44_50_1e9 (L lx1 : ℝ) (hL : 1.01 * 10 ^ 14 ≤ L) (hx1 : 1 ≤ lx1) (hx1L : lx1 ≤ L) :
    1000000000 * (1 + 9e-7 / log 1000000000) ≤ α * L - 10 * log lx1 - 2.5 * log L := by
  have hL0 : 0 < L := by linarith
  have h1 : log lx1 ≤ log L := log_le_log (by linarith) hx1L
  have h2 := log_le_lin14 L hL0
  have hm := rhs_le9
  simp only [α]
  nlinarith

/-- **Theorem 51's condition at u₀ = 10⁹, α₃ = 10⁻⁵**, `log 3¹⁰ + α L − 10 log L ≥ u₀(1 + 9·10⁻⁷/log u₀)`,
p. 56. -/
theorem u0cond_51_1e9 (L : ℝ) (hL : 1.01 * 10 ^ 14 ≤ L) :
    1000000000 * (1 + 9e-7 / log 1000000000) ≤ 10 * log 3 + α * L - 10 * log L := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin14 L hL0
  have h3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
  have hm := rhs_le9
  simp only [α]
  nlinarith

/-- **The other ranges at `L ≥ 1.01·10¹⁴`**, α = 10⁻⁵, printed ε: (140), α < 1/24, α < 1/6,
`N^{1/2−α}/log²⁰ N ≥ z²` in logs, `log z > 4000` of Lemma 18, and `ε ≤ 1/74` of Theorem 6. -/
theorem ranges_1e9 (L : ℝ) (hL : 1.01 * 10 ^ 14 ≤ L) :
    8 * α + 160 * log L / L < 1 ∧ α < 1 / 24 ∧ α < 1 / 6 ∧
      L / 4 ≤ (1 / 2 - α) * L - 20 * log L ∧ 4000 < L / 8 ∧ Section9.ε ≤ 1 / 74 := by
  have hL0 : 0 < L := by linarith
  have h2 := log_le_lin14 L hL0
  refine ⟨?_, by norm_num, by norm_num, ?_, by linarith, by norm_num⟩
  · have hlog : log L ≤ L / 1000 := by nlinarith
    have : 160 * log L / L ≤ 160 / 1000 := by
      rw [div_le_iff₀ hL0]; nlinarith
    simp only [α]; linarith
  · simp only [α]; nlinarith

/-- **Chen at exp(exp 32.25) from the printed ε**, with the u₀ = 10⁹ range conditions.
CONDITIONAL ON Thm44At, Thm50At, Thm51At at t = 32.25 with the printed ε = 1.452·10⁻⁷, u₀ = 10⁹,
corrected per F-0020 to F-0022. -/
theorem chen_3225_printed (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3225 / 100) (cA3225P caseA w)) (hQ : Thm50At (3225 / 100) (cQ3225P caseA))
    (hB : Thm51At (3225 / 100) cB3225P) :
    BJS3At (3225 / 100) ∧
    (∀ N : ℕ, exp (exp (3225 / 100)) < (N : ℝ) →
      (∀ lx1 : ℝ, 1 ≤ lx1 → lx1 ≤ Real.log N →
        1000000000 * (1 + 9e-7 / log 1000000000) ≤
          α * Real.log N - 10 * log lx1 - 2.5 * log (Real.log N)) ∧
      1000000000 * (1 + 9e-7 / log 1000000000) ≤
        10 * log 3 + α * Real.log N - 10 * log (Real.log N)) := by
  refine ⟨chen_3225 caseA w hw (thm44_of_P caseA w hA) (thm50_of_P caseA hQ) (thm51_of_P hB), ?_⟩
  intro N hN
  have h9 : (1.01 : ℝ) * 10 ^ 14 ≤ Real.log N := le_trans BJSm3225.exp3225_ge (logN_ge hN)
  exact ⟨fun lx1 h1 h2 => u0cond_44_50_1e9 _ lx1 h9 h1 h2, u0cond_51_1e9 _ h9⟩

/-- Vacuity of the range lemmas: L = 1.01·10¹⁴ meets their hypothesis. -/
example : (1.01 : ℝ) * 10 ^ 14 ≤ 1.01 * 10 ^ 14 := le_rfl

end LeanLab.ChenExplicit.Printed3225

#print axioms LeanLab.ChenExplicit.Printed3225.cAaE_anti
#print axioms LeanLab.ChenExplicit.Printed3225.cAbPE_anti
#print axioms LeanLab.ChenExplicit.Printed3225.l2E_mono
#print axioms LeanLab.ChenExplicit.Printed3225.l1E_mono
#print axioms LeanLab.ChenExplicit.Printed3225.cQaE_mono
#print axioms LeanLab.ChenExplicit.Printed3225.cQbE_mono
#print axioms LeanLab.ChenExplicit.Printed3225.cBPE_mono
#print axioms LeanLab.ChenExplicit.Printed3225.thm44_of_P
#print axioms LeanLab.ChenExplicit.Printed3225.thm50_of_P
#print axioms LeanLab.ChenExplicit.Printed3225.thm51_of_P
#print axioms LeanLab.ChenExplicit.Printed3225.margin_3225_printed
#print axioms LeanLab.ChenExplicit.Printed3225.u0cond_44_50_1e9
#print axioms LeanLab.ChenExplicit.Printed3225.u0cond_51_1e9
#print axioms LeanLab.ChenExplicit.Printed3225.ranges_1e9
#print axioms LeanLab.ChenExplicit.Printed3225.chen_3225_printed
