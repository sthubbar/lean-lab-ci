/-
AI-written Lean code, Claude, 2026-10-21, PC run 20261021T1103Z-29422, unit U-1406, track T2 FRONTIER.
P0009 BJS 2022, arXiv 2207.09452 v6, copies/P0009.txt. The analogue of PrintedWiring.lean, U-1317,
at X₂ = exp(exp 32.15): a formal Lean step from the printed Theorems 44, 50, 51 and eq (125) of
Lemma 42, WITH their printed hypotheses as premises, to the Thm44At, Thm50At, Thm51At instances that
Printed3215Pos.chenPos_3215_printed of U-1361 takes.

Scope, as in PrintedWiring: the printed theorems quantify over X₂, X₃, δ as well as α, N. The lab has
the X₂-only constants at 32.15 only at δ₁ = 1.5029 and δ₂ = 1.47115, from AssemblyT3215, so the Props
below are the printed theorems AT X₂ = exp(exp 32.15), X₃ = X₂^{1/8} AND these δ, which the printed
universal statements imply. Every printed hypothesis is a premise; every N-level hypothesis is
discharged in Lean at α₁ = α₂ = α₃ = αP = 1.0905·10⁻⁵, ε₀ = 2.15·10⁻⁴.

The same two named gaps as at 32.155: F-0020, Theorem 44 (a) verbatim has 2e^{-γ}, so `PrintedThm44`
carries e^{γ} as the proof (143) gives and `printed44_imp_lit` shows it implies the verbatim form;
and (125), |A| > N / log N, a separate printed lemma, `PrintedLemma42`. Theorems 50, 51 are
transcribed verbatim and in the weaker F-0021, F-0022 forms, verbatim ⇒ weaker PROVED.

Main results:
* `chenPos_3215_of_printedC`: ChenPosAt 32.15 and π₂(N) > 10⁻⁵ U_N N / log² N for every even
  N > exp(exp 32.15), CONDITIONAL ON PrintedThm44, PrintedThm50C, PrintedThm51C, PrintedLemma42.
* `chenPos_3215_of_printed`: the same CONDITIONAL ON the verbatim PrintedThm50 and PrintedThm51.
* The Corollary 4 form at 32.15 is in Cor4At3215.lean, which imports this file.
Vacuity: `shape44`, `shape50`, `shape51`, `hyps_inhabited`.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.PrintedWiring
import LeanLab.ChenExplicit.Printed3215Pos
import LeanLab.ChenExplicit.Statements

open Real Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

noncomputable section
namespace LeanLab.ChenExplicit.PrintedWiring3215

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.Printed3215Pos
open LeanLab.ChenExplicit.PrintedWiring (x1 x2 Kδ cardA wP cAaLit cBLit log_x1 log_x2 lterm_le gT_le
  pbar_ge53 cardA_pos exp45_ge exp31_le u0 u0R)

/-! ### Printed objects at 32.15 -/

/-- log log X₂ = 32.15. -/
abbrev ll : ℝ := 3215 / 100
/-- X₂ = exp(exp 32.15). -/
abbrev X2 : ℝ := exp (exp ll)
/-- X₃ = X₂^{1/8}. -/
abbrev X3 : ℝ := exp (exp ll / 8)
/-- δ for Theorems 44 and 50. -/
abbrev δ1 : ℝ := 1.5029
/-- δ for Theorem 51, which states its own "Let 0 < δ < 2", line 3327. -/
abbrev δ2 : ℝ := 1.47115

/-- Theorem 44, p. 42 and 43, P0009.txt lines 2399 to 2447, at X₂ = exp(exp 32.15), δ = δ₁; the
hypotheses are those quoted in PrintedWiring.Gen44. -/
def Gen44 (cAa cAb : ℝ → ℕ → ℝ) (k1 : ℕ → ℝ) : Prop :=
  10.4 ≤ Real.log (Real.log (x1 X2)) → (0 < δ1 ∧ δ1 < 2) → 3022 ≤ Kδ δ1 (x1 X2) →
  ∀ a1 : ℝ, 0 < a1 → ∀ N : ℕ, X2 ≤ N → Even N →
    u0R ≤ (N : ℝ) ^ a1 / (Real.log (x1 N) ^ 10 * Real.log N ^ (2.5 : ℝ)) →
    zN N ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - a1) / Real.log N ^ 20 →
    8 * a1 + 160 * Real.log (Real.log N) / Real.log N < 1 →
    (k1 N < Kδ δ1 (x1 N) → cAa a1 N * ((cardA N : ℝ) * U N / Real.log N) < SA N (zN N)) ∧
    (Kδ δ1 (x1 N) ≤ k1 N → cAb a1 N * ((cardA N : ℝ) * U N / Real.log N) < SA N (zN N))

/-- Theorem 50, p. 51, lines 2952 to 2991, at X₂ = exp(exp 32.15), δ = δ₁. -/
def Gen50 (cQa cQb : ℝ → ℕ → ℝ) (k1 : ℕ → ℝ) : Prop :=
  10.4 ≤ Real.log (Real.log (x1 X2)) →
  ∀ a2 : ℝ, 0 < a2 → a2 < 1 / 24 → ∀ N : ℕ, X2 ≤ N → Even N →
    u0R ≤ (N : ℝ) ^ a2 / (Real.log (x1 N) ^ 10 * Real.log N ^ (2.5 : ℝ)) →
    (k1 N < Kδ δ1 (x1 N) →
      (sumSAq N (zN N) (yN N) : ℝ) < U N * N / Real.log N ^ 2 * cQa a2 N) ∧
    (Kδ δ1 (x1 N) ≤ k1 N →
      (sumSAq N (zN N) (yN N) : ℝ) < U N * N / Real.log N ^ 2 * cQb a2 N)

/-- Theorem 51, p. 56, lines 3325 to 3355, at X₃ = X₂^{1/8}, δ = δ₂. -/
def Gen51 (cB : ℝ → ℝ → ℕ → ℝ) : Prop :=
  (0 < δ2 ∧ δ2 < 2) → ∀ e0 : ℝ, 0 < e0 → e0 < 1 → 10.4 ≤ Real.log (Real.log (x2 X3)) →
  ∀ N : ℕ, X3 ^ 8 < N → Even N → ∀ a3 : ℝ, 0 < a3 → a3 < 1 / 6 →
    u0R ≤ 3 ^ 10 * (N : ℝ) ^ a3 / Real.log N ^ 10 →
    (SB N (zN N) (yN N) : ℝ) < U N * N / Real.log N ^ 2 * cB e0 a3 N

/-! ### The printed theorems at 32.15 -/

/-- **Theorem 44 VERBATIM**, case (a) with 2e^{-γ}. -/
def PrintedThm44Lit (k1 : ℕ → ℝ) : Prop :=
  Gen44 (fun a N => cAaLit a Section9.ε AT3215.gE twinC AT3215.c4a (Real.log N))
    (fun a N => cAbA a Section9.ε (Real.log (Real.log X2)) AT3215.gE twinC
      (BJSEm.eps (Kδ δ1 (x1 X2))) AT3215.aS AT3215.c4S (wP N) (Real.log N) (Real.log X2)) k1

/-- **Theorem 44 with the F-0020 correction**, e^{γ} in (a); (b) verbatim. -/
def PrintedThm44 (k1 : ℕ → ℝ) : Prop :=
  Gen44 (fun a N => cAaA a Section9.ε AT3215.gE twinC AT3215.c4a (Real.log N))
    (fun a N => cAbA a Section9.ε (Real.log (Real.log X2)) AT3215.gE twinC
      (BJSEm.eps (Kδ δ1 (x1 X2))) AT3215.aS AT3215.c4S (wP N) (Real.log N) (Real.log X2)) k1

/-- **Theorem 50 VERBATIM**: the l(X₂) term over 2e^{γ}∏ log N. -/
def PrintedThm50 (k1 : ℕ → ℝ) : Prop :=
  Gen50 (fun a N => 8.0004 * (1 + 32.02 / Real.log N ^ 2) *
      (l1A a Section9.ε AT3215.gE 106 BJSp3215.nu + l2A a Section9.ε AT3215.gE (Real.log X2)) +
      BJSp3215.l BJSp3215.nu / (2 * AT3215.gE * twinC * Real.log N))
    (fun a N => 8.0004 * (1 + 32.02 / Real.log N ^ 2) * (1 + BJSEm.eps (Kδ δ1 (x1 X2))) *
      (l1A a Section9.ε AT3215.gE 106 BJSp3215.nuS + l2A a Section9.ε AT3215.gE (Real.log X2)) +
      BJSp3215.l BJSp3215.nuS / (2 * AT3215.gE * twinC * Real.log N)) k1

/-- **Theorem 50, weaker form**, the F-0021 factor (2e^{-γ}∏)⁻¹ in the l(X₂) term. -/
def PrintedThm50C (k1 : ℕ → ℝ) : Prop :=
  Gen50 (fun a N => 8.0004 * (1 + 32.02 / Real.log N ^ 2) *
      (l1A a Section9.ε AT3215.gE 106 BJSp3215.nu + l2A a Section9.ε AT3215.gE (Real.log X2)) +
      BJSp3215.l BJSp3215.nu * (AT3215.gE / (2 * twinC * Real.log N)))
    (fun a N => 8.0004 * (1 + 32.02 / Real.log N ^ 2) * (1 + BJSEm.eps (Kδ δ1 (x1 X2))) *
      (l1A a Section9.ε AT3215.gE 106 BJSp3215.nuS + l2A a Section9.ε AT3215.gE (Real.log X2)) +
      BJSp3215.l BJSp3215.nuS * (AT3215.gE / (2 * twinC * Real.log N))) k1

/-- **Theorem 51 VERBATIM**: ε₂((X₃)⁸, δ) and the factor (2e^{γ}∏)⁻¹. -/
def PrintedThm51 : Prop :=
  Gen51 (fun e0 a N => cBLit a Section9.ε e0 AT3215.gE twinC (BJSEm.eps (Kδ δ2 (x2 (X3 ^ 8))))
    BJS.cbar AT3215.mm (Real.log N))

/-- **Theorem 51, weaker form**, F-0021 and F-0022: ε₂(X₃, δ) and (2e^{-γ}∏)⁻¹. -/
def PrintedThm51C : Prop :=
  Gen51 (fun e0 a N => cBA a Section9.ε e0 AT3215.gE twinC (BJSEm.eps (Kδ δ2 (x2 X3)))
    BJS.cbar AT3215.mm (Real.log N))

/-- **Lemma 42, (125)**, p. 39, lines 2239 to 2244, at X₂ = exp(exp 32.15). -/
def PrintedLemma42 : Prop :=
  10.4 ≤ Real.log (Real.log (x1 X2)) → ∀ N : ℕ, 0 < N → Even N → X2 ≤ N →
    (N : ℝ) / Real.log N < cardA N ∧ (cardA N : ℝ) < 1.00005 * N / Real.log N

/-! ### X₂-level facts at 32.15 -/

lemma exp11_le : exp (11 : ℝ) ≤ 60000 := by
  have e : exp (11 : ℝ) = exp 1 ^ 11 := by rw [← exp_nat_mul]; norm_num
  have h := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le 11
  have : (2.7182818286 : ℝ) ^ 11 ≤ 60000 := by norm_num
  rw [e]; linarith

lemma X2_gt : (3 : ℝ) < X2 := by
  have h1 := add_one_le_exp (exp ll)
  have h2 : ll + 1 ≤ exp ll := add_one_le_exp ll
  have h3 : (32 : ℝ) < ll := by norm_num
  unfold X2; linarith

lemma logX2 : Real.log X2 = AT3215.LX := by unfold X2; rw [Real.log_exp]

lemma loglogX2 : Real.log (Real.log X2) = 3215 / 100 := by
  rw [logX2]; unfold AT3215.LX; rw [Real.log_exp]

lemma log_x1_X2 : Real.log (x1 X2) = exp ll - 5 * ll := by
  rw [log_x1 (by linarith [X2_gt]), loglogX2, logX2]

lemma Kδ1_X2 : Kδ δ1 (x1 X2) = Eps3215.B1 := by unfold Kδ Eps3215.B1; rw [log_x1_X2]

lemma e1_eq : BJSEm.eps (Kδ δ1 (x1 X2)) = AT3215.e1 := by rw [Kδ1_X2]

/-- log log x₁(X₂) ≥ 10.4, the first hypothesis of Theorems 44 and 50 and of (125). -/
theorem loglog_x1_X2 : 10.4 ≤ Real.log (Real.log (x1 X2)) := by
  rw [log_x1_X2]
  have hE := BJSm3215.exp3215_ge
  have h1 : exp (10.4 : ℝ) ≤ exp ll - 5 * ll := by
    have := exp_le_exp.mpr (show (10.4 : ℝ) ≤ 11 by norm_num)
    have := exp11_le
    norm_num at hE ⊢; linarith
  have := Real.log_le_log (exp_pos _) h1
  rwa [Real.log_exp] at this

/-- K_{δ₁}(x₁(X₂)) ≥ 3022, the last hypothesis of (140). -/
theorem K3022 : 3022 ≤ Kδ δ1 (x1 X2) := by
  rw [Kδ1_X2]
  have hE := BJSm3215.exp3215_ge
  have h1 : (1 : ℝ) ≤ exp ll - 5 * ll := by norm_num at hE ⊢; linarith
  have h2 : (exp ll - 5 * ll) ^ (1 : ℝ) ≤ (exp ll - 5 * ll) ^ (1.5029 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  rw [Real.rpow_one] at h2
  unfold Eps3215.B1
  norm_num at hE h2 ⊢; linarith

lemma X3_gt : (1 : ℝ) < X3 := by
  have h1 := add_one_le_exp (exp ll / 8)
  have h2 : 0 < exp ll / 8 := by positivity
  unfold X3; linarith

lemma log_x2_X3 : Real.log (x2 X3) = F0023.ℓP ll := by
  rw [log_x2 X3_gt]; unfold X3 F0023.ℓP F0023.Λ3P; rw [Real.log_exp]

lemma Kδ2_X3 : Kδ δ2 (x2 X3) = Eps3215.B2 := by unfold Kδ Eps3215.B2; rw [log_x2_X3]

/-- log log x₂(X₃) ≥ 10.4, a hypothesis of Theorem 51. -/
theorem loglog_x2_X3 : 10.4 ≤ Real.log (Real.log (x2 X3)) := by
  rw [log_x2_X3]
  have := BJSm3215.logℓ_bounds.1
  rw [Eps3215.ℓ_eq] at this
  linarith

lemma X3_8 : X3 ^ 8 = X2 := by
  unfold X3 X2; rw [← exp_nat_mul]; congr 1; push_cast; ring

lemma log_x2_X38 : Real.log (x2 (X3 ^ 8)) = exp ll - 15 * ll := by
  rw [X3_8, log_x2 (by linarith [X2_gt]), loglogX2, logX2]

/-! ### N-level facts for X₂ < N -/

lemma logN_facts {N : ℕ} (hN : X2 < (N : ℝ)) :
    1 < (N : ℝ) ∧ AT3215.LX ≤ Real.log N ∧ (9.174 : ℝ) * 10 ^ 13 ≤ Real.log N := by
  have h1 : 1 < (N : ℝ) := by linarith [X2_gt]
  have hL := Printed3215Pos.logN_ge hN
  exact ⟨h1, hL, le_trans exp3215_ge' hL⟩

lemma x1N {N : ℕ} (hN : X2 < (N : ℝ)) :
    Real.log (x1 N) = Real.log N - 5 * Real.log (Real.log N) ∧ 3 ≤ Real.log (x1 N) ∧
      Real.log (x1 N) ≤ Real.log N := by
  obtain ⟨h1, -, h9⟩ := logN_facts hN
  have e := log_x1 h1
  have hl := Printed3215Pos.log_le_lin14 (Real.log N) (by linarith)
  have hl0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  refine ⟨e, ?_, ?_⟩ <;> rw [e] <;> nlinarith

lemma u0_44 {N : ℕ} (hN : X2 < (N : ℝ)) :
    u0R ≤ (N : ℝ) ^ αP / (Real.log (x1 N) ^ 10 * Real.log N ^ (2.5 : ℝ)) := by
  obtain ⟨h1, -, h9⟩ := logN_facts hN
  obtain ⟨-, hx3, hxL⟩ := x1N hN
  set L := Real.log N with hLd
  set lx := Real.log (x1 N)
  have key := u0cond_44_50_A L lx h9 (by linarith) hxL
  have hNp : (0 : ℝ) < N := by linarith
  have hlx : 0 < lx := by linarith
  have hL0 : 0 < L := by linarith
  have e1 : (N : ℝ) ^ αP = exp (L * αP) := by rw [rpow_def_of_pos hNp]
  have e2 : lx ^ 10 = exp (10 * Real.log lx) := by
    rw [show (10 : ℝ) * Real.log lx = ((10 : ℕ) : ℝ) * Real.log lx by norm_num, exp_nat_mul,
      exp_log hlx]
  have e3 : L ^ (2.5 : ℝ) = exp (Real.log L * 2.5) := rpow_def_of_pos hL0 _
  rw [e1, e2, e3, ← exp_add, ← exp_sub, exp_le_exp]
  unfold u0
  linarith

lemma z_44 {N : ℕ} (hN : X2 < (N : ℝ)) :
    zN N ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - αP) / Real.log N ^ 20 := by
  obtain ⟨h1, -, h9⟩ := logN_facts hN
  set L := Real.log N with hLd
  have hr := (ranges_A L h9).2.2.2.2.1
  have hNp : (0 : ℝ) < N := by linarith
  have hL0 : 0 < L := by linarith
  have e0 : zN N ^ 2 = exp (L / 4) := by
    simp only [zN]; rw [rpow_def_of_pos hNp, sq, ← exp_add]; congr 1; rw [← hLd]; ring
  have e1 : (N : ℝ) ^ ((1 : ℝ) / 2 - αP) = exp (L * ((1 : ℝ) / 2 - αP)) := by
    rw [rpow_def_of_pos hNp]
  have e2 : L ^ 20 = exp (20 * Real.log L) := by
    rw [show (20 : ℝ) * Real.log L = ((20 : ℕ) : ℝ) * Real.log L by norm_num, exp_nat_mul,
      exp_log hL0]
  rw [e0, e1, e2, ← exp_sub, exp_le_exp]
  linarith

lemma r140 {N : ℕ} (hN : X2 < (N : ℝ)) :
    8 * αP + 160 * Real.log (Real.log N) / Real.log N < 1 :=
  (ranges_A _ (logN_facts hN).2.2).1

lemma u0_51 {N : ℕ} (hN : X2 < (N : ℝ)) :
    u0R ≤ 3 ^ 10 * (N : ℝ) ^ αP / Real.log N ^ 10 := by
  obtain ⟨h1, -, h9⟩ := logN_facts hN
  set L := Real.log N with hLd
  have key := u0cond_51_A L h9
  have hNp : (0 : ℝ) < N := by linarith
  have hL0 : 0 < L := by linarith
  have e0 : (3 : ℝ) ^ 10 = exp (10 * Real.log 3) := by
    rw [show (10 : ℝ) * Real.log 3 = ((10 : ℕ) : ℝ) * Real.log 3 by norm_num, exp_nat_mul,
      exp_log (by norm_num)]
  have e1 : (N : ℝ) ^ αP = exp (L * αP) := by rw [rpow_def_of_pos hNp]
  have e2 : L ^ 10 = exp (10 * Real.log L) := by
    rw [show (10 : ℝ) * Real.log L = ((10 : ℕ) : ℝ) * Real.log L by norm_num, exp_nat_mul,
      exp_log hL0]
  rw [e0, e1, e2, ← exp_add, ← exp_sub, exp_le_exp]
  unfold u0
  linarith

/-- w of Theorem 44 (b) for N > X₂, 0 below; only N > X₂ is ever used. -/
def wW (N : ℕ) : ℝ := if X2 < (N : ℝ) then wP N else 0

lemma wW_bounds (N : ℕ) : 0 ≤ wW N ∧ wW N ≤ Real.log N := by
  unfold wW
  split_ifs with hN
  · obtain ⟨h1, -, h9⟩ := logN_facts hN
    obtain ⟨-, hx3, hxL⟩ := x1N hN
    set L := Real.log (N : ℝ)
    set lx := Real.log (x1 N)
    have hA : Real.log (lx ^ 10) = 10 * Real.log lx := by rw [Real.log_pow]; norm_num
    have hl3 : 1 ≤ Real.log lx := by
      have := Real.log_le_log (by norm_num) hx3
      have := log_three_gt_d9; linarith
    have hlogA : 1 ≤ Real.log (Real.log (lx ^ 10)) := by
      rw [hA]
      have he : exp 1 ≤ 10 * Real.log lx := by have := exp_one_lt_d9; linarith
      have := Real.log_le_log (exp_pos 1) he
      rwa [Real.log_exp] at this
    have hlL : Real.log lx ≤ Real.log L := Real.log_le_log (by linarith) hxL
    have hlin := Printed3215Pos.log_le_lin14 L (by linarith)
    unfold wP
    rw [show Real.log (x1 N) = lx from rfl]
    have hA0 : 0 ≤ 1.3841 * Real.log (lx ^ 10) := by rw [hA]; linarith
    refine ⟨div_nonneg hA0 (by linarith), ?_⟩
    have := div_le_self hA0 hlogA
    rw [hA] at this ⊢
    linarith
  · exact ⟨le_rfl, Real.log_natCast_nonneg N⟩

/-- The printed case split of Theorems 44 and 50 at δ₁ = 1.5029. -/
def caseK (k1 : ℕ → ℝ) (N : ℕ) : Prop := k1 N < Kδ δ1 (x1 N)

lemma mainTerm_le {N : ℕ} (hN : X2 < (N : ℝ)) (hA : (N : ℝ) / Real.log N < cardA N) :
    mainTerm N ≤ (cardA N : ℝ) * U N / Real.log N := by
  obtain ⟨h1, -, h9⟩ := logN_facts hN
  have hU := U_pos N
  have hL0 : 0 < Real.log N := by linarith
  have e : mainTerm N = (N : ℝ) / Real.log N * U N / Real.log N := by
    simp only [mainTerm]; field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right hA.le hU.le
  exact div_le_div_of_nonneg_right this hL0.le

/-! ### Theorem 44 to Thm44At at 32.15 -/

/-- **Printed Theorem 44, with F-0020, and (125) give Thm44At at 32.15**, every hypothesis of the
printed theorem discharged at α₁ = αP. CONDITIONAL ON PrintedThm44 and PrintedLemma42. -/
theorem thm44At_of_printed (k1 : ℕ → ℝ) (hP : PrintedThm44 k1) (h42 : PrintedLemma42) :
    Thm44At (3215 / 100) (cA3215P (caseK k1) wW) := by
  intro N hE hN
  have hX : X2 < (N : ℝ) := hN
  obtain ⟨h1, hL, h9⟩ := logN_facts hX
  obtain ⟨ha, hb⟩ := hP loglog_x1_X2 ⟨by norm_num, by norm_num⟩ K3022 αP (by norm_num) N hX.le hE
    (u0_44 hX) (z_44 hX) (r140 hX)
  obtain ⟨hA, -⟩ := h42 loglog_x1_X2 N (by exact_mod_cast (show (0 : ℝ) < N by linarith)) hE hX.le
  have hM := mainTerm_le hX hA
  unfold cA3215P
  by_cases hc : caseK k1 N
  · rw [if_pos hc]
    have hlo := cAa_ge AT3215.gE twinC AT3215.c4a (Real.log N) g_ge g_le AT3215.hT
      AT3215.hc4a (by linarith)
    have hc0 : 0 ≤ cAaA αP Section9.ε AT3215.gE twinC AT3215.c4a (Real.log N) := by
      have := g_ge
      norm_num at hlo this ⊢; nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM hc0) (ha hc)
  · rw [if_neg hc]
    have hb' := hb (not_lt.mp hc)
    have hw : wW N = wP N := by unfold wW; rw [if_pos hX]
    simp only at hb'
    rw [loglogX2, logX2, e1_eq, ← hw] at hb'
    have hlo := cAb_ge AT3215.gE twinC AT3215.e1 AT3215.aS AT3215.c4S (wW N)
      (Real.log N) AT3215.LX g_ge g_le AT3215.hT AT3215.he1 AT3215.ha AT3215.hc4S (wW_bounds N)
      AT3215.LX_ge hL
    have hc0 : 0 ≤ cAbA αP Section9.ε (3215 / 100) AT3215.gE twinC AT3215.e1 AT3215.aS
        AT3215.c4S (wW N) (Real.log N) AT3215.LX := by
      have := g_ge
      norm_num [Section9.ε] at hlo this ⊢; nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM hc0) hb'

/-- **The F-0020 corrected Theorem 44 implies the verbatim one** at 32.15. -/
theorem printed44_imp_lit (k1 : ℕ → ℝ) (hP : PrintedThm44 k1) : PrintedThm44Lit k1 := by
  intro hll hδ hK a1 ha1 N hN hE hu hz h140
  obtain ⟨ha, hb⟩ := hP hll hδ hK a1 ha1 N hN hE hu hz h140
  refine ⟨fun hc => lt_of_le_of_lt ?_ (ha hc), hb⟩
  have hX : AT3215.LX ≤ Real.log N := by
    rw [← logX2]; exact Real.log_le_log (by linarith [X2_gt]) hN
  have hLX := AT3215.LX_ge
  have hL0 : 0 < Real.log N := by linarith
  have hll0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  have h8 : 8 * a1 < 1 := by
    have : 0 ≤ 160 * Real.log (Real.log N) / Real.log N := by positivity
    linarith
  have hM0 : 0 ≤ (cardA N : ℝ) * U N / Real.log N := by
    have := U_pos N; positivity
  apply mul_le_mul_of_nonneg_right _ hM0
  simp only [cAaLit, cAaA]
  have hs := Section9F9.small_div29 32.02 (Real.log N) (by norm_num) (by norm_num) (by linarith)
  apply mul_le_mul_of_nonneg_left _ (by norm_num at hs ⊢; linarith)
  have hfr : 2 * exp (-eulerMascheroniConstant) * Real.log (3 - 8 * a1) / (4 - 8 * a1) ≤
      fS AT3215.gE (4 - 8 * a1) := by
    unfold fS
    rw [show (4 : ℝ) - 8 * a1 - 1 = 3 - 8 * a1 by ring]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have hlog : 0 ≤ Real.log (3 - 8 * a1) := Real.log_nonneg (by linarith)
    have hinv : exp (-eulerMascheroniConstant) ≤ AT3215.gE := by
      rw [exp_neg]
      have hg := g_ge
      calc (exp eulerMascheroniConstant)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
        _ ≤ AT3215.gE := by linarith
    have := mul_le_mul_of_nonneg_right hinv hlog
    linarith
  linarith

/-! ### Theorem 50 to Thm50At at 32.15 -/

/-- **Verbatim Theorem 50 implies the weaker F-0021 form** at 32.15. -/
theorem printed50_imp_C (k1 : ℕ → ℝ) (hP : PrintedThm50 k1) : PrintedThm50C k1 := by
  intro hll a2 h1 h2 N hN hE hu
  obtain ⟨ha, hb⟩ := hP hll a2 h1 h2 N hN hE hu
  have hX : AT3215.LX ≤ Real.log N := by
    rw [← logX2]; exact Real.log_le_log (by linarith [X2_gt]) hN
  have hLX := AT3215.LX_ge
  have hL0 : 0 < Real.log N := by linarith
  have hM0 : 0 ≤ U N * N / Real.log N ^ 2 := by have := U_pos N; positivity
  have hg : (1 : ℝ) ≤ AT3215.gE := by have := g_ge; linarith
  have hT : (0 : ℝ) < twinC := by have := AT3215.hT; linarith
  refine ⟨fun hc => lt_of_lt_of_le (ha hc) ?_, fun hc => lt_of_lt_of_le (hb hc) ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hM0
    have := lterm_le _ _ _ _ AT3215.hla.1 hg hT hL0
    simp only; linarith
  · apply mul_le_mul_of_nonneg_left _ hM0
    have := lterm_le _ _ _ _ AT3215.hlS.1 hg hT hL0
    simp only; linarith

/-- **The weaker Theorem 50 gives Thm50At at 32.15**, hypotheses discharged at α₂ = αP.
CONDITIONAL ON PrintedThm50C. -/
theorem thm50At_of_printedC (k1 : ℕ → ℝ) (hP : PrintedThm50C k1) :
    Thm50At (3215 / 100) (cQ3215P (caseK k1)) := by
  intro N hE hN
  have hX : X2 < (N : ℝ) := hN
  obtain ⟨h1, hL, h9⟩ := logN_facts hX
  obtain ⟨ha, hb⟩ := hP loglog_x1_X2 αP (by norm_num) (by norm_num) N hX.le hE (u0_44 hX)
  have hL0 : 0 < Real.log N := by linarith
  have hM0 : 0 ≤ U N * N / Real.log N ^ 2 := by have := U_pos N; positivity
  have hg0 : 0 ≤ AT3215.gE := AT3215.g0
  have hT : (0 : ℝ) < twinC := by have := AT3215.hT; linarith
  have hdiv : AT3215.gE / (2 * twinC * Real.log N) ≤ AT3215.gE / (2 * twinC) := by
    apply div_le_div_of_nonneg_left hg0 (by positivity)
    nlinarith
  unfold cQ3215P
  by_cases hc : caseK k1 N
  · rw [if_pos hc]
    have h := ha hc
    simp only at h
    rw [logX2] at h
    refine lt_of_lt_of_le h ?_
    rw [mul_comm (cQaA _ _ _ _ _ _ _ _)]
    apply mul_le_mul_of_nonneg_left _ hM0
    unfold cQaA
    have e1 : l1aA = l1A αP Section9.ε AT3215.gE 106 BJSp3215.nu := rfl
    have e2 : AT3215.la = BJSp3215.l BJSp3215.nu := rfl
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hdiv AT3215.hla.1
    rw [e2] at this
    linarith
  · rw [if_neg hc]
    have h := hb (not_lt.mp hc)
    simp only at h
    rw [logX2, e1_eq] at h
    refine lt_of_lt_of_le h ?_
    rw [mul_comm (cQbA _ _ _ _ _ _ _ _ _)]
    apply mul_le_mul_of_nonneg_left _ hM0
    unfold cQbA
    have e1 : l1SA = l1A αP Section9.ε AT3215.gE 106 BJSp3215.nuS := rfl
    have e2 : AT3215.lS = BJSp3215.l BJSp3215.nuS := rfl
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hdiv AT3215.hlS.1
    rw [e2] at this
    linarith

/-! ### Theorem 51 to Thm51At at 32.15 -/

/-- **The weaker Theorem 51 gives Thm51At at 32.15**, hypotheses discharged at δ₂ = 1.47115,
ε₀ = 2.15·10⁻⁴, α₃ = αP. CONDITIONAL ON PrintedThm51C. -/
theorem thm51At_of_printedC (hP : PrintedThm51C) : Thm51At (3215 / 100) cB3215P := by
  intro N hE hN
  have hX : X2 < (N : ℝ) := hN
  have h := hP ⟨by norm_num, by norm_num⟩ At3215.ee0 (by norm_num) (by norm_num) loglog_x2_X3 N
    (by rw [X3_8]; exact hX) hE αP (by norm_num) (by norm_num) (u0_51 hX)
  simp only at h
  rw [Kδ2_X3] at h
  unfold cB3215P
  rw [mul_comm]
  exact h

/-- ε₂((X₃)⁸, δ₂) ≤ 1/51 at 32.15, so the verbatim ε₂ of Theorem 51 is at most the corrected one. -/
lemma eps_lit_le : BJSEm.eps (Kδ δ2 (x2 (X3 ^ 8))) ≤ 1 / 51 := by
  have hE := BJSm3215.exp3215_ge
  have hpos : exp (31 : ℝ) ≤ exp ll - 15 * ll := by have := exp31_le; norm_num at hE ⊢; linarith
  have hp0 : 0 < exp ll - 15 * ll := lt_of_lt_of_le (exp_pos _) hpos
  have hl : 31 ≤ Real.log (exp ll - 15 * ll) := by
    have := Real.log_le_log (exp_pos _) hpos; rwa [Real.log_exp] at this
  have hB : (BJS.oddPrimorial 53 : ℝ) ≤ Kδ δ2 (x2 (X3 ^ 8)) := by
    unfold Kδ; rw [log_x2_X38, rpow_def_of_pos hp0]
    refine le_trans exp45_ge (exp_le_exp.mpr ?_)
    show (45 : ℝ) ≤ Real.log (exp ll - 15 * ll) * (1.47115 : ℝ)
    have := mul_le_mul_of_nonneg_right hl (by norm_num : (0 : ℝ) ≤ 1.47115)
    norm_num at this ⊢; linarith
  have hp := pbar_ge53 hB
  unfold BJSEm.eps
  have : (53 : ℝ) ≤ (BJSEm.pbar (Kδ δ2 (x2 (X3 ^ 8))) : ℝ) := by exact_mod_cast hp
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- The algebraic comparison of Theorem 51's verbatim and weaker constants, for the cBA of
Printed3215Pos. -/
lemma cBLit_le (a e e0 g T e2 e2' cb m L : ℝ)
    (hP0 : 0 ≤ (1 + 4.51 / L ^ 2) * (2 / (1 / 2 - a) * g + 3 * e * 106 * exp 2 * h (3 / 2 - 3 * a)) *
      (1 + e0 + 9 / L) *
      (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)))
    (hS0 : 0 ≤ 320 * m * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0)))
    (he : e2' ≤ e2) (hgT : 1 / (2 * g * T) ≤ g / (2 * T)) :
    cBLit a e e0 g T e2' cb m L ≤ cBA a e e0 g T e2 cb m L := by
  have key : cBA a e e0 g T e2 cb m L - cBLit a e e0 g T e2' cb m L =
      1.00005 * ((e2 - e2') * ((1 + 4.51 / L ^ 2) *
        (2 / (1 / 2 - a) * g + 3 * e * 106 * exp 2 * h (3 / 2 - 3 * a)) * (1 + e0 + 9 / L) *
        (cb + 36 / L ^ 2 + (log (8 / 3) + 64 / L ^ 2) * (10 * log (1 + e0) / L + 27 / L ^ 2)))) +
      (g / (2 * T) - 1 / (2 * g * T)) * (320 * m * (1 + e0) / (3 * log (1 + e0)) +
        0.13 * (1 + e0) * L ^ 5 / (exp (L / 8) * log (1 + e0))) := by
    unfold cBA cBLit; ring
  have t1 := mul_nonneg (sub_nonneg.mpr he) hP0
  have t2 := mul_nonneg (sub_nonneg.mpr hgT) hS0
  nlinarith

/-- **Verbatim Theorem 51 implies the weaker F-0021, F-0022 form** at 32.15. -/
theorem printed51_imp_C (hP : PrintedThm51) : PrintedThm51C := by
  intro hδ e0 he0 he1 hll N hN hE a3 ha3 ha3' hu
  have hh := hP hδ e0 he0 he1 hll N hN hE a3 ha3 ha3' hu
  refine lt_of_lt_of_le hh ?_
  have hX : X2 < (N : ℝ) := by rw [← X3_8]; exact hN
  obtain ⟨h1, hL, h9⟩ := logN_facts hX
  have hL0 : 0 < Real.log (N : ℝ) := by linarith
  have hM0 : 0 ≤ U N * N / Real.log (N : ℝ) ^ 2 := by have := U_pos N; positivity
  apply mul_le_mul_of_nonneg_left _ hM0
  simp only
  rw [Kδ2_X3]
  have he2 : BJSEm.eps Eps3215.B2 = 1 / 51 := Eps3215.eps2_3215
  have hle : BJSEm.eps (Kδ δ2 (x2 (X3 ^ 8))) ≤ BJSEm.eps Eps3215.B2 := by rw [he2]; exact eps_lit_le
  have hg := g_ge
  have hg0 : (0 : ℝ) ≤ AT3215.gE := AT3215.g0
  have hT := AT3215.hT
  have hlog1 : 0 < Real.log (1 + e0) := Real.log_pos (by linarith)
  have hm0 := BJSm3215.mX3_vS_bounds.1
  have hcb := AT3215.hcb.1
  have h830 := log83_nonneg
  have hhh : 0 ≤ h (3 / 2 - 3 * a3) := h_nonneg _ (by linarith)
  have hε : (0 : ℝ) < Section9.ε := by norm_num [Section9.ε]
  have hA0 : 0 ≤ 2 / (1 / 2 - a3) * AT3215.gE + 3 * Section9.ε * 106 * exp 2 * h (3 / 2 - 3 * a3) :=
    add_nonneg (mul_nonneg (div_nonneg (by norm_num) (by linarith)) hg0)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε.le) (by norm_num))
        (exp_pos 2).le) hhh)
  have hB0 : 0 ≤ 1 + e0 + 9 / Real.log (N : ℝ) := by
    have := div_nonneg (by norm_num : (0 : ℝ) ≤ 9) hL0.le; linarith
  have hC0 : 0 ≤ BJS.cbar + 36 / Real.log (N : ℝ) ^ 2 + (log (8 / 3) + 64 / Real.log (N : ℝ) ^ 2) *
      (10 * log (1 + e0) / Real.log (N : ℝ) + 27 / Real.log (N : ℝ) ^ 2) :=
    add_nonneg (add_nonneg hcb (by positivity)) (mul_nonneg (add_nonneg h830 (by positivity))
      (add_nonneg (div_nonneg (by linarith) hL0.le) (by positivity)))
  have hP0 := mul_nonneg (mul_nonneg (mul_nonneg (by positivity :
    (0 : ℝ) ≤ 1 + 4.51 / Real.log (N : ℝ) ^ 2) hA0) hB0) hC0
  have hS0 : 0 ≤ 320 * AT3215.mm * (1 + e0) / (3 * log (1 + e0)) +
      0.13 * (1 + e0) * Real.log (N : ℝ) ^ 5 / (exp (Real.log (N : ℝ) / 8) * log (1 + e0)) :=
    add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm0) (by linarith)) (by linarith))
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg hL0.le 5))
        (mul_nonneg (exp_pos _).le hlog1.le))
  have hgT := gT_le AT3215.gE twinC (by linarith) (by linarith)
  exact cBLit_le _ _ _ _ _ _ _ _ _ _ hP0 hS0 hle hgT

/-! ### A positive Chen count above exp(exp 32.15) from the printed statements -/

/-- **Chen at exp(exp 32.15) with κ = 10⁻⁵, CONDITIONAL ON PrintedThm44 (Theorem 44 with the F-0020
e^{γ}), PrintedThm50C, PrintedThm51C (Theorems 50, 51 in their weaker F-0021, F-0022 forms) and
PrintedLemma42 ((125)).** Every other hypothesis of the printed theorems is discharged in Lean. -/
theorem chenPos_3215_of_printedC (k1 : ℕ → ℝ)
    (h : PrintedThm44 k1 ∧ PrintedThm50C k1 ∧ PrintedThm51C ∧ PrintedLemma42) :
    ChenPosAt (3215 / 100) ∧
      ∀ N : ℕ, Even N → exp (exp (3215 / 100)) < N → (1 / 100000 : ℝ) * mainTerm N < chenCount N :=
  let r := chenPos_3215_printed (caseK k1) wW wW_bounds (thm44At_of_printed k1 h.1 h.2.2.2)
    (thm50At_of_printedC k1 h.2.1) (thm51At_of_printedC h.2.2.1)
  ⟨r.1, r.2.1⟩

/-- **The same CONDITIONAL ON PrintedThm44 (F-0020), the VERBATIM PrintedThm50 and PrintedThm51,
and PrintedLemma42.** -/
theorem chenPos_3215_of_printed (k1 : ℕ → ℝ)
    (h : PrintedThm44 k1 ∧ PrintedThm50 k1 ∧ PrintedThm51 ∧ PrintedLemma42) :
    ChenPosAt (3215 / 100) ∧
      ∀ N : ℕ, Even N → exp (exp (3215 / 100)) < N → (1 / 100000 : ℝ) * mainTerm N < chenCount N :=
  chenPos_3215_of_printedC k1 ⟨h.1, printed50_imp_C k1 h.2.1, printed51_imp_C h.2.2.1, h.2.2.2⟩

/-! ### Vacuity at 32.15 -/

lemma natX2 {N : ℕ} (hN : X2 ≤ (N : ℝ)) : 3 ≤ N := by
  have : (3 : ℝ) < N := lt_of_lt_of_le X2_gt hN
  exact_mod_cast this.le

/-- The shape of Theorem 44 at 32.15 is consistent: with both constants −1 it holds outright. -/
theorem shape44 (k1 : ℕ → ℝ) : Gen44 (fun _ _ => -1) (fun _ _ => -1) k1 := by
  intro _ _ _ a1 _ N hN _ _ _ _
  have h3 := natX2 hN
  have hc : (0 : ℝ) < cardA N := by exact_mod_cast cardA_pos N h3
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hM : 0 < (cardA N : ℝ) * U N / Real.log N := by have := U_pos N; positivity
  have hS : (0 : ℝ) ≤ SA N (zN N) := Nat.cast_nonneg _
  exact ⟨fun _ => by linarith, fun _ => by linarith⟩

/-- The shape of Theorem 50 at 32.15 is consistent. -/
theorem shape50 (k1 : ℕ → ℝ) :
    Gen50 (fun _ N => ((⌈yN N⌉₊ * N : ℕ) + 1 : ℝ) / (U N * N / Real.log N ^ 2))
      (fun _ N => ((⌈yN N⌉₊ * N : ℕ) + 1 : ℝ) / (U N * N / Real.log N ^ 2)) k1 := by
  intro _ a2 _ _ N hN _ _
  have h3 := natX2 hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < U N * N / Real.log N ^ 2 := by have := U_pos N; positivity
  have hs : (sumSAq N (zN N) (yN N) : ℝ) ≤ ((⌈yN N⌉₊ * N : ℕ) : ℝ) := by
    exact_mod_cast Verify1312.sumSAq_le N (zN N) (yN N)
  have e : U N * N / Real.log N ^ 2 * (((⌈yN N⌉₊ * N : ℕ) + 1 : ℝ) / (U N * N / Real.log N ^ 2)) =
      ((⌈yN N⌉₊ * N : ℕ) + 1 : ℝ) := by have := (U_pos N).ne'; field_simp
  exact ⟨fun _ => by rw [e]; linarith, fun _ => by rw [e]; linarith⟩

/-- The shape of Theorem 51 at 32.15 is consistent. -/
theorem shape51 : Gen51 (fun _ _ N => ((N : ℝ) + 1) / (U N * N / Real.log N ^ 2)) := by
  intro _ e0 _ _ _ N hN _ a3 _ _ _
  have hX : X2 < (N : ℝ) := by rw [← X3_8]; exact hN
  have h3 := natX2 hX.le
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < U N * N / Real.log N ^ 2 := by have := U_pos N; positivity
  have hs : SB N (zN N) (yN N) ≤ N := by
    classical
    unfold SB BSet
    exact (card_filter_le _ _).trans ((card_filter_le _ _).trans (card_range N).le)
  have hs' : (SB N (zN N) (yN N) : ℝ) ≤ N := by exact_mod_cast hs
  have e : U N * N / Real.log N ^ 2 * (((N : ℝ) + 1) / (U N * N / Real.log N ^ 2)) = (N : ℝ) + 1 := by
    have := (U_pos N).ne'; field_simp
  rw [e]; linarith

/-- **The hypotheses are inhabited at 32.15**: an even N > X₂ exists, and for it, at α = αP, every
N-level premise of Theorems 44, 50, 51 holds. -/
theorem hyps_inhabited : ∃ N : ℕ, Even N ∧ X2 < (N : ℝ) ∧
    u0R ≤ (N : ℝ) ^ αP / (Real.log (x1 N) ^ 10 * Real.log N ^ (2.5 : ℝ)) ∧
    zN N ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - αP) / Real.log N ^ 20 ∧
    8 * αP + 160 * Real.log (Real.log N) / Real.log N < 1 ∧
    u0R ≤ 3 ^ 10 * (N : ℝ) ^ αP / Real.log N ^ 10 ∧ X3 ^ 8 < (N : ℝ) := by
  set M := ⌈X2⌉₊ + 1
  have hX : X2 < ((2 * M : ℕ) : ℝ) := by
    have h1 := Nat.le_ceil X2
    have h0 : (0 : ℝ) ≤ ⌈X2⌉₊ := Nat.cast_nonneg _
    push_cast [M]; linarith
  exact ⟨2 * M, even_two_mul M, hX, u0_44 hX, z_44 hX, r140 hX, u0_51 hX, by rw [X3_8]; exact hX⟩

end LeanLab.ChenExplicit.PrintedWiring3215

#print axioms LeanLab.ChenExplicit.PrintedWiring3215.loglog_x1_X2
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.K3022
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.loglog_x2_X3
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.thm44At_of_printed
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.printed44_imp_lit
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.printed50_imp_C
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.thm50At_of_printedC
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.thm51At_of_printedC
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.eps_lit_le
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.printed51_imp_C
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.chenPos_3215_of_printedC
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.chenPos_3215_of_printed
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.shape44
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.shape50
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.shape51
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.hyps_inhabited
#print axioms LeanLab.ChenExplicit.PrintedWiring3215.wW_bounds
