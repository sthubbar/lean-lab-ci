/-
AI-written Lean code, Claude, 2026-10-19, run 20261019T0903Z-22821, built in the cloud workspace for the PC lab,
unit U-1045, track T2. A scripted port of AssemblyT3272.lean of PC run 20261019T0703Z-249, U-1041.
P0009 BJS 2022 Theorem 3 at exp(exp 32.716), the lab's corrected Section 9 with every numeric input PROVED.

Changes against the 32.72 chain: log log X₂ = 32.716; δ = 1.47681, just above the ε₁ boundary
δ* = 1.4767973 where 1.47681 · 32.716 = 48.3153 against log(3·5·…·59) = 48.3149; ε₀ = 1.6·10⁻⁴;
m(X₃) ≤ 4.64·10⁻¹⁰, proved in BJSm32716.lean, Python mpmath m ≈ 4.567·10⁻¹⁰. The Lean case (b) margin
depends on log log X₂ only through m(X₃), so the step from 32.72 is the m bound: exact rational
arithmetic on the bounds of At32716.margin_bP gives a Lean-side slack of about 1.3·10⁻⁵ at g = 1.781,
against 7.4·10⁻⁵ at 32.72.

Inputs, all PROVED: At32716.margin_bP and margin_aP; ε₁ = 1/57, ε₂ = 1/51 from At32716Eps.lean;
m(X₃) ≤ 4.64·10⁻¹⁰ from BJSm32716.lean; a(X₂) ≤ 10⁻¹⁸, c₄, c₄*, l, l*, l₁, l₁* ≤ 10⁻²⁰ from
BJSpX2At32716, BJSaX2At32716, BJSc2X2At32716, BJSl1X2At32716; e^γ, the twin prime constant, c̄ and
the F(c) integral from GammaBounds, TwinCNumeric, BJSCbar and FIntegral5.

`chen_32716` is CONDITIONAL ON BJS Theorems 44, 50, 51 with their constants as CORRECTED per
FINDINGS F-0020, F-0021, F-0022, Theorem 51 at ε₀ = 1.6·10⁻⁴, for any split of the even N into
case (a) and case (b) and any factor w(N) ∈ [0, log N] of Theorem 44 (b). So: if the three sieve
theorems hold as corrected, every even N > exp(exp 32.716) has more than 2·10⁻⁴ U_N N / log² N
representations as a prime plus a number with at most two prime factors. The paper prints
exp(exp 32.7), which does not follow from its printed argument, FINDING F-0023. The lab's Python
model of the corrected argument at α = 10⁻⁵ first closes near log log X₂ = 32.7132. Theorems 44, 50, 51
require N^α ≥ exp(10⁹(1 + 9·10⁻⁷/log 10⁹)) up to log powers, so α ≥ about 6.2·10⁻⁶ at these X₂; at that
smallest α the model closes near 32.7100, numerics/threshold_alphamin_U1045.
Chen's theorem itself is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.At32716
import LeanLab.ChenExplicit.At32716Eps
import LeanLab.ChenExplicit.BJSm32716
import LeanLab.ChenExplicit.BJSc2X2At32716
import LeanLab.ChenExplicit.BJSl1X2At32716
import LeanLab.ChenExplicit.Section9Link

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT32716

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.At32716

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{32.716}. -/
abbrev LX : ℝ := exp (32716 / 1000)

/-- ε₁, ε₂ at 32.716. -/
abbrev e1 : ℝ := BJSEm.eps At32716Eps.B1
abbrev e2 : ℝ := BJSEm.eps At32716Eps.B2
/-- m(X₃) at 32.716. -/
abbrev mm : ℝ := BJSm32716.mX3 BJSm32716.vS
/-- The X₂-only constants at 32.716. -/
abbrev aS : ℝ := BJSaX2At32716.aX2 gE twinC BJSc32716.c2term
abbrev c4S : ℝ := BJSp32716.c4 BJSp32716.nuS
abbrev l1S : ℝ := BJSl32716.l1 gE 106 BJSp32716.nuS
abbrev lS : ℝ := BJSp32716.l BJSp32716.nuS
abbrev c4a : ℝ := BJSp32716.c4 BJSp32716.nu
abbrev l1a : ℝ := BJSl32716.l1 gE 106 BJSp32716.nu
abbrev la : ℝ := BJSp32716.l BJSp32716.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.716). -/
def cA32716 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAa gE twinC c4a (Real.log N)
  else cAbP (32716 / 1000) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.716), C₁(ε) = 106. -/
def cQ32716 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQa gE twinC l1a la (Real.log N) LX
  else cQb gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 1.6·10⁻⁴. -/
def cB32716 (N : ℕ) : ℝ := cBP ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (10 : ℝ) ^ 14 ≤ LX := by
  have := BJSm32716.exp32716_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [At32716Eps.eps1_32716]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [At32716Eps.eps2_32716]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (32716 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc32716.c2term_bounds
  have h1 := BJSaX2At32716.aX2_le g0 g_le hT c1
  have h0 := BJSaX2At32716.aX2_nonneg g0 g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp32716.nuS_good
  have h1 := BJSp32716.c4_le g; have h0 := BJSp32716.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp32716.nuS_good
  have h1 := BJSp32716.l_le g; have h0 := BJSp32716.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp32716.nu_good
  have h1 := BJSp32716.c4_le g; have h0 := BJSp32716.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp32716.nu_good
  have h1 := BJSp32716.l_le g; have h0 := BJSp32716.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl32716.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp32716.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl32716.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp32716.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.716)**, PROVED. -/
theorem margin_32716 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (32716 / 1000) (cA32716 caseA w) (cQ32716 caseA) cB32716 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA32716 cQ32716 cB32716
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aP gE twinC e2 BJS.cbar mm c4a l1a la (Real.log N) LX g_ge g_le hT he2 hcb
      BJSm32716.mX3_vS_bounds hc4a hl1a hla LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bP gE twinC e1 e2 BJS.cbar mm aS c4S (w N) l1S lS (Real.log N) LX g_ge g_le hT
      he1 he2 hcb BJSm32716.mX3_vS_bounds ha hc4S (hw N) hl1S hlS LX_ge hL hI

/-- **BJS Theorem 3 at exp(exp 32.716), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_32716 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (32716 / 1000) (cA32716 caseA w)) (hQ : Thm50At (32716 / 1000) (cQ32716 caseA))
    (hB : Thm51At (32716 / 1000) cB32716) : BJS3At (32716 / 1000) :=
  BJS3At_of_sieveBounds _ (by norm_num) _ _ _ hA hQ hB (margin_32716 caseA w hw)

#print axioms margin_32716
#print axioms chen_32716
#print axioms BJSm32716.mX3_vS_bounds

end LeanLab.ChenExplicit.AT32716
