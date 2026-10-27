/-
AI-written Lean code, Claude, 2026-10-19, PC run 20261019T0703Z-249, unit U-1041, a sed port of the cloud 32.73 file of U-5042, CLOUD 20261019T0114Z-cloud13, track T2.
U-1041 changes against At3273.lean, all checked by the build: log log X₂ = 32.72, δ = 1.4767 at the ε₁
boundary; ε₀ = 1.37·10⁻⁴; the m(X₃) hypothesis 10⁻¹⁰ → 3.4·10⁻¹⁰, proved in BJSm3272.lean; the
integral hypothesis 0.1476 → 0.14725, proved in FIntegral5.lean, so the m̄ bound 0.02208 → 0.02177.
Lean-side case (b) slack about 7.4·10⁻⁵ at g = 1.781, by exact rational arithmetic on the bounds.
P0009 BJS 2022 Theorem 3 at exp(exp 32.72), the lab's corrected Section 9 with every numeric
input PROVED, as AssemblyT.lean's `chen_328` does at 32.8.

Inputs, all PROVED: At3272.margin_bP and margin_aP, PC run 20261019T0003Z-19699, units U-0988;
ε₁ = 1/57, ε₂ = 1/51 from At3272Eps.lean, U-0989; m(X₃) ≤ 3.4·10⁻¹⁰ from BJSm3272.lean; a(X₂) ≤ 10⁻¹⁸,
c₄, c₄*, l, l*, l₁, l₁* ≤ 10⁻²⁰ from the ports BJSpX2At3272, BJSaX2At3272, BJSc2X2At3272,
BJSl1X2At3272; e^γ, the twin prime constant, c̄ and the F(c) integral from GammaBounds,
TwinCNumeric, BJSCbar and FIntegral. Here ε₀ = 1.37·10⁻⁴ in Theorem 51's constant, as in At3272.

`chen_3272` is CONDITIONAL ON BJS Theorems 44, 50, 51 with their constants as CORRECTED per
FINDINGS F-0020, F-0021, F-0022, Theorem 51 at ε₀ = 1.37·10⁻⁴, for any split of the even N into
case (a) and case (b) and any factor w(N) ∈ [0, log N] of Theorem 44 (b). So: if the three sieve
theorems hold as corrected, every even N > exp(exp 32.72) has more than 2·10⁻⁴ U_N N / log² N
representations as a prime plus a number with at most two prime factors. The paper prints
exp(exp 32.7), which does not follow from its printed argument, FINDING F-0023; Python puts the
corrected argument's limit near 32.714. Chen's theorem itself is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.At3272
import LeanLab.ChenExplicit.At3272Eps
import LeanLab.ChenExplicit.BJSm3272
import LeanLab.ChenExplicit.BJSc2X2At3272
import LeanLab.ChenExplicit.BJSl1X2At3272
import LeanLab.ChenExplicit.Section9Link

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT3272

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.At3272

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{32.72}. -/
abbrev LX : ℝ := exp (3272 / 100)

/-- ε₁, ε₂ at 32.72. -/
abbrev e1 : ℝ := BJSEm.eps At3272Eps.B1
abbrev e2 : ℝ := BJSEm.eps At3272Eps.B2
/-- m(X₃) at 32.72. -/
abbrev mm : ℝ := BJSm3272.mX3 BJSm3272.vS
/-- The X₂-only constants at 32.72. -/
abbrev aS : ℝ := BJSaX2At3272.aX2 gE twinC BJSc3272.c2term
abbrev c4S : ℝ := BJSp3272.c4 BJSp3272.nuS
abbrev l1S : ℝ := BJSl3272.l1 gE 106 BJSp3272.nuS
abbrev lS : ℝ := BJSp3272.l BJSp3272.nuS
abbrev c4a : ℝ := BJSp3272.c4 BJSp3272.nu
abbrev l1a : ℝ := BJSl3272.l1 gE 106 BJSp3272.nu
abbrev la : ℝ := BJSp3272.l BJSp3272.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.72). -/
def cA3272 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAa gE twinC c4a (Real.log N)
  else cAbP (3272 / 100) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.72), C₁(ε) = 106. -/
def cQ3272 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQa gE twinC l1a la (Real.log N) LX
  else cQb gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 1.37·10⁻⁴. -/
def cB3272 (N : ℕ) : ℝ := cBP ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (10 : ℝ) ^ 14 ≤ LX := by
  have := BJSm3272.exp3272_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [At3272Eps.eps1_3272]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [At3272Eps.eps2_3272]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (3272 / 100) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc3272.c2term_bounds
  have h1 := BJSaX2At3272.aX2_le g0 g_le hT c1
  have h0 := BJSaX2At3272.aX2_nonneg g0 g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp3272.nuS_good
  have h1 := BJSp3272.c4_le g; have h0 := BJSp3272.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp3272.nuS_good
  have h1 := BJSp3272.l_le g; have h0 := BJSp3272.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp3272.nu_good
  have h1 := BJSp3272.c4_le g; have h0 := BJSp3272.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp3272.nu_good
  have h1 := BJSp3272.l_le g; have h0 := BJSp3272.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3272.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3272.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3272.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3272.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.72)**, PROVED. -/
theorem margin_3272 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (3272 / 100) (cA3272 caseA w) (cQ3272 caseA) cB3272 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA3272 cQ3272 cB3272
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aP gE twinC e2 BJS.cbar mm c4a l1a la (Real.log N) LX g_ge g_le hT he2 hcb
      BJSm3272.mX3_vS_bounds hc4a hl1a hla LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bP gE twinC e1 e2 BJS.cbar mm aS c4S (w N) l1S lS (Real.log N) LX g_ge g_le hT
      he1 he2 hcb BJSm3272.mX3_vS_bounds ha hc4S (hw N) hl1S hlS LX_ge hL hI

/-- **BJS Theorem 3 at exp(exp 32.72), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_3272 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3272 / 100) (cA3272 caseA w)) (hQ : Thm50At (3272 / 100) (cQ3272 caseA))
    (hB : Thm51At (3272 / 100) cB3272) : BJS3At (3272 / 100) :=
  BJS3At_of_sieveBounds _ (by norm_num) _ _ _ hA hQ hB (margin_3272 caseA w hw)

end LeanLab.ChenExplicit.AT3272
