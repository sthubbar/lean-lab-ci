/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T0114Z-cloud13, unit U-5042, track T2.
P0009 BJS 2022 Theorem 3 at exp(exp 32.73), the lab's corrected Section 9 with every numeric
input PROVED, as AssemblyT.lean's `chen_328` does at 32.8.

Inputs, all PROVED: At3273.margin_bP and margin_aP, PC run 20261019T0003Z-19699, units U-0988;
ε₁ = 1/57, ε₂ = 1/51 from At3273Eps.lean, U-0989; m(X₃) ≤ 10⁻¹⁰ from BJSm3273.lean; a(X₂) ≤ 10⁻¹⁸,
c₄, c₄*, l, l*, l₁, l₁* ≤ 10⁻²⁰ from the ports BJSpX2At3273, BJSaX2At3273, BJSc2X2At3273,
BJSl1X2At3273; e^γ, the twin prime constant, c̄ and the F(c) integral from GammaBounds,
TwinCNumeric, BJSCbar and FIntegral. Here ε₀ = 6.4·10⁻⁵ in Theorem 51's constant, as in At3273.

`chen_3273` is CONDITIONAL ON BJS Theorems 44, 50, 51 with their constants as CORRECTED per
FINDINGS F-0020, F-0021, F-0022, Theorem 51 at ε₀ = 6.4·10⁻⁵, for any split of the even N into
case (a) and case (b) and any factor w(N) ∈ [0, log N] of Theorem 44 (b). So: if the three sieve
theorems hold as corrected, every even N > exp(exp 32.73) has more than 2·10⁻⁴ U_N N / log² N
representations as a prime plus a number with at most two prime factors. The paper prints
exp(exp 32.7), which does not follow from its printed argument, FINDING F-0023; Python puts the
corrected argument's limit near 32.714. Chen's theorem itself is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.At3273
import LeanLab.ChenExplicit.At3273Eps
import LeanLab.ChenExplicit.BJSm3273
import LeanLab.ChenExplicit.BJSc2X2At3273
import LeanLab.ChenExplicit.BJSl1X2At3273
import LeanLab.ChenExplicit.Section9Link

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT3273

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.At3273

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{32.73}. -/
abbrev LX : ℝ := exp (3273 / 100)

/-- ε₁, ε₂ at 32.73. -/
abbrev e1 : ℝ := BJSEm.eps At3273Eps.B1
abbrev e2 : ℝ := BJSEm.eps At3273Eps.B2
/-- m(X₃) at 32.73. -/
abbrev mm : ℝ := BJSm3273.mX3 BJSm3273.vS
/-- The X₂-only constants at 32.73. -/
abbrev aS : ℝ := BJSaX2At3273.aX2 gE twinC BJSc3273.c2term
abbrev c4S : ℝ := BJSp3273.c4 BJSp3273.nuS
abbrev l1S : ℝ := BJSl3273.l1 gE 106 BJSp3273.nuS
abbrev lS : ℝ := BJSp3273.l BJSp3273.nuS
abbrev c4a : ℝ := BJSp3273.c4 BJSp3273.nu
abbrev l1a : ℝ := BJSl3273.l1 gE 106 BJSp3273.nu
abbrev la : ℝ := BJSp3273.l BJSp3273.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.73). -/
def cA3273 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAa gE twinC c4a (Real.log N)
  else cAbP (3273 / 100) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.73), C₁(ε) = 106. -/
def cQ3273 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQa gE twinC l1a la (Real.log N) LX
  else cQb gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 6.4·10⁻⁵. -/
def cB3273 (N : ℕ) : ℝ := cBP ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (10 : ℝ) ^ 14 ≤ LX := by
  have := BJSm3273.exp3273_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [At3273Eps.eps1_3273]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [At3273Eps.eps2_3273]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (3273 / 100) LX - 1), log (t - 1) / t ≤ 0.1476 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt.I3_le

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc3273.c2term_bounds
  have h1 := BJSaX2At3273.aX2_le g0 g_le hT c1
  have h0 := BJSaX2At3273.aX2_nonneg g0 g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp3273.nuS_good
  have h1 := BJSp3273.c4_le g; have h0 := BJSp3273.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp3273.nuS_good
  have h1 := BJSp3273.l_le g; have h0 := BJSp3273.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp3273.nu_good
  have h1 := BJSp3273.c4_le g; have h0 := BJSp3273.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp3273.nu_good
  have h1 := BJSp3273.l_le g; have h0 := BJSp3273.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3273.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3273.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3273.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3273.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.73)**, PROVED. -/
theorem margin_3273 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (3273 / 100) (cA3273 caseA w) (cQ3273 caseA) cB3273 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA3273 cQ3273 cB3273
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aP gE twinC e2 BJS.cbar mm c4a l1a la (Real.log N) LX g_ge g_le hT he2 hcb
      BJSm3273.mX3_vS_bounds hc4a hl1a hla LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bP gE twinC e1 e2 BJS.cbar mm aS c4S (w N) l1S lS (Real.log N) LX g_ge g_le hT
      he1 he2 hcb BJSm3273.mX3_vS_bounds ha hc4S (hw N) hl1S hlS LX_ge hL hI

/-- **BJS Theorem 3 at exp(exp 32.73), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_3273 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3273 / 100) (cA3273 caseA w)) (hQ : Thm50At (3273 / 100) (cQ3273 caseA))
    (hB : Thm51At (3273 / 100) cB3273) : BJS3At (3273 / 100) :=
  BJS3At_of_sieveBounds _ (by norm_num) _ _ _ hA hQ hB (margin_3273 caseA w hw)

end LeanLab.ChenExplicit.AT3273
