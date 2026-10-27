/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6403, track T1.
Written from AssemblyT32716.lean of PC U-1045 by a substitution script; the ε₁ and ε₂ inputs by hand.
P0009 BJS 2022 Theorem 3 at the PRINTED threshold exp(exp 32.7), from the lab's corrected Section 9,
with two values of δ: δ₁ = 1.478, the printed value, for the k₁ split of Theorems 44 and 50, so
ε₁ = 1/57 by F0023.eps1_printed and the X₂-only constants of BJSpX2At3270 and friends; and δ₂ = 1.445
for Theorem 51, which states its own "Let 0 < δ < 2", papers/P0009.txt line 3327, so ε₂ = 1/51 by
Eps3270.eps2_3270 and m(X₃) ≤ 10⁻¹¹ by BJSm3270.lean, Python m ≈ 5.9·10⁻¹² against 1.21·10⁻⁸ at
δ = 1.478. α₁ = α₂ = α₃ = 10⁻⁵ as printed, ε₀ = 2·10⁻⁵. Lean-side case (b) slack about 3.7·10⁻⁴.

`chen_3270` is CONDITIONAL ON BJS Theorems 44 and 50 at δ₁ = 1.478 and Theorem 51 at δ₂ = 1.445, all
at α = 10⁻⁵ with their constants CORRECTED per FINDINGS F-0020, F-0021, F-0022. So, if those hold, every
even N > exp(exp 32.7) has more than 2·10⁻⁴ U_N N / log² N representations as a prime plus a number with
at most two prime factors: the paper's printed threshold is RECOVERED from its own argument once δ is
re-chosen in Theorem 51. This qualifies FINDING F-0023: it holds for the printed single δ only.
Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.At3270
import LeanLab.ChenExplicit.Eps3270
import LeanLab.ChenExplicit.BJSm3270
import LeanLab.ChenExplicit.BJSc2X2At3270
import LeanLab.ChenExplicit.BJSl1X2At3270
import LeanLab.ChenExplicit.Section9Link

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT3270

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.At3270

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{32.7}. -/
abbrev LX : ℝ := exp (327 / 10)

/-- ε₁, ε₂ at 32.7. -/
abbrev e1 : ℝ := BJSEm.eps F0023.B1P
abbrev e2 : ℝ := BJSEm.eps Eps3270.B2
/-- m(X₃) at 32.7. -/
abbrev mm : ℝ := BJSm3270.mX3 BJSm3270.vS
/-- The X₂-only constants at 32.7. -/
abbrev aS : ℝ := BJSaX2At3270.aX2 gE twinC BJSc3270.c2term
abbrev c4S : ℝ := BJSp3270.c4 BJSp3270.nuS
abbrev l1S : ℝ := BJSl3270.l1 gE 106 BJSp3270.nuS
abbrev lS : ℝ := BJSp3270.l BJSp3270.nuS
abbrev c4a : ℝ := BJSp3270.c4 BJSp3270.nu
abbrev l1a : ℝ := BJSl3270.l1 gE 106 BJSp3270.nu
abbrev la : ℝ := BJSp3270.l BJSp3270.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.7). -/
def cA3270 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAa gE twinC c4a (Real.log N)
  else cAbP (327 / 10) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.7), C₁(ε) = 106. -/
def cQ3270 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQa gE twinC l1a la (Real.log N) LX
  else cQb gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 2·10⁻⁵. -/
def cB3270 (N : ℕ) : ℝ := cBP ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (10 : ℝ) ^ 14 ≤ LX := by
  have := BJSm3270.exp3270_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [F0023.eps1_printed]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [Eps3270.eps2_3270]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (327 / 10) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc3270.c2term_bounds
  have h1 := BJSaX2At3270.aX2_le g0 g_le hT c1
  have h0 := BJSaX2At3270.aX2_nonneg g0 g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp3270.nuS_good
  have h1 := BJSp3270.c4_le g; have h0 := BJSp3270.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp3270.nuS_good
  have h1 := BJSp3270.l_le g; have h0 := BJSp3270.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp3270.nu_good
  have h1 := BJSp3270.c4_le g; have h0 := BJSp3270.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp3270.nu_good
  have h1 := BJSp3270.l_le g; have h0 := BJSp3270.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3270.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3270.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3270.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3270.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.7)**, PROVED. -/
theorem margin_3270 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (327 / 10) (cA3270 caseA w) (cQ3270 caseA) cB3270 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA3270 cQ3270 cB3270
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aP gE twinC e2 BJS.cbar mm c4a l1a la (Real.log N) LX g_ge g_le hT he2 hcb
      BJSm3270.mX3_vS_bounds hc4a hl1a hla LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bP gE twinC e1 e2 BJS.cbar mm aS c4S (w N) l1S lS (Real.log N) LX g_ge g_le hT
      he1 he2 hcb BJSm3270.mX3_vS_bounds ha hc4S (hw N) hl1S hlS LX_ge hL hI

/-- **BJS Theorem 3 at exp(exp 32.7), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_3270 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (327 / 10) (cA3270 caseA w)) (hQ : Thm50At (327 / 10) (cQ3270 caseA))
    (hB : Thm51At (327 / 10) cB3270) : BJS3At (327 / 10) :=
  BJS3At_of_sieveBounds _ (by norm_num) _ _ _ hA hQ hB (margin_3270 caseA w hw)

#print axioms margin_3270
#print axioms chen_3270
#print axioms BJSm3270.mX3_vS_bounds

end LeanLab.ChenExplicit.AT3270
