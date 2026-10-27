/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1914Z-cloud49, unit U-6713, track T2: a scripted port by gen/port3225_U6713.py of the 3230 file of cloud46 U-6602 to log log X₂ = 32.25, α = 10⁻⁵, Lemma 18 at u₀ = 10⁸ with ε = 1.91·10⁻⁷ through Section9U8.lean, δ₁ = 1.4985 for Theorems 44 and 50 and δ₂ = 1.4665 for Theorem 51, ε₁ = 1/57, ε₂ = 1/51, m(X₃) ≤ 10⁻¹¹ with ν ℓ ≥ 158; ν(x₁) log x₁ ≥ 135 in place of 145, so the Siegel term of (87) is bounded by 10⁻²⁶ in place of 10⁻³⁰, p(X₂) ≤ 10⁻²⁴ unchanged. Numeric lemmas retightened by the HAND table of the script. The 3230 header follows unchanged; where it differs from the code, the code is authoritative.
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1618Z-cloud46, unit U-6602, track T2.
Written from AssemblyT3270.lean of cloud42 U-6403 by gen/port3230_U6602.py; the ε₁ and ε₂ inputs by hand.
P0009 BJS 2022 Theorem 3 at exp(exp 32.3), below the printed exp(exp 32.7), from the lab's corrected
Section 9, with two values of δ re-chosen at the boundaries of the U-6404 model: δ₁ = 1.496 for the k₁
split of Theorems 44 and 50, so ε₁ = 1/57 by Eps3230.eps1_3230 and the X₂-only constants of BJSpX2At3230
and friends; and δ₂ = 1.464 for Theorem 51, which states its own "Let 0 < δ < 2", papers/P0009.txt
line 3327, so ε₂ = 1/51 by Eps3230.eps2_3230 and m(X₃) ≤ 10⁻¹¹ by BJSm3230.lean, Python m ≈ 8.8·10⁻¹².
α₁ = α₂ = α₃ = 10⁻⁵ as printed, ε₀ = 2·10⁻⁵. The model of U-6404 at α = 10⁻⁵ gives case (b) slack
about 4.4·10⁻⁴ over 2·10⁻⁴ at 32.3, and α = 10⁻⁵ is above the smallest admissible α ≈ 9.4·10⁻⁶ there.

`chen_3230` is CONDITIONAL ON BJS Theorems 44 and 50 at δ₁ = 1.496 and Theorem 51 at δ₂ = 1.464, all at
α = 10⁻⁵ with their constants CORRECTED per FINDINGS F-0020, F-0021, F-0022, and on the paper's range
conditions at these parameters, which the Thm44At, Thm50At and Thm51At hypotheses carry. So, if those
hold, every even N > exp(exp 32.3) has more than 2·10⁻⁴ U_N N / log² N representations as a prime plus a
number with at most two prime factors. Chen's theorem is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT32
import LeanLab.ChenExplicit.At3225
import LeanLab.ChenExplicit.Eps3225
import LeanLab.ChenExplicit.BJSm3225
import LeanLab.ChenExplicit.BJSc2X2At3225
import LeanLab.ChenExplicit.BJSl1X2At3225
import LeanLab.ChenExplicit.Section9Link

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT3225

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.Section9U8
  LeanLab.ChenExplicit.At3225

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{32.25}. -/
abbrev LX : ℝ := exp (3225 / 100)

/-- ε₁, ε₂ at 32.25. -/
abbrev e1 : ℝ := BJSEm.eps Eps3225.B1
abbrev e2 : ℝ := BJSEm.eps Eps3225.B2
/-- m(X₃) at 32.25. -/
abbrev mm : ℝ := BJSm3225.mX3 BJSm3225.vS
/-- The X₂-only constants at 32.25. -/
abbrev aS : ℝ := BJSaX2At3225.aX2 gE twinC BJSc3225.c2term
abbrev c4S : ℝ := BJSp3225.c4 BJSp3225.nuS
abbrev l1S : ℝ := BJSl3225.l1 gE 106 BJSp3225.nuS
abbrev lS : ℝ := BJSp3225.l BJSp3225.nuS
abbrev c4a : ℝ := BJSp3225.c4 BJSp3225.nu
abbrev l1a : ℝ := BJSl3225.l1 gE 106 BJSp3225.nu
abbrev la : ℝ := BJSp3225.l BJSp3225.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.25). -/
def cA3225 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAaU gE twinC c4a (Real.log N)
  else cAbPU (3225 / 100) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.25), C₁(εU) = 106. -/
def cQ3225 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQaU gE twinC l1a la (Real.log N) LX
  else cQbU gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 2·10⁻⁵. -/
def cB3225 (N : ℕ) : ℝ := cBPU ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (10 : ℝ) ^ 14 ≤ LX := by
  have := BJSm3225.exp3225_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [Eps3225.eps1_3225]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [Eps3225.eps2_3225]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (3225 / 100) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc3225.c2term_bounds
  have h1 := BJSaX2At3225.aX2_le g0 g_le hT c1
  have h0 := BJSaX2At3225.aX2_nonneg g0 g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp3225.nuS_good
  have h1 := BJSp3225.c4_le g; have h0 := BJSp3225.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp3225.nuS_good
  have h1 := BJSp3225.l_le g; have h0 := BJSp3225.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp3225.nu_good
  have h1 := BJSp3225.c4_le g; have h0 := BJSp3225.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp3225.nu_good
  have h1 := BJSp3225.l_le g; have h0 := BJSp3225.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3225.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3225.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl3225.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp3225.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.25)**, PROVED. -/
theorem margin_3225 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (3225 / 100) (cA3225 caseA w) (cQ3225 caseA) cB3225 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA3225 cQ3225 cB3225
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aP gE twinC e2 BJS.cbar mm c4a l1a la (Real.log N) LX g_ge g_le hT he2 hcb
      BJSm3225.mX3_vS_bounds hc4a hl1a hla LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bP gE twinC e1 e2 BJS.cbar mm aS c4S (w N) l1S lS (Real.log N) LX g_ge g_le hT
      he1 he2 hcb BJSm3225.mX3_vS_bounds ha hc4S (hw N) hl1S hlS LX_ge hL hI

/-- **BJS Theorem 3 at exp(exp 32.25), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_3225 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (3225 / 100) (cA3225 caseA w)) (hQ : Thm50At (3225 / 100) (cQ3225 caseA))
    (hB : Thm51At (3225 / 100) cB3225) : BJS3At (3225 / 100) :=
  BJS3At_of_sieveBounds32 _ (by norm_num) _ _ _ hA hQ hB (margin_3225 caseA w hw)

#print axioms margin_3225
#print axioms chen_3225
#print axioms BJSm3225.mX3_vS_bounds

end LeanLab.ChenExplicit.AT3225
