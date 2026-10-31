/-
AI wrote this Lean code. CODEX task44.
Numeric assembly of the U1498 margins at log log X2 equal 31.567.
No chen_31567 is claimed here. The printed u0 condition fails at this alpha.
See PrintedRange31567 and PROGRESS.md. Binary Goldbach is OPEN.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.U1498Margin
import LeanLab.ChenExplicit.Eps31567
import LeanLab.ChenExplicit.U1498MX3
import LeanLab.ChenExplicit.BJSc2X2At31567
import LeanLab.ChenExplicit.BJSl1X2At31567
import LeanLab.ChenExplicit.Section9Link
import LeanLab.ChenExplicit.U1498Link

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT31567

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9 LeanLab.ChenExplicit.F0023
  LeanLab.ChenExplicit.Section9U8 LeanLab.ChenExplicit.U1498Section9F5
  LeanLab.ChenExplicit.U1498Margin

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{31.567}. -/
abbrev LX : ℝ := exp (31567 / 1000)

/-- ε₁, ε₂ at 31.567. -/
abbrev e1 : ℝ := BJSEm.eps Eps31567.B1
abbrev e2 : ℝ := BJSEm.eps Eps31567.B2
/-- m(X₃) at 31.567. -/
abbrev mm : ℝ := U1498MX3.mX3 U1498MX3.vS
/-- The X₂-only constants at 31.567. -/
abbrev aS : ℝ := BJSaX2At31567.aX2 gE twinC BJSc31567.c2term
abbrev c4S : ℝ := BJSp31567.c4 BJSp31567.nuS
abbrev l1S : ℝ := BJSl31567.l1 gE 106 BJSp31567.nuS
abbrev lS : ℝ := BJSp31567.l BJSp31567.nuS
abbrev c4a : ℝ := BJSp31567.c4 BJSp31567.nu
abbrev l1a : ℝ := BJSl31567.l1 gE 106 BJSp31567.nu
abbrev la : ℝ := BJSp31567.l BJSp31567.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 31.567). -/
def cA31567 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAaU gE twinC c4a (Real.log N)
  else cAbPU (31567 / 1000) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 31.567), C₁(εU) = 106. -/
def cQ31567 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQaU gE twinC l1a la (Real.log N) LX
  else cQbU gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 1.48·10⁻⁴. -/
def cB31567 (N : ℕ) : ℝ := cBPU ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (5 : ℝ) * 10 ^ 13 ≤ LX := by
  have := U1498MX3.exp31567_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [Eps31567.eps1_31567]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [Eps31567.eps2_31567]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (31567 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc31567.c2term_bounds
  have h1 := BJSaX2At31567.aX2_le g0 g_le hT c1
  have h0 := BJSaX2At31567.aX2_nonneg g0 g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp31567.nuS_good
  have h1 := BJSp31567.c4_le g; have h0 := BJSp31567.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp31567.nuS_good
  have h1 := BJSp31567.l_le g; have h0 := BJSp31567.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp31567.nu_good
  have h1 := BJSp31567.c4_le g; have h0 := BJSp31567.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp31567.nu_good
  have h1 := BJSp31567.l_le g; have h0 := BJSp31567.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl31567.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp31567.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl31567.l1_bounds (C1 := 106) g0 g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp31567.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- **The corrected Section 9 margin holds for every even N > exp(exp 31.567)**. -/
theorem margin_31567 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (31567 / 1000) (cA31567 caseA w) (cQ31567 caseA) cB31567 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA31567 cQ31567 cB31567
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := U1498Link.margin_a_31567 gE twinC e2 BJS.cbar c4a l1a la (Real.log N)
      g_ge g_le hT he2 hcb hc4a hl1a hla hL
    linarith
  · simp only [hc, ite_false]
    exact U1498Link.margin_b_31567 gE twinC e1 e2 BJS.cbar aS c4S (w N) l1S lS
      (Real.log N) g_ge g_le hT he1 he2 hcb ha hc4S (hw N) hl1S hlS hL

/-- The factor multiplying c4 star in printed Theorem 44 b, with L equal log N. -/
def wFactor (L : ℝ) : ℝ :=
  1.3841 * (10 * log (L - 5 * log L)) / log (10 * log (L - 5 * log L))

lemma wFactor_bounds {L : ℝ} (hL : LX ≤ L) : 0 ≤ wFactor L ∧ wFactor L ≤ L := by
  have h5 : (5e13 : ℝ) ≤ L := by have := LX_ge; norm_num at this ⊢; linarith
  have hsub := BJSp31567.Lsub_ge h5
  have hs := BJSp31567.sqrtL_ge h5
  have hl := BJSp31567.logL_le h5
  have hl0 := BJSp31567.logL_nonneg h5
  have he := exp_one_lt_d9
  have hy0 : 0 < L - 5 * log L := by linarith
  have hy1 : 1 ≤ log (L - 5 * log L) := by
    rw [le_log_iff_exp_le hy0]; linarith
  have hd : 1 ≤ log (10 * log (L - 5 * log L)) := by
    rw [le_log_iff_exp_le (by linarith)]; linarith
  have hn : 0 ≤ 1.3841 * (10 * log (L - 5 * log L)) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (by linarith [hy1]))
  have hlog : log (L - 5 * log L) ≤ log L := log_le_log hy0 (by linarith)
  have hw : wFactor L ≤ 13.841 * log L := by
    unfold wFactor
    rw [div_le_iff₀ (by linarith)]
    have hn' : 1.3841 * (10 * log (L - 5 * log L)) ≤ 13.841 * log L := by linarith
    have := mul_le_mul_of_nonneg_left hd (show 0 ≤ 13.841 * log L by positivity)
    nlinarith
  have hs2 : sqrt L * sqrt L = L := mul_self_sqrt (by linarith)
  constructor
  · unfold wFactor; exact div_nonneg hn (by linarith)
  · nlinarith

/-- The printed w factor above X2 and zero elsewhere. -/
noncomputable def w31567 (N : ℕ) : ℝ := if exp LX < (N : ℝ) then wFactor (Real.log N) else 0

lemma w31567_bounds (N : ℕ) : 0 ≤ w31567 N ∧ w31567 N ≤ Real.log N := by
  unfold w31567
  split_ifs with hN
  · have hp : (0 : ℝ) < N := (exp_pos LX).trans hN
    exact wFactor_bounds ((Real.lt_log_iff_exp_lt hp).mpr hN).le
  · exact ⟨le_rfl, Real.log_natCast_nonneg N⟩

/-- The two U1498 margins with the actual w factor and all numeric hypotheses discharged. -/
theorem margin_actual_31567 (caseA : ℕ → Prop) :
    MarginAt (31567 / 1000) (cA31567 caseA w31567) (cQ31567 caseA) cB31567 :=
  margin_31567 caseA w31567 w31567_bounds

/-- All constants and the two margin cases have a concrete numeric instance. -/
example : MarginAt (31567 / 1000) (cA31567 (fun _ => True) (fun _ => 0))
    (cQ31567 (fun _ => True)) cB31567 :=
  margin_31567 (fun _ => True) (fun _ => 0) (fun N => ⟨le_rfl, Real.log_natCast_nonneg N⟩)

#print axioms wFactor_bounds
#print axioms w31567_bounds
#print axioms margin_actual_31567
#print axioms margin_31567

end LeanLab.ChenExplicit.AT31567
