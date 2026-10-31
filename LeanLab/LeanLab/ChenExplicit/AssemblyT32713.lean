/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T1217Z-cloud42, unit U-6400, track T2.
A scripted port, gen/port32713_U6400.py, of AssemblyT32716.lean of PC U-1045, onto the α = 1/160000
constants of Section9A160.lean, plus the hand-written lemmas exp32713_sharp and alpha_admissible.
P0009 BJS 2022 Theorem 3 at exp(exp 32.713), the lab's corrected Section 9 with every numeric input PROVED.

Changes against the 32.716 chain: α₁ = α₂ = α₃ = 1/160000 = 6.25·10⁻⁶ in place of 10⁻⁵; the paper's
Theorems 44, 50, 51 allow any α meeting their N^α condition, and `alpha_admissible` checks the
arithmetic of that condition for every log N ≥ e^{32.713}. log log X₂ = 32.713; δ = 1.47694, just above
the ε₁ boundary δ* = 1.4769328 where 1.47694 · log x₁(X₂) = 48.31514 against log(3·5·…·59) = 48.31490;
ε₀ = 1.96·10⁻⁴; m(X₃) ≤ 6.93·10⁻¹⁰, proved in BJSm32713.lean, Python mpmath m ≈ 6.748·10⁻¹⁰ with
φ(ℓ) ≈ 1.7154·10⁻¹¹ and ν ℓ ≈ 147.323. Exact rational arithmetic on the bounds of At32713.margin_bP
gives a Lean-side slack of about 3.57·10⁻⁵ at g = 1.781.

Inputs, all PROVED: At32713.margin_bP and margin_aP; ε₁ = 1/57, ε₂ = 1/51 from At32713Eps.lean;
m(X₃) ≤ 6.93·10⁻¹⁰ from BJSm32713.lean; a(X₂) ≤ 10⁻¹⁸, c₄, c₄*, l, l*, l₁, l₁* ≤ 10⁻²⁰ from
BJSpX2At32713, BJSaX2At32713, BJSc2X2At32713, BJSl1X2At32713, the last with k_{α₂} at the new α;
e^γ, the twin prime constant, c̄ and the F(c) integral from GammaBounds, TwinCNumeric, BJSCbar and
FIntegral5.

`chen_32713` is CONDITIONAL ON BJS Theorems 44, 50, 51 at α = 1/160000 with their constants as
CORRECTED per FINDINGS F-0020, F-0021, F-0022, Theorem 51 at ε₀ = 1.96·10⁻⁴, for any split of the even
N into case (a) and case (b) and any factor w(N) ∈ [0, log N] of Theorem 44 (b). So: if the three
sieve theorems hold as corrected, every even N > exp(exp 32.713) has more than 2·10⁻⁴ U_N N / log² N
representations as a prime plus a number with at most two prime factors. The paper prints
exp(exp 32.7), which does not follow from its printed argument, FINDING F-0023. The lab's Python model
of the corrected argument at the smallest admissible α first closes near log log X₂ = 32.7100,
numerics/threshold_alphamin_U1045, so this Lean margin sits 0.003 above the model limit.
Chen's theorem itself is not in doubt; Goldbach is open.
-/
import LeanLab.ChenExplicit.AssemblyT
import LeanLab.ChenExplicit.At32713
import LeanLab.ChenExplicit.At32713Eps
import LeanLab.ChenExplicit.BJSm32713
import LeanLab.ChenExplicit.BJSc2X2At32713
import LeanLab.ChenExplicit.BJSl1X2At32713
import LeanLab.ChenExplicit.Section9Link
import LeanLab.ChenExplicit.Section9A160

open Real

noncomputable section
namespace LeanLab.ChenExplicit.AT32713

open LeanLab.ChenExplicit LeanLab.ChenExplicit.Section9A160
  LeanLab.ChenExplicit.At32713

/-- e^γ. -/
abbrev gE : ℝ := exp eulerMascheroniConstant
/-- log X₂ = e^{32.713}. -/
abbrev LX : ℝ := exp (32713 / 1000)

/-- ε₁, ε₂ at 32.713. -/
abbrev e1 : ℝ := BJSEm.eps At32713Eps.B1
abbrev e2 : ℝ := BJSEm.eps At32713Eps.B2
/-- m(X₃) at 32.713. -/
abbrev mm : ℝ := BJSm32713.mX3 BJSm32713.vS
/-- The X₂-only constants at 32.713. -/
abbrev aS : ℝ := BJSaX2At32713.aX2 gE twinC BJSc32713.c2term
abbrev c4S : ℝ := BJSp32713.c4 BJSp32713.nuS
abbrev l1S : ℝ := BJSl32713.l1 gE 106 BJSp32713.nuS
abbrev lS : ℝ := BJSp32713.l BJSp32713.nuS
abbrev c4a : ℝ := BJSp32713.c4 BJSp32713.nu
abbrev l1a : ℝ := BJSl32713.l1 gE 106 BJSp32713.nu
abbrev la : ℝ := BJSp32713.l BJSp32713.nu

open Classical in
/-- Theorem 44's corrected constant at X₂ = exp(exp 32.713). -/
def cA32713 (caseA : ℕ → Prop) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  if caseA N then cAa gE twinC c4a (Real.log N)
  else cAbP (32713 / 1000) gE twinC e1 aS c4S (w N) (Real.log N) LX

open Classical in
/-- Theorem 50's corrected constant at X₂ = exp(exp 32.713), C₁(ε) = 106. -/
def cQ32713 (caseA : ℕ → Prop) (N : ℕ) : ℝ :=
  if caseA N then cQa gE twinC l1a la (Real.log N) LX
  else cQb gE twinC e1 l1S lS (Real.log N) LX

/-- Theorem 51's corrected constant at X₃ = X₂^{1/8}, ε₀ = 1.96·10⁻⁴. -/
def cB32713 (N : ℕ) : ℝ := cBP ee0 gE twinC e2 BJS.cbar mm (Real.log N)

lemma LX_ge : (10 : ℝ) ^ 14 ≤ LX := by
  have := BJSm32713.exp32713_ge; unfold LX; linarith

lemma hT : (0.65 : ℝ) ≤ twinC := by have := twinC_ge_065; norm_num at this ⊢; linarith

lemma hcb : 0 ≤ BJS.cbar ∧ BJS.cbar ≤ 0.363084 := by
  have h1 := BJS.cbar_lt; have h2 := BJS.cbar_gt
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

lemma he1 : 0 ≤ e1 ∧ e1 ≤ 1 / 57 := by
  unfold e1; rw [At32713Eps.eps1_32713]; norm_num

lemma he2 : 0 ≤ e2 ∧ e2 ≤ 1 / 51 := by
  unfold e2; rw [At32713Eps.eps2_32713]; norm_num

lemma hI : ∫ t in (2 : ℝ)..(ccP (32713 / 1000) LX - 1), log (t - 1) / t ≤ 0.14725 := by
  obtain ⟨c1, c2⟩ := cc_boundsP LX LX_ge
  exact (FInt.Ic_le_I3 _ (by linarith) (by linarith)).trans FInt5.I3_le5

lemma g0 : 0 ≤ gE := (exp_pos _).le

lemma ha : 0 ≤ aS ∧ aS ≤ 1 / 10 ^ 18 := by
  obtain ⟨c0, c1⟩ := BJSc32713.c2term_bounds
  have h1 := BJSaX2At32713.aX2_le g0 Section9.g_le hT c1
  have h0 := BJSaX2At32713.aX2_nonneg g0 Section9.g_le hT c0
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4S : 0 ≤ c4S ∧ c4S ≤ 1 / 10 ^ 20 := by
  have g := BJSp32713.nuS_good
  have h1 := BJSp32713.c4_le g; have h0 := BJSp32713.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hlS : 0 ≤ lS ∧ lS ≤ 1 / 10 ^ 20 := by
  have g := BJSp32713.nuS_good
  have h1 := BJSp32713.l_le g; have h0 := BJSp32713.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hc4a : 0 ≤ c4a ∧ c4a ≤ 1 / 10 ^ 20 := by
  have g := BJSp32713.nu_good
  have h1 := BJSp32713.c4_le g; have h0 := BJSp32713.c4_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hla : 0 ≤ la ∧ la ≤ 1 / 10 ^ 20 := by
  have g := BJSp32713.nu_good
  have h1 := BJSp32713.l_le g; have h0 := BJSp32713.l_nonneg g
  exact ⟨h0, by norm_num at h1 ⊢; linarith⟩

lemma hl1S : 0 ≤ l1S ∧ l1S ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl32713.l1_bounds (C1 := 106) g0 Section9.g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp32713.nuS_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

lemma hl1a : 0 ≤ l1a ∧ l1a ≤ 1 / 10 ^ 20 := by
  obtain ⟨a, b⟩ := BJSl32713.l1_bounds (C1 := 106) g0 Section9.g_le (by norm_num : (0:ℝ) ≤ 106)
    (by norm_num : (106:ℝ) ≤ 1e6) BJSp32713.nu_good
  exact ⟨a, by norm_num at b ⊢; linarith⟩

/-- `e^{32.713} ≥ 1.6029·10¹⁴`, by the quartic Taylor bound for `e^{0.713}`. -/
lemma exp32713_sharp : (1.6029 * 10 ^ 14 : ℝ) ≤ exp (32713 / 1000) := by
  have e : exp (32713 / 1000 : ℝ) = exp 1 ^ 32 * exp (713 / 1000) := by
    rw [exp_one_pow, ← exp_add]; norm_num
  have h1 : (2.7182818283 : ℝ) ^ 32 ≤ exp 1 ^ 32 :=
    pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 32
  have h2 : (2.03 : ℝ) ≤ exp (713 / 1000) := by
    have h := Real.sum_le_exp_of_nonneg (x := (713 / 1000 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  rw [e]
  have h3 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have h4 : (1.6029 * 10 ^ 14 : ℝ) ≤ (2.7182818283 : ℝ) ^ 32 * 2.03 := by norm_num
  linarith

/-- **α = 1/160000 is admissible in Theorems 44, 50, 51 above exp(exp 32.713)**, the arithmetic half:
for every `log N = L ≥ e^{32.713}`, `α L - 12.5 log L ≥ 10⁹(1 + 10⁻⁷)`. The theorems need
`N^α/(log¹⁰ x₁(N) log^{5/2} N) ≥ exp(u₀(1 + 9·10⁻⁷/log u₀))` with `u₀ = 10⁹`, as read by U-1045;
`log x₁(N) ≤ log N` and `9·10⁻⁷/log 10⁹ < 10⁻⁷`, so this inequality implies that condition.
The reading of the condition from the paper is not checked by Lean. -/
lemma alpha_admissible (L : ℝ) (hL : exp (32713 / 1000) ≤ L) :
    (10 : ℝ) ^ 9 * (1 + 1 / 10 ^ 7) + 12.5 * Real.log L ≤ Section9A160.α * L := by
  have hE := exp32713_sharp
  have hE0 : 0 < exp (32713 / 1000 : ℝ) := exp_pos _
  have hL0 : 0 < L := lt_of_lt_of_le hE0 hL
  have hlog : Real.log L ≤ 32713 / 1000 + (L / exp (32713 / 1000) - 1) := by
    have h := Real.log_le_sub_one_of_pos (x := L / exp (32713 / 1000)) (div_pos hL0 hE0)
    rw [Real.log_div hL0.ne' hE0.ne', Real.log_exp] at h; linarith
  set t := L / exp (32713 / 1000) with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hE0]; linarith
  have hLt : L = t * exp (32713 / 1000) := by rw [ht]; field_simp
  have h1 : (1 / 160000 : ℝ) * (t * (1.6029 * 10 ^ 14)) ≤ 1 / 160000 * L := by
    rw [hLt]; gcongr
  unfold Section9A160.α
  nlinarith

/-- **The corrected Section 9 margin holds for every even N > exp(exp 32.713)**, PROVED. -/
theorem margin_32713 (caseA : ℕ → Prop) (w : ℕ → ℝ)
    (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N) :
    MarginAt (32713 / 1000) (cA32713 caseA w) (cQ32713 caseA) cB32713 := by
  intro N _ hN
  have hpos : (0 : ℝ) < N := lt_trans (exp_pos _) hN
  have hL : LX ≤ Real.log N := ((Real.lt_log_iff_exp_lt hpos).mpr hN).le
  unfold cA32713 cQ32713 cB32713
  by_cases hc : caseA N
  · simp only [hc, ite_true]
    have := margin_aP gE twinC e2 BJS.cbar mm c4a l1a la (Real.log N) LX Section9.g_ge Section9.g_le hT he2 hcb
      BJSm32713.mX3_vS_bounds hc4a hl1a hla LX_ge hL
    linarith
  · simp only [hc, ite_false]
    exact margin_bP gE twinC e1 e2 BJS.cbar mm aS c4S (w N) l1S lS (Real.log N) LX Section9.g_ge Section9.g_le hT
      he1 he2 hcb BJSm32713.mX3_vS_bounds ha hc4S (hw N) hl1S hlS LX_ge hL hI

/-- **BJS Theorem 3 at exp(exp 32.713), CONDITIONAL ON Theorems 44, 50, 51 as corrected.** -/
theorem chen_32713 (caseA : ℕ → Prop) (w : ℕ → ℝ) (hw : ∀ N : ℕ, 0 ≤ w N ∧ w N ≤ Real.log N)
    (hA : Thm44At (32713 / 1000) (cA32713 caseA w)) (hQ : Thm50At (32713 / 1000) (cQ32713 caseA))
    (hB : Thm51At (32713 / 1000) cB32713) : BJS3At (32713 / 1000) :=
  BJS3At_of_sieveBounds _ (by norm_num) _ _ _ hA hQ hB (margin_32713 caseA w hw)

#print axioms alpha_admissible
#print axioms margin_32713
#print axioms chen_32713
#print axioms BJSm32713.mX3_vS_bounds

end LeanLab.ChenExplicit.AT32713
