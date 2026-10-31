/-
Proposition 8.1 of P0029 Bhowmik, Grimmelt, The exceptional set of the Goldbach problem,
arXiv 2607.27282v2, as PRINTED on pages 30 and 31, read from Steve's copy copies/P0029.pdf with
pdftotext and the 150 dpi page images, unit U-1331, track T1. Replaces nothing: the U-1322 module
BG2026Prop81MPR.lean is kept as it is.

Line by line check, page numbers of the PDF:
* `Prop81` of U-1322 is NOT the printed Proposition 8.1. The print, page 30 bottom and page 31
  top, (8.3): fix `2/5 ≤ ϑ < 4/9`, `R = X^ϑ`, `r̃ ≤ R`, `0 < δ̃ < h/L`, `L = log X`, `h = h(ϑ)`.
  There are `c' = c'(ϑ) > 0`, `ε₀ = ε₀(ϑ) > 0` such that for every `ε > 0` and all but
  `O_ε(X^{3/5+ε})` even `N ∈ [X/2, X]`, every even `N`, not only multiples of `r̃`,
  `r₂(N) = 𝔖(N) N + 𝔖(χ̃, χ̃, N) B(β̃, β̃) N^{2β̃-1} + O(𝔖(N) X (δ̃L)^{c'}) + O(𝔖(N) N r̃/φ(r̃)²) + O(X^{1-ε₀})`,
  implied constants depending only on `ϑ`. `Prop81` is instead the page 32 consequence at the
  multiples of `r̃`, with `b`, `E` and `δ/4`. Faithful form here: `Prop81Print`.
* `MajorPart81` of U-1322 lets the major arcs have `X^{1-ϑ+}` exceptions. The print, page 31
  Sketch, has the major arc formula for EVERY `N`, error `O(𝔖(N) X e^{-cH}) + O(X^{1-ε₀})`, and puts
  all exceptions on the minor arcs, `O_ε(X^{1+ε}/R + X^{3/5+ε})`, Lemma 4.2. Faithful form here:
  `MajorFormula81`.
* `Theorem82`, BhowmikGrimmelt2026.lean: MATCH with Theorem 8.2, page 31, `A > 5/2`, `c = c(δ)`,
  `r₀ = r₀(A, δ)`, `X = r̃^A`, (8.4) with `X^{3/5}` exceptions among even `N ∈ [X/2, X]`, `r̃ ∣ N`.

The quantifier gap, page 31 Sketch, last paragraph: `ε₀ = ε₀(ϑ)` is fixed before `ε`, but the
minor arc count by Chebyshev at threshold `X^{1-ε₀}` from Lemma 4.2, page 16, is
`(X³/R + X^{13/5}) (log X)⁵ / X^{2-2ε₀} = (X^{1+2ε₀}/R + X^{3/5+2ε₀}) (log X)⁵`, not `O_ε(X^{3/5+ε})` for
`ε < 2ε₀`; the text says "after decreasing ε₀ if necessary", which makes `ε₀` depend on `ε`.
`Prop81PrintFix` puts `ε₀` after `ε`; Theorem 8.2 uses one fixed `ε`, page 32, so it is unaffected.

Q-1322a, Lemma 7.3, pages 26 and 27: the arcs of Lemma 7.3 are `𝔐(R)`, `𝔪(R)` of (4.3), width
`R/(qN)`; `η` enters only through `T_q = ηNq/R` in the weight `b_R`, Lemma 7.2. On `𝔐(R)` the term
`T_q |β| ≤ η`, `arc_inside_weight`, and the error there is the `η⁴ X³ log X` term; on `𝔪(R)`,
`T_q |α - a/q| > η`, `minor_outside_weight`, and only the sup on `𝔪(R)` is used, where MPR gives
`B ≥ R`, `minorArcSup_of_MPR`. So `X^{-2/5}` becomes `X^{2·19/24-2} = X^{-5/12}` with `X^{o(1)}` for
`(log X)⁵`: `lemma73_mpr_exponent`, `lemma79_mpr`.

AI wrote this Lean code, Claude, 2026-10-21. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.BG2026Prop81MPR

namespace LeanLab.ExceptionalSet.BG2026
open Real Finset ArithmeticFunction

noncomputable section

/-! ### The printed statements -/

/-- The beta factor `B(ϱ₁, ϱ₂) = Γ(ϱ₁) Γ(ϱ₂) / Γ(ϱ₁ + ϱ₂)`, page 30, at real arguments. -/
def betaFactor (a b : ℝ) : ℝ := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

/-- Even `N ∈ [X/2, X]`. -/
def evenWin (X : ℝ) : Finset ℕ := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter Even

/-- The main terms of (8.3), page 31: `𝔖(N) N + 𝔖(χ̃, χ̃, N) B(β̃, β̃) N^{2β̃-1}`, `β̃ = 1 - δ̃`,
with `GS r χ N` standing for Pintz's generalised singular series `𝔖(χ̃, χ̃, N)` of (6.4). -/
def main83 (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (δt : ℝ) (N : ℕ) : ℝ :=
  Sing N * N + GS r χ N * betaFactor (1 - δt) (1 - δt) * (N : ℝ) ^ (2 * (1 - δt) - 1)

/-- The error terms of (8.3) without their constant: `𝔖(N) X (δ̃L)^{c'} + 𝔖(N) N r̃/φ(r̃)² + X^{1-ε₀}`. -/
def err83 (c' ε0 X : ℝ) (r : ℕ) (δt : ℝ) (N : ℕ) : ℝ :=
  Sing N * X * (δt * Real.log X) ^ c' + Sing N * N * (r / (Nat.totient r : ℝ) ^ 2) + X ^ (1 - ε0)

/-- The Siegel zero setting of Section 8, page 30: `χ̃` primitive real mod `r̃ ≤ X^ϑ` and
`L(1 - δ̃, χ̃) = 0` with `0 < δ̃ < h / log X`. -/
def Siegel81 (ϑ h X : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δt : ℝ) : Prop :=
  (r : ℝ) ≤ X ^ ϑ ∧ χ.IsPrimitive ∧ (∀ a, (χ a).im = 0) ∧ 0 < δt ∧ δt < h / Real.log X ∧
    DirichletCharacter.LFunction χ ((1 - δt : ℝ) : ℂ) = 0

/-- Proposition 8.1 AS PRINTED, pages 30 and 31, at level `ϑ`, exception exponent `σ` (`3/5` in the
print): `h`, `c'`, `ε₀` and the implied constant `C` depend on `ϑ` only, then for every `ε > 0` a
constant `K`, and all but `K X^{σ+ε}` even `N ∈ [X/2, X]` satisfy (8.3). -/
def Prop81Print (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) (ϑ σ : ℝ) : Prop :=
  ∃ h c' ε0 C : ℝ, 0 < h ∧ 0 < c' ∧ 0 < ε0 ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
    ∀ X : ℝ, 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δt : ℝ),
    Siegel81 ϑ h X r χ δt → ∃ B : Finset ℕ, (B.card : ℝ) ≤ K * X ^ (σ + ε) ∧
      ∀ N ∈ evenWin X, N ∉ B → |r2 N - main83 GS r χ δt N| ≤ C * err83 c' ε0 X r δt N

/-- Proposition 8.1 with the quantifier order its proof supports: `ε₀` and `C` chosen after `ε`. -/
def Prop81PrintFix (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) (ϑ σ : ℝ) : Prop :=
  ∃ h c' : ℝ, 0 < h ∧ 0 < c' ∧ ∀ ε : ℝ, 0 < ε → ∃ ε0 C K : ℝ, 0 < ε0 ∧ 0 < C ∧ 0 < K ∧
    ∀ X : ℝ, 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δt : ℝ),
    Siegel81 ϑ h X r χ δt → ∃ B : Finset ℕ, (B.card : ℝ) ≤ K * X ^ (σ + ε) ∧
      ∀ N ∈ evenWin X, N ∉ B → |r2 N - main83 GS r χ δt N| ≤ C * err83 c' ε0 X r δt N

/-- The major arc formula of the page 31 Sketch, after the cutoff `H = H₁` of (8.2), CITED from
Pintz [20, Thm 1]: for EVERY even `N ∈ [X/2, X]`, no exceptions,
`|r_𝔐(N) - main| ≤ C (𝔖(N) X (δ̃L)^{c'} + 𝔖(N) N r̃/φ(r̃)² + X^{1-ε₀})`. -/
def MajorFormula81 (GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ) (ϑ : ℝ) (rMaj : ℝ → ℕ → ℝ) :
    Prop :=
  ∃ h c' ε0 C : ℝ, 0 < h ∧ 0 < c' ∧ 0 < ε0 ∧ 0 < C ∧
    ∀ X : ℝ, 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δt : ℝ),
    Siegel81 ϑ h X r χ δt →
      ∀ N ∈ evenWin X, |rMaj X N - main83 GS r χ δt N| ≤ C * err83 c' ε0 X r δt N

/-- The printed order implies the fixed order. PROVED. -/
theorem prop81PrintFix_of_print {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ σ : ℝ}
    (h : Prop81Print GS ϑ σ) : Prop81PrintFix GS ϑ σ := by
  obtain ⟨hh, c', ε0, C, hh0, hc', hε0, hC, hK⟩ := h
  refine ⟨hh, c', hh0, hc', fun ε hε => ?_⟩
  obtain ⟨K, hK0, hb⟩ := hK ε hε
  exact ⟨ε0, C, K, hε0, hC, hK0, hb⟩

/-! ### Proposition 8.1 from the printed halves -/

theorem err83_nonneg {c' ε0 X : ℝ} (hX : 0 ≤ X) (r : ℕ) {δt : ℝ} (hδ : 0 ≤ δt) (hL : 0 ≤ Real.log X)
    (N : ℕ) : 0 ≤ err83 c' ε0 X r δt N := by
  unfold err83
  have := Sing_pos N
  have h1 : 0 ≤ (δt * Real.log X) ^ c' := Real.rpow_nonneg (mul_nonneg hδ hL) _
  positivity

/-- Minor arc count at threshold `X^{1-e}`: at most `K X^{m + 2e + ε'}` indices, `m = max(1-ϑ, 2κ-1)`. -/
theorem minor_count_threshold {ϑ κ : ℝ} {rMin : ℝ → ℕ → ℝ} (hm : MinorL2 ϑ κ rMin) {e ε' : ℝ}
    (hε' : 0 < ε') : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      (((evenWin X).filter (fun N => X ^ (1 - e) < |rMin X N|)).card : ℝ) ≤
        K * X ^ (max (1 - ϑ) (2 * κ - 1) + 2 * e + ε') := by
  obtain ⟨C, hC, hL2⟩ := hm ε' hε'
  refine ⟨2 * C, by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have ht : 0 < X ^ (1 - e) := by positivity
  have hsub : (evenWin X).filter (fun N => X ^ (1 - e) < |rMin X N|) ⊆
      (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun N => X ^ (1 - e) < |rMin X N|) := by
    intro N hN
    simp only [evenWin, mem_filter] at hN ⊢
    exact ⟨hN.1.1, hN.2⟩
  have hcard := card_large_le (Icc ⌈X / 2⌉₊ ⌊X⌋₊) (rMin X) ht (hL2 X hX)
  have h1 := (Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)
  refine h1.trans (hcard.trans ?_)
  set m := max (1 - ϑ) (2 * κ - 1)
  have hsq : (X ^ (1 - e)) ^ 2 = X ^ (2 - 2 * e) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num; ring_nf
  rw [hsq, div_le_iff₀ (by positivity)]
  have e1 : X ^ ε' * X ^ (3 - ϑ) ≤ X ^ (m + 2 * e + ε') * X ^ (2 - 2 * e) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX
      (by have := le_max_left (1 - ϑ) (2 * κ - 1); linarith)
  have e2 : X ^ ε' * X ^ (2 * κ + 1) ≤ X ^ (m + 2 * e + ε') * X ^ (2 - 2 * e) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX
      (by have := le_max_right (1 - ϑ) (2 * κ - 1); linarith)
  calc C * X ^ ε' * (X ^ (3 - ϑ) + X ^ (2 * κ + 1))
      = C * (X ^ ε' * X ^ (3 - ϑ) + X ^ ε' * X ^ (2 * κ + 1)) := by ring
    _ ≤ C * (2 * (X ^ (m + 2 * e + ε') * X ^ (2 - 2 * e))) := by
        apply mul_le_mul_of_nonneg_left _ hC.le; linarith
    _ = 2 * C * X ^ (m + 2 * e + ε') * X ^ (2 - 2 * e) := by ring

/-- Proposition 8.1, fixed quantifier order, with exception exponent `σ ≥ max(1-ϑ, 2κ-1)`, from
the printed major arc formula and the minor arc mean square. CONDITIONAL ON `MajorFormula81 GS ϑ`
and `MinorL2 ϑ κ`, for any split `r₂ = r_𝔐 + r_𝔪`. -/
theorem prop81PrintFix_of_parts {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ κ σ : ℝ}
    {rMaj rMin : ℝ → ℕ → ℝ} (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N)
    (hσ : max (1 - ϑ) (2 * κ - 1) ≤ σ)
    (hM : MajorFormula81 GS ϑ rMaj) (hm : MinorL2 ϑ κ rMin) : Prop81PrintFix GS ϑ σ := by
  obtain ⟨h, c', ε0, C, hh, hc', hε0, hC, hMaj⟩ := hM
  refine ⟨h, c', hh, hc', fun ε hε => ?_⟩
  set e := min ε0 (ε / 4) with he
  have he0 : 0 < e := lt_min hε0 (by linarith)
  have hee : e ≤ ε / 4 := min_le_right _ _
  have heε0 : e ≤ ε0 := min_le_left _ _
  obtain ⟨K, hK, hcnt⟩ := minor_count_threshold hm (e := e) (ε' := ε / 2) (by linarith)
  refine ⟨e, C + 1, K, he0, by linarith, hK, fun X hX r _ χ δt hS => ?_⟩
  have hX1 : 1 ≤ X := by linarith
  set B := (evenWin X).filter (fun N => X ^ (1 - e) < |rMin X N|)
  refine ⟨B, ?_, fun N hN hNB => ?_⟩
  · refine (hcnt X hX1).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  · have hmin : |rMin X N| ≤ X ^ (1 - e) := by
      by_contra hc; push Not at hc
      exact hNB (mem_filter.mpr ⟨hN, hc⟩)
    have hmaj := hMaj X hX r χ δt hS N hN
    have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hpow : X ^ (1 - ε0) ≤ X ^ (1 - e) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hE0 := err83_nonneg (c' := c') (ε0 := ε0) (by linarith) r hS.2.2.2.1.le hL N
    have hEE : err83 c' ε0 X r δt N ≤ err83 c' e X r δt N := by
      unfold err83; linarith
    have hE1 : X ^ (1 - e) ≤ err83 c' e X r δt N := by
      unfold err83
      have hs := Sing_pos N
      have h1 : 0 ≤ (δt * Real.log X) ^ c' := Real.rpow_nonneg (mul_nonneg hS.2.2.2.1.le hL) _
      have h2 : 0 ≤ Sing N * X * (δt * Real.log X) ^ c' := by positivity
      have h3 : 0 ≤ Sing N * N * (r / (Nat.totient r : ℝ) ^ 2) := by positivity
      linarith
    rw [hsplit X N]
    calc |rMaj X N + rMin X N - main83 GS r χ δt N|
        = |(rMaj X N - main83 GS r χ δt N) + rMin X N| := by ring_nf
      _ ≤ |rMaj X N - main83 GS r χ δt N| + |rMin X N| := abs_add_le _ _
      _ ≤ C * err83 c' e X r δt N + err83 c' e X r δt N := by
          have := mul_le_mul_of_nonneg_left hEE hC.le
          linarith
      _ = (C + 1) * err83 c' e X r δt N := by ring

/-- Proposition 8.1 as the print intends it at `ϑ ∈ [2/5, 4/9)`, exceptions `X^{3/5+ε}`, Vinogradov's
`κ = 4/5`. CONDITIONAL ON `MajorFormula81 GS ϑ` and `MinorL2 ϑ (4/5)`. -/
theorem prop81PrintFix_vinogradov {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ : ℝ}
    {rMaj rMin : ℝ → ℕ → ℝ} (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N) (hϑ : 2 / 5 ≤ ϑ)
    (hM : MajorFormula81 GS ϑ rMaj) (hm : MinorL2 ϑ (4 / 5) rMin) :
    Prop81PrintFix GS ϑ (3 / 5) :=
  prop81PrintFix_of_parts hsplit (by rw [max_le_iff]; constructor <;> linarith) hM hm

/-- Proposition 8.1 at `ϑ ∈ [5/12, 4/9)` with MPR's `κ = 19/24`, exceptions `X^{7/12+ε}`.
CONDITIONAL ON `MajorFormula81 GS ϑ` and `MinorL2 ϑ (19/24)`. -/
theorem prop81PrintFix_mpr {GS : (r : ℕ) → DirichletCharacter ℂ r → ℕ → ℝ} {ϑ : ℝ}
    {rMaj rMin : ℝ → ℕ → ℝ} (hsplit : ∀ X N, r2 N = rMaj X N + rMin X N) (hϑ : 5 / 12 ≤ ϑ)
    (hM : MajorFormula81 GS ϑ rMaj) (hm : MinorL2 ϑ (19 / 24) rMin) :
    Prop81PrintFix GS ϑ (7 / 12) :=
  prop81PrintFix_of_parts hsplit (by rw [max_le_iff]; constructor <;> linarith) hM hm

/-! ### The quantifier gap, exponent arithmetic -/

/-- Chebyshev at threshold `X^{1-ε₀}` on Lemma 4.2's bound `X^{13/5}`, page 16, leaves exponent
`3/5 + 2ε₀`, and on `X³/R`, `R = X^ϑ`, exponent `1 - ϑ + 2ε₀`. -/
theorem chebyshev_exponents (ϑ ε0 : ℝ) :
    13 / 5 - 2 * (1 - ε0) = 3 / 5 + 2 * ε0 ∧ (3 - ϑ) - 2 * (1 - ε0) = 1 - ϑ + 2 * ε0 := by
  constructor <;> ring

/-- A larger power is not `O` of a smaller one: for `a > b` no `K` has `X^a ≤ K X^b` for all `X ≥ 1`.
So `X^{3/5+2ε₀}` is not `O(X^{3/5+ε})` when `ε < 2ε₀`. PROVED. -/
theorem not_rpow_isBigO {a b : ℝ} (hab : b < a) :
    ¬ ∃ K : ℝ, ∀ X : ℝ, 1 ≤ X → X ^ a ≤ K * X ^ b := by
  rintro ⟨K, hK⟩
  set X := max 2 ((|K| + 1) ^ (a - b)⁻¹) with hXd
  have hX1 : 1 ≤ X := le_trans (by norm_num) (le_max_left _ _)
  have hX0 : 0 < X := by linarith
  have hab' : 0 < a - b := by linarith
  have hKX : |K| + 1 ≤ X ^ (a - b) := by
    have h1 : (|K| + 1) ^ (a - b)⁻¹ ≤ X := le_max_right _ _
    have h2 := Real.rpow_le_rpow (by positivity) h1 hab'.le
    rwa [Real.rpow_inv_rpow (by positivity) hab'.ne'] at h2
  have hsplit : X ^ a = X ^ (a - b) * X ^ b := by
    rw [← Real.rpow_add hX0]; ring_nf
  have hb : 0 < X ^ b := by positivity
  have := hK X hX1
  rw [hsplit] at this
  have hK' : K ≤ |K| := le_abs_self K
  nlinarith

/-- The gap at the printed `ε₀`: `ε = ε₀` already has `3/5 + ε < 3/5 + 2ε₀`. -/
theorem gap_instance {ε0 : ℝ} (h : 0 < ε0) : (3 / 5 : ℝ) + ε0 < 3 / 5 + 2 * ε0 := by linarith

/-! ### Q-1322a: Lemma 7.3 with the MPR minor arc bound -/

/-- Lemma 7.2 proof, page 26: on the arc `|β| ≤ R/(qN)` of `𝔐(R)`, `T_q |β| ≤ η` for `T_q = ηNq/R`.
So the points between the shrunk weight scale and the Section 4 arc lie in `𝔐(R)` and are paid by
the `η⁴` term, not by the minor arc bound. PROVED. -/
theorem arc_inside_weight {η N q R β : ℝ} (hη : 0 < η) (hN : 0 < N) (hq : 0 < q) (hR : 0 < R)
    (hβ : |β| ≤ R / (q * N)) : η * N * q / R * |β| ≤ η := by
  have hk : 0 ≤ η * N * q / R := by positivity
  calc η * N * q / R * |β| ≤ η * N * q / R * (R / (q * N)) := mul_le_mul_of_nonneg_left hβ hk
    _ = η := by field_simp

/-- Lemma 7.2 proof, page 26: on `𝔪(R)`, `|α - a/q| > R/(qN)` for `q ≤ R`, so `T_q |α - a/q| > η`. -/
theorem minor_outside_weight {η N q R β : ℝ} (hη : 0 < η) (hN : 0 < N) (hq : 0 < q) (hR : 0 < R)
    (hβ : R / (q * N) < |β|) : η < η * N * q / R * |β| := by
  have hk : 0 < η * N * q / R := by positivity
  calc η = η * N * q / R * (R / (q * N)) := by field_simp
    _ < η * N * q / R * |β| := mul_lt_mul_of_pos_left hβ hk

/-- Smooth weight transfer for MPR, partial summation over `t ∈ [N/5, N]`: a minor arc point of
level `N` has `q t |β| > R/5` at every such length `t`, so MPR's `B ≥ R/5`. PROVED. -/
theorem minor_rescale {N q R β t : ℝ} (hN : 0 < N) (hq : 0 < q)
    (hβ : R / (q * N) < |β|) (ht : N / 5 ≤ t) : R / 5 < q * t * |β| := by
  have h1 : R < q * N * |β| := by rwa [div_lt_iff₀ (by positivity), mul_comm] at hβ
  have hb : 0 ≤ |β| := abs_nonneg β
  nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg hq.le hb)]

/-- `η = R^{-1/4}` gives `η⁴ = R^{-1}`, page 27. -/
theorem eta_fourth {R : ℝ} (hR : 0 < R) : (R ^ (-(1 / 4) : ℝ)) ^ (4 : ℕ) = R ^ (-1 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]; norm_num

/-- The minor arc factor of (7.8): `sup² ∫|S|² / X³` with `sup = X^κ` is `X^{2κ-2}`; Vinogradov
`κ = 4/5` gives `-2/5`, the printed exponent; MPR `κ = 19/24` gives `-5/12`, smaller. -/
theorem lemma73_mpr_exponent :
    2 * (4 / 5 : ℝ) + 1 - 3 = -(2 / 5) ∧ 2 * (19 / 24 : ℝ) + 1 - 3 = -(5 / 12) ∧
      -(5 / 12 : ℝ) < -(2 / 5) := by norm_num

/-- (7.9) with MPR at `R = X^ϑ`, `η = R^{-1/4}`: `X³ (R^{-1} + X^{-5/12} + η⁴) = 2 X^{3-ϑ} + X^{31/12}`.
At `ϑ = 5/12` both exponents are `31/12`. PROVED. -/
theorem lemma79_mpr {X ϑ : ℝ} (hX : 0 < X) :
    X ^ (3 : ℝ) * ((X ^ ϑ) ^ (-1 : ℝ) + X ^ (-(5 / 12) : ℝ) + ((X ^ ϑ) ^ (-(1 / 4) : ℝ)) ^ (4 : ℕ)) =
      2 * X ^ (3 - ϑ) + X ^ (31 / 12 : ℝ) := by
  have hR : 0 < X ^ ϑ := by positivity
  rw [eta_fourth hR, ← Real.rpow_mul hX.le]
  have a1 : X ^ (3 : ℝ) * X ^ (ϑ * -1) = X ^ (3 - ϑ) := by
    rw [← Real.rpow_add hX]; ring_nf
  have a2 : X ^ (3 : ℝ) * X ^ (-(5 / 12) : ℝ) = X ^ (31 / 12 : ℝ) := by
    rw [← Real.rpow_add hX]; norm_num
  linear_combination 2 * a1 + a2

/-- `ϑ = 5/12` lies in the printed range `2/5 ≤ ϑ < 4/9` of page 30. -/
theorem five_twelfths_in_range : (2 / 5 : ℝ) ≤ 5 / 12 ∧ (5 / 12 : ℝ) < 4 / 9 := by norm_num

/-! ### Vacuity tests -/

/-- The split hypothesis holds with `r_𝔐 = r₂`, `r_𝔪 = 0`, and then `MinorL2` holds, `vacuity_minorL2`. -/
theorem vacuity_split : (∀ X N, r2 N = (fun _ N => r2 N : ℝ → ℕ → ℝ) X N + (fun _ _ => (0 : ℝ)) X N)
    ∧ MinorL2 (5 / 12) (19 / 24) (fun _ _ => 0) :=
  ⟨fun _ _ => by simp, vacuity_minorL2 _ _⟩

/-- `Siegel81` instance shape: the window `evenWin 4` contains `2` and `4`. -/
theorem vacuity_evenWin : 2 ∈ evenWin 4 ∧ 4 ∈ evenWin 4 := by
  refine ⟨?_, ?_⟩ <;> simp only [evenWin, mem_filter, mem_Icc] <;> refine ⟨⟨?_, ?_⟩, by decide⟩ <;>
    norm_num [Nat.ceil_le, Nat.le_floor_iff]

end

end LeanLab.ExceptionalSet.BG2026
