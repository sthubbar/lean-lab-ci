/-
P0068 Zhan 1991, Theorem 2, split into cited LEAF steps. Burst 20261122.
Source: papers/Zhan1991.pdf, journal pages 261 to 269, pdf pages 3 to 11, read from page images
rendered at 110 and 220 dpi. Every LEAF below is a step of Zhan's proof, with page and display.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Readings: `≪` is `∃ K N₀, ∀ N ≥ N₀, ‖·‖ ≤ K · bound`; `L = log N`; `χ₀` is `1` in
`DirichletCharacter ℂ q`. Constants `c₁, c₂, c₃` are chosen in the order the paper chooses them:
`c₁` large, then `c₂` large in terms of `c₁` and `B`, then `c₃` large; this is the order behind
"we may take c₂ ≥ c₁ + 1", "c₂ ≥ 2B + 1" and "if c₃ is sufficiently large", pages 263 to 269.
-/
import LeanLab.Zhan1991.Theorems235
import LeanLab.PNTPort.Vinogradov.Final

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-! ### Definitions, each cited -/

/-- The twisted sum of display (3.1), page 263: `Σ_{N-A<n≤N} Λ(n) χ(n) e(nλ)`. -/
def Schi {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℝ) (N : ℕ) (A : ℝ) : ℂ :=
  ∑ n ∈ shortWin N A, (Λ n : ℂ) * χ n * ee (n * lam)

/-- Estimate (1.3), `S(α; N, A) ≪ A L^{-B}`, with fixed constants `c₁, c₂, K, N₀`, under the
hypotheses of Theorem 2, page 260, on the range `lo N ≤ A ≤ hi N`. -/
def Est13 (B c1 c2 K N₀ : ℝ) (lo hi : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ), N₀ ≤ N → lo N ≤ A → A ≤ hi N →
    Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam → Real.log N ^ c2 ≤ q →
    ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B)

/-- The hypotheses of Theorem 2, page 260, after the reduction to `A ≤ N^{2/3}` of pages 262
and 263, with `α` replaced by its data `q, λ`: `N^{3/5} L^{c₃} ≤ A ≤ N^{2/3}`,
`L^{c₂} ≤ q ≤ τ`, `|λ| ≤ 1/(qτ)`, `τ = A² N⁻¹ L^{-c₁}`, condition (1.2). -/
def Hyp2 (c1 c2 c3 : ℝ) (N : ℕ) (A lam : ℝ) (q : ℕ) : Prop :=
  (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3 ≤ A ∧ A ≤ (N : ℝ) ^ (2 / 3 : ℝ) ∧ 1 ≤ q ∧
    Real.log N ^ c2 ≤ q ∧ (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) ∧
    |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))

/-- `M_X(s) = Σ_{n≤X} μ(n) n^{-s}` of the Heath-Brown identity, page 263, as an arithmetic
function. -/
def muTrunc (X : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ X then (μ n : ℝ) else 0, by simp⟩

/-- The coefficients `a_j(n)` of page 263: `log n` for `j = 1`, `1` for `1 < j ≤ 10`,
`μ(n)` for `10 < j ≤ 20`. -/
def aj (j n : ℕ) : ℂ :=
  if j = 1 then (Real.log n : ℂ) else if j ≤ 10 then 1 else (μ n : ℂ)

/-- The dyadic range `I_j = (N_j, 2N_j]` of display (3.5), page 264, cut to positive integers. -/
def dyad (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun n => x < n)

/-- `f_j(s, χ) = Σ_{n ∈ I_j} a_j(n) χ(n) n^{-s}`, display (3.6), page 264. -/
def fj {q : ℕ} (j : ℕ) (x : ℝ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ dyad x, aj j n * χ n * (n : ℂ) ^ (-s)

/-- `F(s, χ) = Π_{j=1}^{20} f_j(s, χ)`, display (3.6), page 264; `Nv j` is `N_{j+1}`. -/
def Fprod {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ j : Fin 20, fj (j.val + 1) (Nv j) χ s

/-- Condition (3.5), page 264: `N ≪ Π N_j ≪ N` and `N_j ≤ X = N^{1/10}` for `11 ≤ j ≤ 20`.
The implied constants are read as `2^{-21}` and `1`, which is what `N - A < n₁⋯n₂₀ ≤ N`,
`A ≤ N/2` and `n_j ∈ (N_j, 2N_j]` give. -/
def Cond35 (N : ℕ) (Nv : Fin 20 → ℝ) : Prop :=
  (∀ j, (1 / 2 : ℝ) ≤ Nv j) ∧ (N : ℝ) / 2 ^ 21 ≤ ∏ j, Nv j ∧ ∏ j, Nv j ≤ N ∧
    ∀ j : Fin 20, 10 ≤ j.val → Nv j ≤ (N : ℝ) ^ (1 / 10 : ℝ)

/-- `T = q^{1/2} (N A⁻¹ + |λ| N) N^{2ε}`, display (3.7), page 264. -/
def Tcut (q : ℕ) (N : ℕ) (A lam ε : ℝ) : ℝ :=
  (q : ℝ) ^ (1 / 2 : ℝ) * (N / A + |lam| * N) * (N : ℝ) ^ (2 * ε)

/-- `T₀ = 4π (|λ| N + N A⁻¹)`, page 265. -/
def T0cut (N : ℕ) (A lam : ℝ) : ℝ := 4 * π * (|lam| * N + N / A)

/-- The weight `min (A, N / min_{N-A≤u≤N} |t + 2πλu|)` of (3.8), page 265, read as `A` when the
inner minimum is `0`. -/
def wt38 (N : ℕ) (A lam t : ℝ) : ℝ :=
  let m := sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N)
  if m = 0 then A else min A (N / m)

/-! ### Cited lemmas of Section II, LEAF statements -/

/-- Lemma 1 of the paper, cited from Titchmarsh, page 261, first derivative test: for real `F, G`
on `(a, b)` with `G/F'` monotone, `|F'| ≥ m > 0` and `|G| ≤ M`,
`∫_a^b G(u) e(F(u)) du ≪ M/m`. Continuity of `F'` and `G` is added. -/
def Lemma1 : Prop :=
  ∃ K : ℝ, ∀ (a b m M : ℝ) (F F' G : ℝ → ℝ), a ≤ b → 0 < m →
    (∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u) → ContinuousOn F' (Set.Icc a b) →
    ContinuousOn G (Set.Icc a b) →
    (MonotoneOn (fun u => G u / F' u) (Set.Icc a b) ∨
      AntitoneOn (fun u => G u / F' u) (Set.Icc a b)) →
    (∀ u ∈ Set.Icc a b, m ≤ |F' u|) → (∀ u ∈ Set.Icc a b, |G u| ≤ M) →
    ‖∫ u in a..b, (G u : ℂ) * ee (F u)‖ ≤ K * M / m

/-- Lemma 6 of the paper, cited [9], page 262, mean value theorem with characters:
`∫_U^{U+T} Σ_χ |Σ_{n=M+1}^{M+N} a_n χ(n) n^{-s}|² dt ≪ Σ (qT + n) |a_n|² n^{-2σ}`,
`s = σ + it`, for all `T ≥ 1` and real `U`. -/
def Lemma6 : Prop :=
  ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (M Nn : ℕ) (c : ℕ → ℂ) (T U σ : ℝ), 1 ≤ T →
    ∫ t in U..(U + T), ∑ χ : DirichletCharacter ℂ q,
      ‖∑ n ∈ Finset.Icc (M + 1) (M + Nn), c n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * Complex.I))‖ ^ 2
    ≤ K * ∑ n ∈ Finset.Icc (M + 1) (M + Nn), (q * T + n) * ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)

/-- Lemma 7 of the paper, cited [1], page 262: for `1/2 ≤ σ ≤ 1 + (log qT)⁻¹`, `2 ≤ |t| ≤ T`,
any `χ mod q`, `L^{(k)}(σ+it, χ) ≪ (qT)^{(1-σ)/2 + ε}`, `k = 0, 1`. -/
def Lemma7 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t T : ℝ)
    (k : ℕ), k ≤ 1 → 1 / 2 ≤ σ → σ ≤ 1 + 1 / Real.log (q * T) → 2 ≤ |t| → |t| ≤ T →
    ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (σ + t * Complex.I)‖
      ≤ K * ((q : ℝ) * T) ^ ((1 - σ) / 2 + ε)

section Zhan1122_zhan_lemma1_helpers
open Set MeasureTheory intervalIntegral Complex
/-- Second mean value step: a monotone weight bounded by `C`, against `h` whose tail integrals
are bounded by `B`. -/
private theorem lemma1_smvt_bound (a b C B : ℝ) (g : ℝ → ℝ) (h : ℝ → ℂ) (hab : a ≤ b)
    (hg : MonotoneOn g (Icc a b)) (hgb : ∀ u ∈ Icc a b, |g u| ≤ C)
    (hh : IntervalIntegrable h volume a b)
    (hH : ∀ x ∈ Icc a b, ‖∫ u in x..b, h u‖ ≤ B) :
    ‖∫ u in a..b, g u • h u‖ ≤ 3 * C * B := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hH b hbI)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hgb a haI)
  set f : ℝ → ℝ := fun u => g u + C with hf
  have hfm : MonotoneOn f (Icc a b) := fun x hx y hy hxy => by
    simp only [hf]; linarith [hg hx hy hxy]
  have hfa : 0 ≤ f a := by
    simp only [hf]; linarith [neg_abs_le (g a), hgb a haI]
  obtain ⟨ξ, hξ, hle⟩ :=
    exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn hab hfa hfm hh
  have hfi : IntervalIntegrable (fun x ↦ f x • h x) volume a b :=
    intervalIntegrable_iff.2 <| hh.def'.smul_of_top_right <|
      (hfm.memLp_isCompact isCompact_Icc).mono_measure <|
        Measure.restrict_mono_set volume (uIcc_of_le hab ▸ uIoc_subset_uIcc)
  have hci : IntervalIntegrable (fun x ↦ C • h x) volume a b := hh.smul C
  have heq : (∫ u in a..b, g u • h u) = (∫ u in a..b, f u • h u) - ∫ u in a..b, C • h u := by
    rw [← intervalIntegral.integral_sub hfi hci]
    congr 1; ext u; simp only [hf]; rw [add_smul]; abel
  rw [heq, intervalIntegral.integral_smul]
  have hfb : f b ≤ 2 * C := by
    simp only [hf]; linarith [le_abs_self (g b), hgb b hbI]
  have h1 : ‖∫ u in a..b, f u • h u‖ ≤ 2 * C * B :=
    hle.trans (mul_le_mul hfb (hH ξ hξ) (norm_nonneg _) (by linarith))
  have h2 : ‖C • ∫ u in a..b, h u‖ ≤ C * B := by
    rw [norm_smul, Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (hH a haI) hC
  calc _ ≤ ‖∫ u in a..b, f u • h u‖ + ‖C • ∫ u in a..b, h u‖ := norm_sub_le _ _
    _ ≤ 2 * C * B + C * B := add_le_add h1 h2
    _ = 3 * C * B := by ring

/-- The monotone case of Lemma 1. -/
private theorem lemma1_mono (a b m M : ℝ) (F F' G : ℝ → ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hF : ∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u) (hF' : ContinuousOn F' (Set.Icc a b))
    (hG : ContinuousOn G (Set.Icc a b))
    (hmono : MonotoneOn (fun u => G u / F' u) (Set.Icc a b))
    (hFm : ∀ u ∈ Set.Icc a b, m ≤ |F' u|) (hGM : ∀ u ∈ Set.Icc a b, |G u| ≤ M) :
    ‖∫ u in a..b, (G u : ℂ) * ee (F u)‖ ≤ 1 * M / m := by
  have hI : uIcc a b = Icc a b := uIcc_of_le hab
  set h : ℝ → ℂ := fun u => (F' u : ℂ) * ee (F u) with hhdef
  set E : ℝ → ℂ := fun u => ee (F u) / (2 * π * I) with hE
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hEd : ∀ u ∈ Icc a b, HasDerivAt E (h u) u := by
    intro u hu
    have h1 : HasDerivAt (fun u => ((F u : ℝ) : ℂ)) (F' u) u := (hF u hu).ofReal_comp
    have h2 := ((h1.const_mul (2 * π * I : ℂ)).cexp).div_const (2 * π * I)
    convert h2 using 1
    all_goals first
      | (simp only [hE, ee]; done)
      | (show (F' u : ℂ) * ee (F u) = _; simp only [ee]; field_simp)
  have hFc : ContinuousOn F (Icc a b) := fun u hu => (hF u hu).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc a b) := by
    simp only [hhdef, ee]
    exact (continuous_ofReal.comp_continuousOn hF').mul
      ((continuous_const.mul continuous_ofReal).cexp.comp_continuousOn hFc)
  have hhi : ∀ x ∈ Icc a b, IntervalIntegrable h volume x b := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.2]
    exact hhc.mono (Icc_subset_Icc hx.1 le_rfl)
  have hnE : ∀ u, ‖E u‖ = 1 / (2 * π) := by
    intro u
    simp only [hE, ee, norm_div]
    rw [show (2 * π * I : ℂ) * (F u : ℂ) = ((2 * π * F u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    simp [abs_of_pos Real.pi_pos]
  have hH : ∀ x ∈ Icc a b, ‖∫ u in x..b, h u‖ ≤ 1 / π := by
    intro x hx
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := E)
      (fun u hu => hEd u (by rw [uIcc_of_le hx.2] at hu; exact ⟨hx.1.trans hu.1, hu.2⟩))
      (hhi x hx)]
    calc _ ≤ ‖E b‖ + ‖E x‖ := norm_sub_le _ _
      _ = 1 / π := by rw [hnE, hnE]; field_simp; ring
  have hF0 : ∀ u ∈ Icc a b, F' u ≠ 0 := fun u hu h0 => by
    have := hFm u hu; rw [h0, abs_zero] at this; linarith
  have hgb : ∀ u ∈ Icc a b, |G u / F' u| ≤ M / m := by
    intro u hu
    rw [abs_div]
    have hp : 0 < |F' u| := abs_pos.2 (hF0 u hu)
    rw [div_le_div_iff₀ hp hm]
    have hM : 0 ≤ M := (abs_nonneg _).trans (hGM u hu)
    nlinarith [hGM u hu, hFm u hu, abs_nonneg (G u)]
  have heq : (∫ u in a..b, (G u : ℂ) * ee (F u)) = ∫ u in a..b, (G u / F' u) • h u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [hI] at hu
    simp only [hhdef, Complex.real_smul]
    have := hF0 u hu
    push_cast
    rw [← mul_assoc, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 this)]
  rw [heq]
  have key := lemma1_smvt_bound a b (M / m) (1 / π) _ h hab hmono hgb
    (hhi a ⟨le_rfl, hab⟩) hH
  have hMm : 0 ≤ M / m := (abs_nonneg _).trans (hgb a ⟨le_rfl, hab⟩)
  refine key.trans ?_
  have : 3 * (M / m) * (1 / π) ≤ M / m := by
    rw [mul_one_div, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  rw [one_mul]; linarith

/-- Lemma 1 of Zhan 1991, page 261, from Titchmarsh Lemma 4.3, with `K = 1`. -/
private theorem zhan_lemma1_proof : Lemma1 := by
  refine ⟨1, ?_⟩
  intro a b m M F F' G hab hm hF hF' hG hmon hFm hGM
  rcases hmon with hmon | hanti
  · exact lemma1_mono a b m M F F' G hab hm hF hF' hG hmon hFm hGM
  · have h := lemma1_mono a b m M F F' (fun u => -G u) hab hm hF hF' hG.neg
      (by
        have := hanti.neg
        intro x hx y hy hxy
        have := this hx hy hxy
        simp only at this
        simp only [neg_div]; exact this)
      hFm (fun u hu => by rw [abs_neg]; exact hGM u hu)
    have he : (∫ u in a..b, ((-G u : ℝ) : ℂ) * ee (F u)) = -∫ u in a..b, (G u : ℂ) * ee (F u) := by
      rw [← intervalIntegral.integral_neg]; congr 1; ext u; push_cast; ring
    rw [he, norm_neg] at h
    exact h
end Zhan1122_zhan_lemma1_helpers

/-- LEAF: Lemma 1, page 261, cited from Titchmarsh. Class MEDIUM. -/
theorem zhan_lemma1_leaf : Lemma1 := zhan_lemma1_proof

/-- LEAF: Lemma 2, page 261 display (2.1), cited from Zhan [4]; the `k = 1` case is derived as in
[1] Lemma 11. Class HARD. The Prop is `Lemma2` of Theorems235.lean. -/
theorem zhan_lemma2_leaf : Lemma2 := by
  sorry

/-- LEAF: Lemma 3, page 261 display (2.2), cited from Jutila [3]; the `k = 1` case as for
Lemma 2. Class HARD. The Prop is `Lemma3` of Theorems235.lean. -/
theorem zhan_lemma3_leaf : Lemma3 := by
  sorry

/-- LEAF: Lemma 6, page 262, cited [9], mean value theorem for Dirichlet polynomials with
characters. Class MEDIUM. -/
theorem zhan_lemma6_leaf : Lemma6 := by
  sorry

/-- LEAF: Lemma 7, page 262, cited [1], hybrid convexity bound for `L^{(k)}`. Class HARD. -/
theorem zhan_lemma7_leaf : Lemma7 := by
  sorry

/-! ### Top level steps of the Proof of Theorem 2, pages 262 to 269 -/

/-- Estimate (1.3) on the small range `N^{3/5} L^{c₃} ≤ A ≤ N^{2/3}`, the case the proof treats
after the reduction of pages 262 and 263. -/
def SmallRange : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧
    ∃ K N₀ : ℝ, Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
      (fun N => (N : ℝ) ^ (2 / 3 : ℝ))

/-- Estimate (1.3) on the large range `N L⁻¹ ≤ A ≤ N`, page 263. -/
def LargeRange : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m,
    ∃ K N₀ : ℝ, Est13 B c1 c2 K N₀ (fun N => (N : ℝ) / Real.log N) (fun N => (N : ℝ))

/-- The reduction of pages 262 and 263 as an implication with the same `B, c₁, c₂, c₃`:
(1.3) on `N^{3/5} L^{c₃} ≤ A ≤ N^{2/3}` gives (1.3) on `N^{2/3} ≤ A ≤ N L⁻¹`. -/
def MiddleReduction : Prop :=
  ∀ B c1 c2 c3 K N₀ : ℝ, 0 < B → 0 < c1 → 0 < c2 → 0 < c3 →
    Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
      (fun N => (N : ℝ) ^ (2 / 3 : ℝ)) →
    ∃ K' N₀' : ℝ, Est13 B c1 c2 K' N₀' (fun N => (N : ℝ) ^ (2 / 3 : ℝ))
      (fun N => (N : ℝ) / Real.log N)

/-- LEAF: page 262 last display and page 263 first line, the reduction from
`N^{2/3} ≤ A ≤ N L⁻¹` to `A ≤ N^{2/3}`: cut `(N-A, N]` into `J` blocks of length
`A₁ ∈ [N^{2/3}/2, N^{2/3}]` and apply (1.3) to each block, `≪ J · A₁ L^{-B} ≪ A L^{-B}`.
Class HARD. QUESTION: the paper applies (1.3) to each block with the same `α`, but (1.2) with
`τ₁ = A₁² N⁻¹ L^{-c₁}` need not hold, since `q ≤ τ = A² N⁻¹ L^{-c₁}` may exceed `τ₁`; for
`α = 1/q` with `q` near `N L^{-c₁-2}` each block sum is of size about `A₁`, so the blockwise
bound fails though the total may still be small. The implication is stated, not the blockwise
step. -/
theorem middle_reduction_leaf : MiddleReduction := by
  sorry

section Zhan1122_large_range_helpers
open Filter Asymptotics
/-- The two phase functions agree, `e(x) = exp(2πix)`. -/
private theorem ee_eq_vin (x : ℝ) : ee x = LeanLab.PNTPort.LargeSieve.e x := by
  unfold ee LeanLab.PNTPort.LargeSieve.e
  congr 1; push_cast; ring

/-- `|e(x)| = 1`. -/
private theorem ee_norm_v (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Page 260, `S(α; N, A) = S(α; N) - S(α; ⌊N - A⌋)` with PNTPort's full sum. PROVED. -/
private theorem sexp_eq_diff (N : ℕ) (A α : ℝ) (hA0 : 0 ≤ A) (hAN : A ≤ N) :
    Sexp α N A = LeanLab.PNTPort.Vinogradov.S N α -
      LeanLab.PNTPort.Vinogradov.S ⌊(N : ℝ) - A⌋₊ α := by
  unfold Sexp LeanLab.PNTPort.Vinogradov.S shortWin
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n : ℕ => (N : ℝ) - A < n)]
  have hset : (Finset.Icc 1 N).filter (fun n : ℕ => ¬ ((N : ℝ) - A < n)) =
      Finset.Icc 1 ⌊(N : ℝ) - A⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩
      have h3 : (n : ℝ) ≤ N - A := (Nat.le_floor_iff (by linarith)).mp h2
      refine ⟨⟨h1, ?_⟩, h3⟩
      have : (n : ℝ) ≤ N := by linarith
      exact_mod_cast this
  rw [hset]
  simp only [ee_eq_vin]
  ring

/-- The Chebyshev bound for PNTPort's full sum. PROVED. -/
private theorem S_trivial (M : ℕ) (α : ℝ) :
    ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤ (Real.log 4 + 4) * M := by
  have hb : ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤ Chebyshev.psi M := by
    unfold LeanLab.PNTPort.Vinogradov.S
    calc _ ≤ ∑ n ∈ Finset.Icc 1 M, ‖(Λ n : ℂ) * LeanLab.PNTPort.LargeSieve.e (n * α)‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 M, Λ n := by
          apply Finset.sum_congr rfl
          intro n _
          rw [norm_mul, ← ee_eq_vin, ee_norm_v, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ ≤ ∑ n ∈ Finset.Ioc 0 M, Λ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            have hh := Finset.mem_Icc.mp hn
            exact Finset.mem_Ioc.mpr ⟨by omega, hh.2⟩
          · intro n _ _
            exact ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by simp [Chebyshev.psi]
  exact hb.trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _))

/-- Vinogradov's bound at any `M ≤ N`, with the trivial bound when `M < q`. PROVED. -/
private theorem S_bound_M (N M q : ℕ) (a : ℤ) (α : ℝ) (hq : 1 ≤ q) (hcop : IsCoprime a (q : ℤ))
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (hMN : M ≤ N) :
    ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤
      300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        (1 + Real.log N) ^ 4 + (Real.log 4 + 4) * q := by
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hl4 : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  by_cases hqM : q ≤ M
  · have hv := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq hcop hα hqM
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_trans hq hqM
    have h1 : (M : ℝ) / Real.sqrt q ≤ N / Real.sqrt q :=
      div_le_div_of_nonneg_right hMN' (Real.sqrt_nonneg _)
    have h2 : (M : ℝ) ^ ((4 : ℝ) / 5) ≤ (N : ℝ) ^ ((4 : ℝ) / 5) :=
      Real.rpow_le_rpow (by linarith) hMN' (by norm_num)
    have h3 : Real.sqrt (M * q) ≤ Real.sqrt (N * q) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hMN' hq0.le)
    have h4 : (1 + Real.log M) ^ 4 ≤ (1 + Real.log N) ^ 4 := by
      have := Real.log_le_log (by linarith) hMN'
      have := Real.log_nonneg hM1
      gcongr
    have h5 : 0 ≤ (M : ℝ) / Real.sqrt q + (M : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (M * q) := by
      have := Real.sqrt_nonneg ((M : ℝ) * q)
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ M) ((4 : ℝ) / 5)
      have := div_nonneg (by linarith : (0 : ℝ) ≤ M) (Real.sqrt_nonneg (q : ℝ))
      linarith
    have h6 : 0 ≤ (1 + Real.log M) ^ 4 := by have := Real.log_nonneg hM1; positivity
    calc ‖LeanLab.PNTPort.Vinogradov.S M α‖
        ≤ 300 * ((M : ℝ) / Real.sqrt q + (M : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (M * q)) *
          (1 + Real.log M) ^ 4 := hv
      _ ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
          (1 + Real.log N) ^ 4 := by
          apply mul_le_mul _ h4 h6 (by linarith)
          linarith
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hl4 hq0.le)
  · push Not at hqM
    have hMq : (M : ℝ) ≤ q := by exact_mod_cast hqM.le
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hfirst : 0 ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) +
        Real.sqrt (N * q)) * (1 + Real.log N) ^ 4 := by
      have := Real.sqrt_nonneg ((N : ℝ) * q)
      have := Real.rpow_nonneg hN0 ((4 : ℝ) / 5)
      have := div_nonneg hN0 (Real.sqrt_nonneg (q : ℝ))
      have h0 : 0 ≤ (1 + Real.log N) ^ 4 := by
        rcases Nat.eq_zero_or_pos N with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ N := by exact_mod_cast h
          have := Real.log_nonneg this; positivity
      positivity
    calc ‖LeanLab.PNTPort.Vinogradov.S M α‖ ≤ (Real.log 4 + 4) * M := S_trivial M α
      _ ≤ (Real.log 4 + 4) * q := mul_le_mul_of_nonneg_left hMq hl4
      _ ≤ _ := le_add_of_nonneg_left hfirst

set_option maxHeartbeats 1600000 in
/-- Page 263, (1.3) on `N L⁻¹ ≤ A ≤ N` from Vinogradov: with `c₁, c₂ ≥ 2B + 12`,
`‖S(α; N, A)‖ ≤ 2 · 300 (N q^{-1/2} + N^{4/5} + (Nq)^{1/2}) (1 + L)^4 + 2 (log 4 + 4) q ≪ N L^{-B-1}
≤ A L^{-B}`, using `L^{c₂} ≤ q ≤ τ ≤ N L^{-c₁}`. PROVED. -/
private theorem largeRange_of_vinogradov : LargeRange := by
  intro B hB
  refine ⟨2 * B + 12, fun c1 hc1 => ⟨2 * B + 12, fun c2 hc2 => ?_⟩⟩
  have hasy := (isLittleO_log_rpow_rpow_atTop (B + 5) (by norm_num : (0 : ℝ) < 1 / 5)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hasy.and (eventually_ge_atTop (Real.exp 1)))
  refine ⟨2 * (300 * 16 * 3 + 8), X0, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  obtain ⟨hb, he⟩ := hX0 N hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 1) he
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hP15 : 0 < (N : ℝ) ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hN0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLpos.le _),
    abs_of_nonneg hP15.le, one_mul] at hb
  have hLp : ∀ u v : ℝ, u ≤ v → L ^ u ≤ L ^ v := fun u v h =>
    Real.rpow_le_rpow_of_exponent_le hL1 h
  have hA0 : 0 < A := lt_of_lt_of_le (div_pos hN0 hLpos) hlo
  have hNA : (N : ℝ) ≤ A * L := by rwa [div_le_iff₀ hLpos] at hlo
  obtain ⟨hαe, hgcd, hlam, hq1, hqτ⟩ := hcond
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hLc1 : 0 < L ^ (-c1) := Real.rpow_pos_of_pos hLpos _
  have hLc1le : L ^ (-c1) ≤ 1 := by
    have := hLp (-c1) 0 (by linarith); simpa using this
  set τ := A ^ 2 / N * L ^ (-c1) with hτ
  have hτN : τ ≤ N * L ^ (-c1) := by
    rw [hτ]
    apply mul_le_mul_of_nonneg_right _ hLc1.le
    rw [div_le_iff₀ hN0]; nlinarith
  have hqN : q ≤ N := by
    have : (q : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
    rw [hαe, add_sub_cancel_left]
    refine hlam.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_left hqτ hq0.le
  have hcop : IsCoprime a (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  have hdiff := sexp_eq_diff N A α hA0.le hhi
  have hbN := S_bound_M N N q a α hq1 hcop hα le_rfl
  have hbM := S_bound_M N ⌊(N : ℝ) - A⌋₊ q a α hq1 hcop hα (by
    apply Nat.floor_le_of_le; linarith)
  -- the pieces
  set P := (N : ℝ) * L ^ (-B - 1) with hP
  have hpow : ∀ u : ℝ, (N : ℝ) * L ^ (4 : ℝ) * L ^ u = N * L ^ (u + 4) := by
    intro u; rw [mul_assoc, ← Real.rpow_add hLpos]; ring_nf
  have hs1 : (N : ℝ) / Real.sqrt q ≤ N * L ^ (-(c2 / 2)) := by
    have hsq : L ^ (c2 / 2) ≤ Real.sqrt q := by
      rw [show L ^ (c2 / 2) = Real.sqrt (L ^ c2) by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLpos.le]; ring_nf]
      exact Real.sqrt_le_sqrt hq
    rw [Real.rpow_neg hLpos.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hN0.le (Real.rpow_pos_of_pos hLpos _) hsq
  have hs2 : Real.sqrt (N * q) ≤ N * L ^ (-(c1 / 2)) := by
    have h1 : (N : ℝ) * q ≤ (N * L ^ (-(c1 / 2))) ^ 2 := by
      have hsq2 : (L ^ (-(c1 / 2))) ^ 2 = L ^ (-c1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
      have e : (N * L ^ (-(c1 / 2))) ^ 2 = N * (N * L ^ (-c1)) := by
        rw [mul_pow, hsq2]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (hqτ.trans hτN) hN0.le
    rw [Real.sqrt_le_left (by positivity)]
    exact h1
  have hs3 : (N : ℝ) ^ ((4 : ℝ) / 5) ≤ N * L ^ (-(B + 5)) := by
    have e : (N : ℝ) = N ^ ((4 : ℝ) / 5) * N ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    rw [Real.rpow_neg hLpos.le]
    have hLB : 0 < L ^ (B + 5) := Real.rpow_pos_of_pos hLpos _
    rw [← div_eq_mul_inv, le_div_iff₀ hLB]
    calc (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (B + 5) ≤ N ^ ((4 : ℝ) / 5) * N ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hN0.le _)
      _ = N := e.symm
  have hs4 : (q : ℝ) ≤ N * L ^ (-c1) := hqτ.trans hτN
  have hlogs : (1 + L) ^ 4 ≤ 16 * L ^ (4 : ℝ) := by
    rw [show L ^ (4 : ℝ) = L ^ (4 : ℕ) by norm_cast]
    have : 1 + L ≤ 2 * L := by linarith
    calc (1 + L) ^ 4 ≤ (2 * L) ^ 4 := by gcongr
      _ = 16 * L ^ 4 := by ring
  have hL4 : 0 ≤ L ^ (4 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hbig : 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
      (1 + L) ^ 4 + (Real.log 4 + 4) * q ≤ (300 * 16 * 3 + 8) * P := by
    have hsum0 : 0 ≤ (N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q) := by
      have := Real.sqrt_nonneg ((N : ℝ) * q)
      have := Real.rpow_nonneg hN0.le ((4 : ℝ) / 5)
      have := div_nonneg hN0.le (Real.sqrt_nonneg (q : ℝ))
      linarith
    have hl4 : Real.log 4 + 4 ≤ 8 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have t1 : (N : ℝ) * L ^ (-(c2 / 2)) * L ^ (4 : ℝ) ≤ P := by
      rw [mul_assoc, ← Real.rpow_add hLpos, hP]
      exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have t2 : (N : ℝ) * L ^ (-(B + 5)) * L ^ (4 : ℝ) ≤ P := by
      rw [mul_assoc, ← Real.rpow_add hLpos, hP]
      exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have t3 : (N : ℝ) * L ^ (-(c1 / 2)) * L ^ (4 : ℝ) ≤ P := by
      rw [mul_assoc, ← Real.rpow_add hLpos, hP]
      exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have t4 : (N : ℝ) * L ^ (-c1) ≤ P := by
      rw [hP]; exact mul_le_mul_of_nonneg_left (hLp _ _ (by linarith)) hN0.le
    have hA1 : 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        (1 + L) ^ 4 ≤ 300 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) +
          Real.sqrt (N * q)) * (16 * L ^ (4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogs (by linarith)
    have hA2 : ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((4 : ℝ) / 5) + Real.sqrt (N * q)) *
        L ^ (4 : ℝ) ≤ 3 * P := by
      have := mul_le_mul_of_nonneg_right (add_le_add (add_le_add hs1 hs3) hs2) hL4
      nlinarith
    have hA3 : (Real.log 4 + 4) * q ≤ 8 * P := by
      have hq0' : (0 : ℝ) ≤ q := hq0.le
      calc (Real.log 4 + 4) * q ≤ 8 * q := mul_le_mul_of_nonneg_right hl4 hq0'
        _ ≤ 8 * P := by linarith
    nlinarith
  have hPA : P ≤ A * L ^ (-B) := by
    rw [hP, show (-B - 1 : ℝ) = -B + (-1) by ring, Real.rpow_add hLpos, Real.rpow_neg_one]
    have hLB0 : 0 < L ^ (-B) := Real.rpow_pos_of_pos hLpos _
    calc (N : ℝ) * (L ^ (-B) * L⁻¹) = N / L * L ^ (-B) := by ring
      _ ≤ A * L ^ (-B) := mul_le_mul_of_nonneg_right hlo hLB0.le
  rw [hdiff]
  calc ‖LeanLab.PNTPort.Vinogradov.S N α - LeanLab.PNTPort.Vinogradov.S ⌊(N : ℝ) - A⌋₊ α‖
      ≤ ‖LeanLab.PNTPort.Vinogradov.S N α‖ +
        ‖LeanLab.PNTPort.Vinogradov.S ⌊(N : ℝ) - A⌋₊ α‖ := norm_sub_le _ _
    _ ≤ 2 * ((300 * 16 * 3 + 8) * P) := by linarith
    _ ≤ 2 * (300 * 16 * 3 + 8) * (A * L ^ (-B)) := by nlinarith
    _ = _ := by ring
end Zhan1122_large_range_helpers

/-- LEAF: page 263 lines 1 and 2, "As for `N L⁻¹ ≤ A ≤ N`, (1.3) follows immediately from
Vinogradov's classical result". Class MEDIUM. Needs `c₁` large, since `q ≤ τ ≤ N L^{-c₁}` enters
Vinogradov's bound through `(Nq)^{1/2}`. -/
theorem large_range_leaf : LargeRange := largeRange_of_vinogradov

/-- The bound of display (3.1), page 263, after the reduction:
`Σ_{χ≠χ₀} |Σ_{N-A<n≤N} Λ(n) χ(n) e(nλ)| ≪ q^{1/2} A L^{-B-1}`. -/
def Eq31 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q], N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), ‖Schi χ lam N A‖
        ≤ K * (q : ℝ) ^ (1 / 2 : ℝ) * A * Real.log N ^ (-B - 1)

/-- The "well-known approach" display on page 263, before (3.1): with `α = a/q + λ`,
`(a, q) = 1`, `S(α; N, A) ≪ L q^{-1/2} Σ_{χ≠χ₀} |Σ Λ(n) χ(n) e(nλ)| + L² + L A q^{-1/2}`.
The side conditions `1 ≤ A ≤ N` and `q ≤ N` are added; they hold under Theorem 2. -/
def WellKnown : Prop :=
  ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N → 1 ≤ A →
    A ≤ N → α = a / q + lam → Int.gcd a q = 1 → (q : ℝ) ≤ N →
    ‖Sexp α N A‖ ≤ K * (Real.log N * (q : ℝ) ^ (-(1 / 2) : ℝ) *
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), ‖Schi χ lam N A‖)
      + Real.log N ^ (2 : ℝ) + Real.log N * A * (q : ℝ) ^ (-(1 / 2) : ℝ))

section Zhan1122_wellKnown_helpers
/-- Gauss sum bound `|τ(χ)| ≤ √q` for every Dirichlet character mod `q`, Davenport ch. 9,
by Parseval over the twists `τ(χ, e(a·/q))`. PROVED, port of `gaussSum_norm_le` of U-1529. -/
private theorem gaussSum_norm_le_wk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ √q := by
  classical
  let e136 : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun a => gaussSum χ (e136.mulShift a)
  have hortho (t : ZMod q) : ∑ a : ZMod q, e136 (t * a) = if t = 0 then (q : ℂ) else 0 := by
    by_cases ht : t = 0
    · simp [ht, e136]
    · rw [ite_eq_right ht]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
  have hstar (x : ZMod q) : star (e136 x) = e136 (-x) := by
    simpa [e136, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv] using
      (Complex.inv_eq_conj (Circle.norm_coe (ZMod.toCircle x))).symm
  have henergy : (∑ a : ZMod q, G a * star (G a)) =
      q * ∑ x : ZMod q, χ x * star (χ x) := by
    simp only [G, gaussSum, star_sum, star_mul, AddChar.mulShift_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    have hterm (a y : ZMod q) :
        χ x * e136 (a * x) * (star (e136 (a * y)) * star (χ y)) =
          (χ x * star (χ y)) * e136 ((x - y) * a) := by
      rw [hstar]
      calc
        _ = (χ x * star (χ y)) * (e136 (a * x) * e136 (-(a * y))) := by ring
        _ = _ := by rw [← AddChar.map_add_eq_mul]; congr 2 <;> ring
    simp_rw [hterm]
    simp_rw [← Finset.mul_sum, hortho]
    simp [sub_eq_zero, mul_ite]
    ring
  have hchars : (∑ x : ZMod q, χ x * star (χ x)) = (q.totient : ℂ) := by
    have ht (x : ZMod q) : χ x * star (χ x) = (1 : DirichletCharacter ℂ q) x := by
      by_cases hx : IsUnit x
      · change χ x * (starRingEnd ℂ) (χ x) = _
        rw [Complex.mul_conj', ← hx.unit_spec, χ.unit_norm_eq_one]
        simp [MulChar.one_apply hx]
      · simp [MulChar.map_nonunit _ hx]
    simp_rw [ht]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  rw [hchars] at henergy
  change (∑ a : ZMod q, G a * (starRingEnd ℂ) (G a)) = _ at henergy
  simp_rw [Complex.mul_conj'] at henergy
  have hreal : (∑ a : ZMod q, ‖G a‖ ^ 2) = (q : ℝ) * q.totient := by
    exact_mod_cast henergy
  have hunit (u : (ZMod q)ˣ) : ‖G u‖ = ‖gaussSum χ e136‖ := by
    dsimp [G]
    rw [gaussSum_mulShift_eq, norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
  have htriv : (∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re) = (q.totient : ℝ) := by
    have h := MulChar.sum_one_eq_card_units (R := ZMod q) (R' := ℂ)
    rw [ZMod.card_units_eq_totient] at h
    have hh := congrArg (fun z : ℂ => Complex.reCLM z) h
    rw [map_sum] at hh
    simpa using hh
  have hlow : (q.totient : ℝ) * ‖gaussSum χ e136‖ ^ 2 ≤ ∑ a : ZMod q, ‖G a‖ ^ 2 := by
    calc
      _ = ∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re * ‖gaussSum χ e136‖ ^ 2 := by
        rw [← Finset.sum_mul, htriv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : IsUnit a
        · rw [← ha.unit_spec, MulChar.one_apply (Units.isUnit ha.unit), Complex.one_re, one_mul,
            hunit]
        · rw [MulChar.map_nonunit _ ha, Complex.zero_re, zero_mul]
          positivity
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  change ‖gaussSum χ e136‖ ^ 2 ≤ (q : ℝ)
  rw [hreal] at hlow
  nlinarith

/-- Port of U-1529 `stdAddChar_eq_sum_gauss`: for a unit `m` mod `q`,
`e(m/q) = (1/φ(q)) Σ_χ χ(m⁻¹) τ(χ)`, Davenport ch. 9 (1), p. 65. PROVED. -/
private theorem stdAddChar_eq_sum_gauss_wk {q : ℕ} [NeZero q] {m : ZMod q} (hm : IsUnit m) :
    ZMod.stdAddChar m = (1 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * gaussSum χ ZMod.stdAddChar := by
  unfold gaussSum
  have h_inner : ∀ χ : DirichletCharacter ℂ q,
      χ m⁻¹ * ∑ a : ZMod q, χ a * ZMod.stdAddChar a =
      ∑ a : ZMod q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) := by
    intro χ
    rw [Finset.mul_sum]
  simp_rw [h_inner]
  rw [Finset.sum_comm]
  have h_sum : ∀ a : ZMod q,
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) =
      (∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a) * ZMod.stdAddChar a := by
    intro a
    have : (fun χ : DirichletCharacter ℂ q => χ m⁻¹ * (χ a * ZMod.stdAddChar a)) = (fun χ : DirichletCharacter ℂ q => (χ m⁻¹ * χ a) * ZMod.stdAddChar a) := by
      ext χ
      rw [mul_assoc]
    rw [this, Finset.sum_mul]
  simp_rw [h_sum]
  have h_char_sum : ∀ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a = if m = a then (q.totient : ℂ) else 0 := by
    intro a
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm]
  simp_rw [h_char_sum]
  have h_eval : ∑ a : ZMod q, (if m = a then (q.totient : ℂ) else 0) * ZMod.stdAddChar a = (q.totient : ℂ) * ZMod.stdAddChar m := by
    rw [Finset.sum_eq_single m]
    · split_ifs with h_if
      · rfl
      · contradiction
    · intro b _ hb
      split_ifs with h_if
      · exact False.elim (hb h_if.symm)
      · rw [zero_mul]
    · intro h
      exfalso
      exact h (Finset.mem_univ m)
  rw [h_eval, ← mul_assoc]
  have h_div : (1 / (q.totient : ℂ)) * (q.totient : ℂ) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    have h_totient_pos : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast ne_of_gt h_totient_pos
  rw [h_div, one_mul]

/-- Evaluating a character at an inverse unit is evaluating the inverse character. PROVED. -/
private lemma character_inv_unit_wk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : ZMod q} (hm : IsUnit m) : χ m⁻¹ = χ⁻¹ m := by
  rw [MulChar.inv_apply, ← hm.unit_spec, Ring.inverse_unit, ZMod.inv_coe_unit]

/-- Pointwise character expansion, page 263: for a unit `m` and any `n`,
`[(n, q) = 1] e(mn/q) = (1/φ(q)) Σ_χ χ̄(m) τ(χ) χ̄(n)`. PROVED. -/
private lemma unit_expansion_wk {q : ℕ} [NeZero q] {m : ZMod q} (hm : IsUnit m) (n : ℕ) :
    (if IsUnit (n : ZMod q) then ZMod.stdAddChar (m * (n : ZMod q)) else 0) =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * χ⁻¹ (n : ZMod q) := by
  by_cases hn : IsUnit (n : ZMod q)
  · rw [if_pos hn, stdAddChar_eq_sum_gauss_wk (hm.mul hn)]
    simp_rw [character_inv_unit_wk _ (hm.mul hn), map_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    ring
  · rw [if_neg hn]
    simp [MulChar.map_nonunit _ hn]

private lemma ee_add_wk (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_ee_wk (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee; rw [Complex.norm_exp]; simp

private lemma stdAddChar_int_mul_wk {q : ℕ} [NeZero q] (a : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) = ee ((a : ℝ) * n / q) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * (n : ℤ))
  simp only [Int.cast_mul, Int.cast_natCast] at h
  rw [h]
  unfold ee
  congr 1
  push_cast
  ring

/-- Ramanujan's sum at a reduced residue: `Σ_{b < q, (b,q)=1} e(ab/q) = μ(q)` for
`(a,q) = 1`; it turns the reduced residues into the main term `μ(q)/φ(q) T(η)` of `R`,
p. 357 and p. 361. Unit U-1519. -/
private theorem ramanujan_coprime_wk {q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ee ((a : ℝ) * b / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  let c : ℕ → ℂ := fun n => ∑ b ∈ (Finset.range n).filter (fun b => Nat.Coprime b n), ee ((a : ℝ)*b/n)
  have hfiber : ∀ n : ℕ, 0 < n → ∀ d ∈ n.divisors,
      (∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), ee ((a : ℝ)*b/n)) = c (n/d) := by
    intro n hn d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mem_divisors hd
    rw [Nat.mul_div_cancel_left r hd0]
    dsimp [c]
    symm
    apply Finset.sum_bij (fun b _ => d*b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨by nlinarith [hb.1], ?_⟩
      rw [Nat.gcd_mul_left, show Nat.gcd r b=1 from hb.2.symm, mul_one]
    · intro b hb b' hb' he
      exact Nat.eq_of_mul_eq_mul_left hd0 he
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hdb : d ∣ b := hb.2 ▸ Nat.gcd_dvd_right (d*r) b
      obtain ⟨u, rfl⟩ := hdb
      refine ⟨u, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_left hd0).mp hb.1
      · rw [Nat.gcd_mul_left] at hb
        have hg : Nat.gcd r u = 1 := by nlinarith [hb.2]
        exact (show Nat.Coprime r u from hg).symm
    · intro b hb
      have hr0 : r ≠ 0 := by intro hr; subst r; simp at hn
      push_cast
      field_simp
  have hgroup : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, c d) =
      ∑ b ∈ Finset.range n, ee ((a : ℝ)*b/n) := by
    intro n hn
    rw [← Nat.sum_div_divisors n c]
    calc (∑ d ∈ n.divisors, c (n/d)) = ∑ d ∈ n.divisors,
        ∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), ee ((a : ℝ)*b/n) := by
          apply Finset.sum_congr rfl
          intro d hd; exact (hfiber n hn d hd).symm
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun b hb => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n b, by omega⟩) _
  have htotal : ∀ n : ℕ, 0 < n → n ∣ q →
      (∑ b ∈ Finset.range n, ee ((a : ℝ)*b/n)) = if n=1 then 1 else 0 := by
    intro n hn hnq
    by_cases hn1 : n=1
    · subst n; simp [ee]
    · rw [ite_eq_right hn1]
      have hac : Nat.Coprime a n := ha.of_dvd_right hnq
      have hp : IsPrimitiveRoot (ee ((a : ℝ)/n)) n := by
        convert Complex.isPrimitiveRoot_exp_of_coprime a n (by omega) hac using 1
        unfold ee; push_cast; congr 1
      have hepow : ∀ b : ℕ, ee ((a : ℝ)*b/n) = ee ((a : ℝ)/n)^b := by
        intro b
        induction b with
        | zero => simp [ee]
        | succ b ih => rw [pow_succ, ← ih, ← ee_add_wk]; congr 1; push_cast; ring
      simp_rw [hepow]
      exact hp.geom_sum_eq_zero (by omega)
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := c) (g := fun n => if n=1 then (1 : ℂ) else 0) {n | n ∣ q}
    (fun m n hmn hn => hmn.trans hn)).mp
      (fun n hn hnq => (hgroup n hn).trans (htotal n hn hnq)) q (by omega) (dvd_refl q)
  rw [Nat.sum_divisorsAntidiagonal (fun d r => ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if r=1 then 1 else 0))] at hinv
  have hs : (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (if q/d=1 then 1 else 0)) = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    rw [Finset.sum_eq_single q]
    · rw [Nat.div_self (by omega), ite_eq_left rfl, mul_one]
    · intro d hd hdq
      have hd' := Nat.dvd_of_mem_divisors hd
      have hneq : q/d ≠ 1 := by
        intro h
        have := Nat.div_mul_cancel hd'
        rw [h, one_mul] at this
        exact hdq this
      rw [ite_eq_right hneq, mul_zero]
    · intro h; exact False.elim (h (Nat.mem_divisors_self q (by omega)))
  rw [hs] at hinv
  exact hinv.symm

private theorem gaussSum_one_wk {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  have hsum : gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ee ((1 : ℝ) * a / q) := by
    unfold gaussSum
    rw [Finset.sum_filter]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.val_lt
    · intro a _ b _ h
      exact ZMod.val_injective q h
    · intro b hb
      refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
    · intro a _
      have hcop : IsUnit a ↔ Nat.Coprime a.val q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      by_cases ha : IsUnit a
      · rw [MulChar.one_apply ha, one_mul, if_pos (hcop.mp ha)]
        have he := ZMod.stdAddChar_coe (N := q) (a.val : ℤ)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at he
        rw [he]
        unfold ee
        congr 1
        push_cast
        ring
      · rw [MulChar.map_nonunit _ ha, zero_mul, if_neg (fun h => ha (hcop.mpr h))]
  rw [hsum]
  simpa only [Nat.cast_one] using ramanujan_coprime_wk (q := q) (a := 1) (NeZero.pos q) (Nat.coprime_one_left q)

/- parity helper -/
private lemma odd_of_mul_odd_wk {p m : ℕ} (h : Odd (p * m)) : Odd m := by
  rw [Nat.odd_iff] at h ⊢
  by_contra hc
  have h0 : m % 2 = 0 := by omega
  rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at h
  omega

/- C': p <= (p-1)^2 for p >= 3 -/
private lemma prime_le_pred_sq_wk {p : ℕ} (hp : 3 ≤ p) : p ≤ (p - 1) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
  have h : t + 3 - 1 = t + 2 := by omega
  rw [h, pow_two]
  nlinarith

/- D: n <= 4 * totient n ^ 2, over the reals -/
private lemma totient_key_wk (n : ℕ) :
    (n:ℝ) ≤ 4 * (n.totient:ℝ) ^ 2 ∧ (Odd n → (n:ℝ) ≤ 2 * (n.totient:ℝ) ^ 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · rcases Nat.eq_or_lt_of_le hpos with h1 | h2
      · subst h1; norm_num
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
        obtain ⟨m, rfl⟩ := hpdvd
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
        have hp0 : (0:ℝ) ≤ (p:ℝ) := by linarith
        have hm : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at h2
          · exact h
        have hlt : m < p * m := by
          have h2p := hp.two_le
          have hm1 : 0 < m := hm
          nlinarith
        obtain ⟨ihm, ihm2⟩ := ih m hlt
        have hpp : (p:ℝ) ≤ (p:ℝ)^2 := by nlinarith
        have h1p : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
          rw [Nat.cast_sub hp.one_le]; norm_num
        constructor
        · by_cases hpm : p ∣ m
          · rw [Nat.totient_mul_of_prime_of_dvd hp hpm]; push_cast
            calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (4 * (m.totient:ℝ)^2) :=
                  mul_le_mul_of_nonneg_left ihm hp0
              _ = 4 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
              _ ≤ 4 * (p:ℝ)^2 * (m.totient:ℝ)^2 := by
                  nlinarith [hpp, sq_nonneg (m.totient:ℝ)]
              _ = 4 * ((p:ℝ) * (m.totient:ℝ))^2 := by ring
          · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm]
            push_cast [h1p]
            rcases eq_or_lt_of_le hp.two_le with hp_eq | hp_gt
            · subst hp_eq
              norm_num
              have hmo : Odd m := by
                rw [← Nat.not_even_iff_odd, even_iff_two_dvd]; exact hpm
              have hs2 := ihm2 hmo
              calc (2:ℝ) * (m:ℝ) ≤ 2 * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 (by norm_num)
                _ = 4 * (m.totient:ℝ)^2 := by ring
            · have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp_gt
              have hsq : (p:ℝ) ≤ ((p:ℝ) - 1)^2 := by nlinarith
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (4 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left ihm hp0
                _ = 4 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ ((p:ℝ) - 1)^2 * (4 * (m.totient:ℝ)^2) := by
                    nlinarith [hsq, sq_nonneg (m.totient:ℝ)]
                _ = 4 * (((p:ℝ) - 1) * (m.totient:ℝ))^2 := by ring
        · intro hodd
          have hmo : Odd m := odd_of_mul_odd_wk hodd
          have hs2 := ihm2 hmo
          by_cases hp_eq : p = 2
          · subst hp_eq
            exact absurd hodd (by
              rw [Nat.odd_iff, Nat.mul_mod]; simp)
          · have hp3 : (3:ℝ) ≤ (p:ℝ) := by
              have : 3 ≤ p := by have := hp.two_le; omega
              exact_mod_cast this
            by_cases hpm : p ∣ m
            · rw [Nat.totient_mul_of_prime_of_dvd hp hpm]; push_cast
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 hp0
                _ = 2 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ 2 * (p:ℝ)^2 * (m.totient:ℝ)^2 := by
                    nlinarith [hpp, sq_nonneg (m.totient:ℝ)]
                _ = 2 * ((p:ℝ) * (m.totient:ℝ))^2 := by ring
            · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm]
              push_cast [h1p]
              have hsq : (p:ℝ) ≤ ((p:ℝ) - 1)^2 := by nlinarith
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 hp0
                _ = 2 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ ((p:ℝ) - 1)^2 * (2 * (m.totient:ℝ)^2) := by
                    nlinarith [hsq, sq_nonneg (m.totient:ℝ)]
                _ = 2 * (((p:ℝ) - 1) * (m.totient:ℝ))^2 := by ring

private lemma totient_sq_ge_wk (n : ℕ) : (n:ℝ) ≤ 4 * (n.totient:ℝ) ^ 2 := (totient_key_wk n).1

/-- The product bound: `∏ p ≤ (|s| + 1) ∏ (p - 1)`, i.e. `∏ p/(p - 1) ≤ |s| + 1`. Induction on the maximum element:
removing `a` leaves `|s| - 1` elements, all `≥ 2` and `< a`, so `a ≥ |s| + 1`, and `a ≥ |s| + 1` is
exactly what `a·|s| ≤ (|s| + 1)(a - 1)` needs. -/
private theorem prod_le_card_succ_mul_prod_pred_wk {s : Finset ℕ} (h2 : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  revert h2
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h2
    have h2a : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have han : a ∉ s := fun h => absurd (ha a h) (lt_irrefl a)
    have hP := ih h2s
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨h2s x hx, by have := ha x hx; omega⟩
    have hcard : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have ham : s.card + 2 ≤ a := by omega
    obtain ⟨t, ht⟩ : ∃ t, a = s.card + 2 + t := ⟨a - (s.card + 2), by omega⟩
    have ha1 : a - 1 = s.card + 1 + t := by omega
    rw [Finset.prod_insert han, Finset.prod_insert han, Finset.card_insert_of_notMem han, ha1, ht]
    calc (s.card + 2 + t) * ∏ p ∈ s, p
        ≤ (s.card + 2 + t) * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
          Nat.mul_le_mul_left _ hP
      _ = ((s.card + 2 + t) * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((s.card + 1 + 1) * (s.card + 1 + t)) * ∏ p ∈ s, (p - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          nlinarith
      _ = (s.card + 1 + 1) * ((s.card + 1 + t) * ∏ p ∈ s, (p - 1)) := by ring

/-- `n ≤ φ(n) * (number of distinct prime divisors of n + 1)`. -/
private theorem totient_mul_card_succ_ge_wk (n : ℕ) :
    n ≤ Nat.totient n * (n.primeFactors.card + 1) := by
  have hid := Nat.totient_mul_prod_primeFactors n
  have hP : ∏ p ∈ n.primeFactors, p ≤
      (n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_le_card_succ_mul_prod_pred_wk fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * (n.primeFactors.card + 1)) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * ((n.primeFactors.card + 1) *
            ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hP
      _ = (Nat.totient n * (n.primeFactors.card + 1)) *
            ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

private theorem totient_ge_div_card_succ_wk (n : ℕ) :
    (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) ≤ (Nat.totient n : ℝ) := by
  have h := totient_mul_card_succ_ge_wk n
  have hc : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hc]
  have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * ((n.primeFactors.card : ℝ) + 1) := by
    exact_mod_cast h
  linarith

private theorem two_pow_card_primeFactors_le_wk {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        have h2a : 2 ≤ a := hs a (Finset.mem_insert_self a s)
        have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        calc 2 ^ s.card * 2 ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul (ih h2s) h2a
          _ = a * ∏ p ∈ s, p := by ring
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    key _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : 0 < n := by omega
  exact h1.trans (Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd n))

private theorem card_primeFactors_le_log_div_wk {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 := two_pow_card_primeFactors_le_wk hn
  have h2' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast h2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hlog := Real.log_le_log hbase h2'
  rw [Real.log_pow] at hlog
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  linarith

/-- **`φ(n) ≫ n / log n`**: `log 2 · n / (1 + log n) ≤ φ(n)` for `n ≥ 1`, the shape the coefficient
bound `‖c'‖ ≪ q^{-3/2} (1 + log q)^2` needs. -/
private theorem totient_ge_log_two_mul_div_wk {n : ℕ} (hn : 1 ≤ n) :
    Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤ (Nat.totient n : ℝ) := by
  have hφ := totient_ge_div_card_succ_wk n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlog1 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := card_primeFactors_le_log_div_wk hn
  -- `k + 1 ≤ (1 + log n) / log 2`
  have hk2 : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [le_div_iff₀ hlog2] at hk
    linarith
  have hk1 : ((n.primeFactors.card : ℝ) + 1) * Real.log 2 ≤ 1 + Real.log n := by
    nlinarith [hk2, hlog2lt]
  have hone : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  -- `log 2 · n / (1 + log n) ≤ n / (k + 1)`
  have hstep : Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤
      (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + Real.log n) hone]
    nlinarith [hk1, hnpos, hlog2]
  exact hstep.trans hφ
/-- Page 263, the principal character term: `|τ(χ₀)| = |c_q(1)| = |μ(q)| ≤ 1`, Hardy-Wright
Theorem 271, Davenport ch. 26 p. 147. PROVED. -/
private theorem gaussSum_one_norm_le_wk {q : ℕ} [NeZero q] :
    ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ≤ 1 := by
  rw [gaussSum_one_wk, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- Page 263, `φ(q) ≫ q^{1/2}`: `√q ≤ 2 φ(q)`, from `q ≤ 4 φ(q)²`. PROVED. -/
private theorem sqrt_le_two_totient_wk (q : ℕ) (_hq : 1 ≤ q) :
    Real.sqrt q ≤ 2 * (q.totient : ℝ) := by
  calc Real.sqrt q ≤ Real.sqrt ((2 * (q.totient : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [totient_sq_ge_wk q])
    _ = 2 * (q.totient : ℝ) := Real.sqrt_sq (by positivity)

/-- Page 263, `φ(q) ≫ q L⁻¹`: from `φ(q)/q ≥ 1/(ω(q)+1)` and `ω(q) ≤ log q / log 2`. PROVED. -/
private theorem le_log_mul_totient_wk (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) ≤ 2 * (Real.log q + 1) * (q.totient : ℝ) := by
  have h := totient_ge_log_two_mul_div_wk hq
  have hl : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  rw [div_le_iff₀ (by linarith)] at h
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith [mul_le_mul_of_nonneg_right hlog2.le hq0]

/-- Page 263: the mass of one prime `p` on `n ≤ N`, `p ∣ n`, is `Σ Λ(n) ≤ log N`, since only
the powers `p^k ≤ N` count, each with `Λ = log p`. PROVED. -/
private lemma prime_mass_le_wk (N p : ℕ) (hp : p.Prime) (hN : 1 ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), Λ n ≤ Real.log N := by
  classical
  set S := (Finset.Icc 1 N).filter (fun n => p ∣ n)
  set K := Nat.log p N
  have hsub : S.filter (fun n => Λ n ≠ 0) ⊆ (Finset.Icc 1 K).image (fun k => p ^ k) := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hpn⟩, hΛ⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨r, k, hr, hk, rfl⟩ := hΛ
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
    subst hpr
    simp only [Finset.mem_image, Finset.mem_Icc]
    exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hp.one_lt hnN⟩, rfl⟩
  have hval : ∀ n ∈ S.filter (fun n => Λ n ≠ 0), Λ n = Real.log p := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hpn⟩, hΛ⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨r, k, hr, hk, rfl⟩ := hΛ
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
    subst hpr
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hcard : (S.filter (fun n => Λ n ≠ 0)).card ≤ K := by
    calc _ ≤ ((Finset.Icc 1 K).image (fun k => p ^ k)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 K).card := Finset.card_image_le
      _ = K := by simp
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp0 := hp.pos
  calc ∑ n ∈ S, Λ n = ∑ n ∈ S.filter (fun n => Λ n ≠ 0), Λ n :=
        (Finset.sum_filter_ne_zero _).symm
    _ = (S.filter (fun n => Λ n ≠ 0)).card * Real.log p := by
        rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * Real.log p := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogp
    _ = Real.log ((p ^ K : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]
    _ ≤ Real.log N := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.pow_log_le_self p (by omega)

/-- Page 263, "drop `(n, q) > 1` at cost `O(L²)`": the `n ≤ N` with `Λ(n) ≠ 0` and
`(n, q) > 1` are powers of the at most `log q / log 2` primes `p ∣ q`, each `p` giving mass
`≤ log N`. PROVED. -/
private theorem noncoprime_mass_wk (N q : ℕ) (hN : 2 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤
      2 * Real.log N ^ 2 := by
  classical
  have hnn : ∀ (n p : ℕ), 0 ≤ (if p ∣ n then Λ n else 0) := by
    intro n p; split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_refl _
  have hpt : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
      Λ n ≤ ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n else 0) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn.2
    have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩
    calc Λ n = (if p ∣ n then Λ n else 0) := by rw [if_pos hpn]
      _ ≤ _ := Finset.single_le_sum (f := fun p => if p ∣ n then Λ n else 0)
          (fun i _ => hnn n i) hpmem
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
        ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n else 0) := Finset.sum_le_sum hpt
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact Finset.sum_nonneg (fun p _ => hnn i p)
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), Λ n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N := by
        apply Finset.sum_le_sum
        intro p hp
        exact prime_mass_le_wk N p (Nat.prime_of_mem_primeFactors hp) (by omega)
    _ = q.primeFactors.card * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.log N ^ 2 := by
        have hc := card_primeFactors_le_log_div_wk hq
        have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
        have hlq : Real.log q ≤ Real.log N :=
          Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqN)
        have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
        have hc0 : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
        have hc2 : (q.primeFactors.card : ℝ) ≤ 2 * Real.log N := by
          rw [le_div_iff₀ (by linarith)] at hc
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc2 hL0]

private lemma card_shortWin_wk (N : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ((shortWin N A).card : ℝ) ≤ A + 1 := by
  have hsub : shortWin N A ⊆ Finset.Icc (N - ⌊A⌋₊) N := by
    intro n hn
    simp only [shortWin, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨?_, hn.1.2⟩
    have h1 := Nat.lt_floor_add_one A
    have h2 : (N : ℝ) < n + (⌊A⌋₊ + 1) := by linarith [hn.2]
    have h3 : N < n + (⌊A⌋₊ + 1) := by exact_mod_cast h2
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hc2 : (shortWin N A).card ≤ ⌊A⌋₊ + 1 := by omega
  have : ((shortWin N A).card : ℝ) ≤ ⌊A⌋₊ + 1 := by exact_mod_cast hc2
  linarith [Nat.floor_le hA]

private lemma norm_Schi_le_wk {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℝ) (N : ℕ) (A : ℝ)
    (hA : 0 ≤ A) : ‖Schi χ lam N A‖ ≤ (A + 1) * Real.log N := by
  unfold Schi
  calc ‖∑ n ∈ shortWin N A, (Λ n : ℂ) * χ n * ee (n * lam)‖
      ≤ ∑ n ∈ shortWin N A, ‖(Λ n : ℂ) * χ n * ee (n * lam)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ shortWin N A, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [shortWin, Finset.mem_filter, Finset.mem_Icc] at hn
        rw [norm_mul, norm_mul, norm_ee_wk, mul_one, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc Λ n * ‖χ n‖ ≤ Λ n * 1 :=
              mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ Real.log n := by rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log N := by
              apply Real.log_le_log (by exact_mod_cast hn.1.1) (by exact_mod_cast hn.1.2)
    _ = (shortWin N A).card * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A + 1) * Real.log N := by
        apply mul_le_mul_of_nonneg_right (card_shortWin_wk N A hA)
        exact Real.log_natCast_nonneg N

/-- The character sum after expansion, split at `χ₀`, with `|τ(χ)| ≤ √q`. PROVED. -/
private lemma char_part_bound_wk {q : ℕ} [NeZero q] (m : ZMod q) (S : DirichletCharacter ℂ q → ℂ) :
    ‖(1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * S χ⁻¹‖ ≤
      (1 / (q.totient : ℝ)) * (‖S 1‖ +
        Real.sqrt q * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ‖S χ‖) := by
  classical
  have hnorm : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
    simp [norm_div, Complex.norm_natCast]
  rw [norm_mul, hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let g : DirichletCharacter ℂ q → ℝ := fun χ => ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖S χ‖
  calc ‖∑ χ : DirichletCharacter ℂ q, χ⁻¹ m * gaussSum χ ZMod.stdAddChar * S χ⁻¹‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ⁻¹ m * gaussSum χ ZMod.stdAddChar * S χ⁻¹‖ :=
        norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, g χ⁻¹ := by
        apply Finset.sum_le_sum
        intro χ _
        simp only [g, inv_inv]
        rw [norm_mul, norm_mul]
        have := DirichletCharacter.norm_le_one χ⁻¹ m
        have h0 : 0 ≤ ‖gaussSum χ ZMod.stdAddChar‖ * ‖S χ⁻¹‖ := by positivity
        nlinarith [norm_nonneg (gaussSum χ ZMod.stdAddChar), norm_nonneg (S χ⁻¹)]
    _ = ∑ χ : DirichletCharacter ℂ q, g χ :=
        Fintype.sum_equiv (Equiv.inv _) (fun χ => g χ⁻¹) g (fun _ => rfl)
    _ = g 1 + ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), g χ := by
        rw [Finset.filter_ne', Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    _ ≤ ‖S 1‖ + ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          Real.sqrt q * ‖S χ‖ := by
        apply add_le_add
        · simp only [g, inv_one]
          have := gaussSum_one_norm_le_wk (q := q)
          nlinarith [norm_nonneg (S 1)]
        · apply Finset.sum_le_sum
          intro χ _
          exact mul_le_mul_of_nonneg_right (gaussSum_norm_le_wk χ⁻¹) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

private theorem wellKnown_proof : WellKnown := by
  classical
  refine ⟨8, 3, ?_⟩
  intro N A α lam a q _ hN hA1 hAN hα hgcd hqN
  set L := Real.log N with hL
  have hN3 : (3 : ℝ) ≤ N := hN
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hq1n : 1 ≤ q := NeZero.one_le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1n
  have hqpos : (0 : ℝ) < q := by linarith
  set m : ZMod q := (a : ZMod q) with hmdef
  have hm : IsUnit m := by
    have h := Int.gcd_eq_gcd_ab a q
    rw [hgcd] at h
    refine isUnit_iff_exists_inv.mpr ⟨((Int.gcdA a q : ℤ) : ZMod q), ?_⟩
    have h2 := congrArg (fun z : ℤ => (z : ZMod q)) h
    simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero] at h2
    exact h2.symm
  -- split each term
  set W := shortWin N A
  have hterm : ∀ n : ℕ, (Λ n : ℂ) * ee (n * α) =
      (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then
        ZMod.stdAddChar (m * (n : ZMod q)) else 0) +
      (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q))) := by
    intro n
    have he : ee (n * α) = ee ((a : ℝ) * n / q) * ee (n * lam) := by
      rw [← ee_add_wk, hα]; congr 1; ring
    rw [he, ← stdAddChar_int_mul_wk]
    split_ifs <;> ring
  have hsplit : Sexp α N A =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * Schi χ⁻¹ lam N A +
      ∑ n ∈ W, (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q))) := by
    unfold Sexp
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    congr 1
    simp_rw [unit_expansion_wk hm]
    unfold Schi
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro χ _
    ring
  -- bound the non-coprime part
  have hT2 : ‖∑ n ∈ W, (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q)))‖ ≤ 2 * L ^ 2 := by
    calc _ ≤ ∑ n ∈ W, ‖(Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
          ZMod.stdAddChar (m * (n : ZMod q)))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ W, (if Nat.Coprime n q then 0 else Λ n) := by
          apply Finset.sum_le_sum
          intro n _
          have hu := ZMod.isUnit_iff_coprime n q
          by_cases h : Nat.Coprime n q
          · rw [if_pos h, if_pos (hu.mpr h)]; simp
          · rw [if_neg h, if_neg (fun h' => h (hu.mp h'))]
            rw [norm_mul, norm_mul, norm_ee_wk, mul_one, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            simp [AddChar.norm_apply]
      _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n := by
          rw [Finset.sum_filter]
          simp_rw [ite_not]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [W, shortWin, Finset.mem_filter] at hn
            exact hn.1
          · intro n _ _
            split_ifs
            · exact le_refl _
            · exact ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ 2 * L ^ 2 := noncoprime_mass_wk N q hN2 hq1n (by exact_mod_cast hqN)
  have hchar := char_part_bound_wk m (fun χ => Schi χ lam N A)
  have hP := norm_Schi_le_wk (1 : DirichletCharacter ℂ q) lam N A (by linarith)
  set T := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
    ‖Schi χ lam N A‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set s := Real.sqrt q with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hqpos
  have hss : s * s = q := Real.mul_self_sqrt hqpos.le
  have h1 : s ≤ 2 * q.totient := sqrt_le_two_totient_wk q hq1n
  have h2 : (q : ℝ) ≤ 2 * (Real.log q + 1) * q.totient := le_log_mul_totient_wk q hq1n
  have hlogq : Real.log q ≤ L := Real.log_le_log hqpos hqN
  have h2' : s * s ≤ 4 * L * q.totient := by rw [hss]; nlinarith
  have hrp : (q : ℝ) ^ (-(1 / 2) : ℝ) = 1 / s := by
    rw [Real.rpow_neg hqpos.le, ← Real.sqrt_eq_rpow, one_div]
  have hL2 : L ^ (2 : ℝ) = L ^ 2 := Real.rpow_two L
  have hu1 : 1 / (q.totient : ℝ) ≤ 2 / s := by
    rw [div_le_div_iff₀ hphi hs0]; linarith
  have hu2 : 1 / (q.totient : ℝ) * s ≤ 4 * L / s := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hphi hs0]; linarith
  have hL0 : 0 ≤ L := by linarith
  have ht0 : 0 ≤ 1 / s := by positivity
  rw [hrp, hL2, hsplit]
  calc _ ≤ ‖(1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * Schi χ⁻¹ lam N A‖ +
      ‖∑ n ∈ W, (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q)))‖ := norm_add_le _ _
    _ ≤ (1 / (q.totient : ℝ)) * (‖Schi 1 lam N A‖ + s * T) + 2 * L ^ 2 :=
        add_le_add hchar hT2
    _ = 1 / (q.totient : ℝ) * ‖Schi 1 lam N A‖ + (1 / (q.totient : ℝ) * s) * T + 2 * L ^ 2 := by
        ring
    _ ≤ 2 / s * ((A + 1) * L) + 4 * L / s * T + 2 * L ^ 2 := by
        gcongr
    _ = 2 * (1 / s) * ((A + 1) * L) + 4 * L * (1 / s) * T + 2 * L ^ 2 := by ring
    _ ≤ 8 * (L * (1 / s) * T + L ^ 2 + L * A * (1 / s)) := by
        nlinarith [mul_nonneg (mul_nonneg hL0 ht0) hT0,
          mul_nonneg (mul_nonneg hL0 ht0) (by linarith : (0 : ℝ) ≤ A - 1), sq_nonneg L]
end Zhan1122_wellKnown_helpers

/-- LEAF: page 263, the display chain from `S(α; N, A)` to `≪ L q^{-1/2} Σ_{χ≠χ₀} |…| + L² +
L A q^{-1/2}`: drop `(n, q) > 1` at cost `O(L²)`, expand `e(an/q)` in characters, Gauss sums.
Class MEDIUM. -/
theorem wellKnown_leaf : WellKnown := wellKnown_proof

/-- PROVED, page 263, "Hence, if we take `c₂ ≥ 2B + 1`, it is sufficient to show (3.1)": the
small range estimate follows from the well-known display and (3.1), using `L^{c₂} ≤ q`,
`A ≥ L^{c₃}` and `q ≤ τ ≤ N`. QUESTION: with `c₂ = 2B + 1` the term `L A q^{-1/2}` is only
`≪ A L^{1/2-B}`; the proof takes `c₂ ≥ 2B + 2`, harmless since `c₂` is free. -/
theorem smallRange_of_wellKnown_eq31 (hW : WellKnown) (h31 : Eq31) : SmallRange := by
  intro B hB
  obtain ⟨c1m, h31⟩ := h31 B hB
  refine ⟨max c1m 0, fun c1 hc1 => ?_⟩
  obtain ⟨c2m, h31'⟩ := h31 c1 (le_trans (le_max_left _ _) hc1)
  have hc10 : 0 ≤ c1 := le_trans (le_max_right _ _) hc1
  refine ⟨max c2m (2 * B + 2), fun c2 hc2 => ?_⟩
  obtain ⟨c3, hc3, K, N₀, e⟩ := h31' c2 (le_trans (le_max_left _ _) hc2)
  have hc2B : 2 * B + 2 ≤ c2 := le_trans (le_max_right _ _) hc2
  obtain ⟨KW, NW, eW⟩ := hW
  refine ⟨max c3 (B + 2), lt_of_lt_of_le hc3 (le_max_left _ _), max KW 0 * (max K 0 + 2),
    max (max N₀ NW) 3, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  beta_reduce at hlo hhi
  obtain ⟨hα, hgcd, hlam, hq1, hqτ⟩ := hcond
  have : NeZero q := ⟨by omega⟩
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNW : NW ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  set L := Real.log (N : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  have hLpos : 0 < L := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNp1 : 1 ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlo' : (N : ℝ) ^ (3 / 5 : ℝ) * L ^ c3 ≤ A :=
    le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)) (by positivity)) hlo
  have hAL : L ^ (B + 2) ≤ A :=
    le_trans (le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right c3 _))
      (le_mul_of_one_le_left (by positivity) hNp1)) hlo
  have hA1 : 1 ≤ A := le_trans (Real.one_le_rpow hL1 (by linarith)) hAL
  have hAN : A ≤ N := by
    refine le_trans hhi ?_
    calc (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hqN : (q : ℝ) ≤ N := by
    refine le_trans hqτ ?_
    have h1 : L ^ (-c1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    have h2 : A ^ 2 / N ≤ N := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc A ^ 2 / N * L ^ (-c1) ≤ A ^ 2 / N * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ N := by linarith
  have hW' := eW N A α lam a q hNW hA1 hAN hα hgcd hqN
  have h31v := e N A lam q hN0 ⟨hlo', hhi, hq1, hq, hqτ, hlam⟩
  set Sc := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
    ‖Schi χ lam N A‖ with hSdef
  have hS0 : 0 ≤ Sc := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hLB : 0 ≤ L ^ (-B) := Real.rpow_nonneg hLpos.le _
  have hX : 0 ≤ A * L ^ (-B) := mul_nonneg (by linarith) hLB
  -- identities
  have eL : L * L ^ (-B - 1) = L ^ (-B) := by
    have := Real.rpow_add hLpos 1 (-B - 1)
    rw [Real.rpow_one] at this; rw [← this]; congr 1; ring
  have eL2 : L ^ (2 : ℝ) = L ^ (B + 2) * L ^ (-B) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have hqh : 0 < (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have eq : (q : ℝ) ^ (-(1 / 2) : ℝ) = ((q : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hq0.le _
  have hqL : L ^ (B + 1) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : L ^ (2 * B + 2) ≤ q :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hL1 hc2B) hq
    have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← Real.rpow_mul hLpos.le] at h2
    have : (2 * B + 2) * (1 / 2) = B + 1 := by ring
    rwa [this] at h2
  have hqinv : (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ L ^ (-B - 1) := by
    rw [eq, show -B - 1 = -(B + 1) by ring, Real.rpow_neg hLpos.le]
    exact inv_anti₀ (by positivity) hqL
  have T1 : L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc ≤ max K 0 * (A * L ^ (-B)) := by
    have hs : Sc ≤ max K 0 * (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1) := by
      refine le_trans h31v ?_
      have : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1) := by positivity
      have := mul_le_mul_of_nonneg_right (le_max_left K 0) this
      simpa [mul_assoc] using this
    have h0 : 0 ≤ L * (q : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    calc L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc
        ≤ L * (q : ℝ) ^ (-(1 / 2) : ℝ) * (max K 0 * (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) :=
          mul_le_mul_of_nonneg_left hs h0
      _ = max K 0 * (A * (L * L ^ (-B - 1))) *
            ((q : ℝ) ^ (1 / 2 : ℝ))⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ) := by rw [eq]; ring
      _ = max K 0 * (A * L ^ (-B)) := by
          rw [eL, mul_assoc _ _ ((q : ℝ) ^ (1 / 2 : ℝ)), inv_mul_cancel₀ hqh.ne', mul_one]
  have T2 : L ^ (2 : ℝ) ≤ A * L ^ (-B) := by
    rw [eL2]; exact mul_le_mul_of_nonneg_right hAL hLB
  have T3 : L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ A * L ^ (-B) := by
    calc L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ L * A * L ^ (-B - 1) :=
          mul_le_mul_of_nonneg_left hqinv (by positivity)
      _ = A * (L * L ^ (-B - 1)) := by ring
      _ = A * L ^ (-B) := by rw [eL]
  have hY0 : 0 ≤ L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
      L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have hY : L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
      L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ (max K 0 + 2) * (A * L ^ (-B)) := by
    nlinarith
  calc ‖Sexp α N A‖ ≤ KW * (L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
        L * A * (q : ℝ) ^ (-(1 / 2) : ℝ)) := hW'
    _ ≤ max KW 0 * (L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
        L * A * (q : ℝ) ^ (-(1 / 2) : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY0
    _ ≤ max KW 0 * ((max K 0 + 2) * (A * L ^ (-B))) :=
        mul_le_mul_of_nonneg_left hY (le_max_right _ _)
    _ = max KW 0 * (max K 0 + 2) * A * L ^ (-B) := by ring

/-- PROVED helper for the support argument of Heath-Brown's identity, page 263: if `f` vanishes
on `n ≤ a` and `g` on `n ≤ b`, then `f * g` vanishes on `n ≤ ab`. -/
theorem af_mul_vanish (f g : ArithmeticFunction ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n : ℕ, (n : ℝ) ≤ a → f n = 0) (hg : ∀ n : ℕ, (n : ℝ) ≤ b → g n = 0) :
    ∀ n : ℕ, (n : ℝ) ≤ a * b → (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h : (x.1 : ℝ) ≤ a
  · simp [hf _ h]
  by_cases h' : (x.2 : ℝ) ≤ b
  · simp [hg _ h']
  exfalso
  push Not at h h'
  have e : (n : ℝ) = x.1 * x.2 := by exact_mod_cast hx.1.symm
  have := mul_lt_mul'' h h' ha hb
  linarith

/-- Evaluation at `n` as an additive map, a helper for reading the identity of page 263
coefficientwise. -/
def evalHom (n : ℕ) : ArithmeticFunction ℝ →+ ℝ :=
  { toFun := fun f => f n, map_zero' := rfl, map_add' := fun _ _ => rfl }

/-- PROVED, page 263, Heath-Brown's identity
`-ζ'/ζ = Σ_{j=1}^k C(k,j) (-1)^{j-1} ζ' ζ^{j-1} M^j - (ζ'/ζ)(1 - ζM)^k`, `M = M_X`, read
coefficientwise for `n ≤ X^k`, where the last term has no coefficient:
`Λ(n) = Σ_{j=1}^k (-1)^{j-1} C(k,j) (log * ζ^{j-1} * M_X^j)(n)`. The paper takes `k = 10`,
`X = N^{1/10}`, so `X ≥ 1`; the hypothesis `1 ≤ X` is needed, since for `X = -5`, `k = 2`
the truncation `M_X` is `0` and the identity would force `Λ(n) = 0` for `n ≤ 25`. -/
theorem heathBrown_identity (k : ℕ) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) (hn : 1 ≤ n)
    (hnX : (n : ℝ) ≤ X ^ k) :
    (Λ n : ℝ) = ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * (k.choose j : ℝ) *
      ((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) *
        muTrunc X ^ j) n) := by
  set Z : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ) with hZ
  set M := muTrunc X with hM
  set E : ArithmeticFunction ℝ := 1 - Z * M with hE
  -- E vanishes up to X
  have hE0 : ∀ m : ℕ, (m : ℝ) ≤ X → E m = 0 := by
    intro m hm
    have h1 : (Z * M) m = (Z * (μ : ArithmeticFunction ℝ)) m := by
      rw [hZ, ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hile : i ≤ m := Nat.divisor_le hi
      have : (i : ℝ) ≤ X := le_trans (by exact_mod_cast hile) hm
      simp [hM, muTrunc, this]
    rw [hE, sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, h1, hZ,
      ArithmeticFunction.coe_zeta_mul_coe_moebius]; ring
  have hEk : ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ, (m : ℝ) ≤ X ^ j → (E ^ j) m = 0 := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simpa using hE0
      · rw [pow_succ]
        exact af_mul_vanish _ _ _ _ (by positivity) (by linarith) (ih hpos) hE0
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have : n = 1 := by
      have : (n : ℝ) ≤ 1 := by simpa using hnX
      have : n ≤ 1 := by exact_mod_cast this
      omega
    subst this; simp
  have hΛ1 : ∀ m : ℕ, (m : ℝ) ≤ 1 → (Λ m : ℝ) = 0 := by
    intro m hm
    have : m ≤ 1 := by exact_mod_cast hm
    interval_cases m <;> simp
  have hvan : ((Λ : ArithmeticFunction ℝ) * E ^ k) n = 0 :=
    af_mul_vanish _ _ 1 (X ^ k) zero_le_one (by positivity) hΛ1 (hEk k hk) n (by simpa using hnX)
  have hIcc : Finset.Icc 1 k = Finset.Ico (0 + 1) (k + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hpow : 1 - E ^ k = ∑ j ∈ Finset.Icc 1 k,
      (((-1 : ℤ) ^ (j - 1) * (k.choose j : ℤ) : ℤ) : ArithmeticFunction ℝ) * (Z * M) ^ j := by
    have hE' : E = -(Z * M) + 1 := by rw [hE]; ring
    rw [hE', add_pow, Finset.sum_range_succ', hIcc, ← Finset.sum_Ico_add', ← Finset.range_eq_Ico]
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    rw [sub_add_cancel_right, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [neg_pow]
    push_cast
    ring
  have hring : (Λ : ArithmeticFunction ℝ) * (1 - E ^ k) = ∑ j ∈ Finset.Icc 1 k,
      (((-1 : ℤ) ^ (j - 1) * (k.choose j : ℤ) : ℤ) : ArithmeticFunction ℝ) *
        (ArithmeticFunction.log * Z ^ (j - 1) * M ^ j) := by
    rw [hpow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    rw [← ArithmeticFunction.vonMangoldt_mul_zeta, Nat.add_sub_cancel]
    ring
  have hsplit : (Λ n : ℝ) = ((Λ : ArithmeticFunction ℝ) * (1 - E ^ k)) n +
      ((Λ : ArithmeticFunction ℝ) * E ^ k) n := by
    rw [← ArithmeticFunction.add_apply, ← mul_add, sub_add_cancel, mul_one]
  rw [hsplit, hvan, add_zero, hring]
  change evalHom n (∑ j ∈ Finset.Icc 1 k, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  push_cast
  rfl

/-- Display (3.8), page 265, with the factor `A` restored on the right:
`Σ_{χ≠χ₀} ∫_{-T}^{T} min(A, N / min_u |t + 2πλu|) |F(1/2+it, χ)| dt ≪ (qN)^{1/2} A L^{-B-c₀}`,
for every decomposition satisfying (3.5) and `T` from (3.7). -/
def Eq38 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ,
    ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Icc (-Tcut q N A lam ε) (Tcut q N A lam ε),
          wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A * Real.log N ^ (-B - c0)

/-- LEAF: pages 263 to 265, displays (3.2) to (3.7) and Lemma 1: Heath-Brown's identity with
`k = 10`, Perron's formula (3.3), dyadic splitting (3.4) and (3.5), the line shift to
`Re s = 1/2`, partial summation against `e(λu)` and Lemma 1 for the inner `u` integral reduce
(3.1) to (3.8). Class HARD. -/
theorem eq31_of_eq38_leaf (h38 : Eq38) : Eq31 := by
  sorry

/-- Display (3.11), page 265: `Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} |F(1/2+it, χ)| dt ≪ (qN)^{1/2} L^{-B-c₀}`
for `|T₁| ≤ 2T₀`, `H = N A⁻¹`. -/
def Eq311 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ,
    ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T1 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → |T1| ≤ 2 * T0cut N A lam →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Ioc T1 (T1 + N / A), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * Real.log N ^ (-B - c0)

/-- Display (3.12), page 265: `Σ_{χ≠χ₀} ∫_{T₂}^{2T₂} |F(1/2+it, χ)| dt ≪ (q N⁻¹)^{1/2} A T₂
L^{-B-c₀}` for `T₀ ≤ |T₂| ≤ 2T`; the range between `T₂` and `2T₂` is taken unoriented and the
right side uses `|T₂|`. -/
def Eq312 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ,
    ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)

section Zhan1122_eq38_of_eq311_eq312_helpers
open MeasureTheory
/-- The weight of (3.8) is nonnegative. -/
private theorem wt38_nonneg' (N : ℕ) (A lam t : ℝ) (hA : 0 ≤ A) : 0 ≤ wt38 N A lam t := by
  unfold wt38
  simp only
  have hm : 0 ≤ sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N) :=
    Real.sInf_nonneg (by rintro _ ⟨u, _, rfl⟩; exact abs_nonneg _)
  split_ifs
  · exact hA
  · exact le_min hA (div_nonneg (Nat.cast_nonneg _) hm)

/-- The weight of (3.8) is at most `A`. -/
private theorem wt38_le_A (N : ℕ) (A lam t : ℝ) : wt38 N A lam t ≤ A := by
  unfold wt38
  simp only
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- If `|t + 2πλu| ≥ μ > 0` on `[N - A, N]` then the weight of (3.8) is at most `N/μ`. -/
private theorem wt38_le_of (N : ℕ) (A lam t mu38 : ℝ) (hA : 0 ≤ A) (hμ : 0 < mu38)
    (h : ∀ u ∈ Set.Icc ((N : ℝ) - A) N, mu38 ≤ |t + 2 * π * lam * u|) :
    wt38 N A lam t ≤ N / mu38 := by
  unfold wt38
  simp only
  have hne : (Set.Icc ((N : ℝ) - A) N).Nonempty := ⟨N, by constructor <;> linarith⟩
  have hm : mu38 ≤ sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N) :=
    le_csInf (hne.image _) (by rintro _ ⟨u, hu, rfl⟩; exact h u hu)
  rw [if_neg (by linarith)]
  exact (min_le_right _ _).trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hμ hm)

/-- `F(1/2 + it, χ)` of display (3.6) is continuous in `t`. -/
private theorem Fprod_continuous {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => Fprod Nv χ (1 / 2 + t * Complex.I)) := by
  unfold Fprod fj
  apply continuous_finsetProd
  intro j _
  apply continuous_finsetSum
  intro n hn
  have hn1 : 1 ≤ n := by
    simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

/-- A finite covering bound: if `w ≤ Σ cᵢ 1_{Iᵢ}` on `[a, b]`, then
`∫_a^b w f ≤ Σ cᵢ ∫_{Iᵢ} f` for nonnegative `w`, `f` with `f` integrable on each `Iᵢ`. -/
private theorem integral_le_pieces {ι : Type*} (s : Finset ι) (I : ι → Set ℝ) (c : ι → ℝ)
    (w f : ℝ → ℝ) (a b : ℝ) (hI : ∀ i, MeasurableSet (I i))
    (hfI : ∀ i ∈ s, IntegrableOn f (I i)) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hw : ∀ t, 0 ≤ w t) (hf : ∀ t, 0 ≤ f t)
    (hcov : ∀ t ∈ Set.Icc a b, w t ≤ ∑ i ∈ s, (I i).indicator (fun _ => c i) t) :
    ∫ t in Set.Icc a b, w t * f t ≤ ∑ i ∈ s, c i * ∫ t in I i, f t := by
  set G : ℝ → ℝ := fun t => ∑ i ∈ s, (I i).indicator (fun t => c i * f t) t with hG
  have hGi : Integrable G := by
    apply integrable_finsetSum
    intro i hi
    exact (integrable_indicator_iff (hI i)).2 ((hfI i hi).const_mul (c i))
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    apply Finset.sum_nonneg
    intro i hi
    exact Set.indicator_nonneg (fun t _ => mul_nonneg (hc i hi) (hf t)) t
  have h1 : ∫ t in Set.Icc a b, w t * f t ≤ ∫ t in Set.Icc a b, G t := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => mul_nonneg (hw t) (hf t))
    · exact hGi.integrableOn
    · refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
      have := mul_le_mul_of_nonneg_right (hcov t ht) (hf t)
      refine this.trans (le_of_eq ?_)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hti : t ∈ I i
      · simp [Set.indicator_of_mem hti]
      · simp [Set.indicator_of_notMem hti]
  have h2 : ∫ t in Set.Icc a b, G t ≤ ∫ t, G t :=
    setIntegral_le_integral hGi (Filter.Eventually.of_forall hG0)
  have h3 : ∫ t, G t = ∑ i ∈ s, c i * ∫ t in I i, f t := by
    rw [hG, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hI i), integral_const_mul]
    · intro i hi
      exact (integrable_indicator_iff (hI i)).2 ((hfI i hi).const_mul (c i))
  linarith

/-- The harmonic sum with the `m = 0` term read as `1`: `Σ_{m ≤ R} 1/max(1, m) ≤ 2 + log R`. -/
private theorem sum_inv_max_le (R : ℕ) :
    ∑ m ∈ Finset.range (R + 1), 1 / max 1 (m : ℝ) ≤ 2 + Real.log R := by
  rw [Finset.sum_range_succ']
  have hh := harmonic_le_one_add_log R
  have hcast : ((harmonic R : ℚ) : ℝ) = ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
    simp [harmonic, Rat.cast_sum]
  have heq : ∑ i ∈ Finset.range R, 1 / max 1 (((i + 1 : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [max_eq_right (by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])]
    push_cast; ring
  rw [heq, ← hcast]
  simp only [Nat.cast_zero, max_eq_left (zero_le_one' ℝ), div_one]
  linarith

/-- Dyadic location: every `x > 1` has `2^j < x ≤ 2^{j+1}` for some `j`. -/
private theorem exists_two_pow_between (x : ℝ) (hx : 1 < x) :
    ∃ j : ℕ, (2 : ℝ) ^ j < x ∧ x ≤ 2 ^ (j + 1) := by
  classical
  have hex : ∃ n : ℕ, x ≤ (2 : ℝ) ^ n := (pow_unbounded_of_one_lt x (by norm_num : (1:ℝ) < 2)).imp fun _ h => h.le
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.find hex := ⟨_, rfl⟩
  have hspec : x ≤ (2 : ℝ) ^ n := hn ▸ Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hspec
    linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨j, ?_, hspec⟩
  by_contra hcon
  push_neg at hcon
  have := Nat.find_min hex (show j < Nat.find hex by omega)
  exact this hcon

set_option maxHeartbeats 2000000 in
/-- Page 265, displays (3.9) and (3.10): (3.11) and (3.12) give (3.8). The range `|t| ≤ T₀` is
cut into the intervals `(s₀ + mH, s₀ + (m+1)H]` and `(s₀ - (m+1)H, s₀ - mH]`, `s₀ = -2πλN`,
`H = N/A`, with weight `2A/m`; the range `T₀ < |t| ≤ T` into `±(T₀2^j, T₀2^{j+1}]` with weight
`2N/(T₀2^j)`. Both inputs are used with `c₀ + 1`. -/
private theorem eq38_of_eq311_eq312_proof (h311 : Eq311) (h312 : Eq312) : Eq38 := by
  intro B hB c0 hc0 ε hε
  obtain ⟨c1a, hc1a⟩ := h311 B hB (c0 + 1) (by linarith)
  obtain ⟨c1b, hc1b⟩ := h312 B hB (c0 + 1) (by linarith) ε hε
  refine ⟨max (max c1a c1b) 0, fun c1 hc1 => ?_⟩
  have hc1a' : c1a ≤ c1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc1
  have hc1b' : c1b ≤ c1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc1
  have hc10 : 0 ≤ c1 := le_trans (le_max_right _ _) hc1
  obtain ⟨c2a, hc2a⟩ := hc1a c1 hc1a'
  obtain ⟨c2b, hc2b⟩ := hc1b c1 hc1b'
  refine ⟨max (max c2a c2b) (c1 + 1), fun c2 hc2 => ?_⟩
  have hc2a' : c2a ≤ c2 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc2
  have hc2b' : c2b ≤ c2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc2
  have hc21 : c1 + 1 ≤ c2 := le_trans (le_max_right _ _) hc2
  obtain ⟨c3a, hc3a, K1, N1, H1⟩ := hc2a c2 hc2a'
  obtain ⟨c3b, hc3b, K2, N2, H2⟩ := hc2b c2 hc2b'
  refine ⟨max c3a c3b, lt_max_of_lt_left hc3a,
    12 * max K1 0 + 4 * (3 + 4 * ε) * max K2 0, max (max N1 N2) (Real.exp 20), ?_⟩
  intro N A lam q _ Nv hN hyp hc
  have hNa : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNe : Real.exp 20 ≤ N := le_trans (le_max_right _ _) hN
  have Npos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hNe
  have hexp : (21 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNbig : (21 : ℝ) ≤ N := by linarith
  have hL20 : 20 ≤ Real.log N := (Real.le_log_iff_exp_le Npos).2 hNe
  set L := Real.log N with hLdef
  have Lpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  obtain ⟨hA1, hA2, hq1, hq2, hq3, hlam⟩ := hyp
  have hc3mono : ∀ c3' ≤ max c3a c3b, (N : ℝ) ^ (3 / 5 : ℝ) * L ^ c3' ≤ A := fun c3' h =>
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 h)
      (Real.rpow_nonneg Npos.le _)) hA1
  have hypa : Hyp2 c1 c2 c3a N A lam q :=
    ⟨hc3mono _ (le_max_left _ _), hA2, hq1, hq2, hq3, hlam⟩
  have hypb : Hyp2 c1 c2 c3b N A lam q :=
    ⟨hc3mono _ (le_max_right _ _), hA2, hq1, hq2, hq3, hlam⟩
  have hA1' : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have h2 : (1 : ℝ) ≤ L ^ (max c3a c3b) := Real.one_le_rpow hL1 (le_max_of_le_left hc3a.le)
    nlinarith
  have Apos : 0 < A := by linarith
  have hAN : A ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  set H := (N : ℝ) / A with hHdef
  have Hpos : 0 < H := div_pos Npos Apos
  have hHN : H ≤ N := div_le_self Npos.le hA1'
  have hpi4 : π ≤ 4 := Real.pi_le_four
  have hpi3 : 3 < π := Real.pi_gt_three
  -- `4π|λ|A ≤ H`, from `|λ| ≤ 1/(qτ)`, `q ≥ L^{c₂}`, `c₂ ≥ c₁ + 1` and `L ≥ 4π`
  have hlamb : 4 * π * |lam| * A ≤ H := by
    have hτpos : 0 < A ^ 2 / N * L := by positivity
    have hLc : L ≤ L ^ c2 * L ^ (-c1) := by
      rw [← Real.rpow_add Lpos]
      calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ ≤ L ^ (c2 + -c1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hX : A ^ 2 / N * L ≤ q * (A ^ 2 / N * L ^ (-c1)) := by
      calc A ^ 2 / N * L ≤ A ^ 2 / N * (L ^ c2 * L ^ (-c1)) :=
            mul_le_mul_of_nonneg_left hLc (by positivity)
        _ = L ^ c2 * (A ^ 2 / N * L ^ (-c1)) := by ring
        _ ≤ q * (A ^ 2 / N * L ^ (-c1)) :=
            mul_le_mul_of_nonneg_right hq2 (by positivity)
    have hl : |lam| ≤ 1 / (A ^ 2 / N * L) := hlam.trans (one_div_le_one_div_of_le hτpos hX)
    have e : 4 * π * (1 / (A ^ 2 / N * L)) * A = (4 * π / L) * H := by
      rw [hHdef]; field_simp
    have h4 : 4 * π / L ≤ 1 := by rw [div_le_one Lpos]; linarith
    calc 4 * π * |lam| * A ≤ 4 * π * (1 / (A ^ 2 / N * L)) * A := by gcongr
      _ = (4 * π / L) * H := e
      _ ≤ 1 * H := mul_le_mul_of_nonneg_right h4 Hpos.le
      _ = H := one_mul H
  set s0 : ℝ := -2 * π * lam * N with hs0def
  set T0 := T0cut N A lam with hT0def
  set T := Tcut q N A lam ε with hTdef
  have hT0 : T0 = 4 * π * (|lam| * N + H) := rfl
  have hlN : 0 ≤ |lam| * N := by positivity
  have hs0 : |s0| = 2 * π * |lam| * N := by
    rw [hs0def, show -2 * π * lam * (N : ℝ) = -(2 * π * N * lam) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π * N)]
    ring
  have hpH : 0 ≤ π * H := by positivity
  have hs0T : |s0| ≤ T0 / 2 := by rw [hs0]; linarith [hT0, hpH]
  have hHT0 : 4 * H ≤ T0 := by
    nlinarith [hT0, mul_pos (show (0 : ℝ) < π - 1 by linarith) Hpos,
      mul_nonneg Real.pi_pos.le hlN]
  have T0pos : 0 < T0 := by linarith
  have hs0b := abs_le.1 hs0T
  -- pointwise bounds for the weight
  have hw0 : ∀ t, 0 ≤ wt38 N A lam t := fun t => wt38_nonneg' N A lam t Apos.le
  have hwA : ∀ t, wt38 N A lam t ≤ A := fun t => wt38_le_A N A lam t
  have hwfar : ∀ t, H ≤ |t - s0| → wt38 N A lam t ≤ 2 * N / |t - s0| := by
    intro t ht
    have hpos : 0 < |t - s0| / 2 := by linarith
    have hb0 := wt38_le_of N A lam t (|t - s0| / 2) Apos.le hpos (by
      intro u hu
      have hu1 : |u - N| ≤ A := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      have hb : |2 * π * lam * (u - N)| ≤ H / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        have := mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 2 * π * |lam|)
        linarith
      have he : t + 2 * π * lam * u = (t - s0) - (-(2 * π * lam * (u - N))) := by
        rw [hs0def]; ring
      rw [he]
      have := abs_sub_abs_le_abs_sub (t - s0) (-(2 * π * lam * (u - N)))
      rw [abs_neg] at this
      linarith)
    calc wt38 N A lam t ≤ N / (|t - s0| / 2) := hb0
      _ = 2 * N / |t - s0| := by rw [div_div_eq_mul_div]; ring
  have hwbig : ∀ t, T0 ≤ |t| → wt38 N A lam t ≤ 2 * N / |t| := by
    intro t ht
    have hpos : 0 < |t| / 2 := by linarith
    have hb0 := wt38_le_of N A lam t (|t| / 2) Apos.le hpos (by
      intro u hu
      have hu0 : 0 ≤ u := by linarith [hu.1]
      have hu1 : |u| ≤ N := by rw [abs_of_nonneg hu0]; exact hu.2
      have hb : |2 * π * lam * u| ≤ T0 / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        have := mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 2 * π * |lam|)
        linarith [hT0, hpH]
      have := abs_sub_abs_le_abs_sub t (-(2 * π * lam * u))
      rw [abs_neg, sub_neg_eq_add] at this
      linarith)
    calc wt38 N A lam t ≤ N / (|t| / 2) := hb0
      _ = 2 * N / |t| := by rw [div_div_eq_mul_div]; ring
  have hwm : ∀ (m : ℕ) (t : ℝ), (m : ℝ) * H ≤ |t - s0| →
      wt38 N A lam t ≤ 2 * A / max 1 (m : ℝ) := by
    intro m t ht
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Nat.cast_zero, max_eq_left zero_le_one, div_one]
      linarith [hwA t]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [max_eq_right hm1]
      have hH : H ≤ |t - s0| := le_trans (by nlinarith) ht
      have hpos : 0 < (m : ℝ) * H := by positivity
      calc wt38 N A lam t ≤ 2 * N / |t - s0| := hwfar t hH
        _ ≤ 2 * N / ((m : ℝ) * H) := div_le_div_of_nonneg_left (by positivity) hpos ht
        _ = 2 * A / m := by rw [hHdef]; field_simp
  -- the pieces
  set R := ⌈2 * T0 / H⌉₊ + 1 with hRdef
  set M := ⌊2 * (1 + 2 * ε) * L⌋₊ + 1 with hMdef
  let T1p : ℕ → ℝ := fun m => s0 + m * H
  let T1n : ℕ → ℝ := fun m => s0 - (m + 1) * H
  let T2p : ℕ → ℝ := fun j => T0 * 2 ^ j
  have hT2pos : ∀ j, 0 < T2p j := fun j => mul_pos T0pos (by positivity)
  let I : (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) → Set ℝ :=
    Sum.elim (Sum.elim (fun m => Set.Ioc (T1p m) (T1p m + H))
        (fun m => Set.Ioc (T1n m) (T1n m + H)))
      (Sum.elim (fun j => Set.uIoc (T2p j) (2 * T2p j))
        (fun j => Set.uIoc (-T2p j) (2 * -T2p j)))
  let c : (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) → ℝ :=
    Sum.elim (Sum.elim (fun m => if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
        (fun m => if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0))
      (Sum.elim (fun j => if T2p j ≤ T then 2 * N / T2p j else 0)
        (fun j => if T2p j ≤ T then 2 * N / T2p j else 0))
  let s : Finset ((ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ)) :=
    ((range R).disjSum (range R)).disjSum ((range M).disjSum (range M))
  have hmaxpos : ∀ m : ℕ, (0 : ℝ) < max 1 (m : ℝ) := fun m => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    rcases i with (m | m) | (j | j)
    · show 0 ≤ (if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
      split_ifs
      · exact div_nonneg (by linarith) (hmaxpos m).le
      · exact le_rfl
    · show 0 ≤ (if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
      split_ifs
      · exact div_nonneg (by linarith) (hmaxpos m).le
      · exact le_rfl
    · show 0 ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
      split_ifs
      · exact div_nonneg (by positivity) (hT2pos j).le
      · exact le_rfl
    · show 0 ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
      split_ifs
      · exact div_nonneg (by positivity) (hT2pos j).le
      · exact le_rfl
  -- the dyadic range has `≪ L` pieces
  have hNq : (q : ℝ) ≤ N := by
    have hLc1 : L ^ (-c1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    have h2 : A ^ 2 / N ≤ N := by rw [div_le_iff₀ Npos]; nlinarith
    calc (q : ℝ) ≤ A ^ 2 / N * L ^ (-c1) := hq3
      _ ≤ A ^ 2 / N * 1 := mul_le_mul_of_nonneg_left hLc1 (by positivity)
      _ ≤ N := by rw [mul_one]; exact h2
  have hTle : T ≤ N * N ^ (2 * ε) * T0 := by
    have hq12 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
      calc (q : ℝ) ^ (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hq1r (by norm_num)
        _ = q := Real.rpow_one _
        _ ≤ N := hNq
    have hin : H + |lam| * N ≤ T0 := by
      nlinarith [hT0, mul_nonneg (show (0 : ℝ) ≤ 4 * π - 1 by linarith) (add_nonneg hlN Hpos.le)]
    show (q : ℝ) ^ (1 / 2 : ℝ) * (N / A + |lam| * N) * (N : ℝ) ^ (2 * ε) ≤ _
    calc (q : ℝ) ^ (1 / 2 : ℝ) * (N / A + |lam| * N) * (N : ℝ) ^ (2 * ε)
        ≤ N * T0 * (N : ℝ) ^ (2 * ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hq12 hin (by positivity) Npos.le)
            (Real.rpow_nonneg Npos.le _)
      _ = N * N ^ (2 * ε) * T0 := by ring
  have hjM : ∀ j : ℕ, (2 : ℝ) ^ j ≤ N * N ^ (2 * ε) → j ∈ range M := by
    intro j hj
    have hlog : (j : ℝ) * Real.log 2 ≤ L + 2 * ε * L := by
      have := Real.log_le_log (by positivity) hj
      rw [Real.log_pow, Real.log_mul Npos.ne' (Real.rpow_pos_of_pos Npos _).ne',
        Real.log_rpow Npos] at this
      linarith
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjx : (j : ℝ) ≤ 2 * (1 + 2 * ε) * L := by
      nlinarith [mul_nonneg hj0 (le_of_lt (sub_pos.2 hl2))]
    rw [Finset.mem_range, hMdef]
    have := Nat.le_floor hjx
    omega
  have hTT0 : ∀ t, t ≤ T → t / T0 ≤ N * N ^ (2 * ε) := by
    intro t ht
    rw [div_le_iff₀ T0pos]
    linarith
  -- every `t` in `[-T, T]` lies in a piece whose weight dominates `wt38`
  have hcov : ∀ t ∈ Set.Icc (-T) T,
      wt38 N A lam t ≤ ∑ i ∈ s, (I i).indicator (fun _ => c i) t := by
    intro t ht
    have hpick : ∀ i ∈ s, t ∈ I i → wt38 N A lam t ≤ c i →
        wt38 N A lam t ≤ ∑ i ∈ s, (I i).indicator (fun _ => c i) t := by
      intro i hi hti hwc
      refine hwc.trans (le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun i => (I i).indicator (fun _ => c i) t)
        (fun k _ => Set.indicator_nonneg (fun _ _ => hc0 k) t) hi))
      show c i = (I i).indicator (fun _ => c i) t
      rw [Set.indicator_of_mem hti]
    have hRb : ∀ m : ℕ, (m : ℝ) ≤ 2 * T0 / H → m ∈ range R := by
      intro m hm
      rw [Finset.mem_range, hRdef]
      have h1 : (m : ℝ) ≤ ⌈2 * T0 / H⌉₊ := hm.trans (Nat.le_ceil _)
      have h2 : m ≤ ⌈2 * T0 / H⌉₊ := by exact_mod_cast h1
      omega
    by_cases hsmall : |t| ≤ T0
    · have ht1 := abs_le.1 hsmall
      by_cases hts : s0 < t
      · set x := (t - s0) / H with hx
        have hxpos : 0 < x := div_pos (by linarith) Hpos
        have hxH : x * H = t - s0 := by rw [hx]; field_simp
        have hcx : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.2 hxpos).ne'
        set m := ⌈x⌉₊ - 1 with hm
        have hmc' : m + 1 = ⌈x⌉₊ := by omega
        have hmc : (m : ℝ) + 1 = ⌈x⌉₊ := by exact_mod_cast hmc'
        have hlt : (m : ℝ) < x := by have := Nat.ceil_lt_add_one hxpos.le; linarith
        have hle : x ≤ (m : ℝ) + 1 := by rw [hmc]; exact Nat.le_ceil x
        have hA' : (m : ℝ) * H < t - s0 := by rw [← hxH]; exact mul_lt_mul_of_pos_right hlt Hpos
        have hB' : t - s0 ≤ ((m : ℝ) + 1) * H := by
          rw [← hxH]; exact mul_le_mul_of_nonneg_right hle Hpos.le
        have he : ((m : ℝ) + 1) * H = m * H + H := by ring
        have hmR : m ∈ range R := by
          apply hRb
          have hx2 : x ≤ 2 * T0 / H := by
            rw [hx]; apply div_le_div_of_nonneg_right _ Hpos.le; linarith
          linarith
        apply hpick (Sum.inl (Sum.inl m)) (by simp [s, hmR])
        · show t ∈ Set.Ioc (T1p m) (T1p m + H)
          constructor
          · show s0 + m * H < t
            linarith
          · show t ≤ s0 + m * H + H
            linarith
        · show wt38 N A lam t ≤ (if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
          rw [if_pos]
          · apply hwm m t
            rw [abs_of_pos (by linarith)]
            linarith
          · show |s0 + m * H| ≤ 2 * T0
            rw [abs_le]; constructor <;> linarith
      · push_neg at hts
        set x := (s0 - t) / H with hx
        have hx0 : 0 ≤ x := div_nonneg (by linarith) Hpos.le
        have hxH : x * H = s0 - t := by rw [hx]; field_simp
        set m := ⌊x⌋₊ with hm
        have hle : (m : ℝ) ≤ x := Nat.floor_le hx0
        have hlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
        have hA' : (m : ℝ) * H ≤ s0 - t := by
          rw [← hxH]; exact mul_le_mul_of_nonneg_right hle Hpos.le
        have hB' : s0 - t < ((m : ℝ) + 1) * H := by
          rw [← hxH]; exact mul_lt_mul_of_pos_right hlt Hpos
        have he : ((m : ℝ) + 1) * H = m * H + H := by ring
        have hmR : m ∈ range R := by
          apply hRb
          have hx2 : x ≤ 2 * T0 / H := by
            rw [hx]; apply div_le_div_of_nonneg_right _ Hpos.le; linarith
          linarith
        apply hpick (Sum.inl (Sum.inr m)) (by simp [s, hmR])
        · show t ∈ Set.Ioc (T1n m) (T1n m + H)
          constructor
          · show s0 - (m + 1) * H < t
            linarith
          · show t ≤ s0 - (m + 1) * H + H
            linarith
        · show wt38 N A lam t ≤ (if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
          rw [if_pos]
          · apply hwm m t
            rw [abs_of_nonpos (by linarith)]
            linarith
          · show |s0 - (m + 1) * H| ≤ 2 * T0
            rw [abs_le]; constructor <;> linarith
    · push_neg at hsmall
      by_cases htpos : 0 < t
      · have habs : |t| = t := abs_of_pos htpos
        rw [habs] at hsmall
        obtain ⟨j, hj1, hj2⟩ :=
          exists_two_pow_between (t / T0) (by rw [one_lt_div T0pos]; exact hsmall)
        have hT2a : T0 * 2 ^ j < t := by rwa [lt_div_iff₀ T0pos, mul_comm] at hj1
        have hT2b : t ≤ 2 * (T0 * 2 ^ j) := by
          rw [div_le_iff₀ T0pos] at hj2
          have e : (2 : ℝ) ^ (j + 1) * T0 = 2 * (T0 * 2 ^ j) := by ring
          rw [e] at hj2
          exact hj2
        have hjm : j ∈ range M := hjM j (le_trans hj1.le (hTT0 t ht.2))
        apply hpick (Sum.inr (Sum.inl j)) (by simp [s, hjm])
        · show t ∈ Set.uIoc (T2p j) (2 * T2p j)
          rw [Set.mem_uIoc]
          exact Or.inl ⟨hT2a, hT2b⟩
        · show wt38 N A lam t ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
          rw [if_pos (show T0 * 2 ^ j ≤ T by linarith [ht.2])]
          calc wt38 N A lam t ≤ 2 * N / |t| := hwbig t (by rw [habs]; linarith)
            _ ≤ 2 * N / T2p j := by
              rw [habs]
              exact div_le_div_of_nonneg_left (by positivity) (hT2pos j) hT2a.le
      · push_neg at htpos
        have habs : |t| = -t := abs_of_nonpos htpos
        rw [habs] at hsmall
        obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near
          (show 1 ≤ -t / T0 by rw [one_le_div T0pos]; linarith) (by norm_num : (1 : ℝ) < 2)
        have hT2a : T0 * 2 ^ j ≤ -t := by rwa [le_div_iff₀ T0pos, mul_comm] at hj1
        have hT2b : -t < 2 * (T0 * 2 ^ j) := by
          rw [div_lt_iff₀ T0pos] at hj2
          have e : (2 : ℝ) ^ (j + 1) * T0 = 2 * (T0 * 2 ^ j) := by ring
          rw [e] at hj2
          exact hj2
        have hjm : j ∈ range M := hjM j (le_trans hj1 (hTT0 (-t) (by linarith [ht.1])))
        apply hpick (Sum.inr (Sum.inr j)) (by simp [s, hjm])
        · show t ∈ Set.uIoc (-T2p j) (2 * -T2p j)
          rw [Set.mem_uIoc]
          right
          constructor
          · show 2 * -(T0 * 2 ^ j) < t
            linarith
          · show t ≤ -(T0 * 2 ^ j)
            linarith
        · show wt38 N A lam t ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
          rw [if_pos (show T0 * 2 ^ j ≤ T by linarith [ht.1])]
          calc wt38 N A lam t ≤ 2 * N / |t| := hwbig t (by rw [habs]; linarith)
            _ ≤ 2 * N / T2p j := by
              rw [habs]
              exact div_le_div_of_nonneg_left (by positivity) (hT2pos j) hT2a
  -- integrate
  have hf : ∀ χ : DirichletCharacter ℂ q,
      Continuous (fun t : ℝ => ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) :=
    fun χ => (Fprod_continuous Nv χ).norm
  have hIm : ∀ i, MeasurableSet (I i) := by
    intro i
    rcases i with (m | m) | (j | j)
    · exact measurableSet_Ioc
    · exact measurableSet_Ioc
    · exact measurableSet_uIoc
    · exact measurableSet_uIoc
  have hIi : ∀ χ : DirichletCharacter ℂ q, ∀ i,
      IntegrableOn (fun t : ℝ => ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) (I i) := by
    intro χ i
    rcases i with (m | m) | (j | j)
    · exact (hf χ).integrableOn_Ioc
    · exact (hf χ).integrableOn_Ioc
    · exact (hf χ).integrableOn_uIoc
    · exact (hf χ).integrableOn_uIoc
  let S : (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) → ℝ := fun i =>
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
      ∫ t in I i, ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
  have hstep : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ ∑ i ∈ s, c i * S i := by
    calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
            ∑ i ∈ s, c i * ∫ t in I i, ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ := by
          apply Finset.sum_le_sum
          intro χ _
          exact integral_le_pieces s I c (wt38 N A lam)
            (fun t => ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) (-T) T hIm
            (fun i _ => hIi χ i) (fun i _ => hc0 i) hw0 (fun t => norm_nonneg _) hcov
      _ = ∑ i ∈ s, c i * S i := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          exact (Finset.mul_sum _ _ _).symm
  -- per-piece bounds from (3.11) and (3.12)
  set E := ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A * L ^ (-B - (c0 + 1)) with hE
  have hX0 : 0 ≤ ((q : ℝ) * N) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hY0 : 0 ≤ L ^ (-B - (c0 + 1)) := Real.rpow_nonneg Lpos.le _
  have hE0 : 0 ≤ E := mul_nonneg (mul_nonneg hX0 Apos.le) hY0
  have hK1 : 0 ≤ max K1 0 := le_max_right _ _
  have hK2 : 0 ≤ max K2 0 := le_max_right _ _
  have hqN : ((q : ℝ) / N) ^ (1 / 2 : ℝ) * N = ((q : ℝ) * N) ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow (Nat.cast_nonneg _) Npos.le, Real.mul_rpow (Nat.cast_nonneg _) Npos.le]
    have hs : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add Npos]; norm_num
    have hpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos Npos _
    rw [div_mul_eq_mul_div, div_eq_iff hpos.ne', mul_assoc, hs]
  have hZ0 : 0 ≤ ((q : ℝ) / N) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hshortb : ∀ T1 : ℝ, |T1| ≤ 2 * T0 →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Ioc T1 (T1 + H), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ max K1 0 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - (c0 + 1)) := by
    intro T1 hv
    refine le_trans (H1 N A lam q Nv T1 hNa hypa hc hv) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hY0
  have hdyb : ∀ T2 : ℝ, T0 ≤ |T2| → |T2| ≤ 2 * T →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ max K2 0 * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * L ^ (-B - (c0 + 1)) := by
    intro T2 hv1 hv2
    refine le_trans (H2 N A lam q Nv T2 hNb hypb hc hv1 hv2) ?_
    have hp : 0 ≤ ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * L ^ (-B - (c0 + 1)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hZ0 Apos.le) (abs_nonneg _)) hY0
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left K2 0) hp]
  have hfam1 : ∀ m ∈ range R, c (Sum.inl (Sum.inl m)) * S (Sum.inl (Sum.inl m)) ≤
      2 / max 1 (m : ℝ) * (max K1 0 * E) := by
    intro m _
    have hm0 : (0 : ℝ) ≤ 2 / max 1 (m : ℝ) := div_nonneg (by norm_num) (hmaxpos m).le
    show (if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0) * S (Sum.inl (Sum.inl m)) ≤ _
    split_ifs with hv
    · have hb := hshortb (T1p m) hv
      calc 2 * A / max 1 (m : ℝ) * S (Sum.inl (Sum.inl m))
          ≤ 2 * A / max 1 (m : ℝ) *
              (max K1 0 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by linarith) (hmaxpos m).le)
        _ = 2 / max 1 (m : ℝ) * (max K1 0 * E) := by rw [hE]; ring
    · rw [zero_mul]; exact mul_nonneg hm0 (mul_nonneg hK1 hE0)
  have hfam2 : ∀ m ∈ range R, c (Sum.inl (Sum.inr m)) * S (Sum.inl (Sum.inr m)) ≤
      2 / max 1 (m : ℝ) * (max K1 0 * E) := by
    intro m _
    have hm0 : (0 : ℝ) ≤ 2 / max 1 (m : ℝ) := div_nonneg (by norm_num) (hmaxpos m).le
    show (if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0) * S (Sum.inl (Sum.inr m)) ≤ _
    split_ifs with hv
    · have hb := hshortb (T1n m) hv
      calc 2 * A / max 1 (m : ℝ) * S (Sum.inl (Sum.inr m))
          ≤ 2 * A / max 1 (m : ℝ) *
              (max K1 0 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by linarith) (hmaxpos m).le)
        _ = 2 / max 1 (m : ℝ) * (max K1 0 * E) := by rw [hE]; ring
    · rw [zero_mul]; exact mul_nonneg hm0 (mul_nonneg hK1 hE0)
  have hfam3 : ∀ j ∈ range M, c (Sum.inr (Sum.inl j)) * S (Sum.inr (Sum.inl j)) ≤
      2 * (max K2 0 * E) := by
    intro j _
    show (if T2p j ≤ T then 2 * N / T2p j else 0) * S (Sum.inr (Sum.inl j)) ≤ _
    have hp := hT2pos j
    split_ifs with hv
    · have hv1 : T0 ≤ |T2p j| := by
        rw [abs_of_pos hp]
        exact le_mul_of_one_le_right T0pos.le (one_le_pow₀ (by norm_num))
      have hv2 : |T2p j| ≤ 2 * T := by rw [abs_of_pos hp]; linarith
      have hb := hdyb (T2p j) hv1 hv2
      rw [abs_of_pos hp] at hb
      calc 2 * N / T2p j * S (Sum.inr (Sum.inl j))
          ≤ 2 * N / T2p j * (max K2 0 * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * T2p j *
              L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by positivity) hp.le)
        _ = 2 * (max K2 0 * ((((q : ℝ) / N) ^ (1 / 2 : ℝ) * N) * A * L ^ (-B - (c0 + 1)))) := by
            field_simp
        _ = 2 * (max K2 0 * E) := by rw [hqN]
    · rw [zero_mul]; exact mul_nonneg (by norm_num) (mul_nonneg hK2 hE0)
  have hfam4 : ∀ j ∈ range M, c (Sum.inr (Sum.inr j)) * S (Sum.inr (Sum.inr j)) ≤
      2 * (max K2 0 * E) := by
    intro j _
    show (if T2p j ≤ T then 2 * N / T2p j else 0) * S (Sum.inr (Sum.inr j)) ≤ _
    have hp := hT2pos j
    split_ifs with hv
    · have hv1 : T0 ≤ |-T2p j| := by
        rw [abs_neg, abs_of_pos hp]
        exact le_mul_of_one_le_right T0pos.le (one_le_pow₀ (by norm_num))
      have hv2 : |-T2p j| ≤ 2 * T := by rw [abs_neg, abs_of_pos hp]; linarith
      have hb := hdyb (-T2p j) hv1 hv2
      rw [abs_neg, abs_of_pos hp] at hb
      calc 2 * N / T2p j * S (Sum.inr (Sum.inr j))
          ≤ 2 * N / T2p j * (max K2 0 * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * T2p j *
              L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by positivity) hp.le)
        _ = 2 * (max K2 0 * ((((q : ℝ) / N) ^ (1 / 2 : ℝ) * N) * A * L ^ (-B - (c0 + 1)))) := by
            field_simp
        _ = 2 * (max K2 0 * E) := by rw [hqN]
    · rw [zero_mul]; exact mul_nonneg (by norm_num) (mul_nonneg hK2 hE0)
  -- the harmonic sum and the count of dyadic pieces
  have hy : 2 * T0 / H ≤ 2 * N + 32 := by
    have e : 2 * T0 / H = 8 * π * (|lam| * A) + 8 * π := by
      have hAH : A * H = N := by rw [hHdef]; field_simp
      rw [div_eq_iff Hpos.ne']
      linear_combination 2 * hT0 - 8 * π * |lam| * hAH
    rw [e]
    nlinarith
  have hypos : 0 < 2 * T0 / H := div_pos (by linarith) Hpos
  have hceil : (⌈2 * T0 / H⌉₊ : ℝ) ≤ (N : ℝ) ^ 2 := by
    have := Nat.ceil_lt_add_one hypos.le
    nlinarith
  have hlogc : Real.log (⌈2 * T0 / H⌉₊ : ℝ) ≤ 2 * L := by
    have hpos : (0 : ℝ) < ⌈2 * T0 / H⌉₊ := by exact_mod_cast Nat.ceil_pos.2 hypos
    calc Real.log (⌈2 * T0 / H⌉₊ : ℝ) ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hpos hceil
      _ = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
  have hharm : ∑ m ∈ range R, 1 / max 1 (m : ℝ) ≤ 2 + 2 * L :=
    (sum_inv_max_le ⌈2 * T0 / H⌉₊).trans (by linarith)
  have hshort : ∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E) ≤
      (2 + 2 * L) * (2 * (max K1 0 * E)) := by
    calc ∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E)
        = (∑ m ∈ range R, 1 / max 1 (m : ℝ)) * (2 * (max K1 0 * E)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m _
          ring
      _ ≤ (2 + 2 * L) * (2 * (max K1 0 * E)) :=
          mul_le_mul_of_nonneg_right hharm (by positivity)
  have hMle : (M : ℝ) ≤ (3 + 4 * ε) * L := by
    have h1 : (M : ℝ) = (⌊2 * (1 + 2 * ε) * L⌋₊ : ℝ) + 1 := by rw [hMdef]; push_cast; ring
    have h2 := Nat.floor_le (show 0 ≤ 2 * (1 + 2 * ε) * L by positivity)
    rw [h1]
    nlinarith
  have hdy : ∑ j ∈ range M, 2 * (max K2 0 * E) = M * (2 * (max K2 0 * E)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLexp : L ^ (-B - c0) = L ^ (-B - (c0 + 1)) * L := by
    rw [← Real.rpow_add_one Lpos.ne']
    congr 1
    ring
  have hsplit : ∑ i ∈ s, c i * S i =
      (∑ m ∈ range R, c (Sum.inl (Sum.inl m)) * S (Sum.inl (Sum.inl m)) +
        ∑ m ∈ range R, c (Sum.inl (Sum.inr m)) * S (Sum.inl (Sum.inr m))) +
      (∑ j ∈ range M, c (Sum.inr (Sum.inl j)) * S (Sum.inr (Sum.inl j)) +
        ∑ j ∈ range M, c (Sum.inr (Sum.inr j)) * S (Sum.inr (Sum.inr j))) := by
    simp only [s, Finset.sum_disjSum]
  have hKE1 : 0 ≤ max K1 0 * E := mul_nonneg hK1 hE0
  have hKE2 : 0 ≤ max K2 0 * E := mul_nonneg hK2 hE0
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ ∑ i ∈ s, c i * S i := hstep
    _ ≤ (∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E) +
          ∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E)) +
        (∑ j ∈ range M, 2 * (max K2 0 * E) + ∑ j ∈ range M, 2 * (max K2 0 * E)) := by
        rw [hsplit]
        exact add_le_add (add_le_add (Finset.sum_le_sum hfam1) (Finset.sum_le_sum hfam2))
          (add_le_add (Finset.sum_le_sum hfam3) (Finset.sum_le_sum hfam4))
    _ ≤ 2 * ((2 + 2 * L) * (2 * (max K1 0 * E))) + 2 * (M * (2 * (max K2 0 * E))) := by
        rw [hdy]; linarith [hshort]
    _ ≤ (12 * max K1 0 + 4 * (3 + 4 * ε) * max K2 0) * E * L := by
        have h1 := mul_le_mul_of_nonneg_right (show 4 * (2 + 2 * L) ≤ 12 * L by linarith) hKE1
        have h2 := mul_le_mul_of_nonneg_right hMle hKE2
        nlinarith
    _ = (12 * max K1 0 + 4 * (3 + 4 * ε) * max K2 0) * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A *
          Real.log N ^ (-B - c0) := by
        rw [hLexp, hE]; ring
end Zhan1122_eq38_of_eq311_eq312_helpers

/-- LEAF: page 265, displays (3.9) and (3.10): split `|t| ≤ T₀` into intervals of length
`H = N A⁻¹ ≥ 4π|λ|A`, weight `A` on the one with `|t + 2πλN| ≤ H` and `N/(kH)` on the `k`-th,
and the tail `T₀ ≤ |t| ≤ T` with weight `≪ N/|t|` cut dyadically; so (3.11) and (3.12) give
(3.8). Class MEDIUM. -/
theorem eq38_of_eq311_eq312_leaf (h311 : Eq311) (h312 : Eq312) : Eq38 :=
  eq38_of_eq311_eq312_proof h311 h312

/-- LEAF: pages 265 to 269, proof of (3.11): Propositions 1, 2, 3 with Lemmas 2, 3, 6, 7 and
(3.13) to (3.18), then Cases a) and b) on how many `N_j > N^{1/5}`. Class HARD. -/
theorem eq311_leaf : Eq311 := by
  sorry

/-- LEAF: page 269, last paragraph, proof of (3.12), "essentially the same as that of (3.11)"
with the usual power moments of `L`-functions in place of Lemmas 2 and 3. Class HARD. -/
theorem eq312_leaf : Eq312 := by
  sorry

/-! ### Assembly, PROVED from the LEAF steps -/

/-- Theorem 2 from the three ranges of pages 262 and 263: the small range `A ≤ N^{2/3}`, the
reduction of the middle range `N^{2/3} ≤ A ≤ N L⁻¹` to it, and Vinogradov's large range. -/
theorem theorem2_of_ranges (hs : SmallRange) (hr : MiddleReduction) (hl : LargeRange) :
    Theorem2 := by
  intro B hB
  obtain ⟨a1, h1⟩ := hs B hB
  obtain ⟨a3, h3⟩ := hl B hB
  obtain ⟨b1, h1'⟩ := h1 (max (max a1 a3) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨b3, h3'⟩ := h3 (max (max a1 a3) 1) (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨c3, hc3, K1, N1, e1⟩ :=
    h1' (max (max b1 b3) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨K3, N3, e3⟩ := h3' (max (max b1 b3) 1) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hc1 : (0 : ℝ) < max (max a1 a3) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc2 : (0 : ℝ) < max (max b1 b3) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K2, N2, e2⟩ := hr B _ _ c3 K1 N1 hB hc1 hc2 hc3 e1
  refine ⟨max (max a1 a3) 1, max (max b1 b3) 1, c3, hc1, hc2, hc3,
    max (max K1 K2) K3, max (max N1 N2) N3, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hA : 0 ≤ A := le_trans (by positivity) hlo
  have hX : 0 ≤ A * Real.log N ^ (-B) := mul_nonneg hA (Real.rpow_nonneg hL _)
  have key : ∀ K', K' ≤ max (max K1 K2) K3 →
      K' * A * Real.log N ^ (-B) ≤ max (max K1 K2) K3 * A * Real.log N ^ (-B) := by
    intro K' hK'
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hK' hX
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N := le_trans (le_max_right _ _) hN
  rcases le_total A ((N : ℝ) ^ (2 / 3 : ℝ)) with h | h
  · exact le_trans (e1 N A α lam a q hN1 hlo h hcond hq)
      (key _ (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rcases le_total A ((N : ℝ) / Real.log N) with h' | h'
    · exact le_trans (e2 N A α lam a q hN2 h h' hcond hq)
        (key _ (le_trans (le_max_right _ _) (le_max_left _ _)))
    · exact le_trans (e3 N A α lam a q hN3 h' hhi hcond hq) (key _ (le_max_right _ _))

/-- Theorem 2 assembled from the LEAF chain: (3.11) and (3.12) give (3.8), (3.8) gives (3.1),
(3.1) with the well-known display gives the small range, then the three ranges. Its axioms
include `sorryAx` through the LEAFs; the assembly steps themselves are proved. -/
theorem theorem2_from_leaves : Theorem2 :=
  theorem2_of_ranges
    (smallRange_of_wellKnown_eq31 wellKnown_leaf
      (eq31_of_eq38_leaf (eq38_of_eq311_eq312_leaf eq311_leaf eq312_leaf)))
    middle_reduction_leaf large_range_leaf

end

end LeanLab.Zhan1991
