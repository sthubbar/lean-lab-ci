/-
P0080 S. Hathi, arXiv 2109.13174, section 4: the assembly of Theorem 1.1 from the major arc
bound Lemma 2.1, the minor arc bound built from Lemmas 2.2, 2.3 and the bound
`|G(α)| ≤ λ₀ L` on the minor arcs, and the step `k = k' + 2`.
The analytic inputs are hypotheses on abstract real numbers `Maj N`, `Min N`, the major and
minor arc parts of `R_{k'}(N)`; nothing analytic is proved here.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Hathi2021.Statements

open Filter Topology

namespace LeanLab.Hathi2021

/-- The robust margin of `margin_l5_robust`, as a real number. -/
noncomputable def mR : ℝ :=
  ((9 / 10 - lam0 ^ 19 * (11001 / 1000) * c0 5 * (1001 / 1000) : ℚ) : ℝ)

theorem mR_pos : 0 < mR := by
  unfold mR; exact_mod_cast margin_l5_robust

theorem mR_eq : mR = 9 / 10 - (lam0 : ℝ) ^ 19 * (11001 / 1000) * (c0 5 : ℝ) * (1001 / 1000) := by
  unfold mR; push_cast; ring

/-- The section 4 inequality with explicit `o(1)` error functions: for `l = 5`, `k' = 29`,
if the major arc part is at least `0.9 · 8 J(1) N L^{29} − e₁ N L^{29}` and the minor arc part
is at most `λ₀^{19} (11 + ε)(1 + δ) J(0) 8 N c_{0,5} L^{29} + e₂ N L^{29}` in absolute value,
with `ε ≤ 1/1000`, `(1 + δ)² ≤ 1001/1000`, `J(0) ≤ (1 + δ) J(1)`, and `e₁ + e₂ < 8 J(1) mR`,
then `Maj + Min > 0`. -/
theorem section4_pos {Maj Min J0 J1 N L e1 e2 ε δ : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hJ0 : 0 ≤ J0) (hJ1 : 0 < J1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hδ0 : 0 ≤ δ) (hδ : (1 + δ) ^ 2 ≤ 1001 / 1000) (hJ : J0 ≤ (1 + δ) * J1)
    (hMaj : 9 / 10 * 8 * J1 * N * L ^ 29 - e1 * N * L ^ 29 ≤ Maj)
    (hMin : |Min| ≤ (lam0 : ℝ) ^ 19 * (11 + ε) * (1 + δ) * J0 * 8 * N * (c0 5 : ℝ) * L ^ 29
      + e2 * N * L ^ 29)
    (he : e1 + e2 < 8 * J1 * mR) : 0 < Maj + Min := by
  have hc : (0 : ℝ) ≤ (c0 5 : ℝ) := by unfold c0; norm_num
  have hl : (0 : ℝ) ≤ (lam0 : ℝ) ^ 19 := by unfold lam0; positivity
  have hP : 0 < N * L ^ 29 := by positivity
  -- (11 + ε)(1 + δ) J0 ≤ 11.001 · 1.001 · J1
  have key : (11 + ε) * (1 + δ) * J0 ≤ 11001 / 1000 * (1001 / 1000) * J1 := by
    have h1 : (1 + δ) * J0 ≤ (1 + δ) ^ 2 * J1 := by
      have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 + δ); nlinarith
    have h2 : (1 + δ) ^ 2 * J1 ≤ 1001 / 1000 * J1 := mul_le_mul_of_nonneg_right hδ hJ1.le
    have h3 : (11 + ε) * ((1 + δ) * J0) ≤ 11001 / 1000 * ((1 + δ) * J0) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hMin' : |Min| ≤ (lam0 : ℝ) ^ 19 * (c0 5 : ℝ) * (11001 / 1000 * (1001 / 1000) * J1)
      * 8 * (N * L ^ 29) + e2 * (N * L ^ 29) := by
    have : (lam0 : ℝ) ^ 19 * (11 + ε) * (1 + δ) * J0 * 8 * N * (c0 5 : ℝ) * L ^ 29
        = (lam0 : ℝ) ^ 19 * (c0 5 : ℝ) * ((11 + ε) * (1 + δ) * J0) * 8 * (N * L ^ 29) := by ring
    have hmono : (lam0 : ℝ) ^ 19 * (c0 5 : ℝ) * ((11 + ε) * (1 + δ) * J0) * 8 * (N * L ^ 29)
        ≤ (lam0 : ℝ) ^ 19 * (c0 5 : ℝ) * (11001 / 1000 * (1001 / 1000) * J1) * 8 * (N * L ^ 29) := by
      apply mul_le_mul_of_nonneg_right _ hP.le
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left key (mul_nonneg hl hc)
    linarith
  have hneg : -|Min| ≤ Min := neg_abs_le Min
  have hsum : (N * L ^ 29) * (8 * J1 * mR - (e1 + e2)) ≤ Maj + Min := by
    rw [mR_eq]; nlinarith
  have : 0 < (N * L ^ 29) * (8 * J1 * mR - (e1 + e2)) := mul_pos hP (by linarith)
  linarith

/-- The same for a sequence: if `L N → ∞`, `J(1) > 0` is fixed and the error functions tend
to 0, then `Maj N + Min N > 0` for all large `N ≡ 4 (mod 8)`. -/
theorem section4_eventually {Maj Min : ℕ → ℝ} {L : ℕ → ℝ} {J0 J1 ε δ : ℝ} {e1 e2 : ℝ → ℝ}
    (hJ0 : 0 ≤ J0) (hJ1 : 0 < J1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hδ0 : 0 ≤ δ) (hδ : (1 + δ) ^ 2 ≤ 1001 / 1000) (hJ : J0 ≤ (1 + δ) * J1)
    (hLt : Tendsto L atTop atTop)
    (he1 : Tendsto e1 atTop (𝓝 0)) (he2 : Tendsto e2 atTop (𝓝 0))
    (hMaj : ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → N % 8 = 4 →
      9 / 10 * 8 * J1 * N * L N ^ 29 - e1 (L N) * N * L N ^ 29 ≤ Maj N)
    (hMin : ∃ N₂ : ℕ, ∀ N, N₂ ≤ N → N % 8 = 4 →
      |Min N| ≤ (lam0 : ℝ) ^ 19 * (11 + ε) * (1 + δ) * J0 * 8 * N * (c0 5 : ℝ) * L N ^ 29
        + e2 (L N) * N * L N ^ 29) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → N % 8 = 4 → 0 < Maj N + Min N := by
  obtain ⟨N₁, hMaj⟩ := hMaj
  obtain ⟨N₂, hMin⟩ := hMin
  have hpos : 0 < 8 * J1 * mR := by have := mR_pos; positivity
  have hsum : Tendsto (fun x => e1 x + e2 x) atTop (𝓝 0) := by simpa using he1.add he2
  have hev : ∀ᶠ x in atTop, e1 x + e2 x < 8 * J1 * mR :=
    hsum.eventually (gt_mem_nhds hpos)
  have hev2 : ∀ᶠ N in atTop, e1 (L N) + e2 (L N) < 8 * J1 * mR ∧ 0 < L N :=
    (hLt.eventually hev).and (hLt.eventually (eventually_gt_atTop 0))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hev2
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hN h8 => ?_⟩
  have h1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have h2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have h3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have h4 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨he, hLpos⟩ := hN₃ N h3
  exact section4_pos (by exact_mod_cast h4) hLpos hJ0 hJ1 hε0 hε hδ0 hδ hJ
    (hMaj N h1 h8) (hMin N h2 h8) he

/-- Theorem 1.1 from the section 4 inputs: the major and minor arc bounds for `R_{29}`, and the
link that `Maj N + Min N > 0` gives a representation with at most 29 powers. -/
theorem theorem11_of_section4 {Maj Min : ℕ → ℝ} {L : ℕ → ℝ} {J0 J1 ε δ : ℝ}
    {e1 e2 : ℝ → ℝ}
    (hJ0 : 0 ≤ J0) (hJ1 : 0 < J1) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hδ0 : 0 ≤ δ) (hδ : (1 + δ) ^ 2 ≤ 1001 / 1000) (hJ : J0 ≤ (1 + δ) * J1)
    (hLt : Tendsto L atTop atTop)
    (he1 : Tendsto e1 atTop (𝓝 0)) (he2 : Tendsto e2 atTop (𝓝 0))
    (hMaj : ∃ N₁ : ℕ, ∀ N, N₁ ≤ N → N % 8 = 4 →
      9 / 10 * 8 * J1 * N * L N ^ 29 - e1 (L N) * N * L N ^ 29 ≤ Maj N)
    (hMin : ∃ N₂ : ℕ, ∀ N, N₂ ≤ N → N % 8 = 4 →
      |Min N| ≤ (lam0 : ℝ) ^ 19 * (11 + ε) * (1 + δ) * J0 * 8 * N * (c0 5 : ℝ) * L N ^ 29
        + e2 (L N) * N * L N ^ 29)
    (hrep : ∀ N, 0 < Maj N + Min N → FourSqAtMost 29 N) : Theorem11 := by
  obtain ⟨N₀, h⟩ := section4_eventually hJ0 hJ1 hε0 hε hδ0 hδ hJ hLt he1 he2 hMaj hMin
  exact theorem11_of_fourMod8_29 ⟨N₀, fun N h8 hN => hrep N (h N hN h8)⟩

end LeanLab.Hathi2021
