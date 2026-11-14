/-
P0069 page 22 Lemma 8, a diagnostic for the old lab strip continuation split.
The paper explicitly includes the principal pole term. The old auxiliary leaf
asserts analyticity across that pole for every character. That auxiliary
statement is false. This is a lab interface QUESTION, not a paper error.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic

namespace LeanLab.BHP1997.Decomp561i
open Complex Filter Set
open scoped Topology

/-- P0069 page 22 Lemma 8, the principal pole obstructs continuity at 1.
Use Mathlib residue one rather than a cited pole hypothesis. -/
theorem riemannZeta_not_continuousAt_one561 :
    ¬ ContinuousAt riemannZeta (1 : ℂ) := by
  intro hc
  have ht : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) (1 : ℂ) :=
    (continuousAt_id.sub continuousAt_const).mul hc
  have hz : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 0) := by
    simpa only [sub_self, zero_mul] using ht.tendsto.mono_left nhdsWithin_le_nhds
  have he : (0 : ℂ) = 1 := tendsto_nhds_unique hz riemannZeta_residue_one
  exact zero_ne_one he

/-- P0069 page 22 Lemma 8, a concrete witness against the old lab analytic strip
leaf: x equals 2 and the principal character has modulus 1. -/
theorem principal_strip_continuation_false561 :
    ¬ AnalyticOnNhd ℂ (fun s : ℂ => (1 : DirichletCharacter ℂ 1).LFunction s)
      {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log 2} := by
  intro h
  have hm : (1 : ℂ) ∈ {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log 2} := by
    simp only [Set.mem_ofPred_eq, Complex.one_re]
    constructor
    · norm_num
    · have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      linarith [one_div_pos.mpr hl]
  apply riemannZeta_not_continuousAt_one561
  simpa only [DirichletCharacter.LFunction_modOne_eq] using (h 1 hm).continuousAt

/-- P0069 page 22 Lemma 8, the exact universal type of the old lab
leaf_strip_continuation is false. This theorem imports neither that admitted
leaf nor its target module. The sealed old statement remains unchanged. -/
theorem leaf_strip_continuation_type_false561 :
    ¬ (∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q,
        AnalyticOnNhd ℂ (fun s : ℂ => χ.LFunction s)
          {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 + 1 / Real.log x}) := by
  intro h
  apply principal_strip_continuation_false561
  exact h 2 (by norm_num) 1 (by norm_num) (by norm_num) 1


/-- P0069 page 22 Lemma 8, residue one forces unboundedness on every real
segment immediately to the right of the principal pole. -/
theorem riemannZeta_not_bounded_real_segment561 {b : ℝ} (hb : 1 < b) :
    ¬ ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ b → ‖riemannZeta (σ : ℂ)‖ ≤ C := by
  rintro ⟨C, hC⟩
  have he : ∀ᶠ s : ℂ in 𝓝[≠] 1, (1 / 2 : ℝ) < ‖(s - 1) * riemannZeta s‖ := by
    exact (tendsto_norm.comp riemannZeta_residue_one).eventually
      (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < ‖(1 : ℂ)‖))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp he
  have hb0 : 0 < b - 1 := sub_pos.mpr hb
  let t : ℝ := min (δ / 2) (min ((b - 1) / 2) (1 / (4 * (|C| + 1))))
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htb : t ≤ (b - 1) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have htC : t ≤ 1 / (4 * (|C| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hσ : 1 + t ≤ b := by linarith
  have hn : ‖((1 + t : ℝ) : ℂ) - 1‖ = t := by
    rw [show (((1 + t : ℝ) : ℂ) - 1) = (t : ℂ) by push_cast; ring]
    simp [Real.norm_eq_abs, abs_of_pos ht]
  have hlarge : (1 / 2 : ℝ) < ‖((((1 + t : ℝ) : ℂ) - 1) * riemannZeta ((1 + t : ℝ) : ℂ))‖ := by
    apply hsmall
    constructor
    · simpa only [Metric.mem_ball, dist_eq_norm, hn] using htδ
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hh
      have hh' := congrArg Complex.re hh
      simp only [Complex.ofReal_re, Complex.one_re] at hh'
      linarith
  have hupper := hC (1 + t) (by linarith) hσ
  rw [norm_mul, hn] at hlarge
  have htprod : t * (4 * (|C| + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (|C| + 1))).mp htC
  have hcabs : t * ‖riemannZeta ((1 + t : ℝ) : ℂ)‖ ≤ t * |C| :=
    mul_le_mul_of_nonneg_left (hupper.trans (le_abs_self C)) ht.le
  nlinarith

/-- P0069 page 22 Lemma 8, the exact universal type of the old lab
leaf_strip_polynomial_growth is false for the principal character. The paper
pole term is essential even for a bound with unspecified constants. -/
theorem leaf_strip_polynomial_growth_type_false561 :
    ¬ (∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q,
        ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧
          ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 + 1 / Real.log x →
            ‖χ.LFunction s‖ ≤ C * (|s.im| + 1) ^ k) := by
  intro h
  obtain ⟨C, k, hC, hk, hbound⟩ := h 2 (by norm_num) 1 (by norm_num) (by norm_num) 1
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  apply riemannZeta_not_bounded_real_segment561 (b := 1 + 1 / Real.log 2) (by linarith [one_div_pos.mpr hl])
  refine ⟨C, fun σ hσ hσb => ?_⟩
  have hh := hbound (σ : ℂ) (by simp only [Complex.ofReal_re]; linarith)
    (by simpa only [Complex.ofReal_re] using hσb)
  simpa only [DirichletCharacter.LFunction_modOne_eq, Complex.ofReal_im, abs_zero,
    zero_add, Real.one_rpow, mul_one] using hh

end LeanLab.BHP1997.Decomp561i
