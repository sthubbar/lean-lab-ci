/-
Split of the LEAF leafB8_adjoint of Split1122bBoundary8.lean: the adjoint function of the
linear sieve, Nathanson Theorem 9.4, as quoted by Bordignon, Johnston and Starichkova,
arXiv 2207.09452v6, papers/P0009.pdf, page 6. The adjoint function is
q(s) = the integral over x > 0 of exp (- s x - Ein x), with
Ein x = the integral over [0, x] of (1 - e ^ -t) / t. It satisfies s q'(s) = - q(s + 1)
for s > 0, s q(s) → 1 as s → ∞, and K(q) = e ^ -γ. Numerically K(q) = 0.5614595.
The twin leafB8_adjoint_twin, statement copied verbatim, is proved from three LEAFs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- The entire exponential integral Ein x = the integral over [0, x] of (1 - e ^ -t) / t,
used in the adjoint function of Nathanson Theorem 9.4, as quoted by BJS arXiv 2207.09452
page 6. -/
def einB8 (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t

/-- The adjoint function of Nathanson Theorem 9.4, as quoted by BJS arXiv 2207.09452 page 6:
q(s) = the integral over x > 0 of exp (- s x - Ein x). -/
def adjQB8 (s : ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), exp (-s * x - einB8 x)

-- Helper lemmas for einB8
lemma einB8_zero : einB8 0 = 0 := by
  simp [einB8, intervalIntegral.integral_same]

lemma einB8_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ einB8 x := by
  have h₁ : 0 ≤ ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t := by
    have h₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) x → 0 ≤ (1 - exp (-t)) / t := by
      intro t ht
      have h₃ : 0 ≤ t := by exact ht.1
      have h₄ : t ≤ x := by exact ht.2
      by_cases ht0 : t = 0
      · simp [ht0]
      · have h₅ : 0 < t := by contrapose! ht0; linarith
        have h₆ : exp (-t) < 1 := by
          have h₇ : -t < 0 := by linarith
          have h₈ : exp (-t) < exp 0 := Real.exp_lt_exp.mpr h₇
          have h₉ : exp 0 = (1 : ℝ) := by norm_num
          linarith
        have h₇ : 1 - exp (-t) > 0 := by linarith
        have h₈ : (1 - exp (-t)) / t > 0 := by positivity
        linarith
    -- Use the fact that the integrand is non-negative on [0, x]
    by_cases hx0 : x = 0
    · simp_all [intervalIntegral.integral_same]
    · have h₃ : 0 < x := by contrapose! hx0; linarith
      have h₄ : IntervalIntegrable (fun t : ℝ => (1 - exp (-t)) / t) MeasureTheory.volume 0 x := by
        apply Continuous.intervalIntegrable
        continuity
      have h₅ : 0 ≤ ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t := by
        apply intervalIntegral.integral_nonneg
        <;> simp_all
        <;>
        (try norm_num) <;>
        (try linarith) <;>
        (try
          {
            intro t ht
            exact h₂ t ht
          })
      exact h₅
  simpa [einB8] using h₁

lemma hasDerivAt_einB8 {x : ℝ} (hx : 0 < x) :
    HasDerivAt einB8 ((1 - exp (-x)) / x) x := by
  have h₁ : HasDerivAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t) ((1 - exp (-x)) / x) x := by
    have h₂ : HasDerivAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t) ((1 - exp (-x)) / x) x := by
      -- Use the fundamental theorem of calculus for interval integrals
      have h₃ : ContinuousOn (fun t : ℝ => (1 - exp (-t)) / t) (Set.Icc 0 x) := by
        apply ContinuousOn.div
        · apply ContinuousOn.sub
          · exact continuousOn_const
          · exact ContinuousOn.exp (ContinuousOn.neg continuousOn_id)
        · exact continuousOn_id
        · intro t ht
          by_cases ht0 : t = 0
          · simp_all
          · positivity
      have h₄ : HasDerivAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t) ((1 - exp (-x)) / x) x := by
        have h₅ : HasDerivAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t) ((1 - exp (-x)) / x) x := by
          apply HasDerivAt.congr_of_eventuallyEq (intervalIntegral.integral_hasDerivAt (by
            apply Continuous.intervalIntegrable
            continuity
          ))
          filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
          simp_all
          <;>
          (try norm_num) <;>
          (try linarith)
        exact h₅
      exact h₄
    exact h₂
  have h₂ : einB8 = (fun x : ℝ => ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t) := by
    funext x
    simp [einB8]
  rw [h₂] at *
  exact h₁

lemma einB8_le {x : ℝ} (hx : 0 ≤ x) : einB8 x ≤ x := by
  have h₁ : einB8 x = ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t := rfl
  rw [h₁]
  have h₂ : ∫ t in (0 : ℝ)..x, (1 - exp (-t)) / t ≤ ∫ t in (0 : ℝ)..x, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by continuity) (by continuity)
    <;> simp_all [Set.Icc_subset_Icc_left]
    <;>
    (try
      {
        intro t ht
        have h₃ : 0 ≤ t := by exact ht.1
        have h₄ : t ≤ x := by exact ht.2
        by_cases ht0 : t = 0
        · simp_all
        · have h₅ : 0 < t := by contrapose! ht0; linarith
          have h₆ : exp (-t) ≥ 0 := Real.exp_pos (-t) |>.le
          have h₇ : (1 - exp (-t)) / t ≤ 1 := by
            have h₈ : 1 - exp (-t) ≤ t := by
              have h₉ : Real.exp (-t) ≥ 1 - t := by
                have h₁₀ : Real.exp (-t) ≥ 1 + (-t) := by
                  linarith [Real.add_one_le_exp (-t)]
                linarith
              linarith
            have h₉ : 0 < t := by positivity
            rw [div_le_iff (by positivity)]
            nlinarith
          linarith
      })
  have h₃ : ∫ t in (0 : ℝ)..x, (1 : ℝ) = x := by
    simp [intervalIntegral.integral_const]
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  linarith

-- Helper lemmas for adjQB8
lemma adjQB8_integrable (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-s * x - einB8 x)) (Set.Ioi (0 : ℝ)) := by sorry

lemma adjQB8_hasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt adjQB8 (-∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) s := by sorry

lemma key_IBP (s : ℝ) (hs : 0 < s) :
    s * (∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) = adjQB8 (s + 1) := by sorry

/-- LEAF: Nathanson Theorem 9.4, the delay relation of the adjoint function: for s > 0,
q'(s) = - the integral of x exp (- s x - Ein x) by differentiation under the integral, and
integrating by parts with d/dx exp (- s x - Ein x) = - (s + (1 - e ^ -x) / x) times the
integrand gives s q'(s) = - q(s + 1). Class MEDIUM: dominated differentiation of a
parameter integral plus integration by parts on (0, ∞). -/
theorem leafB8_adjQ_deriv (s : ℝ) (hs : 0 < s) :
    HasDerivAt adjQB8 (-adjQB8 (s + 1) / s) s := by
  have h₁ : HasDerivAt adjQB8 (-∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) s := adjQB8_hasDerivAt s hs
  have h₂ : s * (∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) = adjQB8 (s + 1) := key_IBP s hs
  have h₃ : -∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x) = -adjQB8 (s + 1) / s := by
    have h₄ : s ≠ 0 := by linarith
    have h₅ : ∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x) = adjQB8 (s + 1) / s := by
      have h₆ : s * (∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x)) = adjQB8 (s + 1) := h₂
      have h₇ : ∫ x in Set.Ioi (0 : ℝ), x * exp (-s * x - einB8 x) = adjQB8 (s + 1) / s := by
        field_simp [h₄] at h₆ ⊢
        <;> nlinarith
      exact h₇
    rw [h₅]
    <;> field_simp [hs.ne']
    <;> ring
  have h₄ : HasDerivAt adjQB8 (-adjQB8 (s + 1) / s) s := by
    convert h₁ using 1
    <;> rw [h₃]
  exact h₄

/-- LEAF: Nathanson Theorem 9.4, normalization of the adjoint function: s q(s) → 1 as
s → ∞, by the substitution x = y / s, s q(s) = the integral over y > 0 of
exp (- y - Ein (y / s)), and Ein (y / s) → 0 with 0 ≤ Ein, dominated convergence. Class
MEDIUM: dominated convergence on (0, ∞) and continuity of Ein at 0. -/
theorem leafB8_adjQ_tendsto :
    Filter.Tendsto (fun s => s * adjQB8 s) Filter.atTop (nhds 1) := by
  sorry

/-- LEAF: Nathanson Theorem 9.4, the Mertens type constant: for the explicit adjoint
function, K(q) = q(3) (1 + log 2) + the integral over [2, 3] of
(1 + log (t - 1)) q(t + 1) / t equals e ^ -γ, through Ein x = log x + γ + E_1(x) and the
integral of e ^ -t / t. Numerically K(q) = 0.5614595. Class HARD: Laplace transform
identities and γ as a limit of the exponential integral. -/
theorem leafB8_adjQ_K : kConstB8 adjQB8 = exp (-eulerMascheroniConstant) := by
  sorry

/-- Twin of leafB8_adjoint of Split1122bBoundary8.lean, statement copied verbatim, from
the three LEAFs above with q the explicit adjoint function adjQB8. -/
theorem leafB8_adjoint_twin :
    ∃ q : ℝ → ℝ, IsAdjB8 q ∧ kConstB8 q = exp (-eulerMascheroniConstant) :=
  ⟨adjQB8, ⟨fun s hs => leafB8_adjQ_deriv s hs, leafB8_adjQ_tendsto⟩, leafB8_adjQ_K⟩

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_adjoint_twin
