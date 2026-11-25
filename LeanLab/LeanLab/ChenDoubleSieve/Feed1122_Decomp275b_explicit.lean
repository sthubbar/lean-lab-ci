import LeanLab.ChenDoubleSieve.FunctionalStatements

/-!
Explicit forms of the linear sieve functions F and f and of Buchstab's function
on their first ranges, derived from the defining equations of Wu 2004,
https://arxiv.org/pdf/0705.1652, page 6 equation 2.6 for F and f, and
page 9 Lemma 2.10 for Buchstab's function ω.
Every statement is proved from the hypotheses `IsLinearSieve` or `IsBuchstab`
of FunctionalStatements.lean by the fundamental theorem of calculus.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set MeasureTheory

namespace LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit
open Wu04Functional

/-- A function continuous on a closed interval with zero derivative inside is constant. -/
theorem eq_of_deriv_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn g (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt g 0 x) : g b = g a := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    (intervalIntegrable_const (c := (0:ℝ)))
  simp at this
  linarith

/-- The map v ↦ v * F v is continuous on a closed interval inside the positive axis. -/
theorem mul_contOn {F : ℝ → ℝ} {S : Set ℝ} (hF : ContinuousOn F S) {a b : ℝ}
    (hsub : Icc a b ⊆ S) : ContinuousOn (fun v => v * F v) (Icc a b) :=
  continuousOn_id.mul (hF.mono hsub)

/-- Wu 2004 page 6 equation 2.6: F u = 2 e^γ / u for 0 < u ≤ 3. -/
theorem F_eq {F f : ℝ → ℝ} (h : IsLinearSieve F f) :
    ∀ u, 0 < u → u ≤ 3 → F u = 2 * exp eulerMascheroniConstant / u := by
  obtain ⟨hF, hf, h0, hd⟩ := h
  intro u hu0 hu3
  rcases le_or_gt u 2 with hu2 | hu2
  · exact (h0 u hu0 hu2).1
  · set c := 2 * exp eulerMascheroniConstant
    have key : u * F u - c = 2 * F 2 - c := by
      refine eq_of_deriv_zero (g := fun v => v * F v - c) hu2.le ?_ ?_
      · exact (mul_contOn hF (fun x hx => by simp at hx ⊢; linarith [hx.1])).sub
          continuousOn_const
      · intro x hx
        have hz : f (x - 1) = 0 := (h0 (x - 1) (by linarith [hx.1]) (by linarith [hx.2])).2
        have := ((hd x hx.1).1).sub_const c
        rwa [hz] at this
    have h2 : F 2 = c / 2 := (h0 2 (by norm_num) le_rfl).1
    rw [h2] at key
    field_simp
    linarith

/-- Wu 2004 page 6 equation 2.6: f u = 2 e^γ log (u - 1) / u for 2 ≤ u ≤ 4. -/
theorem f_eq {F f : ℝ → ℝ} (h : IsLinearSieve F f) :
    ∀ u, 2 ≤ u → u ≤ 4 → f u = 2 * exp eulerMascheroniConstant * Real.log (u - 1) / u := by
  have hFe := F_eq h
  obtain ⟨hF, hf, h0, hd⟩ := h
  intro u hu2 hu4
  set c := 2 * exp eulerMascheroniConstant
  have key : u * f u - c * Real.log (u - 1) = 2 * f 2 - c * Real.log (2 - 1) := by
    refine eq_of_deriv_zero (g := fun v => v * f v - c * Real.log (v - 1)) hu2 ?_ ?_
    · refine (mul_contOn hf (fun x hx => by simp at hx ⊢; linarith [hx.1])).sub
        (continuousOn_const.mul ?_)
      refine ContinuousOn.log (continuousOn_id.sub continuousOn_const) ?_
      intro x hx
      simp at hx ⊢
      linarith [hx.1]
    · intro x hx
      have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
      have hl : HasDerivAt (fun v => Real.log (v - 1)) (1 / (x - 1)) x :=
        ((hasDerivAt_id x).sub_const 1).log hx1
      have := ((hd x (by linarith [hx.1])).2).sub (hl.const_mul c)
      have hFx : F (x - 1) = c / (x - 1) :=
        hFe (x - 1) (by linarith [hx.1]) (by linarith [hx.2])
      rw [hFx] at this
      convert this using 1
      field_simp
      ring
  have h2 : f 2 = 0 := (h0 2 (by norm_num) le_rfl).2
  rw [h2] at key
  norm_num at key
  have hu : u ≠ 0 := by linarith
  field_simp
  linarith

/-- Wu 2004 page 6 equation 2.6, integrated: u F u = 2 e^γ + ∫ from 3 to u of f (t - 1)
for 3 ≤ u ≤ 5. -/
theorem F_mid {F f : ℝ → ℝ} (h : IsLinearSieve F f) :
    ∀ u, 3 ≤ u → u ≤ 5 →
      u * F u = 2 * exp eulerMascheroniConstant + ∫ t in (3:ℝ)..u, f (t - 1) := by
  have hFe := F_eq h
  obtain ⟨hF, hf, h0, hd⟩ := h
  intro u hu3 _
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v => v * F v) (f' := fun t => f (t - 1)) hu3
    (mul_contOn hF (fun x hx => by simp at hx ⊢; linarith [hx.1]))
    (fun x hx => (hd x (by linarith [hx.1])).1) ?_
  · have h3 : F 3 = 2 * exp eulerMascheroniConstant / 3 := hFe 3 (by norm_num) le_rfl
    rw [hint, h3]
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hu3]
    refine hf.comp (continuousOn_id.sub continuousOn_const) ?_
    intro x hx
    simp at hx ⊢
    linarith [hx.1]

/-- Wu 2004 page 6 equation 2.6, integrated: u f u = 4 f 4 + ∫ from 4 to u of F (t - 1)
for 4 ≤ u ≤ 6. -/
theorem f_mid {F f : ℝ → ℝ} (h : IsLinearSieve F f) :
    ∀ u, 4 ≤ u → u ≤ 6 → u * f u = 4 * f 4 + ∫ t in (4:ℝ)..u, F (t - 1) := by
  obtain ⟨hF, hf, h0, hd⟩ := h
  intro u hu4 _
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v => v * f v) (f' := fun t => F (t - 1)) hu4
    (mul_contOn hf (fun x hx => by simp at hx ⊢; linarith [hx.1]))
    (fun x hx => (hd x (by linarith [hx.1])).2) ?_
  · rw [hint]
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hu4]
    refine hF.comp (continuousOn_id.sub continuousOn_const) ?_
    intro x hx
    simp at hx ⊢
    linarith [hx.1]

/-- Wu 2004 page 9 Lemma 2.10: ω u = (1 + log (u - 1)) / u for 2 ≤ u ≤ 3. -/
theorem omega_eq {ω : ℝ → ℝ} (hω : IsBuchstab ω) :
    ∀ u, 2 ≤ u → u ≤ 3 → ω u = (1 + Real.log (u - 1)) / u := by
  obtain ⟨hc, h1, hd⟩ := hω
  intro u hu2 hu3
  have key : u * ω u - (1 + Real.log (u - 1)) = 2 * ω 2 - (1 + Real.log (2 - 1)) := by
    refine eq_of_deriv_zero (g := fun v => v * ω v - (1 + Real.log (v - 1))) hu2 ?_ ?_
    · refine (mul_contOn hc (fun x hx => by simp at hx ⊢; linarith [hx.1])).sub
        (continuousOn_const.add ?_)
      refine ContinuousOn.log (continuousOn_id.sub continuousOn_const) ?_
      intro x hx
      simp at hx ⊢
      linarith [hx.1]
    · intro x hx
      have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
      have hl : HasDerivAt (fun v => Real.log (v - 1)) (1 / (x - 1)) x :=
        ((hasDerivAt_id x).sub_const 1).log hx1
      have := (hd x hx.1).sub (hl.const_add 1)
      have hωx : ω (x - 1) = 1 / (x - 1) :=
        h1 (x - 1) (by linarith [hx.1]) (by linarith [hx.2])
      rw [hωx] at this
      convert this using 1
      ring
  have h2 : ω 2 = 1 / 2 := h1 2 (by norm_num) (by norm_num)
  rw [h2] at key
  norm_num at key
  have hu : u ≠ 0 := by linarith
  field_simp
  linarith

end LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit

#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit.F_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit.f_eq
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit.F_mid
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit.f_mid
#print axioms LeanLab.ChenDoubleSieve.Task275.Feed1122Explicit.omega_eq
