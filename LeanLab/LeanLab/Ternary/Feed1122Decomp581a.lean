/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 bottom Buchstab display.
Split of the two open limits of Decomp581a into a cited short interval
prime number theorem, a deterministic layer cake transfer for the fixed smooth
weight, a uniform rough cofactor estimate, a prime sum to integral passage and
a change of variables. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp581a

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory

/-- LEAF: MMS page 11 bottom display, the prime number theorem in the reference
interval, uniformly over its subintervals. Class HARD for Codex.
CITED: this needs an error term beating x times exp of minus the square root of
log x, for example the Vinogradov Korobov zero free region or Huxley's short
interval theorem. The lab StrongPNT envelope is too weak, see
Task571.pnt_envelope_not_half_referenceLength. Open subintervals are used so
that the layer cake transfer applies directly. -/
theorem shortIntervalPNT_reference :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ a b : ℝ, x ≤ a → a ≤ b →
      b ≤ x + Task379.referenceLength x →
      |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
        ε * Task379.referenceLength x := by
  sorry

/-- Layer cake plan step one: the profile is symmetric about one half.
MMS page 11, the fixed smooth g1. -/
theorem profile_symm (s : ℝ) :
    expNegInvGlue (1 - s) * expNegInvGlue (1 - (1 - s)) = expNegInvGlue s * expNegInvGlue (1 - s) := by
  rw [sub_sub_cancel, mul_comm]

/-- Layer cake plan step one: the profile increases on the left half, so
superlevel sets are intervals. MMS page 11, the fixed smooth g1. -/
theorem profile_mono_left {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 1 / 2) :
    expNegInvGlue s * expNegInvGlue (1 - s) ≤ expNegInvGlue t * expNegInvGlue (1 - t) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [expNegInvGlue.zero_of_nonpos hs, zero_mul]
    exact mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  simp only [expNegInvGlue, not_le.mpr hs, not_le.mpr ht0, not_le.mpr h1s, not_le.mpr h1t,
    ite_false, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : s * (1 - s) ≤ t * (1 - t) := by nlinarith
  have e1 : -s⁻¹ + -(1 - s)⁻¹ = -(s * (1 - s))⁻¹ := by field_simp; ring
  have e2 : -t⁻¹ + -(1 - t)⁻¹ = -(t * (1 - t))⁻¹ := by field_simp; ring
  rw [e1, e2, neg_le_neg_iff]
  exact inv_anti₀ (by positivity) key

/-- Layer cake plan step one: the profile decreases on the right half.
MMS page 11, the fixed smooth g1. -/
theorem profile_anti_right {s t : ℝ} (hs : 1 / 2 ≤ s) (hst : s ≤ t) :
    expNegInvGlue t * expNegInvGlue (1 - t) ≤ expNegInvGlue s * expNegInvGlue (1 - s) := by
  have h := profile_mono_left (s := 1 - t) (t := 1 - s) (by linarith) (by linarith)
  rwa [profile_symm, profile_symm] at h

/-- LEAF: MMS page 11 bottom display, layer cake step for the weighted prime
sum. Class MEDIUM for Open Math OS. The profile is unimodal and vanishes at the
ends, so its superlevel sets are open subintervals; integrating the interval
hypothesis over levels bounds the weighted error by the profile maximum M. -/
theorem weightedPrime_layerCake_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          Task379.referenceWeight x n * ρ n) -
        ∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t| ≤
        M * ε * Task379.referenceLength x := by
  sorry

/-- Change of variables for the rescaled profile. MMS page 11, g1 in
Proposition 5.1 rescaled to the reference interval. -/
theorem profile_rescale_integral (x L : ℝ) (hL : 0 < L) :
    (∫ t in x..(x + L), expNegInvGlue ((t - x) / L) * expNegInvGlue (1 - (t - x) / L)) =
      L * ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have h := intervalIntegral.integral_comp_div_sub
    (fun s => expNegInvGlue s * expNegInvGlue (1 - s)) (c := L) (d := x / L) hL.ne'
    (a := x) (b := x + L)
  simp only [sub_div] at *
  rw [h]
  have e1 : x / L - x / L = 0 := sub_self _
  have e2 : (x + L) / L - x / L = 1 := by field_simp; ring
  rw [e1, e2, smul_eq_mul]

/-- The fixed profile has positive integral. MMS page 11, g1 nonzero. -/
theorem profile_integral_pos :
    0 < ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have hc : Continuous (fun s : ℝ => expNegInvGlue s * expNegInvGlue (1 - s)) := by
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ zero_lt_one
  intro s hs
  exact mul_pos (expNegInvGlue.pos_of_pos hs.1) (expNegInvGlue.pos_of_pos (by linarith [hs.2]))

/-- The weight integral is the length times the fixed profile integral I.
MMS page 11, change of variables. Proved from the two lemmas above. -/
theorem weightIntegral_scaling :
    ∃ I : ℝ, 0 < I ∧ ∀ x : ℝ, 1 ≤ x →
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
        I * Task379.referenceLength x := by
  refine ⟨_, profile_integral_pos, fun x hx => ?_⟩
  have hL : 0 < Task379.referenceLength x := by
    unfold Task379.referenceLength
    have : (0 : ℝ) < x := by linarith
    positivity
  unfold Task379.referenceWeight
  rw [profile_rescale_integral x _ hL, mul_comm]

theorem referenceLength_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    0 < Task379.referenceLength x := by
  unfold Task379.referenceLength
  have : (0 : ℝ) < x := by linarith
  positivity

/-- primeMean_transfer from the layer cake bound and the integral scaling,
with C equal to M over I. CONDITIONAL ON weightedPrime_layerCake_bound and
weightIntegral_scaling. MMS page 11 bottom display. -/
theorem primeMean_transfer_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |primeMean x - 1| ≤ C * ε := by
  obtain ⟨M, hM, hB⟩ := weightedPrime_layerCake_bound
  obtain ⟨I, hI, hS⟩ := weightIntegral_scaling
  refine ⟨M / I, div_pos hM hI, fun x hx ε hε hyp => ?_⟩
  have hL := referenceLength_pos_of_one_le hx
  have hb := hB x hx ε hε hyp
  have hs := hS x hx
  rw [hs] at hb
  have hIL : 0 < I * Task379.referenceLength x := mul_pos hI hL
  have he : primeMean x - 1 =
      (Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          Task379.referenceWeight x n * ρ n) - I * Task379.referenceLength x) /
        (I * Task379.referenceLength x) := by
    unfold primeMean
    rw [hs]
    field_simp
  rw [he, abs_div, abs_of_pos hIL, div_le_iff₀ hIL]
  calc _ ≤ M * ε * Task379.referenceLength x := hb
    _ = M / I * ε * (I * Task379.referenceLength x) := by field_simp

/-- MMS page 11 bottom display, passage from interval prime counts to the
smooth weighted prime sum. Pass 6: proved from primeMean_transfer_of_leaves,
CONDITIONAL ON the leaf weightedPrime_layerCake_bound.
Deterministic layer cake step: the reference weight is unimodal with value zero
at both ends, so each superlevel set is an open subinterval, and the weighted
sum and the weight integral are integrals over levels of counts and lengths.
One may take C equal to the maximum of the profile over its integral. -/
theorem primeMean_transfer :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |primeMean x - 1| ≤ C * ε :=
  primeMean_transfer_of_leaves

/-- The weighted prime limit from the two leaves above.
MMS page 11 bottom display. CONDITIONAL ON shortIntervalPNT_reference
and primeMean_transfer. -/
theorem primeMean_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeMean x - 1| ≤ δ := by
  intro δ hδ
  obtain ⟨C, hC, hT⟩ := primeMean_transfer
  obtain ⟨X, hX⟩ := shortIntervalPNT_reference (δ / C) (by positivity)
  refine ⟨max 1 X, fun x hx => ?_⟩
  have h := hT x ((le_max_left _ _).trans hx) (δ / C) (by positivity)
    (fun a b ha hab hb => hX x ((le_max_right _ _).trans hx) a b ha hab hb)
  have he : C * (δ / C) = δ := by field_simp
  linarith

/-- The frozen Buchstab main term of the composite rough numbers.
MMS page 11 bottom display: for each least prime factor p from x to the one
quarter up to the square root of x, the cofactors rough at p have density
buchstab of log of x over p divided by log p, over log p. New definition,
needed to separate the rough cofactor estimate from the prime sum. -/
noncomputable def compositeModelSum (x : ℝ) : ℝ :=
  Real.log x * ∑ p ∈ range (⌊x⌋₊ + 1),
    if p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x then
      Task571.buchstabModel (Real.log (x / p) / Real.log p) / (p * Real.log p) else 0

/-- LEAF: MMS page 11 bottom display, Buchstab identity plus the prime number
theorem for the rough cofactors n over p in the rescaled reference interval,
uniformly in the least prime p. Class HARD for Codex. CITED short interval
input as in shortIntervalPNT_reference, applied to primes and to products of
two primes at least p. The finite bucket identity is compositeRough_buchstab. -/
theorem compositeMean_model :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - compositeModelSum x| ≤ δ := by
  sorry

/-- LEAF: MMS page 11 bottom display, the prime sum to integral passage in the
logarithmic coordinate a equal to log p over log x, from one quarter to one half.
Class MEDIUM for Open Math OS. Partial summation with the prime number theorem;
the lab Mertens estimates of Decomp581b handle the analogous triple sums. -/
theorem compositeModelSum_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeModelSum x -
        ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2| ≤ δ := by
  sorry

/-- MMS page 11 bottom display, the substitution u equal to one over a minus
one, mapping one quarter to three and one half to one. Derived, no cited input. -/
theorem compositeIntegral_substitution :
    (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2) =
      ∫ t in (1 : ℝ)..3, Task571.buchstabModel t := by
  set g := Task571.buchstabModel
  have hgc : ContinuousOn g (Set.Ici 1) := by
    have hc := (Task571.buchstabStage_continuous_clamp 8).continuousOn
      (s := Set.Ici (1 : ℝ))
    refine hc.congr fun u hu => ?_
    simp only [g, Task571.buchstabModel, max_eq_right (Set.mem_Ici.mp hu)]
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := (1 / 4 : ℝ)) (b := 1 / 2)
    (f := fun a : ℝ => (1 - a) / a) (f' := fun a : ℝ => -1 / a ^ 2) (g := g)
    (fun a ha => by
      have ha0 : a ≠ 0 := by
        rw [Set.uIcc_of_le (by norm_num)] at ha; linarith [ha.1]
      have h1 : HasDerivAt (fun a : ℝ => 1 - a) (-1) a := by
        simpa using (hasDerivAt_id a).const_sub 1
      have h3 : HasDerivAt (fun a : ℝ => (1 - a) / a)
          ((-1 * a - (1 - a) * 1) / a ^ 2) a := h1.div (hasDerivAt_id a) ha0
      refine h3.congr_deriv ?_
      field_simp
      ring)
    (by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro a ha
      rw [Set.uIcc_of_le (by norm_num)] at ha
      have : 0 < a := by linarith [ha.1]
      exact pow_ne_zero 2 this.ne')
    (by
      apply hgc.mono
      rintro _ ⟨a, ha, rfl⟩
      rw [Set.uIcc_of_le (by norm_num)] at ha
      have h0 : 0 < a := by linarith [ha.1]
      show 1 ≤ (1 - a) / a
      rw [le_div_iff₀ h0]; linarith [ha.2])
  simp only [Function.comp_apply] at hsub
  rw [show ((1 : ℝ) - 1 / 4) / (1 / 4) = 3 by norm_num,
    show ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 by norm_num,
    intervalIntegral.integral_symm 1 3] at hsub
  have hneg : (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), g ((1 - a) / a) / a ^ 2) =
      -∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), g ((1 - a) / a) * (-1 / a ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; funext a; ring
  rw [hneg]
  linarith [hsub]

/-- The composite rough limit from the three leaves above.
MMS page 11 bottom display. CONDITIONAL ON compositeMean_model,
compositeModelSum_limit and compositeIntegral_substitution. -/
theorem compositeMean_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - (∫ t in (1 : ℝ)..3, Task571.buchstabModel t)| ≤ δ := by
  intro δ hδ
  obtain ⟨X₁, h₁⟩ := compositeMean_model (δ / 2) (by linarith)
  obtain ⟨X₂, h₂⟩ := compositeModelSum_limit (δ / 2) (by linarith)
  refine ⟨max X₁ X₂, fun x hx => ?_⟩
  have a₁ := h₁ x ((le_max_left _ _).trans hx)
  have a₂ := h₂ x ((le_max_right _ _).trans hx)
  rw [compositeIntegral_substitution] at a₂
  have ha := abs_add_le (compositeMean x - compositeModelSum x)
    (compositeModelSum x - ∫ t in (1 : ℝ)..3, Task571.buchstabModel t)
  rw [sub_add_sub_cancel] at ha
  linarith

end LeanLab.Ternary.MMS.Task581
