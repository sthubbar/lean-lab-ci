/-
P0075 line, T2, unit U-6364, I-5170 candidate C2, CLOUD 20261020T1125Z-cloud41, 2026-10-20.
An explicit almost all statement for primes in short multiplicative windows: if
`J_θ(X, δ) ≤ c δ log²(2.0001/δ) X²`, then the set of `y ∈ (X/2, X]` with no prime in
`(y, (1+δ)y]` has measure at most `4 c log²(2.0001/δ)/δ`, by Markov's inequality, since there
the integrand of `J_θ` is `δ²y² ≥ δ²X²/4`. With the lab's `J_θ ≤ 1.2945` from the smoothed
weight, CONDITIONAL ON the zero inputs of SmoothTheorem2.lean, this is `almost_all_smooth`.
AI-written Lean code, Claude. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.ChirreHagen2025.SmoothGoldbach

namespace LeanLab.ChirreHagen2025
open Real Chebyshev MeasureTheory Set

/-- No prime in `(y, (1+δ)y]`. -/
def NoPrimeIn (δ y : ℝ) : Prop := ∀ p : ℕ, p.Prime → ¬ (y < p ∧ (p : ℝ) ≤ (1 + δ) * y)

theorem theta_eq_of_noPrimeIn {δ y : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y) (h : NoPrimeIn δ y) :
    θ ((1 + δ) * y) = θ y := by
  unfold theta
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hky : y ≤ (1 + δ) * y := by nlinarith
  constructor
  · rintro ⟨⟨h0, hp⟩, hpr⟩
    refine ⟨⟨h0, ?_⟩, hpr⟩
    by_contra hlt
    push_neg at hlt
    have h1 : y < p := by
      have := Nat.lt_floor_add_one y
      have h2 : (⌊y⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hlt
      linarith
    have h3 : (p : ℝ) ≤ (1 + δ) * y := by
      have := (Nat.le_floor_iff (by positivity)).mp hp
      exact this
    exact h p hpr ⟨h1, h3⟩
  · rintro ⟨⟨h0, hp⟩, hpr⟩
    exact ⟨⟨h0, le_trans hp (Nat.floor_le_floor hky)⟩, hpr⟩

/-- Markov: the measure of the `y ∈ (X/2, X]` with no prime in `(y, (1+δ)y]`. -/
theorem measure_noPrime_le {X δ c : ℝ} (hX : 2 ≤ X) (hδ : 0 < δ)
    (hJ : Jtheta X δ ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2) :
    volume.real {y | y ∈ Ioc (X / 2) X ∧ NoPrimeIn δ y}
      ≤ 4 * c * Real.log (2.0001 / δ) ^ 2 / δ := by
  set f : ℝ → ℝ := fun y => (θ ((1 + δ) * y) - θ y - δ * y) ^ 2 with hf
  set μ := volume.restrict (Ioc (X / 2) X)
  have hX0 : 0 < X := by linarith
  -- integrability of f on [1, X]
  have hfi : IntervalIntegrable f volume 1 X := by
    have hm1 : Monotone fun t => θ ((1 + δ) * t) := fun u v h => theta_mono (by nlinarith)
    have hm2 : Monotone fun t => θ t + δ * t := fun u v h => by
      have := theta_mono h; nlinarith
    have hs : ∀ a b : ℝ, IntervalIntegrable (fun t => θ ((1 + δ) * t)) volume a b :=
      fun a b => hm1.intervalIntegrable
    have ht : ∀ a b : ℝ, IntervalIntegrable (fun t => θ t + δ * t) volume a b :=
      fun a b => hm2.intervalIntegrable
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) univ := by fun_prop
    -- (A - B)² with A, B monotone, bounded on [1, X]
    have hA := (hm1.monotoneOn (Set.uIcc 1 X))
    have hB := (hm2.monotoneOn (Set.uIcc 1 X))
    have h1 : 0 ≤ (1 : ℝ) := by norm_num
    have hA0 : ∀ t ∈ Set.uIcc (1 : ℝ) X, 0 ≤ θ ((1 + δ) * t) := fun t _ => theta_nonneg _
    have hB0 : ∀ t ∈ Set.uIcc (1 : ℝ) X, 0 ≤ θ t + δ * t := fun t ht' => by
      rw [Set.uIcc_of_le (by linarith)] at ht'
      have := theta_nonneg t; nlinarith [ht'.1]
    have iAA := (hA.mul hA hA0 hA0).intervalIntegrable (μ := volume)
    have iAB := (hA.mul hB hA0 hB0).intervalIntegrable (μ := volume)
    have iBB := (hB.mul hB hB0 hB0).intervalIntegrable (μ := volume)
    refine ((iAA.sub (iAB.const_mul 2)).add iBB).congr ?_
    intro t _
    simp only [hf, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    ring
  have hfI1 : IntegrableOn f (Ioc 1 X) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hfi
  have hfI : IntegrableOn f (Ioc (X / 2) X) :=
    hfI1.mono_set (Ioc_subset_Ioc_left (by linarith))
  have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun y => sq_nonneg _
  set ε := δ ^ 2 * X ^ 2 / 4 with hε
  have hmk := mul_meas_ge_le_integral_of_nonneg hf0 hfI ε
  -- the bad set lies in {ε ≤ f} ∩ Ioc
  have hsub : {y | y ∈ Ioc (X / 2) X ∧ NoPrimeIn δ y} ⊆ {y | ε ≤ f y} ∩ Ioc (X / 2) X := by
    rintro y ⟨hy, hn⟩
    refine ⟨?_, hy⟩
    have hy0 : 0 ≤ y := by linarith [hy.1]
    simp only [Set.mem_ofPred_eq, hf, hε]
    rw [theta_eq_of_noPrimeIn hδ.le hy0 hn]
    have : X / 2 ≤ y := hy.1.le
    have hxy : X ^ 2 / 4 ≤ y ^ 2 := by nlinarith
    have : (θ y - θ y - δ * y) ^ 2 = δ ^ 2 * y ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg δ]
  have hmeas : μ.real {y | ε ≤ f y} = volume.real ({y | ε ≤ f y} ∩ Ioc (X / 2) X) := by
    simp only [μ, measureReal_def]
    rw [Measure.restrict_apply' measurableSet_Ioc]
  have hmono : volume.real {y | y ∈ Ioc (X / 2) X ∧ NoPrimeIn δ y}
      ≤ volume.real ({y | ε ≤ f y} ∩ Ioc (X / 2) X) :=
    measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Ioc_lt_top.ne)
  -- ∫ over (X/2, X] ≤ J_θ(X, δ)
  have hint : ∫ y, f y ∂μ ≤ Jtheta X δ := by
    unfold Jtheta
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set hfI1
      (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (Filter.Eventually.of_forall (Ioc_subset_Ioc_left (by linarith)))
  have hεpos : 0 < ε := by positivity
  have key : ε * volume.real {y | y ∈ Ioc (X / 2) X ∧ NoPrimeIn δ y}
      ≤ c * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
    rw [hmeas] at hmk
    have := mul_le_mul_of_nonneg_left hmono hεpos.le
    linarith
  rw [le_div_iff₀ hδ]
  have e : ε = δ * (δ * X ^ 2 / 4) := by rw [hε]; ring
  rw [e] at key
  have hp : 0 < δ * X ^ 2 / 4 := by positivity
  have k2 : δ * X ^ 2 / 4 * (volume.real {y | y ∈ Ioc (X / 2) X ∧ NoPrimeIn δ y} * δ)
      ≤ δ * X ^ 2 / 4 * (4 * c * Real.log (2.0001 / δ) ^ 2) := by
    nlinarith
  exact le_of_mul_le_mul_left k2 hp

/-- Under RH, from the zero inputs: for `X ≥ 5·10^17`, `0 < δ ≤ 10^-13` with `δ √X < 1`, the
`y ∈ (X/2, X]` with no prime in `(y, (1+δ)y]` have measure at most
`5.178 log²(2.0001/δ)/δ`. -/
theorem almost_all_smooth {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → SmoothT2.ExplicitA γ Z δ)
    (hH : SmoothT2.HadamardK γ) (h14 : SmoothT2.Ordinates14 γ) (hL : SmoothT2.Lemma26 γ)
    {X δ : ℝ} (hX : 5 * 10 ^ 17 ≤ X) (hδ : 0 < δ) (hδ13 : δ ≤ 1 / 10 ^ 13)
    (hs : δ * √X < 1) :
    volume.real {y | y ∈ Ioc (X / 2) X ∧ NoPrimeIn δ y}
      ≤ 5.178 * Real.log (2.0001 / δ) ^ 2 / δ := by
  have h2 := SmoothT2.theorem2_smooth_of hE hH h14 hL X δ (by linarith) hδ hδ13
  have hθ := Jtheta_le_of_c (by norm_num) h2 hX hδ hδ13 hs
  have := measure_noPrime_le (by linarith) hδ hθ
  have e : 4 * (1.001 * 1.2913 + 0.0019) * Real.log (2.0001 / δ) ^ 2 / δ
      ≤ 5.178 * Real.log (2.0001 / δ) ^ 2 / δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    have : 0 ≤ Real.log (2.0001 / δ) ^ 2 := sq_nonneg _
    nlinarith
  linarith

end LeanLab.ChirreHagen2025
