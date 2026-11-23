/-
P0069, pages 26 to 41. Burst S64 group A, unit Decomp312a.lower_mean_value_supply.
Additivity of the Section 4 supply contract. The paper builds the lower weight
a0 on page 32 as a finite sum of kept Buchstab pieces, each of which satisfies
the mean value property 4.2 by Lemmata 12 to 16 or Theorem 4, and it obtains u0
on page 41 by summing the densities. The lab splits 4.2 for a family into the
divisor bound, MeanValue41, ReferenceDensity and ShortApproximation for an
auxiliary family. This file proves that each of these is additive, so that a
future split of the supply into kept pieces can be assembled with no gap.
Nothing here is an analytic input and no statement of Decomp312a is changed.
The file imports only the definitions, not Decomp312a, to keep the build light.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Sifted312
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.Decomp312c

namespace LeanLab.BHP1997.Decomp312aSupplyAdd
open Classical Complex DecompC165b Decomp312c
open scoped BigOperators
open Filter

/-- Divisor bounds add. Page 26, condition 3.1 for a sum of two pieces. -/
theorem divisor_bound_add {a1 a2 : ℝ → ℕ → ℝ} {B0 : ℝ}
    (h1 : ∃ C : ℝ, ∀ x k, |a1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0)
    (h2 : ∃ C : ℝ, ∀ x k, |a2 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) :
    ∃ C : ℝ, ∀ x k, |a1 x k + a2 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0 := by
  obtain ⟨C1, hC1⟩ := h1
  obtain ⟨C2, hC2⟩ := h2
  refine ⟨C1 + C2, fun x k => ?_⟩
  have e1 := hC1 x k
  have e2 := hC2 x k
  have t := abs_add_le (a1 x k) (a2 x k)
  nlinarith

/-- Pages 26 and 27, the truncation error of 4.11 and 4.12 adds over pieces. -/
theorem shortApproximation_add {ε : ℝ} {a1 a2 b1 b2 : ℝ → ℕ → ℝ}
    (h1 : ShortApproximation ε a1 b1) (h2 : ShortApproximation ε a2 b2) :
    ShortApproximation ε (fun x k => a1 x k + a2 x k) (fun x k => b1 x k + b2 x k) := by
  intro A hA
  obtain ⟨C1, X1, hC1⟩ := h1 A hA
  obtain ⟨C2, X2, hC2⟩ := h2 A hA
  refine ⟨C1 + C2, max X1 X2, fun x hx => ?_⟩
  have e1 := hC1 x ((le_max_left _ _).trans hx)
  have e2 := hC2 x ((le_max_right _ _).trans hx)
  have hs : (∑ k ∈ leftInterval ε x, |(a1 x k + a2 x k) - (b1 x k + b2 x k)|) ≤
      ∑ k ∈ leftInterval ε x, (|a1 x k - b1 x k| + |a2 x k - b2 x k|) := by
    apply Finset.sum_le_sum
    intro k _
    have := abs_add_le (a1 x k - b1 x k) (a2 x k - b2 x k)
    have e : (a1 x k + a2 x k) - (b1 x k + b2 x k) = (a1 x k - b1 x k) + (a2 x k - b2 x k) := by
      ring
    rw [e]
    exact this
  rw [Finset.sum_add_distrib] at hs
  have hr : (C1 + C2) * x ^ (11 / 20 + ε) * Real.log x ^ (-A) =
      C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) +
        C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
  rw [hr]
  linarith

/-- Pages 24 and 25, the I1 character average is linear in the family. -/
theorem referenceAverage_add (a1 a2 : ℝ → ℕ → ℝ) (x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    referenceAverage (fun x k => a1 x k + a2 x k) x χ =
      referenceAverage a1 x χ + referenceAverage a2 x χ := by
  unfold referenceAverage
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- Page 33, the reference densities of kept pieces add, as in the
Siegel Walfisz calculation and the subtraction of discarded integrals. -/
theorem referenceDensity_add {u1 u2 : ℝ} {a1 a2 : ℝ → ℕ → ℝ}
    (h1 : ReferenceDensity u1 a1) (h2 : ReferenceDensity u2 a2) :
    ReferenceDensity (u1 + u2) (fun x k => a1 x k + a2 x k) := by
  intro A hA
  obtain ⟨C1, X1, hC1⟩ := h1 A hA
  obtain ⟨C2, X2, hC2⟩ := h2 A hA
  refine ⟨C1 + C2, max X1 X2, fun x hx q hq hqA χ => ?_⟩
  have e1 := hC1 x ((le_max_left _ _).trans hx) q hq hqA χ
  have e2 := hC2 x ((le_max_right _ _).trans hx) q hq hqA χ
  rw [referenceAverage_add]
  have e : referenceAverage a1 x χ + referenceAverage a2 x χ -
      Thm2.delta χ * ((u1 + u2 : ℝ) : ℂ) / (Real.log x : ℂ) =
      (referenceAverage a1 x χ - Thm2.delta χ * (u1 : ℂ) / (Real.log x : ℂ)) +
        (referenceAverage a2 x χ - Thm2.delta χ * (u2 : ℂ) / (Real.log x : ℂ)) := by
    push_cast
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hr : (C1 + C2) * Real.log x ^ (-A) =
      C1 * Real.log x ^ (-A) + C2 * Real.log x ^ (-A) := by ring
  rw [hr]
  exact add_le_add e1 e2

/-- The Dirichlet polynomial integrand of 4.1 is continuous in the height.
Every index of Ioc with lower end a natural floor is positive. -/
theorem integrand_continuous (a : ℝ → ℕ → ℝ) (x σ : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
      (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖) := by
  apply Continuous.norm
  apply continuous_finset_sum
  intro k hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1
    exact_mod_cast this.ne'
  apply Continuous.div continuous_const
  · apply Continuous.const_cpow
    · unfold Thm4.half
      fun_prop
    · exact Or.inl hk0
  · intro t
    rw [Complex.cpow_def_of_ne_zero hk0]
    exact Complex.exp_ne_zero _

/-- For a fixed positive exponent c the lower height exp of log x to the
one third is eventually at most x to the c. This orders the limits of the
integral in 4.1 when c is 0.45 minus 2 epsilon over 3. -/
theorem eventually_lower_le_upper {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ c := by
  have h0 : Tendsto (fun L : ℝ => L ^ (-(2 / 3 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h1 : ∀ᶠ L : ℝ in atTop, L ^ (-(2 / 3 : ℝ)) ≤ c :=
    (h0.eventually (ge_mem_nhds hc))
  have h2 : ∀ᶠ L : ℝ in atTop, L ^ (1 / 3 : ℝ) ≤ c * L := by
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with L hL hpos
    have e : L ^ (1 / 3 : ℝ) = L ^ (-(2 / 3 : ℝ)) * L := by
      rw [← Real.rpow_add_one hpos.ne']
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_right hL hpos.le
  have h3 := Real.tendsto_log_atTop.eventually h2
  filter_upwards [h3, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.mpr
  linarith [mul_comm (Real.log x) c]

/-- Page 24, display 4.1 is additive over pieces, for epsilon below 0.675
so that the height range of 4.1 is eventually nonempty. -/
theorem meanValue41_add {ε : ℝ} (hε : ε < 0.675) {a1 a2 : ℝ → ℕ → ℝ}
    (h1 : MeanValue41 ε a1) (h2 : MeanValue41 ε a2) :
    MeanValue41 ε (fun x k => a1 x k + a2 x k) := by
  intro A hA
  obtain ⟨C1, X1, hC1⟩ := h1 A hA
  obtain ⟨C2, X2, hC2⟩ := h2 A hA
  have hc : (0 : ℝ) < 0.45 - 2 * ε / 3 := by linarith
  obtain ⟨X3, hX3⟩ := eventually_atTop.mp (eventually_lower_le_upper hc)
  refine ⟨C1 + C2, max (max X1 X2) X3, fun x hx q hq hqA χ σ hσ => ?_⟩
  have e1 := hC1 x ((le_max_left _ _).trans ((le_max_left _ _).trans hx)) q hq hqA χ σ hσ
  have e2 := hC2 x ((le_max_right _ _).trans ((le_max_left _ _).trans hx)) q hq hqA χ σ hσ
  have hab := hX3 x ((le_max_right _ _).trans hx)
  have i1 := (integrand_continuous a1 x σ χ).intervalIntegrable (μ := MeasureTheory.volume)
    (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (0.45 - 2 * ε / 3))
  have i2 := (integrand_continuous a2 x σ χ).intervalIntegrable (μ := MeasureTheory.volume)
    (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (0.45 - 2 * ε / 3))
  have hmono := intervalIntegral.integral_mono_on hab
    ((integrand_continuous (fun x k => a1 x k + a2 x k) x σ χ).intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (i1.add i2) (fun t _ => by
      refine le_trans (le_of_eq ?_) (norm_add_le _ _)
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring)
  rw [intervalIntegral.integral_add i1 i2] at hmono
  have hr : (C1 + C2) * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) =
      C1 * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C2 * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring
  rw [hr]
  linarith

/-- Pages 32, 33 and 41, assembly of the supply at one epsilon from two kept
pieces. If the sifted lower family splits pointwise into two pieces, each
with its own auxiliary family carrying the divisor bound, 4.1, an I1 density
and the truncation approximation, then the sifted family has the supply
conclusions of Decomp312a.lower_mean_value_supply at that epsilon with the
summed density. CONDITIONAL on all hypotheses, which are the kept pieces of
the paper. The minorant and the density range are passed through. -/
theorem supply_at_of_two_pieces {B0 ε u1 u2 : ℝ} (hε : ε < 0.675)
    {c0 f1 f2 b1 b2 : ℝ → ℕ → ℝ}
    (hsplit : ∀ x k, section4SiftedFamily c0 x k = f1 x k + f2 x k)
    (hc : ∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
      C * ((k.divisors.card : ℕ) : ℝ) ^ B0)
    (hb1 : ∃ C : ℝ, ∀ x k, |b1 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0)
    (hb2 : ∃ C : ℝ, ∀ x k, |b2 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0)
    (hm1 : MeanValue41 ε b1) (hm2 : MeanValue41 ε b2)
    (hd1 : ReferenceDensity u1 b1) (hd2 : ReferenceDensity u2 b2)
    (ha1 : ShortApproximation ε f1 b1) (ha2 : ShortApproximation ε f2 b2)
    (hu : 0.9953 < u1 + u2) (hu1 : u1 + u2 ≤ 1)
    (hlo : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k) :
    ∃ (u0 : ℝ) (b : ℝ → ℕ → ℝ),
      0.9953 < u0 ∧ u0 ≤ 1 ∧
      (∃ C : ℝ, ∀ x k, |section4SiftedFamily c0 x k| ≤
        C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B0) ∧
      MeanValue41 ε b ∧ ReferenceDensity u0 b ∧
      ShortApproximation ε (section4SiftedFamily c0) b ∧
      ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        ∀ k ∈ leftInterval ε x, section4SiftedFamily c0 x k ≤ Decomp132.primeWeight k := by
  have e : section4SiftedFamily c0 = fun x k => f1 x k + f2 x k := by
    funext x k
    exact hsplit x k
  refine ⟨u1 + u2, fun x k => b1 x k + b2 x k, hu, hu1, hc, divisor_bound_add hb1 hb2,
    meanValue41_add hε hm1 hm2, referenceDensity_add hd1 hd2, ?_, hlo⟩
  rw [e]
  exact shortApproximation_add ha1 ha2

end LeanLab.BHP1997.Decomp312aSupplyAdd
