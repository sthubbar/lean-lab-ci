/-
Supply split for euler_gen_eq from DecompJ249.
The sealed leaf is unchanged. The two arithmetic leaves below remain OPEN.
Source: P0029 page 23 display 6.4 and Pintz Part I pages 19 and 20 displays 7.10 to 7.15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.DecompJ249

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- The coefficient of display 6.4 extended by zero at modulus zero. -/
noncomputable def aqZero247 {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) (q : ℕ) : ℂ :=
  if h : q = 0 then 0 else @Aq r₁ r₂ χ₁ χ₂ N q ⟨h⟩

/-- The zero extension adds no modulus zero coefficient. -/
theorem aqZero247_zero {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) :
    aqZero247 χ₁ χ₂ N 0 = 0 := by
  simp [aqZero247]

/-- At a positive modulus the extension is the original coefficient. -/
theorem aqZero247_succ {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ) (q : ℕ) :
    aqZero247 χ₁ χ₂ N (q + 1) = Aq χ₁ χ₂ N (q + 1) := by
  simp [aqZero247]

/-- A modulus outside the conductor divisibility restriction contributes zero.
Source: P0029 page 23 display 6.4 and Pintz Part I page 19 display 7.9. -/
theorem aqZero247_eq_zero_of_not_lcm_dvd {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) (q : ℕ) (hq : ¬ Nat.lcm r₁ r₂ ∣ q) :
    aqZero247 χ₁ χ₂ N q = 0 := by
  by_cases hzero : q = 0
  · simp [aqZero247, hzero]
  · have hd : ¬ (r₁ ∣ q ∧ r₂ ∣ q) := by
      simpa only [Nat.lcm_dvd_iff] using hq
    simp [aqZero247, hzero, Aq, hd]

/-- LEAF. P0029 page 23 display 6.4. Pintz Part I page 20 display 7.13.
For fixed primitive characters and positive N, the coefficients are uniformly bounded
by a constant times the reciprocal totient square. The constant depends on the fixed data.
This is a pointwise coefficient bound and states no summability or Euler product. -/
theorem aqZero247_totient_bound {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2) := by
  sorry

/-- A reciprocal totient square coefficient bound gives absolute summability.
This implication uses only the proved seventh power totient estimate and the p series test. -/
theorem aqZero247_norm_summable_of_bound {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2)) :
    Summable (fun q : ℕ => ‖aqZero247 χ₁ χ₂ N q‖) := by
  have hs : Summable (fun q : ℕ => C * (7 * (q : ℝ) ^ (-(7 : ℝ) / 4))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : (-(7 : ℝ) / 4) < -1)).mul_left 7).mul_left C
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hs
  intro q
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst q
    simp only [aqZero247_zero, norm_zero]
    positivity
  · exact (hbound q hq).trans (mul_le_mul_of_nonneg_left
      (LeanLab.Zinoviev1997.inv_totient_sq_seven q hq) hC)

/-- CONDITIONAL ON aqZero247_totient_bound.
This supplies the absolute convergence input of Pintz Part I page 20 display 7.15. -/
theorem aqZero247_norm_summable {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ‖aqZero247 χ₁ χ₂ N q‖) := by
  obtain ⟨C, hC, hbound⟩ := aqZero247_totient_bound χ₁ χ₂ hχ₁ hχ₂ N hN
  exact aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hbound

/-- LEAF. P0029 page 23 display 6.4. Pintz Part I pages 19 and 20 displays 7.10 to 7.14.
After every conductor prime is included, the finite product of local factors equals
its expansion over smooth moduli. This is an exact identity at each cutoff.
It states no convergence as the cutoff grows. -/
theorem aqZero247_smooth_expansion {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂)
    (N : ℤ) (hN : 1 ≤ N) (X : ℕ) (hX₁ : r₁ < X) (hX₂ : r₂ < X) :
    ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p =
      ∑' q : X.smoothNumbers, aqZero247 χ₁ χ₂ N q := by
  sorry

/-- Removing the zero coefficient recovers exactly the positive modulus series. -/
theorem aqZero247_tsum {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (hsum : Summable (aqZero247 χ₁ χ₂ N)) :
    (∑' q : ℕ, aqZero247 χ₁ χ₂ N q) = genSing χ₁ χ₂ N := by
  rw [hsum.tsum_eq_zero_add, aqZero247_zero, zero_add]
  simp only [aqZero247_succ, genSing]

/-- Smooth modulus sums tend to the full series under the explicit summability hypothesis.
This uses Mathlib's smooth number tail estimate and no arithmetic leaf. -/
theorem aqZero247_smooth_tendsto {r₁ r₂ : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (N : ℤ)
    (hsum : Summable (aqZero247 χ₁ χ₂ N)) :
    Tendsto (fun X : ℕ => ∑' q : X.smoothNumbers, aqZero247 χ₁ χ₂ N q)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  rw [← aqZero247_tsum χ₁ χ₂ N hsum, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt
    hsum (aqZero247_zero χ₁ χ₂ N) hε
  refine ⟨X₀, fun X hX => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hX₀ X hX

/-- CONDITIONAL ON aqZero247_totient_bound and aqZero247_smooth_expansion.
This is the exact sealed euler_gen_eq conclusion, with no direct sorry.
The original leaf stays unchanged for the reviewer to repoint. -/
theorem euler_gen_eq_supply247 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : IsPrimeComponents χ₁ ψ₁) (h₂ : IsPrimeComponents χ₂ ψ₂) (N : ℤ) (hN : 1 ≤ N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorGen (ψ₁ p) (ψ₂ p) N p)
      atTop (𝓝 (genSing χ₁ χ₂ N)) := by
  have hsum := (aqZero247_norm_summable χ₁ χ₂ hχ₁ hχ₂ N hN).of_norm
  apply (aqZero247_smooth_tendsto χ₁ χ₂ N hsum).congr'
  filter_upwards [eventually_gt_atTop r₁, eventually_gt_atTop r₂] with X hX₁ hX₂
  exact (aqZero247_smooth_expansion χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N hN X hX₁ hX₂).symm

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_zero
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_succ
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_tsum
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_smooth_tendsto
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_norm_summable
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_smooth_expansion
#print axioms LeanLab.BhowmikGrimmelt2026.euler_gen_eq_supply247

#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_totient_bound
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_norm_summable_of_bound

#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_eq_zero_of_not_lcm_dvd
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247
