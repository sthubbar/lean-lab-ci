/-
P0070 Section 6, page 367, replacing an induced character by its primitive character in 36.
The added Euler factors have no zeros for positive real part.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.PrimitiveReduction

namespace LeanLab.PerelliPintz1992.Section6
open Real Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Induction adds no Euler factor zeros in the right half plane. -/
theorem euler_factor_ne_zero {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpow : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos
      (show 0 < (p : ℝ) by linarith) (-s)
  have hn : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, hpow]
    calc
      ‖χ p‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (by linarith) _)
      _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_neg_of_pos hs)
  intro hzero
  have hh := congrArg norm (sub_eq_zero.mp hzero)
  rw [norm_one] at hh
  linarith

#print axioms euler_factor_ne_zero


/-- Character induction preserves the order of every nontrivial L zero. -/
theorem analyticOrderAt_changeLevel {r q : ℕ+} (h : (r : ℕ) ∣ (q : ℕ))
    (ψ : DirichletCharacter ℂ (r : ℕ)) {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    analyticOrderAt (ψ.changeLevel h).LFunction s = analyticOrderAt ψ.LFunction s := by
  have hs1 : s ≠ 1 := by
    intro hh
    simp [hh] at hs'
  let g : ℂ → ℂ := fun z => ∏ p ∈ (q : ℕ).primeFactors, (1 - ψ p * (p : ℂ) ^ (-z))
  have hg0 : g s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact euler_factor_ne_zero ψ (Nat.prime_of_mem_primeFactors hp) hs
  have hg : AnalyticAt ℂ g s := by
    dsimp [g]
    apply Finset.analyticAt_fun_prod
    intro p hp
    apply AnalyticAt.sub analyticAt_const
    apply AnalyticAt.mul analyticAt_const
    apply AnalyticAt.cpow analyticAt_const (analyticAt_id.neg)
    exact Complex.natCast_mem_slitPlane.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hf : AnalyticAt ℂ ψ.LFunction s := by
    apply DifferentiableOn.analyticAt (s := ({1} : Set ℂ)ᶜ)
    · intro z hz
      exact (ψ.differentiableAt_LFunction z (Or.inl (by simpa using hz))).differentiableWithinAt
    · apply isClosed_singleton.isOpen_compl.mem_nhds
      simpa using hs1
  have heq : (ψ.changeLevel h).LFunction =ᶠ[𝓝 s] ψ.LFunction * g := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact DirichletCharacter.LFunction_changeLevel h ψ (Or.inr hz)
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hf hg,
    analyticOrderAt_eq_zero.mpr (Or.inr hg0), add_zero]

#print axioms analyticOrderAt_changeLevel


/-- The nontrivial zero count, including multiplicities, is unchanged by induction. -/
theorem zeroCount_changeLevel {r q : ℕ+} (h : (r : ℕ) ∣ (q : ℕ))
    (ψ : DirichletCharacter ℂ (r : ℕ)) (σ T : ℝ) :
    zeroCount (ψ.changeLevel h) σ T = zeroCount ψ σ T := by
  unfold zeroCount
  apply tsum_congr
  intro s
  by_cases hregion : s ∈ zeroRegion σ T
  · rw [ite_eq_left hregion, ite_eq_left hregion]
    rw [analyticOrderAt_changeLevel h ψ hregion.2.1 hregion.2.2.1]
  · simp only [ite_eq_right hregion]

#print axioms zeroCount_changeLevel


/-- Sum the zero counts over all characters induced by the fixed ψ. -/
theorem sum_induced_zeroCount (Q : Finset ℕ+) {r : ℕ+}
    (ψ : DirichletCharacter ℂ (r : ℕ)) (σ T : ℝ) :
    (∑ c ∈ inducedFamily Q ψ, zeroCount c.2 σ T) =
      ((inducedFamily Q ψ).card : ENNReal) * zeroCount ψ σ T := by
  calc
    (∑ c ∈ inducedFamily Q ψ, zeroCount c.2 σ T) =
        ∑ _c ∈ inducedFamily Q ψ, zeroCount ψ σ T := by
      apply Finset.sum_congr rfl
      intro c hc
      obtain ⟨h, hh⟩ := (Finset.mem_filter.mp hc).2
      rw [← hh, zeroCount_changeLevel]
    _ = ((inducedFamily Q ψ).card : ENNReal) * zeroCount ψ σ T := by
      rw [Finset.sum_const, nsmul_eq_mul]

#print axioms sum_induced_zeroCount


/-- The zero count multiplicity bound used in equation 36. -/
theorem sum_induced_zeroCount_le (Q : Finset ℕ+) {r : ℕ+}
    (ψ : DirichletCharacter ℂ (r : ℕ)) (σ T : ℝ) (X : ℕ)
    (hQ : ∀ q ∈ Q, (q : ℕ) ≤ X) :
    (∑ c ∈ inducedFamily Q ψ, zeroCount c.2 σ T) ≤
      ENNReal.ofReal ((X : ℝ) / (r : ℝ)) * zeroCount ψ σ T := by
  rw [sum_induced_zeroCount]
  have hh := ENNReal.ofReal_le_ofReal (inducedFamily_card_le Q ψ X hQ)
  have hc : ((inducedFamily Q ψ).card : ENNReal) ≤
      ENNReal.ofReal ((X : ℝ) / (r : ℝ)) := by
    simpa only [ENNReal.ofReal_natCast] using hh
  exact mul_le_mul' hc le_rfl

#print axioms sum_induced_zeroCount_le

end
end LeanLab.PerelliPintz1992.Section6
