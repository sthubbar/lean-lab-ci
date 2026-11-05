/-
Consequences of the proved local bound on page 23 display 6.5.
These results do not identify the limit with the generalized singular series.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Audit1610

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Every finite product of component factors is bounded by the ordinary finite product.
Source: P0029 page 23 display 6.5, before the missing global identification. -/
theorem euler_partial_norm_le247 {r₁ r₂ : ℕ}
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : 1 ≤ N) (X : ℕ) :
    ‖∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p‖ ≤
      ∏ p ∈ (Finset.range X).filter Nat.Prime, eulerFactorSing N p := by
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p hp => local_bound (ψ₁ p) (ψ₂ p) (h₁ p) (h₂ p) N hN p
      (Finset.mem_filter.mp hp).2)

/-- The finite component products have a uniform norm bound.
Source: P0029 page 23 displays 6.4 and 6.5. This is weaker than convergence. -/
theorem euler_partial_bounded247 {r₁ r₂ : ℕ}
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ,
      ‖∏ p ∈ (Finset.range X).filter Nat.Prime,
        eulerFactorGen (ψ₁ p) (ψ₂ p) N p‖ ≤ C := by
  obtain ⟨C, hC⟩ := (euler_sing_eq N hN).bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun X => ?_⟩
  exact (euler_partial_norm_le247 ψ₁ ψ₂ h₁ h₂ N hN X).trans
    ((hC ⟨X, rfl⟩).trans (le_max_left _ _))

/-- Every limit along an increasing subsequence satisfies the desired norm bound.
Source: P0029 page 23 display 6.5. The value of the limit is not identified here. -/
theorem euler_subseq_norm_le247 {r₁ r₂ : ℕ}
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : 1 ≤ N) (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : ℂ)
    (hz : Tendsto (fun k : ℕ => ∏ p ∈ (Finset.range (φ k)).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) atTop (𝓝 z)) :
    ‖z‖ ≤ singular N := by
  exact le_of_tendsto_of_tendsto' hz.norm ((euler_sing_eq N hN).comp hφ.tendsto_atTop)
    (fun k => euler_partial_norm_le247 ψ₁ ψ₂ h₁ h₂ N hN (φ k))

/-- The component products have an increasing convergent subsequence.
Its limit has norm at most the ordinary singular series.
Source: P0029 page 23 display 6.5. This supplies no equality with genSing. -/
theorem euler_exists_subseq247 {r₁ r₂ : ℕ}
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k : ℕ => ∏ p ∈ (Finset.range (φ k)).filter Nat.Prime,
        eulerFactorGen (ψ₁ p) (ψ₂ p) N p) atTop (𝓝 z) ∧ ‖z‖ ≤ singular N := by
  obtain ⟨C, hC, hbound⟩ := euler_partial_bounded247 ψ₁ ψ₂ h₁ h₂ N hN
  have hmem : ∀ X : ℕ, (∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) ∈ Metric.closedBall (0 : ℂ) C := by
    intro X
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound X
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) C).tendsto_subseq hmem
  exact ⟨z, φ, hφ, hlim, euler_subseq_norm_le247 ψ₁ ψ₂ h₁ h₂ N hN φ hφ z hlim⟩

/-- The ordinary Euler factor at two vanishes for odd N.
Source: P0029 page 6 display 2.10 and page 23 display 6.4. -/
theorem euler_two_odd247 (N : ℕ) (hN : Odd N) : eulerFactorSing N 2 = 0 := by
  have hram : ramanujan 2 (N : ℤ) = -1 := by
    have hfil : (Finset.range 2).filter (fun a => Nat.Coprime a 2) = {1} := by decide
    unfold ramanujan
    rw [hfil, Finset.sum_singleton]
    simp only [Nat.cast_one, one_mul, Int.cast_natCast, Nat.cast_ofNat]
    have hexp : 2 * (Real.pi : ℂ) * Complex.I * (((N : ℝ) / 2 : ℝ) : ℂ) =
        (N : ℂ) * (Real.pi * Complex.I) := by
      push_cast
      ring
    unfold ee
    rw [hexp, Complex.exp_nat_mul, Complex.exp_pi_mul_I, hN.neg_one_pow]
  rw [Audit1610.eulerFactorSing_prime N 2 Nat.prime_two, hram, Nat.totient_two]
  norm_num

/-- Every primitive character pair has zero generalized Euler factor at two for odd N.
Source: P0029 page 23 display 6.5, at the parity prime. -/
theorem euler_gen_two_odd247 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℕ) (hN : Odd N) :
    eulerFactorGen χ₁ χ₂ N 2 = 0 := by
  have hN₁ : 1 ≤ N := by obtain ⟨k, hk⟩ := hN; omega
  have hb := local_bound χ₁ χ₂ hχ₁ hχ₂ N hN₁ 2 Nat.prime_two
  rw [euler_two_odd247 N hN] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

/-- At odd N every component partial product with cutoff at least three is exactly zero.
Source: P0029 page 23 displays 6.4 and 6.5, the parity obstruction. -/
theorem euler_odd_partial_zero247 {r₁ r₂ : ℕ}
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : Odd N) (X : ℕ) (hX : 3 ≤ X) :
    (∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩)
  exact euler_gen_two_odd247 (ψ₁ 2) (ψ₂ 2) (h₁ 2) (h₂ 2) N hN

/-- At odd N the full component product sequence converges to zero.
Source: P0029 page 23 displays 6.4 and 6.5. No claim about genSing is used. -/
theorem euler_odd_tendsto_zero247 {r₁ r₂ : ℕ}
    (ψ₁ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₁ p))
    (ψ₂ : ∀ p : ℕ, DirichletCharacter ℂ (compLevel r₂ p))
    (h₁ : ∀ p, (ψ₁ p).IsPrimitive) (h₂ : ∀ p, (ψ₂ p).IsPrimitive)
    (N : ℕ) (hN : Odd N) :
    Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorGen (ψ₁ p) (ψ₂ p) N p) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 3] with X hX
  exact (euler_odd_partial_zero247 ψ₁ ψ₂ h₁ h₂ N hN X hX).symm

/-- The ordinary singular series is zero at every odd natural integer.
Source: P0029 page 6 displays 2.9 and 2.10, the parity obstruction. -/
theorem singular_odd247 (N : ℕ) (hN : Odd N) : singular N = 0 := by
  have hN₁ : 1 ≤ N := by obtain ⟨k, hk⟩ := hN; omega
  have hz : Tendsto (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime,
      eulerFactorSing N p) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 3] with X hX
    symm
    exact Finset.prod_eq_zero
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩)
      (euler_two_odd247 N hN)
  exact tendsto_nhds_unique (euler_sing_eq N hN₁) hz

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.euler_partial_norm_le247
#print axioms LeanLab.BhowmikGrimmelt2026.euler_partial_bounded247
#print axioms LeanLab.BhowmikGrimmelt2026.euler_subseq_norm_le247
#print axioms LeanLab.BhowmikGrimmelt2026.euler_exists_subseq247

#print axioms LeanLab.BhowmikGrimmelt2026.euler_two_odd247
#print axioms LeanLab.BhowmikGrimmelt2026.euler_gen_two_odd247
#print axioms LeanLab.BhowmikGrimmelt2026.euler_odd_partial_zero247
#print axioms LeanLab.BhowmikGrimmelt2026.euler_odd_tendsto_zero247
#print axioms LeanLab.BhowmikGrimmelt2026.singular_odd247
