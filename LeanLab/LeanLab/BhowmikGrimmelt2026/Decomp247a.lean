/-
Supply split for euler_gen_eq from DecompJ249.
The existing statement text is unchanged. The two arithmetic inputs use their exact suppliers.
Source: P0029 page 23 display 6.4 and Pintz Part I pages 19 and 20 displays 7.10 to 7.15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp436b

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology





/-- P0029 page 23 display 6.4. Pintz Part I page 20 display 7.13.
Supplied by the exact finite residue fiber bound in Decomp436a.
For fixed primitive characters and positive N, the coefficients are uniformly bounded
by a constant times the reciprocal totient square. The constant depends on the fixed data.
This is a pointwise coefficient bound and states no summability or Euler product. -/
theorem aqZero247_totient_bound {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2) := by
  exact aqZero247_totient_supply436 χ₁ χ₂ hχ₁ hχ₂ N hN


/-- The exact fixed data coefficient bound supplies absolute summability.
This supplies the absolute convergence input of Pintz Part I page 20 display 7.15. -/
theorem aqZero247_norm_summable {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ‖aqZero247 χ₁ χ₂ N q‖) := by
  obtain ⟨C, hC, hbound⟩ := aqZero247_totient_bound χ₁ χ₂ hχ₁ hχ₂ N hN
  exact aqZero247_norm_summable_of_bound χ₁ χ₂ N C hC hbound

/-- P0029 page 23 display 6.4. Pintz Part I pages 19 and 20 displays 7.10 to 7.14.
Supplied by the exact finite CRT expansion in Decomp436b.
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
  exact aqZero247_smooth_supply436 χ₁ χ₂ hχ₁ hχ₂ ψ₁ ψ₂ h₁ h₂ N hN X hX₁ hX₂



/-- The exact fixed data bound and finite smooth expansion supply the Euler product.
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
