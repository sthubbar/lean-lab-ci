/-
A logical obstruction to proving complex Euler product convergence from local norm bounds alone.
This tests a proof route for P0029 page 23 display 6.5. It is not a claim about the paper.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology

/-- Products of minus one over the primes do not converge.
Each factor has norm one, and the product of those norms is identically one.
Thus a convergent norm majorant does not by itself imply complex product convergence. -/
theorem prime_sign_product_not_tendsto247 :
    ¬ ∃ z : ℂ, Tendsto
      (fun X : ℕ => ∏ p ∈ (Finset.range X).filter Nat.Prime, (-1 : ℂ))
      atTop (𝓝 z) := by
  rintro ⟨z, hz⟩
  obtain ⟨X₀, hX₀⟩ := Metric.tendsto_atTop.mp hz (1 / 2) (by norm_num)
  obtain ⟨p, hpX, hp⟩ := Nat.exists_infinite_primes X₀
  have hnear₁ := hX₀ p hpX
  have hnear₂ := hX₀ (p + 1) (by omega)
  have hstep : (∏ q ∈ (Finset.range (p + 1)).filter Nat.Prime, (-1 : ℂ)) =
      (∏ q ∈ (Finset.range p).filter Nat.Prime, (-1 : ℂ)) * (-1) := by
    simp only [Finset.prod_filter, Finset.prod_range_succ, if_pos hp]
  have hnorm : ‖∏ q ∈ (Finset.range p).filter Nat.Prime, (-1 : ℂ)‖ = 1 := by
    simp
  have hdist : dist (∏ q ∈ (Finset.range (p + 1)).filter Nat.Prime, (-1 : ℂ))
      (∏ q ∈ (Finset.range p).filter Nat.Prime, (-1 : ℂ)) = 2 := by
    rw [dist_eq_norm, hstep]
    have he (a : ℂ) : a * (-1) - a = (-2 : ℂ) * a := by ring
    rw [he, norm_mul, hnorm]
    norm_num
  have htriangle := dist_triangle
    (∏ q ∈ (Finset.range (p + 1)).filter Nat.Prime, (-1 : ℂ)) z
    (∏ q ∈ (Finset.range p).filter Nat.Prime, (-1 : ℂ))
  rw [hdist, dist_comm z] at htriangle
  linarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.prime_sign_product_not_tendsto247
