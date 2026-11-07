/-
A split of `facts81`, the two formulas of display 8.1, into four leaves plus an assembly.

The four leaves are (1) the sign of the ordinary singular series at an even `N ≥ 2`, which
lets its complex image keep the same size, (2) the base case of the generalised series, at
both characters trivial of conductor one, where it is the ordinary singular series, (3) the
conductor saving: twisting the trivial character by a primitive real character of conductor
`r` costs the factor `r / φ(r)²`, and (4) the diagonal factorisation: for a primitive real
`χ` whose conductor divides `N`, the series of the pair `(χ, χ)` is `χ(-1)` times the
series of the pair of trivial characters of conductor one. The assembly rewrites the first
formula into the second through leaf 2 and reads off the second formula from leaf 4.

AI wrote the Lean code. Binary Goldbach is OPEN. The four leaves are open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF. Step 1, the size of the ordinary series: for an even `N` at least two the singular
series `𝔖(N)` is nonnegative, so its image in `ℂ` has modulus `𝔖(N)` itself. This is what
turns the two sides of the first formula of 8.1 into the same shape, one written with the
series and one with its modulus. -/
theorem facts81_pos (N : ℕ) (hEven : Even N) (hN : 2 ≤ N) : 0 ≤ singular N := by
  sorry

/-- LEAF. Step 2, the base case of the generalised series: with both characters trivial of
conductor one, the sum of `Aq` over the moduli is the ordinary singular series. Every modulus
`q + 1` is a multiple of both conductors, the two Gauss factors contribute `μ(q)²`, and the
character sum of the principal character is the Ramanujan sum at `q`, so the two series
coincide as real numbers, and the generalised one is its image in `ℂ`. -/
theorem facts81_base (N : ℕ) (hEven : Even N) (hN : 2 ≤ N) :
    genSing chi1 chi1 N = ((singular N : ℝ) : ℂ) := by
  sorry

/-- LEAF. Step 3, the conductor saving: for a primitive real character `χ` of conductor `r`,
the generalised series of the pair consisting of the trivial character of conductor one and
`χ` is bounded by `r / φ(r)²` times the modulus of the base case series of step 2, with an
absolute constant. This is the loss the twist by `χ` costs, and it is the whole content of
the first formula of 8.1 once step 2 has been used. -/
theorem facts81_saving :
    ∃ K : ℝ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → IsRealChar χ →
      ∀ N : ℕ, Even N → 2 ≤ N →
        ‖genSing chi1 χ N‖ ≤ K * ‖genSing chi1 chi1 N‖ * r / (Nat.totient r : ℝ) ^ 2 := by
  sorry

/-- LEAF. Step 4, the diagonal factorisation: for a primitive real character `χ` of conductor
`r` dividing the even `N`, the generalised series of the pair `(χ, χ)` is `χ(-1)` times the
base case series of step 2. The factor is the product of the two Gauss factors of `χ`, which
is `χ(-1) r`, against the modulus of the principal character, whose square cancels the
`φ(r)²`, and the primitive induced characters agree at every modulus that is a multiple of
`r`, which every surviving modulus is. -/
theorem facts81_diag (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hreal : IsRealChar χ) (N : ℕ) (hEven : Even N) (hN2 : 2 ≤ N) (hdvd : r ∣ N) :
    genSing χ χ N = χ (-1) * genSing chi1 chi1 N := by
  sorry

/-- The two formulas of 8.1, assembled from the four leaves above. The first one is step 2
rewritten into step 3 and then turned back into a real comparison by step 1; the second one
is step 4 followed by step 2. -/
theorem facts81_split : Facts81 := by
  obtain ⟨K, hK⟩ := facts81_saving
  refine ⟨⟨K, ?_⟩, ?_⟩
  · intro r hr0 χ hprim hreal N hEven hN2
    have hnorm : ‖((singular N : ℝ) : ℂ)‖ = singular N := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (facts81_pos N hEven hN2)]
    calc ‖genSing chi1 χ N‖
        ≤ K * ‖genSing chi1 chi1 N‖ * r / (Nat.totient r : ℝ) ^ 2 :=
          hK r χ hprim hreal N hEven hN2
      _ = K * singular N * r / (Nat.totient r : ℝ) ^ 2 := by
          rw [facts81_base N hEven hN2, hnorm]
  · intro r hr0 χ hprim hreal N hEven hN2 hdvd
    calc genSing χ χ N = χ (-1) * genSing chi1 chi1 N :=
          facts81_diag r χ hprim hreal N hEven hN2 hdvd
      _ = χ (-1) * singular N := by rw [facts81_base N hEven hN2]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.facts81_split
