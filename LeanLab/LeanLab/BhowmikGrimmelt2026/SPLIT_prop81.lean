/-
Split of `prop81` of `LeanLab.BhowmikGrimmelt2026.Statements` into three leaves.

`Prop81` is the exceptional-zero Goldbach formula: for `2/5 ≤ ϑ < 4/9`, a primitive real
character `χ` of conductor `r ≤ X^ϑ` with a real zero `1 - δ` closer to `1` than `1/2` over
`log X` forces the count of even `N` in the window `[X/2, X]` on which `r₂(N)` differs from

  `𝔖(N) N + 𝔖(χ, χ, N) B(1-δ, 1-δ) N ^ (2 (1-δ) - 1)`

by more than `C (𝔖(N) X (δ log X)^{c'} + 𝔖(N) N r / φ(r)² + X^(1-ε₀))` to be at most
`C_ε X^(3/5+ε)`, the constants `h, c', ε₀, C` depending on `ϑ` alone.

The argument has two inputs and one mechanical step. One approximation is of `r₂(N)` by the
singular-series main term `𝔖(N) N`; the numbers of the window on which it fails by a fixed
fraction of the threshold are counted by the exponent `3/5`. The other is of the single
character term `𝔖(χ,χ,N) B(1-δ,1-δ) N^(2(1-δ)-1)`; its coefficient carries the factor
`r / φ(r)²` and the threshold carries the matching `𝔖(N) N r / φ(r)²`, so the conductor is
paid for by the condition `r ≤ X^ϑ` with `ϑ ≥ 2/5`. A number violating the sum of the two
deviations violates one of the two by at least half of the threshold, so the two counts add.

The split fixes the four constants at `h = 1/2`, `c' = 1/10`, `ε₀ = 1/10`, `C = 4` and writes
both counts at the halves of that threshold. Each leaf is one inequality at the exponent
`3/5 + ε`, and no leaf says anything about the deviation from the *sum* of the two main terms,
which is what keeps every leaf strictly weaker than the proposition.

* LEAF 1: the count for the deviation of `r₂(N)` from `𝔖(N) N` on the even `N` of the window.
  It mentions `χ` only through the hypotheses, which place it in the same regime; it asserts
  nothing about the character term.
* LEAF 2: the count for the deviation of the character term on its own, at the same half
  threshold. It asserts nothing about `r₂(N) - 𝔖(N) N`.
* LEAF 3: the pointwise step of the addition: if `x` is further than `T` from `y`, then `x` or
  `y` has norm above `T/2`. Pure norm arithmetic; a negative `T` is not excluded because the
  conclusion holds there too, `‖x‖ ≥ 0 > T/2`.

The assembly `prop81_split` has no sorry and does not use `prop81`. Every leaf is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 3. The first count: there is `C_ε` such that for every `X ≥ 2`, every primitive
real character `χ` of conductor `r ≤ X^ϑ` with a real zero `1 - δ`, `0 < δ < (1/2)/log X`, the
even `N` of the window `[X/2, X]` whose distance from `r₂(N)` to the singular-series main term
`𝔖(N) N` exceeds half of the threshold are fewer than `C_ε X^(3/5+ε)`. This is the
approximation of `r₂` by its main term at the precision that the window and the zero force. It
carries no information about the character term, so it is strictly weaker than `Prop81`, which
bounds the count for the deviation from the sum of the two main terms. -/
theorem leaf_count_main (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ (X : ℝ), 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ),
      χ.IsPrimitive → IsRealChar χ → (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < (1 / 2) / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
        Cε * X ^ (3 / 5 + ε) := by
  sorry

/-- LEAF 2 of 3. The second count: there is `C_ε` such that, in the same regime, the even `N`
of the window on which the single character term `𝔖(χ,χ,N) B(1-δ,1-δ) N^(2(1-δ)-1)` itself has
norm above half of the threshold are fewer than `C_ε X^(3/5+ε)`. The threshold is the one that
carries the conductor: the coefficient has the factor `r / φ(r)²` and the threshold has the
matching `𝔖(N) N r / φ(r)²`, which is what makes `r ≤ X^ϑ` affordable for `ϑ ≥ 2/5`. It
asserts nothing about `r₂(N) - 𝔖(N) N`, so it is strictly weaker than `Prop81`. -/
theorem leaf_count_second (ϑ : ℝ) (hϑ : 2 / 5 ≤ ϑ) (hϑ' : ϑ < 4 / 9) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ (X : ℝ), 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ),
      χ.IsPrimitive → IsRealChar χ → (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < (1 / 2) / Real.log X →
      DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
      (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
        Cε * X ^ (3 / 5 + ε) := by
  sorry

/-- LEAF 3 of 3. The pointwise step: for complex `x`, `y` and a real `T`, if `x` is further
than `T` from `y` then `x` or `y` has norm above `T / 2`, since `‖x - y‖ ≤ ‖x‖ + ‖y‖` and two
norms each at most `T / 2` add to at most `T`. Nothing else is assumed, and a negative `T` is
consistent: there `‖x‖ ≥ 0 > T / 2` makes both disjuncts true. This is the only place where the
two counts are put together: it turns one violation of the sum into a violation of one
summand. -/
theorem leaf_half_split {x y : ℂ} {T : ℝ} (h : ¬ ‖x - y‖ ≤ T) :
    ¬ ‖x‖ ≤ T / 2 ∨ ¬ ‖y‖ ≤ T / 2 := by
  by_contra hc
  push_neg at hc
  apply h
  calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    _ ≤ T / 2 + T / 2 := add_le_add hc.1 hc.2
    _ = T := by ring

/-- `Prop81`, assembled from the three leaves and nothing else. The four constants are
`h = 1/2`, `c' = 1/10`, `ε₀ = 1/10`, `C = 4`; for an admissible `N` the deviation from the sum
of the two main terms is `x - y` with `x = r₂(N) - 𝔖(N) N` and `y` the character term, so leaf
3 puts `N` into the set counted by leaf 1 or into the set counted by leaf 2, the two card bounds
are added over the union, and the implied constants add. No sorry, and `prop81` is not used. -/
theorem prop81_split : Prop81 := by
  intro ϑ hϑ hϑ'
  refine ⟨1 / 2, 1 / 10, 1 / 10, 4, by norm_num, by norm_num, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨Cε₁, h₁⟩ := leaf_count_main ϑ hϑ hϑ' ε hε
  obtain ⟨Cε₂, h₂⟩ := leaf_count_second ϑ hϑ hϑ' ε hε
  refine ⟨Cε₁ + Cε₂, ?_⟩
  intro X hX r _inst χ δ hprim hreal hr hδ0 hδL hL
  have hb₁ := h₁ X hX r χ δ hprim hreal hr hδ0 hδL hL
  have hb₂ := h₂ X hX r χ δ hprim hreal hr hδ0 hδL hL
  have hsub : ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N -
              genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10))) ⊆ ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2) ∪ ((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_union] at hN ⊢
    obtain ⟨hNI, hEven, hbad⟩ := hN
    rcases leaf_half_split (x := (r2 N : ℂ) - singular N * N) (y := genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)) (T := (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10))) hbad with hx | hy
    · exact Or.inl ⟨hNI, hEven, hx⟩
    · exact Or.inr ⟨hNI, hEven, hy⟩
  have hcard : (((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N -
              genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10)))).card ≤ (((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card + (((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hval : (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N -
              genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10)))).card : ℕ) : ℝ) ≤ (Cε₁ + Cε₂) * X ^ (3 / 5 + ε) := by
    calc (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N -
              genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
              singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                X ^ (1 - (1 : ℝ) / 10)))).card : ℕ) : ℝ)
        ≤ (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card + (((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) := Nat.cast_le.mpr hcard
      _ = ((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖(r2 N : ℂ) - singular N * N‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℝ) + ((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧ ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℝ) := Nat.cast_add _ _
      _ ≤ Cε₁ * X ^ (3 / 5 + ε) + Cε₂ * X ^ (3 / 5 + ε) := add_le_add hb₁ hb₂
      _ = (Cε₁ + Cε₂) * X ^ (3 / 5 + ε) := by ring
  exact hval

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.prop81_split
