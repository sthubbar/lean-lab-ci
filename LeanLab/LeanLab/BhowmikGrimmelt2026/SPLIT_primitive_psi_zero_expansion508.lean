/-
A split of `primitive_psi_zero_expansion508` into three leaves plus an assembly.

The statement is a sharp explicit formula with zeros: for a primitive character of modulus
`q ≤ √X` there is a height `T` between `X` and `2X` and the finite list `Z` of the zeros with
`|Im ρ| ≤ T`, such that the twisted von Mangoldt sum up to `n` differs from the main term
minus the zero sum by a uniform `O((log X)²)`.

The three leaves are (1) the height and the zero list: up to any height at least `X` the zeros
in the open strip form a finite set, so a finset characterised exactly by the zero condition
exists; (2) the error estimate away from the trivial character, where the main term vanishes;
(3) the same estimate for the trivial character, where the main term is `n` itself. Leaves (2)
and (3) take `T` and `Z` as given, so neither of them has to produce the height or the list;
the assembly takes them from leaf (1) and splits on whether the character is trivial, keeping
the larger of the two constants.

AI wrote the Lean code. Binary Goldbach is open. The three leaves are open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp508a

namespace LeanLab.BhowmikGrimmelt2026

/-- LEAF. Step 1, the height and the zero list: for a primitive `χ` of modulus `q` and any
`X ≥ 2` there is a height `T` between `X` and `2X` and a finset `Z` of complex numbers whose
members are exactly the zeros of the `L`-function of `χ` in the open strip with imaginary part
of absolute value at most `T`. This is the finiteness and the selection step; it produces no
estimate at all, and leaves (2) and (3) only use the characterisation it gives. -/
theorem zero_set_window508 {X q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hX : 2 ≤ X) (hprim : χ.IsPrimitive) :
    ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) := by
  sorry

/-- LEAF. Step 2, the error estimate away from the trivial character: for a primitive
`χ ≠ 1`, a height `T` of the size of `X` and the zero list `Z` up to that height, the twisted
von Mangoldt sum up to `n` plus the zero sum `∑ ρ ∈ Z, mult χ ρ * n ^ ρ / ρ` has size at most
`C * (log X)²`, with `C` independent of `X`, `q`, `χ`, `T`, `Z` and `n`. The main term of the
explicit formula vanishes here, so this is the leaf (2) of the header with the trivial
character removed: it does not produce `T` or `Z`. -/
theorem nonprincipal_psi_zero_bound508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  sorry

/-- LEAF. Step 3, the error estimate for the trivial character: for `χ = 1` primitive, a
height `T` of the size of `X` and the zero list `Z` up to that height, the twisted von
Mangoldt sum up to `n` minus `n` plus the zero sum `∑ ρ ∈ Z, mult χ ρ * n ^ ρ / ρ` has size at
most `C * (log X)²`, again with a constant independent of everything but the hypothesis on the
zeros. The main term of the explicit formula is `n` here, which is the whole difference from
step 2: the leaf takes `T` and `Z` as given instead of producing them. -/
theorem principal_psi_zero_bound508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ = 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) - (n : ℂ) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  sorry

/-- The sharp explicit formula with zeros, assembled from the three leaves above. Leaf 1 gives
the height `T` and the zero list `Z`; the character being trivial or not selects leaf 3 or
leaf 2 for the estimate, and the two constants are merged into their maximum. -/
theorem primitive_psi_zero_expansion508_split (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C₂, hC₂, hnp⟩ := nonprincipal_psi_zero_bound508 Θ hΘ hZ
  obtain ⟨C₃, hC₃, hpr⟩ := principal_psi_zero_bound508 Θ hΘ hZ
  refine ⟨max C₂ C₃, hC₂.trans (le_max_left C₂ C₃), ?_⟩
  intro X hX q _ hqQ χ hprim
  obtain ⟨T, hT, Z, hchar⟩ := zero_set_window508 χ hX hprim
  refine ⟨T, hT, Z, hchar, ?_⟩
  intro n hn1 hnX
  have hlog : (0 : ℝ) ≤ Real.log X ^ 2 := sq_nonneg (Real.log X)
  rcases eq_or_ne χ 1 with h1 | h1
  · subst h1
    have hmain : (if (1 : DirichletCharacter ℂ q) = 1 then (n : ℂ) else 0) = (n : ℂ) := by
      simp
    rw [hmain]
    exact (hpr X hX q hqQ 1 hprim rfl T hT Z hchar n hn1 hnX).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₂ C₃) hlog)
  · have hmain : (if χ = 1 then (n : ℂ) else 0) = 0 := by
      simp only [ite_eq_right h1]
    rw [hmain, sub_zero]
    exact (hnp X hX q hqQ χ hprim h1 T hT Z hchar n hn1 hnX).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₂ C₃) hlog)

end LeanLab.BhowmikGrimmelt2026
