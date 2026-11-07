/-
Split of `akeno_thm1_2`, the statement `AlmostAllDyadic Even (DiffForm 4)`.

The argument has four steps. Take the level of distribution `0.1635` of Theorem 1.1 for the
two smooth weights of the weighted sieve, at level exponent `A + 3`; run the weighted sieve
(parameters `s = 33.5`, `t = 9.5` of Proposition 4.4) so that every even `N ∈ (X/2, X]`
whose level sum stays below the natural threshold `X (ln X)^{-2}` is `p₁ + p₂` with
`p₁ ≥ p₂` primes and `p₁ - p₂ + 1 ∈ P₄`; observe that the level bound at exponent `A + 3`
is below that threshold from some height on; and absorb the finitely many small `X` into the
final constant. Each step is one LEAF below, and `akeno_thm1_2_split` assembles them.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026
open Real Finset
open scoped ContDiff ArithmeticFunction.vonMangoldt

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of the split. The first step: the level of distribution `0.1635` of Theorem 1.1,
read at sieve dimension `k = 2` and weight support parameter `η = 1/2`. For every `A > 0`
there are two smooth weights supported in `[1/2, 1]` and nonnegative constants `C₁, C₂` such
that all but `C₁ X (ln X)^{-A}` integers `N ∈ (X/2, X]` satisfy
`Σ_{d ≤ X^{0.1635}} τ(d)² sup_l |R_{d,l}(N)| ≤ C₂ X (ln X)^{-A}`. -/
theorem leaf_level_sum_exception_bound (A : ℝ) (hA : 0 < A) :
    ∃ (w₁ w₂ : ℝ → ℝ) (C₁ C₂ : ℝ),
      0 ≤ C₁ ∧ 0 ≤ C₂ ∧ SmoothWeight (1 / 2) w₁ ∧ SmoothWeight (1 / 2) w₂ ∧
        ∀ X : ℝ, 2 ≤ X →
          (excCount (fun _ => True)
              (fun N => levelSum 0.1635 2 w₁ w₂ X N ≤ C₂ * X / Real.log X ^ A) X : ℝ)
            ≤ C₁ * X / Real.log X ^ A := by
  sorry

/-- LEAF 2 of the split. The second step: the weighted sieve of Proposition 4.4, at
`s = 33.5` and `t = 9.5`. For any two smooth weights supported in `[1/2, 1]` there is a
height beyond which every even `N ∈ (X/2, X]` whose weighted level sum is at most
`X (ln X)^{-2}` is a sum `p₁ + p₂` of primes with `p₁ ≥ p₂` and `p₁ - p₂ + 1` a product of at
most four primes. -/
theorem leaf_sieve_transfer (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight (1 / 2) w₁)
    (hw₂ : SmoothWeight (1 / 2) w₂) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N → X / 2 < (N : ℝ) →
      (N : ℝ) ≤ X → levelSum 0.1635 2 w₁ w₂ X N ≤ X / Real.log X ^ (2 : ℝ) → DiffForm 4 N := by
  sorry

/-- LEAF 3 of the split. The third step: the comparison of exponents. Since `ln X` tends to
infinity, from some height on `C₂ X (ln X)^{-(A+3)} ≤ X (ln X)^{-2}`, so that the level bound
of LEAF 1 is a stronger hypothesis than the threshold that LEAF 2 consumes. -/
theorem leaf_level_threshold_compare (A : ℝ) (hA : 0 < A) (C₂ : ℝ) (hC₂ : 0 ≤ C₂) :
    ∃ X₁ : ℝ, 3 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X →
      C₂ * X / Real.log X ^ (A + 3) ≤ X / Real.log X ^ (2 : ℝ) := by
  sorry

/-- LEAF 4 of the split. The fourth step, the arithmetic in `X` alone: one nonnegative
constant `C` serves both to weaken the level exponent `A + 3` down to `A` on the range
`X ≥ X₁`, and to dominate the standing bound `X₁` by `C X (ln X)^{-A}` on the short range
`2 ≤ X ≤ X₁`. -/
theorem leaf_final_arithmetic (A : ℝ) (hA : 0 < A) (X₁ C₁ : ℝ) (hX₁ : 0 ≤ X₁) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ X : ℝ, 2 ≤ X → C₁ * X / Real.log X ^ (A + 3) ≤ C * X / Real.log X ^ A) ∧
      (∀ X : ℝ, 2 ≤ X → X ≤ X₁ → X₁ ≤ C * X / Real.log X ^ A) := by
  sorry

/-- Cardinality bookkeeping for the assembly: if every `N ∈ (X/2, X]` of type `S` that fails
`Q` also fails `P`, then the `Q`-exceptions of type `S` are among the `P`-exceptions. -/
private theorem excCount_le_of_imp {S P Q : ℕ → Prop} {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ (N : ℕ), X / 2 < (N : ℝ) → (N : ℝ) ≤ X → S N → ¬ Q N → ¬ P N) :
    excCount S Q X ≤ excCount (fun _ => True) P X := by
  unfold excCount
  refine Finset.card_le_card ?_
  intro N hN
  simp only [Finset.mem_filter, Finset.mem_Icc] at hN ⊢
  obtain ⟨⟨h1, h2⟩, hx, hS, hQ⟩ := hN
  have hNX : (N : ℝ) ≤ X := by
    have h2' : (N : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast h2
    have h3 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX
    linarith
  exact ⟨⟨h1, h2⟩, hx, trivial, h N hx hNX hS hQ⟩

/-- The number of `N ∈ (X/2, X]` of type `S` failing `P` never exceeds `⌊X⌋₊`, the number of
integers in the range at all. -/
private theorem excCount_le_floor {S P : ℕ → Prop} (X : ℝ) : excCount S P X ≤ ⌊X⌋₊ := by
  have hcard : (Finset.Icc 1 ⌊X⌋₊).card = ⌊X⌋₊ := by simp
  have hsub : excCount S P X ≤ (Finset.Icc 1 ⌊X⌋₊).card := by
    unfold excCount
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- LEAF assembly: Theorem 1.2, `AlmostAllDyadic Even (DiffForm 4)`, from the four LEAF
statements above, without using `akeno_thm1_2`. -/
theorem akeno_thm1_2_split : AlmostAllDyadic Even (DiffForm 4) := by
  intro A hA
  have hA3 : (0 : ℝ) < A + 3 := by linarith
  obtain ⟨w₁, w₂, C₁, C₂, hC₁0, hC₂0, hw₁, hw₂, hlev⟩ :=
    leaf_level_sum_exception_bound (A + 3) hA3
  obtain ⟨X₀, hX₀3, hsieve⟩ := leaf_sieve_transfer w₁ w₂ hw₁ hw₂
  obtain ⟨X₁, hX₁3, hthr⟩ := leaf_level_threshold_compare A hA C₂ hC₂0
  have hM0 : (0 : ℝ) ≤ max X₀ X₁ := le_trans (by linarith) (le_max_left X₀ X₁)
  obtain ⟨C, hC0, hscale, hshort⟩ := leaf_final_arithmetic A hA (max X₀ X₁) C₁ hM0 hC₁0
  refine ⟨C, fun X hX => ?_⟩
  rcases le_total X (max X₀ X₁) with hcase | hcase
  · have hcard : (excCount Even (DiffForm 4) X : ℝ) ≤ max X₀ X₁ := by
      have h1 : excCount Even (DiffForm 4) X ≤ ⌊X⌋₊ := excCount_le_floor X
      have h2 : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
      exact le_trans (by exact_mod_cast h1) (le_trans h2 hcase)
    exact le_trans hcard (hshort X hX hcase)
  · have hXmax : max X₀ X₁ ≤ X := hcase
    have hX0 : X₀ ≤ X := le_trans (le_max_left X₀ X₁) hXmax
    have hX1 : X₁ ≤ X := le_trans (le_max_right X₀ X₁) hXmax
    have hUp : (0 : ℝ) ≤ X := by linarith
    have hmono : excCount Even (DiffForm 4) X ≤
        excCount (fun _ => True)
          (fun N => levelSum 0.1635 2 w₁ w₂ X N ≤ C₂ * X / Real.log X ^ (A + 3)) X := by
      refine excCount_le_of_imp hUp ?_
      intro N hx hNX hEven hnotD hsmall
      exact hnotD (hsieve X hX0 N hEven hx hNX (le_trans hsmall (hthr X hX1)))
    exact le_trans (by exact_mod_cast hmono) (le_trans (hlev X hX) (hscale X hX))

end LeanLab.Akeno2026
