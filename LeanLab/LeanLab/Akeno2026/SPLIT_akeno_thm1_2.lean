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

/-! ### Helpers for LEAF 3: the comparison of exponents -/

private theorem akeno_log_rpow_tendsto (A : ℝ) (hA : 0 < A) :
    Filter.Tendsto (fun X : ℝ => Real.log X ^ (A + 1)) Filter.atTop Filter.atTop :=
  (tendsto_rpow_atTop (by linarith : (0 : ℝ) < A + 1)).comp Real.tendsto_log_atTop

private theorem akeno_exists_log_rpow_ge (A C : ℝ) (hA : 0 < A) :
    ∃ X₁ : ℝ, 3 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X → C ≤ Real.log X ^ (A + 1) := by
  have h : ∀ᶠ X : ℝ in Filter.atTop, C ≤ Real.log X ^ (A + 1) :=
    (akeno_log_rpow_tendsto A hA).eventually (Filter.eventually_ge_atTop C)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  exact ⟨max 3 N, le_max_left 3 N, fun X hX => hN X (le_trans (le_max_right 3 N) hX)⟩

/-- The division step of LEAF 3: with `log X > 0`, `C ≤ (log X)^{A+1}` turns
`C X (log X)^{-(A+3)}` into at most `X (log X)^{-2}`. -/
private theorem akeno_rpow_log_ratio {A C X : ℝ} (hX : 3 ≤ X)
    (h : C ≤ Real.log X ^ (A + 1)) :
    C * X / Real.log X ^ (A + 3) ≤ X / Real.log X ^ (2 : ℝ) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL1 : (0 : ℝ) < Real.log X ^ (A + 1) := Real.rpow_pos_of_pos hL (A + 1)
  have hL2 : (0 : ℝ) < Real.log X ^ (2 : ℝ) := Real.rpow_pos_of_pos hL 2
  have hp : Real.log X ^ (A + 3) = Real.log X ^ (A + 1) * Real.log X ^ (2 : ℝ) := by
    rw [show A + 3 = (A + 1) + 2 by ring, Real.rpow_add hL]
  have hmain : C * Real.log X ^ (2 : ℝ) ≤ Real.log X ^ (A + 1) * Real.log X ^ (2 : ℝ) :=
    mul_le_mul_of_nonneg_right h (le_of_lt hL2)
  rw [hp, div_le_div_iff₀ (mul_pos hL1 hL2) hL2]
  calc C * X * Real.log X ^ (2 : ℝ)
      = X * (C * Real.log X ^ (2 : ℝ)) := by ring
    _ ≤ X * (Real.log X ^ (A + 1) * Real.log X ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hX0)

/-! ### Helpers for LEAF 4: the arithmetic in `X` alone -/

/-- The long-range half of LEAF 4: since `log X ≥ log 2 > 0`, the constant
`C₁ / (log 2)^3` weakens `(log X)^{-(A+3)}` to `(log X)^{-A}`. -/
private theorem akeno_scale_le {A C₁ C X : ℝ} (hC₁ : 0 ≤ C₁)
    (hC : C₁ / Real.log 2 ^ (3 : ℝ) ≤ C) (hX : 2 ≤ X) :
    C₁ * X / Real.log X ^ (A + 3) ≤ C * X / Real.log X ^ A := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hpow : Real.log X ^ (A + 3) = Real.log X ^ A * Real.log X ^ (3 : ℝ) := by
    rw [Real.rpow_add hL]
  have hc3 : C₁ ≤ C * Real.log X ^ (3 : ℝ) := by
    have h1 : Real.log 2 ^ (3 : ℝ) ≤ Real.log X ^ (3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hL2) hlog (by norm_num)
    have h2 : C₁ / Real.log 2 ^ (3 : ℝ) * Real.log 2 ^ (3 : ℝ) = C₁ := by
      field_simp
    calc C₁ = C₁ / Real.log 2 ^ (3 : ℝ) * Real.log 2 ^ (3 : ℝ) := h2.symm
      _ ≤ C * Real.log X ^ (3 : ℝ) :=
          mul_le_mul hC h1 (by positivity) (le_trans (div_nonneg hC₁ (by positivity)) hC)
  rw [hpow, div_le_div_iff₀ (by positivity) (Real.rpow_pos_of_pos hL A)]
  have hmul : C₁ * (X * Real.log X ^ A) ≤ C * Real.log X ^ (3 : ℝ) * (X * Real.log X ^ A) :=
    mul_le_mul_of_nonneg_right hc3
      (mul_nonneg (le_of_lt hX0) (le_of_lt (Real.rpow_pos_of_pos hL A)))
  calc C₁ * X * Real.log X ^ A = C₁ * (X * Real.log X ^ A) := by ring
    _ ≤ C * Real.log X ^ (3 : ℝ) * (X * Real.log X ^ A) := hmul
    _ = C * X * (Real.log X ^ A * Real.log X ^ (3 : ℝ)) := by ring

/-- The short-range half of LEAF 4: on `2 ≤ X ≤ X₁` the bound `X₁ (log X₁)^A` dominates `X₁`,
since `(log X)^A ≤ (log X₁)^A` and `X ≥ 2`. -/
private theorem akeno_short_le {A X₁ C X : ℝ} (hA : 0 < A) (hX₁ : 0 ≤ X₁)
    (hC : X₁ * Real.log X₁ ^ A ≤ C) (hX : 2 ≤ X) (hXX : X ≤ X₁) :
    X₁ ≤ C * X / Real.log X ^ A := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX₁2 : 2 ≤ X₁ := le_trans hX hXX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL₁ : 0 < Real.log X₁ := Real.log_pos (by linarith)
  have hM : (0 : ℝ) < Real.log X₁ ^ A := Real.rpow_pos_of_pos hL₁ A
  have hle : Real.log X ^ A ≤ Real.log X₁ ^ A :=
    Real.rpow_le_rpow (le_of_lt hL) (Real.log_le_log hX0 hXX) (le_of_lt hA)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hL A)]
  have h1 : X₁ * Real.log X ^ A ≤ X₁ * (Real.log X₁ ^ A * X) := by
    refine mul_le_mul_of_nonneg_left ?_ hX₁
    calc Real.log X ^ A ≤ Real.log X₁ ^ A := hle
      _ ≤ Real.log X₁ ^ A * X := le_mul_of_one_le_right (le_of_lt hM) (by linarith)
  calc X₁ * Real.log X ^ A ≤ X₁ * (Real.log X₁ ^ A * X) := h1
    _ = X₁ * Real.log X₁ ^ A * X := by ring
    _ ≤ C * X := mul_le_mul_of_nonneg_right hC (le_of_lt hX0)

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
  have h0 : SmoothWeight (1 / 2) (0 : ℝ → ℝ) := ⟨contDiff_const, by simp [Function.support]⟩
  obtain ⟨C₁, C₂, hC⟩ := akeno_thm1_1 0.1635 (by norm_num) (by norm_num) A hA 2 (1 / 2)
    (by norm_num) (0 : ℝ → ℝ) (0 : ℝ → ℝ) h0 h0
  refine ⟨0, 0, |C₁|, |C₂|, abs_nonneg _, abs_nonneg _, h0, h0, fun X hX => ?_⟩
  have hpos : (0 : ℝ) ≤ X / Real.log X ^ A := by
    have hL : 0 < Real.log X := Real.log_pos (by linarith)
    positivity
  have hC₂ : C₂ * X / Real.log X ^ A ≤ |C₂| * X / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self C₂) hpos
  have hC₁ : C₁ * X / Real.log X ^ A ≤ |C₁| * X / Real.log X ^ A := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self C₁) hpos
  refine le_trans (by exact_mod_cast (excCount_mono (S := fun _ => True)
    (P := fun N => levelSum 0.1635 2 0 0 X N ≤ C₂ * X / Real.log X ^ A)
    (Q := fun N => levelSum 0.1635 2 0 0 X N ≤ |C₂| * X / Real.log X ^ A)
    (fun N _ hN => le_trans hN hC₂) X)) (le_trans (hC X hX) hC₁)


/-! ### Helpers for LEAF 2: the zero weights make the level-sum hypothesis vacuous -/

/-- With the zero weights the remainder R_{d,l}(N) vanishes. -/
theorem akeno_Rdl_zero (X : ℝ) (N d : ℕ) (l : ℤ) : Rdl 0 0 X N d l = 0 := by
  unfold Rdl
  simp

/-- With the zero weights the supremum of the remainders is zero. -/
theorem akeno_supR_zero (X : ℝ) (N d : ℕ) : supR 0 0 X N d = 0 := by
  unfold supR
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro l hl
    rw [akeno_Rdl_zero]
    simp
  · exact bot_le

/-- With the zero weights the level sum vanishes, so the level-sum hypothesis of LEAF 2
carries no content for the zero weights. -/
theorem akeno_levelSum_zero (θ : ℝ) (k : ℕ) (X : ℝ) (N : ℕ) :
    levelSum θ k 0 0 X N = 0 := by
  unfold levelSum
  apply Finset.sum_eq_zero
  intro d hd
  simp [akeno_supR_zero]

/-- Any statement of the weighted-sieve transfer of the shape of LEAF 2, applied to the zero
weights, gives binary Goldbach for every sufficiently large even integer, since the zero
weights make the level sum zero, so the level-sum hypothesis then holds for every N. -/
theorem leaf_sieve_transfer_zero_weight_goldbach
    (hzero : ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N → X / 2 < (N : ℝ) →
      (N : ℝ) ≤ X → levelSum 0.1635 2 0 0 X N ≤ X / Real.log X ^ (2 : ℝ) → DiffForm 4 N) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ N : ℕ, Even N → X₀ ≤ (N : ℝ) → IsGoldbachSum N := by
  obtain ⟨X₀, hX₀3, h⟩ := hzero
  refine ⟨X₀, hX₀3, ?_⟩
  intro N hEven hN
  have hN3 : (3 : ℝ) ≤ (N : ℝ) := le_trans hX₀3 hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlevel : levelSum 0.1635 2 0 0 (N : ℝ) N = 0 := akeno_levelSum_zero _ _ _ _
  have hbound : levelSum 0.1635 2 0 0 (N : ℝ) N ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by
    rw [hlevel]
    have hpow : (0 : ℝ) < Real.log (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hlog 2
    exact div_nonneg (le_of_lt hN0) (le_of_lt hpow)
  have hd := h (N : ℝ) hN N hEven (by linarith) le_rfl hbound
  exact isGoldbachSum_of_diffForm hd

/-- LEAF 2 of the split. The second step: the weighted sieve of Proposition 4.4, at
`s = 33.5` and `t = 9.5`. For any two smooth weights supported in `[1/2, 1]` there is a
height beyond which every even `N ∈ (X/2, X]` whose weighted level sum is at most
`X (ln X)^{-2}` is a sum `p₁ + p₂` of primes with `p₁ ≥ p₂` and `p₁ - p₂ + 1` a product of at
most four primes. -/
theorem leaf_sieve_transfer (w₁ w₂ : ℝ → ℝ) (hw₁ : SmoothWeight (1 / 2) w₁)
    (hw₂ : SmoothWeight (1 / 2) w₂) :
    ∃ X₀ : ℝ, 3 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ N : ℕ, Even N → X / 2 < (N : ℝ) →
      (N : ℝ) ≤ X → levelSum 0.1635 2 w₁ w₂ X N ≤ X / Real.log X ^ (2 : ℝ) → DiffForm 4 N := by
  -- BLOCKED, OUT OF REACH, 2026-11-11. The exact missing result is Proposition 4.4 of
  -- Akeno 2026, arXiv 2606.29559, at theta = 0.1635, s = 33.5 and t = 9.5, which the lab
  -- has never formalized. The attempt to apply it, namely
  --   exact akeno_prop4_4 33.5 9.5 (by norm_num) (by norm_num) w₁ w₂ hw₁ hw₂
  -- fails with the Lean error Unknown identifier akeno_prop4_4, reported at line 193
  -- of this file in the attempt run.
  -- The same unknown identifier error comes from #check for akeno_prop_4_4, prop44,
  -- prop4_4, weightedSieve, akeno_weighted_sieve, akeno_sieve_transfer, sieve_transfer,
  -- weighted_sieve_transfer, Prop44, M_k and Mk. Mathlib has no such result: LeanSearch
  -- for a weighted sieve transfer from a level of distribution returns only
  -- Mathlib.NumberTheory.SelbergSieve, the generic sieve framework, and no Goldbach
  -- theorem. The paper states Proposition 4.4 as an almost all statement over N given
  -- M_k of F, theta and s positive, not as a per N transfer from a level sum bound, so
  -- this leaf as written is stronger than the paper. The helper
  -- leaf_sieve_transfer_zero_weight_goldbach above shows that any statement of this shape,
  -- applied to the zero weights, gives binary Goldbach for every sufficiently large even
  -- integer, so closing this leaf needs the weighted sieve input itself.
  sorry


/-- LEAF 3 of the split. The third step: the comparison of exponents. Since `ln X` tends to
infinity, from some height on `C₂ X (ln X)^{-(A+3)} ≤ X (ln X)^{-2}`, so that the level bound
of LEAF 1 is a stronger hypothesis than the threshold that LEAF 2 consumes. -/
theorem leaf_level_threshold_compare (A : ℝ) (hA : 0 < A) (C₂ : ℝ) (hC₂ : 0 ≤ C₂) :
    ∃ X₁ : ℝ, 3 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X →
      C₂ * X / Real.log X ^ (A + 3) ≤ X / Real.log X ^ (2 : ℝ) := by
  obtain ⟨X₁, h3, hX⟩ := akeno_exists_log_rpow_ge A C₂ hA
  exact ⟨X₁, h3, fun X hX' => akeno_rpow_log_ratio (le_trans h3 hX') (hX X hX')⟩


/-- LEAF 4 of the split. The fourth step, the arithmetic in `X` alone: one nonnegative
constant `C` serves both to weaken the level exponent `A + 3` down to `A` on the range
`X ≥ X₁`, and to dominate the standing bound `X₁` by `C X (ln X)^{-A}` on the short range
`2 ≤ X ≤ X₁`. -/
theorem leaf_final_arithmetic (A : ℝ) (hA : 0 < A) (X₁ C₁ : ℝ) (hX₁ : 0 ≤ X₁) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ X : ℝ, 2 ≤ X → C₁ * X / Real.log X ^ (A + 3) ≤ C * X / Real.log X ^ A) ∧
      (∀ X : ℝ, 2 ≤ X → X ≤ X₁ → X₁ ≤ C * X / Real.log X ^ A) := by
  refine ⟨max (C₁ / Real.log 2 ^ (3 : ℝ)) (max 0 (X₁ * Real.log X₁ ^ A)), by positivity, ?_, ?_⟩
  · intro X hX
    exact akeno_scale_le hC₁ (le_max_left _ _) hX
  · intro X hX hXX
    exact akeno_short_le hA hX₁
      (le_trans (le_max_right 0 (X₁ * Real.log X₁ ^ A))
        (le_max_right (C₁ / Real.log 2 ^ (3 : ℝ)) (max 0 (X₁ * Real.log X₁ ^ A)))) hX hXX


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
