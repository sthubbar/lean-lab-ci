import LeanLab.Zhan1991.SPLIT_major_1122

/-!
P0068 Zhan 1991, page 271, step 3 of SPLIT_major_1122, the singular integral
`∫_{-L⁴/U}^{L⁴/U} v(λ)³ e(-Nλ) dλ = 3U² L⁻³ + O(U² L⁻⁴)`, split into: the full period identity,
the integral over `[-1/2, 1/2]` counts window triples `n₁ + n₂ + n₃ = N` weighted by
`(log n₁ log n₂ log n₃)⁻¹`; the weighted count is `3U² L⁻³ + O(U² L⁻⁴)`; and the tail
`L⁴/U ≤ |λ| ≤ 1/2` is `O(U² L⁻⁴)`. `singIntEval_of_parts` is PROVED from the three.
burst-20261122, session S80. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real

noncomputable section

/-- The singular integrand `v(λ)³ e(-Nλ)`, page 271. -/
def singIntegrand (N : ℕ) (U lam : ℝ) : ℂ := vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)

/-- The weighted count of window triples `n₁ + n₂ + n₃ = N`, weight `(log n₁ log n₂ log n₃)⁻¹`. -/
def weightedTriples (N : ℕ) (U : ℝ) : ℝ :=
  ∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
    ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
      ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        if n₁ + n₂ + n₃ = N then 1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) else 0

/-- Orthogonality over one period: the full singular integral is the weighted count. -/
def FullPeriodIdentity : Prop :=
  ∀ (N : ℕ) (U : ℝ), (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), singIntegrand N U lam).re =
    weightedTriples N U

/-- The weighted count is `3U² L⁻³ + O(U² L⁻⁴)`: about `3U²` triples, the hexagon area, each of
weight `L⁻³ (1 + O(L⁻¹))`. -/
def WeightedTriplesEval : Prop :=
  ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |weightedTriples N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)
      - 3 * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-3 : ℝ)|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)

/-- The tail `L⁴/U ≤ |λ| ≤ 1/2` of the singular integral is `O(U² L⁻⁴)`, from `v(λ) ≪ 1/(|λ| L)`. -/
def SingIntTail : Prop :=
  ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |(∫ lam in (-(1 / 2 : ℝ))..(-(Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))),
        singIntegrand N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam).re +
      (∫ lam in (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))..(1 / 2),
        singIntegrand N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam).re|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)

/-- The integrand is continuous. PROVED. -/
theorem singIntegrand_continuous (N : ℕ) (U : ℝ) : Continuous (singIntegrand N U) := by
  unfold singIntegrand vSum ee
  fun_prop

/-- Page 271, step 3 from its three parts. PROVED. -/
theorem singIntEval_of_parts (h1 : FullPeriodIdentity) (h2 : WeightedTriplesEval)
    (h3 : SingIntTail) : SingIntEval := by
  intro c hc
  obtain ⟨K2, N2, hK2⟩ := h2 c hc
  obtain ⟨K3, N3, hK3⟩ := h3 c hc
  refine ⟨K2 + K3, max N2 N3, fun N hN => ?_⟩
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c
  set w := Real.log N ^ (4 : ℝ) / U
  have hint : ∀ a b : ℝ, IntervalIntegrable (singIntegrand N U) MeasureTheory.volume a b :=
    fun a b => (singIntegrand_continuous N U).intervalIntegrable a b
  have hsplit : (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), singIntegrand N U lam) =
      (∫ lam in (-(1 / 2 : ℝ))..(-w), singIntegrand N U lam) +
      (∫ lam in (-w)..w, singIntegrand N U lam) +
      (∫ lam in w..(1 / 2), singIntegrand N U lam) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hfull := h1 N U
  rw [hsplit, Complex.add_re, Complex.add_re] at hfull
  have hsi : singInt N U w = (∫ lam in (-w)..w, singIntegrand N U lam).re := rfl
  have e2 := hK2 N ((le_max_left _ _).trans hN)
  have e3 := hK3 N ((le_max_right _ _).trans hN)
  rw [hsi]
  have : (∫ lam in (-w)..w, singIntegrand N U lam).re - 3 * U ^ 2 * Real.log N ^ (-3 : ℝ) =
      (weightedTriples N U - 3 * U ^ 2 * Real.log N ^ (-3 : ℝ)) -
      ((∫ lam in (-(1 / 2 : ℝ))..(-w), singIntegrand N U lam).re +
        (∫ lam in w..(1 / 2), singIntegrand N U lam).re) := by linarith
  rw [this]
  calc _ ≤ |weightedTriples N U - 3 * U ^ 2 * Real.log N ^ (-3 : ℝ)| +
        |(∫ lam in (-(1 / 2 : ℝ))..(-w), singIntegrand N U lam).re +
          (∫ lam in w..(1 / 2), singIntegrand N U lam).re| := abs_sub _ _
    _ ≤ K2 * U ^ 2 * Real.log N ^ (-4 : ℝ) + K3 * U ^ 2 * Real.log N ^ (-4 : ℝ) :=
        add_le_add e2 e3
    _ = _ := by ring

/-- LEAF: Page 271, orthogonality of `e(kλ)` over a full period, expanding `v(λ)³`; the pattern is
`triple_count110` of Decomp110. EASY. -/
theorem fullPeriodIdentity_leaf : FullPeriodIdentity := by
  sorry

/-- LEAF: Page 271, the weighted count of window triples: the hexagon `|x₁|, |x₂|, |x₁ + x₂| ≤ U`
has area `3U²` with lattice error `O(U)`, and `log nᵢ = L + O(1)`. MEDIUM. -/
theorem weightedTriplesEval_leaf : WeightedTriplesEval := by
  sorry

/-- LEAF: Page 271, the tail of the singular integral, `|v(λ)| ≪ 1/(|λ| L)` by partial summation,
integrated over `|λ| ≥ L⁴/U`. MEDIUM. -/
theorem singIntTail_leaf : SingIntTail := by
  sorry

/-- Step 3 of the major arc split through its three LEAFs. -/
theorem singIntEval_split : SingIntEval :=
  singIntEval_of_parts fullPeriodIdentity_leaf weightedTriplesEval_leaf singIntTail_leaf

end

end LeanLab.Zhan1991
