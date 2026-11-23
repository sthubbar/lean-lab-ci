import LeanLab.Zhan1991.Decomp110

/-!
P0068 Zhan 1991, the major arc evaluation of page 271, `major_evaluation110` of Decomp110.lean,
split along the standard method the paper cites from Pan and Pan, reference 2, burst-20261122.

Page 271 prints one display only: the integral over `E₁` equals `3 𝔖(N) U² L⁻³ + O(U² L⁻⁴)`,
"by the standard method as in [2]". Reference 2 is not in the lab. The steps below are the
standard circle method steps that display rests on:
1. the major arc approximation `S(a/q + λ) = μ(q)/φ(q) v(λ) + error`, a short interval
   Siegel Walfisz input, cited;
2. the assembly over the arcs, giving the truncated singular series times the singular integral;
3. the singular integral, `3 U² L⁻³ + O(U² L⁻⁴)`;
4. the truncated singular series, `𝔖(N) + O(L⁻¹)`;
5. `𝔖(N)` is bounded.
`majorEval_of_steps` is PROVED from steps 2 to 5.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

noncomputable section
open Real
open scoped ArithmeticFunction.Moebius

/-- Page 271, the standard major arc main term: `v(λ) = Σ_{N₁ < n ≤ N₂} e(nλ) / log n` over the
integers of the window `[N/3 - U, N/3 + U]`, with the endpoint convention of `Win`. -/
def vSum (N : ℕ) (U lam : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
    ee ((n : ℝ) * lam) / (Real.log n : ℂ)

/-- The Ramanujan sum `c_q(N) = Σ_{a mod q, (a, q) = 1} e(aN/q)`, real since the reduced
residues are closed under negation; page 271, the singular series. -/
def ramanujanC (q N : ℕ) : ℝ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    Real.cos (2 * π * (a : ℝ) * N / q)

/-- Page 271, the truncated singular series `Σ_{q ≤ Q₁} μ(q) c_q(N) / φ(q)³`. -/
def singTrunc (N : ℕ) (Q : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N

/-- Page 271, the singular integral over one arc, `Re ∫_{-w}^{w} v(λ)³ e(-Nλ) dλ`. -/
def singInt (N : ℕ) (U w : ℝ) : ℝ :=
  (∫ lam in (-w)..w, vSum N U lam ^ 3 * ee (-(N : ℝ) * lam)).re

/-- Step 1, the major arc approximation: for `q ≤ L^d`, `(a, q) = 1` and `|λ| ≤ L⁴/U`,
`Σ_{N₁ < p ≤ N₂} e(p(a/q + λ)) = μ(q)/φ(q) v(λ) + O(U L^{-A})` for every `A`. -/
def MajorArcApprox : Prop :=
  ∀ d c A : ℝ, 0 < d → 0 < c → 0 < A → ∃ K N₀ : ℝ, ∀ (N : ℕ) (q : ℕ) (a : ℤ) (lam : ℝ),
    N₀ ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ d → Int.gcd a q = 1 →
    |lam| ≤ Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) →
    ‖primeSum110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ((a : ℝ) / q + lam) -
        ((μ q : ℝ) / (Nat.totient q : ℝ) : ℂ) *
          vSum N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) lam‖
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) * Real.log N ^ (-A)

/-- Step 2, the arcs assembled: the major term is the truncated singular series times the
singular integral, up to `O(U² L⁻⁴)`, for every large cutoff exponent `d`. -/
def MajorAssembly : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
    ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
        - singTrunc N (Real.log N ^ d) *
            singInt N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)
              (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))|
        ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)

/-- Step 3, the singular integral: `3 U² L⁻³ + O(U² L⁻⁴)`. -/
def SingIntEval : Prop :=
  ∀ c : ℝ, 0 < c → ∃ K N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    |singInt N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)
        (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c))
      - 3 * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-3 : ℝ)|
      ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 * Real.log N ^ (-4 : ℝ)

/-- Step 4, the truncated singular series: `𝔖(N) + O(L⁻¹)` at `Q₁ = L^d` for large `d`. -/
def SingTruncEval : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
    |singTrunc N (Real.log N ^ d) - Sing N| ≤ K / Real.log N

/-- Step 5, `𝔖(N)` is bounded. -/
def SingBounded : Prop := ∃ C : ℝ, ∀ N : ℕ, |Sing N| ≤ C

/-- LEAF: Page 271, step 1 of the standard method of reference 2, the major arc approximation
by a short interval Siegel Walfisz theorem for `U = N^{5/8} L^c`, which is above Huxley's
`N^{7/12 + ε}`. HARD, cited input. The lab's KumchevLiu2007 `thetaChi_short` is the same
citation wall in theta form, also cited. -/
theorem majorArcApprox_cited : MajorArcApprox := by
  sorry

/-- LEAF: Page 271, step 2 of the standard method, from step 1. HARD. The arcs `I(q, a)` are
disjoint for large `N`; the two half arcs at 0 and 1 form one arc by periodicity; on each arc
`|S³ - (μ(q)/φ(q) v)³| ≪ U² · U L^{-A}`, over at most `L^{2d}` arcs of length `2 L⁴/U`, so
`A = 2d + 8` suffices; then sum `e(-aN/q)` over `a` to get `c_q(N)`, and `μ(q)³ = μ(q)`. -/
theorem majorAssembly_of_approx (h1 : MajorArcApprox) : MajorAssembly := by
  sorry

/-- LEAF: Page 271, step 3 of the standard method, the singular integral. MEDIUM. Over the
whole period the integral counts `n₁ + n₂ + n₃ = N` in the window weighted by
`(log n₁ log n₂ log n₃)⁻¹`: about `3U²` triples, the hexagon area, each weighted
`L⁻³ (1 + O(L⁻¹))`; the tail `|λ| > L⁴/U` is `O(U² L⁻¹¹)` from `v(λ) ≪ 1/(|λ| L)`. -/
theorem singIntEval_leaf : SingIntEval := by
  sorry

/-- LEAF: Page 271, step 4 of the standard method, the singular series tail. MEDIUM.
`μ(q) c_q(N) / φ(q)³` is multiplicative with Euler factor `1 - 1/(p-1)²` for `p ∣ N` and
`1 + 1/(p-1)³` otherwise, matching `Sing`; `|c_q(N)| ≤ (q, N)` gives the tail beyond `Q₁`
as `O(Q₁^{-1+ε} (log log N)³)`, which is `O(L⁻¹)` at `Q₁ = L^d`, `d ≥ 2`. -/
theorem singTruncEval_leaf : SingTruncEval := by
  sorry

/-- LEAF: Page 260, the singular series is bounded: every factor of `Sing` lies in `[0, 2]`
and `∏ (1 + 1/(p-1)³)` over odd primes converges. EASY. -/
theorem singBounded_leaf : SingBounded := by
  sorry

/-- Page 271, the major arc display after (3.21), PROVED from steps 2 to 5. -/
theorem majorEval_of_steps (h2 : MajorAssembly) (h3 : SingIntEval) (h4 : SingTruncEval)
    (h5 : SingBounded) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) := by
  obtain ⟨a₀, ha₀, hA⟩ := h2
  obtain ⟨b₀, hb₀, hB⟩ := h4
  obtain ⟨C, hC⟩ := h5
  refine ⟨max a₀ b₀, lt_of_lt_of_le ha₀ (le_max_left _ _), ?_⟩
  intro d hd c hc
  obtain ⟨K2, N2, hK2⟩ := hA d ((le_max_left _ _).trans hd) c hc
  obtain ⟨K4, N4, hK4⟩ := hB d ((le_max_right _ _).trans hd)
  obtain ⟨K3, N3, hK3⟩ := h3 c hc
  refine ⟨|K2| + |K4| * (3 + |K3|) + |C| * |K3|, max (max N2 N3) (max N4 (Real.exp 1)), ?_⟩
  intro N hN hlarge
  have hN2 : N2 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hlarge)
  have hN3 : N3 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hlarge)
  have hN4 : N4 ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have he : Real.exp 1 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) he
  have hLpos : 0 < Real.log N := by linarith
  set L := Real.log N with hLdef
  set U := (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c with hU
  set M := majorTerm110 N U d
  set sT := singTrunc N (L ^ d)
  set I := singInt N U (L ^ (4 : ℝ) / U)
  have e2 := hK2 N hN hN2
  have e3 := hK3 N hN3
  have e4 := hK4 N hN hN4
  have hC0 : |Sing N| ≤ |C| := (hC N).trans (le_abs_self _)
  have h4eq : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) / L := by
    rw [show (-4 : ℝ) = -3 - 1 by norm_num, Real.rpow_sub hLpos, Real.rpow_one]
  have hP3 : 0 ≤ U ^ 2 * L ^ (-3 : ℝ) := by
    have := Real.rpow_nonneg hLpos.le (-3 : ℝ); positivity
  have hP4 : 0 ≤ U ^ 2 * L ^ (-4 : ℝ) := by
    have := Real.rpow_nonneg hLpos.le (-4 : ℝ); positivity
  have hP43 : U ^ 2 * L ^ (-4 : ℝ) ≤ U ^ 2 * L ^ (-3 : ℝ) := by
    rw [h4eq, mul_div_assoc']
    exact div_le_self hP3 hL1
  have hI : |I| ≤ (3 + |K3|) * (U ^ 2 * L ^ (-3 : ℝ)) := by
    have hK3' : K3 * U ^ 2 * L ^ (-4 : ℝ) ≤ |K3| * (U ^ 2 * L ^ (-3 : ℝ)) := by
      calc K3 * U ^ 2 * L ^ (-4 : ℝ) = K3 * (U ^ 2 * L ^ (-4 : ℝ)) := by ring
        _ ≤ |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hP4
        _ ≤ |K3| * (U ^ 2 * L ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hP43 (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub I (3 * U ^ 2 * L ^ (-3 : ℝ))
    have h3abs : |3 * U ^ 2 * L ^ (-3 : ℝ)| = 3 * (U ^ 2 * L ^ (-3 : ℝ)) := by
      rw [abs_of_nonneg (by nlinarith)]; ring
    rw [h3abs] at this
    nlinarith
  have hmid : |sT - Sing N| * |I| ≤ |K4| * (3 + |K3|) * (U ^ 2 * L ^ (-4 : ℝ)) := by
    have hs : |sT - Sing N| ≤ |K4| / L :=
      e4.trans (div_le_div_of_nonneg_right (le_abs_self _) hLpos.le)
    calc |sT - Sing N| * |I| ≤ (|K4| / L) * ((3 + |K3|) * (U ^ 2 * L ^ (-3 : ℝ))) :=
          mul_le_mul hs hI (abs_nonneg _) (by positivity)
      _ = |K4| * (3 + |K3|) * (U ^ 2 * (L ^ (-3 : ℝ) / L)) := by ring
      _ = |K4| * (3 + |K3|) * (U ^ 2 * L ^ (-4 : ℝ)) := by rw [h4eq]
  have hlast : |Sing N| * |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| ≤ |C| * |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := by
    have hK3'' : |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| ≤ |K3| * (U ^ 2 * L ^ (-4 : ℝ)) :=
      e3.trans (by
        calc K3 * U ^ 2 * L ^ (-4 : ℝ) = K3 * (U ^ 2 * L ^ (-4 : ℝ)) := by ring
          _ ≤ |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hP4)
    calc |Sing N| * |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| ≤ |C| * (|K3| * (U ^ 2 * L ^ (-4 : ℝ))) :=
          mul_le_mul hC0 hK3'' (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hfirst : |M - sT * I| ≤ |K2| * (U ^ 2 * L ^ (-4 : ℝ)) :=
    e2.trans (by
      calc K2 * U ^ 2 * L ^ (-4 : ℝ) = K2 * (U ^ 2 * L ^ (-4 : ℝ)) := by ring
        _ ≤ |K2| * (U ^ 2 * L ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hP4)
  have hsplit : M - 3 * Sing N * U ^ 2 * L ^ (-3 : ℝ) =
      (M - sT * I) + (sT - Sing N) * I + Sing N * (I - 3 * U ^ 2 * L ^ (-3 : ℝ)) := by ring
  rw [hsplit]
  calc |(M - sT * I) + (sT - Sing N) * I + Sing N * (I - 3 * U ^ 2 * L ^ (-3 : ℝ))|
      ≤ |M - sT * I| + |(sT - Sing N) * I| + |Sing N * (I - 3 * U ^ 2 * L ^ (-3 : ℝ))| :=
        abs_add_three _ _ _
    _ = |M - sT * I| + |sT - Sing N| * |I| + |Sing N| * |I - 3 * U ^ 2 * L ^ (-3 : ℝ)| := by
        rw [abs_mul, abs_mul]
    _ ≤ |K2| * (U ^ 2 * L ^ (-4 : ℝ)) + |K4| * (3 + |K3|) * (U ^ 2 * L ^ (-4 : ℝ)) +
        |C| * |K3| * (U ^ 2 * L ^ (-4 : ℝ)) := by linarith
    _ = _ := by ring

/-- `major_evaluation110` through the split: step 1 cited, steps 2 to 5 LEAFs. Shows `sorryAx`
until they close. -/
theorem major_evaluation_split :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) :=
  majorEval_of_steps (majorAssembly_of_approx majorArcApprox_cited) singIntEval_leaf
    singTruncEval_leaf singBounded_leaf

end

end LeanLab.Zhan1991
