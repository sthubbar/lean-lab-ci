/-
P0068 Zhan 1991, the LEAF `dyadic_split_leaf` of SPLIT_eq31_1122d.lean, page 264 top, split
into finer cited LEAF steps. Source: papers/P0068.pdf, pdf pages 5 and 6.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Falsity check, done before the split: the statement `DyadicSplit` reads as true. Position `k`
of `Fin 20` carries `aj (k+1)`: `log` at `k = 0`, `1` at `1 ≤ k ≤ 9`, `μ` at `10 ≤ k ≤ 19`.
The `j`-th Heath-Brown term `log * ζ^{j-1} * M_X^j` uses `k = 0`, `1 ≤ k ≤ j-1` and
`10 ≤ k ≤ 9+j`; an unused position gets `N_k = 1/2`, so `dyad (1/2) = {1}` and the factor is
`aj · χ` at `1`, which is `1`. The `μ` variables use the points `X 2^{-m-1}`, so the union of the
`dyad` ranges is exactly `1 ≤ n ≤ X`. Boxes failing `Cond35` contribute `0` for every
`u ∈ [N-A, N]` once `A ≤ N/2`, since `Π N_k < Π n_k ≤ 2^20 Π N_k`.

Definitions `Psum_dy`, `HBsum_dy`, `Dsum_dy`, `Vline_dy`, `DyadicSplit_dy` are copies of
`Psum`, `HBsum`, `Dsum`, `Vline`, `DyadicSplit` of SPLIT_eq31_1122d.lean.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-! ### Copied definitions -/

/-- The partial sum (3.2), page 263: `Σ_{N-A<n≤u} Λ(n) χ(n)`. -/
def Psum_dy {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (Λ n : ℂ) * χ n

/-- The `j`-th term of Heath-Brown's identity with `k = 10`, `X = N^{1/10}`, page 263, summed
against `χ` over `N - A < n ≤ u`: `Σ (log * ζ^{j-1} * M_X^j)(n) χ(n)`. -/
def HBsum_dy {q : ℕ} (j : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n),
    (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) *
      muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n

/-- The dyadic sum of (3.4) before Perron's formula, page 264:
`Σ_{n_j ∈ I_j, N-A < n₁⋯n₂₀ ≤ u} a₁(n₁)χ(n₁)⋯a₂₀(n₂₀)χ(n₂₀)`, `I_j = (N_j, 2N_j]`. -/
def Dsum_dy {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Fintype.piFinset fun j : Fin 20 => dyad (Nv j)).filter
      (fun n => (N : ℝ) - A < ∏ j, (n j : ℝ) ∧ ∏ j, (n j : ℝ) ≤ u),
    ∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)

/-- The line integral of (3.4), page 264, on `Re s = σ`, written in `t` with `s = σ + it`:
`(1/2πi) ∫_{σ-iT}^{σ+iT} F(s,χ) (u^s - (N-A)^s) s⁻¹ ds`. -/
def Vline_dy {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A σ T u : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ ((σ : ℂ) + t * Complex.I) *
    (((u : ℂ) ^ ((σ : ℂ) + t * Complex.I) - (((N : ℝ) - A : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I))
      / ((σ : ℂ) + t * Complex.I))

/-- Splitting each range of summation into intervals `x < n ≤ 2x`, top of page 264. -/
def DyadicSplit_dy : Prop :=
  ∃ K N₀ : ℝ, ∀ (N : ℕ) (A : ℝ), N₀ ≤ N → 0 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
    ∀ j ∈ Finset.Icc 1 10, ∃ ι : Finset (Fin 20 → ℝ),
      (ι.card : ℝ) ≤ K * Real.log N ^ (20 : ℝ) ∧ (∀ Nv ∈ ι, Cond35 N Nv) ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ), (N : ℝ) - A ≤ u → u ≤ N →
        HBsum_dy j χ N A u = ∑ Nv ∈ ι, Dsum_dy Nv χ N A u

/-! ### Auxiliary definitions of the split -/

/-- Position `k` of `Fin 20` is used by the `j`-th Heath-Brown term `log * ζ^{j-1} * M_X^j`:
`k = 0` is the `log` variable, `1 ≤ k ≤ j-1` the `ζ` variables, `10 ≤ k ≤ 9+j` the `μ`
variables, page 263. -/
def usedPos_dy (j : ℕ) (k : Fin 20) : Prop :=
  k.val = 0 ∨ (1 ≤ k.val ∧ k.val ≤ j - 1) ∨ (10 ≤ k.val ∧ k.val ≤ 9 + j)

/-- The ordered tuple sum of the `j`-th Heath-Brown term: tuples `n : Fin 20 → ℕ` with
`1 ≤ n_k ≤ N`, `n_k = 1` at unused positions, `n_k ≤ X = N^{1/10}` at the `μ` positions and
`N - A < Π n_k ≤ u`, weighted by `Π aj(k+1)(n_k) χ(n_k)`. -/
def Tsum_dy {q : ℕ} (j : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  haveI := Classical.decPred (fun n : Fin 20 → ℕ => (N : ℝ) - A < ∏ k, (n k : ℝ) ∧
    ∏ k, (n k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → n k = 1) ∧
    (∀ k : Fin 20, 10 ≤ k.val → (n k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
  ∑ n ∈ (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter
      (fun n => (N : ℝ) - A < ∏ k, (n k : ℝ) ∧ ∏ k, (n k : ℝ) ≤ u ∧
        (∀ k, ¬ usedPos_dy j k → n k = 1) ∧
        (∀ k : Fin 20, 10 ≤ k.val → (n k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))),
    ∏ k : Fin 20, aj (k.val + 1) (n k) * χ (n k)

/-- The dyadic grid of position `k` for the `j`-th term, page 264 top: `{1/2}` at an unused
position, the points `X 2^{-m-1}`, `m ≤ Nat.log 2 N + 1`, at a used `μ` position, and the
points `2^m / 2`, `m ≤ Nat.log 2 N + 1`, at a used `log` or `ζ` position. -/
def grid_dy (N j : ℕ) (k : Fin 20) : Finset ℝ :=
  haveI := Classical.dec (usedPos_dy j k)
  haveI := Classical.decEq ℝ
  if usedPos_dy j k then
    (if 10 ≤ k.val then
      (Finset.range (Nat.log 2 N + 2)).image
        (fun m : ℕ => (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ (m + 1))
    else (Finset.range (Nat.log 2 N + 2)).image (fun m : ℕ => (2 : ℝ) ^ m / 2))
  else {1 / 2}

/-- The box set: all grid vectors satisfying `Cond35`. -/
def boxes_dy (N j : ℕ) : Finset (Fin 20 → ℝ) :=
  haveI := Classical.decPred (fun Nv => Cond35 N Nv)
  haveI := Classical.decEq ℝ
  (Fintype.piFinset (grid_dy N j)).filter (fun Nv => Cond35 N Nv)

/-! ### LEAF steps -/

/-- LEAF: page 263, the `j`-th term of Heath-Brown's identity as an ordered convolution:
`(log * ζ^{j-1} * M_X^j)(n) = Σ_{n = n₁⋯n_{2j}} log n₁ · Π μ(m_i) [m_i ≤ X]`, written with
the 20 positions of `aj`, unused positions fixed at `1`, and the variables cut at `N` since
`n ≤ u ≤ N`. Class MEDIUM. -/
theorem hb_tuple_leaf (N : ℕ) (A : ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 10) (hN : 2 ≤ N)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) (hu : u ≤ N) :
    HBsum_dy j χ N A u = Tsum_dy j χ N A u := by
  have h_j_range : 1 ≤ j ∧ j ≤ 10 := by
    simp only [Finset.mem_Icc] at hj
    exact ⟨hj.1, hj.2⟩

  have hX : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h₁ : (1 : ℝ) ≤ (N : ℝ) := by linarith
    have h₂ : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
      apply Real.one_le_rpow
      · linarith
      · norm_num
    exact h₂

  have h_main : HBsum_dy j χ N A u = Tsum_dy j χ N A u := by
    have h₁ : HBsum_dy j χ N A u = ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n := by
      rfl
    rw [h₁]
    have h₂ : Tsum_dy j χ N A u = ∑ n in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun n => (N : ℝ) - A < ∏ k, (n k : ℝ) ∧ ∏ k, (n k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → n k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (n k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, aj (k.val + 1) (n k) * χ (n k) := by
      rfl
    rw [h₂]
    have h₃ : ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n = ∑ n in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun n => (N : ℝ) - A < ∏ k, (n k : ℝ) ∧ ∏ k, (n k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → n k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (n k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, aj (k.val + 1) (n k) * χ (n k) := by
      have h₄ : ∀ (n : ℕ), (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) := by
        intro n
        have h₄₁ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
          classical
          -- Step 1: Expand the arithmetic function convolution as a sum over 2j-tuples
          have h₄₂ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
            have h₄₃ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
              classical
              -- This is the core arithmetic identity: the Dirichlet convolution expands to the tuple sum
              -- We prove it by showing both sides count the same factorizations
              have h₄₄ : ∀ (n : ℕ), (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
                intro n
                -- Use the fact that the arithmetic function convolution expands to a sum over factorizations
                -- and the tuple sum with constraints matches this expansion exactly
                have h₄₅ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
                  -- Prove the core identity by expanding the Dirichlet convolution
                  have h₄₆ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
                    classical
                    -- The arithmetic function log * ζ^(j-1) * muTrunc(X)^j expands to a sum over 2j-tuples
                    -- which exactly matches the 20-tuple sum with constraints
                    -- This is a known combinatorial identity from Heath-Brown's identity
                    have h₄₇ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) := by
                      -- Prove by case analysis on j (since j ∈ [1, 10])
                      have h_j_cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by
                        have h₁ : j ∈ Finset.Icc 1 10 := hj
                        have h₂ : 1 ≤ j ∧ j ≤ 10 := Finset.mem_Icc.mp h₁
                        interval_cases j <;> norm_num at h₂ ⊢ <;> (try omega) <;> (try aesop)
                      rcases h_j_cases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
                      <;> simp_all [Fin.sum_univ_succ, Finset.prod_const, Finset.sum_const, Finset.card_range]
                      <;> norm_num [ArithmeticFunction.mul_apply, ArithmeticFunction.pow_apply, muTrunc, aj, usedPos_dy, Finset.filter_filter, Finset.filter_eq'] at *
                      <;> try contradiction
                      <;> try aesop
                      <;> try
                        {
                          classical
                          -- For each case, the identity holds by definition of Dirichlet convolution
                          -- and the fact that the 20-tuple sum matches the convolution expansion
                          simp_all [Finset.sum_filter, Finset.filter_eq', Fintype.piFinset, Finset.prod_const]
                          <;> norm_num
                          <;> aesop
                        }
                      <;> try
                        {
                          -- Use the fact that the convolution expansion matches the tuple sum
                          simp_all [ArithmeticFunction.mul_apply, Finset.sum_const, Finset.card_range]
                          <;> norm_num
                          <;> aesop
                        }
                    rw [h₄₇]
                  exact h₄₆
                exact h₄₅
              exact h₄₄ n
            rw [h₄₃]
          rw [h₄₂]
        rw [h₄₁]
      have h₅ : ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n = ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) * χ n := by
        apply Finset.sum_congr rfl
        intro n hn
        have h₅₁ : (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) := by
          have h₅₂ := h₄ n
          exact h₅₂
        rw [h₅₁]
        <;> simp [mul_assoc]
      have h₆ : ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) * χ n = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) := by
        have h₆₁ : ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) * χ n = ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ((∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ n) := by
          apply Finset.sum_congr rfl
          intro n hn
          have h₆₂ : (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) * χ n = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ((∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ n) := by
            rw [Finset.mul_sum]
            <;> simp [mul_assoc, mul_comm, mul_left_comm]
          rw [h₆₂]
        rw [h₆₁]
        have h₆₃ : ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ((∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ n) = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) := by
          classical
          -- Define the sets
          let S : Finset ℕ := (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n)
          let T (n : ℕ) : Finset (Fin 20 → ℕ) := (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
          let T' : Finset (Fin 20 → ℕ) := (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)))
          -- The LHS is sum over n in S of sum over t in T n of f(t) * χ(n)
          -- We can rewrite this as sum over pairs (n, t) in the sigma type
          have h₆₄ : ∑ n in S, ∑ t in T n, ((∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ n) = ∑ p in (S.sigma fun n => T n), ((∏ k : Fin 20, (aj (k.val + 1) (p.2 k) : ℂ)) * χ p.1) := by
            calc
              ∑ n in S, ∑ t in T n, ((∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ n) = ∑ n in S, ∑ t in T n, ((∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ n) := rfl
              _ = ∑ p in (S.sigma fun n => T n), ((∏ k : Fin 20, (aj (k.val + 1) (p.2 k) : ℂ)) * χ p.1) := by
                rw [Finset.sum_sigma']
                <;> simp [Prod.fst, Prod.snd]
                <;> aesop
          rw [h₆₄]
          -- Now we need to show that the sigma type is in bijection with T'
          have h₆₅ : ∑ p in (S.sigma fun n => T n), ((∏ k : Fin 20, (aj (k.val + 1) (p.2 k) : ℂ)) * χ p.1) = ∑ t in T', (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) := by
            -- Use the bijection between the sigma type and T'
            have h₆₆ : ∀ (p : ℕ × (Fin 20 → ℕ)), p ∈ (S.sigma fun n => T n) → (p.2 : Fin 20 → ℕ) ∈ T' := by
              intro p hp
              simp only [S, T, T', Finset.mem_sigma, Finset.mem_filter, Finset.mem_piFinset, Finset.mem_Icc, Set.mem_setOf_eq] at hp ⊢
              -- Extract the conditions from hp
              have h₁ : p.1 ∈ Finset.Icc 1 ⌊u⌋₊ := by exact Finset.mem_filter.mp (hp.1).1
              have h₂ : (N : ℝ) - A < p.1 := by exact (Finset.mem_filter.mp (hp.1).2).2
              have h₃ : p.2 ∈ Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 p.1 := by exact (hp.2.1).1
              have h₄ : ∏ k, (p.2 k : ℕ) = p.1 := by exact (Finset.mem_filter.mp (hp.2.2)).1
              have h₅ : (∀ k, ¬ usedPos_dy j k → p.2 k = 1) := by exact (Finset.mem_filter.mp (hp.2.2)).2.1
              have h₆ : (∀ k : Fin 20, 10 ≤ k.val → (p.2 k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) := by exact (Finset.mem_filter.mp (hp.2.2)).2.2
              -- Prove the conditions for T'
              have h₇ : p.2 ∈ Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N := by
                -- Each component is between 1 and p.1, and p.1 ≤ ⌊u⌋₊ ≤ u ≤ N
                have h₇₁ : ∀ k : Fin 20, p.2 k ∈ Finset.Icc 1 p.1 := by
                  intro k
                  exact (Fintype.mem_piFinset.mp h₃) k
                have h₇₂ : ∀ k : Fin 20, 1 ≤ p.2 k ∧ p.2 k ≤ p.1 := by
                  intro k
                  exact Finset.mem_Icc.mp (h₇₁ k)
                have h₇₃ : p.1 ≤ ⌊u⌋₊ := by
                  exact (Finset.mem_Icc.mp h₁).2
                have h₇₄ : (⌊u⌋₊ : ℝ) ≤ u := by exact Nat.le_ceil u
                have h₇₅ : (p.1 : ℝ) ≤ u := by
                  have h₇₅₁ : (p.1 : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast h₇₃
                  linarith
                have h₇₆ : u ≤ N := by exact_mod_cast hu
                have h₇₇ : ∀ k : Fin 20, 1 ≤ p.2 k ∧ p.2 k ≤ N := by
                  intro k
                  have h₇₇₁ : 1 ≤ p.2 k ∧ p.2 k ≤ p.1 := h₇₂ k
                  have h₇₇₂ : (p.2 k : ℕ) ≤ p.1 := h₇₇₁.2
                  have h₇₇₃ : (p.1 : ℕ) ≤ N := by
                    have h₇₇₄ : (p.1 : ℝ) ≤ N := by linarith
                    exact_mod_cast h₇₇₄
                  exact ⟨h₇₇₁.1, by linarith⟩
                have h₇₈ : ∀ k : Fin 20, p.2 k ∈ Finset.Icc 1 N := by
                  intro k
                  exact Finset.mem_Icc.mpr (h₇₇ k)
                exact Fintype.mem_piFinset.mpr h₇₈
              have h₈ : (N : ℝ) - A < ∏ k, (p.2 k : ℝ) := by
                have h₈₁ : (∏ k, (p.2 k : ℝ) : ℝ) = (p.1 : ℝ) := by
                  norm_cast at h₄ ⊢
                  <;> simp_all [Finset.prod_const]
                  <;> ring_nf at * <;> norm_cast at * <;> simp_all
                rw [h₈₁]
                exact_mod_cast h₂
              have h₉ : ∏ k, (p.2 k : ℝ) ≤ u := by
                have h₉₁ : (∏ k, (p.2 k : ℝ) : ℝ) = (p.1 : ℝ) := by
                  norm_cast at h₄ ⊢
                  <;> simp_all [Finset.prod_const]
                  <;> ring_nf at * <;> norm_cast at * <;> simp_all
                rw [h₉₁]
                have h₉₂ : (p.1 : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp h₁).2
                have h₉₃ : (⌊u⌋₊ : ℝ) ≤ u := by exact Nat.le_ceil u
                linarith
              have h₁₀ : (∀ k, ¬ usedPos_dy j k → p.2 k = 1) := h₅
              have h₁₁ : (∀ k : Fin 20, 10 ≤ k.val → (p.2 k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) := h₆
              exact ⟨h₇, h₈, h₉, h₁₀, h₁₁⟩

            have h₆₇ : ∀ (t : Fin 20 → ℕ), t ∈ T' → (∏ k, t k, t) ∈ (S.sigma fun n => T n) := by
              intro t ht
              simp only [S, T, T', Finset.mem_sigma, Finset.mem_filter, Finset.mem_piFinset, Finset.mem_Icc, Set.mem_setOf_eq] at ht ⊢
              have h₁ : t ∈ Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N := ht.1
              have h₂ : (N : ℝ) - A < ∏ k, (t k : ℝ) := ht.2.1
              have h₃ : ∏ k, (t k : ℝ) ≤ u := ht.2.2.1
              have h₄ : (∀ k, ¬ usedPos_dy j k → t k = 1) := ht.2.2.2.1
              have h₅ : (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) := ht.2.2.2.2
              have h₆ : ∏ k, (t k : ℕ) ∈ Finset.Icc 1 ⌊u⌋₊ := by
                have h₆₁ : 1 ≤ ∏ k, (t k : ℕ) := by
                  have h₆₂ : ∀ k : Fin 20, 1 ≤ t k := by
                    intro k
                    have h₆₃ : t k ∈ Finset.Icc 1 N := (Fintype.mem_piFinset.mp h₁) k
                    exact (Finset.mem_Icc.mp h₆₃).1
                  have h₆₃ : 1 ≤ ∏ k, (t k : ℕ) := by
                    calc 1 ≤ ∏ k : Fin 20, 1 := by simp
                      _ ≤ ∏ k, (t k : ℕ) := Finset.prod_le_prod (fun k _ => by linarith [h₆₂ k]) (fun k _ => by linarith [h₆₂ k])
                  exact h₆₃
                have h₆₂ : ∏ k, (t k : ℕ) ≤ ⌊u⌋₊ := by
                  have h₆₃ : (∏ k, (t k : ℕ) : ℝ) ≤ u := by
                    have h₆₄ : (∏ k, (t k : ℝ) : ℝ) ≤ u := by exact_mod_cast h₃
                    have h₆₅ : (∏ k, (t k : ℕ) : ℝ) = (∏ k, (t k : ℝ) : ℝ) := by norm_cast
                    rw [h₆₅] at *
                    exact_mod_cast h₆₄
                  have h₆₄ : (∏ k, (t k : ℕ) : ℝ) ≤ u := h₆₃
                  have h₆₅ : (∏ k, (t k : ℕ) : ℝ) ≤ ⌊u⌋₊ := by
                    have h₆₆ : (⌊u⌋₊ : ℝ) ≥ u - 1 := by
                      linarith [Nat.ceil_lt_add_one u]
                    have h₆₇ : (∏ k, (t k : ℕ) : ℝ) ≤ u := h₆₄
                    have h₆₈ : (∏ k, (t k : ℕ) : ℕ) ≤ ⌊u⌋₊ := by
                      by_contra h
                      have h₆₉ : ⌊u⌋₊ < ∏ k, (t k : ℕ) := by omega
                      have h₆₁₀ : (⌊u⌋₊ : ℝ) < (∏ k, (t k : ℕ) : ℝ) := by exact_mod_cast h₆₉
                      have h₆₁₁ : (∏ k, (t k : ℕ) : ℝ) ≤ u := h₆₄
                      have h₆₁₂ : (⌊u⌋₊ : ℝ) < u := by linarith
                      have h₆₁₃ : (⌊u⌋₊ : ℝ) ≥ u - 1 := by linarith [Nat.ceil_lt_add_one u]
                      have h₆₁₄ : (∏ k, (t k : ℕ) : ℝ) > u - 1 := by linarith
                      have h₆₁₅ : (∏ k, (t k : ℕ) : ℕ) > u - 1 := by exact_mod_cast h₆₁₄
                      have h₆₁₆ : (∏ k, (t k : ℕ) : ℕ) ≤ u := by
                        by_contra h'
                        have h₆₁₇ : u < ∏ k, (t k : ℕ) := by omega
                        have h₆₁₈ : (u : ℝ) < (∏ k, (t k : ℕ) : ℝ) := by exact_mod_cast h₆₁₇
                        linarith
                      omega
                    exact_mod_cast h₆₈
                  exact Finset.mem_Icc.mpr ⟨h₆₁, h₆₂⟩
              have h₇ : (N : ℝ) - A < (∏ k, (t k : ℕ) : ℝ) := by exact_mod_cast h₂
              have h₈ : t ∈ Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 (∏ k, t k) := by
                have h₈₁ : ∀ k : Fin 20, t k ∈ Finset.Icc 1 N := (Fintype.mem_piFinset.mp h₁) k
                have h₈₂ : ∀ k : Fin 20, 1 ≤ t k ∧ t k ≤ N := by
                  intro k
                  exact Finset.mem_Icc.mp (h₈₁ k)
                have h₈₃ : ∀ k : Fin 20, t k ≤ ∏ k, t k := by
                  intro k
                  have h₈₄ : 1 ≤ t k := h₈₂ k |>.1
                  have h₈₅ : t k ≤ ∏ i, t i := by
                    calc t k ≤ ∏ i, t i := by
                      apply Finset.single_le_prod (fun i _ => by linarith [h₈₂ i |>.1]) (Finset.mem_univ k)
                      _ = ∏ i, t i := by rfl
                    _ = ∏ i, t i := by rfl
                  exact h₈₅
                have h₈₆ : ∀ k : Fin 20, t k ∈ Finset.Icc 1 (∏ k, t k) := by
                  intro k
                  have h₈₇ : 1 ≤ t k := h₈₂ k |>.1
                  have h₈₈ : t k ≤ ∏ k, t k := h₈₃ k
                  exact Finset.mem_Icc.mpr ⟨h₈₇, h₈₈⟩
                exact Fintype.mem_piFinset.mpr h₈₆
              have h₉ : ∏ k, (t k : ℕ) = ∏ k, t k := by simp
              have h₁₀ : (∀ k, ¬ usedPos_dy j k → t k = 1) := h₄
              have h₁₁ : (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) := h₅
              exact ⟨h₆, h₇, h₈, by simp_all [h₉], h₁₀, h₁₁⟩

            have h₆₈ : ∀ (p : ℕ × (Fin 20 → ℕ)), p ∈ (S.sigma fun n => T n) → (∏ k, p.2 k = p.1) := by
              intro p hp
              simp only [S, T, Finset.mem_sigma, Finset.mem_filter, Finset.mem_piFinset, Finset.mem_Icc, Set.mem_setOf_eq] at hp
              have h₁ : ∏ k, (p.2 k : ℕ) = p.1 := by exact (Finset.mem_filter.mp (hp.2.2)).1
              simp_all [Finset.prod_const]
              <;> norm_cast at * <;> simp_all

            -- Use Finset.sum_bij to establish the equality
            have h₆₉ : ∑ p in (S.sigma fun n => T n), ((∏ k : Fin 20, (aj (k.val + 1) (p.2 k) : ℂ)) * χ p.1) = ∑ t in T', (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) := by
              have h₆₁₀ : ∑ p in (S.sigma fun n => T n), ((∏ k : Fin 20, (aj (k.val + 1) (p.2 k) : ℂ)) * χ p.1) = ∑ t in T', (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) := by
                apply Finset.sum_bij' (fun (p : ℕ × (Fin 20 → ℕ)) _ => p.2) (fun (t : Fin 20 → ℕ) _ => (∏ k, t k, t))
                <;> simp_all [h₆₆, h₆₇, h₆₈]
                <;> aesop
              rw [h₆₁₀]
            rw [h₆₉]
          rw [h₆₅]
          <;> simp_all [S, T, T']
          <;> aesop
        rw [h₆₃]
      have h₇ : ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k) := by
        have h₇₁ : ∀ (t : Fin 20 → ℕ), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) = ∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k) := by
          intro t
          have h₇₂ : χ (∏ k : Fin 20, t k) = ∏ k : Fin 20, χ (t k) := by
            -- Dirichlet characters are completely multiplicative
            have h₇₃ : χ (∏ k : Fin 20, t k) = ∏ k : Fin 20, χ (t k) := by
              rw [show (∏ k : Fin 20, t k : ℕ) = ∏ k : Fin 20, t k by rfl]
              -- Use the fact that Dirichlet characters are completely multiplicative
              have h₇₄ : ∀ (s : Finset (Fin 20)) (f : Fin 20 → ℕ), χ (∏ k in s, f k) = ∏ k in s, χ (f k) := by
                intro s f
                induction' s using Finset.induction_on with k s hk ih
                · simp [DirichletCharacter.one_apply]
                · rw [Finset.prod_insert hk, DirichletCharacter.mul_apply]
                  rw [ih]
                  <;> ring
              have h₇₅ : χ (∏ k : Fin 20, t k) = ∏ k : Fin 20, χ (t k) := by
                have h₇₆ : χ (∏ k in (Finset.univ : Finset (Fin 20)), t k) = ∏ k in (Finset.univ : Finset (Fin 20)), χ (t k) := h₇₄ (Finset.univ : Finset (Fin 20)) t
                simpa [Finset.prod_const] using h₇₆
              exact h₇₅
            exact h₇₃
          calc
            (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) = (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * (∏ k : Fin 20, χ (t k)) := by rw [h₇₂]
            _ = ∏ k : Fin 20, ((aj (k.val + 1) (t k) : ℂ) * χ (t k)) := by
              rw [Finset.prod_mul_distrib]
              <;> simp [mul_assoc, mul_comm, mul_left_comm]
            _ = ∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k) := by rfl
        calc
          ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [h₇₁ t]
          _ = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k) := by rfl
      have h₈ : ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k) = ∑ n in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun n => (N : ℝ) - A < ∏ k, (n k : ℝ) ∧ ∏ k, (n k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → n k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (n k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, aj (k.val + 1) (n k) * χ (n k) := by
        -- This is just a variable rename from t to n
        apply Finset.sum_bij' (fun (t : Fin 20 → ℕ) _ => t) (fun (n : Fin 20 → ℕ) _ => n)
        <;> simp_all [Finset.mem_filter, Finset.mem_piFinset]
        <;> aesop
      calc
        ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) * muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n = ∑ n in (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 n).filter (fun t => ∏ k, (t k : ℕ) = n ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ))) * χ n := by rw [h₅]
        _ = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), (∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ)) * χ (∏ k, t k) := by rw [h₆]
        _ = ∑ t in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun t => (N : ℝ) - A < ∏ k, (t k : ℝ) ∧ ∏ k, (t k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → t k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (t k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, (aj (k.val + 1) (t k) : ℂ) * χ (t k) := by rw [h₇]
        _ = ∑ n in (Fintype.piFinset fun _ : Fin 20 => Finset.Icc 1 N).filter (fun n => (N : ℝ) - A < ∏ k, (n k : ℝ) ∧ ∏ k, (n k : ℝ) ≤ u ∧ (∀ k, ¬ usedPos_dy j k → n k = 1) ∧ (∀ k : Fin 20, 10 ≤ k.val → (n k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))), ∏ k : Fin 20, aj (k.val + 1) (n k) * χ (n k) := by rw [h₈]
    rw [h₃]
  rw [h_main]

/-- LEAF: page 264 top, the dyadic partition: each tuple of `Tsum_dy` lies in exactly one box
`Π (N_k, 2N_k]` of the grid, and boxes failing `Cond35` carry no tuple with
`N - A < Π n_k ≤ u` when `N - A ≤ u ≤ N`, `A ≤ N^{2/3}`, `N ≥ N₀`. Class MEDIUM. -/
theorem tuple_dyadic_leaf : ∃ N₀ : ℝ, ∀ (N : ℕ) (A : ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → ∀ j ∈ Finset.Icc 1 10,
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ), (N : ℝ) - A ≤ u → u ≤ N →
      Tsum_dy j χ N A u = ∑ Nv ∈ boxes_dy N j, Dsum_dy Nv χ N A u := by
  sorry

/-! ### PROVED: the count of boxes, page 264 top, "the sum of `O(L^20)` sums" -/

theorem grid_card_dy (N j : ℕ) (k : Fin 20) : (grid_dy N j k).card ≤ Nat.log 2 N + 2 := by
  classical
  unfold grid_dy
  split_ifs
  · exact (Finset.card_image_le).trans (by simp)
  · exact (Finset.card_image_le).trans (by simp)
  · simp

theorem natlog_le_dy (N : ℕ) (hN : 3 ≤ N) : ((Nat.log 2 N + 2 : ℕ) : ℝ) ≤ 4 * Real.log N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h2 : ((Nat.log 2 N : ℕ) : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]
    · apply Real.log_le_log (by positivity)
      have := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
      exact_mod_cast this
  have h3 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have h4 : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have h0 : (0 : ℝ) ≤ (Nat.log 2 N : ℕ) := by positivity
    nlinarith
  push_cast
  linarith

/-- PROVED: the grid has at most `(Nat.log 2 N + 2)^20 ≤ 4^20 L^20` vectors, page 264 top. -/
theorem boxes_card_leaf : ∃ K N₀ : ℝ, ∀ (N : ℕ), N₀ ≤ N → ∀ j ∈ Finset.Icc 1 10,
    ((boxes_dy N j).card : ℝ) ≤ K * Real.log N ^ (20 : ℝ) := by
  classical
  refine ⟨4 ^ 20, 3, ?_⟩
  intro N hN j _
  have hN3 : 3 ≤ N := by exact_mod_cast hN
  have hc : (boxes_dy N j).card ≤ (Nat.log 2 N + 2) ^ 20 := by
    unfold boxes_dy
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Fintype.card_piFinset]
    calc ∏ k : Fin 20, (grid_dy N j k).card ≤ ∏ _k : Fin 20, (Nat.log 2 N + 2) :=
          Finset.prod_le_prod' (fun k _ => grid_card_dy N j k)
      _ = (Nat.log 2 N + 2) ^ 20 := by simp
  have hcR : ((boxes_dy N j).card : ℝ) ≤ ((Nat.log 2 N + 2 : ℕ) : ℝ) ^ 20 := by
    exact_mod_cast hc
  have hl := natlog_le_dy N hN3
  have hpos : (0 : ℝ) ≤ ((Nat.log 2 N + 2 : ℕ) : ℝ) := by positivity
  rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc ((boxes_dy N j).card : ℝ) ≤ ((Nat.log 2 N + 2 : ℕ) : ℝ) ^ 20 := hcR
    _ ≤ (4 * Real.log N) ^ 20 := pow_le_pow_left₀ hpos hl 20
    _ = 4 ^ 20 * Real.log N ^ 20 := by ring


/-! ### Assembly -/

theorem boxes_cond35_dy (N j : ℕ) : ∀ Nv ∈ boxes_dy N j, Cond35 N Nv := by
  classical
  intro Nv h
  unfold boxes_dy at h
  exact (Finset.mem_filter.mp h).2

/-- PROVED from the two LEAF steps and the proved box count: `DyadicSplit_dy`, page 264 top. -/
theorem dyadicSplit_split_dy : DyadicSplit_dy := by
  obtain ⟨N₁, h1⟩ := tuple_dyadic_leaf
  obtain ⟨K, N₂, h2⟩ := boxes_card_leaf
  refine ⟨K, max (max N₁ N₂) 2, ?_⟩
  intro N A hN hA hA' j hj
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hN3' : 2 ≤ N := by exact_mod_cast hN3
  refine ⟨boxes_dy N j, h2 N hN2 j hj, boxes_cond35_dy N j, ?_⟩
  intro q χ u hu1 hu2
  rw [hb_tuple_leaf N A j hj hN3' q χ u hu2]
  exact h1 N A hN1 hA hA' j hj q χ u hu1 hu2

end

end LeanLab.Zhan1991
