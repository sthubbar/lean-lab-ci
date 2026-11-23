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
  sorry

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
