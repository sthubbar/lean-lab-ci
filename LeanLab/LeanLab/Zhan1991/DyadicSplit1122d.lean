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



/-! ### Batch 1: dyad membership and grid unfoldings -/

private lemma dyad_mem (x : ℝ) (n : ℕ) :
    n ∈ dyad x ↔ x < (n : ℝ) ∧ 1 ≤ n ∧ (n : ℝ) ≤ 2 * x := by
  unfold dyad
  rw [Finset.mem_filter, Finset.mem_Icc]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · rw [show (n ≤ ⌊2 * x⌋₊) ↔ (n : ℝ) ≤ 2 * x from Nat.le_floor_iff' (by omega)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩

private lemma dyad_half : dyad (1 / 2) = {1} := by
  ext n
  rw [dyad_mem, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 : (n : ℝ) < 2 := by linarith
    have h5 : n < 2 := by exact_mod_cast h4
    omega
  · rintro rfl
    norm_num

private lemma grid_dy_not_used {N j : ℕ} {k : Fin 20} (h : ¬ usedPos_dy j k) :
    grid_dy N j k = {1 / 2} := by
  unfold grid_dy
  rw [if_neg h]

private lemma grid_dy_used_mu {N j : ℕ} {k : Fin 20} (h : usedPos_dy j k) (h10 : 10 ≤ k.val) :
    grid_dy N j k = (Finset.range (Nat.log 2 N + 2)).image
      (fun m : ℕ => (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ (m + 1)) := by
  unfold grid_dy
  rw [if_pos h, if_pos h10]

private lemma grid_dy_used_log {N j : ℕ} {k : Fin 20} (h : usedPos_dy j k) (h10 : ¬ 10 ≤ k.val) :
    grid_dy N j k = (Finset.range (Nat.log 2 N + 2)).image (fun m : ℕ => (2 : ℝ) ^ m / 2) := by
  unfold grid_dy
  rw [if_pos h, if_neg h10]




open Finset Real

/-- For `1 ≤ x ≤ N` there is a grid index `m ≤ log₂N + 1` with `2^m/2 < x ≤ 2^m`. -/
private lemma log_grid_exists {N x : ℕ} (hx : 1 ≤ x) (hxN : x ≤ N) :
    ∃ m ∈ Finset.range (Nat.log 2 N + 2), (2 : ℝ) ^ m / 2 < (x : ℝ) ∧ (x : ℝ) ≤ (2 : ℝ) ^ m := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hxne : x ≠ 0 := by omega
  have hLx : ((2 : ℝ) ^ Nat.log 2 x) ≤ (x : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hxne
  have hLx' : x < 2 ^ (Nat.log 2 x).succ := Nat.lt_pow_succ_log_self (by norm_num) x
  have hcast : (x : ℝ) < (2 : ℝ) ^ Nat.log 2 x * 2 := by
    have h1 : (x : ℝ) < (2 : ℝ) ^ (Nat.log 2 x).succ := by exact_mod_cast hLx'
    have h2 : ((2 : ℝ) ^ (Nat.log 2 x).succ) = (2 : ℝ) ^ Nat.log 2 x * 2 := by rw [pow_succ]
    rw [h2] at h1
    exact h1
  have hmN : Nat.log 2 x ≤ Nat.log 2 N := Nat.log_mono_right (b := 2) hxN
  by_cases h : (2 : ℝ) ^ Nat.log 2 x = (x : ℝ)
  · refine ⟨Nat.log 2 x, ?_, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · rw [h]; linarith
    · rw [h]
  · refine ⟨Nat.log 2 x + 1, ?_, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · have hlt : (2 : ℝ) ^ Nat.log 2 x < (x : ℝ) := lt_of_le_of_ne hLx h
      have : ((2 : ℝ) ^ (Nat.log 2 x + 1)) / 2 = (2 : ℝ) ^ Nat.log 2 x := by
        rw [pow_succ]; ring
      rw [this]; exact hlt
    · have h2 : ((2 : ℝ) ^ (Nat.log 2 x + 1)) = (2 : ℝ) ^ Nat.log 2 x * 2 := by rw [pow_succ]
      rw [h2]; linarith

/-- Uniqueness of the grid index in the `log`/`ζ` family. -/
private lemma pow2_le {a b : ℕ} (hab : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  pow_le_pow_right₀ (by norm_num) hab

private lemma log_grid_unique {x : ℕ} {m m' : ℕ}
    (h1 : (2 : ℝ) ^ m / 2 < (x : ℝ)) (h2 : (x : ℝ) ≤ (2 : ℝ) ^ m)
    (h3 : (2 : ℝ) ^ m' / 2 < (x : ℝ)) (h4 : (x : ℝ) ≤ (2 : ℝ) ^ m') : m = m' := by
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exfalso
    have hle : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (m' - 1) := pow2_le (by omega)
    have hsplit : (2 : ℝ) ^ m' / 2 = (2 : ℝ) ^ (m' - 1) := by
      conv_lhs => rw [show m' = (m' - 1) + 1 by omega]
      rw [pow_succ]; ring
    rw [hsplit] at h3
    linarith
  · exact heq
  · exfalso
    have hle : (2 : ℝ) ^ m' ≤ (2 : ℝ) ^ (m - 1) := pow2_le (by omega)
    have hsplit : (2 : ℝ) ^ m / 2 = (2 : ℝ) ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]; ring
    rw [hsplit] at h1
    linarith


/-! ### Batch 3: the `μ` family of grid points -/

/-- For `1 ≤ x ≤ X = N^{1/10}` there is a grid index `m ≤ log₂N + 1` with
`X/2^{m+1} < x ≤ X/2^m`. -/
private lemma mu_grid_exists {N x : ℕ} (hN : 1 ≤ N) (hx : 1 ≤ x)
    (hxX : (x : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :
    ∃ m ∈ Finset.range (Nat.log 2 N + 2),
      (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ (m + 1) < (x : ℝ) ∧
        (x : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ m := by
  set X : ℝ := (N : ℝ) ^ (1 / 10 : ℝ) with hXdef
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNrpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hXpos : 0 < X := Real.rpow_pos_of_pos hNrpos _
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 (by norm_num)
  have hXN : X ≤ (N : ℝ) := by
    calc X ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  set K : ℕ := ⌊X / (x : ℝ)⌋₊ with hKdef
  have hXx_nonneg : (0 : ℝ) ≤ X / (x : ℝ) := by positivity
  have hKle : (K : ℝ) ≤ X / (x : ℝ) := Nat.floor_le hXx_nonneg
  have hKlt : X / (x : ℝ) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK1 : 1 ≤ K := by
    rw [Nat.one_le_floor_iff, le_div_iff₀ hxpos]
    linarith
  have hK0 : K ≠ 0 := by omega
  have hKx : (K : ℝ) ≤ X := le_trans hKle (div_le_self hXpos.le (by exact_mod_cast hx))
  have hKN : K ≤ N := by
    have h2 : (K : ℝ) ≤ (N : ℝ) := le_trans hKx hXN
    exact_mod_cast h2
  have hlogKN : Nat.log 2 K ≤ Nat.log 2 N := Nat.log_mono_right hKN
  refine ⟨Nat.log 2 K, ?_, ?_, ?_⟩
  · simp only [Finset.mem_range]; omega
  · have hpow : (K : ℝ) < (2 : ℝ) ^ (Nat.log 2 K + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) K
      exact_mod_cast h
    have hstep : (K : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 K + 1) := by
      have hK1' : K + 1 ≤ 2 ^ (Nat.log 2 K + 1) := by
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) K
        omega
      exact_mod_cast hK1'
    have hlt : X / (x : ℝ) < (2 : ℝ) ^ (Nat.log 2 K + 1) := lt_of_lt_of_le hKlt hstep
    have hmul : X < (2 : ℝ) ^ (Nat.log 2 K + 1) * (x : ℝ) := (div_lt_iff₀ hxpos).mp hlt
    exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
  · have hpow : (2 : ℝ) ^ Nat.log 2 K ≤ (K : ℝ) := by
      have h := Nat.pow_log_le_self 2 hK0
      exact_mod_cast h
    have hle : (2 : ℝ) ^ Nat.log 2 K ≤ X / (x : ℝ) := le_trans hpow hKle
    have hmul : (2 : ℝ) ^ Nat.log 2 K * (x : ℝ) ≤ X := (le_div_iff₀ hxpos).mp hle
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)

/-- Uniqueness of the dyadic exponent: if `2^a ≤ Y < 2^{a+1}` and the same for `b` then `a = b`. -/
private lemma pow2_exp_unique {Y : ℝ} {a b : ℕ}
    (h1 : (2 : ℝ) ^ a ≤ Y) (h2 : Y < (2 : ℝ) ^ (a + 1))
    (h3 : (2 : ℝ) ^ b ≤ Y) (h4 : Y < (2 : ℝ) ^ (b + 1)) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exfalso
    have hle : (2 : ℝ) ^ (a + 1) ≤ (2 : ℝ) ^ b := pow2_le (by omega)
    linarith
  · exact h
  · exfalso
    have hle : (2 : ℝ) ^ (b + 1) ≤ (2 : ℝ) ^ a := pow2_le (by omega)
    linarith

/-- Uniqueness of the grid index in the `μ` family. -/
private lemma mu_grid_unique {X : ℝ} {x : ℕ} (hx : 0 < (x : ℝ)) {m m' : ℕ}
    (h1 : X / 2 ^ (m + 1) < (x : ℝ)) (h2 : (x : ℝ) ≤ X / 2 ^ m)
    (h3 : X / 2 ^ (m' + 1) < (x : ℝ)) (h4 : (x : ℝ) ≤ X / 2 ^ m') : m = m' := by
  have step : ∀ a : ℕ, X / 2 ^ (a + 1) < (x : ℝ) → (x : ℝ) ≤ X / 2 ^ a →
      (2 : ℝ) ^ a ≤ X / x ∧ X / x < (2 : ℝ) ^ (a + 1) := by
    intro a hA hB
    have hpa : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
    have hpb : (0 : ℝ) < (2 : ℝ) ^ (a + 1) := by positivity
    constructor
    · have hmul : (x : ℝ) * (2 : ℝ) ^ a ≤ X := by
        have := (le_div_iff₀ hpa).mp hB
        linarith
      have h2a : (2 : ℝ) ^ a * (x : ℝ) ≤ X := by linarith
      exact (le_div_iff₀ hx).mpr h2a
    · have hmul : X < (x : ℝ) * (2 : ℝ) ^ (a + 1) := by
        have := (div_lt_iff₀ hpb).mp hA
        linarith
      have h2a : X < (2 : ℝ) ^ (a + 1) * (x : ℝ) := by linarith
      exact (div_lt_iff₀ hx).mpr h2a
  exact pow2_exp_unique (step m h1 h2).1 (step m h1 h2).2 (step m' h3 h4).1 (step m' h3 h4).2


/-! ### Batch 4: grid membership helpers and the per-coordinate box point -/

private lemma grid_not_used_val {N j : ℕ} {k : Fin 20} {Nv : ℝ}
    (h : Nv ∈ grid_dy N j k) (hu : ¬ usedPos_dy j k) : Nv = 1 / 2 := by
  rw [grid_dy_not_used hu] at h
  simpa using h

private lemma grid_used_mu_val {N j : ℕ} {k : Fin 20} {Nv : ℝ}
    (h : Nv ∈ grid_dy N j k) (huse : usedPos_dy j k) (h10 : 10 ≤ k.val) :
    ∃ m ∈ Finset.range (Nat.log 2 N + 2), Nv = (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ (m + 1) := by
  rw [grid_dy_used_mu huse h10] at h
  obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
  exact ⟨a, ha, hae.symm⟩

private lemma grid_used_log_val {N j : ℕ} {k : Fin 20} {Nv : ℝ}
    (h : Nv ∈ grid_dy N j k) (huse : usedPos_dy j k) (h10 : ¬ 10 ≤ k.val) :
    ∃ m ∈ Finset.range (Nat.log 2 N + 2), Nv = (2 : ℝ) ^ m / 2 := by
  rw [grid_dy_used_log huse h10] at h
  obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
  exact ⟨a, ha, hae.symm⟩

/-- `N^{2/3} ≤ N/2` for `N ≥ 8`. -/
private lemma rpow_two_thirds_le_half {N : ℕ} (hN : 8 ≤ N) :
    (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) / 2 := by
  have hNr : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have h8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcube : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    norm_num
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    have h : (2 : ℝ) ^ (3 : ℕ) ≤ ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
      rw [hcube]
      norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h
  have hsplit : (N : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hNr]
    norm_num
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hNr.le _
  nlinarith

private lemma two_mul_mu_val (X : ℝ) (m : ℕ) :
    2 * (X / 2 ^ (m + 1)) = X / 2 ^ m := by
  have h : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by rw [pow_succ]
  rw [h]
  field_simp

private lemma two_mul_log_val (m : ℕ) : 2 * ((2 : ℝ) ^ m / 2) = (2 : ℝ) ^ m := by ring

private lemma one_le_two_pow (m : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)

private lemma div_mu_split (X : ℝ) (m : ℕ) :
    X / 2 ^ (m + 1) = X / 2 ^ m / 2 := by
  have h : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m * 2 := by rw [pow_succ]
  rw [h]
  field_simp

/-- The per-coordinate box point. -/
private lemma coord_exists {N j : ℕ} (hN1 : 1 ≤ N) (k : Fin 20) {x : ℕ} (hx1 : 1 ≤ x)
    (hxN : x ≤ N) (hxX : 10 ≤ k.val → (x : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))
    (hxun : ¬ usedPos_dy j k → x = 1) :
    ∃ Nv : ℝ, Nv ∈ grid_dy N j k ∧ x ∈ dyad Nv ∧ (1 / 2 : ℝ) ≤ Nv ∧
      (10 ≤ k.val → Nv ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
        2 * Nv ≤ (N : ℝ) ^ (1 / 10 : ℝ)) := by
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hX1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hN1' (by norm_num)
  have hXpos : (0 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  by_cases huse : usedPos_dy j k
  · by_cases h10 : 10 ≤ k.val
    · obtain ⟨m, hm, hm1, hm2⟩ := mu_grid_exists hN1 hx1 (hxX h10)
      refine ⟨(N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ (m + 1), ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
      · rw [grid_dy_used_mu huse h10]
        exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
      · rw [dyad_mem]
        exact ⟨hm1, hx1, by rw [two_mul_mu_val]; exact hm2⟩
      · rw [div_mu_split]
        have hx2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ m := le_trans (by exact_mod_cast hx1) hm2
        linarith
      · rw [div_mu_split]
        have hx2 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ m := le_trans (by exact_mod_cast hx1) hm2
        have hle : (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ m ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
          div_le_self hXpos.le (one_le_two_pow m)
        linarith
      · rw [two_mul_mu_val]
        exact div_le_self hXpos.le (one_le_two_pow m)
    · obtain ⟨m, hm, hm1, hm2⟩ := log_grid_exists hx1 hxN
      refine ⟨(2 : ℝ) ^ m / 2, ?_, ?_, ?_, fun h => absurd h h10⟩
      · rw [grid_dy_used_log huse h10]
        exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
      · rw [dyad_mem]
        exact ⟨hm1, hx1, by rw [two_mul_log_val]; exact hm2⟩
      · linarith [one_le_two_pow m]
  · have hx1' : x = 1 := hxun huse
    refine ⟨1 / 2, ?_, ?_, le_rfl, fun _ => ⟨by linarith, by linarith⟩⟩
    · rw [grid_dy_not_used huse]; simp
    · rw [hx1', dyad_half]; simp




/-! ### LEAF steps -/

/-- LEAF: page 263, the `j`-th term of Heath-Brown's identity as an ordered convolution:
`(log * ζ^{j-1} * M_X^j)(n) = Σ_{n = n₁⋯n_{2j}} log n₁ · Π μ(m_i) [m_i ≤ X]`, written with
the 20 positions of `aj`, unused positions fixed at `1`, and the variables cut at `N` since
`n ≤ u ≤ N`. Class MEDIUM. -/
private lemma fiber_sum {ι : Type*} (S : Finset ℕ) (T : Finset ι) (g : ι → ℕ)
    (B : ι → ℂ) (ch : ℕ → ℂ) :
    (∑ n ∈ S, ∑ i ∈ T.filter (fun i => g i = n), B i * ch n)
      = ∑ i ∈ T, (if g i ∈ S then B i * ch (g i) else 0) := by
  classical
  rw [Finset.sum_congr rfl (fun n _ =>
    Finset.sum_filter (s := T) (p := fun i => g i = n) (f := fun i => B i * ch n))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hmem : g i ∈ S
  · rw [if_pos hmem]
    have h1 : (if g i = g i then B i * ch (g i) else 0) = B i * ch (g i) := by rw [if_pos rfl]
    rw [← h1]
    refine Finset.sum_eq_single_of_mem (s := S)
      (f := fun b => if g i = b then B i * ch b else 0) (g i) hmem ?_
    intro b _ hne
    rw [if_neg]
    exact fun h => hne h.symm
  · rw [if_neg hmem]
    refine Finset.sum_eq_zero ?_
    intro b hb
    rw [if_neg]
    intro h
    rw [← h] at hb
    exact absurd hb hmem

private lemma sum_piFinset_succ_const {β : Type*} [AddCommMonoid β] (d M : ℕ)
    (h : (Fin (d + 1) → ℕ) → β) :
    (∑ g ∈ Fintype.piFinset (fun _ : Fin (d + 1) => Finset.Icc 1 M), h g)
      = ∑ a ∈ Finset.Icc 1 M,
          ∑ g' ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M), h (Fin.cons a g') := by
  rw [← Finset.sum_product (s := Finset.Icc 1 M)
    (t := Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M))
    (f := fun p : ℕ × (Fin d → ℕ) => h (Fin.cons p.1 p.2))]
  refine Finset.sum_bij (fun g _ => (g 0, Fin.tail g)) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_product]
    exact ⟨(Fintype.mem_piFinset.mp hg) 0,
      Fintype.mem_piFinset.mpr (fun i => (Fintype.mem_piFinset.mp hg) i.succ)⟩
  · intro g1 _ g2 _ heq
    simp only [Prod.mk.injEq] at heq
    rw [← Fin.cons_self_tail g1, ← Fin.cons_self_tail g2, heq.1, heq.2]
  · intro p hp
    obtain ⟨a, g'⟩ := p
    simp only [Finset.mem_product] at hp
    refine ⟨Fin.cons a g', ?_, rfl⟩
    refine Fintype.mem_piFinset.mpr (fun i => ?_)
    induction i using Fin.cases with
    | zero => simpa using hp.1
    | succ j => simpa using Fintype.mem_piFinset.mp hp.2 j
  · intro g _
    exact (congrArg h (Fin.cons_self_tail g)).symm

private lemma prod_apply_tuple_aux (d M : ℕ) (F : Fin d → ArithmeticFunction ℝ) :
    ∀ n ∈ Finset.Icc 1 M,
      (∏ i, F i) n
        = ∑ g ∈ (Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M)).filter
            (fun g => ∏ i, g i = n), ∏ i, F i (g i) := by
  induction d with
  | zero =>
    intro n hn
    have h1 : (∏ i : Fin 0, F i) = (1 : ArithmeticFunction ℝ) := by simp
    rw [h1, ArithmeticFunction.one_apply,
      Fintype.piFinset_of_isEmpty (s := fun _ : Fin 0 => Finset.Icc 1 M), Finset.sum_filter]
    by_cases hc : n = 1 <;> simp [hc, eq_comm]
  | succ d ih =>
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    rw [Fin.prod_univ_succ, ArithmeticFunction.mul_apply, Finset.sum_filter,
      sum_piFinset_succ_const d M
        (fun g => if (∏ i : Fin (d + 1), g i) = n then ∏ i : Fin (d + 1), F i (g i) else 0)]
    have hcons : ∀ (a : ℕ) (g' : Fin d → ℕ),
        (∏ i : Fin (d + 1), (Fin.cons a g' : Fin (d + 1) → ℕ) i) = a * ∏ i, g' i := by
      intro a g'
      rw [Fin.prod_univ_succ (f := fun i : Fin (d + 1) => (Fin.cons a g' : Fin (d + 1) → ℕ) i)]
      simp
    have hconsF : ∀ (a : ℕ) (g' : Fin d → ℕ),
        (∏ i : Fin (d + 1), F i ((Fin.cons a g' : Fin (d + 1) → ℕ) i))
          = F 0 a * ∏ i : Fin d, F i.succ (g' i) := by
      intro a g'
      rw [Fin.prod_univ_succ (f := fun i : Fin (d + 1) =>
        F i ((Fin.cons a g' : Fin (d + 1) → ℕ) i))]
      simp
    simp only [hcons, hconsF]
    have hIH : ∀ x ∈ n.divisorsAntidiagonal,
        ((∏ i : Fin d, F i.succ) : ArithmeticFunction ℝ) x.2
          = ∑ g' ∈ (Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M)).filter
              (fun g' => ∏ i, g' i = x.2), ∏ i : Fin d, F i.succ (g' i) := by
      intro x hx
      obtain ⟨hxa, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hx2 : 1 ≤ x.2 := by
        rcases Nat.eq_zero_or_pos x.2 with h | h
        · rw [h, Nat.mul_zero] at hxa; omega
        · exact h
      have hx2M : x.2 ≤ M := by
        have hx1 : 1 ≤ x.1 := by
          rcases Nat.eq_zero_or_pos x.1 with h | h
          · rw [h, Nat.zero_mul] at hxa; omega
          · exact h
        have : x.2 ≤ x.1 * x.2 := Nat.le_mul_of_pos_left _ hx1
        omega
      exact ih (fun i => F i.succ) x.2 (Finset.mem_Icc.mpr ⟨hx2, hx2M⟩)
    set P := Fintype.piFinset (fun _ : Fin d => Finset.Icc 1 M) with hP
    have hLHS : (∑ x ∈ n.divisorsAntidiagonal, F 0 x.1 * (∏ i : Fin d, F i.succ) x.2)
        = ∑ p ∈ (n.divisorsAntidiagonal ×ˢ P).filter (fun p => ∏ i, p.2 i = p.1.2),
            F 0 p.1.1 * ∏ i : Fin d, F i.succ (p.2 i) := by
      rw [Finset.sum_filter]
      rw [Finset.sum_product (s := n.divisorsAntidiagonal) (t := P)
        (f := fun p : (ℕ × ℕ) × (Fin d → ℕ) =>
          if ∏ i, p.2 i = p.1.2 then F 0 p.1.1 * ∏ i : Fin d, F i.succ (p.2 i) else 0)]
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [hIH x hx, Finset.mul_sum, Finset.sum_filter]
    have hRHS : (∑ a ∈ Finset.Icc 1 M,
          ∑ g' ∈ P, if a * ∏ i, g' i = n then F 0 a * ∏ i : Fin d, F i.succ (g' i) else 0)
        = ∑ q ∈ (Finset.Icc 1 M ×ˢ P).filter (fun q => q.1 * ∏ i, q.2 i = n),
            F 0 q.1 * ∏ i : Fin d, F i.succ (q.2 i) := by
      rw [Finset.sum_filter]
      rw [← Finset.sum_product (s := Finset.Icc 1 M) (t := P)
        (f := fun q : ℕ × (Fin d → ℕ) =>
          if q.1 * ∏ i, q.2 i = n then F 0 q.1 * ∏ i : Fin d, F i.succ (q.2 i) else 0)]
    rw [hLHS, hRHS]
    refine Finset.sum_bij (fun p _ => (p.1.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpp, hpf⟩ := hp
      rw [Finset.mem_product] at hpp
      obtain ⟨hpd, hpg⟩ := hpp
      obtain ⟨hp1, -⟩ := Nat.mem_divisorsAntidiagonal.mp hpd
      have hnpos : 0 < n := by omega
      have hdvd : p.1.1 ∣ n := ⟨p.1.2, hp1.symm⟩
      have hpos : 0 < p.1.1 := Nat.pos_of_dvd_of_pos hdvd hnpos
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.succ_le_of_lt hpos, (Nat.le_of_dvd hnpos hdvd).trans hnM⟩, hpg⟩, ?_⟩
      rw [hpf]; exact hp1
    · intro p1 h1p p2 h2p heq
      obtain ⟨⟨a1, b1⟩, g1⟩ := p1
      obtain ⟨⟨a2, b2⟩, g2⟩ := p2
      simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq] at h1p h2p heq
      obtain ⟨-, hf1⟩ := h1p
      obtain ⟨-, hf2⟩ := h2p
      obtain ⟨h1, h2⟩ := heq
      rw [h2] at hf1
      have hb : b1 = b2 := by rw [← hf1, hf2]
      rw [h1, hb, h2]
    · intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqp, hqf⟩ := hq
      rw [Finset.mem_product] at hqp
      obtain ⟨hqa, hqg⟩ := hqp
      refine ⟨((q.1, ∏ i, q.2 i), q.2), ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, hqg⟩, rfl⟩
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨hqf, by omega⟩
    · intro p _
      rfl

private lemma prod_range_twenty (j : ℕ) (hj1 : 1 ≤ j) (hj10 : j ≤ 10) {X : ℝ}
    (g : ℕ → ArithmeticFunction ℝ)
    (h0 : g 0 = ArithmeticFunction.log)
    (h1 : ∀ m, 1 ≤ m → m ≤ j - 1 → g m = ArithmeticFunction.zeta)
    (h2 : ∀ m, j ≤ m → m ≤ 9 → g m = 1)
    (h3 : ∀ m, 10 ≤ m → m ≤ 9 + j → g m = muTrunc X)
    (h4 : ∀ m, 10 + j ≤ m → g m = 1) :
    ∏ m ∈ Finset.range 20, g m
      = ArithmeticFunction.log * ArithmeticFunction.zeta ^ (j - 1) * muTrunc X ^ j := by
  set U : Finset ℕ := ({0} : Finset ℕ) ∪ (Finset.Icc 1 (j - 1) ∪ Finset.Icc 10 (9 + j)) with hU
  have hsub : U ⊆ Finset.range 20 := by
    intro m hm
    rw [hU] at hm
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, Finset.mem_range] at hm ⊢
    rcases hm with rfl | hm | hm
    · omega
    · omega
    · omega
  have hoff : ∀ m ∈ Finset.range 20, m ∉ U → g m = 1 := by
    intro m hm20 hmU
    rw [hU] at hmU
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at hmU
    push_neg at hmU
    obtain ⟨hm0, hm1, hm2⟩ := hmU
    rcases Nat.lt_or_ge m j with hj | hj
    · exact absurd (hm1 (by omega)) (by omega)
    rcases Nat.lt_or_ge m 10 with h10 | h10
    · exact h2 m hj (by omega)
    · exact h4 m (by omega)
  rw [← Finset.prod_subset hsub hoff]
  have hd1 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 (j - 1) ∪ Finset.Icc 10 (9 + j)) := by
    rw [Finset.disjoint_union_right]
    constructor
    · rw [Finset.disjoint_singleton_left, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_singleton_left, Finset.mem_Icc]; omega
  have hd2 : Disjoint (Finset.Icc 1 (j - 1)) (Finset.Icc 10 (9 + j)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  rw [hU, Finset.prod_union hd1, Finset.prod_union hd2, Finset.prod_singleton, h0]
  have hA : ∏ m ∈ Finset.Icc 1 (j - 1), g m = ArithmeticFunction.zeta ^ (j - 1) := by
    rw [Finset.prod_congr rfl (fun m hm => by
      simp only [Finset.mem_Icc] at hm
      exact h1 m hm.1 hm.2), Finset.prod_const, Nat.card_Icc]
    congr 1 <;> omega
  have hB : ∏ m ∈ Finset.Icc 10 (9 + j), g m = muTrunc X ^ j := by
    rw [Finset.prod_congr rfl (fun m hm => by
      simp only [Finset.mem_Icc] at hm
      exact h3 m hm.1 hm.2), Finset.prod_const, Nat.card_Icc]
    congr 1 <;> omega
  rw [hA, hB, mul_assoc]

set_option maxHeartbeats 4000000 in
theorem hb_tuple_leaf (N : ℕ) (A : ℝ) (j : ℕ) (hj : j ∈ Finset.Icc 1 10) (hN : 2 ≤ N)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) (hu : u ≤ N) :
    HBsum_dy j χ N A u = Tsum_dy j χ N A u := by
  classical
  obtain ⟨hj1, hj10⟩ := Finset.mem_Icc.mp hj
  set X : ℝ := (N : ℝ) ^ (1 / 10 : ℝ) with hX
  set ch : ℕ → ℂ := (fun n => χ n) with hch
  set g : ℕ → ArithmeticFunction ℝ := (fun m =>
    if m = 0 then ArithmeticFunction.log
    else if m ≤ j - 1 then ArithmeticFunction.zeta
    else if 10 ≤ m ∧ m ≤ 9 + j then muTrunc X else 1) with hg
  set F : Fin 20 → ArithmeticFunction ℝ := (fun k => g k.val) with hF
  set P : Finset (Fin 20 → ℕ) := Fintype.piFinset (fun _ : Fin 20 => Finset.Icc 1 N) with hP
  set S : Finset ℕ := (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n) with hS
  set Bf : (Fin 20 → ℕ) → ℂ := (fun gg => ∏ k : Fin 20, ((F k (gg k) : ℝ) : ℂ)) with hBf
  set Wf : (Fin 20 → ℕ) → ℂ := (fun gg => ∏ k : Fin 20, aj (k.val + 1) (gg k) * ch (gg k)) with hWf
  set cd : (Fin 20 → ℕ) → Prop := (fun gg =>
    (N : ℝ) - A < ∏ k, (gg k : ℝ) ∧ ∏ k, (gg k : ℝ) ≤ u ∧
    (∀ k, ¬ usedPos_dy j k → gg k = 1) ∧
    (∀ k : Fin 20, 10 ≤ k.val → (gg k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))) with hcd
  have hFk : ∀ k : Fin 20, F k = g k.val := fun k => by rw [hF]
  have hg0 : g 0 = ArithmeticFunction.log := by rw [hg]; simp
  have hg1 : ∀ m, 1 ≤ m → m ≤ j - 1 → g m = ArithmeticFunction.zeta := by
    intro m h1 h2
    rw [hg]
    have h0 : ¬ (m = 0) := by omega
    simp [h0, h2]
  have hg2 : ∀ m, j ≤ m → m ≤ 9 → g m = 1 := by
    intro m h1 h2
    rw [hg]
    have h0 : ¬ (m = 0) := by omega
    have h3 : ¬ (m ≤ j - 1) := by omega
    have h4 : ¬ (10 ≤ m ∧ m ≤ 9 + j) := by omega
    simp [h0, h3, h4]
  have hg3 : ∀ m, 10 ≤ m → m ≤ 9 + j → g m = muTrunc X := by
    intro m h1 h2
    rw [hg]
    have h0 : ¬ (m = 0) := by omega
    have h3 : ¬ (m ≤ j - 1) := by omega
    simp [h0, h3, h1, h2]
  have hg4 : ∀ m, 10 + j ≤ m → g m = 1 := by
    intro m h1
    rw [hg]
    have h0 : ¬ (m = 0) := by omega
    have h3 : ¬ (m ≤ j - 1) := by omega
    have h4 : ¬ (10 ≤ m ∧ m ≤ 9 + j) := by omega
    simp [h0, h3, h4]
  have hprod : ∏ k : Fin 20, F k
      = ArithmeticFunction.log * ArithmeticFunction.zeta ^ (j - 1) * muTrunc X ^ j := by
    have h1 : ∏ k : Fin 20, F k = ∏ m ∈ Finset.range 20, g m := by
      rw [hF]
      simpa using Fin.prod_univ_eq_prod_range (fun m => g m) 20
    rw [h1]
    exact prod_range_twenty j hj1 hj10 (X := X) g hg0 hg1 hg2 hg3 hg4
  have hcoef : ∀ n ∈ Finset.Icc 1 N,
      (((ArithmeticFunction.log * ArithmeticFunction.zeta ^ (j - 1) * muTrunc X ^ j) n : ℝ) : ℂ)
        = ∑ gg ∈ P.filter (fun gg => ∏ k, gg k = n), Bf gg := by
    intro n hn
    have h := prod_apply_tuple_aux 20 N F n hn
    rw [hprod] at h
    rw [h, hP, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun gg _ => ?_)
    exact Complex.ofReal_prod Finset.univ (fun k => F k (gg k))
  have hfl : ⌊u⌋₊ ≤ N := by
    by_cases h0 : 0 ≤ u
    · have h1 : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le h0
      have h2 : u ≤ (N : ℝ) := hu
      have h3 : ((⌊u⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := le_trans h1 h2
      exact_mod_cast h3
    · push_neg at h0
      rw [Nat.floor_eq_zero.mpr (by linarith)]
      exact Nat.zero_le N
  have hnN : ∀ n ∈ S, n ∈ Finset.Icc 1 N := by
    intro n hn
    rw [hS] at hn
    obtain ⟨hnI, -⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnu⟩ := Finset.mem_Icc.mp hnI
    exact Finset.mem_Icc.mpr ⟨hn1, le_trans hnu hfl⟩
  have hstep1 : HBsum_dy j χ N A u
      = ∑ n ∈ S, (∑ gg ∈ P.filter (fun gg => ∏ k, gg k = n), Bf gg) * ch n := by
    unfold HBsum_dy
    rw [hS, ← hX]
    simp only [hch]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hcoef n (hnN n hn)]
  have hstep23 : (∑ n ∈ S, (∑ gg ∈ P.filter (fun gg => ∏ k, gg k = n), Bf gg) * ch n)
      = ∑ gg ∈ P, (if ∏ k, gg k ∈ S then Bf gg * ch (∏ k, gg k) else 0) := by
    simp only [Finset.sum_mul]
    exact fiber_sum S P (fun gg => ∏ k, gg k) Bf ch
  have hX1 : 1 ≤ X := by
    rw [hX]
    exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hunused : ∀ k : Fin 20, ¬ usedPos_dy j k → F k = 1 := by
    intro k hk
    rw [hFk k]
    have hne0 : k.val ≠ 0 := by
      intro h; exact hk (by unfold usedPos_dy; exact Or.inl h)
    have hn1 : ¬ (1 ≤ k.val ∧ k.val ≤ j - 1) := by
      intro h; exact hk (by unfold usedPos_dy; exact Or.inr (Or.inl h))
    have hn2 : ¬ (10 ≤ k.val ∧ k.val ≤ 9 + j) := by
      intro h; exact hk (by unfold usedPos_dy; exact Or.inr (Or.inr h))
    rcases Nat.lt_or_ge k.val 10 with h10 | h10
    · exact hg2 k.val (by omega) (by omega)
    · exact hg4 k.val (by omega)
  have hmul_ch : ∀ m n : ℕ, ch (m * n) = ch m * ch n := by
    intro m n
    rw [hch]
    dsimp only
    rw [Nat.cast_mul, map_mul]
  have hchi_prod : ∀ (t : Finset (Fin 20)) (gg : Fin 20 → ℕ),
      ch (∏ k ∈ t, gg k) = ∏ k ∈ t, ch (gg k) := by
    intro t
    induction t using Finset.induction with
    | empty =>
      intro gg
      rw [hch]
      dsimp only
      simp
    | insert a s ha ih =>
      intro gg
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih gg]
      exact hmul_ch (gg a) (∏ k ∈ s, gg k)
  have hpt : ∀ gg ∈ P,
      (if ∏ k, gg k ∈ S then Bf gg * ch (∏ k, gg k) else 0)
        = (if cd gg then Wf gg else 0) := by
    intro gg hmem
    have hmem' := Fintype.mem_piFinset.mp hmem
    have hge1 : ∀ k : Fin 20, 1 ≤ gg k := fun k => (Finset.mem_Icc.mp (hmem' k)).1
    have hcast : ((∏ k : Fin 20, gg k : ℕ) : ℝ) = ∏ k : Fin 20, (gg k : ℝ) := by
      push_cast
      ring
    have hge1' : 1 ≤ ∏ k : Fin 20, gg k := Finset.one_le_prod (fun k _ => hge1 k)
    have hcastn : ((∏ k : Fin 20, gg k : ℕ) : ℝ) = ∏ k : Fin 20, (gg k : ℝ) := hcast
    have hcd' : cd gg ↔ ((N : ℝ) - A < ∏ k, (gg k : ℝ) ∧ ∏ k, (gg k : ℝ) ≤ u ∧
              (∀ k, ¬ usedPos_dy j k → gg k = 1) ∧
              (∀ k : Fin 20, 10 ≤ k.val → (gg k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))) :=
      Iff.rfl
    by_cases hc : cd gg
    · obtain ⟨hc1, hc2, hc3, hc4⟩ := hcd'.mp hc
      have hS1 : ∏ k, gg k ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hge1', Nat.le_floor (by rw [hcast]; exact hc2)⟩, by rw [hcast]; exact hc1⟩
      rw [if_pos hS1, if_pos hc]
      have hk0 : ∀ k : Fin 20, k.val = 0 → ((F k (gg k) : ℝ) : ℂ) = aj (k.val + 1) (gg k) := by
        intro k h0
        have h01 : k.val + 1 = 1 := by omega
        have hgk : gg k ≠ 0 := by have := hge1 k; omega
        rw [hFk, hg, h01, h0]
        simp [aj, ArithmeticFunction.log_apply]
      have hkz : ∀ k : Fin 20, 1 ≤ k.val → k.val ≤ j - 1 →
          ((F k (gg k) : ℝ) : ℂ) = aj (k.val + 1) (gg k) := by
        intro k h1 h2
        have hne0 : k.val ≠ 0 := by omega
        have hm1 : k.val + 1 ≠ 1 := by omega
        have hm2 : k.val + 1 ≤ 10 := by omega
        have hgk : gg k ≠ 0 := by have := hge1 k; omega
        rw [hFk, hg]
        have haj1 : aj (k.val + 1) (gg k) = 1 := by
          simp only [aj]
          rw [if_neg hm1, if_pos hm2]
        simp only [hne0, if_false, h2, if_true]
        rw [haj1]
        simp [ArithmeticFunction.zeta_apply, hgk]
      have hkm : ∀ k : Fin 20, 10 ≤ k.val → k.val ≤ 9 + j →
          ((F k (gg k) : ℝ) : ℂ) = aj (k.val + 1) (gg k) := by
        intro k h1 h2
        have hne0 : k.val ≠ 0 := by omega
        have hnm : ¬ (k.val ≤ j - 1) := by intro h; omega
        have hm1 : k.val + 1 ≠ 1 := by omega
        have hm2 : ¬ (k.val + 1 ≤ 10) := by omega
        have hXk : (gg k : ℝ) ≤ X := by
          have := hc4 k h1
          rw [hX]
          exact this
        rw [hFk, hg]
        have hmv : muTrunc X (gg k) = ((μ (gg k) : ℤ) : ℝ) := by
          simp [muTrunc, hXk]
        have hc12 : 10 ≤ k.val ∧ k.val ≤ 9 + j := ⟨h1, h2⟩
        simp only [hne0, if_false, hnm, hc12, true_and, and_true, if_true, hmv]
        simp only [aj]
        rw [if_neg hm1, if_neg hm2]
        rw [Complex.ofReal_intCast]
      have hku : ∀ k : Fin 20, ¬ usedPos_dy j k →
          ((F k (gg k) : ℝ) : ℂ) = aj (k.val + 1) (gg k) := by
        intro k hk
        have hk1 : gg k = 1 := hc3 k hk
        rw [hunused k hk, ArithmeticFunction.one_apply, if_pos hk1]
        have hne0 : k.val ≠ 0 := by
          intro h; exact hk (by unfold usedPos_dy; exact Or.inl h)
        have hne1 : ¬ (1 ≤ k.val ∧ k.val ≤ j - 1) := by
          intro h; exact hk (by unfold usedPos_dy; exact Or.inr (Or.inl h))
        have hne2 : ¬ (10 ≤ k.val ∧ k.val ≤ 9 + j) := by
          intro h; exact hk (by unfold usedPos_dy; exact Or.inr (Or.inr h))
        have hm1 : k.val + 1 ≠ 1 := by omega
        by_cases hb : k.val + 1 ≤ 10
        · have haj1 : aj (k.val + 1) (gg k) = 1 := by
            simp only [aj]
            rw [if_neg hm1, if_pos hb]
          rw [haj1]
          norm_num
        · have hajm : aj (k.val + 1) (gg k) = ((μ (gg k) : ℤ) : ℂ) := by
            simp only [aj]
            rw [if_neg hm1, if_neg hb]
          rw [hajm, hk1]
          norm_num
      have hfac : ∀ k : Fin 20, ((F k (gg k) : ℝ) : ℂ) = aj (k.val + 1) (gg k) := by
        intro k
        by_cases hup : usedPos_dy j k
        · unfold usedPos_dy at hup
          rcases hup with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hk0 k h0
          · exact hkz k h1 h2
          · exact hkm k h1 h2
        · exact hku k hup
      have hBval : Bf gg = ∏ k : Fin 20, aj (k.val + 1) (gg k) := by
        rw [hBf]
        exact Finset.prod_congr rfl (fun k _ => hfac k)
      have hchval : ch (∏ k : Fin 20, gg k) = ∏ k : Fin 20, ch (gg k) := hchi_prod Finset.univ gg
      rw [hBval, hchval, ← Finset.prod_mul_distrib, hWf]
    · rw [if_neg hc]
      by_cases hS1 : ∏ k, gg k ∈ S
      · rw [if_pos hS1]
        rw [hS] at hS1
        obtain ⟨hS1I, hS1b⟩ := Finset.mem_filter.mp hS1
        obtain ⟨-, hS1f⟩ := Finset.mem_Icc.mp hS1I
        have hA : (N : ℝ) - A < ∏ k, (gg k : ℝ) := by rw [← hcast]; exact hS1b
        have hB : ∏ k, (gg k : ℝ) ≤ u := by
          by_cases h0 : 0 ≤ u
          · rw [← hcast]
            exact le_trans (by exact_mod_cast hS1f) (Nat.floor_le h0)
          · push_neg at h0
            have hz : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
            rw [hz] at hS1f
            omega
        have hCD : ¬ (∀ k, ¬ usedPos_dy j k → gg k = 1) ∨
            ¬ (∀ k : Fin 20, 10 ≤ k.val → (gg k : ℝ) ≤ X) := by
          by_contra hcon
          push_neg at hcon
          exact hc (hcd'.mpr ⟨hA, hB, hcon.1, hcon.2⟩)
        have hzero : Bf gg = 0 := by
          rw [hBf]
          rcases hCD with hC | hD
          · push_neg at hC
            obtain ⟨k, hk, hne⟩ := hC
            refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
            rw [hunused k hk, ArithmeticFunction.one_apply, if_neg hne]
            norm_num
          · push_neg at hD
            obtain ⟨k, hk10, hkX⟩ := hD
            refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
            by_cases hup : usedPos_dy j k
            · unfold usedPos_dy at hup
              rcases hup with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exfalso; omega
              · exfalso; omega
              · have hFm : F k = muTrunc X := by
                  rw [hFk]; exact hg3 k.val h1 h2
                have hx0 : ¬ ((gg k : ℝ) ≤ X) := by linarith
                rw [hFm]
                have hmv0 : muTrunc X (gg k) = 0 := by
                  simp [muTrunc, hx0]
                rw [hmv0]
                norm_num
            · rw [hunused k hup, ArithmeticFunction.one_apply]
              have hne1 : gg k ≠ 1 := by
                intro h
                rw [h] at hkX
                push_cast at hkX
                linarith
              rw [if_neg hne1]
              norm_num
        rw [hzero, zero_mul]
      · rw [if_neg hS1]
  have hT2 : Tsum_dy j χ N A u = ∑ gg ∈ P, (if cd gg then Wf gg else 0) := by
    unfold Tsum_dy
    rw [Finset.sum_filter, hP]
    refine Finset.sum_congr rfl (fun gg _ => ?_)
    by_cases h : cd gg
    · rw [if_pos h,
        if_pos (show ((N : ℝ) - A < ∏ k, (gg k : ℝ) ∧ ∏ k, (gg k : ℝ) ≤ u ∧
          (∀ k, ¬ usedPos_dy j k → gg k = 1) ∧
          (∀ k : Fin 20, 10 ≤ k.val → (gg k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))) from h)]
    · rw [if_neg h,
        if_neg (show ¬ ((N : ℝ) - A < ∏ k, (gg k : ℝ) ∧ ∏ k, (gg k : ℝ) ≤ u ∧
          (∀ k, ¬ usedPos_dy j k → gg k = 1) ∧
          (∀ k : Fin 20, 10 ≤ k.val → (gg k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))) from h)]
  rw [hstep1, hstep23]
  exact Eq.trans (Finset.sum_congr rfl hpt) hT2.symm

/-- LEAF: page 264 top, the dyadic partition: each tuple of `Tsum_dy` lies in exactly one box
`Π (N_k, 2N_k]` of the grid, and boxes failing `Cond35` carry no tuple with
`N - A < Π n_k ≤ u` when `N - A ≤ u ≤ N`, `A ≤ N^{2/3}`, `N ≥ N₀`. Class MEDIUM. -/
theorem tuple_dyadic_leaf : ∃ N₀ : ℝ, ∀ (N : ℕ) (A : ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → ∀ j ∈ Finset.Icc 1 10,
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ), (N : ℝ) - A ≤ u → u ≤ N →
      Tsum_dy j χ N A u = ∑ Nv ∈ boxes_dy N j, Dsum_dy Nv χ N A u := by
  classical
  refine ⟨64, ?_⟩
  intro N A hN hA0 hA23 j hj q χ u hu1 hu2
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN1n : 1 ≤ N := by exact_mod_cast hN1
  have hX1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hXpos : (0 : ℝ) < (N : ℝ) ^ (1 / 10 : ℝ) := by linarith
  have hN8r : (8 : ℝ) ≤ (N : ℝ) := by linarith
  have hN8 : 8 ≤ N := by exact_mod_cast hN8r
  have hA2 : A ≤ (N : ℝ) / 2 := le_trans hA23 (rpow_two_thirds_le_half hN8)
  have hNA : (N : ℝ) / 2 ≤ (N : ℝ) - A := by linarith
  set S : Finset (Fin 20 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 20 => Finset.Icc 1 N)).filter (fun x : Fin 20 → ℕ =>
      (N : ℝ) - A < ∏ k, (x k : ℝ) ∧ ∏ k, (x k : ℝ) ≤ u ∧
      (∀ k, ¬ usedPos_dy j k → x k = 1) ∧
      (∀ k : Fin 20, 10 ≤ k.val → (x k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ))) with hSdef
  set Bs : (Fin 20 → ℝ) → Finset (Fin 20 → ℕ) := fun Nv =>
    (Fintype.piFinset (fun k : Fin 20 => dyad (Nv k))).filter (fun x : Fin 20 → ℕ =>
      (N : ℝ) - A < ∏ k, (x k : ℝ) ∧ ∏ k, (x k : ℝ) ≤ u) with hBdef
  have hTsum : Tsum_dy j χ N A u =
      ∑ x ∈ S, ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) := by
    unfold Tsum_dy
    refine Finset.sum_congr ?_ (fun x _ => rfl)
    apply Finset.ext
    intro y
    simp only [hSdef, Finset.mem_filter]
  have hDsum : ∀ Nv : Fin 20 → ℝ, Dsum_dy Nv χ N A u =
      ∑ x ∈ Bs Nv, ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) := by
    intro Nv
    unfold Dsum_dy
    refine Finset.sum_congr ?_ (fun x _ => rfl)
    apply Finset.ext
    intro y
    simp only [hBdef, Finset.mem_filter]
  have keyI : ∀ Nv ∈ boxes_dy N j, ∀ x ∈ Bs Nv, x ∈ S := by
    intro Nv hNvbox x hxB
    rw [boxes_dy] at hNvbox
    obtain ⟨hNvgrid, hCond⟩ := Finset.mem_filter.mp hNvbox
    rw [hBdef] at hxB
    obtain ⟨hxdy, hxQ⟩ := Finset.mem_filter.mp hxB
    obtain ⟨hxQ1, hxQ2⟩ := hxQ
    have hxdy' : ∀ k : Fin 20, x k ∈ dyad (Nv k) := fun k => Fintype.mem_piFinset.mp hxdy k
    have hNvg' : ∀ k : Fin 20, Nv k ∈ grid_dy N j k := fun k => Fintype.mem_piFinset.mp hNvgrid k
    have hx1 : ∀ k, 1 ≤ x k := fun k => ((dyad_mem _ _).mp (hxdy' k)).2.1
    have hxN : ∀ k, x k ≤ N := by
      intro k
      have hge : ∀ i : Fin 20, (1 : ℝ) ≤ (x i : ℝ) := fun i => by exact_mod_cast hx1 i
      have hmem : k ∈ (Finset.univ : Finset (Fin 20)) := Finset.mem_univ k
      have hsplit : (∏ i, (x i : ℝ)) = (x k : ℝ) * ∏ i ∈ Finset.univ.erase k, (x i : ℝ) :=
        (Finset.mul_prod_erase _ _ hmem).symm
      have hone : (1 : ℝ) ≤ ∏ i ∈ Finset.univ.erase k, (x i : ℝ) :=
        Finset.one_le_prod₀ (fun i _ => hge i)
      have hxk0 : (0 : ℝ) ≤ (x k : ℝ) := by positivity
      have hle : (x k : ℝ) ≤ ∏ i, (x i : ℝ) := by rw [hsplit]; nlinarith
      have hle2 : (x k : ℝ) ≤ (N : ℝ) := le_trans hle (le_trans hxQ2 hu2)
      exact_mod_cast hle2
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun k => ?_), ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hx1 k, hxN k⟩
    · refine ⟨hxQ1, hxQ2, fun k hk => ?_, fun k hk10 => ?_⟩
      · have hval : Nv k = 1 / 2 := grid_not_used_val (hNvg' k) hk
        have hmem := hxdy' k
        rw [hval, dyad_half] at hmem
        simpa using hmem
      · by_cases huse : usedPos_dy j k
        · obtain ⟨m, -, hmg⟩ := grid_used_mu_val (hNvg' k) huse hk10
          have hle2 : (x k : ℝ) ≤ 2 * Nv k := ((dyad_mem _ _).mp (hxdy' k)).2.2
          rw [hmg, two_mul_mu_val] at hle2
          exact le_trans hle2 (div_le_self hXpos.le (one_le_two_pow m))
        · have hval : Nv k = 1 / 2 := grid_not_used_val (hNvg' k) huse
          have hmem := hxdy' k
          rw [hval, dyad_half] at hmem
          have hxeq : x k = 1 := by simpa using hmem
          rw [hxeq]
          simpa using hX1
  have keyII : ∀ x ∈ S, ∃ Nv : Fin 20 → ℝ, Nv ∈ boxes_dy N j ∧ x ∈ Bs Nv ∧
      ∀ Nv' : Fin 20 → ℝ, Nv' ∈ boxes_dy N j → x ∈ Bs Nv' → Nv' = Nv := by
    intro x hxS
    rw [hSdef] at hxS
    obtain ⟨hxI, hxP⟩ := Finset.mem_filter.mp hxS
    obtain ⟨hxQ1, hxQ2, hxUn, hxMu⟩ := hxP
    have hxAll : ∀ i : Fin 20, 1 ≤ x i ∧ x i ≤ N := by
      have h := hxI
      simp only [Fintype.mem_piFinset, Finset.mem_Icc] at h
      exact h
    have hx1 : ∀ k, 1 ≤ x k := fun k => (hxAll k).1
    have hxN : ∀ k, x k ≤ N := fun k => (hxAll k).2
    have hcoord : ∀ k : Fin 20, ∃ Nv : ℝ, Nv ∈ grid_dy N j k ∧ x k ∈ dyad Nv ∧
        (1 / 2 : ℝ) ≤ Nv ∧ (10 ≤ k.val → Nv ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
          2 * Nv ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :=
      fun k => coord_exists hN1n k (hx1 k) (hxN k) (hxMu k) (fun h => hxUn k h)
    let Nv : Fin 20 → ℝ := fun k => Classical.choose (hcoord k)
    have hNv : ∀ k : Fin 20, Nv k ∈ grid_dy N j k ∧ x k ∈ dyad (Nv k) ∧
        (1 / 2 : ℝ) ≤ Nv k ∧ (10 ≤ k.val → Nv k ≤ (N : ℝ) ^ (1 / 10 : ℝ) ∧
          2 * Nv k ≤ (N : ℝ) ^ (1 / 10 : ℝ)) :=
      fun k => Classical.choose_spec (hcoord k)
    have hxNv : ∀ k, Nv k < (x k : ℝ) := fun k => ((dyad_mem _ _).mp (hNv k).2.1).1
    have hxle : ∀ k, (x k : ℝ) ≤ 2 * Nv k := fun k => ((dyad_mem _ _).mp (hNv k).2.1).2.2
    have h35a : ∀ i : Fin 20, (1 / 2 : ℝ) ≤ Nv i := fun i => (hNv i).2.2.1
    have h35c : (∏ i, Nv i) ≤ (N : ℝ) := by
      have hle : (∏ i, Nv i) ≤ ∏ i, (x i : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => le_trans (by norm_num : (0:ℝ) ≤ 1/2) (h35a i))
          (fun i _ => (hxNv i).le)
      exact le_trans hle (le_trans hxQ2 hu2)
    have h35b : (N : ℝ) / 2 ^ 21 ≤ ∏ i, Nv i := by
      have hge : ∀ i : Fin 20, (x i : ℝ) / 2 ≤ Nv i := fun i => by linarith [hxle i]
      have h1 : (∏ i, (x i : ℝ) / 2) ≤ ∏ i, Nv i :=
        Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hge i)
      have h2 : (∏ i, (x i : ℝ) / 2) = (∏ i, (x i : ℝ)) / 2 ^ 20 := by
        rw [Finset.prod_div_distrib]
        simp [Finset.prod_const, Fintype.card_fin]
      have hxhalf : (N : ℝ) / 2 ≤ ∏ i, (x i : ℝ) := le_trans hNA hxQ1.le
      calc (N : ℝ) / 2 ^ 21 = ((N : ℝ) / 2) / 2 ^ 20 := by
            rw [div_div, show (2 : ℝ) ^ 21 = 2 * 2 ^ 20 by norm_num [pow_succ]]
        _ ≤ (∏ i, (x i : ℝ)) / 2 ^ 20 := div_le_div_of_nonneg_right hxhalf (by positivity)
        _ = ∏ i, (x i : ℝ) / 2 := h2.symm
        _ ≤ ∏ i, Nv i := h1
    have hCond35 : Cond35 N Nv :=
      ⟨h35a, h35b, h35c, fun i hi => ((hNv i).2.2.2 hi).1⟩
    have hNvbox : Nv ∈ boxes_dy N j := by
      rw [boxes_dy]
      exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun k => (hNv k).1), hCond35⟩
    have hxBs : x ∈ Bs Nv := by
      rw [hBdef]
      exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun k => (hNv k).2.1), hxQ1, hxQ2⟩
    refine ⟨Nv, hNvbox, hxBs, fun Nv' hNv'box hxB' => ?_⟩
    funext k
    rw [hBdef] at hxB'
    obtain ⟨hxdy', -⟩ := Finset.mem_filter.mp hxB'
    have hdy' : x k ∈ dyad (Nv' k) := Fintype.mem_piFinset.mp hxdy' k
    rw [boxes_dy] at hNv'box
    obtain ⟨hNv'grid, -⟩ := Finset.mem_filter.mp hNv'box
    have hg' : Nv' k ∈ grid_dy N j k := Fintype.mem_piFinset.mp hNv'grid k
    by_cases huse : usedPos_dy j k
    · by_cases h10 : 10 ≤ k.val
      · obtain ⟨m, -, hm⟩ := grid_used_mu_val (hNv k).1 huse h10
        obtain ⟨m', -, hm'⟩ := grid_used_mu_val hg' huse h10
        have e1 := ((dyad_mem _ _).mp (hNv k).2.1)
        have e2 := ((dyad_mem _ _).mp hdy')
        have e1l : ((N : ℝ) ^ (1 / 10 : ℝ)) / 2 ^ (m + 1) < (x k : ℝ) := hm ▸ e1.1
        have e1u : (x k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ m := by
          rw [← two_mul_mu_val]; exact hm ▸ e1.2.2
        have e2l : ((N : ℝ) ^ (1 / 10 : ℝ)) / 2 ^ (m' + 1) < (x k : ℝ) := hm' ▸ e2.1
        have e2u : (x k : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) / 2 ^ m' := by
          rw [← two_mul_mu_val]; exact hm' ▸ e2.2.2
        have heq : m = m' := mu_grid_unique (x := x k) (by exact_mod_cast hx1 k) e1l e1u e2l e2u
        rw [hm, hm', heq]
      · obtain ⟨m, -, hm⟩ := grid_used_log_val (hNv k).1 huse h10
        obtain ⟨m', -, hm'⟩ := grid_used_log_val hg' huse h10
        have e1 := ((dyad_mem _ _).mp (hNv k).2.1)
        have e2 := ((dyad_mem _ _).mp hdy')
        have e1l : (2 : ℝ) ^ m / 2 < (x k : ℝ) := hm ▸ e1.1
        have e1u : (x k : ℝ) ≤ (2 : ℝ) ^ m := by
          rw [← two_mul_log_val]; exact hm ▸ e1.2.2
        have e2l : (2 : ℝ) ^ m' / 2 < (x k : ℝ) := hm' ▸ e2.1
        have e2u : (x k : ℝ) ≤ (2 : ℝ) ^ m' := by
          rw [← two_mul_log_val]; exact hm' ▸ e2.2.2
        have heq : m = m' := log_grid_unique e1l e1u e2l e2u
        rw [hm, hm', heq]
    · rw [grid_not_used_val (hNv k).1 huse, grid_not_used_val hg' huse]
  have hstep : (∑ Nv ∈ boxes_dy N j, ∑ x ∈ Bs Nv,
      ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k)) =
      ∑ x ∈ S, ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) := by
    have e1 : ∀ Nv ∈ boxes_dy N j, (∑ x ∈ Bs Nv, ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k))
        = ∑ x ∈ S, (if x ∈ Bs Nv then ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) else 0) := by
      intro Nv hNv
      have hsub : Bs Nv ⊆ S := fun x hx => keyI Nv hNv x hx
      have hsum := Finset.sum_subset (s₁ := Bs Nv) (s₂ := S)
        (f := fun x => if x ∈ Bs Nv then ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) else 0)
        hsub (fun x _ hxnot => by rw [if_neg hxnot])
      rw [← hsum]
      exact Finset.sum_congr rfl (fun x hx => by rw [if_pos hx])
    calc (∑ Nv ∈ boxes_dy N j, ∑ x ∈ Bs Nv,
          ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k))
        = ∑ Nv ∈ boxes_dy N j, ∑ x ∈ S,
            (if x ∈ Bs Nv then ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) else 0) :=
          Finset.sum_congr rfl e1
      _ = ∑ x ∈ S, ∑ Nv ∈ boxes_dy N j,
            (if x ∈ Bs Nv then ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) else 0) :=
          Finset.sum_comm
      _ = ∑ x ∈ S, ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) := by
          refine Finset.sum_congr rfl (fun x hxS => ?_)
          obtain ⟨Nv0, hNv0, hxBs0, huniq⟩ := keyII x hxS
          have hsingle := Finset.sum_eq_single (s := boxes_dy N j)
            (f := fun Nv => if x ∈ Bs Nv then
              ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) else 0)
            Nv0 (fun b hb hne => by
              rw [if_neg]
              intro hxb
              exact hne (huniq b hb hxb)) (fun hnot => absurd hNv0 hnot)
          rw [hsingle, if_pos hxBs0]
  rw [hTsum]
  rw [show (∑ Nv ∈ boxes_dy N j, Dsum_dy Nv χ N A u) =
      ∑ Nv ∈ boxes_dy N j, ∑ x ∈ Bs Nv, ∏ k : Fin 20, aj (k.val + 1) (x k) * χ (x k) from
    Finset.sum_congr rfl (fun Nv _ => hDsum Nv)]
  exact hstep.symm



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
