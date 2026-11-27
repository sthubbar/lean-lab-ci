/-
P0068 Zhan 1991, the step H5 of SPLIT_eq31_1122d.lean, page 264 last two displays and page 265
first display, split into three cited LEAF steps. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

The definitions `Psum`, `Vline` and the target `PartialSumLemma1` are copied from
SPLIT_eq31_1122d.lean with the suffix `_ps`, character for character apart from the names.
Falsity check: the statement looks true. `Psum (N - A) = 0` and `Vline (N - A) = 0`, so the
boundary terms of the partial summation vanish at `u = N - A`; the approximation error contributes
`E` at `u = N` and `2π|λ| A E` from the integral; the inner integral has `G = u^{-1/2}` with
`G ≤ (N - A)^{-1/2} ≤ 2 N^{-1/2}`, and `G/F'` with `F' = t/(2πu) + λ` changes monotonicity only at
`u = t/(2πλ)`, so Lemma 1 applies on at most two pieces, and the trivial bound `A (N-A)^{-1/2}`
covers the case `min_u |t + 2πλu| = 0`.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- The partial sum (3.2), page 263: `Σ_{N-A<n≤u} Λ(n) χ(n)`. -/
def Psum_ps {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  Finset.sum ((Finset.Icc 1 ⌊u⌋₊).filter (fun (n : ℕ) => (N : ℝ) - A < n)) (fun n => (Λ n : ℂ) * χ n)

/-- The line integral of (3.4), page 264, on `Re s = σ`, written in `t` with `s = σ + it`:
`(1/2πi) ∫_{σ-iT}^{σ+iT} F(s,χ) (u^s - (N-A)^s) s⁻¹ ds`. -/
def Vline_ps {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A σ T u : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ ((σ : ℂ) + t * Complex.I) *
    (((u : ℂ) ^ ((σ : ℂ) + t * Complex.I) - (((N : ℝ) - A : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I))
      / ((σ : ℂ) + t * Complex.I))


/-- Partial summation and Lemma 1, page 264 last two displays and page 265 first display: if the
partial sums (3.2) agree with a combination of the line integrals on `Re s = 1/2` up to `E` on
`[N-A, N]`, then `Σ Λ(n)χ(n)e(nλ) ≪ N^{-1/2} Σ |c_i| ∫ min(A, N/min_u |t+2πλu|) |F_i| dt
+ (1 + 2π|λ|A) E`. -/
def PartialSumLemma1_ps : Prop :=
  ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (κ : Type) (ι : Finset κ) (Nf : κ → Fin 20 → ℝ) (c : κ → ℂ) (E : ℝ),
    N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    (∀ u : ℝ, (N : ℝ) - A ≤ u → u ≤ N →
      ‖Psum_ps χ N A u - ∑ i ∈ ι, c i * Vline_ps (Nf i) χ N A (1 / 2) T u‖ ≤ E) →
    ‖Schi χ lam N A‖ ≤ K * (N : ℝ) ^ (-(1 / 2) : ℝ) * (∑ i ∈ ι, ‖c i‖ *
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod (Nf i) χ (1 / 2 + t * Complex.I)‖)
      + (1 + 2 * π * |lam| * A) * E


/-! ### The LEAF steps -/

/-- Step S1 and the first half of S2, page 264, the display after "Hence": partial summation of
`Σ Λ(n)χ(n)e(nλ)` against `e(λu)` over `N - A < u ≤ N`, the replacement of `Psum` by the
combination `Σ c_i Vline_i` at cost `E + 2π|λ| A E`, and integration by parts back, using
`Vline_i (N - A) = 0`. -/
def AbelApprox_ps : Prop :=
  ∃ N₀ : ℝ, ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (κ : Type) (ι : Finset κ) (Nf : κ → Fin 20 → ℝ) (c : κ → ℂ) (E : ℝ),
    N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    (∀ u : ℝ, (N : ℝ) - A ≤ u → u ≤ N →
      ‖Psum_ps χ N A u - ∑ i ∈ ι, c i * Vline_ps (Nf i) χ N A (1 / 2) T u‖ ≤ E) →
    ‖Schi χ lam N A - ∑ i ∈ ι, c i * ∫ u in ((N : ℝ) - A)..N,
        deriv (fun v => Vline_ps (Nf i) χ N A (1 / 2) T v) u * ee (lam * u)‖
      ≤ (1 + 2 * π * |lam| * A) * E

/-- Step S2 second half and S3, page 264 the display after "The inner integral above can be
estimated by Lemma 1" and page 265 first display: `∂_u Vline = (1/2π) ∫ F(s) u^{s-1} dt` on
`Re s = 1/2`, Fubini, and Lemma 1 for `∫_{N-A}^N u^{-1/2} e(t log u/2π + λu) du`. -/
def InnerBound_ps : Prop :=
  ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Nv : Fin 20 → ℝ), N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    ‖∫ u in ((N : ℝ) - A)..N, deriv (fun v => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u)‖
      ≤ K * (N : ℝ) ^ (-(1 / 2) : ℝ) *
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖

 /-- Step S1, page 264, the display after "Hence": Abel summation of `Σ_{N-A<n≤N} Λ(n)χ(n)e(nλ)`
against `e(λu)`, `= Psum(N)e(λN) - ∫_{N-A}^N Psum(u) 2πiλ e(λu) du`, using `Psum(N-A) = 0`. -/
def AbelSum_ps : Prop :=
  ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ A → A ≤ N →
    IntervalIntegrable (fun u => Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)))
      MeasureTheory.volume ((N : ℝ) - A) N ∧
    Schi χ lam N A = Psum_ps χ N A N * ee (lam * N)
      - ∫ u in ((N : ℝ) - A)..N, Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u))

/-- Step S2 first half, page 264, the display after "Hence": integration by parts back for the
line integral, `Vline(N)e(λN) - ∫ Vline(u) 2πiλ e(λu) du = ∫ ∂_u Vline(u) e(λu) du`, using
`Vline(N - A) = 0`. -/
def ByParts_ps : Prop :=
  ∃ N₀ : ℝ, ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Nv : Fin 20 → ℝ), N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    IntervalIntegrable (fun u => Vline_ps Nv χ N A (1 / 2) T u *
        (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume ((N : ℝ) - A) N ∧
    Vline_ps Nv χ N A (1 / 2) T N * ee (lam * N)
      - ∫ u in ((N : ℝ) - A)..N, Vline_ps Nv χ N A (1 / 2) T u *
          (2 * π * Complex.I * lam * ee (lam * u))
      = ∫ u in ((N : ℝ) - A)..N,
          deriv (fun v => Vline_ps Nv χ N A (1 / 2) T v) u * ee (lam * u)

/-- LEAF: page 264, the display after "Hence", step S1: Abel summation
`Σ_{N-A<n≤N} Λ(n)χ(n)e(nλ) = Psum(N)e(λN) - ∫_{N-A}^N Psum(u) 2πiλ e(λu) du`. Class EASY. -/
theorem abelSum_leaf_ps : AbelSum_ps := by
  intro N A lam q χ hA1 hAN
  have h₁ : IntervalIntegrable (fun u : ℝ => Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume ((N : ℝ) - A) N := by sorry
  have h₂ : Schi χ lam N A = Psum_ps χ N A N * ee (lam * N) - ∫ u in ((N : ℝ) - A)..N, Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)) := by
    have h₃ : Schi χ lam N A = Finset.sum (Finset.Icc 1 N) (fun n => (if (N : ℝ) - A < (n : ℝ) then (Λ n : ℂ) * χ n * ee (n * lam) else 0)) := by
      have h₃₁ : Schi χ lam N A = Finset.sum (shortWin N A) (fun n => (Λ n : ℂ) * χ n * ee (n * lam)) := rfl
      have h₃₂ : Finset.sum (shortWin N A) (fun n => (Λ n : ℂ) * χ n * ee (n * lam)) = Finset.sum ((Finset.Icc 1 N).filter (fun (n : ℕ) => (N : ℝ) - A < (n : ℝ))) (fun n => (Λ n : ℂ) * χ n * ee (n * lam)) := by
        simp [shortWin]
      have h₃₃ : Finset.sum ((Finset.Icc 1 N).filter (fun (n : ℕ) => (N : ℝ) - A < (n : ℝ))) (fun n => (Λ n : ℂ) * χ n * ee (n * lam)) = Finset.sum (Finset.Icc 1 N) (fun n => (if (N : ℝ) - A < (n : ℝ) then (Λ n : ℂ) * χ n * ee (n * lam) else 0)) := by
        rw [Finset.sum_filter]
        <;> simp [Finset.sum_ite, Finset.filter_eq']
        <;> aesop
      rw [h₃₁, h₃₂, h₃₃]
    have h₄ : Psum_ps χ N A N * ee (lam * N) - ∫ u in ((N : ℝ) - A)..N, Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)) = Finset.sum (Finset.Icc 1 N) (fun n => (if (N : ℝ) - A < (n : ℝ) then (Λ n : ℂ) * χ n * ee (n * lam) else 0)) := by
      have h₄₁ : (N : ℝ) - A ≥ 0 := by
        have h₄₂ : (A : ℝ) ≤ N := by exact_mod_cast hAN
        linarith
      have h₄₂ : (N : ℝ) - A < N := by
        have h₄₃ : (1 : ℝ) ≤ A := by exact_mod_cast hA1
        have h₄₄ : (A : ℝ) ≤ N := by exact_mod_cast hAN
        linarith
      -- Define m = floor(N - A) + 1 directly without set
      have h₄₃ : (⌊((N : ℝ) - A)⌋₊ + 1 : ℕ) ≤ N := by
        have h₄₃₁ : (⌊((N : ℝ) - A)⌋₊ : ℕ) < N := by
          have h₄₃₂ : (⌊((N : ℝ) - A)⌋₊ : ℝ) ≤ (N : ℝ) - A := by
            apply Nat.floor_le
            <;> linarith
          have h₄₃₃ : (N : ℝ) - A < N := by
            have h₄₃₄ : (1 : ℝ) ≤ A := by exact_mod_cast hA1
            have h₄₃₅ : (A : ℝ) ≤ N := by exact_mod_cast hAN
            linarith
          have h₄₃₆ : (⌊((N : ℝ) - A)⌋₊ : ℝ) < N := by linarith
          have h₄₃₇ : (⌊((N : ℝ) - A)⌋₊ : ℕ) < N := by
            norm_cast at h₄₃₆ ⊢
            <;> simp_all [Nat.lt_succ_iff]
            <;> linarith
          omega
        have h₄₃₈ : (⌊((N : ℝ) - A)⌋₊ + 1 : ℕ) ≤ N := by
          have h₄₃₉ : (⌊((N : ℝ) - A)⌋₊ : ℕ) < N := h₄₃₁
          have h₄₄₀ : (⌊((N : ℝ) - A)⌋₊ + 1 : ℕ) ≤ N := by
            omega
          exact h₄₄₀
        exact h₄₃₈
      have h₄₄ : (⌊((N : ℝ) - A)⌋₊ : ℝ) ≤ (N : ℝ) - A := by
        have h₄₄₁ : (⌊((N : ℝ) - A)⌋₊ : ℝ) ≤ (N : ℝ) - A := by
          apply Nat.floor_le
          <;> linarith
        exact h₄₄₁
      have h₄₅ : (N : ℝ) - A < (⌊((N : ℝ) - A)⌋₊ : ℝ) + 1 := by
        have h₄₅₁ : (N : ℝ) - A < (⌊((N : ℝ) - A)⌋₊ : ℝ) + 1 := by
          have h₄₅₂ : (N : ℝ) - A < (⌊((N : ℝ) - A)⌋₊ : ℝ) + 1 := by
            linarith [Nat.floor_le ((N : ℝ) - A) (by linarith), Nat.lt_floor_add_one ((N : ℝ) - A) (by linarith)]
          exact h₄₅₂
        exact h₄₅₁
      -- Psum_ps χ N A N = sum_{n=m}^N a_n
      have h₄₆ : Psum_ps χ N A N = Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) N) (fun n => (Λ n : ℂ) * χ n) := by sorry
      -- The integral splits into [N-A, m] + sum_{k=m}^{N-1} [k, k+1]
      have h₄₇ : ∫ u in ((N : ℝ) - A)..N, Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)) = Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) (N - 1)) (fun k => (Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) k) (fun n => (Λ n : ℂ) * χ n)) * (ee (lam * (k + 1 : ℝ)) - ee (lam * (k : ℝ)))) := by sorry
      -- Telescoping sum
      have h₄₈ : Psum_ps χ N A N * ee (lam * N) - Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) (N - 1)) (fun k => (Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) k) (fun n => (Λ n : ℂ) * χ n)) * (ee (lam * (k + 1 : ℝ)) - ee (lam * (k : ℝ)))) = Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) N) (fun n => (Λ n : ℂ) * χ n * ee (lam * (n : ℝ))) := by sorry
      -- The sum over Finset.Icc m N equals the sum over Finset.Icc 1 N with the if condition
      have h₄₉ : Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) N) (fun n => (Λ n : ℂ) * χ n * ee (lam * (n : ℝ))) = Finset.sum (Finset.Icc 1 N) (fun n => (if (N : ℝ) - A < (n : ℝ) then (Λ n : ℂ) * χ n * ee (n * lam) else 0)) := by sorry
      -- Combine everything
      calc
        Psum_ps χ N A N * ee (lam * N) - ∫ u in ((N : ℝ) - A)..N, Psum_ps χ N A u * (2 * π * Complex.I * lam * ee (lam * u)) = Psum_ps χ N A N * ee (lam * N) - Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) (N - 1)) (fun k => (Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) k) (fun n => (Λ n : ℂ) * χ n)) * (ee (lam * (k + 1 : ℝ)) - ee (lam * (k : ℝ)))) := by rw [h₄₇]
        _ = Finset.sum (Finset.Icc (⌊((N : ℝ) - A)⌋₊ + 1) N) (fun n => (Λ n : ℂ) * χ n * ee (lam * (n : ℝ))) := by rw [h₄₈]
        _ = Finset.sum (Finset.Icc 1 N) (fun n => (if (N : ℝ) - A < (n : ℝ) then (Λ n : ℂ) * χ n * ee (n * lam) else 0)) := by rw [h₄₉]
        _ = Finset.sum (Finset.Icc 1 N) (fun n => (if (N : ℝ) - A < (n : ℝ) then (Λ n : ℂ) * χ n * ee (n * lam) else 0)) := by rfl
    rw [h₃, h₄]
  exact ⟨h₁, h₂⟩

/-- LEAF: page 264, the display after "Hence", step S2 first half: integration by parts for
the line integral `Vline` on `Re s = 1/2`, which is differentiable in `u > 0` and vanishes at
`u = N - A`. Class MEDIUM. -/
theorem byParts_leaf_ps : ByParts_ps := by
  sorry

theorem norm_ee_ps (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp]

theorem combine_ps {κ : Type} (ι : Finset κ) (a b lam E : ℝ) (hab : a ≤ b) (P : ℝ → ℂ) (V : κ → ℝ → ℂ)
    (c : κ → ℂ) (D : κ → ℂ) (S : ℂ)
    (hS : S = P b * ee (lam * b) - ∫ u in a..b, P u * (2 * π * Complex.I * lam * ee (lam * u)))
    (hPi : IntervalIntegrable (fun u => P u * (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume a b)
    (hV : ∀ i ∈ ι, IntervalIntegrable (fun u => V i u * (2 * π * Complex.I * lam * ee (lam * u))) MeasureTheory.volume a b ∧
      V i b * ee (lam * b) - ∫ u in a..b, V i u * (2 * π * Complex.I * lam * ee (lam * u)) = D i)
    (hE : ∀ u, a ≤ u → u ≤ b → ‖P u - ∑ i ∈ ι, c i * V i u‖ ≤ E) :
    ‖S - ∑ i ∈ ι, c i * D i‖ ≤ (1 + 2 * π * |lam| * (b - a)) * E := by
  set w : ℝ → ℂ := fun u => 2 * π * Complex.I * lam * ee (lam * u) with hw
  have hsum : ∑ i ∈ ι, c i * D i = (∑ i ∈ ι, c i * V i b) * ee (lam * b)
      - ∫ u in a..b, (∑ i ∈ ι, c i * V i u) * w u := by
    have hint : ∀ i ∈ ι, IntervalIntegrable (fun u => c i * (V i u * w u)) MeasureTheory.volume a b :=
      fun i hi => (hV i hi).1.const_mul (c i)
    have : (fun u => (∑ i ∈ ι, c i * V i u) * w u) = fun u => ∑ i ∈ ι, c i * (V i u * w u) := by
      funext u; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, intervalIntegral.integral_finsetSum hint, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_const_mul, ← (hV i hi).2]; ring
  have hEn : 0 ≤ E := le_trans (norm_nonneg _) (hE b hab le_rfl)
  have hVi : IntervalIntegrable (fun u => (∑ i ∈ ι, c i * V i u) * w u) MeasureTheory.volume a b := by
    have : (fun u => (∑ i ∈ ι, c i * V i u) * w u) = fun u => ∑ i ∈ ι, c i * (V i u * w u) := by
      funext u; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    have h := IntervalIntegrable.sum ι fun i hi => (hV i hi).1.const_mul (c i)
    convert h using 1
    funext u; simp [Finset.sum_apply, hw]
  have hdiff : S - ∑ i ∈ ι, c i * D i = (P b - ∑ i ∈ ι, c i * V i b) * ee (lam * b)
      - ∫ u in a..b, (P u - ∑ i ∈ ι, c i * V i u) * w u := by
    rw [hS, hsum]
    have : (fun u => (P u - ∑ i ∈ ι, c i * V i u) * w u) = fun u => P u * w u - (∑ i ∈ ι, c i * V i u) * w u := by
      funext u; ring
    rw [this, intervalIntegral.integral_sub hPi hVi]; ring
  have hint : ‖∫ u in a..b, (P u - ∑ i ∈ ι, c i * V i u) * w u‖ ≤ E * (2 * π * |lam|) * |b - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [Set.uIoc_of_le hab] at hu
    rw [norm_mul, hw]
    simp only
    rw [norm_mul, norm_ee_ps, mul_one]
    have : ‖(2 * π * Complex.I * lam : ℂ)‖ = 2 * π * |lam| := by
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    rw [this]
    exact mul_le_mul_of_nonneg_right (hE u hu.1.le hu.2) (by positivity)
  rw [hdiff]
  calc _ ≤ ‖(P b - ∑ i ∈ ι, c i * V i b) * ee (lam * b)‖ + ‖∫ u in a..b, (P u - ∑ i ∈ ι, c i * V i u) * w u‖ :=
        norm_sub_le _ _
    _ ≤ E + E * (2 * π * |lam|) * |b - a| := by
        rw [norm_mul, norm_ee_ps, mul_one]; exact add_le_add (hE b hab le_rfl) hint
    _ = (1 + 2 * π * |lam| * (b - a)) * E := by rw [abs_of_nonneg (show (0:ℝ) ≤ b - a by linarith)]; ring

/-- PROVED from S1 and S2 first half: the approximation step `AbelApprox_ps`. -/
theorem abelApprox_of_parts_ps (hS : AbelSum_ps) (hBP : ByParts_ps) : AbelApprox_ps := by
  obtain ⟨N₁, hBP⟩ := hBP
  refine ⟨max N₁ 1, ?_⟩
  intro N A lam T q χ κ ι Nf c E hN hA1 hA2 hT hE
  have hN1 : (1 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hAN : A ≤ N := by
    refine le_trans hA2 ?_
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  obtain ⟨hPi, hSeq⟩ := hS N A lam q χ hA1 hAN
  have h := combine_ps ι ((N : ℝ) - A) N lam E (by linarith) (Psum_ps χ N A)
    (fun i => Vline_ps (Nf i) χ N A (1 / 2) T) c
    (fun i => ∫ u in ((N : ℝ) - A)..N,
      deriv (fun v => Vline_ps (Nf i) χ N A (1 / 2) T v) u * ee (lam * u))
    (Schi χ lam N A) hSeq hPi
    (fun i _ => hBP N A lam T q χ (Nf i) (le_trans (le_max_left _ _) hN) hA1 hA2 hT) hE
  rwa [show (N : ℝ) - ((N : ℝ) - A) = A by ring] at h

/-- LEAF: page 264, the display after "The inner integral above can be estimated by Lemma 1",
and page 265 first display: differentiation of `Vline` in `u`, Fubini over `t ∈ [-T, T]` and
`u ∈ [N-A, N]`, and Lemma 1 on the at most two pieces where `G/F'` is monotone, giving
`≪ N^{-1/2} wt38`. Class MEDIUM. -/
theorem innerBound_leaf_ps (h1 : Lemma1) : InnerBound_ps := by
  sorry

/-- PROVED from the approximation step and the inner bound: the target `PartialSumLemma1`,
copied as `PartialSumLemma1_ps`. -/
theorem partialSum_of_approx_ps (hA : AbelApprox_ps) (hB : Lemma1 → InnerBound_ps)
    (h1 : Lemma1) : PartialSumLemma1_ps := by
  obtain ⟨N₁, hA⟩ := hA
  obtain ⟨K, N₂, hK, hB⟩ := hB h1
  refine ⟨K, max N₁ N₂, hK, ?_⟩
  intro N A lam T q χ κ ι Nf c E hN hA1 hA2 hT hE
  have hab := hA N A lam T q χ κ ι Nf c E (le_trans (le_max_left _ _) hN) hA1 hA2 hT hE
  have hin := fun i => hB N A lam T q χ (Nf i) (le_trans (le_max_right _ _) hN) hA1 hA2 hT
  set I := fun i => ∫ u in ((N : ℝ) - A)..N,
    deriv (fun v => Vline_ps (Nf i) χ N A (1 / 2) T v) u * ee (lam * u) with hI
  set J := fun i => ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod (Nf i) χ (1 / 2 + t * Complex.I)‖
    with hJ
  have hS : ‖∑ i ∈ ι, c i * I i‖ ≤ ∑ i ∈ ι, ‖c i‖ * (K * (N : ℝ) ^ (-(1 / 2) : ℝ) * J i) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hin i) (norm_nonneg _)
  have htri : ‖Schi χ lam N A‖ ≤ ‖∑ i ∈ ι, c i * I i‖ + (1 + 2 * π * |lam| * A) * E := by
    have := norm_le_insert' (Schi χ lam N A) (∑ i ∈ ι, c i * I i)
    have := norm_sub_rev (Schi χ lam N A) (∑ i ∈ ι, c i * I i)
    have h3 := norm_sub_norm_le (Schi χ lam N A) (∑ i ∈ ι, c i * I i)
    linarith
  calc ‖Schi χ lam N A‖ ≤ ‖∑ i ∈ ι, c i * I i‖ + (1 + 2 * π * |lam| * A) * E := htri
    _ ≤ ∑ i ∈ ι, ‖c i‖ * (K * (N : ℝ) ^ (-(1 / 2) : ℝ) * J i)
          + (1 + 2 * π * |lam| * A) * E := by linarith
    _ = K * (N : ℝ) ^ (-(1 / 2) : ℝ) * (∑ i ∈ ι, ‖c i‖ * J i)
          + (1 + 2 * π * |lam| * A) * E := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

/-- PROVED from the three LEAF Props and Lemma 1: the target `PartialSumLemma1_ps`. -/
theorem partialSum_of_parts_ps (hS : AbelSum_ps) (hBP : ByParts_ps)
    (hB : Lemma1 → InnerBound_ps) (h1 : Lemma1) : PartialSumLemma1_ps :=
  partialSum_of_approx_ps (abelApprox_of_parts_ps hS hBP) hB h1

/-- The target from the LEAF theorems and Lemma 1. -/
theorem partialSum_lemma1_ps (h1 : Lemma1) : PartialSumLemma1_ps :=
  partialSum_of_parts_ps abelSum_leaf_ps byParts_leaf_ps innerBound_leaf_ps h1

#print axioms partialSum_of_parts_ps

end

end LeanLab.Zhan1991