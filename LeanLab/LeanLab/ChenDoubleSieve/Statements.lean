/-
Chen's double sieve, Wu 2004 and Wu 2008.
P0036 J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
Acta Arith. 114 (2004) 215 to 273, arXiv 0705.1652, Theorems 1 to 5.
P0043 J. Wu, same title, 2, Acta Arith. 131 (2008), arXiv 0709.3764, Theorem.
Also Chen 1978, D(N) ≤ 7.8342 Θ(N), as quoted by P0036 eq. 1.4; Chen's paper not read here.
Analytic results are `Prop`s, cited with `sorry` only in the `theorem` lines marked cited.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; these are upper bounds for D(N) and lower bounds for Chen's D_{1,2}.
-/
import Mathlib
import LeanLab.ChenExplicit.Reductions

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section
namespace LeanLab.ChenDoubleSieve

open LeanLab.ChenExplicit (twinC twinC_pos ChenAbove)

/-- `D(N) = |{p ≤ N : Ω(N − p) = 1}|`, the Goldbach representations of `N`. -/
def D (N : ℕ) : ℕ := by
  classical exact #{p ∈ range (N + 1) | p.Prime ∧ Ω (N - p) = 1}

/-- `D_{1,2}(N) = |{p ≤ N : Ω(N − p) ≤ 2}|`, with the paper's `Ω(1) = 0`; Mathlib also has
`Ω 0 = 0`, which only matters at `p = N`, never prime for even `N ≥ 4`. -/
def D12 (N : ℕ) : ℕ := by
  classical exact #{p ∈ range (N + 1) | p.Prime ∧ Ω (N - p) ≤ 2}

/-- `∏_{p ∣ N, p > 2} (p − 1)/(p − 2)`. -/
def oddFactor (N : ℕ) : ℝ := ∏ p ∈ N.primeFactors.filter (2 < ·), (((p : ℝ) - 1) / ((p : ℝ) - 2))

/-- `C_N = ∏_{p ∣ N, p > 2} (p − 1)/(p − 2) · ∏_{p > 2} (1 − 1/(p − 1)²)`. -/
def CN (N : ℕ) : ℝ := oddFactor N * twinC

/-- `Θ(N) = C_N N / (log N)²`. -/
def Θ (N : ℕ) : ℝ := CN N * N / Real.log N ^ 2

/-- `π₂(x) = |{p ≤ x : Ω(p + 2) = 1}|`, twin primes. -/
def π2 (x : ℝ) : ℕ := by
  classical exact #{p ∈ range (⌊x⌋₊ + 1) | p.Prime ∧ Ω (p + 2) = 1}

/-- `π_{1,2}(x) = |{p ≤ x : Ω(p + 2) ≤ 2}|`. -/
def π12 (x : ℝ) : ℕ := by
  classical exact #{p ∈ range (⌊x⌋₊ + 1) | p.Prime ∧ Ω (p + 2) ≤ 2}

/-- `Π(x) = C x / (log x)²` with `C = 2 ∏_{p > 2} (1 − 1/(p − 1)²)`. -/
def PiX (x : ℝ) : ℝ := 2 * twinC * x / Real.log x ^ 2

/-- `D_{1,2}(N, θ) = |{αN ≤ p ≤ αN + N^θ : Ω(N − p) ≤ 2}|`. -/
def D12short (α θ : ℝ) (N : ℕ) : ℕ := by
  classical exact #{p ∈ range (N + 1) | p.Prime ∧ Ω (N - p) ≤ 2 ∧
    α * N ≤ p ∧ (p : ℝ) ≤ α * N + (N : ℝ) ^ θ}

/-- `π_{1,2}(x, θ) = |{x ≤ p ≤ x + x^θ : Ω(p + 2) ≤ 2}|`. -/
def π12short (θ x : ℝ) : ℕ := by
  classical exact #{p ∈ range (⌊x + x ^ θ⌋₊ + 1) | p.Prime ∧ Ω (p + 2) ≤ 2 ∧ x ≤ p}

/-- `Ξ(N, θ) = N^θ/(log N)² · C_N`. -/
def Ξ (N : ℕ) (θ : ℝ) : ℝ := (N : ℝ) ^ θ / Real.log N ^ 2 * CN N

/-- `Π(x, θ) = 2 x^θ/(log x)² · ∏_{p > 2} (1 − 1/(p − 1)²)`. -/
def PiShort (x θ : ℝ) : ℝ := 2 * x ^ θ / Real.log x ^ 2 * twinC

/-! ### The theorems, as `Prop`s -/

/-- An upper bound `D(N) ≤ a Θ(N)` for every sufficiently large even `N`. -/
def GoldbachUpper (a : ℝ) : Prop := ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N → (D N : ℝ) ≤ a * Θ N

/-- A lower bound `D_{1,2}(N) ≥ b Θ(N)` for every sufficiently large even `N`. -/
def ChenLower (b : ℝ) : Prop := ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N → b * Θ N ≤ D12 N

/-- `π₂(x) ≤ a Π(x)` for large `x`. -/
def TwinUpper (a : ℝ) : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → (π2 x : ℝ) ≤ a * PiX x

/-- `π_{1,2}(x) ≥ b Π(x)` for large `x`. -/
def TwinChenLower (b : ℝ) : Prop := ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → b * PiX x ≤ π12 x

/-- Wu 2004 Theorem 5: for `θ ≥ 0.971`, large `N`, `x`: `D_{1,2}(N, θ) ≥ 0.012 Ξ(N, θ)` and
`π_{1,2}(x, θ) ≥ 0.006 Π(x, θ)`. `α ∈ (0, 1)` is fixed first, as in the paper; `N₀` may depend
on `α` and `θ`, the paper writes `N₀(θ)`. `N` even. -/
def Wu2004Thm5 : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ θ : ℝ, (971 / 1000 : ℝ) ≤ θ → θ < 1 →
    (∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N → (12 / 1000 : ℝ) * Ξ N θ ≤ D12short α θ N) ∧
    (∃ x₀ : ℝ, ∀ x, x₀ ≤ x → (6 / 1000 : ℝ) * PiShort x θ ≤ π12short θ x)

/-- P0036 Theorem 1, cited. -/
theorem wu2004_thm1 : GoldbachUpper 7.8209 := by sorry
/-- P0036 Theorem 2, cited. -/
theorem wu2004_thm2 : ChenLower 0.836 := by sorry
/-- P0036 Theorem 3, cited. -/
theorem wu2004_thm3 : TwinUpper 3.3996 := by sorry
/-- P0036 Theorem 4, cited. -/
theorem wu2004_thm4 : TwinChenLower 1.104 := by sorry
/-- P0036 Theorem 5, cited. -/
theorem wu2004_thm5 : Wu2004Thm5 := by sorry
/-- P0043 Theorem, cited. -/
theorem wu2008 : ChenLower 0.899 := by sorry
/-- Chen 1978 as quoted by P0036 eq. 1.4, cited. -/
theorem chen1978_quoted : GoldbachUpper 7.8342 := by sorry

/-! ### Links, zero sorry -/

theorem oddFactor_one_le (N : ℕ) : 1 ≤ oddFactor N := LeanLab.ChenExplicit.one_le_oddFactor N

theorem CN_pos (N : ℕ) : 0 < CN N := by
  unfold CN; have := oddFactor_one_le N; have := twinC_pos; positivity

theorem Θ_nonneg (N : ℕ) : 0 ≤ Θ N := by unfold Θ; have := CN_pos N; positivity

theorem Θ_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Θ N := by
  unfold Θ
  have h1 : (1 : ℝ) < N := by exact_mod_cast hN
  have := CN_pos N
  have := Real.log_pos h1
  positivity

theorem PiX_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ PiX x := by
  unfold PiX; have := twinC_pos; positivity

/-- A larger upper constant is a weaker theorem. -/
theorem goldbachUpper_mono {a a' : ℝ} (h : a ≤ a') (H : GoldbachUpper a) : GoldbachUpper a' := by
  obtain ⟨N₀, hN⟩ := H
  exact ⟨N₀, fun N hN' hle => (hN N hN' hle).trans
    (mul_le_mul_of_nonneg_right h (Θ_nonneg N))⟩

/-- A smaller lower constant is a weaker theorem. -/
theorem chenLower_mono {b b' : ℝ} (h : b' ≤ b) (H : ChenLower b) : ChenLower b' := by
  obtain ⟨N₀, hN⟩ := H
  exact ⟨N₀, fun N hN' hle => (mul_le_mul_of_nonneg_right h (Θ_nonneg N)).trans (hN N hN' hle)⟩

theorem twinUpper_mono {a a' : ℝ} (h : a ≤ a') (H : TwinUpper a) : TwinUpper a' := by
  obtain ⟨x₀, hx⟩ := H
  refine ⟨max x₀ 0, fun x hle => ?_⟩
  have hx0 : 0 ≤ x := (le_max_right _ _).trans hle
  exact (hx x ((le_max_left _ _).trans hle)).trans
    (mul_le_mul_of_nonneg_right h (PiX_nonneg hx0))

theorem twinChenLower_mono {b b' : ℝ} (h : b' ≤ b) (H : TwinChenLower b) : TwinChenLower b' := by
  obtain ⟨x₀, hx⟩ := H
  refine ⟨max x₀ 0, fun x hle => ?_⟩
  have hx0 : 0 ≤ x := (le_max_right _ _).trans hle
  exact (mul_le_mul_of_nonneg_right h (PiX_nonneg hx0)).trans (hx x ((le_max_left _ _).trans hle))

/-- Wu 2004 Theorem 1 improves Chen 1978. -/
theorem chen1978_of_wu (h : GoldbachUpper 7.8209) : GoldbachUpper 7.8342 :=
  goldbachUpper_mono (by norm_num) h

/-- Wu 2008 improves Wu 2004 Theorem 2. -/
theorem wu2004_thm2_of_wu2008 (h : ChenLower 0.899) : ChenLower 0.836 :=
  chenLower_mono (by norm_num) h

/-- The Goldbach count is at most the Chen count. -/
theorem D_le_D12 (N : ℕ) : D N ≤ D12 N := by
  unfold D D12
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, by omega⟩

/-- So an upper bound for `D_{1,2}` would bound `D`; conversely a lower bound for `D` would
bound `D_{1,2}`. In particular binary Goldbach in the Hardy-Littlewood lower form
`D(N) ≥ b Θ(N)` gives `ChenLower b`. -/
theorem chenLower_of_goldbachLower {b : ℝ}
    (h : ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N → b * Θ N ≤ D N) : ChenLower b := by
  obtain ⟨N₀, hN⟩ := h
  exact ⟨N₀, fun N hN' hle => (hN N hN' hle).trans (by exact_mod_cast D_le_D12 N)⟩

/-- **Any positive `ChenLower` constant gives Chen's theorem**: every large even `N` is
`p + m` with `m` a product of at most two primes, `m ≠ 0`. -/
theorem chenAbove_of_chenLower {b : ℝ} (hb : 0 < b) (H : ChenLower b) :
    ∃ T : ℝ, ChenAbove T := by
  obtain ⟨N₀, hN⟩ := H
  refine ⟨max N₀ 3, fun N hE hT => ?_⟩
  have hN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) < N := (le_max_left _ _).trans_lt hT
    exact_mod_cast this.le
  have h3 : 3 < N := by
    have : (3 : ℝ) < N := (le_max_right _ _).trans_lt hT
    exact_mod_cast this
  have h1 := hN N hE hN₀
  have hpos : 0 < D12 N := by
    have : 0 < b * Θ N := mul_pos hb (Θ_pos (by omega))
    exact_mod_cast this.trans_le h1
  unfold D12 at hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨hpN, hpr, hΩ⟩ := hp
  have hne : p ≠ N := by
    rintro rfl
    obtain ⟨k, hk⟩ := hE
    have := hpr.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩
    omega
  exact ⟨p, N - p, hpr, by omega, ⟨by omega, hΩ⟩⟩

/-- Wu 2004 Theorem 2, cited, gives Chen's theorem. -/
theorem chen_of_wu2004 : ∃ T : ℝ, ChenAbove T := chenAbove_of_chenLower (by norm_num) wu2004_thm2

end LeanLab.ChenDoubleSieve
