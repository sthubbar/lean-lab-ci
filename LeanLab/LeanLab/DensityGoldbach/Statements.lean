/-
Density versions of the Goldbach problems.
P0038 X. Shao 2012, arXiv 1206.6139, A density version of the Vinogradov three primes theorem:
  Theorem 1.1, Theorem 1.3, Proposition 1.4, Corollary 1.5, and the 5/8 sharpness example.
P0046 H. Li, H. Pan 2007, arXiv math/0701240: three sets with lower densities summing past 2,
  quoted as Shao's Theorem 1.2.
P0047 A. Alsetri, X. Shao 2024, arXiv 2405.18576, Density versions of the binary Goldbach
  problem: Theorems 1.1 and 1.2.
AI-written Lean code, Claude, 2026-10-16, run 20261016T2303Z-22954, unit U-0081.
Checked only by the Lean kernel. Cited results are `sorry`. Binary Goldbach is OPEN.
-/
import Mathlib

open Finset Filter
open scoped Classical

noncomputable section
namespace LeanLab.DensityGoldbach

/-- The primes as a set. -/
def P : Set ℕ := {p | p.Prime}

/-- `#(A ∩ P ∩ [1, N]) / #(P ∩ [1, N])`. -/
def relRatio (A : Set ℕ) (N : ℕ) : ℝ :=
  (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime} : ℝ) / #{n ∈ Icc 1 N | n.Prime}

/-- Lower density of `A` relative to the primes, `liminf_N #(A ∩ [1,N]) / #(P ∩ [1,N])`. -/
def lowerDensity (A : Set ℕ) : ℝ := liminf (relRatio A) atTop

/-- Relative lower density of `A` in the reduced residue class `b mod W`. -/
def lowerDensityRes (A : Set ℕ) (b W : ℕ) : ℝ :=
  liminf (fun N : ℕ =>
    (#{n ∈ Icc 1 N | n ∈ A ∧ n.Prime ∧ n % W = b % W} : ℝ) /
      #{n ∈ Icc 1 N | n.Prime ∧ n % W = b % W}) atTop

/-- `n` is a sum of one element from each of `A₁, A₂, A₃`. -/
def IsSum3 (A₁ A₂ A₃ : Set ℕ) (n : ℕ) : Prop := ∃ a ∈ A₁, ∃ b ∈ A₂, ∃ c ∈ A₃, a + b + c = n

/-- Every sufficiently large odd integer is in `A₁ + A₂ + A₃`. -/
def LargeOddIn (A₁ A₂ A₃ : Set ℕ) : Prop := ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → Odd n → IsSum3 A₁ A₂ A₃ n

/-- P0038 Theorem 1.1, Shao: `δ(A) > 5/8` gives every large odd `N` as a sum of three
elements of `A`. -/
def Shao11 : Prop := ∀ A : Set ℕ, A ⊆ P → 5 / 8 < lowerDensity A → LargeOddIn A A A

theorem shao_1_1 : Shao11 := by sorry

/-- P0046 Li-Pan, Shao's Theorem 1.2: three sets with `δ(A₁) + δ(A₂) + δ(A₃) > 2`. -/
def LiPan : Prop := ∀ A₁ A₂ A₃ : Set ℕ, A₁ ⊆ P → A₂ ⊆ P → A₃ ⊆ P →
  2 < lowerDensity A₁ + lowerDensity A₂ + lowerDensity A₃ → LargeOddIn A₁ A₂ A₃

theorem liPan : LiPan := by sorry

/-- P0038 Theorem 1.3, local version: for every `δ > 0` there is `W = W(δ)` such that the
mod 3 density conditions (1) and the mod `W` local condition (2) give large odd `N`. -/
def Shao13 : Prop := ∀ δ : ℝ, 0 < δ → ∃ W : ℕ, 0 < W ∧ ∀ A : Set ℕ, A ⊆ P →
  3 / 2 + δ ≤ 2 * lowerDensityRes A 1 3 + lowerDensityRes A 2 3 →
  3 / 2 + δ ≤ 2 * lowerDensityRes A 2 3 + lowerDensityRes A 1 3 →
  (∀ b, b < W → Nat.Coprime b W → δ ≤ lowerDensityRes A b W) → LargeOddIn A A A

theorem shao_1_3 : Shao13 := by sorry

/-- The reduced residues mod `m`. -/
def unitsMod (m : ℕ) [NeZero m] : Finset (ZMod m) := univ.filter IsUnit

/-- P0038 Proposition 1.4: `m` odd squarefree, `f` from the reduced residues to `[0,1]` with
average above `5/8`; every `x` is `a₁ + a₂ + a₃` with reduced `aᵢ`, `f a₁ f a₂ f a₃ > 0` and
`f a₁ + f a₂ + f a₃ > 3/2`. -/
def Prop14 (m : ℕ) [NeZero m] : Prop := ∀ f : ZMod m → ℝ,
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) → 5 / 8 * (m.totient : ℝ) < ∑ a ∈ unitsMod m, f a →
  ∀ x : ZMod m, ∃ a₁ ∈ unitsMod m, ∃ a₂ ∈ unitsMod m, ∃ a₃ ∈ unitsMod m,
    x = a₁ + a₂ + a₃ ∧ 0 < f a₁ * f a₂ * f a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃

theorem prop_1_4 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) : Prop14 m := by sorry

/-- P0038 Corollary 1.5: `A ⊆ Z_m^*` with `|A| > 5/8 φ(m)` has `A + A + A = Z_m`. -/
def Cor15 (m : ℕ) [NeZero m] : Prop := ∀ A : Finset (ZMod m), A ⊆ unitsMod m →
  5 / 8 * (m.totient : ℝ) < #A → ∀ x : ZMod m, ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b + c = x

/-- P0047 Theorem 1.2, Alsetri-Shao: if every reduced residue class density is at least some
`η > 1/2`, almost all even `N` are `p₁ + p₂` with `p₁, p₂ ∈ A`: the exceptional even
`n ≤ X` are `o(X)`. -/
def AlsetriShao12 : Prop := ∀ A : Set ℕ, A ⊆ P → ∀ η : ℝ, 1 / 2 < η →
  (∀ W b : ℕ, 0 < W → Nat.Coprime b W → η ≤ lowerDensityRes A b W) →
  Tendsto (fun X : ℕ =>
    (#{n ∈ Icc 1 X | Even n ∧ ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = n} : ℝ) / X) atTop (nhds 0)

theorem alsetriShao_1_2 : AlsetriShao12 := by sorry

/-- P0047 Theorem 1.1: for every `ε > 0` some `A ⊆ P` with `δ(A) > 1 - ε` misses a positive
proportion of the even integers in `A + A`. -/
def AlsetriShao11 : Prop := ∀ ε : ℝ, 0 < ε → ∃ A : Set ℕ, A ⊆ P ∧ 1 - ε < lowerDensity A ∧
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
    c * X ≤ (#{n ∈ Icc 1 X | Even n ∧ ¬ ∃ a ∈ A, ∃ b ∈ A, a + b = n} : ℝ)

theorem alsetriShao_1_1 : AlsetriShao11 := by sorry

end LeanLab.DensityGoldbach
