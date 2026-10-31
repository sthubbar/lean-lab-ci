/-
AI-written Lean code, Claude, 2026-10-19, CLOUD 20261019T2314Z-cloud29, unit U-5755, route R-5091.

# Thin Goldbach bases: how few primes can carry every even number

A set `A` is a Goldbach basis up to `2X` when every even `n` in `[4, 2X]` is `a + b` with
`a, b ∈ A`. Counting unordered pairs, `thin_lower`, gives `X - 1 ≤ C(|A| + 1, 2)`, so
`|A| ≥ √(2X) - 1`. Granville showed, assuming the asymptotic form of binary Goldbach, that a
set of primes with `≍ √(x log x)` elements up to `x` suffices; the lab's greedy set cover gives
`1.01 √(X log X)` for `X` from 500 to 20000, Routes/numerics/r5091_cover.out. `basis_50` is a
kernel-checked instance: 15 primes carry every even number up to 100.

Barrier: every known construction of a thin binary basis is probabilistic and needs the Goldbach
count `r(N) ≫ N/log² N` for every large `N`, so the route assumes binary Goldbach in a stronger
form instead of passing the parity barrier. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Routes.R5091
open Finset

/-- `A` carries every even `n` in `[4, 2X]` as a sum of two of its elements. -/
def IsBasisUpTo (A : Finset ℕ) (X : ℕ) : Prop :=
  ∀ n, Even n → 4 ≤ n → n ≤ 2 * X → ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- The counting lower bound: a basis up to `2X` has `X - 1 ≤ C(|A| + 1, 2)`. -/
theorem thin_lower (A : Finset ℕ) (X : ℕ) (h : IsBasisUpTo A X) :
    X - 1 ≤ (A.card + 1).choose 2 := by
  set f : Sym2 ℕ → ℕ := Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ with hf
  have hsub : (Icc 2 X).image (fun m => 2 * m) ⊆ A.sym2.image f := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_Icc] at hn
    obtain ⟨m, ⟨hm2, hmX⟩, rfl⟩ := hn
    obtain ⟨a, ha, b, hb, hab⟩ := h (2 * m) (even_two_mul m) (by omega) (by omega)
    refine Finset.mem_image.mpr ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, ?_⟩
    simp [hf, hab]
  have hinj : Set.InjOn (fun m => 2 * m) (Icc 2 X : Set ℕ) := by
    intro x _ y _ hxy; simp only at hxy; omega
  calc X - 1 = ((Icc 2 X).image (fun m => 2 * m)).card := by
        rw [Finset.card_image_of_injOn hinj, Nat.card_Icc]; omega
    _ ≤ (A.sym2.image f).card := Finset.card_le_card hsub
    _ ≤ A.sym2.card := Finset.card_image_le
    _ = (A.card + 1).choose 2 := Finset.card_sym2 A

/-- The greedy basis for `X = 50`. -/
def A50 : Finset ℕ := {2, 3, 5, 7, 11, 13, 23, 29, 31, 37, 41, 43, 47, 53, 61}

theorem A50_check : (∀ a ∈ A50, a.Prime) ∧
    ∀ n ∈ Finset.range 101, Even n → 4 ≤ n → ∃ a ∈ A50, ∃ b ∈ A50, a + b = n := by
  decide +kernel

/-- 15 primes carry every even number from 4 to 100; `π(100) = 25`. -/
theorem basis_50 : (∀ a ∈ A50, a.Prime) ∧ IsBasisUpTo A50 50 := by
  refine ⟨A50_check.1, fun n he h4 hn => A50_check.2 n (by simp; omega) he h4⟩

/-- The bound is not vacuous at `X = 50`: `49 ≤ C(16, 2) = 120`. -/
theorem lower_50 : 50 - 1 ≤ (A50.card + 1).choose 2 := thin_lower A50 50 basis_50.2

end LeanLab.Routes.R5091
