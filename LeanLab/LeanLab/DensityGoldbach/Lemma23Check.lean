/-
P0038 Shao 2012, Lemma 2.3, the finite computation: a bitmask check run by the Lean kernel,
no native code. Subsets of the eight units mod 15 are bitmasks below 256.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0123.
-/
import Mathlib

namespace LeanLab.DensityGoldbach.L23

/-- The units mod 15 in increasing order, indexed by `0, …, 7`. -/
def u (k : ℕ) : ℕ := [1, 2, 4, 7, 8, 11, 13, 14].getD k 0

/-- `∀ i < n, f i`, as a structural recursion the kernel can run. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allLt n f

lemma allLt_spec (n : ℕ) (f : ℕ → Bool) : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    simp only [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h; exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

/-- `∑ k < n, f k`. -/
def sumLt : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f n + sumLt n f

lemma sumLt_eq (n : ℕ) (f : ℕ → ℕ) : sumLt n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumLt, ih, Finset.sum_range_succ, add_comm]

/-- Number of the eight unit bits set in `i`. -/
def pop (i : ℕ) : ℕ := sumLt 8 fun k => if i.testBit k then 1 else 0

/-- `⋁ k < n, f k` as a bitwise or. -/
def orLt : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f n ||| orLt n f

lemma testBit_orLt (n : ℕ) (f : ℕ → ℕ) (d : ℕ) :
    (orLt n f).testBit d = true ↔ ∃ k < n, (f k).testBit d = true := by
  induction n with
  | zero => simp [orLt]
  | succ n ih =>
    rw [orLt, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨k, Nat.lt_succ_of_lt hk, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inr ⟨k, hk, h⟩
      · exact Or.inl h

/-- The mask of `A + B` for unit bitmasks `i, j`: bit `d` is set iff `d ≡ u k₁ + u k₂`. -/
def sumMask (i j : ℕ) : ℕ :=
  orLt 8 fun k₁ => orLt 8 fun k₂ =>
    if i.testBit k₁ && j.testBit k₂ then 2 ^ ((u k₁ + u k₂) % 15) else 0

/-- For `x mod 15`, the number of units `w` with `x - w ∈ A + B`. -/
def cnt (D x : ℕ) : ℕ := sumLt 8 fun k => if D.testBit ((x + 15 - u k) % 15) then 1 else 0

/-- The check for one first-set mask `i`. -/
def checkI (a b c i : ℕ) : Bool :=
  !(pop i == a) || allLt 256 fun j => !(pop j == b) ||
    (fun D => allLt 15 fun x => decide (9 ≤ c + cnt D x)) (sumMask i j)

/-- The check for one size type `(a, b, c)`. -/
def check (a b c : ℕ) : Bool := allLt 256 (checkI a b c)

/-- The check on the masks `lo, …, lo + n - 1`, so the kernel work can be split. -/
def checkPart (a b c lo n : ℕ) : Bool := allLt n fun t => checkI a b c (lo + t)

lemma check_of_parts (a b c : ℕ) (h₀ : checkPart a b c 0 64 = true)
    (h₁ : checkPart a b c 64 64 = true) (h₂ : checkPart a b c 128 64 = true)
    (h₃ : checkPart a b c 192 64 = true) : check a b c = true := by
  rw [checkPart, allLt_spec] at h₀ h₁ h₂ h₃
  rw [check, allLt_spec]
  intro i hi
  by_cases g₀ : i < 64
  · simpa using h₀ i g₀
  by_cases g₁ : i < 128
  · simpa [show 64 + (i - 64) = i by omega] using h₁ (i - 64) (by omega)
  by_cases g₂ : i < 192
  · simpa [show 128 + (i - 128) = i by omega] using h₂ (i - 128) (by omega)
  · simpa [show 192 + (i - 192) = i by omega] using h₃ (i - 192) (by omega)

end LeanLab.DensityGoldbach.L23
