/-
P0076 J. Teräväinen, "The Goldbach problem for primes that are sums of two squares plus one",
arXiv 1611.08585 (v2, 14 Aug 2017), Mathematika 64 (2018).
Statements of Theorems 1.1, 1.2, 1.3, 1.4 and of Lemmas 3.4, 3.5, with cheap links.
Theorem 1.5, a Bombieri-Vinogradov type bound for semilinear sieve weights, is not encoded:
its sieve weights depend on Iwaniec's construction and do not have a clean short statement.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN; ternary Goldbach is a theorem, Helfgott 2013.
Foundational declarations are kept here to avoid a proof import cycle.
The four main theorems are assembled in Statements.lean from named analytic leaves.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ternary.Statements

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### The sets of primes -/

/-- `p ∈ 𝒫`: `p` is a prime of the form `x² + y² + 1` with integers `x, y`. -/
def InP (p : ℕ) : Prop := p.Prime ∧ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2 + 1

/-- The set `𝒫` of the paper. -/
def PSet : Set ℕ := {p | InP p}

/-- `p ∈ 𝒫*`: `p` is a prime `x² + y² + 1` with `x, y` coprime integers. -/
def InPStar (p : ℕ) : Prop :=
  p.Prime ∧ ∃ x y : ℤ, Int.gcd x y = 1 ∧ (p : ℤ) = x ^ 2 + y ^ 2 + 1

/-- The set `𝒫* = {x² + y² + 1 : x, y coprime} ∩ 𝒫`. -/
def PStar : Set ℕ := {p | InPStar p}

/-- `n = p + q` with `p, q ∈ 𝒫`. -/
def IsPSum2 (n : ℕ) : Prop := ∃ p q : ℕ, InP p ∧ InP q ∧ p + q = n

/-- `n = p + q + r` with `p, q, r ∈ 𝒫`. -/
def IsPSum3 (n : ℕ) : Prop := ∃ p q r : ℕ, InP p ∧ InP q ∧ InP r ∧ p + q + r = n

/-! ### Theorem 1.1 -/

/-- The number of even `n ∈ [1, N]` with `n ≢ 5, 8 (mod 9)` for which `R n` fails. -/
noncomputable def excCount (R : ℕ → Prop) (N : ℕ) : ℕ :=
  #{n ∈ Icc 1 N | Even n ∧ n % 9 ≠ 5 ∧ n % 9 ≠ 8 ∧ ¬ R n}

/-- Almost all even positive `n ≢ 5, 8 (mod 9)` satisfy `R`: the exceptional count is `o(N)`,
written with an explicit `ε`-`N₀` quantifier for the `o`. -/
def AlmostAllAdmissible (R : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (excCount R N : ℝ) ≤ ε * N

/-- Theorem 1.1: almost all even positive integers `n ≢ 5, 8 (mod 9)` are `p + q`
with `p, q ∈ 𝒫`. -/
def Theorem11 : Prop := AlmostAllAdmissible IsPSum2

/- Theorem 1.1 is assembled in Statements.lean. -/

/-! ### Theorem 1.2 -/

/-- Theorem 1.2: all large enough odd positive integers are `p + q + r` with `p, q, r ∈ 𝒫`.
"Large enough" is an explicit existential threshold `N₀`. -/
def Theorem12 : Prop := ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n → IsPSum3 n

/- Theorem 1.2 is assembled in Statements.lean. -/

/-! ### Theorem 1.3 -/

/-- `#(A ∩ [1, N])`. -/
noncomputable def countIn (A : Set ℕ) (N : ℕ) : ℕ := #{n ∈ Icc 1 N | n ∈ A}

/-- `A` has positive upper density with respect to `B`: for some `c > 0`, infinitely often
`#(A ∩ [1,N]) > c · #(B ∩ [1,N])`. For `A ⊆ B` this is `limsup #(A ∩ [1,N]) / #(B ∩ [1,N]) > 0`. -/
def PosUpperDensityIn (A B : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧ c * (countIn B N : ℝ) < countIn A N

/-- `A` contains infinitely many non-trivial three term progressions `a, a + d, a + 2d`, `d > 0`. -/
def InfinitelyMany3AP (A : Set ℕ) : Prop :=
  {t : ℕ × ℕ | 0 < t.2 ∧ t.1 ∈ A ∧ t.1 + t.2 ∈ A ∧ t.1 + 2 * t.2 ∈ A}.Infinite

/-- Theorem 1.3: every subset of `𝒫*` of positive upper density in `𝒫*` contains infinitely
many non-trivial three term arithmetic progressions. -/
def Theorem13 : Prop := ∀ A : Set ℕ, A ⊆ PStar → PosUpperDensityIn A PStar → InfinitelyMany3AP A

/- Theorem 1.3 is assembled in Statements.lean. -/

/-! ### Theorem 1.4 -/

/-- `‖x‖`, the distance to the nearest integer. -/
noncomputable def distInt (x : ℝ) : ℝ := |x - round x|

/-- Theorem 1.4: for `ξ` irrational, `κ ∈ ℝ` and `ε > 0`, there are infinitely many `p ∈ 𝒫`
with `‖ξ p + κ‖ ≤ p ^ (-θ)`, `θ = 1/80 - ε`. -/
def Theorem14 : Prop := ∀ ξ : ℝ, Irrational ξ → ∀ κ ε : ℝ, 0 < ε →
  {p : ℕ | InP p ∧ distInt (ξ * p + κ) ≤ (p : ℝ) ^ (-(1 / 80 - ε))}.Infinite

/- Theorem 1.4 is assembled in Statements.lean. -/

/-! ### Lemmas 3.4 and 3.5 -/

/-- Lemma 3.4 for a given `J`: every integer `n` with `2^(J-1) ∤ n` is `a + b` with
`a ≡ 2^i (mod 2^(i+2))`, `b ≡ 2^j (mod 2^(j+2))`, `0 ≤ i, j ≤ J - 3`. -/
def Lemma34 (J : ℕ) : Prop := ∀ n : ℤ, ¬ (2 : ℤ) ^ (J - 1) ∣ n → ∃ a b : ℤ, n = a + b ∧
  ∃ i j : ℕ, i ≤ J - 3 ∧ j ≤ J - 3 ∧ a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)] ∧ b ≡ 2 ^ j [ZMOD 2 ^ (j + 2)]

/- Lemma 3.4 is proved below after the base residue table. -/

/-- Lemma 3.5: every `m' ≢ 3, 6 (mod 9)` is `x₁² + x₂² + x₃² + x₄² (mod 27)` with
`x₁² + x₂², x₃² + x₄² ≢ 1 (mod 3)` and `≢ 0 (mod 27)`. -/
def Lemma35 : Prop := ∀ m : ℤ, ¬ m ≡ 3 [ZMOD 9] → ¬ m ≡ 6 [ZMOD 9] →
  ∃ x₁ x₂ x₃ x₄ : ℤ, m ≡ x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 [ZMOD 3 ^ 3] ∧
    ¬ x₁ ^ 2 + x₂ ^ 2 ≡ 1 [ZMOD 3] ∧ ¬ x₃ ^ 2 + x₄ ^ 2 ≡ 1 [ZMOD 3] ∧
    ¬ x₁ ^ 2 + x₂ ^ 2 ≡ 0 [ZMOD 3 ^ 3] ∧ ¬ x₃ ^ 2 + x₄ ^ 2 ≡ 0 [ZMOD 3 ^ 3]

/-! ## Proved links, zero sorry -/

/-- Lemma 3.5, PROVED by an explicit witness for each residue mod 27. -/
theorem lemma_3_5 : Lemma35 := by
  intro m h3 h6
  simp only [Int.ModEq] at h3 h6
  norm_num at h3 h6
  have h : m % 27 = 0 ∨ m % 27 = 1 ∨ m % 27 = 2 ∨ m % 27 = 4 ∨ m % 27 = 5 ∨ m % 27 = 7 ∨ m % 27 = 8 ∨ m % 27 = 9 ∨ m % 27 = 10 ∨ m % 27 = 11 ∨ m % 27 = 13 ∨ m % 27 = 14 ∨ m % 27 = 16 ∨ m % 27 = 17 ∨ m % 27 = 18 ∨ m % 27 = 19 ∨ m % 27 = 20 ∨ m % 27 = 22 ∨ m % 27 = 23 ∨ m % 27 = 25 ∨ m % 27 = 26 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨0, 3, 3, 3, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 5, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 10, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 1, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 7, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 2, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 5, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨3, 3, 3, 3, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 13, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 1, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 8, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 2, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 11, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 13, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 0, 3, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 4, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 8, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 10, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 11, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨1, 1, 1, 7, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩
  · exact ⟨0, 3, 1, 4, by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int.ModEq] <;> (norm_num; try omega)⟩

/-- Lemma 3.4 for `J = 5`, PROVED: the case `2^4 ∤ n`, by a witness for each residue mod 16. -/
theorem lemma_3_4_five : Lemma34 5 := by
  intro n hn
  norm_num at hn
  have h : n % 16 = 1 ∨ n % 16 = 2 ∨ n % 16 = 3 ∨ n % 16 = 4 ∨ n % 16 = 5 ∨ n % 16 = 6 ∨ n % 16 = 7 ∨ n % 16 = 8 ∨ n % 16 = 9 ∨ n % 16 = 10 ∨ n % 16 = 11 ∨ n % 16 = 12 ∨ n % 16 = 13 ∨ n % 16 = 14 ∨ n % 16 = 15 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨13, n - 13, by ring, 0, 2, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 0, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 1, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨2, n - 2, by ring, 1, 1, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 2, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 0, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨5, n - 5, by ring, 0, 1, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨4, n - 4, by ring, 2, 2, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨5, n - 5, by ring, 0, 2, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 0, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 1, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨2, n - 2, by ring, 1, 1, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨9, n - 9, by ring, 0, 2, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨1, n - 1, by ring, 0, 0, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩
  · exact ⟨5, n - 5, by ring, 0, 1, by norm_num, by norm_num, by simp only [Int.ModEq]; norm_num, by simp only [Int.ModEq]; norm_num; omega⟩

/-- Lemma 3.4 for every J at least 5, with its original statement. -/
theorem lemma_3_4 (J : ℕ) (hJ : 5 ≤ J) : Lemma34 J := by
  have hdouble {a : ℤ} {i : ℕ} (h : a ≡ 2 ^ i [ZMOD 2 ^ (i + 2)]) :
      2 * a ≡ 2 ^ (i + 1) [ZMOD 2 ^ (i + 1 + 2)] := by
    have : 2 * a ≡ 2 * 2 ^ i [ZMOD 2 * 2 ^ (i + 2)] := Int.ModEq.mul_left' h
    rw [show (2 : ℤ) ^ (i + 1 + 2) = 2 * 2 ^ (i + 2) by ring, show (2 : ℤ) ^ (i + 1) = 2 * 2 ^ i by ring]
    exact this
  have hstep {J : ℕ} (hJ : 5 ≤ J) (h : Lemma34 J) : Lemma34 (J + 1) := by
    intro n hn
    by_cases hd : (2 : ℤ) ^ (J - 1) ∣ n
    · obtain ⟨n', rfl⟩ := hd
      have hJ1 : J - 1 = (J - 2) + 1 := by omega
      have hnm : (2 : ℤ) ^ (J - 1) * n' = 2 * (2 ^ (J - 2) * n') := by rw [hJ1, pow_succ]; ring
      have hm : ¬ (2 : ℤ) ^ (J - 1) ∣ 2 ^ (J - 2) * n' := by
        rintro ⟨c, hc⟩
        apply hn
        refine ⟨c, ?_⟩
        rw [hnm, hc, show J + 1 - 1 = (J - 1) + 1 by omega, pow_succ]; ring
      obtain ⟨a, b, hab, i, j, hi, hj, ha, hb⟩ := h _ hm
      refine ⟨2 * a, 2 * b, ?_, i + 1, j + 1, by omega, by omega, hdouble ha, hdouble hb⟩
      rw [hnm, hab]; ring
    · obtain ⟨a, b, hab, i, j, hi, hj, ha, hb⟩ := h n hd
      exact ⟨a, b, hab, i, j, by omega, by omega, ha, hb⟩
  induction J, hJ using Nat.le_induction with
  | base => exact lemma_3_4_five
  | succ J hJ ih => exact hstep hJ ih

#print axioms lemma_3_4

/-! ### The integer form of `𝒫` equals the natural number form -/

theorem inP_iff_nat {p : ℕ} : InP p ↔ p.Prime ∧ ∃ x y : ℕ, p = x ^ 2 + y ^ 2 + 1 := by
  constructor
  · rintro ⟨hp, x, y, h⟩
    refine ⟨hp, x.natAbs, y.natAbs, ?_⟩
    have : ((x.natAbs ^ 2 + y.natAbs ^ 2 + 1 : ℕ) : ℤ) = x ^ 2 + y ^ 2 + 1 := by
      push_cast; simp only [sq_abs]
    exact_mod_cast h.trans this.symm
  · rintro ⟨hp, x, y, h⟩
    exact ⟨hp, x, y, by rw [h]; push_cast; ring⟩

theorem pStar_subset : PStar ⊆ PSet := by
  rintro p ⟨hp, x, y, _, h⟩
  exact ⟨hp, x, y, h⟩

/-! ### The local condition mod 9 is necessary -/

theorem sq_mod_nine (x : ℤ) : x ^ 2 % 9 = 0 ∨ x ^ 2 % 9 = 1 ∨ x ^ 2 % 9 = 4 ∨ x ^ 2 % 9 = 7 := by
  have h : x ^ 2 % 9 = (x % 9) ^ 2 % 9 := by rw [pow_two, pow_two, Int.mul_emod]
  rw [h]
  have : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨
    x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by omega
  rcases this with h|h|h|h|h|h|h|h|h <;> rw [h] <;> norm_num

/-- A prime `p ≠ 3` in `𝒫` is `≡ 1, 2, 5, 8 (mod 9)`. -/
theorem inP_mod_nine {p : ℕ} (hp : InP p) (h3 : p ≠ 3) :
    p % 9 = 1 ∨ p % 9 = 2 ∨ p % 9 = 5 ∨ p % 9 = 8 := by
  obtain ⟨hpr, x, y, h⟩ := hp
  have hnd : ¬ 3 ∣ p := by
    intro hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp hd).symm
  have hx := sq_mod_nine x
  have hy := sq_mod_nine y
  generalize x ^ 2 = X at h hx
  generalize y ^ 2 = Y at h hy
  omega

/-- The necessity remark after Theorem 1.1: if `p, q ∈ 𝒫` and neither is `3`, then
`p + q ≢ 5, 8 (mod 9)`. -/
theorem local_obstruction {p q : ℕ} (hp : InP p) (hq : InP q) (hp3 : p ≠ 3) (hq3 : q ≠ 3) :
    (p + q) % 9 ≠ 5 ∧ (p + q) % 9 ≠ 8 := by
  have := inP_mod_nine hp hp3
  have := inP_mod_nine hq hq3
  omega

/-- If `n ≡ 5, 8 (mod 9)` is `p + q` with `p, q ∈ 𝒫`, then `3` is one of the summands. -/
theorem three_used {n p q : ℕ} (hp : InP p) (hq : InP q) (h : p + q = n)
    (hn : n % 9 = 5 ∨ n % 9 = 8) : p = 3 ∨ q = 3 := by
  by_contra hc
  push Not at hc
  have := local_obstruction hp hq hc.1 hc.2
  omega

/-! ### Theorem 1.1 implies weaker almost-all statements -/

theorem excCount_mono {R S : ℕ → Prop} (h : ∀ n, R n → S n) (N : ℕ) :
    excCount S N ≤ excCount R N := by
  unfold excCount
  apply card_le_card
  intro n hn
  simp only [mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, fun hR => hn.2.2.2.2 (h n hR)⟩

theorem almostAll_mono {R S : ℕ → Prop} (h : ∀ n, R n → S n) (hR : AlmostAllAdmissible R) :
    AlmostAllAdmissible S := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hR ε hε
  refine ⟨N₀, fun N hN => le_trans ?_ (hN₀ N hN)⟩
  exact_mod_cast excCount_mono h N

/-- Matomäki's form, one prime from `𝒫` and one generic prime, follows from Theorem 1.1. -/
theorem matomaki_form_of_theorem11 (h : Theorem11) :
    AlmostAllAdmissible (fun n => ∃ p q : ℕ, InP p ∧ q.Prime ∧ p + q = n) :=
  almostAll_mono (fun _ ⟨p, q, hp, hq, hs⟩ => ⟨p, q, hp, hq.1, hs⟩) h

/-- Theorem 1.1 gives almost all even `n ≢ 5, 8 (mod 9)` as Goldbach sums. -/
theorem goldbach_almostAll_of_theorem11 (h : Theorem11) : AlmostAllAdmissible IsGoldbachSum :=
  almostAll_mono (fun _ ⟨p, q, hp, hq, hs⟩ => ⟨p, q, hp.1, hq.1, hs⟩) h

/-! ### Theorem 1.2 implies the lab's ternary form for large `n` -/

theorem isTernarySum_of_isPSum3 {n : ℕ} (h : IsPSum3 n) : IsTernarySum n :=
  let ⟨p, q, r, hp, hq, hr, hs⟩ := h
  ⟨p, q, r, hp.1, hq.1, hr.1, hs⟩

/-- Theorem 1.2 implies Vinogradov's qualitative theorem in the lab's form. -/
theorem ternaryAbove_of_theorem12 (h : Theorem12) : ∃ C : ℝ, LeanLab.Ternary.TernaryAbove C := by
  obtain ⟨N₀, hN₀⟩ := h
  exact ⟨N₀, fun n ho hn => isTernarySum_of_isPSum3 (hN₀ n (by exact_mod_cast hn) ho)⟩

/-! ### Theorem 1.3 gives three term progressions in `𝒫` -/

theorem infinitely3AP_mono {A B : Set ℕ} (hAB : A ⊆ B) (h : InfinitelyMany3AP A) :
    InfinitelyMany3AP B := by
  refine Set.Infinite.mono ?_ h
  rintro t ⟨hd, h1, h2, h3⟩
  exact ⟨hd, hAB h1, hAB h2, hAB h3⟩

theorem two_mem_pStar : 2 ∈ PStar := ⟨Nat.prime_two, 1, 0, by norm_num, by norm_num⟩

theorem countIn_pos_of_mem {A : Set ℕ} {a N : ℕ} (ha : a ∈ A) (h1 : 1 ≤ a) (hN : a ≤ N) :
    0 < countIn A N := by
  unfold countIn
  apply card_pos.mpr
  exact ⟨a, by simp only [mem_filter, mem_Icc]; exact ⟨⟨h1, hN⟩, ha⟩⟩

/-- `𝒫*` has positive upper density in itself. -/
theorem pStar_posDensity_self : PosUpperDensityIn PStar PStar := by
  refine ⟨1 / 2, by norm_num, fun N₀ => ⟨max N₀ 2, le_max_left _ _, ?_⟩⟩
  have := countIn_pos_of_mem two_mem_pStar (by norm_num) (le_max_right N₀ 2)
  have h : (0 : ℝ) < countIn PStar (max N₀ 2) := by exact_mod_cast this
  linarith

/-- Theorem 1.3 implies that `𝒫*`, hence `𝒫`, contains infinitely many non-trivial
three term arithmetic progressions, as stated in the introduction. -/
theorem pSet_3AP_of_theorem13 (h : Theorem13) : InfinitelyMany3AP PStar ∧ InfinitelyMany3AP PSet := by
  have h1 := h PStar le_rfl pStar_posDensity_self
  exact ⟨h1, infinitely3AP_mono pStar_subset h1⟩

/-! ### Theorem 1.4 implies that `𝒫` is infinite, Linnik's theorem -/

theorem pSet_infinite_of_theorem14 (h : Theorem14) : PSet.Infinite :=
  (h _ irrational_sqrt_two 0 1 one_pos).mono fun _ hp => hp.1

/-! ### Small kernel-checked examples -/

/-- Witnesses `(p, x, y)` with `p = x² + y² + 1` prime, all such `p ≤ 201`. -/
def witP : List (ℕ × ℕ × ℕ) :=
  [(2, 0, 1), (3, 1, 1), (5, 0, 2), (11, 1, 3), (17, 0, 4), (19, 3, 3), (37, 0, 6), (41, 2, 6),
   (53, 4, 6), (59, 3, 7), (73, 6, 6), (83, 1, 9), (101, 0, 10), (107, 5, 9), (131, 3, 11),
   (137, 6, 10), (149, 2, 12), (163, 9, 9), (179, 3, 13), (181, 6, 12), (197, 0, 14)]

/-- The primes in `witP`. -/
def listP : List ℕ := witP.map (·.1)

def witCheck : Bool := witP.all fun t => primeB t.1 && t.1 == t.2.1 * t.2.1 + t.2.2 * t.2.2 + 1

theorem witCheck_true : witCheck = true := by decide +kernel

theorem inP_of_mem_listP {p : ℕ} (h : p ∈ listP) : InP p := by
  simp only [listP, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  have := List.all_eq_true.mp witCheck_true t ht
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact inP_iff_nat.mpr ⟨primeB_sound this.1, t.2.1, t.2.2, by rw [this.2]; ring⟩

/-- `repB n k`: some `x, y < k` have `x² + y² + 1 = n`. -/
def repB (n k : ℕ) : Bool :=
  (List.range k).any fun x => (List.range k).any fun y => x * x + y * y + 1 == n

theorem repB_complete {n k x y : ℕ} (hn : n < k * k) (h : n = x ^ 2 + y ^ 2 + 1) :
    repB n k = true := by
  have hx : x < k := by
    by_contra hc; push Not at hc; nlinarith [Nat.mul_le_mul hc hc]
  have hy : y < k := by
    by_contra hc; push Not at hc; nlinarith [Nat.mul_le_mul hc hc]
  simp only [repB, List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨x, hx, y, hy, by rw [h]; ring⟩

/-- `compB n`: some `d` with `2 ≤ d < n` divides `n`. -/
def compB (n : ℕ) : Bool := (List.range n).any fun d => 2 ≤ d && n % d == 0

theorem not_prime_of_compB {n : ℕ} (h : compB n = true) : ¬ n.Prime := by
  simp only [compB, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨d, hdn, h2, hd⟩ := h
  intro hp
  have := (Nat.prime_def_lt.mp hp).2 d hdn (Nat.dvd_of_mod_eq_zero hd)
  omega

def classB (n : ℕ) : Bool := decide (n < 2) || listP.contains n || !repB n 11 || compB n

theorem classB_all : ∀ n, n < 101 → classB n = true := by decide +kernel

/-- PROVED: the primes of the form `x² + y² + 1` up to `100` are exactly
`2, 3, 5, 11, 17, 19, 37, 41, 53, 59, 73, 83`. -/
theorem inP_iff_small {n : ℕ} (hn : n ≤ 100) :
    InP n ↔ n ∈ [2, 3, 5, 11, 17, 19, 37, 41, 53, 59, 73, 83] := by
  have hL : ∀ m, m ≤ 100 → (m ∈ listP ↔ m ∈ [2, 3, 5, 11, 17, 19, 37, 41, 53, 59, 73, 83]) := by
    decide +kernel
  rw [← hL n hn]
  refine ⟨fun h => ?_, inP_of_mem_listP⟩
  have hc := classB_all n (by omega)
  simp only [classB, Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · exact absurd h.1.two_le (by simp only [decide_eq_true_eq] at hc; omega)
  · exact hc
  · obtain ⟨hp, x, y, hxy⟩ := inP_iff_nat.mp h
    rw [repB_complete (by omega) hxy] at hc
    exact absurd hc (by simp)
  · exact absurd h.1 (not_prime_of_compB hc)

/-- For `n ≤ 100`, being a sum of two primes of `𝒫` is a finite check. -/
theorem isPSum2_iff_small {n : ℕ} (hn : n ≤ 100) :
    IsPSum2 n ↔ ∃ p ∈ List.range (n + 1),
      p ∈ [2, 3, 5, 11, 17, 19, 37, 41, 53, 59, 73, 83] ∧
      n - p ∈ [2, 3, 5, 11, 17, 19, 37, 41, 53, 59, 73, 83] := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨p, List.mem_range.mpr (by omega), (inP_iff_small (by omega)).mp hp, ?_⟩
    rw [show p + q - p = q by omega]
    exact (inP_iff_small (by omega)).mp hq
  · rintro ⟨p, hp, h1, h2⟩
    have hp' := List.mem_range.mp hp
    exact ⟨p, n - p, (inP_iff_small (by omega)).mpr h1, (inP_iff_small (by omega)).mpr h2,
      by omega⟩

/-- PROVED: `12, 18, 66` are even, `≢ 5, 8 (mod 9)`, and not sums of two primes of `𝒫`;
so Theorem 1.1 has genuine exceptions and cannot say "all". -/
theorem exceptions_small : ∀ n ∈ [12, 18, 66], Even n ∧ n % 9 ≠ 5 ∧ n % 9 ≠ 8 ∧ ¬ IsPSum2 n := by
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl <;>
  · refine ⟨by decide, by decide, by decide, ?_⟩
    rw [isPSum2_iff_small (by norm_num)]
    decide +kernel

/-- PROVED: `8 = 5 + 3` and `14 = 11 + 3` are `≡ 8, 5 (mod 9)` and are sums of two primes
of `𝒫`, using `3`; this is the exception noted after Theorem 1.1. -/
theorem uses_three : IsPSum2 8 ∧ IsPSum2 14 := by
  refine ⟨⟨5, 3, ?_, ?_, rfl⟩, ⟨11, 3, ?_, ?_, rfl⟩⟩ <;>
    exact inP_of_mem_listP (by decide)

/-- Checker for `n = p + q` with `p, q` in `listP`. -/
def p2B (n : ℕ) : Bool := listP.any fun p => p ≤ n && listP.contains (n - p)

theorem isPSum2_of_p2B {n : ℕ} (h : p2B n = true) : IsPSum2 n := by
  simp only [p2B, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem] at h
  obtain ⟨p, hp, hpn, hq⟩ := h
  exact ⟨p, n - p, inP_of_mem_listP hp, inP_of_mem_listP hq, by omega⟩

/-- Checker for `n = p + q + r` with `p, q, r` in `listP`. -/
def p3B (n : ℕ) : Bool := listP.any fun p => p ≤ n && p2B (n - p)

theorem isPSum3_of_p3B {n : ℕ} (h : p3B n = true) : IsPSum3 n := by
  simp only [p3B, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, hpn, h2⟩ := h
  obtain ⟨q, r, hq, hr, hs⟩ := isPSum2_of_p2B h2
  exact ⟨p, q, r, inP_of_mem_listP hp, hq, hr, by omega⟩

def ternSmallB : ℕ → Bool
  | 0 => true
  | n + 1 => (if (n + 1) % 2 = 1 && 7 ≤ n + 1 then p3B (n + 1) else true) && ternSmallB n

theorem ternSmallB_sound : ∀ N, ternSmallB N = true →
    ∀ n, Odd n → 7 ≤ n → n ≤ N → IsPSum3 n := by
  intro N
  induction N with
  | zero => intro _ n _ h7 hn; omega
  | succ k ih =>
    intro h n ho h7 hn
    simp only [ternSmallB, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact ih h.2 n ho h7 (by omega)
    · obtain rfl : n = k + 1 := by omega
      obtain ⟨h1, -⟩ := h
      split_ifs at h1 with hc
      · exact isPSum3_of_p3B h1
      · exfalso; apply hc
        simp only [decide_eq_true_eq]
        exact ⟨Nat.odd_iff.mp ho, h7⟩

/-- PROVED: every odd `n` with `7 ≤ n ≤ 201` is a sum of three primes of `𝒫`. -/
theorem ternary_small : ∀ n, Odd n → 7 ≤ n → n ≤ 201 → IsPSum3 n :=
  ternSmallB_sound 201 (by decide +kernel)

def binSmallB : ℕ → Bool
  | 0 => true
  | n + 1 => (if (n + 1) % 2 = 0 && 4 ≤ n + 1 && (n + 1) % 9 != 5 && (n + 1) % 9 != 8 &&
      !([12, 18, 66].contains (n + 1)) then p2B (n + 1) else true) && binSmallB n

theorem binSmallB_sound : ∀ N, binSmallB N = true → ∀ n, Even n → 4 ≤ n → n ≤ N →
    n % 9 ≠ 5 → n % 9 ≠ 8 → n ∉ [12, 18, 66] → IsPSum2 n := by
  intro N
  induction N with
  | zero => intro _ n _ h4 hn; omega
  | succ k ih =>
    intro h n he h4 hn h5 h8 hx
    simp only [binSmallB, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · exact ih h.2 n he h4 (by omega) h5 h8 hx
    · obtain rfl : n = k + 1 := by omega
      obtain ⟨h1, -⟩ := h
      split_ifs at h1 with hc
      · exact isPSum2_of_p2B h1
      · exfalso; apply hc
        simp only [decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true']
        refine ⟨⟨⟨⟨Nat.even_iff.mp he, h4⟩, h5⟩, h8⟩, ?_⟩
        simpa using hx

/-- PROVED: every even `n` with `4 ≤ n ≤ 100`, `n ≢ 5, 8 (mod 9)`, except `12, 18, 66`,
is a sum of two primes of `𝒫`. -/
theorem binary_small : ∀ n, Even n → 4 ≤ n → n ≤ 100 → n % 9 ≠ 5 → n % 9 ≠ 8 →
    n ∉ [12, 18, 66] → IsPSum2 n :=
  binSmallB_sound 100 (by decide +kernel)

end LeanLab.Teravainen2016
