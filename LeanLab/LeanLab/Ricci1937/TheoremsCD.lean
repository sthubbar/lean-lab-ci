import Mathlib

/-!
# P0092 Ricci 1937, Theorems (C) and (D) of the introduction, pages 74 and 75

Lab statements, unit U-5611, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Read from the
page images of papers/P0092.pdf, the numdam copy. Binary Goldbach is OPEN; Theorem (D) is an
almost prime binary result, the a = b = 1 case of which would be Goldbach with a count.

Readings.
* "composto con al più a fattori primi (uguali o distinti), ciascuno maggiore di y": `x ≥ 1`,
  `Ω(x) ≤ a` and every prime factor `> y`; `AlmostGT a y x`. For `x = 1` the condition holds
  vacuously, as in the paper, which counts `x` with at most `a` factors.
* Theorem (C): `D · F(x)` is a primitive irreducible integer polynomial of degree `g` with fixed
  divisor `D`, the gcd of its values; so `F(n) = (D·F)(n)/D` is an integer. Encoded with
  `P = D·F` and `F(n) = P(n)/D`, `D = fixedDivisor P`.
* Theorem (D): `m ≠ 0` an integer, `Z(ξ)` counts `0 < x ≤ ξ` with `x` an `a`-almost prime with
  factors `> x^{1/(a+1)}` and `x + 2m` a `b`-almost prime with factors `> x^{1/(b+1)}`; `W(N)` counts
  `N = A + B`, `A, B ≥ 1`, with thresholds `N^{1/(a+1)}`, `N^{1/(b+1)}`. The paper's `O`-statements
  are `≍` claims with constants depending on `a, b, m`.
* Pairs (6, 6) Estermann, (5, 7), (4, 9), (3, 15), (2, 366).

* `almostGT_mono`: `AlmostGT a y x → a ≤ a' → y' ≤ y → AlmostGT a' y' x`, PROVED.
* `wCount_mono`: `W_{a,b}(N) ≤ W_{a',b'}(N)` for `a ≤ a'`, `b ≤ b'`, PROVED.
* `theoremD_W_mono`: the `W` half of Theorem (D) passes from `(a, b)` to `(a', b')`, PROVED.
* `TheoremC1`, `TheoremC2`, `TheoremD` and the five pairs `ricciD`: STATED, cited.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `x ≥ 1` has at most `a` prime factors, counted with multiplicity, each `> y`. -/
def AlmostGT (a : ℕ) (y : ℝ) (x : ℕ) : Prop :=
  1 ≤ x ∧ x.primeFactorsList.length ≤ a ∧ ∀ p ∈ x.primeFactorsList, y < (p : ℝ)

lemma almostGT_mono {a a' : ℕ} {y y' : ℝ} {x : ℕ} (h : AlmostGT a y x) (ha : a ≤ a')
    (hy : y' ≤ y) : AlmostGT a' y' x :=
  ⟨h.1, h.2.1.trans ha, fun p hp => lt_of_le_of_lt hy (h.2.2 p hp)⟩

/-- `W_{a,b}(N)`: the partitions `N = A + B`, `A, B ≥ 1`, `A` an `a`-almost prime with factors
`> N^{1/(a+1)}`, `B` a `b`-almost prime with factors `> N^{1/(b+1)}`. -/
def wCount (a b N : ℕ) : ℕ :=
  #{A ∈ Icc 1 (N - 1) | AlmostGT a ((N : ℝ) ^ ((1 : ℝ) / (a + 1))) A ∧
    AlmostGT b ((N : ℝ) ^ ((1 : ℝ) / (b + 1))) (N - A)}

/-- `Z_{a,b,m}(ξ)`: the `0 < x ≤ ξ` with `x` an `a`-almost prime with factors `> x^{1/(a+1)}` and
`x + 2m > 0` a `b`-almost prime with factors `> x^{1/(b+1)}`. -/
def zCount (a b : ℕ) (m : ℤ) (ξ : ℕ) : ℕ :=
  #{x ∈ Icc (1 : ℕ) ξ | AlmostGT a (((x : ℕ) : ℝ) ^ ((1 : ℝ) / (a + 1))) x ∧ 0 < ((x : ℕ) : ℤ) + 2 * m ∧
    AlmostGT b (((x : ℕ) : ℝ) ^ ((1 : ℝ) / (b + 1))) (((x : ℕ) : ℤ) + 2 * m).toNat}

lemma rpow_inv_mono {N : ℕ} {a a' : ℕ} (ha : a ≤ a') :
    (N : ℝ) ^ ((1 : ℝ) / (a' + 1)) ≤ (N : ℝ) ^ ((1 : ℝ) / (a + 1)) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [Nat.cast_zero]
    rw [Real.zero_rpow (by positivity), Real.zero_rpow (by positivity)]
  · have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    apply Real.rpow_le_rpow_of_exponent_le h1
    have : (a : ℝ) ≤ a' := by exact_mod_cast ha
    gcongr

theorem wCount_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (N : ℕ) :
    wCount a b N ≤ wCount a' b' N := by
  unfold wCount
  refine card_le_card fun A hA => ?_
  rw [mem_filter] at hA ⊢
  exact ⟨hA.1, almostGT_mono hA.2.1 ha (rpow_inv_mono ha),
    almostGT_mono hA.2.2 hb (rpow_inv_mono hb)⟩

/-- Theorem (D), the `W` half: `N/log² N = O(W(N))` over even `N`. -/
def TheoremDW (a b : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    c * N / Real.log N ^ 2 ≤ wCount a b N

/-- Theorem (D), the `Z` half: `ξ/log² ξ = O(Z(ξ))` and `Z(ξ) = O(ξ/log² ξ)` for every `m ≠ 0`. -/
def TheoremDZ (a b : ℕ) : Prop :=
  ∀ m : ℤ, m ≠ 0 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
    c * ξ / Real.log ξ ^ 2 ≤ zCount a b m ξ ∧ (zCount a b m ξ : ℝ) ≤ C * ξ / Real.log ξ ^ 2

def TheoremD (a b : ℕ) : Prop := TheoremDZ a b ∧ TheoremDW a b

/-- Ricci's five pairs, cited: `(6, 6)` after Estermann, `(5, 7)`, `(4, 9)`, `(3, 15)`, `(2, 366)`. -/
theorem ricciD : TheoremD 6 6 ∧ TheoremD 5 7 ∧ TheoremD 4 9 ∧ TheoremD 3 15 ∧ TheoremD 2 366 := by
  sorry

theorem theoremD_W_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (h : TheoremDW a b) :
    TheoremDW a' b' := by
  obtain ⟨c, hc, N₀, hN⟩ := h
  exact ⟨c, hc, N₀, fun N h1 h2 => le_trans (hN N h1 h2) (by exact_mod_cast wCount_mono ha hb N)⟩

/-- The fixed divisor of an integer polynomial, the gcd of its values on the positive integers,
encoded as the largest `D` dividing every value. -/
def fixedDivisor (P : Polynomial ℤ) : ℕ := sSup {D : ℕ | ∀ n : ℕ, 1 ≤ n → (D : ℤ) ∣ P.eval (n : ℤ)}

/-- The hypotheses of Theorem (C): `P = D · F` has integer coefficients, degree `g ≥ 1`, is
primitive and irreducible, with positive leading coefficient so that `F(n) ≥ 1` eventually. -/
def CHyp (P : Polynomial ℤ) : Prop :=
  1 ≤ P.natDegree ∧ P.IsPrimitive ∧ Irreducible P ∧ 0 < P.leadingCoeff

/-- `F(n) = (D·F)(n)/D` as a natural number, for `n` with positive value. -/
def Fval (P : Polynomial ℤ) (n : ℕ) : ℕ := (P.eval (n : ℤ) / fixedDivisor P).toNat

/-- Theorem (C) 1°: infinitely many `F(n)` with at most `3g - 1` prime factors, all `> n^{1/3}`,
and `ξ/log ξ ≪ B(ξ) ≪ ξ/log ξ` for their count. -/
def TheoremC1 : Prop := ∀ P : Polynomial ℤ, CHyp P →
  ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧ ∃ a₃ : ℕ, ∀ ξ : ℕ, a₃ < ξ →
    a₁ * ξ / Real.log ξ < #{n ∈ Icc (1 : ℕ) ξ | AlmostGT (3 * P.natDegree - 1)
        (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) (Fval P n)} ∧
    (#{n ∈ Icc (1 : ℕ) ξ | AlmostGT (3 * P.natDegree - 1) (((n : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) (Fval P n)} : ℝ) <
      a₂ * ξ / Real.log ξ

/-- Theorem (C) 2°: for `g + 1 ≤ s ≤ 3g`, infinitely many `F(n)` with at most `⌊(2sg - 1)/(s - g)⌋`
prime factors, all `> n^{(s-g)/(2s)}`, each with exponent `< s`; with the same two sided count. -/
def TheoremC2 : Prop := ∀ P : Polynomial ℤ, CHyp P → ∀ s : ℕ,
  P.natDegree + 1 ≤ s → s ≤ 3 * P.natDegree →
  ∃ a₁ a₂ : ℝ, 0 < a₁ ∧ 0 < a₂ ∧ ∃ a₃ : ℕ, ∀ ξ : ℕ, a₃ < ξ →
    let S := #{n ∈ Icc (1 : ℕ) ξ | AlmostGT ((2 * s * P.natDegree - 1) / (s - P.natDegree))
        (((n : ℕ) : ℝ) ^ (((s : ℝ) - P.natDegree) / (2 * s))) (Fval P n) ∧
        ∀ p ∈ (Fval P n).primeFactors, (Fval P n).factorization p < s}
    a₁ * ξ / Real.log ξ < S ∧ (S : ℝ) < a₂ * ξ / Real.log ξ

/-- Cited. -/
theorem ricciC1 : TheoremC1 := by sorry

/-- Cited. -/
theorem ricciC2 : TheoremC2 := by sorry

/-- Vacuity of `AlmostGT`: `15 = 3 · 5` has two prime factors, both `> 2`. -/
example : AlmostGT 2 2 15 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [show Nat.primeFactorsList 15 = [3, 5] by norm_num]; simp
  · rw [show Nat.primeFactorsList 15 = [3, 5] by norm_num]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num

end

end LeanLab.Ricci1937
