/-
P0069 Baker Harman Pintz 1997, pages 49 and 50, the proof of Lemma 34, read with
papers/P0069.txt lines 2495 to 2510 and the page images: "Let h_m be the contribution to g_m
from n ~ N, p1 ~ P. With N(s, chi) = sum chi(p1) p1^(-s), we know from Lemma 5 that (3.2)
holds, and of course if P >= Y^eps we may obtain (5.1) and (5.2) from Lemma 33."
Burst burst-20261124 session S4, unit S4-25, split of the LEAF `upD52_leaf_g_big_lemma33` of
Prep1122UpD52Split.lean.

The PROVED helper `upD52_gbig_of_wellspaced` already reduces that LEAF to a well-spaced block
bound for the one-prime coefficient c. This file states that bound as the end of a reduction
in the shape of `kept52_box_reduce` of Prep1122KeptWellspacedSplit52.lean, reusing two of its
LEAFs unchanged, `kept52_lemma33_block`, Lemma 33 on page 48, and `kept52_mvt_lemma1`,
Lemma 1 on page 11, and adding two new LEAFs:
1. gbig52_prime_32, HARD, CITED: Lemma 5 on page 20 for the prime polynomial over p1 ~ P with
   Y^eps <= P <= Y, the range page 50 needs. The lab's `kept52_prime_32` covers only
   Y^c1 <= P, which misses Y^eps <= p1 < Y^c1, the whole range of the big part of g_m.
2. gbig52_box_reduce, HARD: page 50, the reduction of c to products to which Lemma 33
   applies, from the three cited statements as hypotheses.
`upD52_leaf_g_big_lemma33_of_leaves` has the exact statement of the target LEAF and is
PROVED from these. The target file is not changed, since this file imports it.
New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.Prep1122UpD52Split
import LeanLab.BHP1997.Prep1122KeptWellspacedSplit52

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- LEAF: P0069 page 20, Lemma 5, as used on page 50 for the big part of g_m: "With
N(s, chi) = sum chi(p1) p1^(-s), we know from Lemma 5 that (3.2) holds". The prime polynomial
over u < p <= v, with P <= u <= v <= 2P and Y^eps <= P <= Y, at the principal character mod
q <= Q satisfies (3.2) for T0 <= |t| <= Y, T0 = exp(L^(1/3)). Lemma 5 needs only
P > exp(L^(9/10)), see its proof on page 20, so Y^eps <= P is inside its range. The paper's
proof is a contour argument with the zero-free region (3.32). CITED, unconditional in the
literature. Class HARD. -/
theorem gbig52_prime_32 {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 50, proof of Lemma 34, "if P >= Y^eps we may obtain (5.1) and (5.2) from
Lemma 33": the one-prime coefficient c of the big part of g_m is cut into dyadic boxes n ~ N,
p1 ~ P; each box is a product to which Lemma 33 applies, with N(s, chi0) satisfying (3.2) by
Lemma 5, boundary boxes by Lemma 1, and Cauchy Schwarz over the L^O(1) boxes gives the
well-spaced block bound. From the statements of kept52_lemma33_block, gbig52_prime_32 and
kept52_mvt_lemma1 as hypotheses. Class HARD. -/
theorem gbig52_box_reduce {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ)
    {B : ℝ} (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ))
    (H33 : ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (H5 : ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A'))
    (H1 : ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∃ C : ℝ, ∀ x T F : ℝ, ∀ q : ℕ,
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → 2 ≤ T → T ≤ x → 1 ≤ F → F ≤ x →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) → (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ a : ℕ → ℂ,
        ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
          C * Real.log x * ((q : ℝ) * T + F) *
            ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
                (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), ‖a n‖ ^ 2 / n) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 pages 49 and 50: the exact statement of the LEAF `upD52_leaf_g_big_lemma33` of
Prep1122UpD52Split.lean, PROVED from `gbig52_box_reduce`, `gbig52_prime_32` and the two
reused LEAFs `kept52_lemma33_block` and `kept52_mvt_lemma1`, through the PROVED reduction
`upD52_gbig_of_wellspaced`. CONDITIONAL on those LEAFs and on the cited Theorem 4; Lemma 9 is
carried as in the target and not used. -/
theorem upD52_leaf_g_big_lemma33_of_leaves (h4 : Thm4.Theorem4Paper)
    (_h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (a : ℝ → ℕ → ℝ) {B : ℝ}
    (ha : ∃ C : ℝ, ∀ x n, |a x n| ≤ C * ((n.divisors.card : ℕ) : ℝ) ^ B)
    (c : ℝ → ℕ → ℝ)
    (hc : ∀ x k, c x k = ∑ n ∈ k.divisors.filter (fun n : ℕ =>
          (n : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 2 + (2 * (1 / 16 - 1 / 10 ^ 5)) / 4 - 2 * ε)),
        a x n * ∑ p ∈ (k / n).primeFactors.filter (fun p : ℕ =>
            (Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ (p : ℝ) ∧
              (p : ℝ) < (x ^ (11 / 20 + ε)) ^ upperC1 ε) ∧
            (x ^ (11 / 20 + ε)) ^ ε ≤ (p : ℝ)),
          upperRough (k / n / p) (p : ℝ)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (c x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) :=
  upD52_gbig_of_wellspaced c
    (gbig52_box_reduce hε hε8 a ha c hc (kept52_lemma33_block h4 hε hε8)
      (gbig52_prime_32 hε hε8) kept52_mvt_lemma1)

/-- Verbatim check: the assembly has exactly the type of `upD52_leaf_g_big_lemma33`. -/
example : type_of% @upD52_leaf_g_big_lemma33 := @upD52_leaf_g_big_lemma33_of_leaves

end LeanLab.BHP1997.DecompC165d

#print axioms LeanLab.BHP1997.DecompC165d.upD52_leaf_g_big_lemma33_of_leaves
