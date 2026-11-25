/-
P0069 Baker Harman Pintz 1997, pages 11, 12, 20, 48 and 53, read from papers/P0069-original.pdf.
Burst burst-20261122, WAVE 3 unit on the LEAF kept52_wellspaced of the branch
claude/BHP1997-upD_kept_52, file Prep1122KeptLemma33Pieces52.lean.

That LEAF is the end of the proof of Lemma 33 on page 48, "||LMN||_2^2 << Y L^-A if t is in
[T, T + T2]", read for the kept part of k_m on page 53 and the principal character. Its own
hypotheses, Theorem 4 and Lemma 9, do not give it: the paper also uses Lemma 5 on page 20 for
(3.2) of the prime polynomials, and Lemma 1, display 3.3 on page 11, for the discrete mean value
bound. This file splits it once into four LEAFs, each a cited step of the paper:
1. kept52_lemma33_block, HARD, CONDITIONAL on Theorem 4: Lemma 33 on page 48 for one product
   LMN with (beta1, beta2) in R, P1 or P2, on one block of length T2.
2. kept52_prime_32, HARD, CITED: Lemma 5 on page 20, (3.2) for a prime polynomial at the
   principal character for T0 <= |t| <= Y.
3. kept52_mvt_lemma1, HARD, CITED: Lemma 1, display 3.3 on page 11, the mean value bound.
4. kept52_box_reduce, HARD: page 53, the reduction of the kept part of k_m to products to
   which Lemma 33 applies, from the three statements above as hypotheses.
kept52_wellspaced_split has the exact statement of kept52_wellspaced and is PROVED from them.

New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- LEAF: P0069 page 48, Lemma 33 and its proof, "for (beta1, beta2) in R we apply Theorem 4
with N^2 L, LM, M, T2 in place of M, N, L, T. Thus (3.5) holds with X = Y^2", and for P1 with
M^2 N, L^2, N, and P2 by beta1 to 1 - beta1 - beta2, ending "||LMN||_2^2 << Y L^-A if t is in
[T, T + T2]", for the principal character. M and N have lengths Y^beta1 and Y^beta2, satisfy
(3.1) and (3.2) on the block, L has length Y^(1 - beta1 - beta2) and satisfies (3.1), and
(beta1, beta2) lies in R, P1 or P2 as in upperPairRegion. Paper's proof: |LMN|^2 = |(LMN)^2|,
the block is moved into [-T, T] by kept52_dirPoly_shift, and Theorem 4 is applied with its own
x equal to Y^2 and X = x, theta just below 1/2 + theta2/4, and a smaller eps, see the notes.
CONDITIONAL on Theorem 4. HARD. -/
theorem kept52_lemma33_block (h4 : Thm4.Theorem4Paper) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
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
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 20, Lemma 5, used on page 50 as "we know from Lemma 5 that (3.2) holds":
the prime polynomial over u < p <= v, with P <= u <= v <= 2P and Y^c1 <= P <= Y, at the
principal character mod q <= Q satisfies (3.2) for T0 <= |t| <= Y, T0 = exp(L^(1/3)). The
paper's proof is a contour argument with the zero-free region (3.32); for the principal
character the needed region is of Vinogradov Korobov type, an input neither Theorem 4 nor
Lemma 9 gives. CITED, unconditional in the literature. HARD. -/
theorem kept52_prime_32 {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A' : ℝ, 0 < A' → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
        P ≤ u → u ≤ v → v ≤ 2 * P →
      ∀ t : ℝ, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ |t| → |t| ≤ x ^ (11 / 20 + ε) →
        ‖∑ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter
              (fun n : ℕ => n.Prime ∧ u < (n : ℝ) ∧ (n : ℝ) ≤ v),
            (1 : DirichletCharacter ℂ q) (p : ZMod q) / (p : ℂ) ^ Thm4.half t‖ ≤
          K * P ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
  sorry

/-- LEAF: P0069 page 11, Lemma 1, display 3.3: for a well-spaced set S in [-T, T],
||F||_2^2 << L (qT + F) G with G = sum over n of |a_n|^2 / n, here for the principal character
only, a subset of the pairs of the paper. The paper cites Montgomery, Lemma 1.4 and Theorem 6.4
of reference 21. Used for the boundary boxes of the decomposition on page 53. CITED,
unconditional in the literature. HARD. -/
theorem kept52_mvt_lemma1 :
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∃ C : ℝ, ∀ x T F : ℝ, ∀ q : ℕ,
      2 ≤ x → 1 ≤ q → (q : ℝ) ≤ x → 2 ≤ T → T ≤ x → 1 ≤ F → F ≤ x →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) → (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ a : ℕ → ℂ,
        ∑ t ∈ S, ‖Thm4.dirPoly a c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 ≤
          C * Real.log x * ((q : ℝ) * T + F) *
            ∑ n ∈ (Finset.range (⌊c₂ * F⌋₊ + 1)).filter
                (fun n : ℕ => c₁ * F < n ∧ (n : ℝ) < c₂ * F), ‖a n‖ ^ 2 / n := by
  sorry

/-- LEAF: P0069 page 53, "the terms of k_m for which Lemma 33 applies to some arrangement of
the variables", with the proof of Lemma 34 on page 50 for the splitting of the variables: the
kept part of k_m is cut into boxes for p1, p2, p3 and n4 on which the region test of
upperPrimeCovered and psi(n4, p3) are fixed, each inner box a product LMN to which Lemma 33
applies, M and N built from prime polynomials that satisfy (3.2) by Lemma 5, the boundary boxes
bounded by Lemma 1, and Cauchy Schwarz over the boxes, whose number is a power of L absorbed by
A. From the three statements of kept52_lemma33_block, kept52_prime_32 and kept52_mvt_lemma1 as
hypotheses. HARD. -/
theorem kept52_box_reduce {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
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
      ∀ P u v : ℝ, (x ^ (11 / 20 + ε)) ^ upperC1 ε ≤ P → P ≤ x ^ (11 / 20 + ε) →
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
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 48 with page 53: the exact statement of the LEAF kept52_wellspaced of
Prep1122KeptLemma33Pieces52, from the four LEAFs of this file. PROVED from those LEAFs, so
CONDITIONAL on them and on the cited Theorem 4; Lemma 9 is carried as in kept52_wellspaced and
not used. -/
theorem kept52_wellspaced_split (h4 : Thm4.Theorem4Paper) (_h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  kept52_box_reduce hε hε8 (kept52_lemma33_block h4 hε hε8) (kept52_prime_32 hε hε8)
    kept52_mvt_lemma1

end LeanLab.BHP1997.DecompC165d
