/-
Split of helfgott_theorem63_minor_inputs from Feed1122Decomp420b.
Helfgott https://arxiv.org/abs/1312.7748v2, proof of Theorem 6.3 on pages 50 to 52
and its application in section 7.3, pages 62, 63 and 69, equations 7.26, 7.27,
7.30, 7.47 and 7.48. The prime sum over primes above the square root of x is
split from the rest as on page 50; the weighted triangle inequality, the bound
for the small or non-prime part and the bound for the large prime part are
separate leaves. The book 1501.05438 page 274 correction turns 0.77671 into 0.77962.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp420b

namespace LeanLab.Ternary.Task420
open Finset MeasureTheory

/-- LEAF: Helfgott 1312.7748v2 page 50, the triangle inequality with weights
the absolute value of S eta star, after writing S eta plus as S one plus S two,
where S one is the sum over primes p above the square root of x, MEDIUM.
The minor arc integral of the Fourier norm is at most the square of the sum of the
square roots of the two weighted integrals of the squares of S one and S two. -/
theorem helfgott_minor_weighted_triangle (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖helfgottIntegrand N α‖) ≤
      (Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
          ‖LeanLab.HelfgottArcs.S
            (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
              LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
          ‖∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
                (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
            else 0)‖ ^ 2) +
        Real.sqrt (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
          ‖LeanLab.HelfgottArcs.S
            (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
              LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
          ‖LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α (LeanLab.Helfgott2013.xOf N) -
            ∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
                (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
            else 0)‖ ^ 2)) ^ 2 := by
  sorry

/-- LEAF: Helfgott 1312.7748v2 page 50, the display after Clearly: the weighted
integral of the square of S two is at most the maximum of S eta star, which is
the sum of Lambda of n times eta star of n over x, times the integral of the square
of S two over the circle, which by Parseval is the sum of Lambda of n squared
times eta plus of n over x squared over n non-prime or n at most root x, MEDIUM. -/
theorem helfgott_minor_small_part_parseval (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖LeanLab.HelfgottArcs.S
          (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
        ‖LeanLab.HelfgottArcs.S LeanLab.HelfgottArcs.etaPlus α (LeanLab.Helfgott2013.xOf N) -
          ∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
              (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
          else 0)‖ ^ 2) ≤
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
          LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
            (49 * (n / LeanLab.Helfgott2013.xOf N))) *
        ∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
          (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
            LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2) := by
  sorry

/-- LEAF: Helfgott 1312.7748v2 page 51, the bounds from RS62 Theorems 12 and 13
giving the quantity E of 6.10, followed by page 63 equation 7.26 with x at least
4.9e26: the sum of Lambda of n squared times eta plus of n over x squared over n
non-prime or n at most root x is at most 8.4031e-12 x, MEDIUM. -/
theorem helfgott_E_bound (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2)) ≤
      8.4031e-12 * LeanLab.Helfgott2013.xOf N := by
  sorry

/-- LEAF: Helfgott 1312.7748v2 page 63, the display before 7.27, from 7.16 and 7.20:
S eta star at zero is at most root pi over 2 plus 1.9075e-8, times x over kappa, MEDIUM. -/
theorem helfgott_Sstar_zero_upper (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
        LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2 LeanLab.HelfgottArcs.etaT2
          (49 * (n / LeanLab.Helfgott2013.xOf N))) ≤
      (Real.sqrt (Real.pi / 2) + 1.9075e-8) * LeanLab.Helfgott2013.xOf N /
        LeanLab.Helfgott2013.κ := by
  sorry

/-- LEAF: Helfgott 1312.7748v2 pages 51 and 52, Proposition 6.2 applied with
Corollary 5.7 and the minor arc bound 6.16, giving 6.19, so that the weighted
integral of the square of S one is at most the L1 norm root pi over 2 of phi times
x over kappa times M plus T, with M at most 0.77962 x by the repaired 7.47, book
1501.05438 page 274, and T at most 3.5776e-4 x by page 63 equation 7.30, HARD. -/
theorem helfgott_minor_large_prime_part (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖LeanLab.HelfgottArcs.S
          (fun t => LeanLab.HelfgottArcs.mconv LeanLab.HelfgottArcs.eta2
            LeanLab.HelfgottArcs.etaT2 (49 * t)) α (LeanLab.Helfgott2013.xOf N)‖ *
        ‖∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * LeanLab.HelfgottArcs.e (α * n) *
              (LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) : ℂ)
          else 0)‖ ^ 2) ≤
      Real.sqrt (Real.pi / 2) * LeanLab.Helfgott2013.xOf N *
        (0.77962 * LeanLab.Helfgott2013.xOf N + 3.5776e-4 * LeanLab.Helfgott2013.xOf N) /
          LeanLab.Helfgott2013.κ := by
  sorry

/-- The product of the two page 63 bounds is the 7.27 bound 1.0532e-11 x squared
over kappa. Helfgott 1312.7748v2 page 63 equation 7.27. -/
theorem helfgott_727_arith {x A B : ℝ} (hx : 0 ≤ x) (hB0 : 0 ≤ B)
    (hA : A ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / LeanLab.Helfgott2013.κ)
    (hB : B ≤ 8.4031e-12 * x) :
    A * B ≤ 1.0532e-11 * x ^ 2 / LeanLab.Helfgott2013.κ := by
  have hs := LeanLab.Helfgott2013.sqrt_pi_half_lt
  have hs0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hk : LeanLab.Helfgott2013.κ = 49 := rfl
  rw [hk] at hA ⊢
  have hU0 : 0 ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / 49 := by positivity
  have h1 : A * B ≤ (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / 49 * (8.4031e-12 * x) :=
    mul_le_mul hA hB hB0 hU0
  refine h1.trans ?_
  have : (Real.sqrt (Real.pi / 2) + 1.9075e-8) * 8.4031e-12 ≤ (1.0532e-11 : ℝ) := by
    nlinarith
  have hx2 : 0 ≤ x ^ 2 / 49 := by positivity
  have e1 : (Real.sqrt (Real.pi / 2) + 1.9075e-8) * x / 49 * (8.4031e-12 * x) =
      ((Real.sqrt (Real.pi / 2) + 1.9075e-8) * 8.4031e-12) * (x ^ 2 / 49) := by ring
  have e2 : 1.0532e-11 * x ^ 2 / 49 = 1.0532e-11 * (x ^ 2 / 49) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right this hx2

/-- The leaf helfgott_theorem63_minor_inputs from the page 50 to 52 steps of the
proof of Theorem 6.3 and the section 7.3 inputs 7.26, 7.27, 7.30 and repaired 7.47.
Helfgott 1312.7748v2 page 69 equation 7.48. -/
theorem helfgott_theorem63_minor_inputs_of_leaves (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    ∃ M T P : ℝ, 0 ≤ M + T ∧ 0 ≤ P ∧
      M ≤ 0.77962 * LeanLab.Helfgott2013.xOf N ∧
      T ≤ 3.5776e-4 * LeanLab.Helfgott2013.xOf N ∧
      P ≤ 1.0532e-11 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ∧
      (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖helfgottIntegrand N α‖) ≤
        (Real.sqrt (Real.sqrt (Real.pi / 2) * LeanLab.Helfgott2013.xOf N * (M + T) /
            LeanLab.Helfgott2013.κ) + Real.sqrt P) ^ 2 := by
  have hx : 0 ≤ LeanLab.Helfgott2013.xOf N := by
    unfold LeanLab.Helfgott2013.xOf LeanLab.Helfgott2013.ratio
    positivity
  have hk0 : (0 : ℝ) < LeanLab.Helfgott2013.κ := by
    unfold LeanLab.Helfgott2013.κ; norm_num
  have hTri := helfgott_minor_weighted_triangle N hN
  have hPar := helfgott_minor_small_part_parseval N hN
  have hE := helfgott_E_bound N hN
  have hS0 := helfgott_Sstar_zero_upper N hN
  have hLarge := helfgott_minor_large_prime_part N hN
  have hE0 : 0 ≤ (∑' n : ℕ, (if n.Prime ∧ Real.sqrt (LeanLab.Helfgott2013.xOf N) < n then 0 else
      (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
        LeanLab.HelfgottArcs.etaPlus (n / LeanLab.Helfgott2013.xOf N) ^ 2)) := by
    apply tsum_nonneg
    intro n
    split_ifs
    · exact le_refl 0
    · positivity
  have hSmall := hPar.trans (helfgott_727_arith hx hE0 hS0 hE)
  refine ⟨0.77962 * LeanLab.Helfgott2013.xOf N, 3.5776e-4 * LeanLab.Helfgott2013.xOf N,
    1.0532e-11 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ,
    by positivity, by positivity, le_refl _, le_refl _, le_refl _, ?_⟩
  refine hTri.trans ?_
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add (Real.sqrt_le_sqrt hLarge) (Real.sqrt_le_sqrt hSmall)

end LeanLab.Ternary.Task420
