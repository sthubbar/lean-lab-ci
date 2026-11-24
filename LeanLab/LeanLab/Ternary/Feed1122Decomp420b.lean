/-
Feed split of helfgott_minor_norm_integral_upper from Decomp420b.
Helfgott https://arxiv.org/abs/1312.7748v2, section 7.3, page 69, equation 7.48:
Theorem 6.3 bounds the minor arc integral by the square of a sum of two roots,
and the inputs M, T and the product of S at zero with E are bounded in 7.47,
the T display and the E display, with the book 1501.05438 page 274 correction
of f zero that turns 0.77671 into 0.77962. The arithmetic is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420b

namespace LeanLab.Ternary.Task420
open Finset MeasureTheory

/-- LEAF: Helfgott 1312.7748v2 page 69 equation 7.48, the application of Theorem 6.3
with the repaired section 7.3 inputs, HARD for Codex. With x the scale xOf N,
the minor arc integral of the Fourier norm is at most the Theorem 6.3 bound
square of root of the L1 norm root pi over 2 times x times M plus T over kappa,
plus root of P, where P is S of eta star at zero times E, and the inputs obey
M at most 0.77962 x by the repaired 7.47, T at most 3.5776e-4 x, and
P at most 1.0532e-11 x squared over kappa. This is a cited published input. -/
theorem helfgott_theorem63_minor_inputs (N : ℕ) (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    ∃ M T P : ℝ, 0 ≤ M + T ∧ 0 ≤ P ∧
      M ≤ 0.77962 * LeanLab.Helfgott2013.xOf N ∧
      T ≤ 3.5776e-4 * LeanLab.Helfgott2013.xOf N ∧
      P ≤ 1.0532e-11 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ ∧
      (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
        ‖helfgottIntegrand N α‖) ≤
        (Real.sqrt (Real.sqrt (Real.pi / 2) * LeanLab.Helfgott2013.xOf N * (M + T) /
            LeanLab.Helfgott2013.κ) + Real.sqrt P) ^ 2 := by
  sorry

/-- The repaired 7.48 arithmetic in the Theorem 6.3 form: with M at most 0.77962 x,
T at most 3.5776e-4 x and P at most 1.0532e-11 x squared over kappa, the bound is
at most 0.97757 x squared over kappa. Helfgott page 69 equation 7.48 with the
book 1501.05438 page 274 correction, proved by the method of SectionSeven.minor_total. -/
theorem repaired_minor_total_scaled {x M T P : ℝ} (hx : 0 ≤ x) (hMT : 0 ≤ M + T)
    (hM : M ≤ 0.77962 * x) (hT : T ≤ 3.5776e-4 * x) (hP0 : 0 ≤ P)
    (hP : P ≤ 1.0532e-11 * x ^ 2 / LeanLab.Helfgott2013.κ) :
    (Real.sqrt (Real.sqrt (Real.pi / 2) * x * (M + T) / LeanLab.Helfgott2013.κ) +
        Real.sqrt P) ^ 2 ≤ 0.97757 * x ^ 2 / LeanLab.Helfgott2013.κ := by
  have hs := LeanLab.Helfgott2013.sqrt_pi_half_lt
  have hs0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hk0 : (0 : ℝ) < LeanLab.Helfgott2013.κ := by
    unfold LeanLab.Helfgott2013.κ; norm_num
  set y := x / 7 with hy
  have hy0 : 0 ≤ y := by positivity
  have hk : x ^ 2 / LeanLab.Helfgott2013.κ = y ^ 2 := by
    rw [hy]; unfold LeanLab.Helfgott2013.κ; ring
  set A := Real.sqrt (Real.sqrt (Real.pi / 2) * x * (M + T) / LeanLab.Helfgott2013.κ) with hA
  set B := Real.sqrt P with hB
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA2 : A ^ 2 ≤ 0.988717 ^ 2 * y ^ 2 := by
    rw [hA, Real.sq_sqrt (by positivity)]
    have hMT' : M + T ≤ (0.77962 + 3.5776e-4) * x := by linarith
    have h1 : Real.sqrt (Real.pi / 2) * x * (M + T) ≤
        Real.sqrt (Real.pi / 2) * x * ((0.77962 + 3.5776e-4) * x) :=
      mul_le_mul_of_nonneg_left hMT' (mul_nonneg hs0 hx)
    have h2 : Real.sqrt (Real.pi / 2) * x * (M + T) / LeanLab.Helfgott2013.κ ≤
        Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4) * (x ^ 2 / LeanLab.Helfgott2013.κ) := by
      rw [div_le_iff₀ hk0]
      have : Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4) *
          (x ^ 2 / LeanLab.Helfgott2013.κ) * LeanLab.Helfgott2013.κ =
          Real.sqrt (Real.pi / 2) * x * ((0.77962 + 3.5776e-4) * x) := by
        field_simp
      linarith
    rw [hk] at h2
    have hc : Real.sqrt (Real.pi / 2) * (0.77962 + 3.5776e-4) ≤ (0.988717 : ℝ) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg y]
  have hB2 : B ^ 2 ≤ 3.2454e-6 ^ 2 * y ^ 2 := by
    rw [hB, Real.sq_sqrt hP0]
    have : (1.0532e-11 : ℝ) * x ^ 2 / LeanLab.Helfgott2013.κ =
        1.0532e-11 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by ring
    rw [this, hk] at hP
    nlinarith [sq_nonneg y]
  have hA' : A ≤ 0.988717 * y := by
    by_contra h; push_neg at h; nlinarith
  have hB' : B ≤ 3.2454e-6 * y := by
    by_contra h; push_neg at h; nlinarith
  have hsum : A + B ≤ (0.988717 + 3.2454e-6) * y := by linarith
  have hsq : (A + B) ^ 2 ≤ ((0.988717 + 3.2454e-6) * y) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  have hgoal : 0.97757 * x ^ 2 / LeanLab.Helfgott2013.κ =
      0.97757 * (x ^ 2 / LeanLab.Helfgott2013.κ) := by ring
  rw [hgoal, hk]
  nlinarith [sq_nonneg y]

/-- The exact minor arc leaf of Decomp420b from the cited Theorem 6.3 application.
Helfgott page 69 equation 7.48, repaired. CONDITIONAL ON helfgott_theorem63_minor_inputs. -/
theorem helfgott_minor_norm_integral_upper_of_leaves (N : ℕ)
    (hN : (10 : ℝ) ^ (27 : ℕ) ≤ N) :
    (∫ α in Set.Ioc (0 : ℝ) 1 \ helfgottMajorArcs (LeanLab.Helfgott2013.xOf N),
      ‖helfgottIntegrand N α‖) ≤
        0.97757 * LeanLab.Helfgott2013.xOf N ^ 2 / LeanLab.Helfgott2013.κ := by
  obtain ⟨M, T, P, hMT, hP0, hM, hT, hP, hI⟩ := helfgott_theorem63_minor_inputs N hN
  have hx : 0 ≤ LeanLab.Helfgott2013.xOf N := by
    unfold LeanLab.Helfgott2013.xOf LeanLab.Helfgott2013.ratio
    positivity
  exact hI.trans (repaired_minor_total_scaled hx hMT hM hT hP0 hP)

end LeanLab.Ternary.Task420
