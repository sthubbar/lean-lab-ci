/-
Split of `prop52_farey_le_parseval`, burst-20261122 session S144 wave 2.
Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, page 35, last display:
the Farey arcs do not overlap modulo 1, so their integrals sum to at most the integral of
`|S|²` over `R/Z`, and that integral equals `Σ |a_n|²`. The second step, finite Parseval,
is PROVED here from the lab theorem `charSeries_parseval`; the first stays a LEAF.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp580aP2

namespace LeanLab.Ternary.Task580
open MeasureTheory

/-- The squared norm of the finite exponential sum has period one. -/
theorem finset_expSum_norm_sq_periodic (A : Finset ℕ) (a : ℕ → ℂ) :
    Function.Periodic
      (fun α : ℝ => ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) 1 := by
  intro α
  apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have he : Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * (n : ℂ) =
      (n : ℂ) * (2 * Real.pi * Complex.I) by ring, Complex.exp_nat_mul,
      Complex.exp_two_pi_mul_I]
    simp
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((α + 1 : ℝ) : ℂ) * n =
    2 * Real.pi * Complex.I * α * n + 2 * Real.pi * Complex.I * n by push_cast; ring,
    Complex.exp_add, he, mul_one]

/-- LEAF: Helfgott 1312.7748v2 page 35, the non overlap of the intervals
`(b/q − δ₀Q/2qx, b/q + δ₀Q/2qx)` for odd `q ≤ Q` and `(b/q − δ₀Q/qx, b/q + δ₀Q/qx)` for even
`q ≤ 2Q` modulo 1, so the sum of the integrals of the 1 periodic function `|S|²` over these arcs
is at most its integral over one period. Class MEDIUM: it needs the separation
`|b/q − b'/q'| ≥ 1/qq'`, or `2/qq'` for two even denominators, against `Q² = x/2δ₀`, and
the translation of each arc into `(0, 1]` by periodicity of `e`. -/
theorem prop52_farey_arcs_le_circle (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ₀ : 1 ≤ Q₀) (hsize : δ * Q₀ ^ 2 ≤ x / 2) :
    (∑ q ∈ (Finset.Icc 1 ⌊Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Odd q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) +
        (∑ q ∈ (Finset.Icc 1 ⌊2 * Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Even q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) ≤
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2 := by
  classical
  have hp := finset_expSum_norm_sq_periodic A a
  sorry

/-- Finite Parseval on `(0, 1]` for a finite exponential sum, Helfgott 1312.7748v2 page 35,
last display, `∫_{R/Z} |S(α)|² dα = Σ |a_n|²`. PROVED from the lab theorem
`charSeries_parseval` applied to the coefficients cut off outside `A`. -/
theorem finset_expSum_parseval (A : Finset ℕ) (a : ℕ → ℂ) :
    (∫ α in Set.Ioc (0 : ℝ) 1, ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α)‖ ^ 2) =
      ∑ n ∈ A, ‖a n‖ ^ 2 := by
  classical
  set a' : ℕ → ℂ := fun n => if n ∈ A then a n else 0 with ha'
  have hsupp : ∀ n ∉ A, a' n = 0 := fun n hn => by simp [ha', hn]
  have hsum : Summable fun n => ‖a' n‖ :=
    summable_of_ne_finset_zero (s := A) (fun n hn => by simp [hsupp n hn])
  have hp := charSeries_parseval a' hsum
  have hser : ∀ α : ℝ, LeanLab.Ternary.Task420.charSeries a' α =
      ∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * α) := by
    intro α
    unfold LeanLab.Ternary.Task420.charSeries
    rw [tsum_eq_sum (s := A) (fun n hn => by simp [hsupp n hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [ha', hn])
  have hrhs : ∑' n, ‖a' n‖ ^ 2 = ∑ n ∈ A, ‖a n‖ ^ 2 := by
    rw [tsum_eq_sum (s := A) (fun n hn => by simp [hsupp n hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [ha', hn])
  simp only [hser] at hp
  rw [hp, hrhs]

/-- `prop52_farey_le_parseval`, statement copied verbatim, from the LEAF
`prop52_farey_arcs_le_circle` and the PROVED `finset_expSum_parseval`.
CONDITIONAL ON `prop52_farey_arcs_le_circle`. -/
theorem prop52_farey_le_parseval_of_leaves (A : Finset ℕ) (a : ℕ → ℂ) (x δ Q₀ : ℝ)
    (hx : 0 < x) (hδ : 1 ≤ δ) (hQ₀ : 1 ≤ Q₀) (hsize : δ * Q₀ ^ 2 ≤ x / 2) :
    (∑ q ∈ (Finset.Icc 1 ⌊Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Odd q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (2 * q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) +
        (∑ q ∈ (Finset.Icc 1 ⌊2 * Real.sqrt (x / (2 * δ))⌋₊).filter (fun q => Even q),
          ∫ α in (-(δ * Real.sqrt (x / (2 * δ)) / (q * x)))..
            (δ * Real.sqrt (x / (2 * δ)) / (q * x)),
            ∑ b ∈ (Finset.Icc 1 q).filter (fun b => Nat.Coprime b q),
              ‖∑ n ∈ A, a n * LeanLab.Ternary.MMS.e ((n : ℝ) * ((b : ℝ) / q + α))‖ ^ 2) ≤
      ∑ n ∈ A, ‖a n‖ ^ 2 := by
  have h := prop52_farey_arcs_le_circle A a x δ Q₀ hx hδ hQ₀ hsize
  rw [finset_expSum_parseval] at h
  exact h

end LeanLab.Ternary.Task580
