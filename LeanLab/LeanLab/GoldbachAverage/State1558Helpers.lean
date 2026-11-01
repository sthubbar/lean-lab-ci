import LeanLab.GoldbachAverage.OddSumPNT

/-!
# Chebyshev window mass for the State1558 large values route

The genuine bridge from Lemma 4 (Gallagher 1970 Theorem 7) to large values of `G`
averages over a window `[B + 1, 2B]` of length `B`.  This file proves the window mass
input: the von Mangoldt sum over that window is at least `B / 2` once `B` is large.

Source: the lab's PNT with error term `psi_div_log` in `OddSumPNT.lean`, in the form
`|psi x - x| <= A x / log x` for `2 <= x`.  AI wrote this Lean code.  Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.State1558Helpers

open Finset Real ArithmeticFunction

/-- The von Mangoldt mass of the window `(B, 2B]` is at least `B / 2` for large `B`.
This is the window input for the primorial averaging in P0050 pages 4 and 5. -/
theorem window_mass :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      (B : ℝ) / 2 ≤ ∑ n ∈ Icc (B + 1) (2 * B), (vonMangoldt n : ℝ) := by
  obtain ⟨A, hA, hpsi⟩ := psi_div_log
  refine ⟨Nat.ceil (Real.exp (8 * A)) + 2, fun B hB => ?_⟩
  have hB2n : (2 : ℕ) ≤ B := by omega
  have hB2 : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2n
  have hBge : Real.exp (8 * A) ≤ (B : ℝ) := by
    have h1 : Real.exp (8 * A) ≤ ((Nat.ceil (Real.exp (8 * A)) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp (8 * A)) : ℕ) : ℝ) + 2 ≤ (B : ℝ) := by
      exact_mod_cast hB
    linarith
  have hlog1 : 8 * A ≤ Real.log (B : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (8 * A)) hBge
    rwa [Real.log_exp] at h
  have hlog2 : 8 * A ≤ Real.log ((2 * B : ℕ) : ℝ) := by
    have hxl : (B : ℝ) ≤ ((2 * B : ℕ) : ℝ) := by push_cast; linarith
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (B : ℝ)) hxl
    linarith
  -- the two PNT bounds
  have hab2 : |Chebyshev.psi ((2 * B : ℕ) : ℝ) - ((2 * B : ℕ) : ℝ)|
      ≤ A * ((2 * B : ℕ) : ℝ) / Real.log ((2 * B : ℕ) : ℝ) :=
    hpsi _ (by exact_mod_cast (by omega : (2 : ℕ) ≤ 2 * B))
  have hab1 : |Chebyshev.psi ((B : ℕ) : ℝ) - (B : ℝ)|
      ≤ A * (B : ℝ) / Real.log (B : ℝ) := hpsi _ hB2
  have hlogpos2 : (0 : ℝ) < Real.log ((2 * B : ℕ) : ℝ) :=
    Real.log_pos (show (1 : ℝ) < ((2 * B : ℕ) : ℝ) by push_cast; linarith)
  have hlogpos1 : (0 : ℝ) < Real.log (B : ℝ) := Real.log_pos (by linarith)
  -- the error terms are small
  have e1 : A * ((2 * B : ℕ) : ℝ) / Real.log ((2 * B : ℕ) : ℝ) ≤ (B : ℝ) / 4 := by
    rw [div_le_iff₀ hlogpos2]
    have hmul := mul_le_mul_of_nonneg_left hlog2
      (show (0 : ℝ) ≤ (B : ℝ) / 4 by positivity)
    have hexp : (B : ℝ) / 4 * (8 * A) = A * ((2 * B : ℕ) : ℝ) := by
      push_cast; ring
    linarith
  have e2 : A * (B : ℝ) / Real.log (B : ℝ) ≤ (B : ℝ) / 8 := by
    rw [div_le_iff₀ hlogpos1]
    have hmul := mul_le_mul_of_nonneg_left hlog1
      (show (0 : ℝ) ≤ (B : ℝ) / 8 by positivity)
    have hexp : (B : ℝ) / 8 * (8 * A) = A * (B : ℝ) := by ring
    linarith
  -- the window sum equals psi(2B) - psi(B)
  have hpsi2B : Chebyshev.psi ((2 * B : ℕ) : ℝ)
      = ∑ n ∈ Icc 0 (2 * B), (vonMangoldt n : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hpsiB : Chebyshev.psi ((B : ℕ) : ℝ) = ∑ n ∈ Icc 0 B, (vonMangoldt n : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  have hunion : Icc (0 : ℕ) B ∪ Icc (B + 1) (2 * B) = Icc 0 (2 * B) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Icc (0 : ℕ) B) (Icc (B + 1) (2 * B)) := by
    rw [Finset.disjoint_right]
    intro x h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  have hmem : ∑ n ∈ Icc (B + 1) (2 * B), (vonMangoldt n : ℝ)
      = Chebyshev.psi ((2 * B : ℕ) : ℝ) - Chebyshev.psi ((B : ℕ) : ℝ) := by
    rw [hpsi2B, hpsiB]
    have h1 : ∑ n ∈ Icc 0 (2 * B), (vonMangoldt n : ℝ)
        = ∑ n ∈ Icc 0 B, (vonMangoldt n : ℝ)
          + ∑ n ∈ Icc (B + 1) (2 * B), (vonMangoldt n : ℝ) := by
      rw [← hunion, Finset.sum_union hdisj]
    linarith
  -- combine
  rw [hmem]
  have hlow : ((2 * B : ℕ) : ℝ) - A * ((2 * B : ℕ) : ℝ) / Real.log ((2 * B : ℕ) : ℝ)
      ≤ Chebyshev.psi ((2 * B : ℕ) : ℝ) := by
    have h := (abs_le.mp hab2).1
    linarith
  have hhigh : Chebyshev.psi ((B : ℕ) : ℝ)
      ≤ (B : ℝ) + A * (B : ℝ) / Real.log (B : ℝ) := by
    have h := (abs_le.mp hab1).2
    linarith
  have hrel : ((2 * B : ℕ) : ℝ) = 2 * (B : ℝ) := by push_cast; ring
  linarith [hrel]

end LeanLab.GoldbachAverage.State1558Helpers

#print axioms LeanLab.GoldbachAverage.State1558Helpers.window_mass
