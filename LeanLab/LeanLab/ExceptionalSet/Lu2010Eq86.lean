/-
P0095 Lu 2010, equation 63 on page 2379 and equation 86 on page 2392.
CODEX task47, unit U-8091. AI wrote this Lean code. Binary Goldbach is open.

The integer-window part of the equation 86 argument, for rational Fourier sums.
Identifying the coefficients with equation 63 and bounding their energy remain open.
-/
import LeanLab.ExceptionalSet.Lu2010Dirichlet
import LeanLab.PNTPort.LargeSieve.Farey

namespace LeanLab.ExceptionalSet.Lu2010Eq86
open Finset Real
open LeanLab.PNTPort.LargeSieve
open LeanLab.ExceptionalSet.Lu2010Assembly

/-- A finite rational Fourier sum with denominators at most Q. -/
noncomputable def rationalSum (Q : ℕ) (B : ℕ × ℕ → ℂ) (k : ℤ) : ℂ :=
  ∑ p ∈ farey Q, B p * e (-(k : ℝ) * fareyPt p)

/-- The dual large sieve with the negative exponential sign of equation 63. -/
theorem rationalSum_Ioc {Q : ℕ} (hQ : 1 ≤ Q) (B : ℕ × ℕ → ℂ)
    (M : ℤ) (L : ℕ) :
    ∑ k ∈ Ioc M (M + L), ‖rationalSum Q B k‖ ^ 2 ≤
      (L + 2 * (Q : ℝ) ^ 2) * ∑ p ∈ farey Q, ‖B p‖ ^ 2 := by
  have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hs : Spaced (farey Q) (fun p => -fareyPt p) (1 / (Q : ℝ) ^ 2) := by
    intro p hp p' hp' hne
    rw [show -fareyPt p - -fareyPt p' = -(fareyPt p - fareyPt p') by ring, dist0_neg]
    exact farey_spaced Q p hp p' hp' hne
  have h := dual_large_sieve hδ hs B M L
  have he : ∀ k : ℤ, dualSum (farey Q) (fun p => -fareyPt p) B k = rationalSum Q B k := by
    intro k
    unfold dualSum rationalSum
    apply sum_congr rfl
    intro p _
    congr 2
    ring
  simp_rw [he] at h
  convert h using 1
  field_simp

/-- The dual large sieve on a natural-number interval, including a zero left endpoint. -/
theorem rationalSum_Icc {Q A B : ℕ} (hQ : 1 ≤ Q) (hAB : A ≤ B)
    (coeff : ℕ × ℕ → ℂ) :
    ∑ k ∈ Icc A B, ‖rationalSum Q coeff (k : ℤ)‖ ^ 2 ≤
      ((B + 1 - A : ℕ) + 2 * (Q : ℝ) ^ 2) * ∑ p ∈ farey Q, ‖coeff p‖ ^ 2 := by
  have he : (A : ℤ) - 1 + (B + 1 - A : ℕ) = B := by omega
  have hs : (∑ k ∈ Icc A B, ‖rationalSum Q coeff (k : ℤ)‖ ^ 2) =
      ∑ k ∈ Ioc ((A : ℤ) - 1) (B : ℤ), ‖rationalSum Q coeff k‖ ^ 2 := by
    apply sum_nbij (fun k : ℕ => (k : ℤ))
    · intro k hk
      simp only [mem_Icc, mem_Ioc] at hk ⊢
      omega
    · intro k hk k' hk' heq
      change (k : ℤ) = (k' : ℤ) at heq
      exact_mod_cast heq
    · intro k hk
      have hk := Finset.mem_Ioc.mp (Finset.mem_coe.mp hk)
      refine ⟨k.toNat, ?_, ?_⟩
      · apply Finset.mem_coe.mpr
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · change (k.toNat : ℤ) = k
        omega
    · intro k _
      rfl
  rw [hs]
  simpa only [he] using rationalSum_Ioc hQ coeff ((A : ℤ) - 1) (B + 1 - A)

/-- The Lemma 1 window loses at most its length plus the Farey spacing error. -/
theorem rationalSum_window {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) (B : ℕ × ℕ → ℂ) :
    ∑ k ∈ Win N, ‖rationalSum Q B (k : ℤ)‖ ^ 2 ≤
      ((2 * rad N + 1 : ℕ) + 2 * (Q : ℝ) ^ 2) * ∑ p ∈ farey Q, ‖B p‖ ^ 2 := by
  have hAB : N - rad N ≤ N + rad N := by omega
  have h := rationalSum_Icc hQ hAB B
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  have hn : N + rad N + 1 - (N - rad N) ≤ 2 * rad N + 1 := by omega
  have hnr : ((N + rad N + 1 - (N - rad N) : ℕ) : ℝ) ≤
      (2 * rad N + 1 : ℕ) := by exact_mod_cast hn
  linarith

/-- The Farey spacing cost is absorbed by the paper's d, even before taking a limit. -/
theorem spacing_cost {N : ℕ} (hN : 1 ≤ N) :
    ((2 * rad N + 1 : ℕ) : ℝ) + 2 * (⌊PP N⌋₊ : ℝ) ^ 2 ≤ 5 * dd N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hd1 : 1 ≤ dd N := Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 0.9999)
  have hr : (rad N : ℝ) ≤ dd N := by
    refine (Nat.floor_le (by positivity : 0 ≤ dd N * (N : ℝ) ^ (-0.00011 : ℝ))).trans ?_
    have hsmall : (N : ℝ) ^ (-0.00011 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
    exact (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans_eq (mul_one _)
  have hP0 : 0 ≤ PP N := by unfold PP; positivity
  have hq : (⌊PP N⌋₊ : ℝ) ≤ PP N := Nat.floor_le hP0
  have hq2 : (⌊PP N⌋₊ : ℝ) ^ 2 ≤ dd N := by
    calc (⌊PP N⌋₊ : ℝ) ^ 2 ≤ (PP N) ^ 2 := by gcongr
      _ = (N : ℝ) ^ (2 * c) := by
        unfold PP
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ dd N := Real.rpow_le_rpow_of_exponent_le hN1 (by unfold c; norm_num)
  push_cast
  linarith

/-- Equation 86 for a rational Fourier sum, conditional on its coefficient energy estimate. -/
theorem eq86_of_coefficient_energy {N : ℕ} (hN : 1 ≤ N) (B : ℕ × ℕ → ℂ) {C : ℝ}
    (hE : ∑ p ∈ farey ⌊PP N⌋₊, ‖B p‖ ^ 2 ≤
      C * PP N ^ (-1 : ℝ) * (N : ℝ) ^ (2.0003 : ℝ)) :
    ∑ k ∈ Win N, ‖rationalSum ⌊PP N⌋₊ B (k : ℤ)‖ ^ 2 ≤
      (5 * C) * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ : 1 ≤ ⌊PP N⌋₊ := Nat.one_le_floor_iff _ |>.2
    (Real.one_le_rpow hN1 (by unfold c; norm_num))
  calc (∑ k ∈ Win N, ‖rationalSum ⌊PP N⌋₊ B (k : ℤ)‖ ^ 2)
      ≤ (((2 * rad N + 1 : ℕ) : ℝ) + 2 * (⌊PP N⌋₊ : ℝ) ^ 2) *
          ∑ p ∈ farey ⌊PP N⌋₊, ‖B p‖ ^ 2 := rationalSum_window hQ N B
    _ ≤ (5 * dd N) * ∑ p ∈ farey ⌊PP N⌋₊, ‖B p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (spacing_cost hN) (sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (5 * dd N) * (C * PP N ^ (-1 : ℝ) * (N : ℝ) ^ (2.0003 : ℝ)) :=
      mul_le_mul_of_nonneg_left hE (by unfold dd; positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Lu2010Eq86

#print axioms LeanLab.ExceptionalSet.Lu2010Eq86.rationalSum_Ioc
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86.rationalSum_Icc
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86.rationalSum_window
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86.spacing_cost
#print axioms LeanLab.ExceptionalSet.Lu2010Eq86.eq86_of_coefficient_energy
