import LeanLab.HardyLittlewood1923.Decomp354f
import LeanLab.HardyLittlewood1923.Decomp296SquareMean
import LeanLab.HardyLittlewood1923.Decomp296Transfer

/-!
AI wrote this Lean code for CODEX task354.
P0004 pages 22 to 25 equations 3.115 to 3.142.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354b

open Real Finset MeasureTheory
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b

/-- LEAF. P0004 page 24 equation 3.141.
The prime generating function has total square mean of order n log n.
This is Parseval and the prime coefficient estimate on the disjoint Farey arcs.
It has no approximation error or zero free hypothesis. -/
theorem primeSeries_square_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n →
      (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
        ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
          ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) ≤
            C * n * Real.log n := by
  sorry

/-- LEAF. P0004 page 22 equations 3.115 to 3.119 and page 25 equation 3.142.
Cubic coefficient extraction and Farey dissection transfer a finite uniform error
through the two actual square means. The multiplier is the cubic difference
constant times exp of one divided by two pi. This is a finite n identity estimate,
with no asymptotic exponent and no zero free hypothesis. -/
theorem coefficient_transfer {n : ℕ} (hn : 4 ≤ n) {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ E) :
    ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
      (3 * Real.exp 1 / (4 * π)) * E *
        ((∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
          ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ^ 2) +
         (∑ q ∈ Icc 1 (Nat.sqrt n), ∑ p ∈ (range q).filter (fun p => p.Coprime q),
          ∫ θ in arcLeft (Nat.sqrt n) p q..arcRight (Nat.sqrt n) p q,
            ‖localPhi n q θ‖ ^ 2)) := by
  sorry

/-- P0004 pages 22 to 25 equations 3.119, 3.131, 3.141 and 3.142.
The exact transfer target follows from the two smaller OPEN leaves and the
proved rational square mean. CONDITIONAL on primeSeries_square_mean and
coefficient_transfer. -/
theorem coefficient_error_of_uniform {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hE : ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  obtain ⟨A, C, n₀, hc⟩ := hE
  obtain ⟨P, hP, hp⟩ := primeSeries_square_mean
  obtain ⟨Q, hQ, hq⟩ := Decomp296SquareMean.localPhi_square_mean
  let K : ℝ := 3 * Real.exp 1 / (4 * π)
  refine ⟨A + 1, K * |C| * (P + Q), max n₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 ≤ Real.log n := (U1463.one_le_log_of_three (by omega)).trans' (by norm_num)
  have hk : 0 ≤ K := by dsimp [K]; positivity
  have he : 0 ≤ |C| * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by positivity
  have hb := coefficient_transfer hn4 he (fun q hq1 hqN p hpq hcop θ hθ =>
    (hc n hn0 q hq1 hqN p hpq hcop θ hθ).trans
      (by gcongr; exact le_abs_self C))
  have hm := add_le_add (hp n hn4) (hq n hn4)
  have hexp : (n : ℝ) ^ (Θ + 1 / 4) * n = (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by
    conv_lhs => arg 2; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  calc
    _ ≤ K * (|C| * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A) *
        (P * n * Real.log n + Q * n * Real.log n) :=
      hb.trans (mul_le_mul_of_nonneg_left hm (mul_nonneg hk he))
    _ = K * |C| * (P + Q) * ((n : ℝ) ^ (Θ + 1 / 4) * n) *
        (Real.log n ^ A * Real.log n) := by ring
    _ = _ := by rw [hexp, ← pow_succ]

/-- P0004 page 25 equation 3.142.
The exact coefficient to Farey target uses the angular estimate and the new
square mean decomposition. CONDITIONAL on the named OPEN leaves. -/
theorem coefficient_to_farey {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact coefficient_error_of_uniform hΘ0 hΘ1
    (Decomp354f.uniform_arc_error hΘ0 hΘ1 hZ)

#print axioms primeSeries_square_mean
#print axioms coefficient_transfer
#print axioms coefficient_error_of_uniform
#print axioms coefficient_to_farey

end LeanLab.HardyLittlewood1923.Decomp354b
