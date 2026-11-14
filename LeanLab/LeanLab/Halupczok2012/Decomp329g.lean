import LeanLab.Halupczok2012.Decomp329f
import LeanLab.Halupczok2012.Decomp329b

/-!
Fixed exponent analytic supply for the sealed Wu leaf.
Source: Halupczok page 345 and Wu arXiv 0705.1652 pages 5, 34, 38 and 42.
The sole new open leaf concerns only windows of length X to 0.971.
The restriction at 3 comes from the rough sieve support in the written weight proof.
The unrestricted statement of Theorem 5 alone does not give that restriction.
The weight parameter adaptation remains a recorded QUESTION.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329g

open scoped Classical

/-- The part excluded at 3 consists exactly of three times a prime, above 3.
This is an arithmetic description of the extra restriction on Halupczok page 345. -/
theorem isp_two_dvd_three_iff {n : ℕ} (hn : 3 < n) :
    (IsP 2 n ∧ 3 ∣ n) ↔ ∃ q : ℕ, q.Prime ∧ n = 3 * q := by
  constructor
  · rintro ⟨hP, q, rfl⟩
    have hq : 1 < q := by omega
    have hcount := hP.2
    rw [ArithmeticFunction.cardFactors_mul (by decide) (by omega),
      ArithmeticFunction.cardFactors_apply_prime (by decide : Nat.Prime 3)] at hcount
    have hpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hq
    exact ⟨q, ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega), rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨isP_mul (isP_prime (by decide : Nat.Prime 3)) (isP_prime hq),
      dvd_mul_right 3 q⟩

/-- The unrestricted Chen count splits into the sealed rough count and the
prime shifts of the form three times a prime. No distribution estimate is used. -/
theorem chen_count_split {X : ℝ} (hX : 3 ≤ X) (Y : ℝ) :
    ((kRange X Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2))).card =
      ((kRange X Y).filter
        (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card +
      ((kRange X Y).filter
        (fun p => p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p + 2 = 3 * q)).card := by
  let s := (kRange X Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2))
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s) (fun p => ¬ 3 ∣ (p + 2))
  have hgood : s.filter (fun p => ¬ 3 ∣ (p + 2)) =
      (kRange X Y).filter
        (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) := by
    ext p
    simp [s, and_assoc]
  have hbad : s.filter (fun p => ¬ ¬ 3 ∣ (p + 2)) =
      (kRange X Y).filter
        (fun p => p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p + 2 = 3 * q) := by
    ext p
    by_cases hp : p ∈ kRange X Y
    · have hplo := ((Fourier398.window_mem _ _ _).mp hp).1
      have hpn : 3 < p + 2 := by
        have : (3 : ℝ) < p := hX.trans_lt hplo
        have : 3 < p := by exact_mod_cast this
        omega
      simp only [Finset.mem_filter, s, hp, true_and, not_not]
      rw [and_assoc, isp_two_dvd_three_iff hpn]
    · simp [s, hp]
  rw [hgood, hbad] at hsplit
  exact hsplit.symm

/-- A lower bound for all Chen candidates and an upper bound for the excluded
three-times-prime candidates give the required rough count by subtraction. -/
theorem rough_count_lower_of_subtraction {X Y A B : ℝ} (hX : 3 ≤ X)
    (hall : A ≤
      (((kRange X Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2))).card : ℝ))
    (hbad :
      (((kRange X Y).filter
        (fun p => p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p + 2 = 3 * q)).card : ℝ) ≤ B) :
    A - B ≤
      (((kRange X Y).filter
        (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card : ℝ) := by
  have hsplit := chen_count_split hX Y
  have hsplitR := congrArg (fun n : ℕ => (n : ℝ)) hsplit
  push_cast at hsplitR
  linarith

/-- LEAF. Halupczok page 345, Wu arXiv page 5 Theorem 5 at theta 0.971.
Use the rough sieved contribution in the proof on pages 34, 38 and 42.
Only the one power length X to 0.971 is counted, with denominator log X squared.
The full range in Y and its logarithm conversion are proved in Decomp329f.
The restricted rough count and the printed parameter adaptation are not formalized here. -/
theorem fixed_wu_rough_count_leaf :
    ∃ c > 0, ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → 2 ≤ X →
      c * X ^ (0.971 : ℝ) / (Real.log X) ^ 2 ≤
        (((kRange X (X ^ (0.971 : ℝ))).filter
          (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card : ℝ) := by
  sorry

/-- Halupczok page 345, the exact sealed Wu statement from the fixed exponent leaf.
This assembly has no sorry of its own and remains conditional on that open leaf. -/
theorem wu_supply :
  ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
    c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) (Classical.decPred _) (kRange X Y)).card := Decomp329f.wu_of_fixed_power_count fixed_wu_rough_count_leaf

/-- Halupczok pages 345 to 346, the exact sealed assembly statement.
Only Corollary2 and the fixed exponent leaf are inputs to this supply. -/
theorem corollary_3_supply (hCor2 : Corollary2) : Corollary3 :=
  Decomp329b.corollary3_of_inputs hCor2 wu_supply

end LeanLab.Halupczok2012.Decomp329g
