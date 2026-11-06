import LeanLab.HardyLittlewood1923.Decomp448c
import LeanLab.HardyLittlewood1923.Decomp448d
import LeanLab.HardyLittlewood1923.Decomp448e
import LeanLab.HardyLittlewood1923.Decomp415d

/-!
AI wrote this Lean code for CODEX task448.
P0004 pages 19 to 26 equations 2.823 and 3.121 to 3.156.
The analytic assemblies are CONDITIONAL on the primitive character leaf.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp448f

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.Decomp105
open LeanLab.HardyLittlewood1923.Decomp276a
open LeanLab.HardyLittlewood1923.Decomp276b
open LeanLab.HardyLittlewood1923.Decomp276c

open LeanLab.HardyLittlewood1923.Decomp415c

/-- P0004 page 19 equation 2.823 and page 21 averaging.
CONDITIONAL on the primitive character and prime correction leaves. -/
theorem lemma9_on_circle {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          C * (Real.sqrt q * ((q : ℝ) + Real.sqrt n) + angularTerm Θ n q θ) *
            Real.log ((q : ℝ) + 1) ^ A := by
  obtain ⟨A, C, hC, hc⟩ := Decomp448e.prime_character_reduction
  obtain ⟨B, D, hD, hd⟩ := Decomp448d.weighted_character_bound hΘ0 hΘ1 hZ
  refine ⟨A + B, (C + D) * (Real.log 2)⁻¹ ^ (A + B), by positivity,
    4, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  haveI : NeZero q := ⟨by omega⟩
  have hnpos : 0 < n := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ q + 1))
  have hlog0 : 0 ≤ Real.log ((q : ℝ) + 1) := hlog2.le.trans hlog
  have hlog2_le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hscale : 1 ≤ (Real.log 2)⁻¹ := (one_le_inv₀ hlog2).mpr hlog2_le
  have hprod : 1 ≤ (Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1) := by
    rw [← div_eq_inv_mul]
    exact (one_le_div hlog2).mpr hlog
  have hA : Real.log ((q : ℝ) + 1) ^ A ≤
      (Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B) := by
    calc
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ A := by
        gcongr
        exact le_mul_of_one_le_left hlog0 hscale
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ (A + B) :=
        pow_le_pow_right₀ hprod (by omega)
      _ = _ := by rw [mul_pow]
  have hB : Real.log ((q : ℝ) + 1) ^ B ≤
      (Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B) := by
    calc
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ B := by
        gcongr
        exact le_mul_of_one_le_left hlog0 hscale
      _ ≤ ((Real.log 2)⁻¹ * Real.log ((q : ℝ) + 1)) ^ (A + B) :=
        pow_le_pow_right₀ hprod (by omega)
      _ = _ := by rw [mul_pow]
  have he0 := characterEnvelope_nonneg Θ hnpos θ
  have hav := average_character_bound hq θ (hd n hn q hq hqN p hp hpq θ hθ)
  have hr := hc n hn q hq hqN p hp hpq θ hθ
  have heq : angularTerm Θ n q θ = Real.sqrt q * characterEnvelope Θ n θ := by
    unfold angularTerm characterEnvelope
    ring
  rw [heq]
  calc
    _ ≤ Real.sqrt q * (D * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
          Real.log ((q : ℝ) + 1) ^ B) +
        C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) * Real.log ((q : ℝ) + 1) ^ A :=
      hr.trans (add_le_add hav le_rfl)
    _ ≤ Real.sqrt q * (D * ((q : ℝ) + Real.sqrt n + characterEnvelope Θ n θ) *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B))) +
        C * Real.sqrt q * ((q : ℝ) + Real.sqrt n) *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hB (by positivity)
      · exact mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ _ := by
      have hnonneg : 0 ≤ C * Real.sqrt q * characterEnvelope Θ n θ *
          ((Real.log 2)⁻¹ ^ (A + B) * Real.log ((q : ℝ) + 1) ^ (A + B)) := by positivity
      nlinarith only [hnonneg]

/-- P0004 page 23 equation 3.121.
CONDITIONAL on the two analytic leaves. The old target head is preserved exactly. -/
theorem preliminary_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤
          C * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ) * Real.log n ^ A := by
  obtain ⟨A, C, hC, n₀, hc⟩ := Decomp448f.lemma9_on_circle hΘ0 hΘ1 hZ
  refine ⟨A, 2 * C, by positivity, max n₀ 4, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hlog0 : 0 ≤ Real.log ((q : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) q])
  have hlog : Real.log ((q : ℝ) + 1) ≤ Real.log n := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by have := Nat.sqrt_lt_self (by omega : 1 < n); omega : q + 1 ≤ n)
  have hterm : 0 ≤ angularTerm Θ n q θ := by
    unfold angularTerm
    have hg := angularGap_pos (by omega : 0 < n) θ
    have hl : 0 ≤ Real.log (1 / angularGap n θ + 2) :=
      Real.log_nonneg (by
        have : 0 < 1 / angularGap n θ := by positivity
        linarith)
    positivity
  have hpoly := Decomp354c.polynomial_arc_factor hqN
  calc
    _ ≤ C * (Real.sqrt q * ((q : ℝ) + Real.sqrt n) + angularTerm Θ n q θ) *
          Real.log ((q : ℝ) + 1) ^ A := hc n hn0 q hq hqN p hp hpq θ hθ
    _ ≤ C * (2 * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ)) * Real.log n ^ A := by
      apply mul_le_mul _ (pow_le_pow_left₀ hlog0 hlog A) (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _ = _ := by ring


/-- P0004 page 23 equation 3.124.
CONDITIONAL on the two analytic leaves. The old target head is preserved exactly. -/
theorem uniform_arc_error {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by
  obtain ⟨A, C, hC, n₀, hc⟩ := preliminary_arc_error hΘ0 hΘ1 hZ
  obtain ⟨D, hD, hd⟩ := Decomp354d.angular_small hΘ0 hΘ1
  obtain ⟨E, hE, he⟩ := Decomp354e.angular_large hΘ0 hΘ1
  refine ⟨A + 1, C * (1 + D + E), max n₀ 4, fun n hn q hq hqN p hp hpq θ hθ => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hl : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hx : 0 ≤ (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by positivity
  have ha : angularTerm Θ n q θ ≤ (D + E) * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
    by_cases hs : |θ| ≤ 1 / (n : ℝ)
    · have h := hd n hn4 q hq hqN θ hs
      nlinarith only [h, mul_nonneg hE hx]
    · have h := he n hn4 q hq hqN p hp hpq θ hθ (lt_of_not_ge hs)
      nlinarith only [h, mul_nonneg hD hx]
  have hpw : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
    calc _ ≤ (n : ℝ) ^ (Θ + 1 / 4) :=
           Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
         _ ≤ _ := le_mul_of_one_le_right (by positivity) hl
  have hsum : (n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ ≤
      (1 + D + E) * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n := by
    nlinarith only [hpw, ha]
  calc _ ≤ C * ((n : ℝ) ^ (3 / 4 : ℝ) + angularTerm Θ n q θ) * Real.log n ^ A :=
           hc n hn0 q hq hqN p hp hpq θ hθ
       _ ≤ C * ((1 + D + E) * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n) * Real.log n ^ A :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hC) (by positivity)
       _ = _ := by rw [pow_succ]; ring


/-- P0004 page 24 and 25 equations 3.141 and 3.142.
CONDITIONAL on the supplied uniform bound. The target head is exact. -/
theorem coefficient_error_of_uniform {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hE : ∃ A : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ q : ℕ, 1 ≤ q → q ≤ Nat.sqrt n → ∀ p : ℕ, p < q → p.Coprime q →
      ∀ θ : ℝ, θ ∈ Set.Icc (arcLeft (Nat.sqrt n) p q) (arcRight (Nat.sqrt n) p q) →
        ‖localError n p q θ‖ ≤ C * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  obtain ⟨A, C, n₀, hc⟩ := hE
  obtain ⟨P, hP, hp⟩ := Decomp448b.primeSeries_square_mean
  obtain ⟨Q, hQ, hq⟩ := Decomp296SquareMean.localPhi_square_mean
  let K : ℝ := 3 * Real.exp 1 / (4 * π)
  refine ⟨A + 1, K * |C| * (P + Q), max n₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl : 0 ≤ Real.log n := (U1463.one_le_log_of_three (by omega)).trans' (by norm_num)
  have hk : 0 ≤ K := by dsimp [K]; positivity
  have he : 0 ≤ |C| * (n : ℝ) ^ (Θ + 1 / 4) * Real.log n ^ A := by positivity
  have hb := Decomp448c.coefficient_transfer hn4 he (fun q hq1 hqN p hpq hcop θ hθ =>
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
CONDITIONAL on the two analytic task448 leaves. The old target head is preserved exactly. -/
theorem coefficient_to_farey {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ‖(nur 3 n : ℂ) - fareyModel n‖ ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact coefficient_error_of_uniform hΘ0 hΘ1
    (uniform_arc_error hΘ0 hΘ1 hZ)


/-- P0004 page 26 equation 3.156.
CONDITIONAL on the two analytic task448 leaves. The old target head is preserved exactly. -/
theorem finite_approximation_lower {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  exact Decomp354i.finite_approximation_of_farey hΘ0 (coefficient_to_farey hΘ0 hΘ1 hZ)

#print axioms lemma9_on_circle
#print axioms preliminary_arc_error
#print axioms uniform_arc_error
#print axioms coefficient_error_of_uniform
#print axioms coefficient_to_farey
#print axioms finite_approximation_lower

end LeanLab.HardyLittlewood1923.Decomp448f
