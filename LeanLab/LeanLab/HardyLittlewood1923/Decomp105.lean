/-
AI wrote this Lean code for CODEX task105.
P0004 Theorem A, page 21 equation 3.113, ternary case.
The assembly has no proof hole. Its unfinished leaves remain explicit.
Binary Goldbach is OPEN.
-/
import LeanLab.HardyLittlewood1923.U1503Endpoint

set_option maxHeartbeats 1000000

namespace LeanLab.HardyLittlewood1923.Decomp105

open Real Finset
open LeanLab.HardyLittlewood1923.U1438
open LeanLab.HardyLittlewood1923.U1444
open LeanLab.HardyLittlewood1923.U1463
open LeanLab.HardyLittlewood1923.U1468
open LeanLab.HardyLittlewood1923.U1503 (psiPowerLog_of_noZeros)

/-- The finite main term in P0004 page 26 equation 3.156 at r equal to three. -/
noncomputable def finiteMain (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / 2 * ∑ q ∈ Icc 1 (Nat.sqrt n), singTerm n q

/-- LEAF. P0004 page 4, the classical existence input to its functional equation argument.
External source: Landau Handbuch page 489 and the classical theory of zeta zeros. -/
theorem exists_nonreal_zeta_zero :
    ∃ ρ : ℂ, ρ.im ≠ 0 ∧ riemannZeta ρ = 0 := by
  sorry

/-- The elementary functional equation argument on P0004 page 4.
Any nonreal zeta zero and its reflection force Theta to be at least one half. -/
theorem theta_lower_bound_of_complex_zero {Θ : ℝ} (hZ : NoZerosRight Θ)
    {ρ : ℂ} (hi : ρ.im ≠ 0) (hρ : riemannZeta ρ = 0) : 1 / 2 ≤ Θ := by
  have hne1 : ρ ≠ 1 := by
    intro h
    exact hi (by simp [h])
  have hne0 : ρ ≠ 0 := by
    intro h
    exact hi (by simp [h])
  have hneg (n : ℕ) : ρ ≠ -(n : ℂ) := by
    intro h
    exact hi (by simp [h])
  have href : riemannZeta (1 - ρ) = 0 := by
    rw [riemannZeta_one_sub hneg hne1, hρ, mul_zero]
  have hr1 : ρ.re ≤ Θ := by
    apply le_of_not_gt
    intro hlt
    have h := hZ 1 (1 : DirichletCharacter ℂ 1) ρ hlt hne1
    rw [DirichletCharacter.LFunction_modOne_eq, hρ] at h
    exact h rfl
  have hr2 : (1 - ρ).re ≤ Θ := by
    apply le_of_not_gt
    intro hlt
    have hrne : 1 - ρ ≠ 1 := by
      intro h
      exact hne0 (by linear_combination -h)
    have h := hZ 1 (1 : DirichletCharacter ℂ 1) (1 - ρ) hlt hrne
    rw [DirichletCharacter.LFunction_modOne_eq, href] at h
    exact h rfl
  simp only [Complex.sub_re, Complex.one_re] at hr2
  linarith

/-- LEAF. P0004 page 4, the lower bound on Theta.
The functional equation step is proved. Classical zero existence remains explicit. -/
theorem theta_lower_bound {Θ : ℝ} (hZ : NoZerosRight Θ) : 1 / 2 ≤ Θ := by
  obtain ⟨ρ, hi, hρ⟩ := exists_nonreal_zeta_zero
  exact theta_lower_bound_of_complex_zero hZ hi hρ

/-- LEAF. P0004 page 26 section 3.16.
A sufficient tail bound at the target exponent, using the lab's uniform
absolute tail bound. The paper proves a stronger tail estimate. -/
theorem tail_at_target {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) :
    ∃ C : ℝ, ∀ n : ℕ, 4 ≤ n →
      |finiteMain n - (n : ℝ) ^ 2 / 2 * sing3 n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by
  refine ⟨Real.exp 8, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hQ : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hQ0 : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  have hQ1 : (1 : ℝ) ≤ Nat.sqrt n := by exact_mod_cast (by omega : 1 ≤ Nat.sqrt n)
  have hQs : 0 < Real.sqrt (Nat.sqrt n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < Nat.sqrt n))
  have hnQ : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' n
  have hnQ' : (n : ℝ) ≤ 4 * (Nat.sqrt n : ℝ) ^ 2 := by nlinarith
  have hs : Real.sqrt n ≤ 2 * (Nat.sqrt n : ℝ) := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hss : Real.sqrt (Real.sqrt n) ≤ 2 * Real.sqrt (Nat.sqrt n) := by
    have hsq := Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))
    have hsqQ := Real.sq_sqrt hQ0
    nlinarith [Real.sqrt_nonneg (Real.sqrt (n : ℝ)), Real.sqrt_nonneg (Nat.sqrt n : ℝ)]
  have hid : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [hid] at hss
  have hp : (n : ℝ) ^ 2 = (n : ℝ) ^ (7 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have htail := abs_partial_sub_sing3 n (Q := Nat.sqrt n) (by omega)
  rw [finiteMain, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 2 / 2)]
  calc (n : ℝ) ^ 2 / 2 * |∑ q ∈ Icc 1 (Nat.sqrt n), singTerm n q - sing3 n|
      ≤ (n : ℝ) ^ 2 / 2 * (Real.exp 8 / Real.sqrt (Nat.sqrt n)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = Real.exp 8 * (n : ℝ) ^ (7 / 4 : ℝ) *
        ((n : ℝ) ^ (1 / 4 : ℝ) / (2 * Real.sqrt (Nat.sqrt n))) := by rw [hp]; ring
    _ ≤ Real.exp 8 * (n : ℝ) ^ (7 / 4 : ℝ) :=
      mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).mpr hss)
    _ ≤ Real.exp 8 * (n : ℝ) ^ (2 + (Θ - 3 / 4)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (Real.exp_pos 8).le

/-- The finite approximation on the range already proved by U1503.
P0004 page 26 equation 3.156, obtained by adding the proved tail. -/
theorem finite_approximation_upper {Θ : ℝ} (hΘ0 : 47 / 64 ≤ Θ) (hΘ1 : Θ < 3 / 4)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  obtain ⟨B, C, n₀, hfull⟩ :=
    U1503.printedA_form_all_U1503_closed 3 (by omega) Θ hΘ0 hΘ1 hZ
  norm_num [singR_three] at hfull
  obtain ⟨D, htail⟩ := tail_at_target (Θ := Θ) (by linarith)
  refine ⟨B, |C| + |D|, max n₀ 4, fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hlog : 1 ≤ Real.log n := U1463.one_le_log_of_three (by omega)
  have hlogB : 1 ≤ Real.log n ^ B := one_le_pow₀ hlog
  have hx : 0 ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by positivity
  have hf := hfull n hn0
  have ht := htail n hn4
  have ht' : |(n : ℝ) ^ 2 / 2 * sing3 n - finiteMain n| ≤
      D * (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by rwa [abs_sub_comm] at ht
  have hca : C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B ≤
      |C| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
    gcongr
    exact le_abs_self C
  have hda : D * (n : ℝ) ^ (2 + (Θ - 3 / 4)) ≤
      |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
    calc D * (n : ℝ) ^ (2 + (Θ - 3 / 4)) ≤
        |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) := mul_le_mul_of_nonneg_right (le_abs_self D) hx
      _ ≤ |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B :=
        le_mul_of_one_le_right (mul_nonneg (abs_nonneg D) hx) hlogB
  have htri := abs_add_le (nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n)
    ((n : ℝ) ^ 2 / 2 * sing3 n - finiteMain n)
  calc |nur 3 n - finiteMain n|
      ≤ |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n| +
          |(n : ℝ) ^ 2 / 2 * sing3 n - finiteMain n| := by
        convert htri using 1 <;> congr 1 <;> ring
    _ ≤ (|C| + |D|) * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
      nlinarith only [hf, ht', hca, hda]

/-- LEAF. P0004 pages 22 to 26 equations 3.115 to 3.156.
The remaining lower range of the finite Farey approximation.
The paper writes its proof here, with no additional outside input. -/
theorem finite_approximation_lower {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 47 / 64)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  sorry

/-- LEAF. P0004 pages 22 to 26, equations 3.115 to 3.156.
The Farey dissection gives the finite singular series with the printed error.
This is the remaining analytic leaf, including the rational arc estimates. -/
theorem finite_approximation {Θ : ℝ} (hΘ0 : 1 / 2 ≤ Θ) (hΘ1 : Θ < 3 / 4)
    (hZ : NoZerosRight Θ) :
    ∃ B : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |nur 3 n - finiteMain n| ≤
        C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
  by_cases h47 : 47 / 64 ≤ Θ
  · exact finite_approximation_upper h47 hΘ1 hZ
  · exact finite_approximation_lower hΘ0 (lt_of_not_ge h47) hZ

/-- P0004 page 21 equation 3.113, exactly the lab's cited ternary Prop.
The three leaves assemble without a proof hole in this proof. -/
theorem printedA3 : printedA3_stmt := by
  intro Θ hΘ1 hZ
  have hΘ0 := theta_lower_bound hZ
  obtain ⟨B, C, n₀, hfin⟩ := finite_approximation hΘ0 hΘ1 hZ
  obtain ⟨D, htail⟩ := tail_at_target hΘ0
  refine ⟨B, by positivity, |C| + |D|, max n₀ 4, fun n hn => ?_⟩
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn3 : 3 ≤ n := by omega
  have hlog : 1 ≤ Real.log n := U1463.one_le_log_of_three hn3
  have hlogB : 1 ≤ Real.log n ^ B := one_le_pow₀ hlog
  have hx : 0 ≤ (n : ℝ) ^ (2 + (Θ - 3 / 4)) := by positivity
  have hL : 0 ≤ Real.log n ^ B := by positivity
  have hf := hfin n hn0
  have ht := htail n hn4
  have htri := abs_add_le (nur 3 n - finiteMain n)
    (finiteMain n - (n : ℝ) ^ 2 / 2 * sing3 n)
  have hca : C * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B ≤
      |C| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
    gcongr
    exact le_abs_self C
  have hda : D * (n : ℝ) ^ (2 + (Θ - 3 / 4)) ≤
      |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
    calc D * (n : ℝ) ^ (2 + (Θ - 3 / 4)) ≤
        |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) := mul_le_mul_of_nonneg_right (le_abs_self D) hx
      _ ≤ |D| * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B :=
        le_mul_of_one_le_right (mul_nonneg (abs_nonneg D) hx) hlogB
  rw [Real.rpow_natCast]
  calc |nur 3 n - (n : ℝ) ^ 2 / 2 * sing3 n|
      ≤ |nur 3 n - finiteMain n| + |finiteMain n - (n : ℝ) ^ 2 / 2 * sing3 n| := by
        convert htri using 1 <;> congr 1 <;> ring
    _ ≤ (|C| + |D|) * (n : ℝ) ^ (2 + (Θ - 3 / 4)) * Real.log n ^ B := by
      nlinarith only [hf, ht, hca, hda]

/-- P0004 page 21 equation 3.113, exactly the lab's cited Prop for every r at least three.
The established recursion extends the ternary leaf assembly to all r.
This remains CONDITIONAL on the unfinished leaves of printedA3. -/
theorem printedA_all (r : ℕ) (hr : 3 ≤ r) : printedA_stmt r := by
  intro Θ h1 hZ
  have h0 := theta_lower_bound hZ
  set θ := Θ + 1 / 128 with hθ
  have hψ := psiPowerLog_of_noZeros (by linarith) (by linarith) hZ (θ := θ) (by rw [hθ]; linarith)
  obtain ⟨B₀, hA⟩ : ∃ B : ℕ, APow r (Θ - 3 / 4) B :=
    apow_all (θ := θ) (by rw [hθ]; linarith) (by rw [hθ]; linarith) hψ
      (apow_three_of_bound (printedA3 Θ h1 hZ)) r hr
  obtain ⟨K, hK, n₀, hn⟩ := apow_mono (le_max_left B₀ r) hA
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  refine ⟨(max B₀ (s + 2) : ℕ), by positivity,
    K + 3 * (s + 2) * 2 ^ s, max n₀ 3, fun n hn' => ?_⟩
  rw [Real.rpow_natCast]
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hL1 := one_le_log_of_three hn3
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) := by positivity
  have hZ0 : 0 ≤ Real.log n ^ max B₀ (s + 2) := by positivity
  by_cases hpar : n % 2 = (s + 2) % 2
  · rw [← Mr_eq_printed_pos hr (by omega) hpar]
    refine (hn n hpar (le_trans (le_max_left _ _) hn')).trans ?_
    have : 0 ≤ 3 * (s + 2 : ℝ) * 2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    nlinarith
  · rw [(singRProductPos (s + 2) hr n (by omega)).2 hpar, mul_zero, sub_zero,
      abs_of_nonneg (nur_nonneg _ _)]
    refine (nur_unlike_le s n hpar).trans ?_
    have q1 : ((n : ℝ) + 1) ^ s ≤ 2 ^ s * (n : ℝ) ^ s := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) s
    have q2 : (n : ℝ) ^ s ≤ (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) :=
      npow_le_rpow (by omega) (by push_cast; linarith)
    have q3 : Real.log n ^ (s + 2) ≤ Real.log n ^ max B₀ (s + 2) :=
      log_pow_mono hn3 (le_max_right _ _)
    have hKY : 0 ≤ K * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
        Real.log n ^ max B₀ (s + 2) := by positivity
    calc 3 * ((s : ℝ) + 2) * ((n : ℝ) + 1) ^ s * Real.log n ^ (s + 2)
        ≤ 3 * ((s : ℝ) + 2) * (2 ^ s * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4))) *
            Real.log n ^ max B₀ (s + 2) := by
          gcongr
          exact q1.trans (mul_le_mul_of_nonneg_left q2 (by positivity))
      _ ≤ (K + 3 * (s + 2) * 2 ^ s) * (n : ℝ) ^ (((s + 2 : ℕ) : ℝ) - 1 + (Θ - 3 / 4)) *
            Real.log n ^ max B₀ (s + 2) := by
          linarith only [hKY]


#print axioms printedA_all
#print axioms exists_nonreal_zeta_zero
#print axioms theta_lower_bound_of_complex_zero
#print axioms theta_lower_bound
#print axioms tail_at_target
#print axioms finite_approximation_upper
#print axioms finite_approximation_lower
#print axioms finite_approximation
#print axioms printedA3

end LeanLab.HardyLittlewood1923.Decomp105
