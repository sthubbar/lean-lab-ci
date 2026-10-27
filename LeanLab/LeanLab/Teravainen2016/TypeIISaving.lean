/-
P0076 Section 11, displays 11.5 and 11.6, pages 46 to 47.
Elementary power saving from the stated type II parameter conditions.
The exponential sum estimate itself remains a cited input.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.SieveRight

open Filter Asymptotics
open scoped Topology

namespace LeanLab.Teravainen2016

/-- The four parameter conditions in display 11.6. -/
def TypeIIConditions (N M D₁ D₂ θ ε : ℝ) : Prop :=
  D₁ ≤ N ^ (1 - 2 * θ - ε ^ 2) / M ∧
  D₁ * D₂ ^ 2 ≤ M * N ^ (-2 * θ - ε ^ 2) ∧
  N ^ ((1 : ℝ) / 10) ≤ D₁ ∧ θ ≤ 1 / 80 - ε

/-- The type II bound in display 11.5 without the logarithmic factor. -/
noncomputable def typeIIKernel (N R M D₁ D₂ : ℝ) : ℝ :=
  R * N * ((D₁ * M / N + D₁ * D₂ ^ 2 / M) ^ ((1 : ℝ) / 2) +
    (1 / D₁ + 1 / N ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 8))

/-- A sum of two bounded nonnegative terms has a simple fractional power bound. -/
theorem rpow_sum_two_le {N x y a p : ℝ} (hN : 0 < N) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxa : x ≤ N ^ a) (hya : y ≤ N ^ a) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (x + y) ^ p ≤ 2 * N ^ (a * p) := by
  have hs : x + y ≤ 2 * N ^ a := by linarith
  calc
    _ ≤ (2 * N ^ a) ^ p := Real.rpow_le_rpow (add_nonneg hx hy) hs hp
    _ = (2 : ℝ) ^ p * N ^ (a * p) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1

/-- The first two conditions give the two small quantities inside the square root. -/
theorem typeII_energy_conditions {N M D₁ D₂ θ ε : ℝ} (hN : 0 < N) (hM : 0 < M)
    (h : TypeIIConditions N M D₁ D₂ θ ε) :
    D₁ * M / N ≤ N ^ (-2 * θ - ε ^ 2) ∧ D₁ * D₂ ^ 2 / M ≤ N ^ (-2 * θ - ε ^ 2) := by
  constructor
  · have hh := (le_div_iff₀ hM).mp h.1
    rw [div_le_iff₀ hN]
    have he : N ^ (1 - 2 * θ - ε ^ 2) = N ^ (-2 * θ - ε ^ 2) * N := by
      rw [← Real.rpow_add_one hN.ne']
      congr 1
      ring
    rwa [he] at hh
  · exact (div_le_iff₀ hM).mpr (by simpa [mul_comm] using h.2.1)

/-- A lower power bound on the first parameter gives the inverse bound. -/
theorem typeII_inverse_bound {N D₁ : ℝ} (hN : 0 < N) (hD : N ^ ((1 : ℝ) / 10) ≤ D₁) :
    1 / D₁ ≤ N ^ (-(1 : ℝ) / 10) := by
  have h := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN ((1 : ℝ) / 10)) hD
  rw [show (-(1 : ℝ) / 10) = -((1 : ℝ) / 10) by ring, Real.rpow_neg hN.le]
  simpa only [one_div] using h

/-- A useful cancellation of the Fourier scale and the saved power. -/
theorem rpow_scale_cancel {N : ℝ} (hN : 0 < N) (θ a : ℝ) :
    N ^ θ * N * N ^ a = N ^ (1 + θ + a) := by
  calc
    _ = N ^ θ * N ^ (1 : ℝ) * N ^ a := by rw [Real.rpow_one]
    _ = N ^ (θ + 1 + a) := by rw [Real.rpow_add hN, Real.rpow_add hN]
    _ = _ := by congr 1; ring

/-- The polynomial part of display 11.5 saves epsilon squared over two. -/
theorem typeII_kernel_saving {N R M D₁ D₂ θ ε : ℝ} (hN : 1 ≤ N) (hM : 0 < M)
    (hR0 : 0 ≤ R) (hR : R ≤ N ^ θ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : TypeIIConditions N M D₁ D₂ θ ε) :
    typeIIKernel N R M D₁ D₂ ≤ 4 * N ^ (1 - ε ^ 2 / 2) := by
  have hN0 : 0 < N := by linarith
  have hD : 0 < D₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h.2.2.1
  obtain ⟨he1, he2⟩ := typeII_energy_conditions hN0 hM h
  have hf := rpow_sum_two_le hN0 (by positivity : 0 ≤ D₁ * M / N)
    (by positivity : 0 ≤ D₁ * D₂ ^ 2 / M) he1 he2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1)
  have hf' : (D₁ * M / N + D₁ * D₂ ^ 2 / M) ^ ((1 : ℝ) / 2) ≤
      2 * N ^ (-θ - ε ^ 2 / 2) := by convert hf using 1 <;> congr 2 <;> ring
  have hi1 := typeII_inverse_bound hN0 h.2.2.1
  have hi2 : 1 / N ^ ((1 : ℝ) / 2) ≤ N ^ (-(1 : ℝ) / 10) := by
    rw [one_div, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have ht := rpow_sum_two_le hN0 (by positivity : 0 ≤ 1 / D₁)
    (by positivity : 0 ≤ 1 / N ^ ((1 : ℝ) / 2)) hi1 hi2 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 : ℝ) / 8 ≤ 1)
  have ht' : (1 / D₁ + 1 / N ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 8) ≤
      2 * N ^ (-(1 : ℝ) / 80) := by convert ht using 1 <;> congr 2 <;> norm_num
  have hpow : N ^ (1 + θ - 1 / 80) ≤ N ^ (1 - ε ^ 2 / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith [h.2.2.2]
  unfold typeIIKernel
  calc
    _ ≤ (N ^ θ * N) * (2 * N ^ (-θ - ε ^ 2 / 2) + 2 * N ^ (-(1 : ℝ) / 80)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hR hN0.le) (add_le_add hf' ht')
        (by positivity) (by positivity)
    _ = 2 * N ^ (1 - ε ^ 2 / 2) + 2 * N ^ (1 + θ - 1 / 80) := by
      calc
        _ = 2 * (N ^ θ * N * N ^ (-θ - ε ^ 2 / 2)) +
            2 * (N ^ θ * N * N ^ (-(1 : ℝ) / 80)) := by ring
        _ = _ := by rw [rpow_scale_cancel hN0, rpow_scale_cancel hN0]; congr 2 <;> congr 1 <;> ring
    _ ≤ 4 * N ^ (1 - ε ^ 2 / 2) := by linarith

/-- Every fixed logarithm power is eventually smaller than a positive real power. -/
theorem eventually_log_pow_le_rpow (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℝ in atTop, (Real.log N) ^ k ≤ N ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with N hN hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hNr : 0 ≤ N := by linarith
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog k),
    abs_of_nonneg (Real.rpow_nonneg hNr s), one_mul] using hN

/-- The full logarithmic factor is absorbed with the saving printed after display 11.6. -/
theorem typeII_logarithmic_saving {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₀ : ℝ, ∀ N R M D₁ D₂ θ : ℝ, N₀ ≤ N → 0 < M → 0 ≤ R → R ≤ N ^ θ →
      TypeIIConditions N M D₁ D₂ θ ε →
      (Real.log N) ^ 1000 * typeIIKernel N R M D₁ D₂ ≤ 4 * N ^ (1 - ε ^ 2 / 10) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_log_pow_le_rpow 1000
    (show 0 < 2 * ε ^ 2 / 5 by positivity))
  refine ⟨max 1 A, ?_⟩
  intro N R M D₁ D₂ θ hN hM hR0 hR hcond
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hlog := hA N ((le_max_right _ _).trans hN)
  have hD : 0 < D₁ := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hcond.2.2.1
  have hker := typeII_kernel_saving hN1 hM hR0 hR hε hε1 hcond
  calc
    _ ≤ N ^ (2 * ε ^ 2 / 5) * (4 * N ^ (1 - ε ^ 2 / 2)) := by
      apply mul_le_mul hlog hker (by unfold typeIIKernel; positivity) (by positivity)
    _ = 4 * N ^ (1 - ε ^ 2 / 10) := by
      rw [show N ^ (2 * ε ^ 2 / 5) * (4 * N ^ (1 - ε ^ 2 / 2)) =
        4 * (N ^ (2 * ε ^ 2 / 5) * N ^ (1 - ε ^ 2 / 2)) by ring,
        ← Real.rpow_add hN0]
      congr 2
      ring

#print axioms rpow_sum_two_le
#print axioms typeII_energy_conditions
#print axioms typeII_inverse_bound
#print axioms rpow_scale_cancel
#print axioms typeII_kernel_saving
#print axioms eventually_log_pow_le_rpow
#print axioms typeII_logarithmic_saving

end LeanLab.Teravainen2016
