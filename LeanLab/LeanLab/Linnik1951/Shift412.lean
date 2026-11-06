/-
P0093 page 165 proof of Lemma 5. Quantitative local stability.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Stability412

namespace LeanLab.Linnik1951

/-- P0093 page 165 proof of Lemma 5, local phase variation.
The distance between two unit complex phases is at most the angle difference. -/
theorem phase_difference412 (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have he : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
      Complex.exp ((y : ℂ) * Complex.I) *
        (Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm Complex.I, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- P0093 page 165 proof of Lemma 5, the quantitative local variation
behind the shift by Delta. The derivative majorant gives constant twenty pi. -/
theorem power_shift_bound412 (N : ℕ) (hN : 1 ≤ N) (α ξ : ℝ) :
    ‖powerFourier111 N (α + ξ) - powerFourier111 N α‖ ≤
      20 * Real.pi * N * |ξ| := by
  let a : ℕ → ℝ := fun m => ((2 ^ (m + 1) : ℕ) : ℝ) *
    Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  let f : ℝ → ℕ → ℂ := fun β m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * β * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hd : Summable (fun m => f (α + ξ) m - f α m) :=
    (power_fourier_summable111 N hN (α + ξ)).sub (power_fourier_summable111 N hN α)
  have hterm (m : ℕ) : ‖f (α + ξ) m - f α m‖ ≤ (2 * Real.pi * |ξ|) * a m := by
    dsimp [f, a]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hp := phase_difference412 (-(2 * Real.pi * (α + ξ) * (2 ^ (m + 1) : ℕ)))
      (-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)))
    have he : -(2 * Real.pi * (α + ξ) * ((2 ^ (m + 1) : ℕ) : ℝ)) -
        -(2 * Real.pi * α * ((2 ^ (m + 1) : ℕ) : ℝ)) =
          -(2 * Real.pi * ξ * ((2 ^ (m + 1) : ℕ) : ℝ)) := by ring
    rw [he, abs_neg, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (2 ^ (m + 1) : ℕ))] at hp
    calc
      _ ≤ Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) *
          (2 * Real.pi * |ξ| * ((2 ^ (m + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = _ := by ring
  change ‖(∑' m, f (α + ξ) m) - ∑' m, f α m‖ ≤ _
  rw [← (power_fourier_summable111 N hN (α + ξ)).tsum_sub
    (power_fourier_summable111 N hN α)]
  calc
    _ ≤ ∑' m, ‖f (α + ξ) m - f α m‖ := norm_tsum_le_tsum_norm hd.norm
    _ ≤ ∑' m, (2 * Real.pi * |ξ|) * a m :=
      Summable.tsum_le_tsum hterm hd.norm ((weighted_power_summable412 N hN).mul_left _)
    _ = (2 * Real.pi * |ξ|) * ∑' m, a m := tsum_mul_left
    _ ≤ (2 * Real.pi * |ξ|) * (10 * N) :=
      mul_le_mul_of_nonneg_left (weighted_power_bound412 N hN) (by positivity)
    _ = _ := by ring

/-- P0093 page 165 proof of Lemma 5. The first positive term gives a
uniform lower bound for the value at zero for every positive N. -/
theorem power_zero_lower412 (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-2) ≤ ‖powerFourier111 N 0‖ := by
  let a : ℕ → ℝ := fun m => Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N)
  have hi : Function.Injective (fun m : ℕ => 2 ^ (m + 1)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))).comp (add_left_injective 1)
  have ha : Summable a := (damping_summable111 N hN).comp_injective hi
  have heq : powerFourier111 N 0 = ((∑' m, a m : ℝ) : ℂ) := by
    unfold powerFourier111
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    simp [a]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg (fun m => (Real.exp_pos _).le))]
  calc
    _ ≤ a 0 := by
      apply Real.exp_le_exp.mpr
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNp : (0 : ℝ) < N := by positivity
      dsimp [a]
      norm_num
      apply (le_div_iff₀ hNp).mpr
      nlinarith
    _ ≤ ∑' m, a m := ha.le_tsum 0 (fun m hm => (Real.exp_pos _).le)

/-- P0093 page 165 proof of Lemma 5, the displays for xi and Delta.
Exact large_value_stability412 statement with a clean quantitative proof. -/
theorem large_value_stability_proved412 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ α ξ : ℝ,
      |ξ| ≤ 1 / ((N : ℝ) * Real.log N) →
      (1 - η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N α‖ →
      (1 - 2 * η) * ‖powerFourier111 N 0‖ < ‖powerFourier111 N (α + ξ)‖ := by
  obtain ⟨N0, hN0⟩ := exists_nat_gt (Real.exp (20 * Real.pi / (η * Real.exp (-2)) + 1))
  refine ⟨max 2 N0, ?_⟩
  intro N hN α ξ hξ hlarge
  have h2 : 2 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNN : N0 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 20 * Real.pi / (η * Real.exp (-2)) < Real.log N := by
    have hNR : (N0 : ℝ) < N := by exact_mod_cast hNN
    have h := Real.log_le_log (Real.exp_pos _) (hN0.trans hNR).le
    rw [Real.log_exp] at h
    linarith
  have hlp : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall : 20 * Real.pi / Real.log N < η * Real.exp (-2) := by
    apply (div_lt_iff₀ hlp).mpr
    have h := (div_lt_iff₀ (mul_pos hη (Real.exp_pos _))).mp hlog
    nlinarith
  have hdiff : ‖powerFourier111 N (α + ξ) - powerFourier111 N α‖ <
      η * ‖powerFourier111 N 0‖ := by
    calc
      _ ≤ 20 * Real.pi * N * |ξ| := power_shift_bound412 N (by omega) α ξ
      _ ≤ 20 * Real.pi * N * (1 / ((N : ℝ) * Real.log N)) :=
        mul_le_mul_of_nonneg_left hξ (by positivity)
      _ = 20 * Real.pi / Real.log N := by field_simp
      _ < η * Real.exp (-2) := hsmall
      _ ≤ _ := mul_le_mul_of_nonneg_left (power_zero_lower412 N (by omega)) hη.le
  have htri := norm_sub_norm_le (powerFourier111 N α) (powerFourier111 N (α + ξ))
  rw [norm_sub_rev] at hdiff
  nlinarith

end LeanLab.Linnik1951
