/-
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Copy: papers/P0099.pdf.

Unit U-6737, session 20261020T1914Z-cloud49. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Contents, all PROVED with no cited input.
* `l2_identity`: the L2 identity behind the second part of (20), Lemma 6,
  ∫_0^1 (f_m^(m))^2 = (2m)! 4^m ∫_0^1 f_m, by m integrations by parts.
* `sq_integral_abs_le`: Cauchy-Schwarz on [0, 1], (∫|g|)^2 ≤ ∫ g^2.
* `muStar_le`: μ*_m(f_m) ≤ μ_m(f_m) = (2m+1)!/(m! √(2m+1)) for every m.
* `muStar48_upper`, `muStar55_upper`: the upper halves of `MuStar48Bounds` and
  `MuStar55Bounds`. The lower halves stay open.
-/
import Mathlib
import LeanLab.RamareSaouter2003.Theorem2Row59

namespace LeanLab.RamareSaouter2003.MuStarUpper
open Real Polynomial LeanLab.RamareSaouter2003.Smooth

/-- f_m as a polynomial: (-4)^m ((X - 0)(X - 1))^m. -/
noncomputable def F (m : ℕ) : ℝ[X] := C ((-4 : ℝ) ^ m) * ((X - C 0) * (X - C 1)) ^ m

theorem F_eval (m : ℕ) (t : ℝ) : (F m).eval t = fm m t := by
  simp only [F, eval_mul, eval_C, eval_pow, eval_sub, eval_X, fm]
  rw [← mul_pow]; ring_nf

theorem iteratedDeriv_eval (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [Polynomial.deriv, Function.iterate_succ_apply']

theorem iteratedDeriv_fm (m : ℕ) :
    iteratedDeriv m (fm m) = fun x => (derivative^[m] (F m)).eval x := by
  have : fm m = fun x => (F m).eval x := by funext x; rw [F_eval]
  rw [this, iteratedDeriv_eval]

/-- The derivatives of order below m vanish at 0 and 1. -/
theorem iter_eval_zero {m j : ℕ} (hj : j < m) (a : ℝ) (ha : a = 0 ∨ a = 1) :
    (derivative^[j] (F m)).eval a = 0 := by
  have hd : (X - C a) ^ m ∣ F m := by
    rcases ha with rfl | rfl
    · exact Dvd.intro_left (C ((-4 : ℝ) ^ m) * (X - C 1) ^ m) (by rw [F, mul_pow]; ring)
    · exact Dvd.intro_left (C ((-4 : ℝ) ^ m) * (X - C 0) ^ m) (by rw [F, mul_pow]; ring)
  have h2 := pow_sub_dvd_iterate_derivative_of_pow_dvd j hd
  have h3 : X - C a ∣ derivative^[j] (F m) :=
    (dvd_pow_self _ (by omega)).trans h2
  exact (dvd_iff_isRoot.mp h3)

theorem F_natDegree (m : ℕ) : (F m).natDegree ≤ 2 * m := by
  unfold F
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_pow_le).trans ?_
  have : ((X - C (0 : ℝ)) * (X - C 1)).natDegree ≤ 2 := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_X_sub_C, natDegree_X_sub_C]
  nlinarith

theorem F_coeff_top (m : ℕ) : (F m).coeff (2 * m) = (-4 : ℝ) ^ m := by
  have hmon : ((X - C (0 : ℝ)) * (X - C 1)).Monic := (monic_X_sub_C 0).mul (monic_X_sub_C 1)
  have hdeg : ((X - C (0 : ℝ)) * (X - C 1)).natDegree = 2 := by
    rw [(monic_X_sub_C 0).natDegree_mul (monic_X_sub_C 1), natDegree_X_sub_C, natDegree_X_sub_C]
  have hm2 := hmon.pow m
  have hd2 : (((X - C (0 : ℝ)) * (X - C 1)) ^ m).natDegree = 2 * m := by
    rw [hmon.natDegree_pow, hdeg]; ring
  rw [F, coeff_C_mul, ← hd2]
  have : (((X - C (0 : ℝ)) * (X - C 1)) ^ m).coeff
      (((X - C (0 : ℝ)) * (X - C 1)) ^ m).natDegree = 1 := hm2
  rw [this, mul_one]

theorem iter_top (m : ℕ) :
    derivative^[2 * m] (F m) = C ((Nat.factorial (2 * m) : ℝ) * (-4 : ℝ) ^ m) := by
  have hle : (derivative^[2 * m] (F m)).natDegree ≤ 0 := by
    refine (natDegree_iterate_derivative _ _).trans ?_
    have := F_natDegree m
    omega
  rw [eq_C_of_natDegree_le_zero hle, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    F_coeff_top, nsmul_eq_mul]

/-- One integration by parts for polynomials on [0, 1]. -/
theorem ibp (P Q : ℝ[X]) :
    ∫ x in (0 : ℝ)..1, P.eval x * (derivative Q).eval x =
      P.eval 1 * Q.eval 1 - P.eval 0 * Q.eval 0 -
        ∫ x in (0 : ℝ)..1, (derivative P).eval x * Q.eval x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => P.hasDerivAt x)
    (fun x _ => Q.hasDerivAt x) ((derivative P).continuous.intervalIntegrable _ _)
    ((derivative Q).continuous.intervalIntegrable _ _)

theorem ibp_iter (m : ℕ) : ∀ k, k ≤ m →
    ∫ x in (0 : ℝ)..1, (derivative^[m] (F m)).eval x * (derivative^[m] (F m)).eval x =
      (-1) ^ k * ∫ x in (0 : ℝ)..1,
        (derivative^[m - k] (F m)).eval x * (derivative^[m + k] (F m)).eval x := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [ih (by omega)]
    have e1 : m - k = (m - (k + 1)) + 1 := by omega
    have e2 : m + (k + 1) = (m + k) + 1 := by omega
    rw [e1, e2, Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := ibp (derivative^[m - (k + 1)] (F m)) (derivative^[m + k] (F m))
    rw [iter_eval_zero (by omega) 1 (Or.inr rfl), iter_eval_zero (by omega) 0 (Or.inl rfl)] at h
    rw [h, pow_succ]
    ring

/-- The L2 identity of (20): ∫_0^1 (f_m^(m))^2 = (2m)! 4^m ∫_0^1 f_m. PROVED. -/
theorem l2_identity (m : ℕ) :
    ∫ t in (0 : ℝ)..1, (iteratedDeriv m (fm m) t) ^ 2 =
      (Nat.factorial (2 * m) : ℝ) * 4 ^ m * ∫ t in (0 : ℝ)..1, fm m t := by
  rw [iteratedDeriv_fm]
  simp only [sq]
  rw [ibp_iter m m le_rfl, Nat.sub_self, Function.iterate_zero, id, ← two_mul, iter_top]
  simp only [eval_C]
  rw [intervalIntegral.integral_mul_const]
  simp only [F_eval]
  rw [show (4 : ℝ) ^ m = (-1) ^ m * (-4) ^ m by rw [← mul_pow]; norm_num]
  ring_nf

/-- Cauchy-Schwarz on [0, 1]: (∫|g|)^2 ≤ ∫ g^2 for continuous g. PROVED. -/
theorem sq_integral_abs_le (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, |g t|) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (g t) ^ 2 := by
  set c := ∫ t in (0 : ℝ)..1, |g t|
  have hpt : ∀ t, (|g t| - c) ^ 2 = (g t ^ 2 - 2 * c * |g t|) + c ^ 2 := by
    intro t; rw [sub_sq, sq_abs]; ring
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (|g t| - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => sq_nonneg _)
  simp_rw [hpt] at h0
  have i1 : IntervalIntegrable (fun t => g t ^ 2) MeasureTheory.volume 0 1 :=
    (hg.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => 2 * c * |g t|) MeasureTheory.volume 0 1 :=
    ((hg.abs).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) intervalIntegrable_const,
    intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul] at h0
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at h0
  nlinarith

/-- μ*_m(f_m) ≤ μ_m(f_m) = (2m+1)!/(m! √(2m+1)), for every m. PROVED. -/
theorem muStar_le (m : ℕ) :
    muStar m ≤ (Nat.factorial (2 * m + 1) : ℝ) / ((Nat.factorial m : ℝ) * √(2 * m + 1)) := by
  set A := ∫ t in (0 : ℝ)..1, |iteratedDeriv m (fm m) t|
  set B := ∫ t in (0 : ℝ)..1, fm m t
  set μ := (Nat.factorial (2 * m + 1) : ℝ) / ((Nat.factorial m : ℝ) * √(2 * m + 1))
  have hcont : Continuous (iteratedDeriv m (fm m)) := by
    rw [iteratedDeriv_fm]; exact (derivative^[m] (F m)).continuous
  have hCS : A ^ 2 ≤ (Nat.factorial (2 * m) : ℝ) * 4 ^ m * B := by
    rw [← l2_identity]; exact sq_integral_abs_le _ hcont
  have hB : B = 2 ^ (2 * m) * (m.factorial : ℝ) ^ 2 / (2 * m + 1).factorial := norm_fm m
  have hf0 : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hf1 : (0 : ℝ) < (Nat.factorial (2 * m + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hs0 : (0 : ℝ) < √(2 * m + 1) := Real.sqrt_pos.mpr (by positivity)
  have hss : √(2 * m + 1) ^ 2 = (2 * m + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hBpos : 0 < B := by rw [hB]; positivity
  have hμ0 : 0 ≤ μ := by positivity
  have hfac : (Nat.factorial (2 * m + 1) : ℝ) = (2 * m + 1) * Nat.factorial (2 * m) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hkey : (B * μ) ^ 2 = (Nat.factorial (2 * m) : ℝ) * 4 ^ m * B := by
    simp only [μ]
    rw [hB]
    simp only [mul_pow, div_pow]
    rw [hss, hfac]
    rw [hfac] at hf1
    have h2 : (0 : ℝ) < 2 * m + 1 := by positivity
    have h3 : (0 : ℝ) < (Nat.factorial (2 * m) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    field_simp
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg _)
  have hAle : A ≤ B * μ := by
    have hBμ : 0 ≤ B * μ := mul_nonneg hBpos.le hμ0
    nlinarith
  show A / B ≤ μ
  rw [div_le_iff₀ hBpos]; linarith

/-- Upper half of `MuStar48Bounds`: μ*_48(f_48) ≤ μ_48. PROVED. -/
theorem muStar48_upper : muStar 48 ≤ LeanLab.RamareSaouter2003.Row1.mu48 := by
  have h := muStar_le 48
  simp only [LeanLab.RamareSaouter2003.Row1.mu48]
  convert h using 3; norm_num

/-- Upper half of `MuStar55Bounds`: μ*_55(f_55) ≤ μ_55. PROVED. -/
theorem muStar55_upper : muStar 55 ≤ LeanLab.RamareSaouter2003.Row59.mu55 := by
  have h := muStar_le 55
  simp only [LeanLab.RamareSaouter2003.Row59.mu55]
  convert h using 3; norm_num

/-- `MuStar48Bounds` from its lower half alone. PROVED. -/
theorem muStar48Bounds_of_lower (h : LeanLab.RamareSaouter2003.Row1.mu48 / 2 ≤ muStar 48) :
    LeanLab.RamareSaouter2003.Row1.MuStar48Bounds := ⟨h, muStar48_upper⟩

/-- `MuStar55Bounds` from its lower half alone. PROVED. -/
theorem muStar55Bounds_of_lower (h : LeanLab.RamareSaouter2003.Row59.mu55 / 2 ≤ muStar 55) :
    LeanLab.RamareSaouter2003.Row59.MuStar55Bounds := ⟨h, muStar55_upper⟩

end LeanLab.RamareSaouter2003.MuStarUpper

#print axioms LeanLab.RamareSaouter2003.MuStarUpper.muStar_le
#print axioms LeanLab.RamareSaouter2003.MuStarUpper.muStar48Bounds_of_lower
#print axioms LeanLab.RamareSaouter2003.MuStarUpper.muStar55Bounds_of_lower
