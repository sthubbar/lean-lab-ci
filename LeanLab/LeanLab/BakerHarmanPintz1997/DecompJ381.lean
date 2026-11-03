/-
Baker, Harman and Pintz 1997, pages 11, 23 and 24.
CODEX task223. Principal character diagnostic for the sealed large L leaf.
The old leaf is refuted with clean axioms, and U-1609 re-cut it against that refutation.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements
import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput
open scoped Real

namespace LeanLab.BakerHarmanPintz1997
open Finset

namespace LargeL223
attribute [local instance] Classical.propDecidable
open MeasureTheory intervalIntegral

/-- Page 24 diagnostic. A derivative bound controls the left Riemann sum error. -/
theorem sum_integral_error (f f' : ℝ → ℂ) (a b : ℕ) (hab : a ≤ b) {D : ℝ}
    (hD : 0 ≤ D)
    (hf : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f' x) x)
    (hd : ∀ x ∈ Set.Icc (a : ℝ) b, ‖f' x‖ ≤ D) :
    ‖(∑ n ∈ Ico a b, f n) - ∫ x in (a : ℝ)..b, f x‖ ≤ (b - a : ℕ) * D := by
  have hc : ContinuousOn f (Set.Icc (a : ℝ) b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hint : ∀ n ∈ Ico a b, IntervalIntegrable f volume (n : ℝ) (n + 1) := by
    intro n hn
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    rw [Set.uIcc_of_le (by norm_num : (n : ℝ) ≤ n + 1)]
    intro x hx
    have hn' := mem_Ico.mp hn
    have hna : (a : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hnb : (n : ℝ) + 1 ≤ b := by exact_mod_cast hn'.2
    exact ⟨hna.trans hx.1, hx.2.trans hnb⟩
  have he : ∀ n ∈ Ico a b,
      ‖f n - ∫ x in (n : ℝ)..(n + 1), f x‖ ≤ D := by
    intro n hn
    have hn' := mem_Ico.mp hn
    have hna : (a : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hnb : (n : ℝ) + 1 ≤ b := by exact_mod_cast hn'.2
    have hsub : Set.Icc (n : ℝ) (n + 1) ⊆ Set.Icc (a : ℝ) b :=
      fun x hx => ⟨hna.trans hx.1, hx.2.trans hnb⟩
    have hpoint : ∀ x ∈ Set.Icc (n : ℝ) (n + 1), ‖f n - f x‖ ≤ D := by
      intro x hx
      have hb := norm_image_sub_le_of_norm_deriv_le_segment'
        (fun y hy => (hf y (hsub hy)).hasDerivWithinAt)
        (fun y hy => hd y (hsub ⟨hy.1, hy.2.le⟩)) x hx
      rw [norm_sub_rev] at hb
      exact hb.trans (by nlinarith [hx.2])
    have hid : f n - ∫ x in (n : ℝ)..(n + 1), f x =
        ∫ x in (n : ℝ)..(n + 1), (f n - f x) := by
      rw [integral_sub intervalIntegrable_const (hint n hn), intervalIntegral.integral_const]
      simp
    rw [hid]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (n : ℝ)) (b := n + 1) (fun x hx => hpoint x (by
        rw [Set.uIoc_of_le (by linarith)] at hx
        exact ⟨hx.1.le, hx.2⟩))
    simpa using hh
  have hi := sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n : ℝ)) hab
    (fun n hn => by simpa only [Nat.cast_add, Nat.cast_one] using hint n (Finset.mem_Ico.mpr hn))
  rw [← hi, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ico a b, ‖f n - ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ico a b, D := by
      apply sum_le_sum
      intro n hn
      simpa only [Nat.cast_add, Nat.cast_one] using he n hn
    _ = _ := by simp

/-- Page 24 diagnostic. The derivative of a principal critical line term. -/
theorem principal_hasDerivAt (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-(half t)))
      ((-(half t)) * (x : ℂ) ^ (-(half t) - 1)) x := by
  apply hasDerivAt_ofReal_cpow_const hx.ne'
  intro h
  have hh := congrArg Complex.re h
  norm_num [half] at hh

/-- Page 24 diagnostic. Critical line terms have inverse square root norm. -/
theorem principal_norm (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-(half t))‖ = x ^ (-1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  norm_num [half]

/-- Page 24 diagnostic. A uniform derivative norm bound on a positive interval. -/
theorem principal_derivative_norm (t : ℝ) {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    ‖(-(half t)) * (x : ℂ) ^ (-(half t) - 1)‖ ≤ (|t| + 1) * a ^ (-3 / 2 : ℝ) := by
  have hx := ha.trans_le hax
  have hh : ‖half t‖ ≤ |t| + 1 := by
    unfold half
    calc
      _ ≤ ‖(1 : ℂ) / 2‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ _ := by simp [Real.norm_eq_abs]; linarith
  rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-(half t) - 1).re = (-3 / 2 : ℝ) := by simp [half]; norm_num
  rw [hre]
  exact mul_le_mul hh (Real.rpow_le_rpow_of_nonpos ha hax (by norm_num))
    (by positivity) (by positivity)

/-- Page 24 diagnostic. The principal integral retains a square root length main term. -/
theorem principal_integral_lower {a t : ℝ} (ha : 0 < a) :
    a ^ (1 / 2 : ℝ) / (|t| + 1) ≤
      ‖∫ x in a..(4 * a), (x : ℂ) ^ (-(half t))‖ := by
  have hr : -1 < (-(half t)).re := by norm_num [half]
  rw [integral_cpow (Or.inl hr), norm_div]
  have hre : (-(half t) + 1).re = (1 / 2 : ℝ) := by norm_num [half]
  have hnum : a ^ (1 / 2 : ℝ) ≤
      ‖((4 * a : ℝ) : ℂ) ^ (-(half t) + 1) - (a : ℂ) ^ (-(half t) + 1)‖ := by
    have hh := norm_sub_norm_le (((4 * a : ℝ) : ℂ) ^ (-(half t) + 1))
      ((a : ℂ) ^ (-(half t) + 1))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Complex.norm_cpow_eq_rpow_re_of_pos ha, hre, Real.mul_rpow (by norm_num) ha.le] at hh
    have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow]; norm_num
    rw [hfour] at hh
    linarith
  have hden : ‖-(half t) + 1‖ ≤ |t| + 1 := by
    have heq : -(half t) + 1 = (1 : ℂ) / 2 + (-t : ℂ) * Complex.I := by
      unfold half; ring
    rw [heq]
    calc
      _ ≤ ‖(1 : ℂ) / 2‖ + ‖(-t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ _ := by simp [Real.norm_eq_abs]; linarith
  have hd0 : 0 < ‖-(half t) + 1‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hh := congrArg Complex.re hz
    norm_num [half] at hh
  exact div_le_div₀ (by positivity) hnum hd0 hden

/-- Page 24 diagnostic. The principal unsieved interval has an explicit lower bound. -/
theorem principal_sum_lower (k : ℕ) (hk : 0 < k) (t : ℝ) :
    (k : ℝ) ^ (1 / 2 : ℝ) / (|t| + 1) -
      (3 * |t| + 4) * (k : ℝ) ^ (-1 / 2 : ℝ) ≤
    ‖∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t))‖ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hb := sum_integral_error (fun x => (x : ℂ) ^ (-(half t)))
    (fun x => (-(half t)) * (x : ℂ) ^ (-(half t) - 1)) k (4 * k) (by omega)
    (D := (|t| + 1) * (k : ℝ) ^ (-3 / 2 : ℝ)) (by positivity)
    (fun x hx => principal_hasDerivAt t (hk0.trans_le hx.1))
    (fun x hx => principal_derivative_norm t hk0 hx.1)
  have hcount : (4 * k - k : ℕ) = 3 * k := by omega
  rw [hcount] at hb
  have hpower : (k : ℝ) * (k : ℝ) ^ (-3 / 2 : ℝ) = (k : ℝ) ^ (-1 / 2 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (k : ℝ)]
    rw [← Real.rpow_add hk0]
    norm_num
  have herr : ‖(∑ n ∈ Ico k (4 * k), (n : ℂ) ^ (-(half t))) -
      ∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t))‖ ≤
        3 * (|t| + 1) * (k : ℝ) ^ (-1 / 2 : ℝ) := by
    convert hb using 1
    · simp
    · push_cast
      rw [← hpower]
      ring
  have hsplit : (∑ n ∈ Ico k (4 * k), (n : ℂ) ^ (-(half t))) =
      (k : ℂ) ^ (-(half t)) + ∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t)) := by
    rw [← Finset.sum_insert (f := fun n : ℕ => (n : ℂ) ^ (-(half t))) (by simp)]
    congr 1
    ext n
    simp only [mem_insert, mem_Ico, mem_Ioo]
    omega
  have hl := principal_integral_lower (t := t) hk0
  have hn := norm_sub_norm_le
    (∫ x in (k : ℝ)..(4 * k), (x : ℂ) ^ (-(half t)))
    (∑ n ∈ Ico k (4 * k), (n : ℂ) ^ (-(half t)))
  rw [norm_sub_rev] at hn
  rw [hsplit] at hn
  have ht := norm_add_le ((k : ℂ) ^ (-(half t)))
    (∑ n ∈ Ioo k (4 * k), (n : ℂ) ^ (-(half t)))
  have hkterm : ‖(k : ℂ) ^ (-(half t))‖ = (k : ℝ) ^ (-1 / 2 : ℝ) := by
    simpa using principal_norm t hk0
  rw [hkterm] at ht
  rw [hsplit] at herr
  nlinarith

/-- Page 24 diagnostic. A nonempty unit spaced principal height configuration. -/
noncomputable def principalCfg (J : ℕ) : Cfg where
  q := 1
  T := 2 * J
  S := (range J).image (fun i : ℕ => (((J + i : ℕ) : ℝ), (1 : DirichletCharacter ℂ 1)))

/-- Page 24 diagnostic. The two short factors can both be the monomial one. -/
noncomputable def unitPolynomial : DP := ⟨fun _ => 1, {1}⟩

/-- Page 24 diagnostic. Every sampled height has a large principal long factor. -/
theorem principal_sample_lower (J : ℕ) (hJ : 16 ≤ J) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * J) :
    (J : ℝ) ^ 3 / 4 ≤
      ‖∑ n ∈ Ioo (J ^ 8) (4 * J ^ 8), (n : ℂ) ^ (-(half t))‖ := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hJ16 : (16 : ℝ) ≤ J := by exact_mod_cast hJ
  have hp : ((J ^ 8 : ℕ) : ℝ) ^ (1 / 2 : ℝ) = (J : ℝ) ^ 4 := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hJ0.le]
    norm_num
  have hp' : ((J ^ 8 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) = ((J : ℝ) ^ 4)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by positivity), hp]
  have hb := principal_sum_lower (J ^ 8) (by positivity) t
  rw [hp, hp', abs_of_nonneg ht0] at hb
  have hm : (J : ℝ) ^ 3 / 3 ≤ (J : ℝ) ^ 4 / (t + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < t + 1)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (show t + 1 ≤ 3 * (J : ℝ) by linarith)
      (show 0 ≤ (J : ℝ) ^ 3 by positivity)]
  have hp7 : 72 * (J : ℝ) + 48 ≤ (J : ℝ) ^ 7 := by
    have hh : (16 : ℝ) ^ 2 ≤ (J : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hJ16 2
    have hh' := mul_le_mul_of_nonneg_right hh hJ0.le
    have hh7 : (J : ℝ) ^ 3 ≤ (J : ℝ) ^ 7 := pow_le_pow_right₀ hJ1 (by omega)
    nlinarith
  have he : (3 * t + 4) * ((J : ℝ) ^ 4)⁻¹ ≤ (J : ℝ) ^ 3 / 12 := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : 0 < (J : ℝ) ^ 4)]
    have hid : (J : ℝ) ^ 3 / 12 * (J : ℝ) ^ 4 = (J : ℝ) ^ 7 / 12 := by ring
    rw [hid]
    linarith
  linarith

/-- Page 11 and page 24 diagnostic. The principal sample set is well spaced. -/
theorem principalCfg_wellSpaced (J : ℕ) : (principalCfg J).WellSpaced := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := mem_image.mp he
  have hiJ := mem_range.mp hi
  constructor
  · simp only [principalCfg, Nat.cast_add, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (J : ℝ) + i)]
    have : (i : ℝ) < J := by exact_mod_cast hiJ
    linarith
  · intro e he hχ hne
    obtain ⟨j, hj, rfl⟩ := mem_image.mp he
    have hij : i ≠ j := by intro hij; subst j; exact hne rfl
    simp only [Nat.cast_add, add_sub_add_left_eq_sub]
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hh : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      rw [abs_of_nonpos (by linarith : (i : ℝ) - j ≤ 0)]
      linarith
    · have hh : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (i : ℝ) - j)]
      linarith

/-- Page 24 diagnostic. All principal ordinates lie in the required upper half interval. -/
theorem principalCfg_heights (J : ℕ) :
    ∀ e ∈ (principalCfg J).S, e.2 = 1 →
      (principalCfg J).T / 2 ≤ |e.1| ∧ |e.1| ≤ (principalCfg J).T := by
  intro e he hχ
  obtain ⟨i, hi, rfl⟩ := mem_image.mp he
  have hiJ : (i : ℝ) < J := by exact_mod_cast mem_range.mp hi
  simp only [principalCfg, Nat.cast_add, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (J : ℝ) + i)]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i]

/-- Page 24 diagnostic. The two short factors meet the exact sealed coefficient and length bounds. -/
theorem unitPolynomial_famOK :
    FamOK (fun _ => [unitPolynomial, unitPolynomial]) [fun _ => 2, fun _ => 2] 0 (1 / 4) 1 := by
  intro x
  refine ⟨rfl, ?_⟩
  intro i hi hi'
  have hi0 : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases hi0 with rfl | rfl <;>
    simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals
    constructor
    · intro n hn
      simp only [unitPolynomial, mem_singleton] at hn
      subst n
      norm_num
    · intro n hn
      simp [unitPolynomial, Real.rpow_zero]

/-- Page 24 diagnostic. The total product norm grows at the square root x scale. -/
theorem principal_product_lower (J : ℕ) (hJ : 16 ≤ J) :
    (J : ℝ) ^ 4 / 4 ≤ norm1prod
      [unitPolynomial, unitPolynomial, (⟨fun _ => 1, Ioo (J ^ 8) (4 * J ^ 8)⟩ : DP)]
      (principalCfg J) := by
  have hinj : Function.Injective (fun i : ℕ =>
      (((J + i : ℕ) : ℝ), (1 : DirichletCharacter ℂ 1))) := by
    intro i j hij
    have hh := congrArg Prod.fst hij
    dsimp only at hh
    have hnat : J + i = J + j := by exact_mod_cast hh
    omega
  unfold norm1prod
  rw [principalCfg, sum_image (fun i _ j _ h => hinj h)]
  have hterm : ∀ i ∈ range J,
      ‖([unitPolynomial, unitPolynomial, (⟨fun _ => 1, Ioo (J ^ 8) (4 * J ^ 8)⟩ : DP)].map
        (fun P => P.eval (1 : DirichletCharacter ℂ 1) (half ((J + i : ℕ) : ℝ)))).prod‖ =
      ‖∑ n ∈ Ioo (J ^ 8) (4 * J ^ 8), (n : ℂ) ^ (-(half ((J + i : ℕ) : ℝ)))‖ := by
    intro i hi
    have hχ : ∀ z : ZMod 1, (1 : DirichletCharacter ℂ 1) z = 1 := by
      intro z
      apply MulChar.one_apply
      have hz : z = 1 := Subsingleton.elim _ _
      rw [hz]
      exact isUnit_one
    simp [DP.eval, unitPolynomial, hχ]
  rw [sum_congr rfl hterm]
  calc
    _ = ∑ i ∈ range J, (J : ℝ) ^ 3 / 4 := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      apply principal_sample_lower J hJ (by positivity)
      have hh : (i : ℝ) < J := by exact_mod_cast mem_range.mp hi
      push_cast
      linarith

/-- Pages 11 and 24 diagnostic. The principal sample configurations satisfy Std. -/
theorem principalCfg_std (J : ℕ) (hJ : 16 ≤ J) :
    (principalCfg J).Std (16 * (J : ℝ) ^ 8) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hJpow : (J : ℝ) ≤ (J : ℝ) ^ 8 := by
    simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 8 by omega)
  refine ⟨principalCfg_wellSpaced J, by norm_num [principalCfg], ?_, ?_, ?_⟩
  · norm_num [principalCfg]; nlinarith
  · dsimp [principalCfg]; have : (16 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  · norm_num [principalCfg]; nlinarith

/-- Page 23 diagnostic. The sample scales meet both exponential height cutoffs. -/
theorem principalCfg_cutoffs (J : ℕ) (hJ : 16 ≤ J) (hlog : 16 ≤ Real.log J)
    {ε : ℝ} (hε : ε ≤ 1 / 16) :
    T0 (16 * (J : ℝ) ^ 8) ≤ (principalCfg J).T ∧
      (principalCfg J).T ≤ T1 ε (16 * (J : ℝ) ^ 8) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hx1 : 1 ≤ 16 * (J : ℝ) ^ 8 := by
    have hh := one_le_pow₀ hJ1 (n := 8)
    linarith
  have hlogx : 0 ≤ Real.log (16 * (J : ℝ) ^ 8) := Real.log_nonneg hx1
  have hlogeq : Real.log (16 * (J : ℝ) ^ 8) = Real.log 16 + 8 * Real.log J := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  constructor
  · have hcube : Real.log (16 * (J : ℝ) ^ 8) ≤ (Real.log J) ^ 3 := by
      rw [hlogeq]
      have h16 : Real.log 16 ≤ 16 := (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)).trans (by norm_num)
      have hh := mul_nonneg (show 0 ≤ Real.log J - 16 by linarith) (sq_nonneg (Real.log J))
      nlinarith [sq_nonneg (Real.log J - 1)]
    have hroot : (Real.log (16 * (J : ℝ) ^ 8) ^ (1 / 3 : ℝ)) ^ 3 =
        Real.log (16 * (J : ℝ) ^ 8) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogx]
      norm_num
    have hle : Real.log (16 * (J : ℝ) ^ 8) ^ (1 / 3 : ℝ) ≤ Real.log J := by
      have hh : (Real.log (16 * (J : ℝ) ^ 8) ^ (1 / 3 : ℝ)) ^ 3 ≤ (Real.log J) ^ 3 := by
        rw [hroot]; exact hcube
      exact (pow_le_pow_iff_left₀ (by positivity) (by linarith : 0 ≤ Real.log J) (by omega : 3 ≠ 0)).mp hh
    have hh := Real.exp_le_exp.mpr hle
    rw [Real.exp_log hJ0] at hh
    dsimp [T0, L, principalCfg]
    linarith
  · have hquarter : (16 * (J : ℝ) ^ 8) ^ (1 / 4 : ℝ) = 2 * (J : ℝ) ^ 2 := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hJ0.le]
      norm_num
    have hpow := Real.rpow_le_rpow_of_exponent_le hx1
      (show (1 / 4 : ℝ) ≤ 0.45 - 2 * ε / 3 by linarith)
    rw [hquarter] at hpow
    dsimp [principalCfg, T1]
    nlinarith [sq_nonneg ((J : ℝ) - 1)]

/-- Pages 11 and 23 diagnostic. A concrete nonempty configuration meets the source ranges. -/
theorem principal_counterexample_nonempty :
    ∃ J : ℕ, 16 ≤ J ∧ 16 ≤ Real.log J ∧ (principalCfg J).S.Nonempty ∧
      (principalCfg J).Std (16 * (J : ℝ) ^ 8) ∧
      T0 (16 * (J : ℝ) ^ 8) ≤ (principalCfg J).T ∧
      (principalCfg J).T ≤ T1 (1 / 32) (16 * (J : ℝ) ^ 8) ∧
      (principalCfg J).T < 4 * (J : ℝ) ^ 8 := by
  let J : ℕ := ⌈Real.exp 17⌉₊
  have he : Real.exp 17 ≤ (J : ℝ) := Nat.le_ceil _
  have hexp : (18 : ℝ) ≤ Real.exp 17 := by
    convert Real.add_one_le_exp (17 : ℝ) using 1; norm_num
  have hJ : 16 ≤ J := by exact_mod_cast (show (16 : ℝ) ≤ J by linarith)
  have hJ0 : (0 : ℝ) < J := by linarith
  have hlog : 16 ≤ Real.log J := by
    have hh := Real.log_le_log (Real.exp_pos 17) he
    rw [Real.log_exp] at hh
    linarith
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hp : (J : ℝ) ≤ (J : ℝ) ^ 8 := by
    simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 8 by omega)
  obtain ⟨hlo, hhi⟩ := principalCfg_cutoffs J hJ hlog (by norm_num : (1 / 32 : ℝ) ≤ 1 / 16)
  refine ⟨J, hJ, hlog, ?_, principalCfg_std J hJ, hlo, hhi, ?_⟩
  · refine ⟨(((J : ℝ), (1 : DirichletCharacter ℂ 1))), ?_⟩
    apply mem_image.mpr
    exact ⟨0, mem_range.mpr (by omega), by rfl⟩
  · dsimp [principalCfg]
    nlinarith

/-- Page 11 diagnostic. The counterexample lengths also obey the paper standing range. -/
theorem principal_counterexample_lengths (J : ℕ) (hJ : 16 ≤ J) :
    2 ≤ 16 * (J : ℝ) ^ 8 ∧
      2 ≤ 4 * (J : ℝ) ^ 8 ∧ 4 * (J : ℝ) ^ 8 ≤ 16 * (J : ℝ) ^ 8 := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  have hp := one_le_pow₀ hJ1 (n := 8)
  constructor
  · linarith
  constructor <;> linarith

/-- Page 23 diagnostic. The counterexample also satisfies the paper condition 3.39. -/
theorem principal_counterexample_339 (J : ℕ) (hJ : 16 ≤ J) {ε : ℝ} (hε : 0 ≤ ε) :
    max (2 : ℝ) 2 ≤ (16 * (J : ℝ) ^ 8) ^ (0.46 + ε / 8) := by
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  have hx : 16 ≤ 16 * (J : ℝ) ^ 8 := by nlinarith [one_le_pow₀ hJ1 (n := 8)]
  have he : (1 / 4 : ℝ) ≤ 0.46 + ε / 8 := by linarith
  have hb := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 16 * (J : ℝ) ^ 8 by linarith) he
  have ha := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 16) hx (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hfour : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by norm_num
  rw [hfour] at ha
  simpa only [max_self] using ha.trans hb

/-- Page 24. Holder with exponents two, four and four for the sampled product. -/
theorem norm1prod_le_pnorm244 (M N Lp : DP) (c : Cfg) :
    norm1prod [M, N, Lp] c ≤ pnorm M c 2 * pnorm N c 4 * pnorm Lp c 4 := by
  let f := fun e : ℝ × DirichletCharacter ℂ c.q => ‖M.eval e.2 (half e.1)‖
  let g := fun e : ℝ × DirichletCharacter ℂ c.q => ‖N.eval e.2 (half e.1)‖
  let h := fun e : ℝ × DirichletCharacter ℂ c.q => ‖Lp.eval e.2 (half e.1)‖
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt c.S f (fun e => g e * h e)
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt c.S (fun e => g e ^ 2) (fun e => h e ^ 2)
  have hb : (∑ e ∈ c.S, (g e * h e) ^ 2) ≤
      Real.sqrt (∑ e ∈ c.S, g e ^ 4) * Real.sqrt (∑ e ∈ c.S, h e ^ 4) := by
    simpa only [mul_pow, ← pow_mul, show 2 * 2 = 4 by norm_num] using h2
  have hs (v : (ℝ × DirichletCharacter ℂ c.q) → ℝ) :
      Real.sqrt (Real.sqrt (∑ e ∈ c.S, v e ^ 4)) =
        (∑ e ∈ c.S, v e ^ 4) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  calc
    _ = ∑ e ∈ c.S, f e * (g e * h e) := by
      simp [norm1prod, f, g, h]
    _ ≤ Real.sqrt (∑ e ∈ c.S, f e ^ 2) * Real.sqrt (∑ e ∈ c.S, (g e * h e) ^ 2) := h1
    _ ≤ Real.sqrt (∑ e ∈ c.S, f e ^ 2) *
        Real.sqrt (Real.sqrt (∑ e ∈ c.S, g e ^ 4) * Real.sqrt (∑ e ∈ c.S, h e ^ 4)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _), hs g, hs h]
      norm_num only [pnorm, Real.rpow_ofNat] at ⊢
      rw [Real.sqrt_eq_rpow]
      dsimp [f, g, h]
      ring

#print axioms norm1prod_le_pnorm244
#print axioms principal_counterexample_lengths
#print axioms principal_counterexample_339
#print axioms principal_counterexample_nonempty
#print axioms principalCfg_std
#print axioms principalCfg_cutoffs
#print axioms principalCfg_wellSpaced
#print axioms principalCfg_heights
#print axioms unitPolynomial_famOK
#print axioms principal_product_lower
#print axioms principalCfg
#print axioms unitPolynomial
#print axioms principal_sample_lower
#print axioms principal_integral_lower
#print axioms principal_sum_lower
#print axioms sum_integral_error
#print axioms principal_hasDerivAt
#print axioms principal_norm
#print axioms principal_derivative_norm
end LargeL223

/-- Page 23 diagnostic. The sealed large L leaf fails for constant short factors and principal samples. -/
theorem lemma10_large_L_false : ¬ (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮) := by
  classical
  intro hleaf
  obtain ⟨ε0, hε0, hleaf⟩ := hleaf
  let ε : ℝ := min (ε0 / 2) (1 / 16)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεsmall : ε ≤ 1 / 16 := min_le_right _ _
  have hεlt : ε < ε0 := (min_le_left _ _).trans_lt (by linarith)
  let S : ℝ → Set Cfg := fun x => {c | ∃ J : ℕ,
    16 ≤ J ∧ 16 ≤ Real.log J ∧ x = 16 * (J : ℝ) ^ 8 ∧ c = LargeL223.principalCfg J}
  have hs : ∀ x, ∀ c ∈ S x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ (0 : ℝ) ∧
      T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T := by
    intro x c hc
    obtain ⟨J, hJ, hlog, rfl, rfl⟩ := hc
    obtain ⟨hlo, hhi⟩ := LargeL223.principalCfg_cutoffs J hJ hlog hεsmall
    exact ⟨LargeL223.principalCfg_std J hJ, by simp [LargeL223.principalCfg], hlo, hhi,
      LargeL223.principalCfg_heights J⟩
  have hl : ∀ x, ∀ c ∈ S x, (c.q : ℝ) * c.T < x / 4 := by
    intro x c hc
    obtain ⟨J, hJ, hlog, rfl, rfl⟩ := hc
    have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
    have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
    have hh : (J : ℝ) ≤ (J : ℝ) ^ 8 := by
      simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 8 by omega)
    norm_num [LargeL223.principalCfg]
    nlinarith
  have hc := hleaf ε hε hεlt 0 0 (1 / 4) 1
    (fun _ => LargeL223.unitPolynomial) (fun _ => LargeL223.unitPolynomial)
    (fun _ => 2) (fun _ => 2) (fun x => x / 4) S
    (by norm_num) (by norm_num) LargeL223.unitPolynomial_famOK (by intro x; ring) hs hl
  obtain ⟨C, X0, hbound⟩ := hc 1 (by norm_num)
  obtain ⟨J, hJbig⟩ := exists_nat_gt
    (max 16 (max (|X0| + 1) (Real.exp (16 * |C| + 16))))
  have hJ16 : (16 : ℝ) < J := (le_max_left _ _).trans_lt hJbig
  have hJ : 16 ≤ J := by exact_mod_cast hJ16.le
  have hJ0 : (0 : ℝ) < J := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hJX : |X0| + 1 < J :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hJbig
  have hJexp : Real.exp (16 * |C| + 16) < J :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hJbig
  have hlog : 16 * |C| + 16 < Real.log J := by
    have hh := Real.log_lt_log (Real.exp_pos (16 * |C| + 16)) hJexp
    simpa only [Real.log_exp] using hh
  have hlog16 : 16 ≤ Real.log J := by linarith [abs_nonneg C]
  have hJpow : (J : ℝ) ≤ (J : ℝ) ^ 8 := by
    simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 8 by omega)
  have hx : X0 ≤ 16 * (J : ℝ) ^ 8 := by linarith [le_abs_self X0]
  have hmem : LargeL223.principalCfg J ∈ S (16 * (J : ℝ) ^ 8) :=
    ⟨J, hJ, hlog16, rfl, rfl⟩
  have hb := hbound (16 * (J : ℝ) ^ 8) hx (LargeL223.principalCfg J) hmem
  have hsupp : Ioo ⌊(1 / 4 : ℝ) * (16 * (J : ℝ) ^ 8 / 4)⌋₊
      ⌈1 * (16 * (J : ℝ) ^ 8 / 4)⌉₊ = Ioo (J ^ 8) (4 * J ^ 8) := by
    have heq1 : (1 / 4 : ℝ) * (16 * (J : ℝ) ^ 8 / 4) = ((J ^ 8 : ℕ) : ℝ) := by push_cast; ring
    have heq2 : 1 * (16 * (J : ℝ) ^ 8 / 4) = ((4 * J ^ 8 : ℕ) : ℝ) := by push_cast; ring
    rw [heq1, heq2, Nat.floor_natCast, Nat.ceil_natCast]
  dsimp only at hb
  rw [hsupp] at hb
  have hp := LargeL223.principal_product_lower J hJ
  have hroot : (16 * (J : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 4 * (J : ℝ) ^ 4 := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hJ0.le]
    norm_num
  rw [hroot, Real.rpow_one] at hb
  have hlogx : 16 * |C| < L (16 * (J : ℝ) ^ 8) := by
    unfold L
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 16 by norm_num), abs_nonneg C]
  have hlogx0 : 0 < L (16 * (J : ℝ) ^ 8) := by linarith [abs_nonneg C]
  have hcontr := (le_div_iff₀ hlogx0).mp (hp.trans hb)
  have hJ4 : 0 < (J : ℝ) ^ 4 := by positivity
  have hh := mul_lt_mul_of_pos_left hlogx hJ4
  nlinarith [le_abs_self C]

#print axioms lemma10_large_L_false

/-- Page 23 diagnostic. The original encoded Lemma 10 also fails with constant short factors. -/
theorem lemma10_false : ¬ Lemma10 := by
  classical
  intro hleaf
  unfold Lemma10 at hleaf
  obtain ⟨ε0, hε0, hleaf⟩ := hleaf
  let ε : ℝ := min (ε0 / 2) (1 / 16)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεsmall : ε ≤ 1 / 16 := min_le_right _ _
  have hεlt : ε < ε0 := (min_le_left _ _).trans_lt (by linarith)
  let F : ℝ → ℝ := fun x => if 16 ≤ x then 2 else min (-1) (x ^ (0.46 + ε / 8))
  let P : ℝ → DP := fun x => if 16 ≤ x then LargeL223.unitPolynomial else ⟨fun _ => 0, ∅⟩
  let Ll : ℝ → ℝ := fun x => x / (F x * F x)
  have hFne : ∀ x, F x ≠ 0 := by
    intro x
    by_cases hx : 16 ≤ x
    · simp [F, hx]
    · have hh : F x ≤ -1 := by simpa only [F, ite_eq_right hx] using min_le_left (-1) (x ^ (0.46 + ε / 8))
      linarith
  have hprod : ∀ x, F x * F x * Ll x = x := by
    intro x
    dsimp [Ll]
    field_simp [hFne x]
  have hfam : FamOK (fun x => [P x, P x]) [F, F] 0 (1 / 4) 1 := by
    intro x
    by_cases hx : 16 ≤ x
    · refine ⟨rfl, ?_⟩
      intro i hi hi'
      have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi01 with rfl | rfl <;>
        simpa [P, F, hx] using (LargeL223.unitPolynomial_famOK x).2 0 (by simp) (by simp)
    · refine ⟨rfl, ?_⟩
      intro i hi hi'
      have hi01 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi01 with rfl | rfl <;>
        simp [P, F, hx, DP.HasLen, DP.Coef31]
  have hcase : ∀ x, max (F x) (x ^ (0.45 : ℝ)) * max (F x) (x ^ (0.225 : ℝ)) ≤
      x ^ (0.775 + ε / 8) ∨ max (F x) (F x) ≤ x ^ (0.46 + ε / 8) := by
    intro x
    apply Or.inr
    rw [max_self]
    by_cases hx : 16 ≤ x
    · simp only [F, ite_eq_left hx]
      have he : (1 / 4 : ℝ) ≤ 0.46 + ε / 8 := by linarith [hε]
      have hh := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ x by linarith) he
      have hh' := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 16) hx (by norm_num : (0 : ℝ) ≤ 1 / 4)
      norm_num at hh'
      exact hh'.trans hh
    · simpa only [F, ite_eq_right hx] using min_le_right (-1) (x ^ (0.46 + ε / 8))
  let S : ℝ → Set Cfg := fun x => {c | ∃ J : ℕ,
    16 ≤ J ∧ 16 ≤ Real.log J ∧ x = 16 * (J : ℝ) ^ 8 ∧ c = LargeL223.principalCfg J}
  have hs : ∀ x, ∀ c ∈ S x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ (0 : ℝ) ∧
      T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T := by
    intro x c hc
    obtain ⟨J, hJ, hlog, rfl, rfl⟩ := hc
    obtain ⟨hlo, hhi⟩ := LargeL223.principalCfg_cutoffs J hJ hlog hεsmall
    exact ⟨LargeL223.principalCfg_std J hJ, by simp [LargeL223.principalCfg], hlo, hhi,
      LargeL223.principalCfg_heights J⟩
  have hc := hleaf ε hε hεlt 0 0 (1 / 4) 1 P P F F Ll S
    (by norm_num) (by norm_num) hfam hprod hs hcase
  obtain ⟨C, X0, hbound⟩ := hc 1 (by norm_num)
  obtain ⟨J, hJbig⟩ := exists_nat_gt
    (max 16 (max (|X0| + 1) (Real.exp (16 * |C| + 16))))
  have hJ16 : (16 : ℝ) < J := (le_max_left _ _).trans_lt hJbig
  have hJ : 16 ≤ J := by exact_mod_cast hJ16.le
  have hJ0 : (0 : ℝ) < J := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by linarith
  have hJX : |X0| + 1 < J :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hJbig
  have hJexp : Real.exp (16 * |C| + 16) < J :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hJbig
  have hlog : 16 * |C| + 16 < Real.log J := by
    have hh := Real.log_lt_log (Real.exp_pos (16 * |C| + 16)) hJexp
    simpa only [Real.log_exp] using hh
  have hlog16 : 16 ≤ Real.log J := by linarith [abs_nonneg C]
  have hJpow : (J : ℝ) ≤ (J : ℝ) ^ 8 := by
    simpa using pow_le_pow_right₀ hJ1 (show 1 ≤ 8 by omega)
  have hx : X0 ≤ 16 * (J : ℝ) ^ 8 := by linarith [le_abs_self X0]
  have hmem : LargeL223.principalCfg J ∈ S (16 * (J : ℝ) ^ 8) :=
    ⟨J, hJ, hlog16, rfl, rfl⟩
  have hb := hbound (16 * (J : ℝ) ^ 8) hx (LargeL223.principalCfg J) hmem
  have hxx16 : 16 ≤ 16 * (J : ℝ) ^ 8 := by nlinarith [one_le_pow₀ hJ1 (n := 8)]
  simp only [P, Ll, F, ite_eq_left hxx16] at hb
  norm_num only [show (2 : ℝ) * 2 = 4 by norm_num] at hb
  have hsupp : Ioo ⌊(1 / 4 : ℝ) * (16 * (J : ℝ) ^ 8 / 4)⌋₊
      ⌈1 * (16 * (J : ℝ) ^ 8 / 4)⌉₊ = Ioo (J ^ 8) (4 * J ^ 8) := by
    have heq1 : (1 / 4 : ℝ) * (16 * (J : ℝ) ^ 8 / 4) = ((J ^ 8 : ℕ) : ℝ) := by push_cast; ring
    have heq2 : 1 * (16 * (J : ℝ) ^ 8 / 4) = ((4 * J ^ 8 : ℕ) : ℝ) := by push_cast; ring
    rw [heq1, heq2, Nat.floor_natCast, Nat.ceil_natCast]
  rw [hsupp] at hb
  have hp := LargeL223.principal_product_lower J hJ
  have hroot : (16 * (J : ℝ) ^ 8) ^ (1 / 2 : ℝ) = 4 * (J : ℝ) ^ 4 := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hJ0.le]
    norm_num
  rw [hroot, Real.rpow_one] at hb
  have hlogx : 16 * |C| < L (16 * (J : ℝ) ^ 8) := by
    unfold L
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 16 by norm_num), abs_nonneg C]
  have hlogx0 : 0 < L (16 * (J : ℝ) ^ 8) := by linarith [abs_nonneg C]
  have hcontr := (le_div_iff₀ hlogx0).mp (hp.trans hb)
  have hJ4 : 0 < (J : ℝ) ^ 4 := by positivity
  have hh := mul_lt_mul_of_pos_left hlogx hJ4
  nlinarith [le_abs_self C]

#print axioms lemma10_false

/-- The long polynomial `L(s,χ) = Σ_{l ≍ F} χ(l) l^{-s}` of Lemma 10, p. 23. -/
noncomputable def longDP (c1 c2 F : ℝ) : DP := ⟨fun _ => 1, Finset.Ioo ⌊c1 * F⌋₊ ⌈c2 * F⌉₊⟩

/-- The pointwise input of the case `L > qT`, p. 24, for a family: the printed `‖L‖_∞ ≪ 𝓛^B` for
`χ ≠ χ₀`, and the same plus the polar main term `L^{1/2}/(1+|t|)` for `χ = χ₀`. The printed bound
without that term is false: `Audit1609.bare_long_sup_false`. -/
def LongSup (c1 c2 : ℝ) (Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg) : Prop :=
  ∃ B' K X0 : ℝ, ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x, ∀ e ∈ c.S,
    (e.2 ≠ 1 → ‖(longDP c1 c2 (Ll x)).eval e.2 (half e.1)‖ ≤ K * L x ^ B') ∧
    (e.2 = 1 → ‖(longDP c1 c2 (Ll x)).eval e.2 (half e.1)‖ ≤
      K * (L x ^ B' + Ll x ^ (1 / 2 : ℝ) / (1 + |e.1|)))

/-- Lemma 10, p. 23, repaired by U-1609: the printed hypotheses plus the lower bound `T₀ ≤ MN`, which
the printed statement lacks. Without it `lemma10_false` refutes the statement. -/
def Lemma10Repaired : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ Ml x * Nl x) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮

/-- LEAF, OPEN. p. 24, the reflection step, reference 24 eq. (21), with the polar term of `χ₀` the
print omits. It should follow from `DecompJ883.fgm_bound` by partial summation over dyadic blocks. -/
theorem lemma10_reflection_sup :
  ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K : ℝ, 0 ≤ K ∧
  ∀ (F : ℝ) (c : Cfg), 2 ≤ F → 1 ≤ c.q → 2 < c.T → (c.q : ℝ) * c.T < F →
    ∀ e ∈ c.S, |e.1| ≤ c.T →
      (e.2 ≠ 1 → ‖(longDP c1 c2 F).eval e.2 (half e.1)‖ ≤ K * Real.log F) ∧
      (e.2 = 1 → ‖(longDP c1 c2 F).eval e.2 (half e.1)‖ ≤
        K * (Real.log F + F ^ (1 / 2 : ℝ) / (1 + |e.1|))) := by sorry

/-- LEAF, OPEN. p. 24, Case L > qT, re-cut by U-1609: takes the pointwise input `LongSup`, (3.38) or
(3.39), and `T₀ ≤ MN`. The old form had none of the three and is `lemma10_large_L_false`. -/
theorem lemma10_large_L :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
    (∀ x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ Ml x * Nl x) →
    LongSup c1 c2 Ll 𝒮 →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by sorry

/-- LEAF. p. 24, Case L ≤ qT and (3.38). -/
theorem lemma10_small_L_338 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by sorry

/-- LEAF. p. 24, Case L ≤ qT and (3.39). -/
theorem lemma10_small_L_339 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by sorry

/-- `LongSup` on the large part of a family, from `lemma10_reflection_sup` and `T₀ ≤ MN`. -/
theorem longSup_of_reflection {c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : c1 < c2) {Ml Nl Ll : ℝ → ℝ}
    {𝒮 : ℝ → Set Cfg} (hprod : ∀ x, Ml x * Nl x * Ll x = x)
    (hstd : ∀ x, ∀ c ∈ 𝒮 x, c.Std x) (hlarge : ∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x)
    (hMN : ∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ Ml x * Nl x) : LongSup c1 c2 Ll 𝒮 := by
  obtain ⟨K, hK, hrefl⟩ := lemma10_reflection_sup c1 c2 hc1 hc2
  obtain ⟨X1, hX1⟩ := hMN
  refine ⟨1, K, max X1 1, ?_⟩
  intro x hx c hc e he
  have hx1 : X1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 1 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨hws, hq, -, hT, -⟩ := hstd x c hc
  have hq' : (1 : ℝ) ≤ c.q := by exact_mod_cast hq
  have hlt := hlarge x c hc
  have hF : 2 ≤ Ll x := by nlinarith
  have hT0 : 1 ≤ T0 x := Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx2) _)
  have hprodge : 1 ≤ Ml x * Nl x := hT0.trans (hX1 x hx1)
  have hLx : Ll x ≤ x := by
    have h := hprod x
    nlinarith
  have hlog : Real.log (Ll x) ≤ L x := Real.log_le_log (by linarith) hLx
  obtain ⟨hne, heq⟩ := hrefl (Ll x) c hF hq hT hlt e he (hws e he).1
  rw [Real.rpow_one]
  refine ⟨fun h => (hne h).trans (mul_le_mul_of_nonneg_left hlog hK), fun h => (heq h).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (by linarith) hK

/-- Lemma 10 as repaired by U-1609. CONDITIONAL ON its four OPEN leaves in this file. -/
theorem lemma10_decomposed : Lemma10Repaired := by
  rcases lemma10_large_L with ⟨ε0_1, h_ε0_1, h_large⟩
  rcases lemma10_small_L_338 with ⟨ε0_2, h_ε0_2, h_small_338⟩
  rcases lemma10_small_L_339 with ⟨ε0_3, h_ε0_3, h_small_339⟩
  use min ε0_1 (min ε0_2 ε0_3)
  refine ⟨by positivity, fun ε hε1 hε2 => ?_⟩
  intro A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 h_fam_ok h_prod h_c h_or h_MN A hA

  have h_large_spec := h_large ε hε1 (lt_of_lt_of_le hε2 (min_le_left _ _)) A0 B c1 c2 M N Ml Nl Ll (fun x => {c ∈ 𝒮 x | (c.q : ℝ) * c.T < Ll x}) hc1 hc2 h_fam_ok h_prod (fun x c hc => h_c x c hc.1) (fun x c hc => hc.2) h_or h_MN
    (longSup_of_reflection hc1 hc2 h_prod (fun x c hc => (h_c x c hc.1).1) (fun x c hc => hc.2) h_MN) A hA
  have h_small_338_spec := h_small_338 ε hε1 (lt_of_lt_of_le hε2 (le_trans (min_le_right _ _) (min_le_left _ _))) A0 B c1 c2 M N Ml Nl Ll (fun x => {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)}) hc1 hc2 h_fam_ok h_prod (fun x c hc => h_c x c hc.1) (fun x c hc => hc.2.2) (fun x c hc => hc.2.1) A hA
  have h_small_339_spec := h_small_339 ε hε1 (lt_of_lt_of_le hε2 (le_trans (min_le_right _ _) (min_le_right _ _))) A0 B c1 c2 M N Ml Nl Ll (fun x => {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)}) hc1 hc2 h_fam_ok h_prod (fun x c hc => h_c x c hc.1) (fun x c hc => hc.2.2) (fun x c hc => hc.2.1) A hA

  rcases h_large_spec with ⟨C1, X01, h1⟩
  rcases h_small_338_spec with ⟨C2, X02, h2⟩
  rcases h_small_339_spec with ⟨C3, X03, h3⟩

  use max C1 (max C2 C3), max 1 (max X01 (max X02 X03))
  intro x hx c hc
  have hx_ge_1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx_ge_0 : 0 ≤ x := le_trans (by norm_num) hx_ge_1

  have hx1 : X01 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx2 : X02 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))
  have hx3 : X03 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx))

  have hL_ge_0 : 0 ≤ L x := Real.log_nonneg hx_ge_1
  have H_pos : 0 ≤ x ^ (1 / 2 : ℝ) / L x ^ A := by positivity

  have h_eq_C1 : C1 * (x ^ (1 / 2 : ℝ) / L x ^ A) = C1 * x ^ (1 / 2 : ℝ) / L x ^ A := by ring
  have h_eq_C2 : C2 * (x ^ (1 / 2 : ℝ) / L x ^ A) = C2 * x ^ (1 / 2 : ℝ) / L x ^ A := by ring
  have h_eq_C3 : C3 * (x ^ (1 / 2 : ℝ) / L x ^ A) = C3 * x ^ (1 / 2 : ℝ) / L x ^ A := by ring
  have h_eq_C_max : max C1 (max C2 C3) * (x ^ (1 / 2 : ℝ) / L x ^ A) = max C1 (max C2 C3) * x ^ (1 / 2 : ℝ) / L x ^ A := by ring

  by_cases hL : (c.q : ℝ) * c.T < Ll x
  · have hc_large : c ∈ {c ∈ 𝒮 x | (c.q : ℝ) * c.T < Ll x} := ⟨hc, hL⟩
    have h_ineq := h1 x hx1 c hc_large
    have h_max : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
    have h_mul := mul_le_mul_of_nonneg_right h_max H_pos
    rw [h_eq_C1, h_eq_C_max] at h_mul
    exact le_trans h_ineq h_mul
  · have hL_le : Ll x ≤ (c.q : ℝ) * c.T := not_lt.mp hL
    cases h_or x with
    | inl h_338 =>
      have hc_small : c ∈ {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)} := ⟨hc, hL_le, h_338⟩
      have h_ineq := h2 x hx2 c hc_small
      have h_max : C2 ≤ max C1 (max C2 C3) := le_trans (le_max_left _ _) (le_max_right _ _)
      have h_mul := mul_le_mul_of_nonneg_right h_max H_pos
      rw [h_eq_C2, h_eq_C_max] at h_mul
      exact le_trans h_ineq h_mul
    | inr h_339 =>
      have hc_small : c ∈ {c ∈ 𝒮 x | Ll x ≤ (c.q : ℝ) * c.T ∧ max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)} := ⟨hc, hL_le, h_339⟩
      have h_ineq := h3 x hx3 c hc_small
      have h_max : C3 ≤ max C1 (max C2 C3) := le_trans (le_max_right _ _) (le_max_right _ _)
      have h_mul := mul_le_mul_of_nonneg_right h_max H_pos
      rw [h_eq_C3, h_eq_C_max] at h_mul
      exact le_trans h_ineq h_mul

end LeanLab.BakerHarmanPintz1997
