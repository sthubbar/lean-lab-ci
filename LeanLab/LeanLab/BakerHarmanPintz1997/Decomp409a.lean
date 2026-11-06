/-
P0069 page 25, displays 4.3 to 4.5, supply decomposition for repaired Lemma 11.
Reference 10 page 1372 confirms the kernel denominator s.
https://doi.org/10.4153/CJM-1982-095-9
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

noncomputable section
namespace LeanLab.BakerHarmanPintz1997.Decomp409a
open Finset MeasureTheory intervalIntegral Filter Topology
attribute [local instance] Classical.propDecidable

/-- Page 25, the finite polynomial in the proof of 4.3. -/
def polynomial (a : ℝ → ℕ → ℂ) (x : ℝ) : DP :=
  ⟨a x, Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊⟩

/-- Page 25, the short character sum in 4.5. -/
def window {q : ℕ} (a : ℝ → ℕ → ℂ) (x y : ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, a x k * χ (k : ZMod q)

/-- Page 25, the Perron window kernel with denominator s as in reference 10. -/
def kernel (x y t : ℝ) : ℂ :=
  ((x : ℂ) ^ half t - ((x - y : ℝ) : ℂ) ^ half t) / half t

/-- Page 25, the vertical integral in 4.3 parametrized by real height. -/
def truncated {q : ℕ} (a : ℝ → ℕ → ℂ) (x y T : ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) •
    ∫ t in (-T)..T, (polynomial a x).eval χ (half t) * kernel x y t

/-- Page 25, the common low height density E in 4.4. -/
def density {q : ℕ} (a : ℝ → ℕ → ℂ) (x : ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) •
    ∫ t in (-(T0 x))..(T0 x),
      (polynomial a x).eval χ (half t) * (x : ℂ) ^ (half t - 1)

/-- LEAF. OPEN. Page 25 display 4.3, truncated Perron error only.
The endpoints are arbitrary real endpoints. Endpoint terms are absorbed in the
stated error. Reference 10 page 1372, display 16, is the cited divisor sum step. -/
theorem perron_error {ε B : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 20)
    (a : ℝ → ℕ → ℂ) (ha : ∀ x k, ‖a x k‖ ≤ tau k ^ B) :
    ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ y : ℝ, 2 ≤ y → y ≤ y1 x →
        ‖window a x y χ - truncated a x y (T1 ε x) χ‖ ≤
          C * (x ^ (1 + ε / 4) / T1 ε x) := by
  sorry

/-- Page 25, finite Dirichlet polynomial evaluation is continuous in real height. -/
theorem eval_continuous {q : ℕ} (P : DP) (χ : DirichletCharacter ℂ q) :
    Continuous fun t : ℝ => P.eval χ (half t) := by
  unfold DP.eval
  apply continuous_finsetSum
  intro n hn
  have hc : Continuous fun t : ℝ => -(half t) := by dsimp [half]; fun_prop
  have hp : Continuous fun t : ℝ => (n : ℂ) ^ (-(half t)) :=
    hc.const_cpow (Or.inr (fun t => by
      intro h
      have hh := congrArg Complex.re h
      norm_num [half] at hh))
  exact continuous_const.mul hp

/-- Page 25, the window kernel is continuous in real height for positive endpoints. -/
theorem kernel_continuous {x y : ℝ} (hx : 0 < x) (hxy : 0 < x - y) :
    Continuous (kernel x y) := by
  have hc : Continuous fun t : ℝ => half t := by dsimp [half]; fun_prop
  exact ((hc.const_cpow (Or.inl (by exact_mod_cast hx.ne'))).sub
    (hc.const_cpow (Or.inl (by exact_mod_cast hxy.ne')))).div hc (fun t => by
      intro h
      have hh := congrArg Complex.re h
      norm_num [half] at hh)

/-- Page 25, express the window kernel as an integral of its power derivative. -/
theorem kernel_integral (x y t : ℝ) :
    kernel x y t = ∫ u in (x - y)..x, (u : ℂ) ^ (half t - 1) := by
  rw [integral_cpow (Or.inl (by norm_num [half] : -1 < (half t - 1).re))]
  simp only [sub_add_cancel]
  rfl

/-- Page 25, the high height kernel has a bound independent of height. -/
theorem kernel_norm_le {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x / 2)
    (t : ℝ) : ‖kernel x y t‖ ≤ 2 * y * x ^ (-1 / 2 : ℝ) := by
  have hxy : x - y ≤ x := by linarith
  have hxy0 : 0 < x - y := by linarith
  have hfour : (4 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 2 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
    norm_num
  have hp : (x / 4) ^ (-1 / 2 : ℝ) = 2 * x ^ (-1 / 2 : ℝ) := by
    rw [Real.div_rpow hx.le (by norm_num), hfour]
    ring
  rw [kernel_integral]
  have hnorm : ∀ u ∈ Set.Icc (x - y) x,
      ‖(u : ℂ) ^ (half t - 1)‖ ≤ 2 * x ^ (-1 / 2 : ℝ) := by
    intro u hu
    have hu0 : 0 < u := hxy0.trans_le hu.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (half t - 1).re = -1 / 2 := by norm_num [half]
    rw [hre, ← hp]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hu.1]) (by norm_num)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := x - y) (b := x)
    (fun u hu => hnorm u (by
      rw [Set.uIoc_of_le hxy] at hu
      exact ⟨hu.1.le, hu.2⟩))
  convert hh using 1
  rw [abs_of_nonneg (by linarith : 0 ≤ x - (x - y))]
  ring

/-- Page 25, the second order kernel remainder before 4.4.
The constant eight is an implementation bound, not a printed constant. -/
theorem kernel_taylor {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x / 2)
    (t : ℝ) :
    ‖kernel x y t - (y : ℂ) * (x : ℂ) ^ (half t - 1)‖ ≤
      8 * (|t| + 1) * y ^ 2 * x ^ (-3 / 2 : ℝ) := by
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (half t - 1)
  let f' : ℝ → ℂ := fun u => (half t - 1) * (u : ℂ) ^ (half t - 1 - 1)
  have hxy : x - y ≤ x := by linarith
  have hxy0 : 0 < x - y := by linarith
  have hder : ∀ u ∈ Set.Icc (x - y) x, HasDerivAt f (f' u) u := by
    intro u hu
    apply hasDerivAt_ofReal_cpow_const (hxy0.trans_le hu.1).ne'
    intro he
    have hh := congrArg Complex.re he
    norm_num [half] at hh
  have hcoeff : ‖half t - 1‖ ≤ |t| + 1 := by
    have he : half t - 1 = (-1 / 2 : ℂ) + (t : ℂ) * Complex.I := by unfold half; ring
    rw [he]
    calc
      _ ≤ ‖(-1 / 2 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ _ := by simp [Real.norm_eq_abs]; linarith
  have hfour : (4 : ℝ) ^ (-3 / 2 : ℝ) = 1 / 8 := by
    rw [show (-3 / 2 : ℝ) = (-1 / 2 : ℝ) + (-1) by ring,
      Real.rpow_add (by norm_num),
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow,
      Real.rpow_neg_one]
    norm_num
  have hp : (x / 4) ^ (-3 / 2 : ℝ) = 8 * x ^ (-3 / 2 : ℝ) := by
    rw [Real.div_rpow hx.le (by norm_num), hfour]
    ring
  let D : ℝ := 8 * (|t| + 1) * x ^ (-3 / 2 : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdb : ∀ u ∈ Set.Icc (x - y) x, ‖f' u‖ ≤ D := by
    intro u hu
    have hu0 : 0 < u := hxy0.trans_le hu.1
    dsimp [f', D]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (half t - 1 - 1).re = -3 / 2 := by norm_num [half]
    rw [hre]
    have hu : u ^ (-3 / 2 : ℝ) ≤ 8 * x ^ (-3 / 2 : ℝ) := by
      rw [← hp]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hu.1]) (by norm_num)
    calc
      _ ≤ (|t| + 1) * (8 * x ^ (-3 / 2 : ℝ)) :=
        mul_le_mul hcoeff hu (by positivity) (by positivity)
      _ = _ := by ring
  have hdiff : ∀ u ∈ Set.Icc (x - y) x, ‖f u - f x‖ ≤ D * y := by
    intro u hu
    have hsub : Set.Icc u x ⊆ Set.Icc (x - y) x := fun z hz => ⟨hu.1.trans hz.1, hz.2⟩
    have hb := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun z hz => (hder z (hsub hz)).hasDerivWithinAt)
      (fun z hz => hdb z (hsub ⟨hz.1, hz.2.le⟩)) x ⟨hu.2, le_rfl⟩
    rw [norm_sub_rev] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (by linarith [hu.1]) hD)
  have hfi : IntervalIntegrable f volume (x - y) x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxy]
    exact fun u hu => (hder u hu).continuousAt.continuousWithinAt
  have heq : kernel x y t - (y : ℂ) * (x : ℂ) ^ (half t - 1) =
      ∫ u in (x - y)..x, (f u - f x) := by
    rw [intervalIntegral.integral_sub hfi intervalIntegrable_const,
      intervalIntegral.integral_const, ← kernel_integral]
    congr 1
    simp [f, Complex.real_smul]
  rw [heq]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := x - y) (b := x)
    (fun u hu => hdiff u (by rw [Set.uIoc_of_le hxy] at hu; exact ⟨hu.1.le, hu.2⟩))
  refine hh.trans ?_
  rw [abs_of_nonneg (by linarith : 0 ≤ x - (x - y))]
  dsimp [D]
  ring_nf
  rfl

/-- Page 25 display 4.4 with a pointwise polynomial envelope left explicit. -/
theorem low_height_control {q : ℕ} (a : ℝ → ℕ → ℂ)
    (x y T M : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x / 2) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hP : ∀ t : ℝ, |t| ≤ T → ‖(polynomial a x).eval χ (half t)‖ ≤ M) :
    ‖truncated a x y T χ - (y : ℂ) *
      ((1 / (2 * Real.pi) : ℝ) • ∫ t in (-T)..T,
        (polynomial a x).eval χ (half t) * (x : ℂ) ^ (half t - 1))‖ ≤
      32 * M * T ^ 2 * y ^ 2 * x ^ (-3 / 2 : ℝ) := by
  let P : ℝ → ℂ := fun t => (polynomial a x).eval χ (half t)
  let f : ℝ → ℂ := fun t => P t * kernel x y t
  let g : ℝ → ℂ := fun t => P t * (x : ℂ) ^ (half t - 1)
  have hcP : Continuous P := eval_continuous _ _
  have hcK : Continuous (kernel x y) := kernel_continuous hx (by linarith)
  have hcE : Continuous fun t : ℝ => (x : ℂ) ^ (half t - 1) := by
    have hc : Continuous fun t : ℝ => half t - 1 := by dsimp [half]; fun_prop
    exact hc.const_cpow (Or.inl (by exact_mod_cast hx.ne'))
  have hfi : IntervalIntegrable f volume (-T) T := (hcP.mul hcK).intervalIntegrable _ _
  have hgi : IntervalIntegrable g volume (-T) T := (hcP.mul hcE).intervalIntegrable _ _
  have heq : truncated a x y T χ - (y : ℂ) *
      ((1 / (2 * Real.pi) : ℝ) • ∫ t in (-T)..T, g t) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t in (-T)..T, (f t - (y : ℂ) * g t) := by
    rw [intervalIntegral.integral_sub hfi (hgi.const_mul _),
      intervalIntegral.integral_const_mul, smul_sub]
    simp only [truncated, f, g, P, Complex.real_smul]
    ring
  have hb : ∀ t ∈ Set.uIoc (-T) T,
      ‖f t - (y : ℂ) * g t‖ ≤ M * (8 * (T + 1) * y ^ 2 * x ^ (-3 / 2 : ℝ)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -T ≤ T)] at ht
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have he : f t - (y : ℂ) * g t =
        P t * (kernel x y t - (y : ℂ) * (x : ℂ) ^ (half t - 1)) := by dsimp [f, g]; ring
    rw [he, norm_mul]
    have hk := kernel_taylor hx hy hyx t
    have hk' : ‖kernel x y t - (y : ℂ) * (x : ℂ) ^ (half t - 1)‖ ≤
        8 * (T + 1) * y ^ 2 * x ^ (-3 / 2 : ℝ) := by
      refine hk.trans ?_
      gcongr
    exact mul_le_mul (hP t htT) hk' (norm_nonneg _) hM
  change ‖truncated a x y T χ - (y : ℂ) *
    ((1 / (2 * Real.pi) : ℝ) • ∫ t in (-T)..T, g t)‖ ≤ _
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hπ : 1 / (2 * Real.pi) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [Real.pi_gt_three])
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
  have hTnonneg : 0 ≤ T := by linarith
  have hstrip : 0 ≤ T - -T := by linarith
  have hbudget : 0 ≤ M * y ^ 2 * x ^ (-3 / 2 : ℝ) := by positivity
  have hTT : T * (T + 1) ≤ 2 * T ^ 2 := by nlinarith
  calc
    _ ≤ 1 * (M * (8 * (T + 1) * y ^ 2 * x ^ (-3 / 2 : ℝ)) * (T - -T)) :=
      mul_le_mul_of_nonneg_right hπ (by positivity)
    _ = 16 * (M * y ^ 2 * x ^ (-3 / 2 : ℝ)) * (T * (T + 1)) := by ring
    _ ≤ 16 * (M * y ^ 2 * x ^ (-3 / 2 : ℝ)) * (2 * T ^ 2) :=
      mul_le_mul_of_nonneg_left hTT (by positivity)
    _ = _ := by ring

/-- LEAF. Page 25, the high height kernel estimate between 4.3 and 4.4.
The constant one is a conservative implementation bound after the factor two pi.
This is an integral comparison for one polynomial, with no distribution claim. -/
theorem high_height_error {q : ℕ} (a : ℝ → ℕ → ℂ)
    (x y U V : ℝ) (χ : DirichletCharacter ℂ q)
    (hx : 0 < x) (hy : 0 ≤ y) (hyx : y ≤ x / 2)
    (_hU : 0 ≤ U) (hUV : U ≤ V) :
    ‖truncated a x y V χ - truncated a x y U χ‖ ≤
      y * x ^ (-1 / 2 : ℝ) *
        ((∫ t in U..V, ‖(polynomial a x).eval χ (half t)‖) +
         (∫ t in U..V, ‖(polynomial a x).eval χ (half (-t))‖)) := by
  let f : ℝ → ℂ := fun t => (polynomial a x).eval χ (half t) * kernel x y t
  have hxy : 0 < x - y := by linarith
  have hc : Continuous f := (eval_continuous (polynomial a x) χ).mul (kernel_continuous hx hxy)
  have hfi (r s : ℝ) : IntervalIntegrable f volume r s := hc.intervalIntegrable _ _
  have hleft := integral_add_adjacent_intervals (hfi (-V) (-U)) (hfi (-U) U)
  have hright := integral_add_adjacent_intervals (hfi (-V) U) (hfi U V)
  have hsplit : (∫ t in (-V)..V, f t) - (∫ t in (-U)..U, f t) =
      (∫ t in (-V)..(-U), f t) + (∫ t in U..V, f t) := by
    rw [← hright, ← hleft]
    abel
  have hneg : (∫ t in (-V)..(-U), f t) = ∫ t in U..V, f (-t) := by
    rw [integral_comp_neg]
  have hbound : ∀ t : ℝ, ‖f t‖ ≤
      (2 * y * x ^ (-1 / 2 : ℝ)) * ‖(polynomial a x).eval χ (half t)‖ := by
    intro t
    dsimp [f]
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (kernel_norm_le hx hy hyx t) (norm_nonneg _)
  have hp : ‖∫ t in U..V, f t‖ ≤ (2 * y * x ^ (-1 / 2 : ℝ)) *
      ∫ t in U..V, ‖(polynomial a x).eval χ (half t)‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hUV).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on hUV (hc.norm.intervalIntegrable U V)
      ((continuous_const.mul (eval_continuous (polynomial a x) χ).norm).intervalIntegrable _ _)
      (fun t _ => hbound t)
  have hn : ‖∫ t in U..V, f (-t)‖ ≤ (2 * y * x ^ (-1 / 2 : ℝ)) *
      ∫ t in U..V, ‖(polynomial a x).eval χ (half (-t))‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hUV).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    exact integral_mono_on hUV ((hc.comp continuous_neg).norm.intervalIntegrable U V)
      ((continuous_const.mul ((eval_continuous (polynomial a x) χ).comp continuous_neg).norm).intervalIntegrable _ _)
      (fun t _ => hbound (-t))
  have hI : 0 ≤ (∫ t in U..V, ‖(polynomial a x).eval χ (half t)‖) +
      (∫ t in U..V, ‖(polynomial a x).eval χ (half (-t))‖) := by
    exact add_nonneg (integral_nonneg hUV (fun _ _ => norm_nonneg _))
      (integral_nonneg hUV (fun _ _ => norm_nonneg _))
  change ‖(1 / (2 * Real.pi) : ℝ) • (∫ t in (-V)..V, f t) -
    (1 / (2 * Real.pi) : ℝ) • (∫ t in (-U)..U, f t)‖ ≤ _
  rw [← smul_sub, hsplit, hneg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hn hp))
    (by positivity)).trans ?_
  have hpi : 1 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (le_trans (by norm_num : (1 : ℝ) ≤ 3) Real.pi_gt_three.le)
  calc
    _ = (1 / Real.pi) * (y * x ^ (-1 / 2 : ℝ) *
      ((∫ t in U..V, ‖(polynomial a x).eval χ (half t)‖) +
       (∫ t in U..V, ‖(polynomial a x).eval χ (half (-t))‖))) := by ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi
        (mul_nonneg (by positivity : 0 ≤ y * x ^ (-1 / 2 : ℝ)) hI)


/-- Page 25, exact exponent in the remainder of 4.5. -/
theorem truncation_scale {ε x : ℝ} (hx : 0 < x) :
    x ^ (1 + ε / 4) / T1 ε x = x ^ (0.55 + 11 * ε / 12) := by
  rw [T1, ← Real.rpow_sub hx]
  congr 1
  ring

/-- Page 25, cancellation of the common density in two window approximations. -/
theorem cancel_density {S R E : ℂ} {y z d r C : ℝ}
    (hy : 0 ≤ y) (hz : 0 < z) (hyz : y ≤ z)
    (_hd : 0 ≤ d) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hS : ‖S - (y : ℂ) * E‖ ≤ C * (y * d + r))
    (hR : ‖R - (z : ℂ) * E‖ ≤ C * (z * d + r)) :
    ‖S - ((y / z : ℝ) : ℂ) * R‖ ≤ (2 * C) * (y * d + r) := by
  have he : S - ((y / z : ℝ) : ℂ) * R =
      (S - (y : ℂ) * E) - ((y / z : ℝ) : ℂ) * (R - (z : ℂ) * E) := by
    push_cast
    field_simp [show (z : ℂ) ≠ 0 by exact_mod_cast hz.ne']
    ring
  have hratio : 0 ≤ y / z := div_nonneg hy hz.le
  have hratio1 : y / z ≤ 1 := (div_le_one hz).mpr hyz
  rw [he]
  calc
    _ ≤ ‖S - (y : ℂ) * E‖ + ‖((y / z : ℝ) : ℂ) * (R - (z : ℂ) * E)‖ := norm_sub_le _ _
    _ = ‖S - (y : ℂ) * E‖ + (y / z) * ‖R - (z : ℂ) * E‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hratio]
    _ ≤ C * (y * d + r) + (y / z) * (C * (z * d + r)) :=
      add_le_add hS (mul_le_mul_of_nonneg_left hR hratio)
    _ ≤ (2 * C) * (y * d + r) := by
      have heq : (y / z) * (C * (z * d + r)) = C * (y * d + (y / z) * r) := by
        field_simp [hz.ne']
      rw [heq]
      have := mul_le_mul_of_nonneg_right hratio1 hr
      nlinarith

/-- Page 25, the ranges needed to split the vertical integral hold eventually. -/
theorem eventual_geometry {ε : ℝ} (hε : ε < 1 / 20) :
    Ev fun x => 1 < x ∧ y1 x ≤ x / 2 ∧ T0 x ≤ T1 ε x := by
  have hs : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (-(2 / 3 : ℝ)) < 1 / 4 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      Real.tendsto_log_atTop).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hg : ∀ᶠ x : ℝ in atTop, 1 < x ∧ y1 x ≤ x / 2 ∧ T0 x ≤ T1 ε x := by
    filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1, hs]
      with x hx hL hsx
    have hx0 : 0 < x := by linarith
    have hL0 : 0 < Real.log x := by linarith
    have hroot : Real.log x ^ (1 / 3 : ℝ) =
        Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
      calc
        _ = Real.log x ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := by congr 1; norm_num
        _ = _ := by rw [Real.rpow_add hL0, Real.rpow_one]
    have hrootup : Real.log x ^ (1 / 3 : ℝ) ≤ Real.log x / 4 := by
      rw [hroot]
      nlinarith
    have hrootlo : 1 ≤ Real.log x ^ (1 / 3 : ℝ) :=
      Real.one_le_rpow hL (by norm_num)
    have hexp : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) ≤ 1 / 2 := by
      have he : 2 ≤ Real.exp (3 * Real.log x ^ (1 / 3 : ℝ)) := by
        have := Real.add_one_le_exp (3 * Real.log x ^ (1 / 3 : ℝ))
        linarith
      rw [show -3 * Real.log x ^ (1 / 3 : ℝ) =
        -(3 * Real.log x ^ (1 / 3 : ℝ)) by ring, Real.exp_neg]
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he
    refine ⟨hx, ?_, ?_⟩
    · dsimp [y1]
      nlinarith
    · dsimp [T0, T1, L]
      rw [Real.rpow_def_of_pos hx0]
      apply Real.exp_le_exp.mpr
      nlinarith
  exact (eventually_atTop.1 hg)

/-- Page 25, exponential decay in the low height error absorbs every log power. -/
theorem logarithmic_decay (C D A : ℝ) :
    Ev fun x => 0 < L x ∧ 32 * |C| * L x ^ (A + D) *
      Real.exp (-(L x ^ (1 / 3 : ℝ))) ≤ 1 := by
  have hroot : Tendsto (fun x : ℝ => L x ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp Real.tendsto_log_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3 * (A + D)) 1 (by norm_num)).comp hroot
  have hscaled : Tendsto (fun x : ℝ => 32 * |C| *
      ((L x ^ (1 / 3 : ℝ)) ^ (3 * (A + D)) * Real.exp (-1 * L x ^ (1 / 3 : ℝ))))
      atTop (𝓝 (32 * |C| * 0)) := tendsto_const_nhds.mul hlim
  have he : ∀ᶠ x : ℝ in atTop,
      32 * |C| * ((L x ^ (1 / 3 : ℝ)) ^ (3 * (A + D)) *
        Real.exp (-1 * L x ^ (1 / 3 : ℝ))) ≤ 1 := by
    exact (show Tendsto (fun x : ℝ => 32 * |C| *
      ((L x ^ (1 / 3 : ℝ)) ^ (3 * (A + D)) * Real.exp (-1 * L x ^ (1 / 3 : ℝ))))
      atTop (𝓝 0) from by simpa using hscaled).eventually_le_const (by norm_num)
  apply eventually_atTop.1
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0, he] with x hx he
  have hL : 0 < L x := hx
  refine ⟨hL, ?_⟩
  have hp : (L x ^ (1 / 3 : ℝ)) ^ (3 * (A + D)) = L x ^ (A + D) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    ring
  simpa only [hp, neg_one_mul, mul_assoc] using he

/-- LEAF. OPEN. Page 25, the divisor mean estimate underlying the coefficient envelope.
Reference 10 page 1372 uses its Lemma 2 to obtain the logarithmic envelope.
This is the elementary real divisor moment consequence. It has no characters,
complex powers, contour integrals or short interval distribution conclusion. -/
theorem divisor_moment (B : ℝ) :
    ∃ D : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ k ∈ Finset.Icc 1 N, tau k ^ B) ≤
        C * N * (1 + Real.log N) ^ D := by
  sorry

/-- LEAF. Page 25, unnumbered coefficient envelope before the kernel display.
Reference 10 page 1372 derives the corresponding envelope from its divisor mean
estimate. CONDITIONAL ON divisor_moment. This is only a coefficient sum estimate, with no Perron kernel,
short interval transfer or mean value hypothesis. -/
theorem polynomial_envelope (B : ℝ) (a : ℝ → ℕ → ℂ)
    (ha : ∀ x k, ‖a x k‖ ≤ tau k ^ B) :
    ∃ D C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ),
        ‖(polynomial a x).eval χ (half t)‖ ≤ C * x ^ (1 / 2 : ℝ) * L x ^ D := by
  obtain ⟨D, K, hK, hsum⟩ := divisor_moment B
  refine ⟨D, 4 * K * (4 : ℝ) ^ D, max 2 (Real.exp 1), by positivity, ?_⟩
  intro x hx q inst χ t
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ L x := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hx)
    simpa only [Real.log_exp, L] using hh
  have hL0 : 0 < L x := by linarith
  let N : ℕ := ⌊2 * x⌋₊
  have hN : 1 ≤ N := (Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).mpr (by norm_num; linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNx : (N : ℝ) ≤ 2 * x := Nat.floor_le (by positivity)
  have hlogN : Real.log N ≤ Real.log (2 * x) := Real.log_le_log hN0 hNx
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hbase : 1 + Real.log N ≤ 4 * L x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hlogN
    have hh : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    dsimp [L] at hlog ⊢
    linarith
  have hpow : (1 + Real.log N) ^ D ≤ (4 * L x) ^ D :=
    pow_le_pow_left₀ (by linarith) hbase _
  have hsubset : (polynomial a x).supp ⊆ Finset.Icc 1 N := by
    intro k hk
    have hkk := Finset.mem_Ioc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, hkk.2⟩
  have hterm : ∀ k ∈ (polynomial a x).supp,
      ‖(polynomial a x).coef k * χ (k : ZMod q) * (k : ℂ) ^ (-(half t))‖ ≤
        (2 * x ^ (-1 / 2 : ℝ)) * tau k ^ B := by
    intro k hk
    have hkN := Finset.mem_Icc.mp (hsubset hk)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hkN.1)
    have hkx : x / 2 < (k : ℝ) := by
      exact (Nat.floor_lt (by positivity : 0 ≤ x / 2)).mp (Finset.mem_Ioc.mp hk).1
    have hfour : (4 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 2 := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
      norm_num
    have hpower : (k : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 * x ^ (-1 / 2 : ℝ) := by
      have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < x / 4)
        (show x / 4 ≤ k by linarith) (by norm_num : (-1 / 2 : ℝ) ≤ 0)
      rw [Real.div_rpow hx0.le (by norm_num), hfour] at hh
      nlinarith only [hh]
    have hknorm : ‖(k : ℂ) ^ (-(half t))‖ = (k : ℝ) ^ (-1 / 2 : ℝ) := by
      have he : (k : ℂ) = ((k : ℝ) : ℂ) := by norm_num
      rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hk0]
      congr 1
      norm_num [half]
    rw [norm_mul, norm_mul, hknorm]
    have htau : 0 ≤ tau k ^ B := Real.rpow_nonneg (by simp [tau]) _
    have hcoef := ha x k
    have hchar := DirichletCharacter.norm_le_one χ (k : ZMod q)
    change ‖a x k‖ * ‖χ (k : ZMod q)‖ * (k : ℝ) ^ (-1 / 2 : ℝ) ≤ _
    calc
      _ ≤ tau k ^ B * 1 * (2 * x ^ (-1 / 2 : ℝ)) :=
        mul_le_mul (mul_le_mul hcoef hchar (norm_nonneg _) (by positivity)) hpower
          (by positivity) (by positivity)
      _ = _ := by ring
  have hmoment := hsum N hN
  have hbound : (∑ k ∈ (polynomial a x).supp, tau k ^ B) ≤
      K * (2 * x) * ((4 * L x) ^ D) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N, tau k ^ B :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Real.rpow_nonneg (by simp [tau]) _)
      _ ≤ K * N * (1 + Real.log N) ^ D := hmoment
      _ ≤ _ := by gcongr
  have hcancel : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
    calc
      _ = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-1 / 2 : ℝ) + 1) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by congr 1; norm_num
  calc
    _ ≤ ∑ k ∈ (polynomial a x).supp,
        ‖(polynomial a x).coef k * χ (k : ZMod q) * (k : ℂ) ^ (-(half t))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ (polynomial a x).supp, (2 * x ^ (-1 / 2 : ℝ)) * tau k ^ B :=
      Finset.sum_le_sum hterm
    _ = (2 * x ^ (-1 / 2 : ℝ)) * ∑ k ∈ (polynomial a x).supp, tau k ^ B := by rw [Finset.mul_sum]
    _ ≤ (2 * x ^ (-1 / 2 : ℝ)) * (K * (2 * x) * ((4 * L x) ^ D)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      rw [mul_pow, Real.rpow_natCast]
      calc
        _ = (4 * K * (4 : ℝ) ^ D) * (x ^ (-1 / 2 : ℝ) * x) * L x ^ D := by ring
        _ = _ := by rw [hcancel]


/-- LEAF. Page 25 display 4.4, low height linearization only.
The conclusion has no mean value hypothesis and retains the explicit common E.
CONDITIONAL ON polynomial_envelope only. -/
theorem low_height_error (B : ℝ) (a : ℝ → ℕ → ℂ)
    (ha : ∀ x k, ‖a x k‖ ≤ tau k ^ B) :
    ∀ A : ℝ, 0 < A → ∃ C X : ℝ, 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      ∀ y : ℝ, 2 ≤ y → y ≤ y1 x →
        ‖truncated a x y (T0 x) χ - (y : ℂ) * density a x χ‖ ≤
          C * (y / L x ^ A) := by
  obtain ⟨D, K, Xp, hK, hp⟩ := polynomial_envelope B a ha
  intro A hA
  obtain ⟨Xd, hd⟩ := logarithmic_decay K D A
  obtain ⟨Xg, hg⟩ := eventual_geometry (ε := 0) (by norm_num)
  refine ⟨1, max Xp (max Xd Xg), by norm_num, ?_⟩
  intro x hx q inst χ y hy hymax
  have hxp := (le_max_left Xp (max Xd Xg)).trans hx
  have hxd := (le_max_left Xd Xg).trans ((le_max_right Xp (max Xd Xg)).trans hx)
  have hxg := (le_max_right Xd Xg).trans ((le_max_right Xp (max Xd Xg)).trans hx)
  obtain ⟨hL, hdec⟩ := hd x hxd
  obtain ⟨hx1, hyhalf, _⟩ := hg x hxg
  have hx0 : 0 < x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos hL _
  have hT : 1 ≤ T0 x := Real.one_le_exp (Real.rpow_nonneg hL.le _)
  have hh := low_height_control a x y (T0 x)
    (K * x ^ (1 / 2 : ℝ) * L x ^ D) χ hx0 hy0 (hymax.trans hyhalf) hT
    (by positivity) (fun t _ => hp x hxp q χ t)
  change ‖truncated a x y (T0 x) χ - (y : ℂ) * density a x χ‖ ≤ _ at hh
  have hpow : x ^ (1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ) = x⁻¹ := by
    rw [← Real.rpow_add hx0]
    norm_num [Real.rpow_neg_one]
  have hyy : y1 x / x = Real.exp (-3 * L x ^ (1 / 3 : ℝ)) := by
    dsimp [y1, L]
    field_simp
  have hcancel : T0 x ^ 2 * (y1 x / x) = Real.exp (-(L x ^ (1 / 3 : ℝ))) := by
    rw [hyy, T0, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [abs_of_nonneg hK] at hdec
  have hcoef : 32 * K * L x ^ D * Real.exp (-(L x ^ (1 / 3 : ℝ))) ≤ 1 / L x ^ A := by
    apply (le_div_iff₀ hLA).mpr
    calc
      _ = 32 * K * L x ^ (A + D) * Real.exp (-(L x ^ (1 / 3 : ℝ))) := by
        rw [Real.rpow_add hL]
        ring
      _ ≤ 1 := hdec
  refine hh.trans ?_
  calc
    _ = 32 * K * L x ^ D * T0 x ^ 2 * y ^ 2 *
        (x ^ (1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ)) := by ring
    _ = 32 * K * L x ^ D * T0 x ^ 2 * (y ^ 2 / x) := by rw [hpow]; ring
    _ ≤ 32 * K * L x ^ D * T0 x ^ 2 * (y * y1 x / x) := by
      gcongr
      nlinarith
    _ = y * (32 * K * L x ^ D * (T0 x ^ 2 * (y1 x / x))) := by ring
    _ = y * (32 * K * L x ^ D * Real.exp (-(L x ^ (1 / 3 : ℝ)))) := by rw [hcancel]
    _ ≤ y * (1 / L x ^ A) := mul_le_mul_of_nonneg_left hcoef hy0
    _ = _ := by ring

/-- Page 25 display 4.5, from the three smaller analytic steps and both signs of 4.1.
CONDITIONAL ON perron_error and divisor_moment. The other steps have real proofs.
No cited Lemma11 declaration is used. -/
theorem lemma11_decomposed : Lemma11 := by
  refine ⟨1 / 20, by norm_num, ?_⟩
  intro ε hε hεsmall B a ha hmean
  obtain ⟨Cp, Xp, hCp, hp⟩ := perron_error hε hεsmall a ha
  obtain ⟨Xg, hg⟩ := eventual_geometry hεsmall
  intro A hA
  obtain ⟨Cl, Xl, hCl, hl⟩ := low_height_error B a ha A hA
  obtain ⟨Cm, Xm, hm⟩ := hmean A hA
  let C := Cp + Cl + 2 * |Cm|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨2 * C, max Xp (max Xg (max Xl Xm)), ?_⟩
  intro x hx q inst hq χ y hy hymax
  have hxp : Xp ≤ x := (le_max_left _ _).trans hx
  have hxg : Xg ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxl : Xl ≤ x := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hxm : Xm ≤ x := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  obtain ⟨hx1, hyhalf, hT⟩ := hg x hxg
  have hx0 : 0 < x := by linarith
  have hL : 0 < L x := Real.log_pos hx1
  have hLA : 0 < L x ^ A := Real.rpow_pos_of_pos hL _
  have hT0 : 0 ≤ T0 x := (Real.exp_pos _).le
  have hmain : ∀ z : ℝ, 2 ≤ z → z ≤ y1 x →
      ‖window a x z χ - (z : ℂ) * density a x χ‖ ≤
        C * (z / L x ^ A + x ^ (0.55 + 11 * ε / 12)) := by
    intro z hz hzmax
    have hz0 : 0 ≤ z := by linarith
    have hpz := hp x hxp q χ z hz hzmax
    rw [truncation_scale hx0] at hpz
    have hlz := hl x hxl q χ z hz hzmax
    have hhz := high_height_error a x z (T0 x) (T1 ε x) χ
      hx0 hz0 (hzmax.trans hyhalf) hT0 hT
    obtain ⟨hmplus, hmminus⟩ := hm x hxm q hq χ
    change (∫ t in (T0 x)..(T1 ε x), ‖(polynomial a x).eval χ (half t)‖) ≤
      Cm * x ^ (1 / 2 : ℝ) / L x ^ A at hmplus
    change (∫ t in (T0 x)..(T1 ε x), ‖(polynomial a x).eval χ (half (-t))‖) ≤
      Cm * x ^ (1 / 2 : ℝ) / L x ^ A at hmminus
    have hmabs : Cm * x ^ (1 / 2 : ℝ) / L x ^ A ≤
        |Cm| * x ^ (1 / 2 : ℝ) / L x ^ A := by
      gcongr
      exact le_abs_self Cm
    have hxpow : x ^ (-1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hh : ‖truncated a x z (T1 ε x) χ - truncated a x z (T0 x) χ‖ ≤
        (2 * |Cm|) * (z / L x ^ A) := by
      refine hhz.trans ?_
      calc
        _ ≤ z * x ^ (-1 / 2 : ℝ) *
            (|Cm| * x ^ (1 / 2 : ℝ) / L x ^ A +
             |Cm| * x ^ (1 / 2 : ℝ) / L x ^ A) :=
          mul_le_mul_of_nonneg_left (add_le_add (hmplus.trans hmabs) (hmminus.trans hmabs))
            (by positivity)
        _ = (2 * |Cm|) * (z / L x ^ A) *
            (x ^ (-1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hxpow, mul_one]
    have ht := norm_sub_le_norm_sub_add_norm_sub (window a x z χ)
      (truncated a x z (T1 ε x) χ) ((z : ℂ) * density a x χ)
    have ht' := norm_sub_le_norm_sub_add_norm_sub (truncated a x z (T1 ε x) χ)
      (truncated a x z (T0 x) χ) ((z : ℂ) * density a x χ)
    have hr : 0 ≤ x ^ (0.55 + 11 * ε / 12) := Real.rpow_nonneg hx0.le _
    have hd : 0 ≤ z / L x ^ A := div_nonneg hz0 hLA.le
    have htotal := ht.trans (add_le_add hpz (ht'.trans (add_le_add hh hlz)))
    refine htotal.trans ?_
    dsimp [C]
    nlinarith [mul_nonneg hCp hd, mul_nonneg hCl hr, mul_nonneg (abs_nonneg Cm) hr]
  have hy1pos : 0 < y1 x := by linarith
  have hy1two : 2 ≤ y1 x := hy.trans hymax
  have hs := hmain y hy hymax
  have hr := hmain (y1 x) hy1two le_rfl
  have hc := cancel_density (by linarith : 0 ≤ y) hy1pos hymax
    (by positivity : 0 ≤ (L x ^ A)⁻¹)
    (Real.rpow_nonneg hx0.le (0.55 + 11 * ε / 12)) hC
    (by simpa only [div_eq_mul_inv] using hs)
    (by simpa only [div_eq_mul_inv] using hr)
  simpa only [window, div_eq_mul_inv] using hc

#print axioms polynomial
#print axioms window
#print axioms kernel
#print axioms truncated
#print axioms density
#print axioms perron_error
#print axioms divisor_moment
#print axioms polynomial_envelope
#print axioms logarithmic_decay
#print axioms low_height_error
#print axioms eval_continuous
#print axioms kernel_continuous
#print axioms kernel_integral
#print axioms kernel_norm_le
#print axioms kernel_taylor
#print axioms low_height_control
#print axioms high_height_error
#print axioms truncation_scale
#print axioms cancel_density
#print axioms eventual_geometry
#print axioms lemma11_decomposed

end LeanLab.BakerHarmanPintz1997.Decomp409a
