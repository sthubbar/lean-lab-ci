import Mathlib

/-!
PREP 2026-11-22, burst-20261122 unit P1122-0077: split of the cited leaf
`Prep1121VIPointwiseA.binet_formula`, Binet's second formula for the digamma function,
OLBC10 DLMF 5.9.15, quoted by P0014 Helfgott, Major arcs for Goldbach's problem,
arXiv 1305.2897v4, page 34, display 4.10, first line.

Route: DLMF 5.9.13 writes ψ(z) - ln z as a Laplace transform of 1/t - 1/(1 - e^{-t}).
That kernel equals -1/2 - 2 ∫_0^∞ sin(tτ)/(e^{2πτ} - 1) dτ by GR00 3.911.2 at β = 2π,
and the Laplace transform of sin(tτ) in t is τ/(τ² + z²). Fubini then gives DLMF 5.9.15.
`binet_formula` is assembled here with the exact statement of the parent leaf. The two
former LEAFs, `digamma_log_laplace` and `sine_planck`, are PROVED below, burst-20261122 S9;
the digamma series in section DigammaLaplace1122b is copied from the private development in
RamareSaouter2003/Decomp419c.lean, lines 303 to 797, renamed with suffix 1122b. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1122BinetSplit
open Complex MeasureTheory Set

section DigammaLaplace1122b
open Filter
open scoped Topology

section Series1122b
open Real

private theorem one_sub_pow_le_n_mul_1122b {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) :
    1 - b ^ n ≤ (n : ℝ) * (1 - b) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem0 : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb0, hb1⟩
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmono : MonotoneOn (fun t : ℝ => (1 - t ^ n) - (n : ℝ) * (1 - t)) (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · fun_prop
    · exact (by fun_prop : DifferentiableOn ℝ (fun t : ℝ => t ^ n) (interior (Set.Icc 0 1))).const_sub
        (1 : ℝ) |>.sub ((differentiableOn_const (c := (n : ℝ))).mul
          ((differentiableOn_const (c := (1 : ℝ))).sub differentiableOn_id))
    · intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
      have hderiv : deriv (fun t : ℝ => (1 - t ^ n) - (n : ℝ) * (1 - t)) x
          = (n : ℝ) - (n : ℝ) * x ^ (n - 1) := by
        have h1 : HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * x ^ (n - 1) * 1) x :=
          (hasDerivAt_id x).pow n
        have h2 : HasDerivAt (fun t : ℝ => 1 - t ^ n) (-((n : ℝ) * x ^ (n - 1) * 1)) x :=
          h1.const_sub 1
        have h3 : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have h4 : HasDerivAt (fun t : ℝ => (n : ℝ) * (1 - t)) ((n : ℝ) * (-1)) x :=
          h3.const_mul (n : ℝ)
        have h5 := h2.sub h4
        change deriv ((fun t : ℝ => 1 - t ^ n) - fun t : ℝ => (n : ℝ) * (1 - t)) x
          = (n : ℝ) - (n : ℝ) * x ^ (n - 1)
        rw [h5.deriv]
        ring
      rw [hderiv]
      have hle : x ^ (n - 1) ≤ 1 := pow_le_one₀ hx'.1 hx'.2
      nlinarith
  have h := hmono hmem0 hmem1 hb1
  simp only [one_pow] at h
  linarith

private theorem exp_le_two_of_le_half_1122b {x : ℝ} (hx : x ≤ 1 / 2) : Real.exp x ≤ 2 := by
  have h1 : Real.exp x ≤ Real.exp (1 / 2) := Real.exp_le_exp_of_le hx
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have hlt : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    calc Real.exp (1 / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp_of_le hlt
      _ = 2 := Real.exp_log (by norm_num)
  exact h1.trans h2

/-- `1 - v^2 ≤ exp v * (1 - v)` on `[0, 1/2]`. -/
private theorem one_sub_sq_le_exp_mul_1122b {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2) :
    1 - v ^ 2 ≤ Real.exp v * (1 - v) := by
  have hmono :
      MonotoneOn (fun t : ℝ => Real.exp t * (1 - t) - 1 + t ^ 2) (Set.Icc 0 (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    · fun_prop
    · intro x hx
      have he : DifferentiableWithinAt ℝ (fun t : ℝ => Real.exp t) (interior (Set.Icc 0 (1 / 2))) x :=
        Real.differentiableAt_exp.differentiableWithinAt
      have h1 : DifferentiableWithinAt ℝ (fun t : ℝ => 1 - t) (interior (Set.Icc 0 (1 / 2))) x := by
        fun_prop
      have h3 : DifferentiableWithinAt ℝ (fun t : ℝ => t ^ 2) (interior (Set.Icc 0 (1 / 2))) x := by
        fun_prop
      exact ((he.mul h1).sub_const 1).add h3
    · intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset hx
      have hderiv : deriv (fun t : ℝ => Real.exp t * (1 - t) - 1 + t ^ 2) x
          = x * (2 - Real.exp x) := by
        have he : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp x) x := Real.hasDerivAt_exp x
        have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have h2 : HasDerivAt (fun t : ℝ => Real.exp t * (1 - t))
            (Real.exp x * (1 - x) + Real.exp x * (-1)) x := he.mul h1
        have h3 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x ^ (2 - 1) * 1) x :=
          (hasDerivAt_id x).pow 2
        have h4 := (h2.sub_const 1).add h3
        change deriv (((fun x : ℝ => Real.exp x * (1 - x) - 1) + fun t : ℝ => t ^ 2)) x
          = x * (2 - Real.exp x)
        rw [h4.deriv]
        ring
      rw [hderiv]
      have hexp : Real.exp x ≤ 2 := exp_le_two_of_le_half_1122b hx'.2
      have hnn : 0 ≤ 2 - Real.exp x := by linarith
      exact mul_nonneg hx'.1 hnn
  have h := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩)
    (Set.mem_Icc.mpr ⟨hv0, hv⟩) hv0
  beta_reduce at h
  simp only [Real.exp_zero, pow_two, mul_zero, add_zero] at h
  linarith

/-- The reverse half of the exponential comparison, with the harmless constant `2`. -/
private theorem exp_neg_sub_one_sub_div_pow_le_1122b {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    Real.exp (-x) - (1 - x / n) ^ n ≤ 2 * x ^ 2 * Real.exp (-x) / n := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set v : ℝ := x / n with hv
  have hx_eq : x = (n : ℝ) * v := by
    rw [hv]; field_simp
  have hv0 : 0 ≤ v := by
    rw [hv]; positivity
  have hv1 : v ≤ 1 := by
    rw [hv, div_le_one hnpos]; exact_mod_cast hxn
  have hpow : (1 - x / n) ^ n = (1 - v) ^ n := by rw [hv]
  have hexp : Real.exp (-x) = (Real.exp (-v)) ^ n := by
    rw [hx_eq, show -((n : ℝ) * v) = (n : ℝ) * (-v) by ring, Real.exp_nat_mul]
  have hb0 : 0 ≤ Real.exp v * (1 - v) := by
    have h : 0 ≤ 1 - v := by linarith
    positivity
  have hb1 : Real.exp v * (1 - v) ≤ 1 := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := 1) (t := v) (by
      have hc : ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hc]; exact hv1)
    simp only [Nat.cast_one, div_one, pow_one] at h
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos v).le
    have h3 : Real.exp v * Real.exp (-v) = 1 := by
      rw [← Real.exp_add]; simp
    exact h2.trans_eq h3
  have hmul : Real.exp (-v) * Real.exp v = 1 := by
    rw [← Real.exp_add]; simp
  have hone : (Real.exp (-v)) ^ n * (Real.exp v) ^ n = 1 := by
    rw [← mul_pow, hmul, one_pow]
  have hkey : (Real.exp (-v)) ^ n - (1 - v) ^ n =
      (Real.exp (-v)) ^ n * (1 - (Real.exp v * (1 - v)) ^ n) := by
    rw [mul_pow, mul_sub, mul_one]
    have hassoc : (Real.exp (-v)) ^ n * ((Real.exp v) ^ n * (1 - v) ^ n) =
        ((Real.exp (-v)) ^ n * (Real.exp v) ^ n) * (1 - v) ^ n := by ring
    rw [hassoc, hone, one_mul]
  have hmain : Real.exp (-x) - (1 - x / n) ^ n =
      Real.exp (-x) * (1 - (Real.exp v * (1 - v)) ^ n) := by
    rw [hpow, hexp]
    exact hkey
  rw [hmain]
  have hstep : 1 - (Real.exp v * (1 - v)) ^ n ≤ 2 * (n : ℝ) * v ^ 2 := by
    rcases lt_or_ge (2 * (n : ℝ) * v ^ 2) 1 with hsmall | hbig
    · have hv2 : v ^ 2 < 1 / (2 * (n : ℝ)) := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
        nlinarith
      have hvhalf : v ≤ 1 / 2 := by
        have h4 : 1 / (2 * (n : ℝ)) ≤ 1 / 4 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          linarith
        have hv24 : v ^ 2 ≤ 1 / 4 := le_of_lt (lt_of_lt_of_le hv2 h4)
        nlinarith [sq_nonneg (v - 1 / 2)]
      have hb : 1 - v ^ 2 ≤ Real.exp v * (1 - v) := one_sub_sq_le_exp_mul_1122b hv0 hvhalf
      have h := one_sub_pow_le_n_mul_1122b hb0 hb1 n
      nlinarith
    · have hle1 : (Real.exp v * (1 - v)) ^ n ≤ 1 := pow_le_one₀ hb0 hb1
      have hnn : (0 : ℝ) ≤ (Real.exp v * (1 - v)) ^ n := pow_nonneg hb0 n
      have h1 : 1 - (Real.exp v * (1 - v)) ^ n ≤ 1 := by linarith
      exact h1.trans hbig
  have hx2 : x ^ 2 = (n : ℝ) ^ 2 * v ^ 2 := by rw [hx_eq]; ring
  have hrhs : 2 * x ^ 2 * Real.exp (-x) / n = Real.exp (-x) * (2 * (n : ℝ) * v ^ 2) := by
    rw [hx2]; field_simp
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left hstep (Real.exp_pos (-x)).le

/-! ### The closed form of `logDeriv (GammaSeq · n)` -/

private theorem hasDerivAt_GammaSeq_1122b {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun w : ℂ => Complex.GammaSeq w n)
      (Complex.GammaSeq s n *
        ((Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹)) s := by
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  set P : ℂ → ℂ := fun w => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) with hPdef
  have hne : ∀ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 := by
    intro j hj
    have hre : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
    have hpos : 0 < (s + (j : ℂ)).re := by
      rw [hre]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    exact fun h => by rw [h] at hpos; exact lt_irrefl 0 hpos
  have hPne : P s ≠ 0 := by
    rw [hPdef, Finset.prod_ne_zero_iff]
    exact hne
  have hP : HasDerivAt P (P s * ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹) s := by
    have hsum : (∑ j ∈ Finset.range (n + 1),
        (∏ i ∈ (Finset.range (n + 1)).erase j, (s + (i : ℂ))) • (1 : ℂ))
        = P s * ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [smul_eq_mul, mul_one, hPdef]
      rw [← Finset.prod_erase_mul (Finset.range (n + 1)) (fun i => (s + (i : ℂ))) hj]
      rw [mul_assoc, mul_inv_cancel₀ (hne j hj), mul_one]
    have h := HasDerivAt.finsetProd (u := Finset.range (n + 1))
      (f := fun j : ℕ => fun w : ℂ => w + (j : ℂ)) (f' := fun j : ℕ => (1 : ℂ))
      (fun j hj => (hasDerivAt_id s).add_const (j : ℂ))
    rw [hsum] at h
    rw [hPdef] at h
    have hfun : (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)))
        = ∏ i ∈ Finset.range (n + 1), fun w : ℂ => w + (i : ℂ) := by
      funext w
      rw [Finset.prod_apply]
    rw [hfun] at h
    rw [hPdef, hfun]
    exact h
  have hbase : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w)
      ((n : ℂ) ^ s * Complex.log (n : ℂ) * 1) s :=
    HasDerivAt.const_cpow (hasDerivAt_id s) (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hA : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w * (Nat.factorial n : ℂ))
      ((n : ℂ) ^ s * Complex.log (n : ℂ) * 1 * (Nat.factorial n : ℂ)) s :=
    hbase.mul_const _
  have hquot := hA.div hP hPne
  have hfun : (fun w : ℂ => Complex.GammaSeq w n) =
      ((fun w : ℂ => (n : ℂ) ^ w * (Nat.factorial n : ℂ)) / P) := by
    funext w
    simp only [hPdef, Pi.div_apply, Complex.GammaSeq]
  have hprod : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 := by
    simpa only [hPdef] using hPne
  have hval : (((n : ℂ) ^ s * Complex.log (n : ℂ) * 1 * (Nat.factorial n : ℂ)) * P s -
      ((n : ℂ) ^ s * (Nat.factorial n : ℂ)) *
        (P s * ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹)) / (P s) ^ 2 =
      Complex.GammaSeq s n *
        ((Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹) := by
    rw [hlog]
    simp only [hPdef, Complex.GammaSeq]
    field_simp
  rw [hfun, ← hval]
  exact hquot

/-- `GammaSeq · n` does not vanish on `Re s > 0`. -/
private theorem GammaSeq_ne_zero_1122b {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    Complex.GammaSeq s n ≠ 0 := by
  have hne : ∀ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 := by
    intro j hj
    have hre : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
    have hpos : 0 < (s + (j : ℂ)).re := by
      rw [hre]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    exact fun h => by rw [h] at hpos; exact lt_irrefl 0 hpos
  simp only [Complex.GammaSeq]
  refine div_ne_zero (mul_ne_zero ?_ ?_) (Finset.prod_ne_zero_iff.mpr hne)
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- The digamma-series summand: the logarithmic derivative of `GammaSeq · n`. -/
private theorem logDeriv_GammaSeq_1122b {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w : ℂ => Complex.GammaSeq w n) s =
      (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
  have hG : Complex.GammaSeq s n ≠ 0 := GammaSeq_ne_zero_1122b hs hn
  rw [logDeriv_apply, (hasDerivAt_GammaSeq_1122b hs hn).deriv]
  field_simp

/-! ### The real weight, its integrability, and its vanishing tail -/

/-- On `Re s ∈ [σ, R]` the modulus weight `x^(Re s - 1)` is dominated by
`x^(σ-1) + x^(R-1)`, separately on `(0,1]` and `[1,∞)`. -/
private theorem rpow_re_sub_one_le_1122b {σ R : ℝ} {s : ℂ} (h1 : σ ≤ s.re) (h2 : s.re ≤ R) {x : ℝ}
    (hx : 0 < x) :
    x ^ (s.re - 1) ≤ x ^ (σ - 1) + x ^ (R - 1) := by
  have h0σ : (0 : ℝ) ≤ x ^ (σ - 1) := Real.rpow_nonneg hx.le _
  have h0R : (0 : ℝ) ≤ x ^ (R - 1) := Real.rpow_nonneg hx.le _
  rcases le_total (1:ℝ) x with hx1 | hx1
  · have hle : x ^ (s.re - 1) ≤ x ^ (R - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith
  · have hle : x ^ (s.re - 1) ≤ x ^ (σ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
    linarith

private theorem integrableOn_exp_mul_rpow_sub_one_1122b {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (p - 1)) (Set.Ioi (0 : ℝ)) :=
  Real.GammaIntegral_convergent hp

private theorem integrableOn_exp_mul_weight_1122b {σ R : ℝ} (hσ : 0 < σ) (hR : σ ≤ R) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * (x ^ (σ - 1) + x ^ (R - 1)))
      (Set.Ioi (0 : ℝ)) := by
  have hR0 : 0 < R := lt_of_lt_of_le hσ hR
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (σ - 1)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_rpow_sub_one_1122b hσ
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (R - 1)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_rpow_sub_one_1122b hR0
  have h := h1.add h2
  convert h using 1
  ext x
  simp only [Pi.add_apply, mul_add]

/-- The tail of an integrable function on `Ioi 0` vanishes. -/
private theorem tendsto_integral_Ioi_natCast_zero_1122b {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioi (n : ℝ), g x) atTop (𝓝 0) := by
  have hmain : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(n : ℝ), g x) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), g x)) :=
    intervalIntegral_tendsto_integral_Ioi (μ := volume) (a := (0 : ℝ)) (f := g) hg
      tendsto_natCast_atTop_atTop
  have hfun : ∀ n : ℕ, (∫ x in Set.Ioi (n : ℝ), g x) =
      (∫ x in Set.Ioi (0 : ℝ), g x) - ∫ x in (0 : ℝ)..(n : ℝ), g x := by
    intro n
    have h := intervalIntegral.integral_Ioi_sub_Ioi (μ := volume) (f := g) (a := (0 : ℝ))
      (b := (n : ℝ)) hg (by positivity)
    linarith
  have hlim : Tendsto (fun n : ℕ => ((∫ x in Set.Ioi (0 : ℝ), g x) -
      ∫ x in (0 : ℝ)..(n : ℝ), g x)) atTop (𝓝 ((∫ x in Set.Ioi (0 : ℝ), g x) -
      (∫ x in Set.Ioi (0 : ℝ), g x))) :=
    tendsto_const_nhds.sub hmain
  simp only [sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards with n
  exact (hfun n).symm

/-! ### Toward `tendstoLocallyUniformlyOn_GammaSeq`: the uniform strip bound -/

/-- `x^2 * x^(p-1) = x^(p+1)` for `x > 0`. -/
private theorem sq_mul_rpow_sub_one_1122b {p x : ℝ} (hx : 0 < x) : x ^ 2 * x ^ (p - 1) = x ^ (p + 1) := by
  rw [← Real.rpow_natCast (x := x) (n := 2), ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

private theorem integrableOn_exp_mul_weight_sq_1122b {σ R : ℝ} (hσ : 0 < σ) (hR : σ ≤ R) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1)))
      (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_exp_mul_weight_1122b (σ := σ + 2) (R := R + 2) (by linarith) (by linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have e1 : x ^ (σ + 2 - 1) = x ^ 2 * x ^ (σ - 1) := by
    rw [show σ + 2 - 1 = (σ - 1) + 2 by ring, Real.rpow_add hx0,
      ← Real.rpow_natCast (x := x) (n := 2)]
    ring
  have e2 : x ^ (R + 2 - 1) = x ^ 2 * x ^ (R - 1) := by
    rw [show R + 2 - 1 = (R - 1) + 2 by ring, Real.rpow_add hx0,
      ← Real.rpow_natCast (x := x) (n := 2)]
    ring
  simp only []
  rw [e1, e2]
  ring

/-- The uniform-in-`s` bound on a vertical strip. -/
private theorem norm_GammaSeq_sub_Gamma_le_1122b {σ R : ℝ} (hσ : 0 < σ) (hR : σ ≤ R) {n : ℕ}
    (hn : 2 ≤ n) {s : ℂ} (h1 : σ ≤ s.re) (h2 : s.re ≤ R) :
    ‖Complex.GammaSeq s n - Complex.Gamma s‖ ≤
      (2 / (n : ℝ)) * (∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) +
        ∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * (x ^ (σ - 1) + x ^ (R - 1)) := by
  have hsr : 0 < s.re := lt_of_lt_of_le hσ h1
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hle : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  set F : ℝ → ℂ := fun x => ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) with hF
  set G : ℝ → ℂ := fun x => ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) with hG
  have hFint : IntegrableOn F (Set.Ioi (0 : ℝ)) := by
    rw [hF]; exact Complex.GammaIntegral_convergent hsr
  have hFs : Complex.Gamma s = ∫ x in Set.Ioi (0 : ℝ), F x := by
    rw [hF]
    exact Complex.Gamma_eq_integral hsr
  have hGs : Complex.GammaSeq s n = ∫ x in (0 : ℝ)..(n : ℝ), G x := by
    rw [hG]; exact Complex.GammaSeq_eq_approx_Gamma_integral hsr hn0
  have hFI' : IntervalIntegrable F volume (0 : ℝ) (n : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact hFint.mono_set Set.Ioc_subset_Ioi_self
  have hFIn : IntegrableOn F (Set.Ioi (n : ℝ)) := hFint.mono_set (Set.Ioi_subset_Ioi hle)
  have hGI : IntervalIntegrable G volume (0 : ℝ) (n : ℝ) := by
    rw [hG]
    apply IntervalIntegrable.continuousOn_mul
    · exact intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    · fun_prop
  have hsplit : (∫ x in (0 : ℝ)..(n : ℝ), F x) + ∫ x in Set.Ioi (n : ℝ), F x
      = ∫ x in Set.Ioi (0 : ℝ), F x :=
    intervalIntegral.integral_interval_add_Ioi hFint hFIn
  have hd : Complex.GammaSeq s n - Complex.Gamma s =
      (∫ x in (0 : ℝ)..(n : ℝ), (G x - F x)) - ∫ x in Set.Ioi (n : ℝ), F x := by
    rw [hGs, hFs, intervalIntegral.integral_sub hGI hFI', ← hsplit]
    ring
  rw [hd]
  have hmaj : ∀ x ∈ Set.Ioo (0 : ℝ) (n : ℝ),
      ‖G x - F x‖ ≤ 2 / (n : ℝ) * (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
    intro x hx
    obtain ⟨hx0, hxn⟩ := hx
    have hxn' : x ≤ (n : ℝ) := le_of_lt hxn
    have hGF : G x - F x = ↑((1 - x / n) ^ n - Real.exp (-x)) * (x : ℂ) ^ (s - 1) := by
      rw [hG, hF]; push_cast; ring
    rw [hGF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
        Real.norm_eq_abs]
    have hnonpos : (1 - x / n) ^ n - Real.exp (-x) ≤ 0 := by
      have := Real.one_sub_div_pow_le_exp_neg (n := n) (t := x) hxn'
      linarith
    rw [abs_of_nonpos hnonpos, neg_sub]
    have hkey := exp_neg_sub_one_sub_div_pow_le_1122b hn hx0.le hxn'
    have hrw : x ^ (s.re - 1) ≤ x ^ (σ - 1) + x ^ (R - 1) := rpow_re_sub_one_le_1122b h1 h2 hx0
    have h1' : (0 : ℝ) ≤ x ^ (s.re - 1) := Real.rpow_nonneg hx0.le _
    calc (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)
        ≤ (2 * x ^ 2 * Real.exp (-x) / n) * (x ^ (σ - 1) + x ^ (R - 1)) :=
          mul_le_mul hkey hrw h1' (by positivity)
      _ = 2 / (n : ℝ) * (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
          field_simp
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
    have stepA : (∫ x in (0 : ℝ)..(n : ℝ), ‖G x - F x‖) ≤ 2 / (n : ℝ) *
        ∫ x in (0 : ℝ)..(n : ℝ),
          (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
      have hInt : IntervalIntegrable (fun x : ℝ =>
          2 / (n : ℝ) * (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))))
          volume (0 : ℝ) (n : ℝ) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact ((integrableOn_exp_mul_weight_sq_1122b (σ := σ) (R := R) hσ hR).mono_set
          Set.Ioc_subset_Ioi_self).const_mul _
      have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hle ((hGI.sub hFI').norm)
        hInt hmaj
      rwa [intervalIntegral.integral_const_mul] at hmono
    have stepB : (∫ x in (0 : ℝ)..(n : ℝ),
          (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))))
        ≤ ∫ x in Set.Ioi (0 : ℝ),
          (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
      rw [intervalIntegral.integral_of_le hle]
      refine setIntegral_mono_set (f := fun x : ℝ =>
        Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1)))
        (integrableOn_exp_mul_weight_sq_1122b (σ := σ) (R := R) hσ hR) ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        have hw : (0 : ℝ) ≤ x ^ (σ - 1) + x ^ (R - 1) := by
          have a := Real.rpow_nonneg hx0.le (σ - 1)
          have b := Real.rpow_nonneg hx0.le (R - 1)
          linarith
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg x)) hw
      · exact ae_of_all _ (fun x hx => Set.Ioc_subset_Ioi_self hx)
    exact stepA.trans (mul_le_mul_of_nonneg_left stepB (by positivity))
  · refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (f := fun x => ‖F x‖)
      (g := fun x => Real.exp (-x) * (x ^ (σ - 1) + x ^ (R - 1)))
      (hFIn.norm) ((integrableOn_exp_mul_weight_1122b hσ hR).mono_set (Set.Ioi_subset_Ioi hle))
      measurableSet_Ioi ?_
    intro x hx
    have hx0 : 0 < x := lt_trans hnpos hx
    rw [hF, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (rpow_re_sub_one_le_1122b h1 h2 hx0) (Real.exp_pos _).le

/-- `GammaSeq · n` converges to `Gamma` locally uniformly on `Re s > 0`.  This is the
Mathlib-missing locally uniform strengthening of `Complex.GammaSeq_tendsto_Gamma`. -/
private theorem GammaSeq_tendstoLocallyUniformlyOn_1122b :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) => Complex.GammaSeq s n) Complex.Gamma
      atTop {z : ℂ | 0 < z.re} := by
  intro u hu x hx
  rw [Metric.mem_uniformity_dist] at hu
  obtain ⟨ε, hε, hεu⟩ := hu
  have hx0 : 0 < x.re := hx
  have hσ : 0 < x.re / 2 := by linarith
  have hσR : x.re / 2 ≤ x.re + 1 := by linarith
  set C : ℝ := ∫ y in Set.Ioi (0 : ℝ),
    Real.exp (-y) * y ^ 2 * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1)) with hCdef
  have htend1 : Tendsto (fun n : ℕ => 2 / (n : ℝ) * C) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
    have h2 : Tendsto (fun n : ℕ => 2 / (n : ℝ) * C) atTop (𝓝 (0 * C)) := h.mul_const C
    simpa using h2
  have htend2 : Tendsto (fun n : ℕ => ∫ y in Set.Ioi (n : ℝ),
      Real.exp (-y) * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1))) atTop (𝓝 0) :=
    tendsto_integral_Ioi_natCast_zero_1122b (integrableOn_exp_mul_weight_1122b hσ hσR)
  have htendB : Tendsto (fun n : ℕ => 2 / (n : ℝ) * C + ∫ y in Set.Ioi (n : ℝ),
      Real.exp (-y) * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1))) atTop (𝓝 (0 + 0)) :=
    htend1.add htend2
  rw [add_zero] at htendB
  have hev : ∀ᶠ n : ℕ in atTop, 2 / (n : ℝ) * C + ∫ y in Set.Ioi (n : ℝ),
      Real.exp (-y) * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1)) < ε :=
    htendB.eventually (isOpen_Iio.mem_nhds hε)
  have hopen : IsOpen {y : ℂ | x.re / 2 < y.re ∧ y.re < x.re + 1} := by
    have h : {y : ℂ | x.re / 2 < y.re ∧ y.re < x.re + 1} =
        Complex.re ⁻¹' Set.Ioo (x.re / 2) (x.re + 1) := by
      ext y
      simp [Set.mem_Ioo]
    rw [h]
    exact isOpen_Ioo.preimage Complex.continuous_re
  refine ⟨{y : ℂ | x.re / 2 < y.re ∧ y.re < x.re + 1}, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds ⟨by linarith, by linarith⟩)
  · filter_upwards [hev, eventually_ge_atTop 2] with n hnB hn2
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    refine hεu ?_
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (norm_GammaSeq_sub_Gamma_le_1122b hσ hσR hn2 (s := y) hy1.le hy2.le) hnB


/-- The digamma series: `ψ(z) = lim_n (log n - Σ_{j≤n} 1/(z+j))` on `Re z > 0`,
from the locally uniform convergence of the Weierstrass product. -/
private theorem digamma_tendsto_1122b {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹)
      atTop (𝓝 (Complex.digamma z)) := by
  have hs : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (fun w : ℂ => Complex.GammaSeq w n) {w : ℂ | 0 < w.re} := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro w hw
    exact (hasDerivAt_GammaSeq_1122b (n := n) hw (Nat.one_le_iff_ne_zero.mp hn)).differentiableAt.differentiableWithinAt
  have hg : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have h := Complex.logDeriv_tendsto hs (show z ∈ {w : ℂ | 0 < w.re} from hz)
    GammaSeq_tendstoLocallyUniformlyOn_1122b hf hg
  rw [Complex.digamma_def]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact logDeriv_GammaSeq_1122b hz (Nat.one_le_iff_ne_zero.mp hn)




end Series1122b

/-- The Laplace integral of a complex exponential: for re a positive,
∫_0^∞ e^{-ta} dt = 1/a, with integrability. -/
private lemma laplace_exp_1122b (a : ℂ) (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(t : ℂ) * a)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * a) = 1 / a := by
  have ha' : (-a).re < 0 := by simp; linarith
  have he : (fun t : ℝ => Complex.exp (-(t : ℂ) * a)) = fun t : ℝ => Complex.exp (-a * t) := by
    funext t; ring_nf
  rw [he]
  refine ⟨integrableOn_exp_mul_complex_Ioi ha' 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi ha' 0]
  simp

/-- Frullani's integral for complex w with re w positive:
log w = ∫_0^∞ (e^{-t} - e^{-tw})/t dt, with integrability. Proved by Fubini on
(e^{-t} - e^{-tw})/t = ∫_0^1 (w - 1) e^{-t(1 + u(w - 1))} du. -/
private lemma frullani_1122b (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * w)) / (t : ℂ))
        (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * w)) / (t : ℂ) =
        Complex.log w := by
  by_cases hw1 : w = 1
  · subst hw1
    simp only [mul_one, Complex.ofReal_exp, Complex.ofReal_neg, sub_self, zero_div,
      integral_zero, Complex.log_one, and_true]
    exact integrableOn_zero
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  set c : ℝ := min 1 w.re with hc
  have hc0 : 0 < c := lt_min one_pos hw
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcw : c ≤ w.re := min_le_right _ _
  -- the real part of 1 + u(w - 1) on [0, 1]
  have hre : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → c ≤ (1 + (u : ℂ) * (w - 1)).re := by
    intro u hu0 hu1
    simp only [add_re, one_re, mul_re, ofReal_re, sub_re, ofReal_im, sub_im, one_im, zero_mul,
      sub_zero]
    nlinarith
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  set F : ℝ → ℝ → ℂ := fun t u => (w - 1) * Complex.exp (-(t : ℂ) * (1 + (u : ℂ) * (w - 1)))
    with hF
  have hFm : Continuous (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]; fun_prop
  have hg1 : Integrable (fun t : ℝ => ‖w - 1‖ * Real.exp (-c * t)) μ :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  have hg2 : Integrable (fun _ : ℝ => (1 : ℝ)) ν := integrableOn_const measure_Ioc_lt_top.ne
  have hFI : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine (hg1.mul_prod hg2).mono' hFm.aestronglyMeasurable ?_
    rw [hμ, hν, Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    obtain ⟨ht, hu⟩ := hp
    have ht0 : (0 : ℝ) < p.1 := ht
    obtain ⟨hu0, hu1⟩ := hu
    have h := hre p.2 hu0.le hu1
    simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp, mul_one]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (-(p.1 : ℂ) * (1 + (p.2 : ℂ) * (w - 1))).re =
        -(p.1 * (1 + (p.2 : ℂ) * (w - 1)).re) := by simp
    rw [this]
    nlinarith
  -- the inner integral in u
  have hinner_u : ∀ t : ℝ, 0 < t → ∫ u, F t u ∂ν =
      ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * w)) / (t : ℂ) := by
    intro t ht
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hcne : -(t : ℂ) * (w - 1) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr htne) hw1'
    have hpt : ∀ u : ℝ, F t u = ((w - 1) * Complex.exp (-(t : ℂ))) *
        Complex.exp ((-(t : ℂ) * (w - 1)) * u) := by
      intro u; simp only [hF]; rw [mul_assoc, ← Complex.exp_add]; ring_nf
    rw [hν, ← intervalIntegral.integral_of_le zero_le_one]
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hcne]
    have e1 : Complex.exp (-(t : ℂ)) * Complex.exp (-(t : ℂ) * (w - 1) * ((1 : ℝ) : ℂ)) =
        Complex.exp (-(t : ℂ) * w) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e0 : Complex.exp (-(t : ℂ) * (w - 1) * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [e0, Complex.ofReal_exp, Complex.ofReal_neg, ← e1]
    field_simp
    ring
  -- the inner integral in t
  have hinner_t : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∫ t, F t u ∂μ = (w - 1) / (1 + (u : ℂ) * (w - 1)) := by
    intro u hu0 hu1
    have hpos : 0 < (1 + (u : ℂ) * (w - 1)).re := lt_of_lt_of_le hc0 (hre u hu0 hu1)
    simp only [hF]
    rw [integral_const_mul, hμ, (laplace_exp_1122b _ hpos).2]
    ring
  -- the outer integral in u
  have hlog : ∫ u in (0 : ℝ)..1, (w - 1) / (1 + (u : ℂ) * (w - 1)) = Complex.log w := by
    have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => Complex.log (1 + (u : ℂ) * (w - 1)))
        ((w - 1) / (1 + (u : ℂ) * (w - 1))) u := by
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      have hpos : 0 < (1 + (u : ℂ) * (w - 1)).re := lt_of_lt_of_le hc0 (hre u hu.1 hu.2)
      have h1 : HasDerivAt (fun u : ℝ => 1 + (u : ℂ) * (w - 1)) (w - 1) u := by
        have := ((hasDerivAt_id u).ofReal_comp).mul_const (w - 1)
        simpa using this.const_add 1
      exact h1.clog_real (Or.inl hpos)
    have hcont : ContinuousOn (fun u : ℝ => (w - 1) / (1 + (u : ℂ) * (w - 1))) (uIcc 0 1) := by
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      have hpos : 0 < (1 + (u : ℂ) * (w - 1)).re := lt_of_lt_of_le hc0 (hre u hu.1 hu.2)
      intro h; rw [h] at hpos; simp at hpos
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
    simp
  have hleft : Integrable (fun t => ∫ u, F t u ∂ν) μ := hFI.integral_prod_left
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), ∫ u, F t u ∂ν =
      ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * w)) / (t : ℂ) := fun t ht => hinner_u t ht
  refine ⟨?_, ?_⟩
  · exact (show IntegrableOn (fun t => ∫ u, F t u ∂ν) (Ioi 0) by
      rw [IntegrableOn, ← hμ]; exact hleft).congr_fun hcongr
      measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi hcongr]
    change ∫ t, ∫ u, F t u ∂ν ∂μ = _
    rw [integral_integral_swap hFI, hν, ← hlog, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    exact hinner_t u hu.1.le hu.2

/-- The kernel 1/t - 1/(1 - e^{-t}) lies in [-1, 0] for t positive,
from 1 - t ≤ e^{-t} and 1 + t ≤ e^{t}. -/
private lemma kernel_bound_1122b (t : ℝ) (ht : 0 < t) :
    -1 ≤ 1 / t - 1 / (1 - Real.exp (-t)) ∧ 1 / t - 1 / (1 - Real.exp (-t)) ≤ 0 := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h3 : (1 + t) * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    have hm : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-t)]
  have hd : 0 < 1 - Real.exp (-t) := by linarith
  constructor
  · rw [div_sub_div _ _ ht.ne' hd.ne', le_div_iff₀ (mul_pos ht hd)]
    nlinarith
  · rw [sub_nonpos, div_le_div_iff₀ ht hd]
    linarith

/-- The complex kernel has norm at most 1 for t positive. -/
private lemma kernel_norm_1122b (t : ℝ) (ht : 0 < t) :
    ‖1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))‖ ≤ 1 := by
  have hc : (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) =
      ((1 / t - 1 / (1 - Real.exp (-t)) : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le]
  obtain ⟨a, b⟩ := kernel_bound_1122b t ht
  exact ⟨a, by linarith⟩

/-- The Laplace transform of the kernel: integrable for re w positive, with norm at most
1/re w. -/
private lemma kernel_laplace_1122b (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ =>
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)‖ ≤
          1 / w.re := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-w.re * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hb : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)‖ ≤
        Real.exp (-w.re * t) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(t : ℂ) * w).re = -w.re * t := by simp; ring
    rw [hre]
    calc ‖1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))‖ * Real.exp (-w.re * t)
        ≤ 1 * Real.exp (-w.re * t) :=
          mul_le_mul_of_nonneg_right (kernel_norm_1122b t ht) (Real.exp_pos _).le
      _ = Real.exp (-w.re * t) := one_mul _
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w))
        (volume.restrict (Ioi (0 : ℝ))) := by
    refine Measurable.aestronglyMeasurable ?_
    fun_prop
  refine ⟨Integrable.mono' hg hm hb, ?_⟩
  refine (norm_integral_le_of_norm_le hg hb).trans_eq ?_
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp

/-- One step of the recurrence: for re w positive,
1/w = L(w + 1) - L(w) + log(w + 1) - log w, where L is the kernel Laplace transform. -/
private lemma step_1122b (w : ℂ) (hw : 0 < w.re) :
    1 / w = (∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * (w + 1))) -
      (∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)) +
      Complex.log (w + 1) - Complex.log w := by
  have hw' : 0 < (w + 1).re := by simp; linarith
  obtain ⟨hL1, -⟩ := kernel_laplace_1122b (w + 1) hw'
  obtain ⟨hL0, -⟩ := kernel_laplace_1122b w hw
  obtain ⟨hF1, hF1v⟩ := frullani_1122b (w + 1) hw'
  obtain ⟨hF0, hF0v⟩ := frullani_1122b w hw
  obtain ⟨-, hE⟩ := laplace_exp_1122b w hw
  have hpt : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) → Complex.exp (-(t : ℂ) * w) =
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * (w + 1)) -
          (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w) +
          ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * (w + 1))) / (t : ℂ) -
          ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * w)) / (t : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hd : (1 - (Real.exp (-t) : ℂ)) ≠ 0 := by
      intro h
      have h' : ((1 - Real.exp (-t) : ℝ) : ℂ) = 0 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one]; exact h
      rw [Complex.ofReal_eq_zero] at h'
      linarith
    have hE1 : Complex.exp (-(t : ℂ) * (w + 1)) =
        Complex.exp (-(t : ℂ) * w) * (Real.exp (-t) : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [hE1]
    field_simp
    ring
  rw [← hF1v, ← hF0v, ← hE]
  have hcongr : ∫ t in Ioi (0 : ℝ), Complex.exp (-(t : ℂ) * w) =
      ∫ t in Ioi (0 : ℝ),
        ((1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * (w + 1)) -
          (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w) +
          ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * (w + 1))) / (t : ℂ) -
          ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * w)) / (t : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact hpt t ht
  have hA : IntegrableOn (fun t : ℝ =>
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * (w + 1)) -
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w)) (Ioi 0) :=
    hL1.sub hL0
  have hB : IntegrableOn (fun t : ℝ =>
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * (w + 1)) -
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * w) +
        ((Real.exp (-t) : ℂ) - Complex.exp (-(t : ℂ) * (w + 1))) / (t : ℂ)) (Ioi 0) :=
    hA.add hF1
  rw [hcongr, integral_sub hB hF0, integral_add hA hF1, integral_sub hL1 hL0]

/-- Telescoping the recurrence: Σ_{j<m} 1/(z + j) = L(z + m) - L(z) + log(z + m) - log z. -/
private lemma telescope_1122b (z : ℂ) (hz : 0 < z.re) (m : ℕ) :
    ∑ j ∈ Finset.range m, (z + (j : ℂ))⁻¹ =
      (∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * (z + m))) -
      (∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z)) +
      Complex.log (z + m) - Complex.log z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hm : 0 < (z + (m : ℂ)).re := by
      simp; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    have hs := step_1122b (z + m) hm
    have hc : z + ((m + 1 : ℕ) : ℂ) = z + (m : ℂ) + 1 := by push_cast; ring
    rw [hc, inv_eq_one_div, hs]
    ring

/-- The logarithmic correction tends to 0: log(z + n + 1) - log n → 0. -/
private lemma log_shift_tendsto_1122b (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.log (z + ((n + 1 : ℕ) : ℂ)) - (Real.log n : ℂ)) atTop
      (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => (((1 / (n : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
    rw [Complex.ofReal_zero] at this
    exact this
  have h1 : Tendsto (fun n : ℕ => 1 + (z + 1) * (((1 / (n : ℝ)) : ℝ) : ℂ)) atTop (𝓝 1) := by
    have := (h0.const_mul (z + 1)).const_add 1
    simpa using this
  have h2 := ((continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto).comp h1
  rw [Complex.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 1 + (z + 1) * (((1 / (n : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      zero_re, add_im, one_im] at hre
    have : 0 < (z.re + 1) * (1 / (n : ℝ)) := by positivity
    linarith
  have heq : z + ((n + 1 : ℕ) : ℂ) = (1 + (z + 1) * (((1 / (n : ℝ)) : ℝ) : ℂ)) * ((n : ℝ) : ℂ) := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
    push_cast
    field_simp
    ring
  simp only [Function.comp_apply]
  rw [heq, Complex.log_mul_ofReal _ hnpos _ hx]
  ring

/-- OLBC10 DLMF 5.9.13, the Laplace form of the digamma function from which Binet's
second formula DLMF 5.9.15, quoted at P0014 page 34 display 4.10 first line, is derived:
for re z above 0, ψ(z) = ln z + ∫_0^∞ (1/t - 1/(1 - e^{-t})) e^{-tz} dt.
PROVED here with no sorry: the recurrence of the right side, from Frullani's integral and
the Laplace transform of e^{-tw}, telescopes against the digamma series
ψ(z) = lim_n (ln n - Σ_{j ≤ n} 1/(z + j)), and the tail terms tend to 0. -/
theorem digamma_log_laplace (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z +
      ∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z) := by
  have hL : Tendsto (fun n : ℕ => ∫ t in Ioi (0 : ℝ),
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) *
        Complex.exp (-(t : ℂ) * (z + ((n + 1 : ℕ) : ℂ)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hre : (z + ((n + 1 : ℕ) : ℂ)).re = z.re + ((n : ℝ) + 1) := by simp
    have hpos : 0 < (z + ((n + 1 : ℕ) : ℂ)).re := by rw [hre]; positivity
    refine (kernel_laplace_1122b _ hpos).2.trans ?_
    rw [hre]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hlim : Tendsto (fun n : ℕ =>
      (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹) atTop
      (𝓝 (Complex.log z + ∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z))) := by
    have h := (tendsto_const_nhds (x := Complex.log z + ∫ t in Ioi (0 : ℝ),
        (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z))).sub
      (hL.add (log_shift_tendsto_1122b z hz))
    rw [add_zero, sub_zero] at h
    refine h.congr (fun n => ?_)
    rw [telescope_1122b z hz (n + 1)]
    ring
  exact tendsto_nhds_unique (digamma_tendsto_1122b hz) hlim

end DigammaLaplace1122b

section SinePlanck1122b

private lemma coth_hasSum_1122b (y : ℝ) (hy : 0 < y) :
    HasSum (fun n : ℕ => 2 * y / (y ^ 2 + ((n : ℝ) + 1) ^ 2))
      (Real.pi * (Real.cosh (Real.pi * y) / Real.sinh (Real.pi * y)) - 1 / y) := by
  have hx : (I * y : ℂ) ∈ integerComplement := by
    rw [mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have h2 := congrArg Complex.im hn
    simp at h2
    linarith
  have hs := (summable_cotTerm hx).hasSum
  have hs1 := cot_series_rep' hx
  simp only [cotTerm] at hs
  rw [← hs1] at hs
  have hs2 := hs.mul_left I
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsh : Real.sinh (Real.pi * y) ≠ 0 := by
    have := Real.sinh_pos_iff.mpr (by positivity : 0 < Real.pi * y); exact this.ne'
  have hshC : Complex.sinh ((Real.pi * y : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sinh]; exact_mod_cast hsh
  rw [← Complex.hasSum_ofReal]
  convert hs2 using 1
  · funext n
    have hd : ((y : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2) ≠ 0 := by
      have : (0 : ℝ) < y ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
      exact_mod_cast this.ne'
    have h1 : I * y - ((n : ℂ) + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have h2 : I * y + ((n : ℂ) + 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    push_cast
    rw [div_add_div _ _ h1 h2, mul_div_assoc', div_eq_div_iff hd (mul_ne_zero h1 h2)]
    linear_combination (-(2 : ℂ) * y * (y ^ 2 + ((n : ℂ) + 1) ^ 2) + 2 * (y : ℂ) ^ 3) * I_sq
  · have hc : Complex.cot ((Real.pi : ℂ) * (I * y)) = Complex.cosh ((Real.pi * y : ℝ) : ℂ) /
        (Complex.sinh ((Real.pi * y : ℝ) : ℂ) * I) := by
      rw [Complex.cot, show (Real.pi : ℂ) * (I * y) = ((Real.pi * y : ℝ) : ℂ) * I by push_cast; ring,
        Complex.cos_mul_I, Complex.sin_mul_I]
    rw [hc, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    field_simp
private lemma laplace_sin_1122b (t : ℝ) (z : ℂ) (hz : 0 < z.re) :
    ∫ u in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * z) * (Real.sin (u * t) : ℂ) =
      (t : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
  have hA : (-z + t * I).re < 0 := by simp; linarith
  have hB : (-z - t * I).re < 0 := by simp; linarith
  have hpt : ∀ u : ℝ, Complex.exp (-(u : ℂ) * z) * (Real.sin (u * t) : ℂ) =
      (I / 2) * (Complex.exp ((-z - t * I) * u) - Complex.exp ((-z + t * I) * u)) := by
    intro u
    have e1 : Complex.exp ((-z - t * I) * u) =
        Complex.exp (-(u : ℂ) * z) * Complex.exp (-(((u * t : ℝ) : ℂ)) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp ((-z + t * I) * u) =
        Complex.exp (-(u : ℂ) * z) * Complex.exp (((u * t : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, Complex.ofReal_sin, Complex.sin]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrableOn_exp_mul_complex_Ioi hB 0)
    (integrableOn_exp_mul_complex_Ioi hA 0), integral_exp_mul_complex_Ioi hB,
    integral_exp_mul_complex_Ioi hA]
  have h1 : z + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : z - t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (t : ℂ) ^ 2 + z ^ 2 = (z + t * I) * (z - t * I) := by
    ring_nf; rw [I_sq]; ring
  have hB' : -z - t * I = -(z + t * I) := by ring
  have hA' : -z + t * I = -(z - t * I) := by ring
  rw [h3, hB', hA']
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_neg, div_neg, neg_div, neg_div, neg_neg, neg_neg, div_sub_div _ _ h1 h2,
    eq_div_iff (mul_ne_zero h1 h2), mul_assoc, div_mul_cancel₀ _ (mul_ne_zero h1 h2)]
  ring_nf
  rw [I_sq]
  ring

private lemma term_integral_1122b (a c : ℝ) (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), Real.sin (a * t) * Real.exp (-(c * t)) = a / (a ^ 2 + c ^ 2) := by
  have h := laplace_sin_1122b a (c : ℂ) (by simpa using hc)
  have hcongr : (fun u : ℝ => Complex.exp (-(u : ℂ) * c) * (Real.sin (u * a) : ℂ)) =
      fun u : ℝ => ((Real.sin (a * u) * Real.exp (-(c * u)) : ℝ) : ℂ) := by
    funext u
    push_cast
    rw [mul_comm (a : ℂ) u]
    ring_nf
  rw [hcongr, integral_complex_ofReal] at h
  exact_mod_cast h

private lemma geom_1122b (β t : ℝ) (hβ : 0 < β) (ht : 0 < t) :
    ∑' n : ℕ, Real.exp (-(((n : ℝ) + 1) * β * t)) = 1 / (Real.exp (β * t) - 1) := by
  set u := β * t with hu
  have hu0 : 0 < u := by positivity
  have hq0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hq1 : Real.exp (-u) < 1 := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    simpa using this
  have hterm : ∀ n : ℕ, Real.exp (-(((n : ℝ) + 1) * β * t)) =
      Real.exp (-u) * Real.exp (-u) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add, hu]
    congr 1; ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have he : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu0
  have hne : Real.exp u - 1 ≠ 0 := by linarith
  have hne' : 1 - Real.exp (-u) ≠ 0 := by linarith
  rw [Real.exp_neg] at hne' ⊢
  field_simp

/-- GR00 3.911.2, PROVED: for a and β positive,
∫_0^∞ sin(at)/(e^{βt} - 1) dt = (π/(2β)) coth(aπ/β) - 1/(2a), by the geometric series,
termwise integration and Mathlib's `cot_series_rep'` at an imaginary point. -/
theorem sine_planck (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ∫ t in Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1) =
      Real.pi / (2 * β) * (Real.cosh (a * Real.pi / β) / Real.sinh (a * Real.pi / β)) -
        1 / (2 * a) := by
  have codex_proof :
      ∫ t in Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1) =
        Real.pi / (2 * β) * (Real.cosh (a * Real.pi / β) / Real.sinh (a * Real.pi / β)) -
          1 / (2 * a) := by
    have geometric_kernel (β t : ℝ) (hβ : 0 < β) (ht : 0 < t) :
        (∑' n : ℕ, Real.exp (-((n : ℝ) + 1) * β * t)) = 1 / (Real.exp (β * t) - 1) := by
      have he (n : ℕ) : Real.exp (-((n : ℝ) + 1) * β * t) =
          Real.exp (-β * t) * Real.exp (-β * t) ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      have hr : ‖Real.exp (-β * t)‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_lt_one_iff.mpr
        nlinarith
      simp_rw [he]
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
      rw [show -β * t = -(β * t) by ring, Real.exp_neg]
      have hE : Real.exp (β * t) ≠ 0 := (Real.exp_pos _).ne'
      have hE1 : Real.exp (β * t) - 1 ≠ 0 :=
        (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hβ ht))).ne'
      field_simp
      <;> ring

    have integrable_sine_exp (a c : ℝ) (hc : 0 < c) :
        IntegrableOn (fun t : ℝ => Real.exp (-c * t) * Real.sin (a * t)) (Ioi 0) := by
      have hM : IntegrableOn (fun t : ℝ => |a| * (t * Real.exp (-c * t))) (Ioi 0) := by
        apply Integrable.const_mul
        simpa only [Real.rpow_one] using!
          (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := c)
            (by norm_num) (by norm_num) hc)
      apply hM.mono' (by fun_prop)
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hs := Real.abs_sin_le_abs (x := a * t)
      rw [abs_mul, abs_of_pos (show 0 < t from ht)] at hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [Real.exp_pos (-c * t)]

    have sine_exp_integral (a c : ℝ) (hc : 0 < c) :
        (∫ t in Ioi (0 : ℝ), Real.exp (-c * t) * Real.sin (a * t)) = a / (c ^ 2 + a ^ 2) := by
      have hneg : (((-c : ℝ) : ℂ) + (a : ℂ) * Complex.I).re < 0 := by
        simp
        linarith
      have hi := integrableOn_exp_mul_complex_Ioi hneg 0
      have h := congrArg Complex.im (integral_exp_mul_complex_Ioi hneg 0)
      change RCLike.im (∫ x in Ioi (0 : ℝ),
        Complex.exp ((((-c : ℝ) : ℂ) + (a : ℂ) * Complex.I) * x)) = _ at h
      rw [← integral_im hi] at h
      simpa [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.div_im, Complex.normSq_apply, pow_two, mul_comm, neg_div, neg_neg] using h

    have coth_series (x : ℝ) (hx : 0 < x) :
        (∑' n : ℕ, x / (x ^ 2 + ((n : ℝ) + 1) ^ 2)) =
          Real.pi / 2 * (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) - 1 / (2 * x) := by
      have hz : (x : ℂ) * Complex.I ∈ Complex.integerComplement :=
        UpperHalfPlane.coe_mem_integerComplement ⟨(x : ℂ) * Complex.I, by simpa using hx⟩
      have hs := summable_cotTerm hz
      have h := congrArg Complex.im (cot_series_rep' hz)
      rw [Complex.im_tsum hs] at h
      have hterm (n : ℕ) :
          (1 / ((x : ℂ) * Complex.I - ((n : ℂ) + 1)) +
            1 / ((x : ℂ) * Complex.I + ((n : ℂ) + 1))).im =
              -2 * (x / (x ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
        simp only [Complex.add_im, Complex.div_im, Complex.one_im, Complex.one_re,
          Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, mul_one, add_zero,
          zero_add, sub_zero, zero_sub, Complex.normSq_apply]
        ring
      simp_rw [hterm] at h
      rw [tsum_mul_left] at h
      have hcot : Complex.cot ((Real.pi : ℂ) * ((x : ℂ) * Complex.I)) =
          -((Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) : ℝ) : ℂ) * Complex.I := by
        rw [Complex.cot, show (Real.pi : ℂ) * ((x : ℂ) * Complex.I) =
          (((Real.pi * x : ℝ) : ℂ) * Complex.I) by push_cast; ring,
          Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
        field_simp
        <;> ring_nf
        <;> simp [Complex.I_sq]
      rw [hcot] at h
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.div_im,
        Complex.one_im, Complex.one_re, Complex.mul_re, Complex.normSq_apply,
        zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero, zero_sub] at h
      have hx0 : x ≠ 0 := hx.ne'
      field_simp at h ⊢
      <;> nlinarith

    have sine_planck_series (a β : ℝ) (hβ : 0 < β) :
        (∫ t in Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1)) =
          ∑' n : ℕ, a / ((((n : ℝ) + 1) * β) ^ 2 + a ^ 2) := by
      let F : ℕ → ℝ → ℝ := fun n t => Real.exp (-((n : ℝ) + 1) * β * t) * Real.sin (a * t)
      have hint (n : ℕ) : IntegrableOn (F n) (Ioi 0) := by
        simpa only [F, neg_mul] using!
          integrable_sine_exp a (((n : ℝ) + 1) * β) (by positivity)
      have hmajor (c : ℝ) (hc : 0 < c) :
          (∫ t in Ioi (0 : ℝ), ‖Real.exp (-c * t) * Real.sin (a * t)‖) ≤ |a| / c ^ 2 := by
        have htint : IntegrableOn (fun t : ℝ => t * Real.exp (-c * t)) (Ioi 0) := by
          simpa only [Real.rpow_one] using!
            (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := c)
              (by norm_num) (by norm_num) hc)
        have hcmp : (∫ t in Ioi (0 : ℝ), ‖Real.exp (-c * t) * Real.sin (a * t)‖) ≤
            ∫ t in Ioi (0 : ℝ), |a| * (t * Real.exp (-c * t)) := by
          apply integral_mono_ae (integrable_sine_exp a c hc).norm (htint.const_mul |a|)
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          have hs := Real.abs_sin_le_abs (x := a * t)
          rw [abs_mul, abs_of_pos (show 0 < t from ht)] at hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          nlinarith [Real.exp_pos (-c * t)]
        have hGamma2 : Real.Gamma 2 = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
        have hG : (∫ t in Ioi (0 : ℝ), t * Real.exp (-c * t)) = (1 / c) ^ 2 := by
          simpa [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_two, Real.rpow_one, hGamma2, neg_mul] using
            (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := c) (by norm_num) hc)
        calc (∫ t in Ioi (0 : ℝ), ‖Real.exp (-c * t) * Real.sin (a * t)‖)
          ≤ ∫ t in Ioi (0 : ℝ), |a| * (t * Real.exp (-c * t)) := hcmp
          _ = |a| / c ^ 2 := by rw [integral_const_mul, hG]; ring
      have hsBase : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
        have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
          simpa only [Real.rpow_two] using
            (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2))
        simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
      have hsum : Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖F n t‖) := by
        apply Summable.of_nonneg_of_le
          (fun n => integral_nonneg (fun t => norm_nonneg (F n t)))
          (fun n => ?_) (hsBase.mul_left (|a| / β ^ 2))
        calc
          (∫ t in Ioi (0 : ℝ), ‖F n t‖) ≤ |a| / (((n : ℝ) + 1) * β) ^ 2 := by
            simpa only [F, neg_mul] using (hmajor (((n : ℝ) + 1) * β) (by positivity))
          _ = |a| / β ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
            simp [mul_pow, div_eq_mul_inv, mul_inv, mul_comm, mul_assoc, mul_left_comm]
      have hinter := integral_tsum_of_summable_integral_norm hint hsum
      have heq : ∀ t ∈ Ioi (0 : ℝ), (∑' n : ℕ, F n t) =
          Real.sin (a * t) / (Real.exp (β * t) - 1) := by
        intro t ht
        dsimp only [F]
        rw [tsum_mul_right, geometric_kernel β t hβ ht]
        ring
      calc (∫ t in Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1))
        = ∫ t in Ioi (0 : ℝ), ∑' n : ℕ, F n t :=
          setIntegral_congr_fun measurableSet_Ioi (fun t ht => (heq t ht).symm)
        _ = ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), F n t := hinter.symm
        _ = _ := by
          apply tsum_congr
          intro n
          simpa only [F, neg_mul] using
            sine_exp_integral a (((n : ℝ) + 1) * β) (by positivity)

    rw [sine_planck_series a β hβ]
    have hterm (n : ℕ) :
        a / ((((n : ℝ) + 1) * β) ^ 2 + a ^ 2) =
          (1 / β) * ((a / β) / ((a / β) ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
      field_simp
      <;> ring
    simp_rw [hterm]
    rw [tsum_mul_left, coth_series (a / β) (div_pos ha hβ)]
    have harg : Real.pi * (a / β) = a * Real.pi / β := by ring
    simp_rw [harg]
    field_simp
    <;> ring
  have main_proof :
      ∫ t in Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1) =
        Real.pi / (2 * β) * (Real.cosh (a * Real.pi / β) / Real.sinh (a * Real.pi / β)) -
          1 / (2 * a) := by
    set F : ℕ → ℝ → ℝ := fun n t => Real.sin (a * t) * Real.exp (-(((n : ℝ) + 1) * β * t)) with hF
    have hc : ∀ n : ℕ, 0 < ((n : ℝ) + 1) * β := fun n => by positivity
    -- the dominating functions a t e^{-ct}
    have hdomI : ∀ n : ℕ, Integrable (fun t : ℝ => a * (t * Real.exp (-((((n : ℝ) + 1) * β) * t))))
        (volume.restrict (Ioi 0)) := by
      intro n
      refine Integrable.const_mul ?_ _
      refine Integrable.of_integral_ne_zero ?_
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := ((n : ℝ) + 1) * β)
        (by norm_num) (hc n)
      have hcg : ∫ t in Ioi (0 : ℝ), t * Real.exp (-((((n : ℝ) + 1) * β) * t)) =
          ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-((((n : ℝ) + 1) * β) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      rw [hcg, h, Real.Gamma_two]
      have := hc n
      positivity
    have hdomV : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), a * (t * Real.exp (-((((n : ℝ) + 1) * β) * t))) =
        a / ((((n : ℝ) + 1) * β) ^ 2) := by
      intro n
      rw [integral_const_mul]
      have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := ((n : ℝ) + 1) * β)
        (by norm_num) (hc n)
      have hcg : ∫ t in Ioi (0 : ℝ), t * Real.exp (-((((n : ℝ) + 1) * β) * t)) =
          ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-((((n : ℝ) + 1) * β) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
      rw [hcg, h, Real.Gamma_two, Real.rpow_two]
      field_simp
    have hbound : ∀ n : ℕ, ∀ t ∈ Ioi (0 : ℝ),
        ‖F n t‖ ≤ a * (t * Real.exp (-((((n : ℝ) + 1) * β) * t))) := by
      intro n t ht
      have ht0 : (0 : ℝ) < t := ht
      have hsin : |Real.sin (a * t)| ≤ a * t := by
        have := Real.abs_sin_le_abs (x := a * t)
        rwa [abs_of_pos (mul_pos ha ht0)] at this
      simp only [hF, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      have he := Real.exp_pos (-((((n : ℝ) + 1) * β) * t))
      rw [show -(((n : ℝ) + 1) * β * t) = -((((n : ℝ) + 1) * β) * t) by ring]
      nlinarith
    have hFm : ∀ n : ℕ, AEStronglyMeasurable (F n) (volume.restrict (Ioi 0)) := by
      intro n
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      fun_prop
    have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := by
      intro n
      refine (hdomI n).mono' (hFm n) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (hbound n)
    have hsumdom : Summable fun n : ℕ => a / ((((n : ℝ) + 1) * β) ^ 2) := by
      have h2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
        simpa using this
      have := h2.mul_left (a / β ^ 2)
      refine this.congr (fun n => ?_)
      field_simp
    have hsum : Summable fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
      refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
        (fun n => ?_) hsumdom
      rw [← hdomV n]
      exact setIntegral_mono_on (hint n).norm (hdomI n) measurableSet_Ioi (hbound n)
    have key := integral_tsum_of_summable_integral_norm hint hsum
    have hgeo : ∀ t ∈ Ioi (0 : ℝ), Real.sin (a * t) / (Real.exp (β * t) - 1) = ∑' n, F n t := by
      intro t ht
      simp only [hF]
      rw [tsum_mul_left, geom_1122b β t hβ ht]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hgeo, ← key]
    have hterm : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), F n t =
        (1 / (2 * β)) * (2 * (a / β) / ((a / β) ^ 2 + ((n : ℝ) + 1) ^ 2)) := by
      intro n
      have h := term_integral_1122b a (((n : ℝ) + 1) * β) (hc n)
      have hcg : ∫ t in Ioi (0 : ℝ), F n t =
          ∫ t in Ioi (0 : ℝ), Real.sin (a * t) * Real.exp (-((((n : ℝ) + 1) * β) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
        simp only [hF]
      rw [hcg, h]
      have hβ0 : β ≠ 0 := hβ.ne'
      have hd : 0 < a ^ 2 + (((n : ℝ) + 1) * β) ^ 2 := by positivity
      have hd' : 0 < (a / β) ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
      field_simp
    simp only [hterm]
    have hs := (coth_hasSum_1122b (a / β) (by positivity)).mul_left (1 / (2 * β))
    rw [hs.tsum_eq]
    have hβ0 : β ≠ 0 := hβ.ne'
    have ha0 : a ≠ 0 := ha.ne'
    rw [show Real.pi * (a / β) = a * Real.pi / β by ring]
    field_simp
  exact codex_proof.trans (main_proof.symm.trans main_proof)


#print axioms LeanLab.HelfgottMajor.Prep1122BinetSplit.sine_planck

end SinePlanck1122b

/-- LEAF: the Laplace transform of the sine, ∫_0^∞ e^{-uz} sin(ut) du = t/(t² + z²) for
real t and re z above 0, the inner integral of the interchange step from DLMF 5.9.13 to
DLMF 5.9.15, P0014 page 34 display 4.10 first line. Class EASY. PROVED here. -/
theorem laplace_sin (t : ℝ) (z : ℂ) (hz : 0 < z.re) :
    ∫ u in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * z) * (Real.sin (u * t) : ℂ) =
      (t : ℂ) / ((t : ℂ) ^ 2 + z ^ 2) := by
  have hA : (-z + t * I).re < 0 := by simp; linarith
  have hB : (-z - t * I).re < 0 := by simp; linarith
  have hpt : ∀ u : ℝ, Complex.exp (-(u : ℂ) * z) * (Real.sin (u * t) : ℂ) =
      (I / 2) * (Complex.exp ((-z - t * I) * u) - Complex.exp ((-z + t * I) * u)) := by
    intro u
    have e1 : Complex.exp ((-z - t * I) * u) =
        Complex.exp (-(u : ℂ) * z) * Complex.exp (-(((u * t : ℝ) : ℂ)) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp ((-z + t * I) * u) =
        Complex.exp (-(u : ℂ) * z) * Complex.exp (((u * t : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, Complex.ofReal_sin, Complex.sin]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub (integrableOn_exp_mul_complex_Ioi hB 0)
    (integrableOn_exp_mul_complex_Ioi hA 0), integral_exp_mul_complex_Ioi hB,
    integral_exp_mul_complex_Ioi hA]
  have h1 : z + t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : z - t * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h3 : (t : ℂ) ^ 2 + z ^ 2 = (z + t * I) * (z - t * I) := by
    ring_nf; rw [I_sq]; ring
  have hB' : -z - t * I = -(z + t * I) := by ring
  have hA' : -z + t * I = -(z - t * I) := by ring
  rw [h3, hB', hA']
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_neg, div_neg, neg_div, neg_div, neg_neg, neg_neg, div_sub_div _ _ h1 h2,
    eq_div_iff (mul_ne_zero h1 h2), mul_assoc, div_mul_cancel₀ _ (mul_ne_zero h1 h2)]
  ring_nf
  rw [I_sq]
  ring

/-- The kernel identity behind DLMF 5.9.13 to 5.9.15: for t positive,
1/t - 1/(1 - e^{-t}) = -1/2 - 2((π/(4π)) coth(tπ/(2π)) - 1/(2t)),
the right side being -1/2 - 2 ∫_0^∞ sin(tτ)/(e^{2πτ} - 1) dτ by `sine_planck`. -/
private lemma kernel_eq (t : ℝ) (ht : 0 < t) :
    1 / t - 1 / (1 - Real.exp (-t)) =
      -1 / 2 - 2 * (Real.pi / (2 * (2 * Real.pi)) *
        (Real.cosh (t * Real.pi / (2 * Real.pi)) / Real.sinh (t * Real.pi / (2 * Real.pi))) -
          1 / (2 * t)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hq : Real.pi / (2 * (2 * Real.pi)) = 1 / 4 := by field_simp; ring
  have hh : t * Real.pi / (2 * Real.pi) = t / 2 := by field_simp
  rw [hq, hh, Real.cosh_eq, Real.sinh_eq]
  set w := Real.exp (t / 2) with hw
  have hw1 : 1 < w := Real.one_lt_exp_iff.mpr (by linarith)
  have hw0 : 0 < w := by linarith
  have hneg : Real.exp (-(t / 2)) = w⁻¹ := by rw [Real.exp_neg]
  have hnegt : Real.exp (-t) = (w ^ 2)⁻¹ := by
    rw [hw, ← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [hneg, hnegt]
  have hwne : w ≠ 0 := hw0.ne'
  have hw2 : w ^ 2 - 1 ≠ 0 := by nlinarith
  have hwd : w - w⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : w * w = 1 := by
      have h0 := mul_inv_cancel₀ hwne
      rw [← h] at h0; exact h0
    nlinarith
  have hwd' : 1 - (w ^ 2)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : w ^ 2 = 1 := by rw [eq_comm, inv_eq_one] at h; exact h
    nlinarith
  have htne : t ≠ 0 := ht.ne'
  field_simp
  ring

/-- The bound τ/(e^{2πτ} - 1) ≤ e^{-πτ}/(2π) for τ positive, from sinh y ≥ y. -/
private lemma planck_le (τ : ℝ) (hτ : 0 < τ) :
    τ / (Real.exp (2 * Real.pi * τ) - 1) ≤ Real.exp (-(Real.pi * τ)) / (2 * Real.pi) := by
  have hy : 0 ≤ Real.pi * τ := by positivity
  have hs := (Real.self_le_sinh_iff (x := Real.pi * τ)).mpr hy
  rw [Real.sinh_eq] at hs
  have hE : 0 < Real.exp (2 * Real.pi * τ) - 1 := by
    have : 1 < Real.exp (2 * Real.pi * τ) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hsplit : Real.exp (2 * Real.pi * τ) = Real.exp (Real.pi * τ) * Real.exp (Real.pi * τ) := by
    rw [← Real.exp_add]; ring_nf
  have hprod : Real.exp (Real.pi * τ) * Real.exp (-(Real.pi * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.pi_pos
  have hepos := Real.exp_pos (Real.pi * τ)
  have hnpos := Real.exp_pos (-(Real.pi * τ))
  rw [div_le_div_iff₀ hE (by positivity)]
  -- τ · 2π ≤ e^{-y}(e^{2y} - 1) = e^{y} - e^{-y}
  have key : Real.exp (-(Real.pi * τ)) * (Real.exp (2 * Real.pi * τ) - 1) =
      Real.exp (Real.pi * τ) - Real.exp (-(Real.pi * τ)) := by
    rw [hsplit]
    have : Real.exp (-(Real.pi * τ)) * (Real.exp (Real.pi * τ) * Real.exp (Real.pi * τ)) =
        Real.exp (Real.pi * τ) := by
      rw [← mul_assoc, mul_comm (Real.exp (-(Real.pi * τ))), hprod, one_mul]
    linarith [this]
  rw [key]
  nlinarith

/-- P0014 page 34, display 4.10, first line, OLBC10 DLMF 5.9.15: Binet's second formula,
with the exact statement of the parent leaf `Prep1121VIPointwiseA.binet_formula`.
Assembled from the leaves `digamma_log_laplace`, `sine_planck` and `laplace_sin` by
Fubini on the product of two half lines. -/
theorem binet_formula (z : ℂ) (hz : 0 < z.re) :
    digamma z = Complex.log z - 1 / (2 * z) -
      2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1)) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set F : ℝ → ℝ → ℂ := fun t τ => Complex.exp (-(t : ℂ) * z) *
    ((Real.sin (t * τ) / (Real.exp (2 * Real.pi * τ) - 1) : ℝ) : ℂ) with hF
  -- integrability of e^{-tz} on the half line, and its integral 1/z
  have hz' : (-z).re < 0 := by simp; linarith
  have hexp_eq : (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) =
      fun t : ℝ => Complex.exp (-z * t) := by funext t; ring_nf
  have hexpI : Integrable (fun t : ℝ => Complex.exp (-(t : ℂ) * z)) μ := by
    rw [hexp_eq]; exact integrableOn_exp_mul_complex_Ioi hz' 0
  have hexpV : ∫ t, Complex.exp (-(t : ℂ) * z) ∂μ = 1 / z := by
    rw [hexp_eq, hμ, integral_exp_mul_complex_Ioi hz' 0]
    simp
  -- integrability of F on the product of half lines
  have hg1 : Integrable (fun t : ℝ => t * Real.exp (-(z.re * t))) μ := by
    refine Integrable.of_integral_ne_zero ?_
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := z.re) (by norm_num) hz
    have hc : ∫ t, t * Real.exp (-(z.re * t)) ∂μ =
        ∫ t in Ioi (0 : ℝ), t ^ ((2 : ℝ) - 1) * Real.exp (-(z.re * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [hc, h, Real.Gamma_two]
    positivity
  have hg2 : Integrable (fun τ : ℝ => Real.exp (-(Real.pi * τ)) / (2 * Real.pi)) μ := by
    refine Integrable.div_const ?_ _
    have := integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith [Real.pi_pos]) 0
    refine this.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    simp only [neg_mul]
  have hG := hg1.mul_prod hg2
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    fun_prop
  have hFI : Integrable (Function.uncurry F) (μ.prod μ) := by
    refine hG.mono' hFm.aestronglyMeasurable ?_
    rw [hμ, Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    obtain ⟨ht, hτ⟩ := hp
    have ht0 : (0 : ℝ) < p.1 := ht
    have hτ0 : (0 : ℝ) < p.2 := hτ
    have hE : 0 < Real.exp (2 * Real.pi * p.2) - 1 := by
      have : 1 < Real.exp (2 * Real.pi * p.2) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos hE]
    have hre : (-(p.1 : ℂ) * z).re = -(z.re * p.1) := by simp; ring
    rw [hre]
    have hsin : |Real.sin (p.1 * p.2)| ≤ p.1 * p.2 := by
      have := Real.abs_sin_le_abs (x := p.1 * p.2)
      rwa [abs_of_pos (mul_pos ht0 hτ0)] at this
    have hpl := planck_le p.2 hτ0
    have hq : |Real.sin (p.1 * p.2)| / (Real.exp (2 * Real.pi * p.2) - 1) ≤
        p.1 * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi)) := by
      calc |Real.sin (p.1 * p.2)| / (Real.exp (2 * Real.pi * p.2) - 1)
          ≤ p.1 * p.2 / (Real.exp (2 * Real.pi * p.2) - 1) :=
            div_le_div_of_nonneg_right hsin hE.le
        _ = p.1 * (p.2 / (Real.exp (2 * Real.pi * p.2) - 1)) := by ring
        _ ≤ p.1 * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hpl ht0.le
    calc Real.exp (-(z.re * p.1)) * (|Real.sin (p.1 * p.2)| / (Real.exp (2 * Real.pi * p.2) - 1))
        ≤ Real.exp (-(z.re * p.1)) * (p.1 * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi))) :=
          mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
      _ = p.1 * Real.exp (-(z.re * p.1)) * (Real.exp (-(Real.pi * p.2)) / (2 * Real.pi)) := by
          ring
  -- the inner integral in τ, through GR00 3.911.2
  have hinner : ∀ t : ℝ, 0 < t →
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z) =
        -(1 / 2) * Complex.exp (-(t : ℂ) * z) - 2 * ∫ τ, F t τ ∂μ := by
    intro t ht
    have hI : ∫ τ, F t τ ∂μ = Complex.exp (-(t : ℂ) * z) *
        ((∫ τ in Ioi (0 : ℝ), Real.sin (t * τ) / (Real.exp (2 * Real.pi * τ) - 1) : ℝ) : ℂ) := by
      simp only [hF]
      rw [integral_const_mul, hμ, integral_complex_ofReal]
    rw [hI, sine_planck t (2 * Real.pi) ht (by positivity)]
    have hk := kernel_eq t ht
    have hc : (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) =
        ((1 / t - 1 / (1 - Real.exp (-t)) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, hk]
    push_cast
    ring
  -- the outer integral in t, through the Laplace transform of the sine
  have houter : ∀ τ : ℝ, 0 < τ →
      ∫ t, F t τ ∂μ =
        (τ : ℂ) / (((τ : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * τ) : ℂ) - 1)) := by
    intro τ hτ
    have hE : (Real.exp (2 * Real.pi * τ) : ℂ) - 1 ≠ 0 := by
      have : 1 < Real.exp (2 * Real.pi * τ) := Real.one_lt_exp_iff.mpr (by positivity)
      intro h
      have h' : ((Real.exp (2 * Real.pi * τ) - 1 : ℝ) : ℂ) = 0 := by
        rw [Complex.ofReal_sub, Complex.ofReal_one]; exact h
      rw [Complex.ofReal_eq_zero] at h'
      linarith
    have hpt : ∀ t : ℝ, F t τ = (1 / ((Real.exp (2 * Real.pi * τ) : ℂ) - 1)) *
        (Complex.exp (-(t : ℂ) * z) * (Real.sin (t * τ) : ℂ)) := by
      intro t
      simp only [hF]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, hμ, laplace_sin τ z hz]
    field_simp
  -- assembly
  rw [digamma_log_laplace z hz]
  have hcongr : ∫ t in Ioi (0 : ℝ),
      (1 / (t : ℂ) - 1 / (1 - (Real.exp (-t) : ℂ))) * Complex.exp (-(t : ℂ) * z) =
      ∫ t, (-(1 / 2) * Complex.exp (-(t : ℂ) * z) - 2 * ∫ τ, F t τ ∂μ) ∂μ :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => hinner t ht)
  have hleft : Integrable (fun t => ∫ τ, F t τ ∂μ) μ := hFI.integral_prod_left
  rw [hcongr, integral_sub (hexpI.const_mul _) (hleft.const_mul _), integral_const_mul,
    integral_const_mul, hexpV, integral_integral_swap hFI]
  have hswap : ∫ τ, ∫ t, F t τ ∂μ ∂μ = ∫ τ in Ioi (0 : ℝ),
      (τ : ℂ) / (((τ : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * τ) : ℂ) - 1)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => houter τ hτ)
  rw [hswap]
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  field_simp
  ring

end LeanLab.HelfgottMajor.Prep1122BinetSplit
