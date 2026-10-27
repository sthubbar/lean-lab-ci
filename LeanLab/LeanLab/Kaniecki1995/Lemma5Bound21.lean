/-
P0022, Kaniecki 1995, inequality (21), p. 370, the bound for `I₂ = ∫_0^∞ k |B|²`,
`B(s) = Σ Λ(n)/n^{2s}`. PC run 20261021T0604Z-1697, unit U-1356, T1.

Proof as on p. 370, "To estimate I₂ we apply (9)": expand `|B(σ+it)|²` as the double series
`Σ_{m,n} a_m a_n cos(2 t (log m - log n))`, `a_n = Λ(n) n^{-2σ}`, integrate term by term
against the kernel `k`, and evaluate each term by (9), p. 365:
`∫_0^∞ k(t) cos(At) dt = 0` for `A ≥ δ`, `= π/(2σ) (e^{σ(2δ-A)} - e^{σA})` for `0 ≤ A < δ`.
PROVED here: the expansion, Fubini for the double series, and
`I₂ = Σ_{m,n} a_m a_n κ(2 |log m - log n|)`, `I2_eq`, CONDITIONAL ON (9) only; then
`0 ≤ κ(A) ≤ κ(0) ≤ π/(T(1-σ/T))`, so (21) follows from the arithmetic input `Near21`, the sum of
`a_m a_n` over the pairs with `2 |log m - log n| < δ`. Named inputs: `Kernel9A`, the paper's (9),
a classical integral; `Near21`, a statement about `Λ` only, no integral.
Also PROVED with no input: `bound21_weak`, the trivial bound `I₂ ≤ L(2σ)² ∫ k`.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Kernel

namespace LeanLab.Kaniecki1995.L5

open LeanLab.Kaniecki1995 Real MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt LSeries.notation ENNReal ComplexConjugate

/-! ### Definitions -/

/-- `δ`, with `e^δ = 1 + 1/T`. -/
noncomputable def dl (T : ℝ) : ℝ := Real.log (1 + 1 / T)

/-- The right side of (9), p. 365, for `A ≥ 0`. -/
noncomputable def kap (T σ A : ℝ) : ℝ :=
  if dl T ≤ A then 0 else π / (2 * σ) * (Real.exp (σ * (2 * dl T - A)) - Real.exp (σ * A))

/-- (9), p. 365: `∫_0^∞ |(e^{δ(σ+it)} - 1)/(σ+it)|² cos(At) dt = κ(A)` for `A ≥ 0`.
CITED classical integral, the paper's own (9). -/
def Kernel9A : Prop :=
  ∀ T σ A : ℝ, 0 < T → 0 < σ → 0 ≤ A →
    ∫ t in Ioi (0 : ℝ), kern T σ t * Real.cos (A * t) = kap T σ A

/-- `a_n = Λ(n) n^{-2σ}`. -/
noncomputable def aL (σ : ℝ) (n : ℕ) : ℝ := Λ n * (n : ℝ) ^ (-(2 * σ))

/-- The weight of the pair `(m, n)` after integration: `a_m a_n κ(2 |log m - log n|)`. -/
noncomputable def w21 (T σ : ℝ) (p : ℕ × ℕ) : ℝ :=
  aL σ p.1 * aL σ p.2 * kap T σ (2 * |Real.log p.1 - Real.log p.2|)

/-- The near diagonal sum: `Σ a_m a_n` over the pairs with `2 |log m - log n| < δ`. -/
noncomputable def near21 (T σ : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, if 2 * |Real.log p.1 - Real.log p.2| < dl T then aL σ p.1 * aL σ p.2 else 0

/-- The arithmetic input of (21): the near diagonal sum is at most
`0.886 + log² T/(8T a²c²) + log T/(4T² ac)`. A statement about `Λ` only. -/
def Near21 : Prop :=
  ∀ a c T : ℝ, 7.02 < T → 0 < c → 1 < a → sig a c T ≤ 3 / 4 →
    near21 T (sig a c T) ≤
      0.886 + Real.log T ^ 2 / (8 * T * a ^ 2 * c ^ 2) + Real.log T / (4 * T ^ 2 * a * c)

/-! ### The coefficients -/

theorem aL_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ aL σ n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

theorem aL_eq_norm_term (σ : ℝ) (n : ℕ) :
    aL σ n = ‖LSeries.term ↗Λ (((2 * σ : ℝ)) : ℂ) n‖ := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · simp [aL, hn]
  · simp only [Complex.ofReal_re, aL]
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem summable_aL {σ : ℝ} (hσ : 1 / 2 < σ) : Summable (aL σ) := by
  have h := summable_norm_iff.2
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (((2 * σ : ℝ)) : ℂ))
      (by simp; linarith))
  exact h.congr fun n => (aL_eq_norm_term σ n).symm

/-- `u_n(t) = a_n e^{-2it log n}`, the `n`-th term of `B(σ + it)`. -/
noncomputable def uB (σ t : ℝ) (n : ℕ) : ℂ :=
  (aL σ n : ℂ) * Complex.exp (((-(2 * t * Real.log n) : ℝ) : ℂ) * Complex.I)

theorem term_eq_uB (σ t : ℝ) (n : ℕ) :
    LSeries.term ↗Λ (2 * sAt σ t) n = uB σ t n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [uB, aL]
  rw [LSeries.term_of_ne_zero hn]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.natCast_log]
  unfold uB aL
  rw [Real.rpow_def_of_pos hpos]
  have : ((Real.log n : ℝ) : ℂ) * (2 * sAt σ t) =
      ((Real.log n * (2 * σ) : ℝ) : ℂ) + ((2 * t * Real.log n : ℝ) : ℂ) * Complex.I := by
    simp only [sAt]; push_cast; ring
  rw [this, Complex.exp_add, div_eq_mul_inv, mul_inv, ← Complex.exp_neg, ← Complex.exp_neg]
  have e1 : Complex.exp (-((Real.log n * (2 * σ) : ℝ) : ℂ)) =
      ((Real.exp (Real.log n * -(2 * σ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(((2 * t * Real.log n : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-(2 * t * Real.log n) : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [e1, e2, Complex.ofReal_mul]
  ring

theorem norm_uB (σ t : ℝ) (n : ℕ) : ‖uB σ t n‖ = aL σ n := by
  unfold uB
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (aL_nonneg σ n)]

theorem dirB_eq (σ t : ℝ) : dirB σ t = ∑' n, uB σ t n := by
  unfold dirB LSeries
  exact tsum_congr fun n => term_eq_uB σ t n

/-- the integrand of the double series -/
noncomputable def G21 (σ t : ℝ) (p : ℕ × ℕ) : ℝ :=
  aL σ p.1 * aL σ p.2 * Real.cos (2 * (Real.log p.1 - Real.log p.2) * t)

theorem re_uB_mul_conj (σ t : ℝ) (p : ℕ × ℕ) :
    (uB σ t p.1 * conj (uB σ t p.2)).re = G21 σ t p := by
  unfold uB G21
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_im]
  simp only [Real.cos_neg, Real.sin_neg]
  rw [show 2 * (Real.log p.1 - Real.log p.2) * t = 2 * t * Real.log p.1 - 2 * t * Real.log p.2 by
    ring, Real.cos_sub]
  ring

theorem summable_prod_aL {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun p : ℕ × ℕ => aL σ p.1 * aL σ p.2 := by
  have h := summable_mul_of_summable_norm (f := aL σ) (g := aL σ)
    ((summable_aL hσ).congr fun n => (Real.norm_of_nonneg (aL_nonneg σ n)).symm)
    ((summable_aL hσ).congr fun n => (Real.norm_of_nonneg (aL_nonneg σ n)).symm)
  exact h

theorem norm_G21_le (σ t : ℝ) (p : ℕ × ℕ) : ‖G21 σ t p‖ ≤ aL σ p.1 * aL σ p.2 := by
  unfold G21
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (aL_nonneg σ _) (aL_nonneg σ _))]
  exact mul_le_of_le_one_right (mul_nonneg (aL_nonneg σ _) (aL_nonneg σ _)) (abs_cos_le_one _)

theorem summable_norm_uB {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    Summable fun n => ‖uB σ t n‖ :=
  (summable_aL hσ).congr fun n => (norm_uB σ t n).symm

theorem summable_norm_conj_uB {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    Summable fun n => ‖conj (uB σ t n)‖ :=
  (summable_norm_uB hσ t).congr fun n => (Complex.norm_conj _).symm

theorem conj_dirB (σ t : ℝ) : conj (dirB σ t) = ∑' n, conj (uB σ t n) := by
  rw [dirB_eq]; exact Complex.conj_tsum _

theorem sq_norm_eq_re (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem dirB_mul_conj {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    dirB σ t * conj (dirB σ t) = ∑' p : ℕ × ℕ, uB σ t p.1 * conj (uB σ t p.2) := by
  rw [conj_dirB, dirB_eq]
  exact tsum_mul_tsum_of_summable_norm (summable_norm_uB hσ t) (summable_norm_conj_uB hσ t)

theorem re_tsum_uB {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    (∑' p : ℕ × ℕ, uB σ t p.1 * conj (uB σ t p.2)).re =
      ∑' p : ℕ × ℕ, (uB σ t p.1 * conj (uB σ t p.2)).re := by
  have hsum : Summable fun p : ℕ × ℕ => uB σ t p.1 * conj (uB σ t p.2) :=
    Summable.of_norm ((summable_prod_aL hσ).congr fun p => by
      rw [norm_mul, Complex.norm_conj, norm_uB, norm_uB])
  exact Complex.re_tsum hsum

/-- **The expansion**: `|B(σ+it)|² = Σ_{m,n} a_m a_n cos(2 (log m - log n) t)`. -/
theorem sq_norm_dirB {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    ‖dirB σ t‖ ^ 2 = ∑' p : ℕ × ℕ, G21 σ t p := by
  rw [sq_norm_eq_re, dirB_mul_conj hσ t, re_tsum_uB hσ t]
  exact tsum_congr fun p => re_uB_mul_conj σ t p

/-! ### Integrability of the kernel -/

theorem kern_nonneg (T σ t : ℝ) : 0 ≤ kern T σ t := by unfold kern; positivity

theorem integrableOn_kern {T σ : ℝ} (hT : 0 < T) (hσ : 0 < σ) :
    Integrable (kern T σ) (volume.restrict (Ioi 0)) := by
  have h := integrable_toReal_of_lintegral_ne_top (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t => ENNReal.ofReal (kern T σ t)) (measurable_kern T σ).ennreal_ofReal.aemeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_kern_le hT hσ))
  refine h.congr (ae_of_all _ fun t => ?_)
  exact ENNReal.toReal_ofReal (kern_nonneg T σ t)

/-! ### `I₂` as a double series, CONDITIONAL ON (9) -/

theorem kap_symm_arg (T σ : ℝ) (hK : Kernel9A) (hT : 0 < T) (hσ : 0 < σ) (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), kern T σ t * Real.cos (2 * x * t) = kap T σ (2 * |x|) := by
  rw [← hK T σ (2 * |x|) hT hσ (by positivity)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  congr 1
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, ← Real.cos_neg]; ring_nf

/-- **`I₂ = Σ_{m,n} a_m a_n κ(2 |log m - log n|)`**, CONDITIONAL ON (9), `Kernel9A`. -/
theorem I2_eq (hK : Kernel9A) {T σ : ℝ} (hT : 0 < T) (hσ : 1 / 2 < σ) :
    wInt T σ (dirB σ) = ENNReal.ofReal (∑' p : ℕ × ℕ, w21 T σ p) := by
  have hσ0 : 0 < σ := by linarith
  set μ := volume.restrict (Ioi (0 : ℝ))
  have hk := integrableOn_kern hT hσ0
  set LL := ∑' n, aL σ n
  have hnormB : ∀ t, ‖dirB σ t‖ ≤ LL := by
    intro t
    rw [dirB_eq]
    refine (norm_tsum_le_tsum_norm ((summable_aL hσ).congr fun n => (norm_uB σ t n).symm)).trans
      (le_of_eq (tsum_congr fun n => norm_uB σ t n))
  have hmeasF : AEStronglyMeasurable (fun t => kern T σ t * ‖dirB σ t‖ ^ 2) μ :=
    ((measurable_kern T σ).mul ((continuous_dirB hσ).norm.pow 2).measurable).aestronglyMeasurable
  have hF : Integrable (fun t => kern T σ t * ‖dirB σ t‖ ^ 2) μ := by
    refine (hk.mul_const (LL ^ 2)).mono' hmeasF (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kern_nonneg T σ t) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnormB t) 2)
      (kern_nonneg T σ t)
  have h1 : wInt T σ (dirB σ) = ENNReal.ofReal (∫ t, kern T σ t * ‖dirB σ t‖ ^ 2 ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun t =>
      mul_nonneg (kern_nonneg T σ t) (sq_nonneg _))).symm
  rw [h1]
  congr 1
  have hint : ∀ p : ℕ × ℕ, Integrable (fun t => kern T σ t * G21 σ t p) μ := by
    intro p
    refine (hk.mul_const (aL σ p.1 * aL σ p.2)).mono' ?_ (ae_of_all _ fun t => ?_)
    · refine ((measurable_kern T σ).mul ?_).aestronglyMeasurable
      unfold G21; fun_prop
    · rw [norm_mul, Real.norm_of_nonneg (kern_nonneg T σ t)]
      exact mul_le_mul_of_nonneg_left (norm_G21_le σ t p) (kern_nonneg T σ t)
  have hsumint : Summable fun p : ℕ × ℕ => ∫ t, ‖kern T σ t * G21 σ t p‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
      (fun p => ?_) ((summable_prod_aL hσ).mul_right (∫ t, kern T σ t ∂μ))
    rw [← integral_const_mul]
    refine integral_mono (hint p).norm (hk.const_mul _) fun t => ?_
    simp only
    rw [norm_mul, Real.norm_of_nonneg (kern_nonneg T σ t), mul_comm (aL σ p.1 * aL σ p.2)]
    exact mul_le_mul_of_nonneg_left (norm_G21_le σ t p) (kern_nonneg T σ t)
  calc ∫ t, kern T σ t * ‖dirB σ t‖ ^ 2 ∂μ
      = ∫ t, ∑' p : ℕ × ℕ, kern T σ t * G21 σ t p ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        simp only
        rw [sq_norm_dirB hσ t, tsum_mul_left]
    _ = ∑' p : ℕ × ℕ, ∫ t, kern T σ t * G21 σ t p ∂μ :=
        (integral_tsum_of_summable_integral_norm hint hsumint).symm
    _ = ∑' p : ℕ × ℕ, w21 T σ p := by
        refine tsum_congr fun p => ?_
        unfold w21
        have : ∀ t, kern T σ t * G21 σ t p =
            aL σ p.1 * aL σ p.2 * (kern T σ t * Real.cos (2 * (Real.log p.1 - Real.log p.2) * t)) :=
          fun t => by unfold G21; ring
        simp_rw [this]
        rw [integral_const_mul, kap_symm_arg T σ hK hT hσ0]

/-! ### Properties of `κ` -/

theorem dl_pos {T : ℝ} (hT : 0 < T) : 0 < dl T :=
  Real.log_pos (by have : 0 < 1 / T := one_div_pos.mpr hT; linarith)

theorem kap_nonneg {T σ A : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A) : 0 ≤ kap T σ A := by
  unfold kap
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    refine mul_nonneg (by positivity) (sub_nonneg.2 (Real.exp_le_exp.2 ?_))
    nlinarith

theorem kap_le_kap0 {T σ A : ℝ} (hT : 0 < T) (hσ : 0 < σ) (hA : 0 ≤ A) :
    kap T σ A ≤ kap T σ 0 := by
  have hd := dl_pos hT
  have h0 : kap T σ 0 = π / (2 * σ) * (Real.exp (σ * (2 * dl T - 0)) - Real.exp (σ * 0)) := by
    unfold kap; rw [if_neg (not_le.2 hd)]
  rw [h0]
  unfold kap
  split_ifs with h
  · exact mul_nonneg (by positivity) (sub_nonneg.2 (Real.exp_le_exp.2 (by nlinarith)))
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e1 : Real.exp (σ * (2 * dl T - A)) ≤ Real.exp (σ * (2 * dl T - 0)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e2 : Real.exp (σ * 0) ≤ Real.exp (σ * A) := Real.exp_le_exp.2 (by nlinarith)
    linarith

/-- `κ(0) = π ((1 + 1/T)^{2σ} - 1)/(2σ) ≤ π/(T(1 - σ/T))`, by `kernel_real_le`. -/
theorem kap0_le {T σ : ℝ} (hT : 0 < T) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) (hσT : σ < T) :
    kap T σ 0 ≤ π / (T * (1 - σ / T)) := by
  have hd := dl_pos hT
  unfold kap; rw [if_neg (not_le.2 hd)]
  refine le_trans (le_of_eq ?_) (kernel_real_le hT hσ1 hσ2 hσT)
  have hb : (0 : ℝ) < 1 + 1 / T := by have := one_div_pos.mpr hT; linarith
  rw [Real.rpow_def_of_pos hb, dl]
  congr 2
  · ring_nf
  · simp

theorem w21_le {T σ : ℝ} (hT : 0 < T) (hσ : 0 < σ) (p : ℕ × ℕ) :
    w21 T σ p ≤ kap T σ 0 *
      (if 2 * |Real.log p.1 - Real.log p.2| < dl T then aL σ p.1 * aL σ p.2 else 0) := by
  unfold w21
  have hab := mul_nonneg (aL_nonneg σ p.1) (aL_nonneg σ p.2)
  split_ifs with h
  · rw [mul_comm (kap T σ 0)]
    exact mul_le_mul_of_nonneg_left (kap_le_kap0 hT hσ (by positivity)) hab
  · push_neg at h
    have : kap T σ (2 * |Real.log p.1 - Real.log p.2|) = 0 := by unfold kap; rw [if_pos h]
    rw [this]; simp

theorem summable_near {σ T : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun p : ℕ × ℕ =>
      if 2 * |Real.log p.1 - Real.log p.2| < dl T then aL σ p.1 * aL σ p.2 else 0 :=
  Summable.of_nonneg_of_le (fun p => by split_ifs <;> simp [mul_nonneg, aL_nonneg])
    (fun p => by split_ifs <;> simp [mul_nonneg, aL_nonneg]) (summable_prod_aL hσ)

/-- **`I₂ ≤ κ(0) · near21`**, CONDITIONAL ON (9). -/
theorem I2_le_near (hK : Kernel9A) {T σ : ℝ} (hT : 0 < T) (hσ : 1 / 2 < σ) :
    wInt T σ (dirB σ) ≤ ENNReal.ofReal (kap T σ 0 * near21 T σ) := by
  have hσ0 : 0 < σ := by linarith
  rw [I2_eq hK hT hσ]
  apply ENNReal.ofReal_le_ofReal
  unfold near21
  rw [← tsum_mul_left]
  have hs1 : Summable (w21 T σ) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (mul_nonneg (aL_nonneg σ _) (aL_nonneg σ _))
      (kap_nonneg hσ0 (by positivity)))
      (fun p => (w21_le hT hσ0 p).trans (by
        split_ifs <;> simp [mul_comm, le_refl]))
      ((summable_near (T := T) hσ).mul_left (kap T σ 0))
  exact hs1.tsum_le_tsum (w21_le hT hσ0) ((summable_near hσ).mul_left _)

/-- **(21), p. 370**, CONDITIONAL ON `Kernel9A`, the paper's (9), and `Near21`. -/
theorem bound21_of (hK : Kernel9A) (hN : Near21) : Bound21 := by
  intro a c T hT hc ha hs
  have hT0 : 0 < T := by linarith
  have hσ1 := sig_gt_half hT hc ha
  refine (I2_le_near hK hT0 hσ1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hnear0 : 0 ≤ near21 T (sig a c T) :=
    tsum_nonneg fun p => by split_ifs <;> simp [mul_nonneg, aL_nonneg]
  have hden : 0 < T * (1 - sig a c T / T) := by
    rw [show T * (1 - sig a c T / T) = T - sig a c T by field_simp]; linarith
  have hpi : 0 ≤ π / (T * (1 - sig a c T / T)) := div_nonneg Real.pi_pos.le hden.le
  exact mul_le_mul (kap0_le hT0 hσ1.le (by linarith) (by linarith)) (hN a c T hT hc ha hs)
    hnear0 hpi

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920`, `Kernel9A`, `Near21`, `Const4`. -/
theorem lemma5_of_21 (h4 : Lemma4) (hP : Parseval1920) (hK : Kernel9A) (hN : Near21)
    (hC : Const4) : Lemma5 :=
  lemma5_of_K4 h4 hP (bound21_of hK hN) hC

/-! ### The trivial bound, PROVED with no input -/

/-- **`I₂ ≤ L(2σ)² ∫_0^∞ k`**, `L(2σ) = Σ Λ(n) n^{-2σ}`, with the kernel bound of
`lintegral_kern_le`. Too weak for (21): `L(2σ)` is about `log T/(2ac)`. -/
theorem bound21_weak {T σ : ℝ} (hT : 0 < T) (hσ : 1 / 2 < σ) :
    wInt T σ (dirB σ) ≤ ENNReal.ofReal ((∑' n, aL σ n) ^ 2 *
      ((Real.exp (Real.log (1 + 1 / T) * σ) - 1) ^ 2 * (π / 2 / σ) +
        4 * Real.exp (Real.log (1 + 1 / T) * σ) * (Real.log (1 + 1 / T) / 2) ^ 2 *
          (π / 2 / (Real.log (1 + 1 / T) / 2)))) := by
  have hσ0 : 0 < σ := by linarith
  set LL := ∑' n, aL σ n
  have hnormB : ∀ t, ‖dirB σ t‖ ≤ LL := by
    intro t
    rw [dirB_eq]
    refine (norm_tsum_le_tsum_norm ((summable_aL hσ).congr fun n => (norm_uB σ t n).symm)).trans
      (le_of_eq (tsum_congr fun n => norm_uB σ t n))
  calc wInt T σ (dirB σ)
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (LL ^ 2) * ENNReal.ofReal (kern T σ t) := by
        refine lintegral_mono fun t => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have : ‖dirB σ t‖ ^ 2 ≤ LL ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnormB t) 2
        nlinarith [kern_nonneg T σ t]
    _ = ENNReal.ofReal (LL ^ 2) * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (kern T σ t) :=
        lintegral_const_mul _ (measurable_kern T σ).ennreal_ofReal
    _ ≤ ENNReal.ofReal (LL ^ 2) * ENNReal.ofReal
          ((Real.exp (Real.log (1 + 1 / T) * σ) - 1) ^ 2 * (π / 2 / σ) +
            4 * Real.exp (Real.log (1 + 1 / T) * σ) * (Real.log (1 + 1 / T) / 2) ^ 2 *
              (π / 2 / (Real.log (1 + 1 / T) / 2))) := by
        gcongr; exact lintegral_kern_le hT hσ0
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-! ### Vacuity: the range hypotheses of `Bound21` hold -/

/-- At `a = 1.96745`, `c = 1.32149`, `T = e^{51}` the hypotheses of `Bound21` hold. -/
theorem bound21_hyps_K : 7.02 < Real.exp 51 ∧ (0 : ℝ) < 1.32149 ∧ (1 : ℝ) < 1.96745 ∧
    sig 1.96745 1.32149 (Real.exp 51) ≤ 3 / 4 := by
  refine ⟨?_, by norm_num, by norm_num, ?_⟩
  · have := Real.add_one_le_exp (51 : ℝ); linarith
  · unfold sig; rw [Real.log_exp]; norm_num

end LeanLab.Kaniecki1995.L5

#print axioms LeanLab.Kaniecki1995.L5.aL_eq_norm_term
#print axioms LeanLab.Kaniecki1995.L5.term_eq_uB
#print axioms LeanLab.Kaniecki1995.L5.re_uB_mul_conj
#print axioms LeanLab.Kaniecki1995.L5.sq_norm_dirB
#print axioms LeanLab.Kaniecki1995.L5.integrableOn_kern
#print axioms LeanLab.Kaniecki1995.L5.I2_eq
#print axioms LeanLab.Kaniecki1995.L5.kap_nonneg
#print axioms LeanLab.Kaniecki1995.L5.kap_le_kap0
#print axioms LeanLab.Kaniecki1995.L5.kap0_le
#print axioms LeanLab.Kaniecki1995.L5.I2_le_near
#print axioms LeanLab.Kaniecki1995.L5.bound21_of
#print axioms LeanLab.Kaniecki1995.L5.lemma5_of_21
#print axioms LeanLab.Kaniecki1995.L5.bound21_weak
#print axioms LeanLab.Kaniecki1995.L5.bound21_hyps_K
