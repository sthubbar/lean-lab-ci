/-
P0069, page 22, horizontal sides for display 3.36.
The final Perron bound is CONDITIONAL on the remaining horizontal leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp488b

namespace LeanLab.BHP1997.DecompC165a.Contour230
open Classical Complex MeanValue132 MeasureTheory Set Filter
open scoped Topology

/-- LEAF. P0069 Baker Harman Pintz 1997, page 22, Lemma 8 as it is used in the
horizontal display before 3.36: the exponent is taken at epsilon equal to the
reciprocal of log x, so that the maximum reads (qT)^(c - sigma) with c equal to
1/2 + 1/log x. The uniformity in epsilon costs one factor log x, the zeta value at
one plus epsilon in Rademacher reference 28. The safe height keeps the pole term
bounded. CITED and OPEN. -/
theorem horizontal_convexity_input :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (q : ℕ) [NeZero q], 1 ≤ q → (q : ℝ) ≤ x →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x →
        1 / 4 ≤ |τ| → |τ| ≤ 2 * x →
        ‖χ.LFunction (((1 / 2 + σ : ℝ) : ℂ) + τ * I)‖ ≤
          C * Real.log x *
            (((q : ℝ) * (|τ| + 1)) ^ (1 / 2 + 1 / Real.log x - σ) + 1) := by
  sorry

/-- P0069 Baker Harman Pintz 1997, page 22, the maximum over sigma in [0, c] in the
horizontal display before 3.36. The product is log-convex in sigma, so it is
bounded by its two endpoint values. -/
theorem horizontal_endpoint_max {Y Z c σ : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z)
    (hσ0 : 0 ≤ σ) (hσc : σ ≤ c) :
    Y ^ (c - σ) * Z ^ σ ≤ Y ^ c + Z ^ c := by
  have hY0 : 0 < Y := by linarith
  have hZ0 : 0 < Z := by linarith
  rcases le_total Y Z with h | h
  · have h1 : Y ^ (c - σ) ≤ Z ^ (c - σ) :=
      Real.rpow_le_rpow hY0.le h (by linarith)
    have h2 : Z ^ (c - σ) * Z ^ σ = Z ^ c := by
      rw [← Real.rpow_add hZ0]; ring_nf
    have h3 : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le _
    have h4 : 0 ≤ Z ^ σ := Real.rpow_nonneg hZ0.le _
    nlinarith [mul_le_mul_of_nonneg_right h1 h4]
  · have h1 : Z ^ σ ≤ Y ^ σ := Real.rpow_le_rpow hZ0.le h hσ0
    have h2 : Y ^ (c - σ) * Y ^ σ = Y ^ c := by
      rw [← Real.rpow_add hY0]; ring_nf
    have h3 : 0 ≤ Z ^ c := Real.rpow_nonneg hZ0.le _
    have h4 : 0 ≤ Y ^ (c - σ) := Real.rpow_nonneg hY0.le _
    nlinarith [mul_le_mul_of_nonneg_left h1 h4]

/-- P0069 Baker Harman Pintz 1997, page 22, the endpoint evaluation in the
horizontal display before 3.36: with c equal to 1/2 + 1/log x, any quantity at
most a fixed power of x loses only a bounded factor against its square root. -/
theorem log_scale_power_le {x Y : ℝ} (hx : 2 ≤ x) (hY : 0 < Y) (hYx : Y ≤ x ^ 4) :
    Y ^ (1 / 2 + 1 / Real.log x) ≤ Real.exp 4 * Real.sqrt Y := by
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.rpow_add hY, Real.sqrt_eq_rpow, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hY.le _)
  rw [Real.rpow_def_of_pos hY]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log Y ≤ 4 * Real.log x := by
    have := Real.log_le_log hY hYx
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  rw [mul_one_div, div_le_iff₀ hL]
  exact hlog

/-- P0069 Baker Harman Pintz 1997, page 22, the horizontal display before 3.36,
pointwise form. On either horizontal side at the safe height, the integrand is
bounded by log x times q^(1/2) T^(-1/2) + N^(1/2) T^(-1). This combines the cited
strip bound with the kernel bound, the maximum over sigma and the endpoint
evaluation. CONDITIONAL on horizontal_convexity_input. -/
theorem horizontal_pointwise_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t σ u : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
      0 ≤ σ → σ ≤ 1 / 2 + 1 / Real.log x → |u| = height T t →
        ‖integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((σ : ℂ) + u * I)‖ ≤
          K * Real.log x * (Real.sqrt q / Real.sqrt T + Real.sqrt N / T) := by
  obtain ⟨C, hC, hL⟩ := horizontal_convexity_input
  refine ⟨24 * C * Real.exp 4, by positivity, ?_⟩
  intro x N T q _ χ t σ u hx hN hNx hT hTx hq hqx ht hσ0 hσc hu
  obtain ⟨hHc, hH1, hHT, hm, hp⟩ := height_spec (t := t) hT
  have hHlow : T / 2 ≤ height T t := by rcases hHc with h | h <;> linarith
  have hH0 : 0 < height T t := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hT0 : 0 < T := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  -- the imaginary part on the side
  have hτlow : 1 / 4 ≤ |t + u| := by
    rcases (abs_eq hH0.le).mp hu with h | h
    · rw [h]; exact hp
    · rw [h, ← sub_eq_add_neg]; exact hm
  have hτup : |t + u| ≤ 2 * T := by
    have := abs_add_le t u
    linarith
  have hLb := hL x hx q hq hqx χ σ (t + u) hσ0 hσc hτlow (by linarith)
  have he : Thm4.half t + ((σ : ℂ) + u * I) =
      (((1 / 2 + σ : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I) := by
    unfold Thm4.half
    push_cast
    ring
  -- the kernel
  obtain ⟨ha2, haN, -⟩ := half_endpoint_bounds N hN
  set a : ℝ := (⌊N⌋₊ : ℝ) + 1 / 2 with ha
  have ha0 : 0 < a := by linarith
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hu; linarith
  have hn : |u| ≤ ‖((σ : ℂ) + u * I)‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + u * I)
  have hz : ((σ : ℂ) + u * I) ≠ 0 :=
    norm_pos_iff.mp ((abs_pos.mpr hu0).trans_le hn)
  have hk := kernel_strip_bound a (1 / 2) hz
  have hk' : ‖kernel a (1 / 2) ((σ : ℂ) + u * I)‖ ≤
      (Real.exp (Real.log a * σ) + Real.exp (Real.log (1 / 2) * σ)) / |u| := by
    apply hk.trans
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hu0) hn
  rw [← Real.rpow_def_of_pos ha0, hu] at hk'
  have hhalf : Real.exp (Real.log (1 / 2) * σ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
    nlinarith
  have haσ : 1 ≤ a ^ σ := Real.one_le_rpow (by linarith) hσ0
  have hK2 : ‖kernel a (1 / 2) ((σ : ℂ) + u * I)‖ ≤ 2 * a ^ σ / height T t := by
    apply hk'.trans
    apply div_le_div_of_nonneg_right _ hH0.le
    linarith
  -- the maximum over sigma and the endpoints
  set c : ℝ := 1 / 2 + 1 / Real.log x with hc
  set Y : ℝ := (q : ℝ) * (|t + u| + 1) with hY
  have hY1 : 1 ≤ Y := by
    have : 1 ≤ |t + u| + 1 := by linarith [abs_nonneg (t + u)]
    nlinarith only [this, hq1]
  have hY3 : Y ≤ 3 * q * T := by
    have : |t + u| + 1 ≤ 3 * T := by linarith
    have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ q)
    linarith
  have hx4 : 3 * x * x ≤ x ^ 4 := by
    have hs : 4 ≤ x * x := by nlinarith only [hx]
    have h4 : x ^ 4 = (x * x) * (x * x) := by ring
    rw [h4]; nlinarith only [hs, hx]
  have hYx : Y ≤ x ^ 4 := by
    have : (q : ℝ) * T ≤ x * x := mul_le_mul hqx hTx hT0.le (by linarith)
    linarith
  have hax : a ≤ x ^ 4 := by
    have : x + 1 / 2 ≤ 3 * x * x := by nlinarith only [hx]
    linarith only [this, hx4, haN, hNx]
  have hYc : Y ^ c ≤ Real.exp 4 * (2 * Real.sqrt q * Real.sqrt T) := by
    apply (log_scale_power_le hx (by linarith) hYx).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 4).le
    calc Real.sqrt Y ≤ Real.sqrt (3 * q * T) := Real.sqrt_le_sqrt hY3
      _ = Real.sqrt 3 * Real.sqrt q * Real.sqrt T := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
      _ ≤ 2 * Real.sqrt q * Real.sqrt T := by
        have h3 : Real.sqrt 3 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have := mul_le_mul_of_nonneg_right h3
          (mul_nonneg (Real.sqrt_nonneg (q : ℝ)) (Real.sqrt_nonneg T))
        linarith
  have hac : a ^ c ≤ Real.exp 4 * (2 * Real.sqrt N) := by
    apply (log_scale_power_le hx ha0 hax).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 4).le
    calc Real.sqrt a ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 2 * Real.sqrt N := Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.sqrt N := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg N)
  have hσc' : a ^ σ ≤ a ^ c := Real.rpow_le_rpow_of_exponent_le (by linarith) hσc
  have hmax := horizontal_endpoint_max hY1 (by linarith : 1 ≤ a) hσ0 hσc
  have hE : (Y ^ (c - σ) + 1) * a ^ σ ≤
      Real.exp 4 * (2 * Real.sqrt q * Real.sqrt T) + 2 * (Real.exp 4 * (2 * Real.sqrt N)) := by
    have hYc0 : 0 ≤ Y ^ c := Real.rpow_nonneg (by linarith) _
    nlinarith only [hmax, hσc', hYc, hac, hYc0]
  -- the product
  have hprod : ‖integrand a (1 / 2) χ t ((σ : ℂ) + u * I)‖ ≤
      C * Real.log x * (2 * ((Y ^ (c - σ) + 1) * a ^ σ)) / height T t := by
    unfold integrand
    rw [norm_mul, he]
    have hP0 : 0 ≤ C * Real.log x * (Y ^ (c - σ) + 1) := by positivity
    calc _ ≤ C * Real.log x * (Y ^ (c - σ) + 1) * (2 * a ^ σ / height T t) :=
          mul_le_mul hLb hK2 (norm_nonneg _) hP0
      _ = _ := by ring
  apply hprod.trans
  rw [div_le_iff₀ hH0]
  have hA : (Real.sqrt q / Real.sqrt T + Real.sqrt N / T) * T =
      Real.sqrt q * Real.sqrt T + Real.sqrt N := by
    rw [add_mul, div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt,
      div_mul_cancel₀ _ hT0.ne']
  have hA0 : 0 ≤ Real.sqrt q / Real.sqrt T + Real.sqrt N / T := by positivity
  have hCl : 0 ≤ C * Real.log x := by positivity
  have hstep : 24 * C * Real.exp 4 * Real.log x *
      (Real.sqrt q / Real.sqrt T + Real.sqrt N / T) * (T / 2) ≤
      24 * C * Real.exp 4 * Real.log x *
      (Real.sqrt q / Real.sqrt T + Real.sqrt N / T) * height T t :=
    mul_le_mul_of_nonneg_left hHlow (by positivity)
  have hid : 24 * C * Real.exp 4 * Real.log x *
      (Real.sqrt q / Real.sqrt T + Real.sqrt N / T) * (T / 2) =
      12 * (C * Real.log x) * Real.exp 4 * (Real.sqrt q * Real.sqrt T + Real.sqrt N) := by
    rw [← hA]; ring
  have hE' := mul_le_mul_of_nonneg_left hE hCl
  have hsq : 0 ≤ Real.sqrt q * Real.sqrt T := by positivity
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have he4 : 0 < Real.exp 4 := Real.exp_pos 4
  have hm1 : 0 ≤ C * Real.log x * Real.exp 4 * (Real.sqrt q * Real.sqrt T) := by positivity
  have hm2 : 0 ≤ C * Real.log x * Real.exp 4 * Real.sqrt N := by positivity
  nlinarith only [hstep, hid, hE', hm1, hm2]

/-- Page 22, horizontal segment estimate before display 3.36.
Subtracting the normalized rectangle integral removes the residue exactly.
The remaining difference is the two horizontal integrals at the safe height.
Split in burst 2: proved from horizontal_pointwise_bound by the length estimate
on each side. The binder h8 is no longer used. CONDITIONAL on
horizontal_convexity_input, the uniform form of Lemma 8. -/
theorem safe_height_horizontal_bound (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x →
      1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
        ‖(1 / (2 * (Real.pi : ℂ) * I)) *
          ((∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
            integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
              ((σ : ℂ) - height T t * I)) -
           (∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
            integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
              ((σ : ℂ) + height T t * I)))‖ ≤
          C * Real.log x * (Real.sqrt q / Real.sqrt T) +
          C * Real.log x * (Real.sqrt N / T) := by
  obtain ⟨K, hK, hpt⟩ := horizontal_pointwise_bound
  refine ⟨K, hK, ?_⟩
  intro x N T q _ χ t hx hN hNx hT hTx hq hqx ht
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hc0 : 0 ≤ 1 / 2 + 1 / Real.log x := by positivity
  have hc2 : 1 / 2 + 1 / Real.log x ≤ 2 := by
    have h2 := Real.log_two_gt_d9
    have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hi : 1 / Real.log x ≤ 1 / (0.6931471803 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have : 1 / (0.6931471803 : ℝ) ≤ 3 / 2 := by norm_num
    linarith
  have hH0 : 0 ≤ height T t := by linarith [(height_spec (t := t) hT).2.1]
  set M := K * Real.log x * (Real.sqrt q / Real.sqrt T + Real.sqrt N / T) with hM
  have hM0 : 0 ≤ M := by positivity
  have h1 : ‖∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
      integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((σ : ℂ) - height T t * I)‖ ≤
      M * |1 / 2 + 1 / Real.log x - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    rw [Set.uIoc_of_le hc0] at hσ
    have he : (σ : ℂ) - height T t * I = (σ : ℂ) + ((-height T t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [he]
    exact hpt x N T q χ t σ (-height T t) hx hN hNx hT hTx hq hqx ht hσ.1.le hσ.2
      (by rw [abs_neg, abs_of_nonneg hH0])
  have h2 : ‖∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
      integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((σ : ℂ) + height T t * I)‖ ≤
      M * |1 / 2 + 1 / Real.log x - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    rw [Set.uIoc_of_le hc0] at hσ
    exact hpt x N T q χ t σ (height T t) hx hN hNx hT hTx hq hqx ht hσ.1.le hσ.2
      (abs_of_nonneg hH0)
  rw [sub_zero, abs_of_nonneg hc0] at h1 h2
  have hcM : M * (1 / 2 + 1 / Real.log x) ≤ M * 2 := mul_le_mul_of_nonneg_left hc2 hM0
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  rw [norm_mul, hnorm]
  have hsub := norm_sub_le
    (∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
      integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((σ : ℂ) - height T t * I))
    (∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
      integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((σ : ℂ) + height T t * I))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  rw [show K * Real.log x * (Real.sqrt q / Real.sqrt T) +
      K * Real.log x * (Real.sqrt N / T) = M by rw [hM]; ring]
  rw [one_div, inv_mul_le_iff₀ hpi]
  nlinarith

/-- Page 22, the rectangle bookkeeping before display 3.36.
The right line minus the left line minus the rectangle is the negative horizontal part. -/
theorem horizontal_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x N T t : ℝ) :
    rightIntegral x N T χ t - lineIntegral N T χ t -
      RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
        (-((height T t : ℂ) * I))
        (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I) =
      -((1 / (2 * (Real.pi : ℂ) * I)) *
        ((∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
          integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
            ((σ : ℂ) - height T t * I)) -
         (∫ σ in (0 : ℝ)..(1 / 2 + 1 / Real.log x),
          integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t
            ((σ : ℂ) + height T t * I)))) := by
  have he (u : ℝ) : Thm4.half t + (u : ℂ) * I = Thm4.half (t + u) := by
    unfold Thm4.half
    push_cast
    ring
  have hleft : lineIntegral N T χ t =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u in (-height T t)..height T t,
          integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t ((u : ℂ) * I) := by
    simp only [lineIntegral, rawLineIntegral, integrand, he]
  rw [hleft]
  unfold rightIntegral RectangleIntegral' RectangleIntegral HIntegral VIntegral
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero,
    Complex.add_re, add_zero, Complex.neg_im, Complex.mul_im, zero_mul,
    zero_add, Complex.add_im, Complex.ofReal_zero, Complex.ofReal_neg, neg_mul, smul_eq_mul, sub_eq_add_neg]
  have hcoef : ((1 / (2 * Real.pi) : ℝ) : ℂ) =
      (1 / (2 * (Real.pi : ℂ) * I)) * I := by
    push_cast
    field_simp
  rw [hcoef]
  ring

/-- Page 22, the absolutely convergent part of either horizontal segment.
Stay delta to the right of real part one for the L-function.
No convexity or other cited input is used. -/
theorem right_half_horizontal_integrand_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b t : ℝ) {σ u δ : ℝ}
    (hδ : 0 < δ) (hσ : 1 / 2 + δ ≤ σ) (hu : u ≠ 0) :
    ‖integrand a b χ t ((σ : ℂ) + u * I)‖ ≤
      (1 + 1 / δ) *
        ((Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u|) := by
  have hδ' : 0 < σ - 1 / 2 := by linarith
  have he : Thm4.half t + ((σ : ℂ) + u * I) =
      (((1 + (σ - 1 / 2) : ℝ) : ℂ) + (t + u) * I) := by
    unfold Thm4.half
    push_cast
    ring
  have hL : ‖χ.LFunction (Thm4.half t + ((σ : ℂ) + u * I))‖ ≤ 1 + 1 / δ := by
    rw [he]
    have hi : 1 / (σ - 1 / 2) ≤ 1 / δ :=
      one_div_le_one_div_of_le hδ (by linarith)
    have hh := LFunction_right_bound χ (t := t + u) hδ'
    push_cast at hh ⊢
    linarith
  have hn : |u| ≤ ‖((σ : ℂ) + u * I)‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + u * I)
  have hz : ((σ : ℂ) + u * I) ≠ 0 :=
    norm_pos_iff.mp ((abs_pos.mpr hu).trans_le hn)
  have hk := kernel_strip_bound a b hz
  have hk' : ‖kernel a b ((σ : ℂ) + u * I)‖ ≤
      (Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u| := by
    apply hk.trans
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hu) hn
  exact (norm_mul _ _).le.trans (mul_le_mul hL hk' (norm_nonneg _) (by positivity))

/-- Page 22, the strip estimate supplied directly by the cited Lemma 8.
This keeps the epsilon loss explicit. CONDITIONAL on Lemma8. -/
theorem strip_horizontal_integrand_bound (h8 : MeanValue132.Lemma8) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, ∀ a b t σ u : ℝ,
      0 ≤ σ → σ ≤ 1 / 2 → u ≠ 0 → 1 / 4 ≤ |t + u| →
        ‖integrand a b χ t ((σ : ℂ) + u * I)‖ ≤
          C * (((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 4) *
            ((Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u|) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h8 ε hε
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ a b t σ u hσ0 hσ1 hu hsep
  let s : ℂ := (((1 / 2 + σ : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)
  have hp : 1 / 4 ≤ ‖s - 1‖ := by
    apply hsep.trans
    simpa [s] using Complex.abs_im_le_norm (s - 1)
  have hs : s ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero] at hp
    norm_num at hp
  have hpole : 1 / ‖s - 1‖ ≤ 4 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4) hp
    norm_num at hh
    simpa only [one_div] using hh
  have hh := hbound q hq χ (1 / 2 + σ) (t + u) (by linarith) (by linarith) hs
  have hexp : 1 + ε - (1 / 2 + σ) = 1 / 2 + ε - σ := by ring
  rw [hexp] at hh
  have he : Thm4.half t + ((σ : ℂ) + u * I) = s := by
    dsimp [s, Thm4.half]
    push_cast
    ring
  have hL : ‖χ.LFunction (Thm4.half t + ((σ : ℂ) + u * I))‖ ≤
      C * (((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 4) := by
    rw [he]
    have ht : ((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 1 / ‖s - 1‖ ≤
        ((q : ℝ) * (|t + u| + 1)) ^ (1 / 2 + ε - σ) + 4 := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left ht hC.le)
  have hn : |u| ≤ ‖((σ : ℂ) + u * I)‖ := by
    simpa using Complex.abs_im_le_norm ((σ : ℂ) + u * I)
  have hz : ((σ : ℂ) + u * I) ≠ 0 :=
    norm_pos_iff.mp ((abs_pos.mpr hu).trans_le hn)
  have hk := kernel_strip_bound a b hz
  have hk' : ‖kernel a b ((σ : ℂ) + u * I)‖ ≤
      (Real.exp (Real.log a * σ) + Real.exp (Real.log b * σ)) / |u| := by
    apply hk.trans
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero]
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hu) hn
  exact (norm_mul _ _).le.trans (mul_le_mul hL hk' (norm_nonneg _) (by positivity))


/-- Page 22, display 3.36. The residue identity bounds the rectangle contribution. -/
theorem safe_rectangle_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x N T : ℝ}
    (hx : 2 ≤ x) (hN : 2 ≤ N) (hT : 2 ≤ T) (t : ℝ) :
    ‖RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
      (-((height T t : ℂ) * I))
      (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I)‖ ≤
        12 * (if χ = 1 then Real.sqrt N / (1 + |t|) else 0) := by
  let c : ℝ := 1 / 2 + 1 / Real.log x
  let H : ℝ := height T t
  have hH : 1 ≤ H := (height_spec (t := t) hT).2.1
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hc : 1 / 2 < c := by dsimp [c]; linarith [one_div_pos.mpr hlog]
  have hre : (-((H : ℂ) * I)).re ≤ ((c : ℂ) + H * I).re := by
    simp; linarith
  have him : (-((H : ℂ) * I)).im ≤ ((c : ℂ) + H * I).im := by
    simp; linarith
  by_cases hχ : χ = 1
  · subst χ
    simp only [ite_true]
    by_cases ht : |t| < H
    · have hp : Rectangle (-((H : ℂ) * I)) ((c : ℂ) + H * I) ∈
          𝓝 (1 - Thm4.half t) := by
        rw [rectangle_mem_nhds_iff]
        have htt := abs_lt.mp ht
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
          sub_self, neg_zero, Complex.add_re, add_zero, Complex.neg_im,
          Complex.mul_im, zero_mul, zero_add, Complex.add_im, Complex.sub_re,
          Complex.one_re, Complex.sub_im, Complex.one_im, Thm4.half]
        rw [Set.uIoo_of_le (by linarith : (0 : ℝ) ≤ c),
          Set.uIoo_of_le (by linarith : -H ≤ H)]
        constructor <;> constructor <;> norm_num at * <;> linarith
      rw [principal_rectangle _ _ _ hre him hp]
      convert half_endpoint_residue_bound q hN t using 1 <;> ring
    · have hne : |t| ≠ H := by
        intro he
        rcases (abs_eq (by linarith : 0 ≤ H)).mp he with he | he
        · have hh := (height_spec (t := t) hT).2.2.2.1
          change 1 / 4 ≤ |t - H| at hh
          rw [he, sub_self, abs_zero] at hh
          norm_num at hh
        · have hh := (height_spec (t := t) hT).2.2.2.2
          change 1 / 4 ≤ |t + H| at hh
          rw [he, neg_add_cancel, abs_zero] at hh
          norm_num at hh
      have hp : 1 - Thm4.half t ∉
          Rectangle (-((H : ℂ) * I)) ((c : ℂ) + H * I) := by
        intro hp
        have hh := hp.2
        change (1 - Thm4.half t).im ∈
          Set.uIcc (-((H : ℂ) * I)).im ((c : ℂ) + H * I).im at hh
        simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
          add_zero, Complex.add_im, zero_add, Complex.sub_im, Complex.one_im] at hh
        have hh' : -t ∈ Set.uIcc (-H) H := by simpa [Thm4.half] using hh
        rw [Set.uIcc_of_le (by linarith : -H ≤ H)] at hh'
        have habs : |t| ≤ H := abs_le.mpr ⟨by linarith [hh'.2], by linarith [hh'.1]⟩
        exact hne (le_antisymm habs (le_of_not_gt ht))
      rw [principal_rectangle_outside _ _ _ hp, norm_zero]
      positivity
  · have hd := nonprincipal_integrand_entire ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) t χ hχ
    have hh : RectangleIntegral
        (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
        (-((H : ℂ) * I)) ((c : ℂ) + H * I) = 0 :=
      HolomorphicOn.vanishesOnRectangle hd.differentiableOn subset_rfl
    simp only [hχ, ite_false, mul_zero]
    change ‖RectangleIntegral' _ (-((H : ℂ) * I)) ((c : ℂ) + H * I)‖ ≤ 0
    rw [RectangleIntegral', hh, smul_zero, norm_zero]

/-- Page 22, display 3.36. Assembly from the three smaller Perron pieces.
The rectangle contribution uses the proved principal residue identity.
CONDITIONAL on safe_height_horizontal_bound. -/
theorem regularized_perron_assembly (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
        ‖partialSum N χ t‖ ≤ ‖lineIntegral N T χ t‖ +
          C * Real.log x * (Real.sqrt q / Real.sqrt T) +
          C * Real.log x * (Real.sqrt N / T) +
          C * (if χ = 1 then Real.sqrt N / (1 + |t|) else 0) := by
  obtain ⟨A, hA, hrem⟩ := summed_perron_remainders
  obtain ⟨B, hB, hhor⟩ := safe_height_horizontal_bound h8
  refine ⟨A + B + 12, by positivity, ?_⟩
  intro x N T q _ χ t hx hN hNx hT hTx hq hqx ht
  have hr := hrem x N T q χ t hx hN hNx hT hTx
  rw [← rightIntegral_eq_perronSeries χ hx N T t] at hr
  have hh := hhor x N T q χ t hx hN hNx hT hTx hq hqx ht
  have hh' : ‖rightIntegral x N T χ t - lineIntegral N T χ t -
      RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
        (-((height T t : ℂ) * I))
        (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I)‖ ≤
      B * Real.log x * (Real.sqrt q / Real.sqrt T) +
      B * Real.log x * (Real.sqrt N / T) := by
    rw [horizontal_identity, norm_neg]
    exact hh
  have hres := safe_rectangle_bound χ hx hN hT t
  let P := partialSum N χ t
  let Q := rightIntegral x N T χ t
  let J := lineIntegral N T χ t
  let R := RectangleIntegral' (integrand ((⌊N⌋₊ : ℝ) + 1 / 2) (1 / 2) χ t)
    (-((height T t : ℂ) * I))
    (((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + height T t * I)
  have hPQ := norm_sub_le_norm_sub_add_norm_sub P Q J
  have hQR := norm_sub_le_norm_sub_add_norm_sub (Q - J) R 0
  have hPJ := norm_sub_le_norm_sub_add_norm_sub P J 0
  simp only [sub_zero] at hQR hPJ
  have hl : 0 ≤ Real.log x := (Real.log_pos (by linarith : 1 < x)).le
  have hz : 0 ≤ (if χ = 1 then Real.sqrt N / (1 + |t|) else 0 : ℝ) := by
    split_ifs <;> positivity
  have hq0 : 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) := by positivity
  have hN0 : 0 ≤ Real.log x * (Real.sqrt N / T) := by positivity
  change ‖P - Q‖ ≤ _ at hr
  change ‖Q - J - R‖ ≤ _ at hh'
  change ‖R‖ ≤ _ at hres
  change ‖P‖ ≤ ‖J‖ + _ + _ + _
  have hm1 := mul_nonneg hA.le hq0
  have hm2 := mul_nonneg hA.le hz
  have hm3 := mul_nonneg hB.le hz
  nlinarith

end LeanLab.BHP1997.DecompC165a.Contour230
