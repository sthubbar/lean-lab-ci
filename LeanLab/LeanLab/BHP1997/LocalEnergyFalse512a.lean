/-
P0069 Baker Harman Pintz 1997, Section 2, pages 9 and 10, display 2.11.
This file serves the refutation of the lab leaf `leaf_minor_local_energy512`,
the uniform local minor arc energy bound for S2 stated with the hypotheses of
Theorem 2 of page 3 only. Theorem 2 puts no coprimality condition on b, while the
proof of 2.11 on pages 9 and 10 expands S2 in Dirichlet characters. The sequence
b(m) = e(m (1/4 + δ/2)) on even m, zero on odd m, with δ = Y^(-1/2), has S2 of
size at least Y/4 on a window of radius 1/(16 Y) around 3/4 - δ/2, and that
window lies in the minor arcs. This file proves the lower bound for the local
minor arc energy at that point. The hypotheses of Theorem 2 for this sequence
are handled in a separate file.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a

namespace LeanLab.BHP1997.Section2MS
open Classical Complex Thm2 MeasureTheory Set
open scoped ComplexConjugate

/-- P0069 page 5, the support (Y, 2Y] of S2: the even integers in a half open
interval are at least as many as the doubled integers it contains. -/
private theorem even_count512 (a c : ℕ) :
    c / 2 - a / 2 ≤ ((Finset.Ioc a c).filter (fun m : ℕ => Even m)).card := by
  have himg : (Finset.Ioc (a / 2) (c / 2)).image (fun k : ℕ => 2 * k) ⊆
      (Finset.Ioc a c).filter (fun m : ℕ => Even m) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    rw [Finset.mem_Ioc] at hk
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, even_two_mul k⟩
  have hcard : ((Finset.Ioc (a / 2) (c / 2)).image (fun k : ℕ => 2 * k)).card =
      c / 2 - a / 2 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by omega),
      Nat.card_Ioc]
  calc c / 2 - a / 2 = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card himg

/-- P0069 page 5, the support (Y, 2Y] of S2 holds more than Y/2 - 1 even integers. -/
private theorem even_count_real512 {Y : ℝ} (hY : 0 ≤ Y) :
    Y / 2 - 1 ≤ (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun m : ℕ => Even m)).card : ℝ) := by
  have h := even_count512 ⌊Y⌋₊ ⌊2 * Y⌋₊
  have h2 : ⌊2 * Y⌋₊ ≤
      2 * ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun m : ℕ => Even m)).card + ⌊Y⌋₊ + 1 := by
    omega
  have h3 : ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤
      2 * (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun m : ℕ => Even m)).card : ℝ) +
        ((⌊Y⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast h2
  have h4 : 2 * Y < ((⌊2 * Y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have h5 : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY
  linarith

/-- P0069 page 5, one term of S2 for the counterexample sequence: with
β = 1/4 + δ/2 and ζ = 3/4 - δ/2 one has β + ζ = 1, so e(m β) e(m t) = e(m (t - ζ)),
whose real part is cos(2π m (t - ζ)). -/
private theorem counter_term512 (δ t : ℝ) (m : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ)) *
      @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))).re =
      Real.cos (2 * Real.pi * m * (t - (3 / 4 - δ / 2))) := by
  rw [fourier_coe_apply, ← Complex.exp_add]
  have harg : 2 * Real.pi * Complex.I * (((m : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ) +
      2 * Real.pi * Complex.I * ((m : ℤ) : ℂ) * (t : ℂ) / ((1 : ℝ) : ℂ) =
      (m : ℂ) * (2 * Real.pi * Complex.I) +
        ((2 * Real.pi * m * (t - (3 / 4 - δ / 2)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul,
    Complex.exp_ofReal_mul_I_re]

/-- P0069 pages 9 and 10, display 2.11, the integrand: for the counterexample
sequence, S2 has norm at least Y/4 at every t within 1/(16 Y) of ζ = 3/4 - δ/2. -/
private theorem counter_poly_lower512 {Y δ t : ℝ} (hY : 40 ≤ Y) (b : ℕ → ℂ)
    (hb : ∀ m : ℕ, b m = if Even m then
      Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * (1 / 4 + δ / 2) : ℝ) : ℂ)) else 0)
    (ht : |t - (3 / 4 - δ / 2)| ≤ 1 / (16 * Y)) :
    Y / 4 ≤ ‖polynomial512 (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) b t‖ := by
  have hYpos : 0 < Y := by linarith
  have hsqrt : (7 / 5 : ℝ) ≤ √2 := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  have hcos : (7 / 10 : ℝ) ≤ Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]; linarith
  have hterm : ∀ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊,
      (if Even m then (7 / 10 : ℝ) else 0) ≤
        (b m * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))).re := by
    intro m hm
    rw [hb m]
    by_cases hev : Even m
    · simp only [hev, ↓reduceIte]
      rw [counter_term512]
      have hmle : (m : ℝ) ≤ 2 * Y :=
        (Nat.le_floor_iff (by linarith)).mp (Finset.mem_Ioc.mp hm).2
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have h2pi : (0 : ℝ) ≤ 2 * Real.pi := mul_nonneg zero_le_two Real.pi_pos.le
      have habs : |2 * Real.pi * m * (t - (3 / 4 - δ / 2))| ≤ Real.pi / 4 := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg h2pi hm0)]
        calc 2 * Real.pi * m * |t - (3 / 4 - δ / 2)|
            ≤ 2 * Real.pi * (2 * Y) * (1 / (16 * Y)) := by
              refine mul_le_mul ?_ ht (abs_nonneg _) (mul_nonneg h2pi (by linarith))
              exact mul_le_mul_of_nonneg_left hmle h2pi
          _ = Real.pi / 4 := by
              rw [mul_one_div, div_eq_div_iff (mul_pos (by norm_num) hYpos).ne'
                (by norm_num)]
              ring
      rw [← Real.cos_abs]
      exact hcos.trans (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) habs)
    · simp only [hev, ↓reduceIte, zero_mul, Complex.zero_re, le_refl]
  have hre : (7 / 10 : ℝ) *
      (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun m : ℕ => Even m)).card : ℝ) ≤
      (polynomial512 (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) b t).re := by
    unfold polynomial512
    rw [Complex.re_sum]
    calc (7 / 10 : ℝ) *
          (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter (fun m : ℕ => Even m)).card : ℝ)
        = ∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, (if Even m then (7 / 10 : ℝ) else 0) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hcount := even_count_real512 (Y := Y) hYpos.le
  have hn := Complex.re_le_norm (polynomial512 (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) b t)
  linarith

/-- P0069 pages 9 and 10, display 2.11: the local minor arc energy at ζ is at least
the integral over any closed window around ζ that lies in the minor arc
neighbourhood, and on that window the integrand is at least c squared. -/
private theorem counter_integral_lower512 (ε D x ζ ρ c : ℝ) (b : ℕ → ℂ)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (hsub : Icc (ζ - ρ) (ζ + ρ) ⊆
      Ioo (ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
        (ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩ minor512 ε D x)
    (hlow : ∀ t ∈ Icc (ζ - ρ) (ζ + ρ),
      c ≤ ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖) :
    2 * ρ * c ^ 2 ≤ localMinorEnergy512 ε D x b ζ := by
  unfold localMinorEnergy512
  have hcont : Continuous (fun t =>
      ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2) :=
    (continuous_polynomial512 _ _).norm.pow 2
  have hintS : IntegrableOn (fun t =>
      ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2)
      (Ioo (ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
        (ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩ minor512 ε D x) :=
    (hcont.integrableOn_Icc
      (a := ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
      (b := ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))).mono_set
      (inter_subset_left.trans Ioo_subset_Icc_self)
  have hintW : IntegrableOn (fun t =>
      ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2)
      (Icc (ζ - ρ) (ζ + ρ)) := hcont.integrableOn_Icc
  have h1 : ∫ t in Icc (ζ - ρ) (ζ + ρ),
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 ≤
      ∫ t in Ioo (ζ - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
        (ζ + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩ minor512 ε D x,
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 :=
    setIntegral_mono_set hintS (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (Filter.Eventually.of_forall hsub)
  have h2 : ∫ _ in Icc (ζ - ρ) (ζ + ρ), c ^ 2 ≤
      ∫ t in Icc (ζ - ρ) (ζ + ρ),
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) b t‖ ^ 2 :=
    setIntegral_mono_on continuous_const.integrableOn_Icc hintW measurableSet_Icc
      (fun t ht => pow_le_pow_left₀ hc (hlow t ht) 2)
  have h3 : ∫ _ in Icc (ζ - ρ) (ζ + ρ), c ^ 2 = 2 * ρ * c ^ 2 := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    ring
  linarith

/-- P0069 page 5, the arcs, and pages 9 and 10, display 2.11: with Y = R^4,
δ = R^(-2) and R at least 10, the closed window of radius 1/(16 Y) around
ζ = 3/4 - δ/2 lies within 1/H of ζ, inside the complete period, and misses every
major arc. The arc at 3/4 has radius at most log^(4D) x / Y, below δ/2 - 1/(16 Y),
and any other r/q with q ≤ log^(2D) x is at distance at least 1/(4q) from 3/4. -/
private theorem counter_window512 (ε D x R δ : ℝ) (hR : 10 ≤ R)
    (hY : length512 ε x = R ^ 4) (hδ : δ * R ^ 2 = 1)
    (hH : x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ≤ length512 ε x)
    (hHpos : 0 < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
    (hQ : 2 ≤ order512 ε x)
    (hL4 : Real.log x ^ (4 * D) ≤ R) (hL4nn : 0 ≤ Real.log x ^ (4 * D))
    (hL2 : Real.log x ^ (2 * D) ≤ R) :
    Icc (3 / 4 - δ / 2 - 1 / (16 * length512 ε x))
        (3 / 4 - δ / 2 + 1 / (16 * length512 ε x)) ⊆
      Ioo (3 / 4 - δ / 2 - 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))))
        (3 / 4 - δ / 2 + 1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) ∩
        minor512 ε D x := by
  intro t ht
  rw [mem_Icc] at ht
  obtain ⟨ht1, ht2⟩ := ht
  have hRpos : 0 < R := by linarith
  have hYpos : 0 < length512 ε x := by rw [hY]; positivity
  obtain ⟨u, hudef, hu⟩ : ∃ u : ℝ, u = R⁻¹ ∧ u * R = 1 :=
    ⟨R⁻¹, rfl, inv_mul_cancel₀ hRpos.ne'⟩
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu10 : u ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_left hR hu0.le
    linarith
  have hu2 : u ^ 2 ≤ 1 / 100 := by
    have := pow_le_pow_left₀ hu0.le hu10 2
    norm_num at this
    linarith
  have hu3 : u ^ 3 ≤ 1 / 1000 := by
    have := pow_le_pow_left₀ hu0.le hu10 3
    norm_num at this
    linarith
  have hu3pos : 0 < u ^ 3 := pow_pos hu0 3
  have hu4pos : 0 < u ^ 4 := pow_pos hu0 4
  have hu4 : u ^ 4 ≤ 1 / 10000 := by
    have := pow_le_pow_left₀ hu0.le hu10 4
    norm_num at this
    linarith
  have hδu : δ = u ^ 2 := by
    linear_combination (-δ * (u * R + 1)) * hu + u ^ 2 * hδ
  have hYu : length512 ε x * u ^ 4 = 1 := by
    rw [hY]
    calc R ^ 4 * u ^ 4 = (u * R) ^ 4 := by ring
      _ = 1 := by rw [hu]; norm_num
  have hρ : 1 / (16 * length512 ε x) = u ^ 4 / 16 := by
    rw [div_eq_iff (mul_pos (by norm_num) hYpos).ne']
    linear_combination (-1 : ℝ) * hYu
  have he : Real.log x ^ (4 * D) / length512 ε x = Real.log x ^ (4 * D) * u ^ 4 := by
    rw [div_eq_iff hYpos.ne']
    linear_combination (-Real.log x ^ (4 * D)) * hYu
  have he0 : 0 ≤ Real.log x ^ (4 * D) / length512 ε x := div_nonneg hL4nn hYpos.le
  have he3 : Real.log x ^ (4 * D) / length512 ε x ≤ u ^ 3 := by
    rw [he]
    have h1 := mul_le_mul_of_nonneg_right hL4 hu4pos.le
    have h2 : R * u ^ 4 = u ^ 3 := by linear_combination u ^ 3 * hu
    linarith
  have hF3 : u ^ 3 < u ^ 2 / 2 - u ^ 4 / 16 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu10), mul_pos hu0 hu0,
      mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]
  rw [hδu, hρ] at ht1 ht2
  rw [hδu]
  refine ⟨?_, ?_⟩
  · have hlt : 1 / (16 * length512 ε x) <
        1 / x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
      one_div_lt_one_div_of_lt hHpos (by linarith)
    rw [hρ] at hlt
    exact ⟨by linarith, by linarith⟩
  · rw [minor512, mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [period512, mem_Ioc]
      have hQr : (2 : ℝ) ≤ (order512 ε x : ℝ) := by exact_mod_cast hQ
      have hQ1 : 1 / (order512 ε x : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hQr
      have hQ0 : 0 ≤ 1 / (order512 ε x : ℝ) := by positivity
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨_, hmem⟩
      simp only [mem_iUnion, exists_prop] at hmem
      obtain ⟨q, hq, r, hr, htq⟩ := hmem
      rw [Finset.mem_Icc] at hq
      rw [mem_Icc] at htq
      obtain ⟨hq1, hqle⟩ := hq
      have hq0 : q ≠ 0 := by omega
      have hqfl : q ≤ ⌊Real.log x ^ (2 * D)⌋₊ := hqle.trans (min_le_right _ _)
      have hqL : (q : ℝ) ≤ Real.log x ^ (2 * D) := (Nat.le_floor_iff' hq0).mp hqfl
      have hqR : (q : ℝ) ≤ R := hqL.trans hL2
      have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      have hqpos : (0 : ℝ) < q := by linarith
      have e1 : Real.log x ^ (4 * D) / (q * length512 ε x) * q =
          Real.log x ^ (4 * D) / length512 ε x := by
        rw [mul_comm (q : ℝ) (length512 ε x), ← div_div, div_mul_cancel₀ _ hqpos.ne']
      have hlo : (r : ℝ) - Real.log x ^ (4 * D) / length512 ε x ≤ t * q := by
        have h := mul_le_mul_of_nonneg_right htq.1 hqpos.le
        rw [sub_mul, div_mul_cancel₀ _ hqpos.ne', e1] at h
        exact h
      have hhi : t * q ≤ (r : ℝ) + Real.log x ^ (4 * D) / length512 ε x := by
        have h := mul_le_mul_of_nonneg_right htq.2 hqpos.le
        rw [add_mul, div_mul_cancel₀ _ hqpos.ne', e1] at h
        exact h
      have hup : t * q ≤ 3 / 4 * q - q * (u ^ 2 / 2 - u ^ 4 / 16) := by
        have h := mul_le_mul_of_nonneg_right ht2 hqpos.le
        nlinarith [h]
      have hdn : 3 / 4 * q - q * (u ^ 2 / 2 + u ^ 4 / 16) ≤ t * q := by
        have h := mul_le_mul_of_nonneg_right ht1 hqpos.le
        nlinarith [h]
      have hB : u ^ 3 < q * (u ^ 2 / 2 - u ^ 4 / 16) := by
        have h := mul_le_mul_of_nonneg_right hq1r
          (show 0 ≤ u ^ 2 / 2 - u ^ 4 / 16 by linarith)
        linarith
      have hA : q * (u ^ 2 / 2 + u ^ 4 / 16) ≤ 1 / 8 := by
        have hA0 : 0 ≤ u ^ 2 / 2 + u ^ 4 / 16 := by positivity
        have h := mul_le_mul_of_nonneg_right hqR hA0
        have h' : R * (u ^ 2 / 2 + u ^ 4 / 16) = u / 2 + u ^ 3 / 16 := by
          linear_combination (u / 2 + u ^ 3 / 16) * hu
        linarith
      rcases lt_trichotomy (3 * q) (4 * r) with h | h | h
      · have hc : 3 * (q : ℝ) + 1 ≤ 4 * (r : ℝ) := by exact_mod_cast h
        linarith
      · have hc : 3 * (q : ℝ) = 4 * (r : ℝ) := by exact_mod_cast h
        linarith
      · have hc : 4 * (r : ℝ) + 1 ≤ 3 * (q : ℝ) := by exact_mod_cast h
        linarith

/-- P0069 pages 9 and 10, display 2.11: every largeness fact about x used by the
counterexample. Powers of log x are eventually below Y^(1/4), the Farey order Q
is eventually at least 2, and log x eventually exceeds any constant. -/
private theorem counter_eventually512 (ε : ℝ) (hε : 0 < ε) (D C : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ x ∧ 10 ≤ (length512 ε x) ^ (1 / 4 : ℝ) ∧
      2 ≤ order512 ε x ∧
      Real.log x ^ (4 * D) ≤ (length512 ε x) ^ (1 / 4 : ℝ) ∧
      Real.log x ^ (2 * D) ≤ (length512 ε x) ^ (1 / 4 : ℝ) ∧
      128 * max C 1 < Real.log x := by
  have hθ : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hY : Filter.Tendsto (fun x : ℝ => length512 ε x) Filter.atTop Filter.atTop := by
    unfold length512
    exact tendsto_rpow_atTop hθ
  have hR : Filter.Tendsto (fun x : ℝ => (length512 ε x) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hY
  have hQ : Filter.Tendsto (fun x : ℝ =>
      (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num)
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5))).comp hY))
  have hlog : ∀ k : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ k ≤ (length512 ε x) ^ (1 / 4 : ℝ) := by
    intro k
    have ho := (isLittleO_log_rpow_rpow_atTop k
      (mul_pos hθ (by norm_num : (0 : ℝ) < 1 / 4))).bound one_pos
    filter_upwards [ho, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    unfold length512
    rw [← Real.rpow_mul hx0]
    exact (le_abs_self _).trans hx
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hR.eventually_ge_atTop 10,
    hQ.eventually_ge_atTop 2, hlog (4 * D), hlog (2 * D),
    Real.tendsto_log_atTop.eventually_gt_atTop (128 * max C 1)] with x h1 h2 h3 h4 h5 h6
  refine ⟨h1, h2, ?_, h4, h5, h6⟩
  unfold order512
  exact Nat.le_floor (by rw [Nat.cast_ofNat]; exact h3)

/-- P0069 pages 9 and 10, display 2.11, fails for a sequence allowed by Theorem 2
of page 3. For b(m) = e(m (1/4 + δ/2)) on even m and zero on odd m, δ = Y^(-1/2),
the local minor arc energy of S2 at ζ = 3/4 - δ/2 is at least Y/128, which
exceeds C Y / log x for every constant C once x is large. So the bound 2.11 with
saving exponent 1 does not hold for this sequence. The paper proves 2.11 by an
expansion in Dirichlet characters, which does not see the even integers. -/
theorem counter_energy_lower512 (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (b : ℝ → ℕ → ℂ)
    (hb : ∀ (x : ℝ) (m : ℕ), b x m = if Even m then
      Complex.exp (2 * Real.pi * Complex.I *
        (((m : ℝ) * (1 / 4 + (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2) : ℝ) : ℂ)) else 0)
    (D C : ℝ) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      C * length512 ε x * Real.log x ^ (-(1 : ℝ)) <
        localMinorEnergy512 ε D x (b x) (3 / 4 - (x ^ (11 / 20 + ε)) ^ (-(1 / 2 : ℝ)) / 2) := by
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (counter_eventually512 ε hε D C)
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨hx1, hR10, hQ, hL4, hL2, hlog⟩ := hx₀ x hx
  have hθ : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hYdef : x ^ (11 / 20 + ε) = length512 ε x := rfl
  have hbx := hb x
  rw [hYdef] at hbx ⊢
  have hYpos : 0 < length512 ε x := by rw [← hYdef]; exact Real.rpow_pos_of_pos hx0 _
  have hYR : length512 ε x = ((length512 ε x) ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hYpos.le]
    have h : (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 := by norm_num
    rw [h, Real.rpow_one]
  have hδR : (length512 ε x) ^ (-(1 / 2 : ℝ)) * ((length512 ε x) ^ (1 / 4 : ℝ)) ^ 2 = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hYpos.le, ← Real.rpow_add hYpos]
    have h : -(1 / 2 : ℝ) + (1 / 4 : ℝ) * ((2 : ℕ) : ℝ) = 0 := by norm_num
    rw [h, Real.rpow_zero]
  have hY40 : 40 ≤ length512 ε x := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) hR10 4
    norm_num at h
    linarith
  have hc : (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) ≤ 1 := by norm_num
  have hH : x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ≤ length512 ε x := by
    rw [← hYdef]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (mul_le_of_le_one_right hθ.le hc)
  have hsub := counter_window512 ε D x ((length512 ε x) ^ (1 / 4 : ℝ))
    ((length512 ε x) ^ (-(1 / 2 : ℝ))) hR10 hYR hδR hH (Real.rpow_pos_of_pos hx0 _) hQ hL4
    (Real.rpow_nonneg (Real.log_nonneg hx1) _) hL2
  have hlow : ∀ t ∈ Icc (3 / 4 - (length512 ε x) ^ (-(1 / 2 : ℝ)) / 2 - 1 / (16 * length512 ε x))
      (3 / 4 - (length512 ε x) ^ (-(1 / 2 : ℝ)) / 2 + 1 / (16 * length512 ε x)),
      length512 ε x / 4 ≤
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (b x) t‖ :=
    fun t ht => counter_poly_lower512 hY40 (b x) hbx
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hE := counter_integral_lower512 ε D x (3 / 4 - (length512 ε x) ^ (-(1 / 2 : ℝ)) / 2)
    (1 / (16 * length512 ε x)) (length512 ε x / 4) (b x)
    (one_div_nonneg.mpr (mul_nonneg (by norm_num) hYpos.le))
    (div_nonneg hYpos.le (by norm_num)) hsub hlow
  have hρY : 1 / (16 * length512 ε x) * (16 * length512 ε x) = 1 :=
    div_mul_cancel₀ _ (mul_pos (by norm_num) hYpos).ne'
  have hval : 2 * (1 / (16 * length512 ε x)) * (length512 ε x / 4) ^ 2 =
      length512 ε x / 128 := by
    linear_combination (length512 ε x / 128) * hρY
  have hmax : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hCmax : C ≤ max C 1 := le_max_left _ _
  have hl : 0 < Real.log x := by linarith
  have h1 : C * length512 ε x * Real.log x ^ (-(1 : ℝ)) =
      length512 ε x * (C / Real.log x) := by
    rw [Real.rpow_neg_one, div_eq_mul_inv]
    ring
  have h2 : C / Real.log x < 1 / 128 := by
    rw [div_lt_iff₀ hl]
    linarith
  have h3 := mul_lt_mul_of_pos_left h2 hYpos
  linarith

end LeanLab.BHP1997.Section2MS
