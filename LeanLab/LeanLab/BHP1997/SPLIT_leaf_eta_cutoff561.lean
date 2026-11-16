/-
Split of theorem leaf_eta_cutoff561 in LeanLab.BHP1997.Decomp561m: the eta
cutoff error of display 2.6 on page 8, the mean square over the even
frequencies of the difference between the truncated eta integral and the
complete period integral.
The cut separates the unit coefficient case with the explicit frequency count
from the two elementary interface estimates (count of even frequencies, sign of
the scale). The u times v scaling is bookkeeping and is proved here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.PrincipalData635

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- Both principal models carry one common factor u times v in front of the
modulus sum, and nothing else in them depends on u and v. -/
private theorem principalArc_units561 (ε D x u v : ℝ) (N : ℕ) :
    principalArc512 ε D x u v N = ((u * v : ℝ) : ℂ) * principalArc512 ε D x 1 1 N := by
  unfold principalArc512
  push_cast
  ring

/-- The complete period model of the same display has the same factor. -/
private theorem completePrincipal_units561 (ε D x u v : ℝ) (N : ℕ) :
    completePrincipal561 ε D x u v N =
      ((u * v : ℝ) : ℂ) * completePrincipal561 ε D x 1 1 N := by
  unfold completePrincipal561
  push_cast
  ring

/-- The eta cutoff difference at any coefficient pair is the unit coefficient
difference multiplied by the common factor. -/
private theorem etaDiff_units561 (ε D x u v : ℝ) (N : ℕ) :
    principalArc512 ε D x u v N - completePrincipal561 ε D x u v N =
      ((u * v : ℝ) : ℂ) *
        (principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N) := by
  rw [principalArc_units561 (u := u) (v := v), completePrincipal_units561 (u := u) (v := v),
    principalArc_units561 (u := 1) (v := 1), completePrincipal_units561 (u := 1) (v := 1)]
  simp only [mul_one, Complex.ofReal_one, one_mul]
  ring

/-- The eta cutoff error is quadratic in the two coefficients. -/
private theorem etaTailError_units561 (ε D x u v : ℝ) :
    etaTailError561 ε D x u v = u ^ 2 * v ^ 2 * etaTailError561 ε D x 1 1 := by
  unfold etaTailError561
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [etaDiff_units561, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/- A: geometric sum bound -/
private lemma norm_sum_range_geom (z : ℂ) (hz1 : ‖z‖ = 1) (hz : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ 2 / ‖1 - z‖ := by
  have h1 : (0:ℝ) < ‖1 - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  have hmul : (∑ k ∈ Finset.range n, z ^ k) * (z - 1) = z ^ n - 1 := geom_sum_mul z n
  have hnorm : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ = ‖z ^ n - 1‖ := by
    rw [← norm_mul, hmul]
  have hle : ‖z ^ n - 1‖ ≤ 2 := by
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz1, one_pow]; norm_num
  rw [le_div_iff₀ h1, norm_sub_rev z 1] at *
  linarith

/- B: norm of 1 - exp(2 pi i t) -/
private lemma norm_one_sub_exp_two_pi_I (t : ℝ) :
    ‖(1:ℂ) - Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)‖
      = 2 * |Real.sin (Real.pi * t)| := by
  have hre : (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)).re = Real.cos (2 * Real.pi * t) :=
    Complex.exp_ofReal_mul_I_re _
  have him : (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)).im = Real.sin (2 * Real.pi * t) :=
    Complex.exp_ofReal_mul_I_im _
  have harg : (2:ℝ) * (Real.pi * t) = 2 * Real.pi * t := by ring
  have hsq : ‖(1:ℂ) - Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)‖ ^ 2
      = (2 * |Real.sin (Real.pi * t)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
    have hcos : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
      rw [← harg, Real.cos_two_mul, Real.sin_sq, Real.cos_sq']; ring
    have hsin : Real.sin (2 * Real.pi * t) = 2 * Real.sin (Real.pi * t) * Real.cos (Real.pi * t) := by
      rw [← harg, Real.sin_two_mul]
    rw [hcos, hsin]
    nlinarith [Real.sin_sq (Real.pi * t), Real.cos_sq' (Real.pi * t), sq_abs (Real.sin (Real.pi * t))]
  have h2 := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h2

/- C: |sin x| >= (2/pi)|x| on |x| <= pi/2 -/
private lemma abs_sin_ge (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    2 / Real.pi * |x| ≤ |Real.sin x| := by
  have hpi := Real.pi_pos
  rcases le_or_gt 0 x with h | h
  · have hx' : x ≤ Real.pi / 2 := by simpa [abs_of_nonneg h] using hx
    have hs : 0 ≤ Real.sin x :=
      Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hx'])
    rw [abs_of_nonneg h, abs_of_nonneg hs]
    exact Real.mul_le_sin h hx'
  · have hx' : -x ≤ Real.pi / 2 := by
      have h1 : |x| = -x := abs_of_neg h
      linarith [hx, h1]
    have hs : Real.sin x ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le h.le (by linarith [hx'])
    rw [abs_of_neg h, abs_of_nonpos hs]
    have := Real.mul_le_sin (x := -x) (by linarith) hx'
    rw [Real.sin_neg] at this
    linarith

/- parity helper -/
private lemma odd_of_mul_odd {p m : ℕ} (h : Odd (p * m)) : Odd m := by
  rw [Nat.odd_iff] at h ⊢
  by_contra hc
  have h0 : m % 2 = 0 := by omega
  rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at h
  omega

/- C': p <= (p-1)^2 for p >= 3 -/
private lemma prime_le_pred_sq {p : ℕ} (hp : 3 ≤ p) : p ≤ (p - 1) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
  have h : t + 3 - 1 = t + 2 := by omega
  rw [h, pow_two]
  nlinarith

/- D: n <= 4 * totient n ^ 2, over the reals -/
private lemma totient_key (n : ℕ) :
    (n:ℝ) ≤ 4 * (n.totient:ℝ) ^ 2 ∧ (Odd n → (n:ℝ) ≤ 2 * (n.totient:ℝ) ^ 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · rcases Nat.eq_or_lt_of_le hpos with h1 | h2
      · subst h1; norm_num
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
        obtain ⟨m, rfl⟩ := hpdvd
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
        have hp0 : (0:ℝ) ≤ (p:ℝ) := by linarith
        have hm : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at h2
          · exact h
        have hlt : m < p * m := by
          have h2p := hp.two_le
          have hm1 : 0 < m := hm
          nlinarith
        obtain ⟨ihm, ihm2⟩ := ih m hlt
        have hpp : (p:ℝ) ≤ (p:ℝ)^2 := by nlinarith
        have h1p : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
          rw [Nat.cast_sub hp.one_le]; norm_num
        constructor
        · by_cases hpm : p ∣ m
          · rw [Nat.totient_mul_of_prime_of_dvd hp hpm]; push_cast
            calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (4 * (m.totient:ℝ)^2) :=
                  mul_le_mul_of_nonneg_left ihm hp0
              _ = 4 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
              _ ≤ 4 * (p:ℝ)^2 * (m.totient:ℝ)^2 := by
                  nlinarith [hpp, sq_nonneg (m.totient:ℝ)]
              _ = 4 * ((p:ℝ) * (m.totient:ℝ))^2 := by ring
          · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm]
            push_cast [h1p]
            rcases eq_or_lt_of_le hp.two_le with hp_eq | hp_gt
            · subst hp_eq
              norm_num
              have hmo : Odd m := by
                rw [← Nat.not_even_iff_odd, even_iff_two_dvd]; exact hpm
              have hs2 := ihm2 hmo
              calc (2:ℝ) * (m:ℝ) ≤ 2 * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 (by norm_num)
                _ = 4 * (m.totient:ℝ)^2 := by ring
            · have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp_gt
              have hsq : (p:ℝ) ≤ ((p:ℝ) - 1)^2 := by nlinarith
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (4 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left ihm hp0
                _ = 4 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ ((p:ℝ) - 1)^2 * (4 * (m.totient:ℝ)^2) := by
                    nlinarith [hsq, sq_nonneg (m.totient:ℝ)]
                _ = 4 * (((p:ℝ) - 1) * (m.totient:ℝ))^2 := by ring
        · intro hodd
          have hmo : Odd m := odd_of_mul_odd hodd
          have hs2 := ihm2 hmo
          by_cases hp_eq : p = 2
          · subst hp_eq
            exact absurd hodd (by
              rw [Nat.odd_iff, Nat.mul_mod]; simp)
          · have hp3 : (3:ℝ) ≤ (p:ℝ) := by
              have : 3 ≤ p := by have := hp.two_le; omega
              exact_mod_cast this
            by_cases hpm : p ∣ m
            · rw [Nat.totient_mul_of_prime_of_dvd hp hpm]; push_cast
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 hp0
                _ = 2 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ 2 * (p:ℝ)^2 * (m.totient:ℝ)^2 := by
                    nlinarith [hpp, sq_nonneg (m.totient:ℝ)]
                _ = 2 * ((p:ℝ) * (m.totient:ℝ))^2 := by ring
            · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm]
              push_cast [h1p]
              have hsq : (p:ℝ) ≤ ((p:ℝ) - 1)^2 := by nlinarith
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 hp0
                _ = 2 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ ((p:ℝ) - 1)^2 * (2 * (m.totient:ℝ)^2) := by
                    nlinarith [hsq, sq_nonneg (m.totient:ℝ)]
                _ = 2 * (((p:ℝ) - 1) * (m.totient:ℝ))^2 := by ring

private lemma totient_sq_ge (n : ℕ) : (n:ℝ) ≤ 4 * (n.totient:ℝ) ^ 2 := (totient_key n).1


/- E: geometric bound over Ioc -/
private lemma sum_Ioc_pow_le (z : ℂ) (hz1 : ‖z‖ = 1) (hz : z ≠ 1) (m n : ℕ) :
    ‖∑ k ∈ Finset.Ioc m n, z ^ k‖ ≤ 4 / ‖1 - z‖ := by
  rcases le_or_gt n m with h | h
  · have hz0 : Finset.Ioc m n = ∅ := by
      ext k
      constructor
      · intro hk; rw [Finset.mem_Ioc] at hk; omega
      · intro hk; simp at hk
    rw [hz0]
    simp only [Finset.sum_empty, norm_zero]
    positivity
  · have hsub : Finset.range (m+1) ⊆ Finset.range (n+1) := by
      intro k hk; rw [Finset.mem_range] at hk ⊢; omega
    have hsd : Finset.Ioc m n = Finset.range (n+1) \ Finset.range (m+1) := by
      ext k
      rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_range, Finset.mem_range]
      omega
    have hsplit := Finset.sum_sdiff hsub (f := fun k => z ^ k)
    rw [← hsd] at hsplit
    have heq : ∑ k ∈ Finset.Ioc m n, z ^ k
        = (∑ k ∈ Finset.range (n+1), z ^ k) - ∑ k ∈ Finset.range (m+1), z ^ k := by
      rw [eq_sub_iff_add_eq]
      exact hsplit
    have hA : ‖∑ k ∈ Finset.range (n+1), z ^ k‖ ≤ 2 / ‖1 - z‖ :=
      norm_sum_range_geom z hz1 hz (n+1)
    have hB : ‖∑ k ∈ Finset.range (m+1), z ^ k‖ ≤ 2 / ‖1 - z‖ :=
      norm_sum_range_geom z hz1 hz (m+1)
    have hP : (0:ℝ) ≤ 2 / ‖1 - z‖ := by
      have : (0:ℝ) < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
      positivity
    rw [heq]
    calc ‖(∑ k ∈ Finset.range (n+1), z ^ k) - ∑ k ∈ Finset.range (m+1), z ^ k‖
        ≤ ‖∑ k ∈ Finset.range (n+1), z ^ k‖ + ‖∑ k ∈ Finset.range (m+1), z ^ k‖ := norm_sub_le _ _
      _ ≤ 2 / ‖1 - z‖ + 2 / ‖1 - z‖ := by linarith
      _ = 4 / ‖1 - z‖ := by ring

/- F: fourier powers -/
private lemma fourier_nat_pow (k : ℕ) (t : AddCircle (1:ℝ)) :
    @fourier 1 (k : ℤ) t = (@fourier 1 1 t) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, fourier_add, ih, pow_succ]

/- G: norm of 1 - fourier 1 t -/
private lemma norm_one_sub_fourier_ge {t : ℝ} (ht : |t| ≤ 1/2) :
    4 * |t| ≤ ‖(1:ℂ) - @fourier 1 1 (t : AddCircle (1:ℝ))‖ := by
  have harg : ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) := by
    push_cast; ring
  have hf : @fourier 1 1 (t : AddCircle (1:ℝ))
      = Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := by
    rw [fourier_coe_apply]
    simp only [Int.cast_one, mul_one]
    congr 1
    push_cast
    ring
  rw [hf, norm_one_sub_exp_two_pi_I]
  have hp := Real.pi_pos
  have h1 : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have h2 : |Real.pi * t| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos hp]; nlinarith
    have h3 := abs_sin_ge (Real.pi * t) h2
    rw [abs_mul, abs_of_pos hp] at h3
    have h4 : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
    linarith [h3, h4]
  linarith

/- H: integral of (t^2)^{-1} -/
private lemma integral_inv_sq_eq {u v : ℝ} (_hu : u ≠ 0) (_hv : v ≠ 0)
    (huv : ∀ t ∈ Set.uIcc u v, t ≠ 0) :
    ∫ t in u..v, (t ^ 2)⁻¹ = -(v⁻¹) + (u⁻¹) := by
  have hderiv : ∀ t ∈ Set.uIcc u v,
      HasDerivAt (fun s : ℝ => -(s⁻¹)) ((t ^ 2)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := huv t ht
    have h1 : HasDerivAt (fun s : ℝ => s⁻¹) (-((t^2)⁻¹)) t := hasDerivAt_inv ht0
    have hh := h1.neg
    have hfin : -(-((t^2)⁻¹)) = (t^2)⁻¹ := neg_neg _
    rw [hfin] at hh
    exact hh
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    have : t ≠ 0 := huv t ht
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/- I: fourier at 1 -/
private lemma fourier_one_eq (t : ℝ) :
    @fourier 1 1 (t : AddCircle (1:ℝ)) = Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := by
  rw [fourier_coe_apply]
  simp only [Int.cast_one, mul_one]
  congr 1
  push_cast
  ring

private lemma norm_fourier_one (t : ℝ) : ‖@fourier 1 1 (t : AddCircle (1:ℝ))‖ = 1 := by
  rw [fourier_one_eq, Complex.norm_exp_ofReal_mul_I]

/- J: polynomial bound -/
private lemma norm_polynomial_Ioc_le {m n : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ 1/2) :
    ‖polynomial512 (Finset.Ioc m n) (fun _ => 1) t‖ ≤ |t|⁻¹ := by
  unfold polynomial512
  have hsum : ∑ k ∈ Finset.Ioc m n, (1:ℂ) * @fourier 1 (k:ℤ) (t : AddCircle (1:ℝ))
      = ∑ k ∈ Finset.Ioc m n, (@fourier 1 1 (t : AddCircle (1:ℝ)))^k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [one_mul, fourier_nat_pow]
  rw [hsum]
  have hz1 : ‖(@fourier 1 1 (t : AddCircle (1:ℝ)))‖ = 1 := norm_fourier_one t
  have hge := norm_one_sub_fourier_ge ht
  have htpos : 0 < |t| := abs_pos.mpr ht0
  have hpos : 0 < ‖(1:ℂ) - @fourier 1 1 (t : AddCircle (1:ℝ))‖ := lt_of_lt_of_le (by linarith) hge
  have hz : (@fourier 1 1 (t : AddCircle (1:ℝ))) ≠ 1 := by
    intro hcon
    rw [hcon, sub_self, norm_zero] at hpos
    exact lt_irrefl 0 hpos
  have hb := sum_Ioc_pow_le _ hz1 hz m n
  have hstep : 4 / ‖(1:ℂ) - @fourier 1 1 (t : AddCircle (1:ℝ))‖ ≤ |t|⁻¹ := by
    rw [div_le_iff₀ hpos]
    have key : |t|⁻¹ * ‖(1:ℂ) - @fourier 1 1 (t : AddCircle (1:ℝ))‖
        = ‖(1:ℂ) - @fourier 1 1 (t : AddCircle (1:ℝ))‖ / |t| := by
      rw [inv_eq_one_div]; ring
    rw [key, le_div_iff₀ htpos]
    linarith [hge]
  linarith [hb, hstep]


/- K: integrand bound -/
private lemma norm_integrand_le {ε x : ℝ} {N : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ 1/2) :
    ‖integrand512 ε x (fun _ => 1) (fun _ => 1) N t‖ ≤ (t^2)⁻¹ := by
  unfold integrand512
  have h1 := norm_polynomial_Ioc_le (m := ⌊x - 2 * length512 ε x⌋₊) (n := ⌊x⌋₊) ht0 ht
  have h2 := norm_polynomial_Ioc_le (m := ⌊length512 ε x⌋₊) (n := ⌊2 * length512 ε x⌋₊) ht0 ht
  have h3 : ‖@fourier 1 (-(N:ℤ)) (t : AddCircle (1:ℝ))‖ = 1 := by
    rw [fourier_coe_apply, Complex.norm_exp]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]
  rw [norm_mul, norm_mul, h3, mul_one]
  have hpos : (0:ℝ) < (t^2)⁻¹ := by
    have : (0:ℝ) < t^2 := by positivity
    positivity
  have htinv : (0:ℝ) < |t|⁻¹ := by positivity
  calc ‖polynomial512 (Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊) (fun _ => 1) t‖ *
        ‖polynomial512 (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊) (fun _ => 1) t‖
      ≤ |t|⁻¹ * |t|⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) (le_of_lt htinv)
    _ = (t^2)⁻¹ := by
        rw [← mul_inv, ← sq_abs]; ring

/- L: tail integral bound -/
private lemma integral_tail_le {A : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hcont : Continuous A)
    (hA : ∀ t : ℝ, 0 < |t| → |t| ≤ 1/2 → ‖A t‖ ≤ (t^2)⁻¹) :
    ‖(∫ t in (-a)..a, A t) - (∫ t in (-(1/2))..(1/2), A t)‖ ≤ 2 / a := by
  have hI : ∀ u v : ℝ, IntervalIntegrable A volume u v := fun u v => hcont.intervalIntegrable u v
  have hI2 : ∀ u v : ℝ, IntervalIntegrable (fun t => ‖A t‖) volume u v :=
    fun u v => hcont.norm.intervalIntegrable u v
  have hpos1 : IntervalIntegrable (fun t : ℝ => (t^2)⁻¹) volume a (1/2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    have hle : a ≤ t := by
      rcases Set.mem_uIcc.mp ht with ⟨h1, -⟩ | ⟨h1, -⟩
      · linarith
      · linarith
    have ht0 : t ≠ 0 := by linarith
    exact pow_ne_zero 2 ht0
  have hpos2 : IntervalIntegrable (fun t : ℝ => (t^2)⁻¹) volume (-(1/2)) (-a) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    have hle : t ≤ -a := by
      rcases Set.mem_uIcc.mp ht with ⟨-, h2⟩ | ⟨-, h2⟩
      · linarith
      · linarith
    have ht0 : t ≠ 0 := by linarith
    exact pow_ne_zero 2 ht0
  have h1 : ∫ t in (-(1/2))..(1/2), A t
      = (∫ t in (-(1/2))..(-a), A t) + ∫ t in (-a)..(1/2), A t :=
    (intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _)).symm
  have h2 : ∫ t in (-a)..(1/2), A t = (∫ t in (-a)..a, A t) + ∫ t in a..(1/2), A t :=
    (intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _)).symm
  have hval1 : ∫ t in (-(1/2))..(-a), (t^2)⁻¹ = 1/a - 2 := by
    rw [integral_inv_sq_eq (u := -(1/2)) (v := -a) (by norm_num) (by linarith) (by
      intro t ht
      have hle : t ≤ -a := by
        rcases Set.mem_uIcc.mp ht with ⟨-, h2⟩ | ⟨-, h2⟩
        · linarith
        · linarith
      linarith)]
    field_simp
    ring
  have hval2 : ∫ t in a..(1/2), (t^2)⁻¹ = 1/a - 2 := by
    rw [integral_inv_sq_eq (u := a) (v := 1/2) (by linarith) (by norm_num) (by
      intro t ht
      have hle : a ≤ t := by
        rcases Set.mem_uIcc.mp ht with ⟨h1, -⟩ | ⟨h1, -⟩
        · linarith
        · linarith
      linarith)]
    field_simp
    ring
  have hb1 : ‖∫ t in (-(1/2))..(-a), A t‖ ≤ 1/a - 2 := by
    have hs1 : ‖∫ t in (-(1/2))..(-a), A t‖ ≤ ∫ t in (-(1/2))..(-a), ‖A t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    have hs2 : ∫ t in (-(1/2))..(-a), ‖A t‖ ≤ ∫ t in (-(1/2))..(-a), (t^2)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) (hI2 _ _) hpos2
      intro t ht
      rw [Set.mem_Icc] at ht
      have hneg : t < 0 := by linarith [ht.2]
      have habs : |t| = -t := abs_of_neg hneg
      exact hA t (by rw [habs]; linarith [ht.2]) (by rw [habs]; linarith [ht.1])
    rw [hval1] at hs2
    linarith
  have hb2 : ‖∫ t in a..(1/2), A t‖ ≤ 1/a - 2 := by
    have hs1 : ‖∫ t in a..(1/2), A t‖ ≤ ∫ t in a..(1/2), ‖A t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    have hs2 : ∫ t in a..(1/2), ‖A t‖ ≤ ∫ t in a..(1/2), (t^2)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) (hI2 _ _) hpos1
      intro t ht
      rw [Set.mem_Icc] at ht
      have hpos : 0 < t := by linarith [ht.1]
      have habs : |t| = t := abs_of_pos hpos
      exact hA t (by rw [habs]; exact hpos) (by rw [habs]; linarith [ht.2])
    rw [hval2] at hs2
    linarith
  have hdiff : (∫ t in (-a)..a, A t) - ∫ t in (-(1/2))..(1/2), A t
      = -((∫ t in (-(1/2))..(-a), A t) + ∫ t in a..(1/2), A t) := by
    rw [h1, h2]; ring
  rw [hdiff, norm_neg]
  have htri : ‖(∫ t in (-(1/2))..(-a), A t) + ∫ t in a..(1/2), A t‖
      ≤ ‖∫ t in (-(1/2))..(-a), A t‖ + ‖∫ t in a..(1/2), A t‖ := norm_add_le _ _
  have hsb : ‖(∫ t in (-(1/2))..(-a), A t) + ∫ t in a..(1/2), A t‖ ≤ (1/a - 2) + (1/a - 2) := by
    linarith
  rw [le_div_iff₀ ha]
  have h2 : ‖(∫ t in (-(1/2))..(-a), A t) + ∫ t in a..(1/2), A t‖ * a
      ≤ ((1/a - 2) + (1/a - 2)) * a :=
    mul_le_mul_of_nonneg_right hsb (le_of_lt ha)
  have h3 : ((1/a - 2) + (1/a - 2)) * a ≤ 2 := by
    field_simp
    nlinarith [ha]
  linarith

/- M: Ramanujan sum bound -/
private lemma norm_fourier_coe561 (n : ℤ) (x : ℝ) :
    ‖@fourier 1 n (x : AddCircle (1:ℝ))‖ = 1 := by
  rw [fourier_coe_apply, Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]

private lemma card_coprime_Icc_le561 (q : ℕ) :
    ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card ≤ q.totient + 1 := by
  have hsub : (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)
      ⊆ insert q ((Finset.range q).filter (fun r => Nat.Coprime r q)) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    rcases eq_or_lt_of_le hr.1.2 with h | h
    · rw [← h]; exact Finset.mem_insert_self _ _
    · rw [Finset.mem_insert]
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hr.2⟩)
  have hc := Finset.card_le_card hsub
  have hnot : q ∉ (Finset.range q).filter (fun r => Nat.Coprime r q) := by simp
  rw [Finset.card_insert_of_notMem hnot] at hc
  have htot : ((Finset.range q).filter (fun r => Nat.Coprime r q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext r
    simp [Nat.coprime_comm]
  rw [htot] at hc
  exact hc

private lemma norm_ramanujan_le561 (q N : ℕ) (hq : 1 ≤ q) :
    ‖ramanujan512 q N‖ ≤ 2 * (q.totient : ℝ) := by
  have hcard := card_coprime_Icc_le561 q
  have hφ1 : (1:ℝ) ≤ (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  unfold ramanujan512
  have hstep : ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      @fourier 1 (-(N:ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1:ℝ))‖
      ≤ (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) := by
    calc ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        @fourier 1 (-(N:ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1:ℝ))‖
        ≤ ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ‖@fourier 1 (-(N:ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1:ℝ))‖ :=
          norm_sum_le _ _
      _ = (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) := by
          rw [Finset.sum_congr rfl (fun r _ => norm_fourier_coe561 _ _), Finset.sum_const,
            nsmul_eq_mul, mul_one]
  calc ‖_‖ ≤ (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) := hstep
    _ ≤ ((q.totient + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * (q.totient : ℝ) := by push_cast; linarith

/- N: sum of q / phi q -/
private lemma div_totient_le_sqrt561 (q : ℕ) (hq : 1 ≤ q) :
    (q:ℝ)/(q.totient:ℝ) ≤ 2 * Real.sqrt q := by
  have h := totient_sq_ge q
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hφ1 : (1:ℝ) ≤ (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this
  have hφ0 : (0:ℝ) < (q.totient:ℝ) := by linarith
  have hsqrt : (0:ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hge : Real.sqrt (q:ℝ) ≤ 2 * (q.totient:ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (q.totient:ℝ))]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [div_le_iff₀ hφ0]
  nlinarith [hge, hsqrt, Real.sq_sqrt hq0.le, Real.sqrt_nonneg (q:ℝ)]

private lemma sum_div_totient_le561 (Y : ℕ) :
    ∑ q ∈ Finset.Icc 1 Y, (q:ℝ)/(q.totient:ℝ) ≤ 2 * (Y:ℝ) * Real.sqrt Y := by
  calc ∑ q ∈ Finset.Icc 1 Y, (q:ℝ)/(q.totient:ℝ)
      ≤ ∑ q ∈ Finset.Icc 1 Y, 2 * Real.sqrt (Y:ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [Finset.mem_Icc] at hq
        have h1 := div_totient_le_sqrt561 q hq.1
        have h2 : Real.sqrt (q:ℝ) ≤ Real.sqrt Y := Real.sqrt_le_sqrt (by exact_mod_cast hq.2)
        linarith
    _ = 2 * (Y:ℝ) * Real.sqrt Y := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hY : ((Y + 1 - 1 : ℕ) : ℝ) = (Y:ℝ) := by
          rw [Nat.add_sub_cancel]
        rw [hY]
        ring

/- continuity of the integrand in t -/
private lemma continuous_integrand561 (ε x : ℝ) (N : ℕ) :
    Continuous (fun t : ℝ => integrand512 ε x (fun _ => 1) (fun _ => 1) N t) := by
  unfold integrand512 polynomial512
  continuity

/- per-frequency bound on the difference of the two principal models -/
private lemma principalArc_diff_le561 {ε D x : ℝ} {N : ℕ}
    (hε : 0 < ε) (hx3 : 3 ≤ x)
    (haq : ∀ q : ℕ, 1 ≤ q → q ≤ ⌊Real.log x ^ (2*D)⌋₊ →
      Real.log x ^ (4*D) / (q * length512 ε x) ≤ 1/2) :
    ‖principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N‖
      ≤ 4 * length512 ε x / Real.log x ^ (4*D) *
          (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊, (q:ℝ)/(q.totient:ℝ)) /
          (Real.log x * Real.log (length512 ε x)) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hLpos : 0 < length512 ε x := by unfold length512; positivity
  have hlogL : 0 < Real.log (length512 ε x) := by
    apply Real.log_pos
    unfold length512
    exact Real.one_lt_rpow (by linarith) (by linarith)
  have hden : 0 < Real.log x * Real.log (length512 ε x) := mul_pos hlog hlogL
  have hlog4 : 0 < Real.log x ^ (4*D) := Real.rpow_pos_of_pos hlog _
  have hcont := continuous_integrand561 ε x N
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
      ‖(↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
          (∫ t in (-(Real.log x ^ (4*D) / (q * length512 ε x)))..(Real.log x ^ (4*D) / (q * length512 ε x)),
            integrand512 ε x (fun _ => 1) (fun _ => 1) N t)
        - (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
          (∫ t in (-(1/2))..(1/2), integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖
      ≤ 4 * (q:ℝ) * length512 ε x / ((q.totient:ℝ) * Real.log x ^ (4*D)) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hq2⟩ := hq
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
    have hφpos : (0:ℝ) < (q.totient:ℝ) := by
      have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
      exact_mod_cast this
    have hapos : 0 < Real.log x ^ (4*D) / (q * length512 ε x) := by positivity
    have hw : ‖(↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2‖
        ≤ 1/(q.totient:ℝ)^2 := by
      rw [norm_div, norm_pow, norm_pow, Complex.norm_intCast, Complex.norm_natCast]
      have h1 := ArithmeticFunction.abs_moebius_le_one (n := q)
      have hm : |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
        have h2 : ((|ArithmeticFunction.moebius q| : ℤ) : ℝ) ≤ ((1:ℤ) : ℝ) := by
          exact_mod_cast h1
        have h3 : |((ArithmeticFunction.moebius q : ℤ) : ℝ)|
            = ((|ArithmeticFunction.moebius q| : ℤ) : ℝ) := by
          rw [← Int.cast_abs]
        rw [h3]
        simpa using h2
      have hm0 : (0:ℝ) ≤ |((ArithmeticFunction.moebius q : ℤ) : ℝ)| := abs_nonneg _
      have hmm : |((ArithmeticFunction.moebius q : ℤ) : ℝ)|^2 ≤ 1 := by nlinarith [hm, hm0]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmul := mul_le_mul_of_nonneg_right hmm (sq_nonneg ((q.totient:ℝ)))
      linarith
    have hr := norm_ramanujan_le561 q N hq1
    have htail := integral_tail_le hapos (haq q hq1 hq2) hcont
      (fun t h1 h2 => norm_integrand_le (abs_pos.mp h1) h2)
    have hfac : (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
          (∫ t in (-(Real.log x ^ (4*D) / (q * length512 ε x)))..(Real.log x ^ (4*D) / (q * length512 ε x)),
            integrand512 ε x (fun _ => 1) (fun _ => 1) N t)
        - (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
          (∫ t in (-(1/2))..(1/2), integrand512 ε x (fun _ => 1) (fun _ => 1) N t)
        = ((↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2) * ramanujan512 q N *
          ((∫ t in (-(Real.log x ^ (4*D) / (q * length512 ε x)))..(Real.log x ^ (4*D) / (q * length512 ε x)),
            integrand512 ε x (fun _ => 1) (fun _ => 1) N t)
          - (∫ t in (-(1/2))..(1/2), integrand512 ε x (fun _ => 1) (fun _ => 1) N t)) := by ring
    rw [hfac, norm_mul, norm_mul]
    have step1 : ‖(↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2‖ *
        ‖ramanujan512 q N‖ ≤ (1/(q.totient:ℝ)^2) * (2 * (q.totient:ℝ)) := by
      apply mul_le_mul hw hr (norm_nonneg _) (by positivity)
    have step2 : ‖(↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2‖ *
        ‖ramanujan512 q N‖ * ‖(∫ t in (-(Real.log x ^ (4*D) / (q * length512 ε x)))..(Real.log x ^ (4*D) / (q * length512 ε x)),
            integrand512 ε x (fun _ => 1) (fun _ => 1) N t)
          - (∫ t in (-(1/2))..(1/2), integrand512 ε x (fun _ => 1) (fun _ => 1) N t)‖
        ≤ (1/(q.totient:ℝ)^2) * (2 * (q.totient:ℝ)) *
            (2 / (Real.log x ^ (4*D) / (q * length512 ε x))) := by
      apply mul_le_mul step1 htail (norm_nonneg _) (by positivity)
    refine step2.trans ?_
    have hqne : ((q:ℝ)) ≠ 0 := ne_of_gt hqpos
    have ha_ne : Real.log x ^ (4*D) / (q * length512 ε x) ≠ 0 := ne_of_gt hapos
    have hφne : ((q.totient:ℝ)) ≠ 0 := ne_of_gt hφpos
    have hl4ne : Real.log x ^ (4*D) ≠ 0 := ne_of_gt hlog4
    have hLne : length512 ε x ≠ 0 := ne_of_gt hLpos
    field_simp
    norm_num
  unfold principalArc512 completePrincipal561
  rw [← mul_sub, norm_mul]
  have hc : ‖((1:ℝ) : ℂ) * ((1:ℝ) : ℂ) / ((Real.log x : ℂ) * (Real.log (length512 ε x) : ℂ))‖
      = 1/(Real.log x * Real.log (length512 ε x)) := by
    have hnum : ((1:ℝ) : ℂ) * ((1:ℝ) : ℂ) = 1 := by push_cast; ring
    rw [hnum, norm_div, norm_one, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hlog, abs_of_pos hlogL, one_div]
  rw [hc]
  have hsum : ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
        (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
          (∫ t in (-(Real.log x ^ (4*D) / (q * length512 ε x)))..(Real.log x ^ (4*D) / (q * length512 ε x)),
            integrand512 ε x (fun _ => 1) (fun _ => 1) N t))
      - (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
        (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
          (∫ t in (-(1/2))..(1/2), integrand512 ε x (fun _ => 1) (fun _ => 1) N t))‖
      ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
          4 * (q:ℝ) * length512 ε x / ((q.totient:ℝ) * Real.log x ^ (4*D)) := by
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have hAfac : ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
        4 * (q:ℝ) * length512 ε x / ((q.totient:ℝ) * Real.log x ^ (4*D))
      = 4 * length512 ε x / Real.log x ^ (4*D) *
          (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊, (q:ℝ)/(q.totient:ℝ)) := by
    have hc : ∀ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
        4 * (q:ℝ) * length512 ε x / ((q.totient:ℝ) * Real.log x ^ (4*D))
          = (4 * length512 ε x / Real.log x ^ (4*D)) * ((q:ℝ)/(q.totient:ℝ)) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      have hφpos : (0:ℝ) < (q.totient:ℝ) := by
        have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
        exact_mod_cast this
      have hl4ne : Real.log x ^ (4*D) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlog _)
      field_simp
    rw [Finset.sum_congr rfl hc]
    rw [Finset.mul_sum]
  calc 1/(Real.log x * Real.log (length512 ε x)) *
        ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
          (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
            (∫ t in (-(Real.log x ^ (4*D) / (q * length512 ε x)))..(Real.log x ^ (4*D) / (q * length512 ε x)),
              integrand512 ε x (fun _ => 1) (fun _ => 1) N t))
        - (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
          (↑(ArithmeticFunction.moebius q) : ℂ) ^ 2 / (↑(q.totient) : ℂ) ^ 2 * ramanujan512 q N *
            (∫ t in (-(1/2))..(1/2), integrand512 ε x (fun _ => 1) (fun _ => 1) N t))‖
      ≤ 1/(Real.log x * Real.log (length512 ε x)) *
          ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊,
            4 * (q:ℝ) * length512 ε x / ((q.totient:ℝ) * Real.log x ^ (4*D)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * length512 ε x / Real.log x ^ (4*D) *
          (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2*D)⌋₊, (q:ℝ)/(q.totient:ℝ)) /
          (Real.log x * Real.log (length512 ε x)) := by
        rw [hAfac]
        have hdne : Real.log x * Real.log (length512 ε x) ≠ 0 := ne_of_gt hden
        field_simp

/-- LEAF: Display 2.6 on page 8, the eta cutoff error at unit coefficients, with
the number of even frequencies kept explicit instead of replaced by the
frequency interval length. The two removed eta tails are integrated against the
reciprocal square of the distance to the nearest integer and the modulus average
over q divided by phi of q is taken over the full modulus range. The count factor
is handed to the leaves below, so this leaf is weaker than the target in the
coefficient pair, unit coefficients against arbitrary u and v, the quadratic
scaling being proved above, and in its right hand side, which is larger than the
target scale once the count exceeds the interval length. The polynomial tail
reduction and its mean square transfer are what remains open. -/
theorem leaf_eta_tail_unit_coeff561 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100)
    (A : ℝ) (hA : 0 < A) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      etaTailError561 ε D x 1 1 ≤
        C * ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2 *
          Real.log x ^ (-A - 7) := by
  have hθ : 0 < 11 / 20 + ε := by linarith
  refine ⟨(A + 3) / 2, fun D hD => ?_⟩
  have hD2 : A + 3 ≤ 2 * D := by linarith
  have hDpos : 0 < D := by linarith
  have hlit : (fun x : ℝ => Real.log x ^ (4 * D)) =o[Filter.atTop] (fun x : ℝ => x ^ (11/20 + ε)) :=
    isLittleO_log_rpow_rpow_atTop (s := 11/20 + ε) (4 * D) hθ
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    (hlit.tendsto_div_nhds_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  set T : ℝ := max X₁ 3 + 1 with hT
  set K : ℝ := 64 / (11/20 + ε) ^ 2 * Real.log 3 ^ (A + 3 - 2 * D) + 1 with hK
  refine ⟨max T K, fun x hx => ?_⟩
  have hxT : T ≤ x := le_trans (le_max_left T K) hx
  have hxK : K ≤ x := le_trans (le_max_right T K) hx
  have hKle : 64 / (11/20 + ε) ^ 2 * Real.log 3 ^ (A + 3 - 2 * D) ≤ max T K := by
    rw [hK] at hxK
    linarith [le_max_right T K]
  have hT3 : (3:ℝ) ≤ T := by rw [hT]; linarith [le_max_right X₁ 3]
  have hx3 : 3 ≤ x := le_trans hT3 hxT
  have hxX1 : X₁ ≤ x := by rw [hT] at hxT; linarith [le_max_left X₁ 3]
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3le : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3
  have hLdef : length512 ε x = x ^ (11/20 + ε) := rfl
  have hLpos : 0 < length512 ε x := by rw [hLdef]; positivity
  have hlogL : Real.log (length512 ε x) = (11/20 + ε) * Real.log x := by
    rw [hLdef, Real.log_rpow hx0]
  have hlogLpos : 0 < Real.log (length512 ε x) := by rw [hlogL]; positivity
  have hlog4 : 0 < Real.log x ^ (4*D) := Real.rpow_pos_of_pos hlog _
  have haq : ∀ q : ℕ, 1 ≤ q → q ≤ ⌊Real.log x ^ (2*D)⌋₊ →
      Real.log x ^ (4*D) / (q * length512 ε x) ≤ 1/2 := by
    intro q hq1 _
    have hqpos : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
    have hX := hX₁ x hxX1
    rw [div_lt_iff₀ (show (0:ℝ) < x ^ (11/20+ε) by positivity)] at hX
    rw [hLdef, div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ) * x ^ (11/20+ε))]
    nlinarith [hX, hqpos]
  have hB : ∀ N : ℕ, ‖principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N‖
      ≤ 4 * length512 ε x / Real.log x ^ (4*D) *
          (2 * ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ) * Real.sqrt ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ)) /
          (Real.log x * Real.log (length512 ε x)) := by
    intro N
    refine (principalArc_diff_le561 hε hx3 haq).trans ?_
    have hsum := sum_div_totient_le561 ⌊Real.log x ^ (2*D)⌋₊
    have hd : (0:ℝ) < Real.log x * Real.log (length512 ε x) := mul_pos hlog hlogLpos
    apply div_le_div_of_nonneg_right _ hd.le
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have heta : etaTailError561 ε D x 1 1 ≤ ((frequencies512 ε x).card : ℝ) *
      (4 * length512 ε x / Real.log x ^ (4*D) *
          (2 * ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ) * Real.sqrt ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ)) /
          (Real.log x * Real.log (length512 ε x))) ^ 2 := by
    unfold etaTailError561
    have hstep : ∑ N ∈ frequencies512 ε x,
        ‖principalArc512 ε D x 1 1 N - completePrincipal561 ε D x 1 1 N‖ ^ 2
        ≤ ∑ _N ∈ frequencies512 ε x,
          (4 * length512 ε x / Real.log x ^ (4*D) *
            (2 * ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ) * Real.sqrt ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ)) /
            (Real.log x * Real.log (length512 ε x))) ^ 2 :=
      Finset.sum_le_sum (fun N _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hB N) 2)
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  refine heta.trans ?_
  set Yq : ℝ := ((⌊Real.log x ^ (2*D)⌋₊ : ℕ) : ℝ) with hYq
  have hY0 : 0 ≤ Yq := by rw [hYq]; positivity
  have hYle : Yq ≤ Real.log x ^ (2*D) := by
    rw [hYq]; exact Nat.floor_le (Real.rpow_nonneg hlog.le _)
  have hsqr : Real.sqrt Yq ≤ Real.log x ^ D := by
    have h1 : Real.sqrt Yq ≤ Real.sqrt (Real.log x ^ (2*D)) := Real.sqrt_le_sqrt hYle
    have h2 : Real.sqrt (Real.log x ^ (2*D)) = Real.log x ^ D := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlog.le]
      congr 1
      ring
    linarith [h1, h2.le]
  have hprod : Yq * Real.sqrt Yq ≤ Real.log x ^ (3*D) := by
    calc Yq * Real.sqrt Yq ≤ Real.log x ^ (2*D) * Real.log x ^ D :=
          mul_le_mul hYle hsqr (Real.sqrt_nonneg _) (by positivity)
      _ = Real.log x ^ (3*D) := by
          rw [← Real.rpow_add hlog]
          congr 1
          ring
  have hBval : (4 * length512 ε x / Real.log x ^ (4*D) *
          (2 * Yq * Real.sqrt Yq) / (Real.log x * Real.log (length512 ε x)))
        ≤ 8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2)) := by
    have hkey : Real.log x ^ (3*D) / (Real.log x ^ (4*D) * Real.log x ^ 2)
        = Real.log x ^ (-(D + 2)) := by
      rw [← Real.rpow_natCast (x := Real.log x) (n := 2), ← Real.rpow_add hlog,
        ← Real.rpow_sub hlog]
      congr 1
      ring
    have hprod' : 2 * Yq * Real.sqrt Yq ≤ 2 * Real.log x ^ (3*D) := by linarith
    have hlim : 4 * length512 ε x / Real.log x ^ (4*D) *
          (2 * Yq * Real.sqrt Yq) / (Real.log x * Real.log (length512 ε x))
        = 8 / (11/20 + ε) * length512 ε x *
            (Real.log x ^ (3*D) / (Real.log x ^ (4*D) * Real.log x ^ 2)) *
            (Yq * Real.sqrt Yq / Real.log x ^ (3*D)) := by
      rw [hlogL]
      have hθne : (11/20 + ε) ≠ 0 := ne_of_gt hθ
      have h4ne : Real.log x ^ (4*D) ≠ 0 := ne_of_gt hlog4
      have hlne : Real.log x ≠ 0 := ne_of_gt hlog
      have h3ne : Real.log x ^ (3*D) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlog _)
      field_simp
      ring
    rw [hlim, hkey]
    have hfac : (0:ℝ) ≤ 8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2)) := by positivity
    calc 8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2)) *
          (Yq * Real.sqrt Yq / Real.log x ^ (3*D))
        ≤ 8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hfac
          rw [div_le_one (by positivity)]
          exact hprod
      _ = 8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2)) := by ring
  have hB2 : (4 * length512 ε x / Real.log x ^ (4*D) *
          (2 * Yq * Real.sqrt Yq) / (Real.log x * Real.log (length512 ε x))) ^ 2
        ≤ 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-A - 7) *
          Real.log 3 ^ (A + 3 - 2 * D) := by
    have hsq : (8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2))) ^ 2
        = 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-(2*D + 4)) := by
      have hxp : Real.log x ^ (-(2*D + 4)) = Real.log x ^ (-(D + 2)) * Real.log x ^ (-(D + 2)) := by
        rw [← Real.rpow_add hlog]
        congr 1
        ring
      rw [hxp]
      field_simp
      ring
    have hmono : (8 / (11/20 + ε) * length512 ε x * Real.log x ^ (-(D + 2))) ^ 2
        ≤ 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-A - 7) *
          Real.log 3 ^ (A + 3 - 2 * D) := by
      rw [hsq]
      have hexp : -(2*D + 4) = (-A - 7) + (A + 3 - 2*D) := by ring
      rw [show Real.log x ^ (-(2*D + 4)) = Real.log x ^ ((-A - 7) + (A + 3 - 2*D)) by rw [hexp],
        Real.rpow_add hlog]
      have hle : Real.log x ^ (A + 3 - 2*D) ≤ Real.log 3 ^ (A + 3 - 2*D) :=
        Real.rpow_le_rpow_of_nonpos hlog3 hlog3le (by linarith)
      have hpos : (0:ℝ) ≤ 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-A - 7) := by
        have h1 : (0:ℝ) < 11/20 + ε := hθ
        have h2 : (0:ℝ) ≤ length512 ε x ^ 2 := sq_nonneg _
        have h3 : (0:ℝ) ≤ Real.log x ^ (-A - 7) := Real.rpow_nonneg hlog.le _
        positivity
      calc 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 *
            (Real.log x ^ (-A - 7) * Real.log x ^ (A + 3 - 2*D))
          = 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-A - 7) *
              Real.log x ^ (A + 3 - 2*D) := by ring
        _ ≤ 64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-A - 7) *
              Real.log 3 ^ (A + 3 - 2*D) := by
            exact mul_le_mul_of_nonneg_left hle hpos
    exact le_trans (pow_le_pow_left₀ (by positivity) hBval 2) hmono
  have hlg0 : (0:ℝ) ≤ Real.log x ^ (-A - 7) := Real.rpow_nonneg hlog.le _
  calc ((frequencies512 ε x).card : ℝ) *
        (4 * length512 ε x / Real.log x ^ (4*D) *
          (2 * Yq * Real.sqrt Yq) / (Real.log x * Real.log (length512 ε x))) ^ 2
      ≤ ((frequencies512 ε x).card : ℝ) *
          (64 / (11/20 + ε) ^ 2 * length512 ε x ^ 2 * Real.log x ^ (-A - 7) *
            Real.log 3 ^ (A + 3 - 2 * D)) :=
        mul_le_mul_of_nonneg_left hB2 (by positivity)
    _ = (64 / (11/20 + ε) ^ 2 * Real.log 3 ^ (A + 3 - 2 * D)) *
          ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2 * Real.log x ^ (-A - 7) := by
        ring
    _ ≤ max T K * ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2 *
          Real.log x ^ (-A - 7) := by
        have h1 : (64 / (11/20 + ε) ^ 2 * Real.log 3 ^ (A + 3 - 2 * D)) *
            ((frequencies512 ε x).card : ℝ) ≤ max T K * ((frequencies512 ε x).card : ℝ) :=
          mul_le_mul_of_nonneg_right hKle (by positivity)
        have h2 : (64 / (11/20 + ε) ^ 2 * Real.log 3 ^ (A + 3 - 2 * D)) *
            ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2
            ≤ max T K * ((frequencies512 ε x).card : ℝ) * length512 ε x ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        exact mul_le_mul_of_nonneg_right h2 hlg0

/-- LEAF: The number of even frequencies in the closed interval from the
ceiling of x to the floor of x plus the interval length. The interval holds at
most the interval length plus one integers, its even part is at most half of
that, and the length is at least one, so three copies of the length cover the
count. This is the step that replaces the explicit count of the unit
coefficient leaf by the interval length factor of the target scale. -/
theorem leaf_frequencies_card561 (ε x : ℝ) (hε : 0 < ε) (hx : 3 ≤ x) :
    ((frequencies512 ε x).card : ℝ) ≤
      3 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH
  have hx0 : 0 ≤ x := by linarith
  have hs : 0 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) :=
    mul_pos (by linarith) (by norm_num)
  have hH1 : 1 ≤ H := by
    rw [hH]
    exact Real.one_le_rpow (by linarith) hs.le
  have hstep : (frequencies512 ε x).card ≤ ⌊x + H⌋₊ + 1 - ⌈x⌉₊ := by
    calc (frequencies512 ε x).card
        ≤ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).card :=
          Finset.card_filter_le _ _
      _ = ⌊x + H⌋₊ + 1 - ⌈x⌉₊ := by simp only [hH, Nat.card_Icc]
  have hbn : ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) ≤ H + 2 := by
    rcases le_or_gt (⌈x⌉₊) ⌊x + H⌋₊ with h | h
    · have hcast : ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) = ((⌊x + H⌋₊ : ℕ) : ℝ) + 1 - ((⌈x⌉₊ : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : ⌈x⌉₊ ≤ ⌊x + H⌋₊ + 1)]
        push_cast
        ring
      have hb : ((⌊x + H⌋₊ : ℕ) : ℝ) ≤ x + H := Nat.floor_le (by linarith)
      have ha : x ≤ ((⌈x⌉₊ : ℕ) : ℝ) := Nat.le_ceil x
      rw [hcast]
      linarith
    · have hzero : ⌊x + H⌋₊ + 1 - ⌈x⌉₊ = 0 := by omega
      rw [hzero]
      push_cast
      linarith
  calc ((frequencies512 ε x).card : ℝ)
      ≤ ((⌊x + H⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) := by exact_mod_cast hstep
    _ ≤ H + 2 := hbn
    _ ≤ 3 * H := by linarith

/-- LEAF: The target scale is nonnegative on the range: the positive power of x,
the square of the interval length and the arbitrary negative power of the
logarithm are each nonnegative. This is the step that lets a bound at the
enlarged constant be multiplied by the scale without turning the inequality
around, including at x where one of the three factors vanishes and including at
zero coefficients. -/
theorem leaf_scale_nonneg561 (ε A x : ℝ) (hx : 3 ≤ x) : 0 ≤ scale512 ε A x := by
  unfold scale512
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : 0 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := Real.rpow_nonneg hx0 _
  have h2 : 0 ≤ length512 ε x ^ 2 := sq_nonneg _
  have h3 : 0 ≤ Real.log x ^ (-A - 7) := Real.rpow_nonneg hlog.le _
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-- The assembly: the target statement follows from the unit coefficient leaf,
the frequency count leaf and the sign of the scale, with the constant of the
unit coefficient leaf enlarged by the coefficient square and by the count
factor three. The eta cutoff error at general coefficients is recovered from the
unit coefficient error by the proved quadratic scaling. -/
theorem leaf_eta_cutoff561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          etaTailError561 ε D x u v ≤ C * scale512 ε A x := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε hε hε' u v A hA
  obtain ⟨D₀, hD₀⟩ := leaf_eta_tail_unit_coeff561 ε hε hε' A hA
  refine ⟨D₀, fun D hD => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hD₀ D hD
  refine ⟨max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3, fun x hx => ?_⟩
  have hCx : C₁ ≤ x := by
    have h : C₁ ≤ max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
      linarith [le_max_left C₁ (3 * (u ^ 2 * v ^ 2) * C₁),
        le_max_left (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    exact h.trans hx
  have hx3 : 3 ≤ x := by
    have h : (3 : ℝ) ≤ max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
      linarith [le_max_right (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    exact h.trans hx
  set card : ℝ := ((frequencies512 ε x).card : ℝ) with hcard_def
  set Y : ℝ := length512 ε x with hY_def
  set lg : ℝ := Real.log x ^ (-A - 7) with hlg_def
  set H : ℝ := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH_def
  have huv : 0 ≤ u ^ 2 * v ^ 2 := by positivity
  have hcard0 : 0 ≤ card := by
    rw [hcard_def]
    exact Nat.cast_nonneg _
  have hY0 : 0 ≤ Y ^ 2 := by positivity
  have hlg0 : 0 ≤ lg := by
    rw [hlg_def]
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hP0 : 0 ≤ card * Y ^ 2 * lg := mul_nonneg (mul_nonneg hcard0 hY0) hlg0
  have hcardH : card ≤ 3 * H := by
    rw [hcard_def, hH_def]
    exact leaf_frequencies_card561 ε x hε hx3
  have hstep : etaTailError561 ε D x 1 1 ≤ C₁ * card * Y ^ 2 * lg := by
    have h := hC₁ x hCx
    rw [hcard_def, hY_def, hlg_def]
    exact h
  have hK : etaTailError561 ε D x 1 1 ≤ max C₁ 0 * card * Y ^ 2 * lg := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left (C₁ : ℝ) 0) hP0
    calc etaTailError561 ε D x 1 1 ≤ C₁ * card * Y ^ 2 * lg := hstep
      _ = C₁ * (card * Y ^ 2 * lg) := by ring
      _ ≤ max C₁ 0 * (card * Y ^ 2 * lg) := hm
      _ = max C₁ 0 * card * Y ^ 2 * lg := by ring
  have hKH : max C₁ 0 * card * Y ^ 2 * lg ≤ max C₁ 0 * (3 * H) * Y ^ 2 * lg := by
    have h0 : 0 ≤ max C₁ 0 * (Y ^ 2 * lg) :=
      mul_nonneg (le_max_right (C₁ : ℝ) 0) (mul_nonneg hY0 hlg0)
    have hm := mul_le_mul_of_nonneg_right hcardH h0
    calc max C₁ 0 * card * Y ^ 2 * lg = card * (max C₁ 0 * (Y ^ 2 * lg)) := by ring
      _ ≤ (3 * H) * (max C₁ 0 * (Y ^ 2 * lg)) := hm
      _ = max C₁ 0 * (3 * H) * Y ^ 2 * lg := by ring
  have hmain : etaTailError561 ε D x u v ≤
      u ^ 2 * v ^ 2 * (max C₁ 0 * (3 * H) * Y ^ 2 * lg) := by
    rw [etaTailError_units561]
    exact (mul_le_mul_of_nonneg_left hK huv).trans (mul_le_mul_of_nonneg_left hKH huv)
  have hscale_eq : H * Y ^ 2 * lg = scale512 ε A x := by
    rw [hH_def, hY_def, hlg_def]
    unfold scale512
    ring
  have hscale0 : 0 ≤ H * Y ^ 2 * lg := by
    rw [hscale_eq]
    exact leaf_scale_nonneg561 ε A x hx3
  have hcoef : 3 * (u ^ 2 * v ^ 2) * max C₁ 0 ≤
      max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3 := by
    have hm : max (3 * (u ^ 2 * v ^ 2) * C₁) 0 = 3 * (u ^ 2 * v ^ 2) * max C₁ 0 := by
      rw [mul_max_of_nonneg C₁ 0 (by positivity : (0 : ℝ) ≤ 3 * (u ^ 2 * v ^ 2)), mul_zero]
    rw [← hm]
    refine max_le ?_ ?_
    · linarith [le_max_right C₁ (3 * (u ^ 2 * v ^ 2) * C₁),
        le_max_left (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
    · linarith [le_max_right (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0]
  have hlast : u ^ 2 * v ^ 2 * (max C₁ 0 * (3 * H) * Y ^ 2 * lg)
      = (3 * (u ^ 2 * v ^ 2) * max C₁ 0) * (H * Y ^ 2 * lg) := by ring
  rw [hlast] at hmain
  calc etaTailError561 ε D x u v
      ≤ (3 * (u ^ 2 * v ^ 2) * max C₁ 0) * (H * Y ^ 2 * lg) := hmain
    _ ≤ (max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3) * (H * Y ^ 2 * lg) :=
        mul_le_mul_of_nonneg_right hcoef hscale0
    _ = (max (max C₁ (3 * (u ^ 2 * v ^ 2) * C₁)) 0 + 3) * scale512 ε A x := by
        rw [hscale_eq]

end LeanLab.BHP1997.Decomp561m
