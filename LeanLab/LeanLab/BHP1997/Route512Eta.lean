/-
P0069 Baker Harman Pintz 1997, Section 2, page 8, the first two displays after 2.6:
extend the eta integral of the principal model to a complete period and replace
the exact convolution count by Y.

This file proves the statement in raw form, with no reference to the 512
definitions, so that Decomp512a can import it. The path is elementary:
orthogonality over a complete period gives the exact count of pairs, which is
within 2 of Y; outside the eta arc each geometric sum is at most 1/(2|t|), so the
tail of the integral is at most 1/(2 eta); the weights are bounded with
1/phi(q) at most K q^(-3/4), and the count of even N in K is at most H + 1.
The threshold is D0 = (A + 7)/2.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512Large

namespace LeanLab.BHP1997.Route512
open Classical Complex MeasureTheory Set
open scoped ComplexConjugate

private theorem norm_fourier512 (n : ℤ) (y : AddCircle (1 : ℝ)) : ‖@fourier 1 n y‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

private theorem cont_fourier512 (n : ℤ) :
    Continuous (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) :=
  (map_continuous (fourier (T := (1 : ℝ)) n)).comp (AddCircle.continuous_mk' 1)

/-- P0069 page 8: the chord bound `4|t| ≤ |e(t) - 1|` on `|t| ≤ 1/2`. -/
theorem four_abs_le512 (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖@fourier 1 (1 : ℤ) (t : AddCircle (1 : ℝ)) - 1‖ := by
  have h1 : @fourier 1 (1 : ℤ) (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  have hpi := Real.pi_pos
  have h3 : |Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [abs_nonneg t]
  have h3' : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [abs_nonneg t]
  rw [h2, Real.norm_eq_abs, abs_mul, abs_two, Real.abs_sin_eq_sin_abs_of_abs_le_pi h3]
  have h4 := Real.mul_le_sin (abs_nonneg (Real.pi * t)) h3'
  have h5 : 2 / Real.pi * |Real.pi * t| = 2 * |t| := by
    rw [abs_mul, abs_of_pos hpi]
    field_simp
  linarith

private theorem geom_telescope512 (t : ℝ) (a b : ℕ) (hab : a ≤ b) :
    (@fourier 1 (1 : ℤ) (t : AddCircle (1 : ℝ)) - 1) *
      ∑ k ∈ Finset.Ioc a b, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)) =
      @fourier 1 ((b : ℤ) + 1) (t : AddCircle (1 : ℝ)) -
        @fourier 1 ((a : ℤ) + 1) (t : AddCircle (1 : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, mul_add, ih]
    push_cast
    rw [fourier_add (m := (b : ℤ) + 1) (n := 1)]
    ring

/-- P0069 page 8: a geometric sum of exponentials over an interval of integers has
norm at most `1/(2|t|)` for `0 < |t| ≤ 1/2`. -/
theorem geom_norm_le512 (t : ℝ) (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) (a b : ℕ) :
    ‖∑ k ∈ Finset.Ioc a b, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))‖ ≤
      1 / (2 * |t|) := by
  have htpos : 0 < |t| := abs_pos.mpr ht0
  rcases le_or_gt a b with hab | hab
  · have h := congrArg norm (geom_telescope512 t a b hab)
    rw [norm_mul] at h
    have h2 : ‖@fourier 1 ((b : ℤ) + 1) (t : AddCircle (1 : ℝ)) -
        @fourier 1 ((a : ℤ) + 1) (t : AddCircle (1 : ℝ))‖ ≤ 2 := by
      calc _ ≤ ‖@fourier 1 ((b : ℤ) + 1) (t : AddCircle (1 : ℝ))‖ +
            ‖@fourier 1 ((a : ℤ) + 1) (t : AddCircle (1 : ℝ))‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_fourier512, norm_fourier512]; norm_num
    have h3 := four_abs_le512 t ht
    have h4 := norm_nonneg
      (∑ k ∈ Finset.Ioc a b, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ)))
    rw [le_div_iff₀ (by positivity)]
    have h5 := mul_le_mul_of_nonneg_right h3 h4
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

/-- P0069 page 8: the integrand `S1 S2 e(-Nt)` with unit coefficients is at most
`1/(4t²)` for `0 < |t| ≤ 1/2`. -/
theorem integrand_norm_le512 (a b c d N : ℕ) (t : ℝ) (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) :
    ‖(∑ k ∈ Finset.Ioc a b, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        (∑ m ∈ Finset.Ioc c d, (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))‖ ≤ 1 / 4 * t ^ (-2 : ℤ) := by
  rw [norm_mul, norm_mul, norm_fourier512, mul_one]
  have h1 := geom_norm_le512 t ht0 ht a b
  have h2 := geom_norm_le512 t ht0 ht c d
  have hpos : 0 < |t| := abs_pos.mpr ht0
  have e : t ^ (-2 : ℤ) = (|t| ^ 2)⁻¹ := by
    rw [sq_abs, zpow_neg]
    norm_cast
  calc _ ≤ (1 / (2 * |t|)) * (1 / (2 * |t|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 1 / 4 * t ^ (-2 : ℤ) := by
      rw [e]
      field_simp
      ring

private theorem cont_integrand512 (S T : Finset ℕ) (N : ℕ) :
    Continuous (fun t : ℝ =>
      (∑ k ∈ S, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        (∑ m ∈ T, (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) :=
  ((continuous_finsetSum S fun k _ => continuous_const.mul (cont_fourier512 k)).mul
    (continuous_finsetSum T fun m _ => continuous_const.mul (cont_fourier512 m))).mul
      (cont_fourier512 _)

/-- P0069 page 8: a continuous function bounded by `1/(4t²)` off the origin has its
integral over a complete period within `1/(2η)` of its integral over `[-η, η]`. -/
theorem tail_le512 (F : ℝ → ℂ) (hF : Continuous F)
    (hb : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 / 2 → ‖F t‖ ≤ 1 / 4 * t ^ (-2 : ℤ))
    (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ‖(∫ t in (-η)..η, F t) - ∫ t in (-1 / 2 : ℝ)..(-1 / 2 + 1), F t‖ ≤ 1 / (2 * η) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have e1 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [e1]
  have split : (∫ t in (-1 / 2 : ℝ)..(1 / 2), F t) =
      (∫ t in (-1 / 2 : ℝ)..(-η), F t) + (∫ t in (-η)..η, F t) + ∫ t in η..(1 / 2), F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _),
      intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have side : ∀ a b : ℝ, a ≤ b → (0 < a ∨ b < 0) → (∀ t ∈ Icc a b, |t| ≤ 1 / 2) →
      ‖∫ t in a..b, F t‖ ≤ 1 / 4 * (a⁻¹ - b⁻¹) := by
    intro a b hab h0 hall
    have h0' : (0 : ℝ) ∉ uIcc a b := by
      rw [uIcc_of_le hab]
      rintro ⟨h1, h2⟩
      rcases h0 with h | h <;> linarith
    calc ‖∫ t in a..b, F t‖ ≤ ∫ t in a..b, ‖F t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, 1 / 4 * t ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_mono_on hab (hF.norm.intervalIntegrable _ _)
          ((intervalIntegral.intervalIntegrable_zpow (Or.inr h0')).const_mul _)
        intro t ht
        refine hb t ?_ (hall t ht)
        rintro rfl
        apply h0'
        rw [uIcc_of_le hab]
        exact ht
      _ = 1 / 4 * (a⁻¹ - b⁻¹) := by
        rw [intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0'⟩)]
        norm_num [zpow_neg_one]
        ring
  have s1 := side η (1 / 2) hη2 (Or.inl hη)
    (fun t ht => by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  have s2 := side (-1 / 2) (-η) (by linarith) (Or.inr (by linarith))
    (fun t ht => by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  rw [split]
  have e2 : (∫ t in (-η)..η, F t) -
      ((∫ t in (-1 / 2 : ℝ)..(-η), F t) + (∫ t in (-η)..η, F t) + ∫ t in η..(1 / 2), F t) =
      -((∫ t in (-1 / 2 : ℝ)..(-η), F t) + ∫ t in η..(1 / 2), F t) := by ring
  rw [e2, norm_neg]
  have e3 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
  have e4 : (-1 / 2 : ℝ)⁻¹ = -2 := by norm_num
  have e5 : (-η)⁻¹ = -η⁻¹ := inv_neg
  have e6 : 1 / (2 * η) = η⁻¹ / 2 := by field_simp
  rw [e3] at s1
  rw [e4, e5] at s2
  rw [e6]
  calc _ ≤ ‖∫ t in (-1 / 2 : ℝ)..(-η), F t‖ + ‖∫ t in η..(1 / 2), F t‖ := norm_add_le _ _
    _ ≤ η⁻¹ / 2 := by linarith

private theorem integral_fourier_raw512 (n : ℤ) (c : ℝ) :
    (∫ t in c..c + 1, @fourier 1 n (t : AddCircle (1 : ℝ))) = if n = 0 then 1 else 0 := by
  have h := fourierCoeff_eq_intervalIntegral (T := (1 : ℝ)) (@fourier 1 n) 0 c
  simp only [one_div_one, one_smul] at h
  rw [fourierCoeff_fourier] at h
  simpa [Pi.single_apply, eq_comm] using h.symm

/-- P0069 page 8: orthogonality over a complete period turns the integral of
`S1 S2 e(-Nt)` with unit coefficients into the count of pairs with `k + m = N`. -/
theorem full_period512 (S T : Finset ℕ) (N : ℕ) (c : ℝ) :
    (∫ t in c..c + 1,
      (∑ k ∈ S, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        (∑ m ∈ T, (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) =
      ∑ m ∈ T, ∑ k ∈ S, if k + m = N then (1 : ℂ) else 0 := by
  have hprod : ∀ t : ℝ,
      (∑ k ∈ S, (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
        (∑ m ∈ T, (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) =
      ∑ k ∈ S, ∑ m ∈ T,
        @fourier 1 ((k : ℤ) + (m : ℤ) - (N : ℤ)) (t : AddCircle (1 : ℝ)) := by
    intro t
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [sub_eq_add_neg, fourier_add, fourier_add]
    ring
  simp_rw [hprod]
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (continuous_finsetSum T fun m _ => cont_fourier512 _).intervalIntegrable _ _)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_finsetSum (fun m _ => (cont_fourier512 _).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_fourier_raw512]
  have he : (k : ℤ) + (m : ℤ) - (N : ℤ) = 0 ↔ k + m = N := by omega
  simp [he]

/-- P0069 page 8: the number of pairs `(k, m)` in `I × J` with `k + m = N` is within
2 of `Y`, for `x ≤ N ≤ x + Y` and `2Y ≤ x`. -/
theorem count512 (x Y : ℝ) (N : ℕ) (hY : 0 ≤ Y) (hxy : 2 * Y ≤ x)
    (hlo : x ≤ (N : ℝ)) (hhi : (N : ℝ) ≤ x + Y) :
    ‖(∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, ∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊,
        if k + m = N then (1 : ℂ) else 0) - (Y : ℂ)‖ ≤ 2 := by
  have hmem : ∀ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊, Y < (m : ℝ) ∧ (m : ℝ) ≤ 2 * Y ∧ m ≤ N := by
    intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    have hmlo : Y < (m : ℝ) := Nat.lt_of_floor_lt hm'.1
    have hmhi : (m : ℝ) ≤ 2 * Y := (Nat.le_floor_iff (by linarith)).mp hm'.2
    exact ⟨hmlo, hmhi, by exact_mod_cast (hmhi.trans (hxy.trans hlo))⟩
  have key : ∀ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊,
      (∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊, if k + m = N then (1 : ℂ) else 0) =
        if N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊ then 1 else 0 := by
    intro m hm
    have hmN := (hmem m hm).2.2
    have h : ∀ k : ℕ, (k + m = N) ↔ (k = N - m) := by intro k; omega
    simp_rw [h]
    rw [Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl key, Finset.sum_boole, ← Complex.ofReal_natCast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hsub : (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).erase ⌊2 * Y⌋₊ ⊆
      (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
        (fun m => N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊) := by
    intro m hm
    have hm1 := Finset.mem_erase.mp hm
    obtain ⟨hmlo, hmhi, hmN⟩ := hmem m hm1.2
    have hm2 : m + 1 ≤ ⌊2 * Y⌋₊ := by
      have := (Finset.mem_Ioc.mp hm1.2).2
      omega
    have hm3 : (m : ℝ) + 1 ≤ 2 * Y := by
      have h2 := Nat.floor_le (by linarith : 0 ≤ 2 * Y)
      have : ((m + 1 : ℕ) : ℝ) ≤ (⌊2 * Y⌋₊ : ℝ) := by exact_mod_cast hm2
      push_cast at this
      linarith
    refine Finset.mem_filter.mpr ⟨hm1.2, Finset.mem_Ioc.mpr ⟨?_, ?_⟩⟩
    · apply (Nat.floor_lt (by linarith : 0 ≤ x - 2 * Y)).mpr
      rw [Nat.cast_sub hmN]
      linarith
    · apply Nat.le_floor
      rw [Nat.cast_sub hmN]
      linarith
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.pred_card_le_card_erase (s := Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) (a := ⌊2 * Y⌋₊)
  have hc3 := Finset.card_filter_le (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊)
    (fun m => N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊)
  have hcard : ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card : ℝ) = (⌊2 * Y⌋₊ : ℝ) - (⌊Y⌋₊ : ℝ) := by
    rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : Y ≤ 2 * Y))]
  have h₁ := Nat.floor_le hY
  have h₂ := Nat.floor_le (by linarith : 0 ≤ 2 * Y)
  have h₃ := Nat.lt_floor_add_one Y
  have h₄ := Nat.lt_floor_add_one (2 * Y)
  have hu : (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
      (fun m => N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊)).card : ℝ) ≤
      ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card : ℝ) := by exact_mod_cast hc3
  have hl : ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card : ℝ) ≤
      (((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
        (fun m => N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊)).card : ℝ) + 1 := by
    have : (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).card ≤ ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
        (fun m => N - m ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊)).card + 1 := by omega
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

/-- P0069 page 8: the weight `μ(q)² c_q(N)/φ(q)²` is bounded, and times `q` it is at
most `K q^(1/2)`. Uses `1/φ(q) ≤ K₀ q^(-3/4)` and the trivial bound `|c_q| ≤ q`. -/
theorem weight_le512 : ∃ K : ℝ, 0 < K ∧ ∀ q N : ℕ, 1 ≤ q →
    ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ ≤ K ∧
    ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ * (q : ℝ) ≤
      K * (q : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨K₀, hK₀, h⟩ := one_div_totient_le512
  refine ⟨K₀ ^ 2, by positivity, fun q N hq => ?_⟩
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hφ : 0 < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hμ : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hsum : ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))‖ ≤ (q : ℝ) := by
    calc _ ≤ ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖@fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ = (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) := by
        simp
      _ ≤ (q : ℝ) := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have hW : ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
        (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ ≤
      (q : ℝ) * (1 / (Nat.totient q : ℝ) ^ 2) := by
    rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    calc _ ≤ 1 ^ 2 / (Nat.totient q : ℝ) ^ 2 * (q : ℝ) := by gcongr
      _ = _ := by ring
  have h1 := h q hq
  have ha : 0 < (q : ℝ) ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hq0 _
  have h2 : 1 / (Nat.totient q : ℝ) ^ 2 ≤ K₀ ^ 2 * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2 := by
    have h3 := mul_le_mul h1 h1 (by positivity) (by positivity)
    calc 1 / (Nat.totient q : ℝ) ^ 2 = 1 / (Nat.totient q : ℝ) * (1 / (Nat.totient q : ℝ)) := by
          ring
      _ ≤ K₀ * (q : ℝ) ^ (-(3 / 4) : ℝ) * (K₀ * (q : ℝ) ^ (-(3 / 4) : ℝ)) := h3
      _ = _ := by ring
  have e1 : (q : ℝ) * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2 =
      (q : ℝ) ^ (1 + (-(3 / 4) + -(3 / 4)) : ℝ) := by
    rw [Real.rpow_add hq0, Real.rpow_add hq0, Real.rpow_one]
    ring
  have e2 : (q : ℝ) * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2 ≤ 1 := by
    rw [e1]
    exact Real.rpow_le_one_of_one_le_of_nonpos hqR (by norm_num)
  have e3 : (q : ℝ) * ((q : ℝ) * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [e1]
    calc (q : ℝ) * (q : ℝ) ^ (1 + (-(3 / 4) + -(3 / 4)) : ℝ) =
          (q : ℝ) ^ (1 + (1 + (-(3 / 4) + -(3 / 4))) : ℝ) := by
          rw [Real.rpow_add hq0 1 (1 + (-(3 / 4) + -(3 / 4))), Real.rpow_one]
      _ ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hqR (by norm_num)
  constructor
  · calc _ ≤ (q : ℝ) * (1 / (Nat.totient q : ℝ) ^ 2) := hW
      _ ≤ (q : ℝ) * (K₀ ^ 2 * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2) := by gcongr
      _ = K₀ ^ 2 * ((q : ℝ) * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2) := by ring
      _ ≤ K₀ ^ 2 * 1 := by gcongr
      _ = K₀ ^ 2 := mul_one _
  · calc _ ≤ (q : ℝ) * (1 / (Nat.totient q : ℝ) ^ 2) * (q : ℝ) := by gcongr
      _ ≤ (q : ℝ) * (K₀ ^ 2 * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2) * (q : ℝ) := by gcongr
      _ = K₀ ^ 2 * ((q : ℝ) * ((q : ℝ) * ((q : ℝ) ^ (-(3 / 4) : ℝ)) ^ 2)) := by ring
      _ ≤ K₀ ^ 2 * (q : ℝ) ^ (1 / 2 : ℝ) := by gcongr

private theorem two_rpow_le512 (a b : ℝ) (hab : a < b) :
    ∀ᶠ x : ℝ in Filter.atTop, 2 * x ^ a ≤ x ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop 2,
    Filter.eventually_gt_atTop 0] with x h2 hx
  have e : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [e]
  nlinarith [Real.rpow_pos_of_pos hx a]

/-- P0069 page 8: the size conditions on `x` used in the eta extension all hold for
large `x`. -/
theorem large512 (θ θ' D : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (hθ' : 0 ≤ θ') (hθ'' : θ' < θ) :
    ∀ᶠ x : ℝ in Filter.atTop, 1 ≤ Real.log x ∧ 1 / θ ≤ Real.log x ∧
      4 * Real.log x ^ (4 * D) ≤ x ^ θ ∧ 2 * x ^ θ ≤ x ∧ x ^ θ' + 1 ≤ x ^ θ ∧ 1 ≤ x := by
  have h1 := Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (1 / θ))
  have h2 := (isLittleO_log_rpow_rpow_atTop (4 * D) hθ).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have h3 := two_rpow_le512 θ 1 hθ1
  have h4 := two_rpow_le512 θ' θ hθ''
  filter_upwards [h1, h2, h3, h4, Filter.eventually_ge_atTop 1] with x a1 a2 a3 a4 a5
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := (le_max_left _ _).trans a1
  refine ⟨hL, (le_max_right _ _).trans a1, ?_, ?_, ?_, a5⟩
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at a2
    linarith
  · simpa using a3
  · have : 1 ≤ x ^ θ' := Real.one_le_rpow a5 hθ'
    linarith

/-- P0069 page 8, the first two displays after 2.6, for one frequency `N`: the
principal model with eta limits differs from the truncated main term by at most
`|c| K Y / R`, where `P = R²` is the range of `q` and `M = R⁴` the arc numerator. -/
theorem eta_pointwise512 (K : ℝ) (hK : 0 < K)
    (hw : ∀ q N : ℕ, 1 ≤ q →
      ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ ≤ K ∧
      ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ * (q : ℝ) ≤
        K * (q : ℝ) ^ (1 / 2 : ℝ))
    (x Y R P M : ℝ) (N : ℕ) (c c' : ℂ) (hR : 1 ≤ R) (hP : P = R ^ 2) (hM : M = R ^ 4)
    (hY : 4 * R ^ 4 ≤ Y) (hxy : 2 * Y ≤ x) (hlo : x ≤ (N : ℝ)) (hhi : (N : ℝ) ≤ x + Y)
    (hc : c' = c * (Y : ℂ)) :
    ‖c * ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          (∫ t in (-(M / (q * Y)))..(M / (q * Y)),
            (∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊,
                (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊,
                (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
      c' * ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ ≤
      ‖c‖ * (K * Y / R) := by
  have hR0 : 0 < R := by linarith
  have hR4 : 0 < R ^ 4 := by positivity
  have hY0 : 0 < Y := by linarith
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  subst hc
  have e : ∀ (w I : ℕ → ℂ) (s : Finset ℕ),
      c * ∑ q ∈ s, w q * I q - c * (Y : ℂ) * ∑ q ∈ s, w q =
        c * ∑ q ∈ s, w q * (I q - (Y : ℂ)) := by
    intro w I s
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  have hU : 0 ≤ Y / (2 * R ^ 4) := by positivity
  have perq : ∀ q ∈ Finset.Icc 1 ⌊P⌋₊,
      ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
          ((∫ t in (-(M / (q * Y)))..(M / (q * Y)),
            (∑ k ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊,
                (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
              (∑ m ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊,
                (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) - (Y : ℂ))‖ ≤
        K * R * (Y / (2 * R ^ 4)) + 2 * K := by
    intro q hq
    have hq' := Finset.mem_Icc.mp hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'.1
    have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
    have hqP : (q : ℝ) ≤ R ^ 2 := by
      rw [← hP]
      exact (Nat.le_floor_iff hP0).mp hq'.2
    obtain ⟨hw1, hw2⟩ := hw q N hq'.1
    have hη : 0 < M / (q * Y) := by rw [hM]; positivity
    have hη2 : M / (q * Y) ≤ 1 / 2 := by
      rw [hM, div_le_iff₀ (by positivity)]
      nlinarith
    have htail := tail_le512 _ (cont_integrand512 (Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊)
      (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) N)
      (fun t ht0 ht => integrand_norm_le512 _ _ _ _ N t ht0 ht) (M / (q * Y)) hη hη2
    rw [full_period512] at htail
    have hcount := count512 x Y N hY0.le hxy hlo hhi
    have e7 : 1 / (2 * (M / (q * Y))) = (q : ℝ) * (Y / (2 * R ^ 4)) := by
      rw [hM]
      field_simp
    rw [e7] at htail
    have hdiff := (norm_add_le _ _).trans (add_le_add htail hcount)
    rw [sub_add_sub_cancel] at hdiff
    have hq12 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ R := by
      calc (q : ℝ) ^ (1 / 2 : ℝ) ≤ (R ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow hq0.le hqP (by norm_num)
        _ = R := by rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hR0.le]
    rw [norm_mul]
    calc _ ≤ ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ *
            ((q : ℝ) * (Y / (2 * R ^ 4)) + 2) :=
          mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
      _ = ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ * (q : ℝ) *
            (Y / (2 * R ^ 4)) +
          2 * ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ := by ring
      _ ≤ K * (q : ℝ) ^ (1 / 2 : ℝ) * (Y / (2 * R ^ 4)) + 2 * K := by gcongr
      _ ≤ K * R * (Y / (2 * R ^ 4)) + 2 * K := by gcongr
  have hcard : ((Finset.Icc 1 ⌊P⌋₊).card : ℝ) ≤ R ^ 2 := by
    rw [Nat.card_Icc, Nat.add_sub_cancel, ← hP]
    exact Nat.floor_le hP0
  have hZ : 4 * R ^ 2 ≤ Y / R := by
    rw [le_div_iff₀ hR0]
    nlinarith
  have hRU : R ^ 2 * (R * (Y / (2 * R ^ 4))) = Y / R / 2 := by
    field_simp
  calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, (K * R * (Y / (2 * R ^ 4)) + 2 * K) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum perq)
    _ = ((Finset.Icc 1 ⌊P⌋₊).card : ℝ) * (K * R * (Y / (2 * R ^ 4)) + 2 * K) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R ^ 2 * (K * R * (Y / (2 * R ^ 4)) + 2 * K) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = K * (R ^ 2 * (R * (Y / (2 * R ^ 4)))) + 2 * K * R ^ 2 := by ring
    _ = K * (Y / R / 2) + 2 * K * R ^ 2 := by rw [hRU]
    _ ≤ K * Y / R := by
      have : K * Y / R = K * (Y / R) := by ring
      rw [this]
      nlinarith

/-- P0069 Baker Harman Pintz 1997, page 8, the first two displays after 2.6, raw
form of the eta extension leaf: for small ε, all real u and v and every A > 0, for
D at least (A + 7)/2 and x large, the mean square over even N in [x, x + H] of the
principal model with eta limits minus the truncated main term is at most
C H Y² (log x)^(-A-7), with Y = x^(11/20+ε) and H = Y^(2(1/16 - 10^(-5))). -/
theorem eta_extension_raw512 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          (∑ N ∈ (Finset.Icc ⌈x⌉₊
              ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
                (fun N => Even N),
            ‖(u * v / (Real.log x * Real.log (x ^ (11 / 20 + ε))) *
                ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
                  (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
                    (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
                      @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))) *
                    ∫ t in (-(Real.log x ^ (4 * D) / (q * x ^ (11 / 20 + ε))))..
                      (Real.log x ^ (4 * D) / (q * x ^ (11 / 20 + ε))),
                      (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
                          (1 : ℂ) * @fourier 1 (k : ℤ) (t : AddCircle (1 : ℝ))) *
                        (∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
                          (1 : ℂ) * @fourier 1 (m : ℤ) (t : AddCircle (1 : ℝ))) *
                          @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) -
              u * v * (x ^ (11 / 20 + ε) : ℝ) /
                  (Real.log x * Real.log (x ^ (11 / 20 + ε))) *
                ∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
                  (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
                    (∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
                      @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ)))‖ ^ 2) ≤
            C * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
              (x ^ (11 / 20 + ε)) ^ 2 * Real.log x ^ (-A - 7)) := by
  obtain ⟨K, hK, hw⟩ := weight_le512
  refine ⟨9 / 20, by norm_num, fun ε hε hε0 u v A hA => ⟨(A + 7) / 2, fun D hD => ?_⟩⟩
  have hD0 : 0 ≤ D := by linarith
  have hθ2 : (0 : ℝ) ≤ 2 * (1 / 16 - 1 / 10 ^ 5) ∧ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) < 1 := by
    norm_num
  have hθ : (0 : ℝ) < 11 / 20 + ε := by linarith
  have hθ1 : 11 / 20 + ε < 1 := by linarith
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (large512 (11 / 20 + ε) ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) D hθ hθ1
      (mul_nonneg hθ.le hθ2.1) (by nlinarith [hθ2.2]))
  refine ⟨max x₀ (2 * (|u| * |v|) ^ 2 * K ^ 2), fun x hx => ?_⟩
  obtain ⟨hL, hL', hY4, hxy, hHY, hx1⟩ := hx₀ x ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hlogY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * Real.log x := Real.log_rpow hx0 _
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hH1 : 1 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
    Real.one_le_rpow hx1 (mul_nonneg hθ.le hθ2.1)
  set Y := x ^ (11 / 20 + ε) with hYdef
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hHdef
  set L := Real.log x with hLdef
  have hL0 : 0 ≤ L := by linarith
  have hR : 1 ≤ L ^ D := Real.one_le_rpow hL hD0
  have hR0 : 0 < L ^ D := by linarith
  have hP : L ^ (2 * D) = (L ^ D) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hL0, Real.rpow_two]
  have hM : L ^ (4 * D) = (L ^ D) ^ 4 := by
    rw [mul_comm, Real.rpow_mul hL0]
    exact_mod_cast Real.rpow_natCast (L ^ D) 4
  have hY4' : 4 * (L ^ D) ^ 4 ≤ Y := by rw [← hM]; exact hY4
  have hLL : 1 ≤ |L| * |Real.log Y| := by
    rw [hlogY, abs_of_nonneg hL0, abs_of_nonneg (mul_nonneg hθ.le hL0)]
    have h1 : 1 ≤ (11 / 20 + ε) * L := by
      have h2 := (div_le_iff₀ hθ).mp hL'
      linarith
    nlinarith
  have hB0 : 0 ≤ K * Y / L ^ D := div_nonneg (mul_nonneg hK.le hY0.le) hR0.le
  refine (Finset.sum_le_sum (g := fun _ => (|u| * |v| * (K * Y / L ^ D)) ^ 2) ?_).trans ?_
  · intro N hN
    have hN' := Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1
    have hlo : x ≤ (N : ℝ) := Nat.ceil_le.mp hN'.1
    have hhi : (N : ℝ) ≤ x + Y := by
      have h1 := (Nat.le_floor_iff (by linarith)).mp hN'.2
      linarith
    apply pow_le_pow_left₀ (norm_nonneg _)
    refine (eta_pointwise512 K hK hw x Y (L ^ D) (L ^ (2 * D)) (L ^ (4 * D)) N _ _ hR hP hM
      hY4' hxy hlo hhi (by ring)).trans ?_
    apply mul_le_mul_of_nonneg_right _ hB0
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hLL
  · rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (mul_le_mul_of_nonneg_right (?_ : _ ≤ 2 * H) (sq_nonneg _)) ?_
    · refine (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans ?_
      rw [Nat.card_Icc]
      have a1 : (⌊x + H⌋₊ : ℝ) ≤ x + H := Nat.floor_le (by linarith)
      have a2 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
      rcases le_or_gt ⌈x⌉₊ (⌊x + H⌋₊ + 1) with h | h
      · rw [Nat.cast_sub h]
        push_cast
        linarith
      · rw [Nat.sub_eq_zero_of_le h.le]
        simp
        linarith
    · have hinv : ((L ^ D) ^ 2)⁻¹ ≤ L ^ (-A - 7) := by
        rw [← hP, ← Real.rpow_neg hL0]
        exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
      have e : 2 * H * (|u| * |v| * (K * Y / L ^ D)) ^ 2 =
          (2 * (|u| * |v|) ^ 2 * K ^ 2) * (H * Y ^ 2 * ((L ^ D) ^ 2)⁻¹) := by ring
      rw [e]
      have hYH : 0 ≤ H * Y ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      calc _ ≤ (2 * (|u| * |v|) ^ 2 * K ^ 2) * (H * Y ^ 2 * L ^ (-A - 7)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hYH) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg hYH (Real.rpow_nonneg hL0 _))

end LeanLab.BHP1997.Route512
