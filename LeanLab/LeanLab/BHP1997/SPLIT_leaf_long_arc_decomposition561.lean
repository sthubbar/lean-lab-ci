/-
Independent split of the arc decomposition step of the long coefficient replacement.
The major arc integral is the integral over a finite family of Farey arcs; the four
inputs below supply the continuity of the integrand, the containment of every arc in the
complete period, the pairwise disjointness of the arcs and the additivity of the
integral over a finite disjoint union.  The assembly uses only those four inputs, plus
an elementary change of variable on a single arc.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Continuity step.  The integrand is the product of the two finite polynomial
sums and one character of the circle, hence a finite sum of continuous functions of the
arc variable `t`, with no hypothesis on the coefficients and none on the parity of the
frequency.  This is what makes the integrand integrable on the bounded union of arcs
used in the union step. -/
theorem leaf561_integrand_continuous561 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => integrand512 ε x a b N t) := by
  have hcoe : Continuous (fun t : ℝ => (t : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
  have hfour : ∀ n : ℤ, Continuous (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) :=
    fun n => (fourier n).continuous.comp hcoe
  simp only [integrand512, polynomial512]
  exact Continuous.mul (Continuous.mul
    (continuous_finset_sum _ (fun k _ => continuous_const.mul (hfour _)))
    (continuous_finset_sum _ (fun k _ => continuous_const.mul (hfour _))))
    (hfour _)

/-! #### Private estimates for the containment and separation steps -/

private lemma length512_pos561 {ε x : ℝ} (hx : 0 < x) : 0 < length512 ε x :=
  Real.rpow_pos_of_pos hx _

private lemma order512_base561 (ε x : ℝ) (hx : 0 < x) :
    ((length512 ε x) ^ (2 * ((1 : ℝ) / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 : ℝ) / 2)
      = (length512 ε x) ^ ((1 : ℝ) / 16 - 1 / 10 ^ 5) := by
  have hexp : (2 : ℝ) * ((1 : ℝ) / 16 - 1 / 10 ^ 5) * ((1 : ℝ) / 2)
      = (1 : ℝ) / 16 - 1 / 10 ^ 5 := by norm_num
  rw [← Real.rpow_mul (le_of_lt (length512_pos561 (ε := ε) hx)), hexp]

private lemma order512_eq_zero561 (ε x : ℝ) (hx : 0 ≤ length512 ε x)
    (h : length512 ε x ≤ 1) : order512 ε x = 0 := by
  have h1 : (length512 ε x) ^ (2 * ((1 : ℝ) / 16 - 1 / 10 ^ 5) : ℝ) ≤ 1 :=
    Real.rpow_le_one hx h (by norm_num)
  have h2 : ((length512 ε x) ^ (2 * ((1 : ℝ) / 16 - 1 / 10 ^ 5) : ℝ)) ^ ((1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one (Real.rpow_nonneg hx _) h1 (by norm_num)
  unfold order512
  rw [Nat.floor_eq_zero]
  linarith

private lemma order512_le561 (ε x : ℝ) (hx : 0 < x) :
    (order512 ε x : ℝ) ≤ (length512 ε x) ^ ((1 : ℝ) / 16 - 1 / 10 ^ 5) / 2 := by
  unfold order512
  rw [order512_base561 ε x hx]
  exact Nat.floor_le
    (div_nonneg (le_of_lt (Real.rpow_pos_of_pos (length512_pos561 (ε := ε) hx)
      ((1 : ℝ) / 16 - 1 / 10 ^ 5))) two_pos.le)

private lemma order512_ge561 (ε x : ℝ) (hx : 0 < x) :
    (length512 ε x) ^ ((1 : ℝ) / 16 - 1 / 10 ^ 5) / 2 - 1 < (order512 ε x : ℝ) := by
  unfold order512
  rw [order512_base561 ε x hx]
  have h := Nat.lt_floor_add_one ((length512 ε x) ^ ((1 : ℝ) / 16 - 1 / 10 ^ 5) / 2)
  linarith

/-- For a positive `a` and a positive `b`, the two logarithmic powers occurring in the
arc half widths are eventually smaller than the corresponding powers of `x`. -/
private lemma eventually_log_small561 (a b D : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (4 * D) < x ^ (a / 4) ∧ 2 ≤ x ^ (a / 4) ∧
        Real.log x ^ (2 * D) + 1 < x ^ (a * b) / 2 := by
  have h4 : (fun x : ℝ => Real.log x ^ (4 * D)) =o[Filter.atTop] (fun x : ℝ => x ^ (a / 4)) :=
    isLittleO_log_rpow_rpow_atTop (s := a / 4) (4 * D) (by linarith)
  have h2 : (fun x : ℝ => Real.log x ^ (2 * D)) =o[Filter.atTop] (fun x : ℝ => x ^ (a * b / 8)) :=
    isLittleO_log_rpow_rpow_atTop (s := a * b / 8) (2 * D) (by positivity)
  have hone : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) < x := Filter.eventually_gt_atTop (1 : ℝ)
  have k4 : ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.log x ^ (4 * D) ≤ x ^ (a / 4) := by
    refine ((h4.const_mul_left 2).eventuallyLE.and hone).mono ?_
    rintro x ⟨hx, hx1⟩
    have hx0 : (0 : ℝ) < x := by linarith
    rw [Real.norm_of_nonneg
        (mul_nonneg two_pos.le (Real.rpow_nonneg (Real.log_nonneg hx1.le) _)),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    exact hx
  have k2 : ∀ᶠ x : ℝ in Filter.atTop, 2 * Real.log x ^ (2 * D) ≤ x ^ (a * b / 8) := by
    refine ((h2.const_mul_left 2).eventuallyLE.and hone).mono ?_
    rintro x ⟨hx, hx1⟩
    have hx0 : (0 : ℝ) < x := by linarith
    rw [Real.norm_of_nonneg
        (mul_nonneg two_pos.le (Real.rpow_nonneg (Real.log_nonneg hx1.le) _)),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
    exact hx
  have hu : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (a / 4) :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < a / 4)).eventually
      (Filter.eventually_ge_atTop (2 : ℝ))
  have hv : ∀ᶠ x : ℝ in Filter.atTop, 4 ≤ x ^ (a * b / 8) :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < a * b / 8)).eventually
      (Filter.eventually_ge_atTop (4 : ℝ))
  refine (k4.and (hu.and (k2.and (hv.and hone)))).mono ?_
  rintro x ⟨hx4, hu2, hx2, hv4, hx1⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hpos : 0 < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos (Real.log_pos hx1) _
  have hv0 : (0 : ℝ) < x ^ (a * b / 8) := Real.rpow_pos_of_pos hx0 _
  have hAB : (x ^ (a * b / 8)) ^ 8 = x ^ (a * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have h48 : 4 * x ^ (a * b / 8) ≤ x ^ (a * b) := by
    have h1 : (4 : ℝ) ≤ (x ^ (a * b / 8)) ^ 7 := by
      calc (4 : ℝ) ≤ 4 ^ 7 := by norm_num
        _ ≤ (x ^ (a * b / 8)) ^ 7 := pow_le_pow_left₀ (by norm_num) hv4 7
    have h2 : 4 * x ^ (a * b / 8) ≤ (x ^ (a * b / 8)) ^ 8 := by
      calc 4 * x ^ (a * b / 8) ≤ (x ^ (a * b / 8)) ^ 7 * x ^ (a * b / 8) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hv0)
        _ = (x ^ (a * b / 8)) ^ 8 := by ring
    rwa [hAB] at h2
  exact ⟨by linarith, hu2, by nlinarith⟩

/-- The half width of a single arc is smaller than the gap separating the centre from
the left end of the complete period. -/
private lemma arc_width_lt561 (ε D x : ℝ) (hx : 1 < x) (ha : 0 < 11 / 20 + ε)
    (hlog4 : Real.log x ^ (4 * D) < x ^ ((11 / 20 + ε) / 4))
    (hu2 : 2 ≤ x ^ ((11 / 20 + ε) / 4))
    (q : ℕ) (hq : 1 ≤ q) (hqo : q ≤ order512 ε x) :
    Real.log x ^ (4 * D) / (q * length512 ε x)
      < 1 / ((q : ℝ) * (order512 ε x : ℝ)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hLpos : 0 < length512 ε x := length512_pos561 hx0
  have hL1 : 1 ≤ length512 ε x := Real.one_le_rpow hx.le ha.le
  have hlogpos : 0 < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hspos : (0 : ℝ) < x ^ ((11 / 20 + ε) / 4) := Real.rpow_pos_of_pos hx0 _
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hordpos : (0 : ℝ) < (order512 ε x : ℝ) := by exact_mod_cast lt_of_lt_of_le hq hqo
  have hw : x ^ ((11 / 20 + ε) / 2)
      = x ^ ((11 / 20 + ε) / 4) * x ^ ((11 / 20 + ε) / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hww : x ^ ((11 / 20 + ε) / 2) * x ^ ((11 / 20 + ε) / 2) = length512 ε x := by
    show x ^ ((11 / 20 + ε) / 2) * x ^ ((11 / 20 + ε) / 2) = x ^ (11 / 20 + ε)
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hord : (order512 ε x : ℝ) ≤ x ^ ((11 / 20 + ε) / 2) := by
    have h2 := order_square_le_length561 ε x hL1
    have hs : (order512 ε x : ℝ) ≤ Real.sqrt (length512 ε x) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg (order512 ε x))]
      exact Real.sqrt_le_sqrt h2
    have he : Real.sqrt (length512 ε x) = x ^ ((11 / 20 + ε) / 2) := by
      rw [Real.sqrt_eq_rpow]
      show (x ^ (11 / 20 + ε)) ^ ((1 : ℝ) / 2) = x ^ ((11 / 20 + ε) / 2)
      rw [← Real.rpow_mul hx0.le]
      congr 1
      ring
    rwa [he] at hs
  have hloglt : Real.log x ^ (4 * D) < x ^ ((11 / 20 + ε) / 2) := by
    have h2 : (1 : ℝ) < x ^ ((11 / 20 + ε) / 4) := by linarith
    rw [hw]
    calc Real.log x ^ (4 * D) < x ^ ((11 / 20 + ε) / 4) := hlog4
      _ = x ^ ((11 / 20 + ε) / 4) * 1 := by ring
      _ < x ^ ((11 / 20 + ε) / 4) * x ^ ((11 / 20 + ε) / 4) :=
          mul_lt_mul_of_pos_left h2 hspos
  have hnum : Real.log x ^ (4 * D) * (order512 ε x : ℝ) < length512 ε x := by
    calc Real.log x ^ (4 * D) * (order512 ε x : ℝ)
        ≤ Real.log x ^ (4 * D) * x ^ ((11 / 20 + ε) / 2) :=
          mul_le_mul_of_nonneg_left hord (le_of_lt hlogpos)
      _ < x ^ ((11 / 20 + ε) / 2) * x ^ ((11 / 20 + ε) / 2) :=
          mul_lt_mul_of_pos_right hloglt
            (Real.rpow_pos_of_pos hx0 ((11 / 20 + ε) / 2))
      _ = length512 ε x := hww
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hnum, hqpos, hordpos, hLpos]

/-- Twice the number of arcs, weighted by the common half width factor, stays below one. -/
private lemma arc_widths_sum_lt561 (ε D x : ℝ) (hx : 1 < x) (ha : 0 < 11 / 20 + ε)
    (hlog4 : Real.log x ^ (4 * D) < x ^ ((11 / 20 + ε) / 4))
    (hu2 : 2 ≤ x ^ ((11 / 20 + ε) / 4))
    (q₁ q₂ : ℕ) (h₁ : q₁ ≤ order512 ε x) (h₂ : q₂ ≤ order512 ε x) :
    Real.log x ^ (4 * D) / length512 ε x * ((q₁ : ℝ) + q₂) < 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hLpos : 0 < length512 ε x := length512_pos561 hx0
  have hL1 : 1 ≤ length512 ε x := Real.one_le_rpow hx.le ha.le
  have hlogpos : 0 < Real.log x ^ (4 * D) := Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hspos : (0 : ℝ) < x ^ ((11 / 20 + ε) / 4) := Real.rpow_pos_of_pos hx0 _
  have hw : x ^ ((11 / 20 + ε) / 2)
      = x ^ ((11 / 20 + ε) / 4) * x ^ ((11 / 20 + ε) / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hww : x ^ ((11 / 20 + ε) / 2) * x ^ ((11 / 20 + ε) / 2) = length512 ε x := by
    show x ^ ((11 / 20 + ε) / 2) * x ^ ((11 / 20 + ε) / 2) = x ^ (11 / 20 + ε)
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hord : (order512 ε x : ℝ) ≤ x ^ ((11 / 20 + ε) / 2) := by
    have h2 := order_square_le_length561 ε x hL1
    have hs : (order512 ε x : ℝ) ≤ Real.sqrt (length512 ε x) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg (order512 ε x))]
      exact Real.sqrt_le_sqrt h2
    have he : Real.sqrt (length512 ε x) = x ^ ((11 / 20 + ε) / 2) := by
      rw [Real.sqrt_eq_rpow]
      show (x ^ (11 / 20 + ε)) ^ ((1 : ℝ) / 2) = x ^ ((11 / 20 + ε) / 2)
      rw [← Real.rpow_mul hx0.le]
      congr 1
      ring
    rwa [he] at hs
  have h2log : 2 * Real.log x ^ (4 * D) < x ^ ((11 / 20 + ε) / 2) := by
    rw [hw]
    have hstep : 2 * Real.log x ^ (4 * D) < 2 * x ^ ((11 / 20 + ε) / 4) := by linarith
    have hstep2 : 2 * x ^ ((11 / 20 + ε) / 4)
        ≤ x ^ ((11 / 20 + ε) / 4) * x ^ ((11 / 20 + ε) / 4) := by
      nlinarith [hu2, hspos]
    linarith
  have hmono : ((q₁ : ℝ) + q₂) ≤ 2 * (order512 ε x : ℝ) := by
    have h1 : (q₁ : ℝ) ≤ (order512 ε x : ℝ) := by exact_mod_cast h₁
    have h2 : (q₂ : ℝ) ≤ (order512 ε x : ℝ) := by exact_mod_cast h₂
    linarith
  have hstep1 : Real.log x ^ (4 * D) / length512 ε x * ((q₁ : ℝ) + q₂)
      ≤ Real.log x ^ (4 * D) / length512 ε x * (2 * x ^ ((11 / 20 + ε) / 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ((q₁ : ℝ) + q₂) ≤ 2 * (order512 ε x : ℝ) := hmono
      _ ≤ 2 * x ^ ((11 / 20 + ε) / 2) := by linarith
  have hstep2 : Real.log x ^ (4 * D) / length512 ε x * (2 * x ^ ((11 / 20 + ε) / 2))
      = 2 * Real.log x ^ (4 * D) / x ^ ((11 / 20 + ε) / 2) := by
    rw [← hww]
    field_simp
  have hstep3 : 2 * Real.log x ^ (4 * D) / x ^ ((11 / 20 + ε) / 2) < 1 := by
    rw [div_lt_one (by positivity)]
    exact h2log
  linarith

/-- Distinct reduced fractions with moduli `q₁`, `q₂` are at distance at least
`1/(q₁ q₂)`. -/
private lemma rational_separation561 (q₁ q₂ r₁ r₂ : ℕ) (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (hr₁ : r₁ ≤ q₁) (hr₂ : r₂ ≤ q₂) (hc₁ : Nat.Coprime r₁ q₁) (hc₂ : Nat.Coprime r₂ q₂)
    (hne : (q₁, r₁) ≠ (q₂, r₂)) :
    1 / ((q₁ : ℝ) * q₂) ≤ |(r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂| := by
  have hmul : r₁ * q₂ ≠ r₂ * q₁ := by
    intro h
    have hd₁ : q₁ ∣ q₂ := by
      have hd : q₁ ∣ r₁ * q₂ := by rw [h]; exact dvd_mul_left q₁ r₂
      exact hc₁.symm.dvd_of_dvd_mul_left hd
    have hd₂ : q₂ ∣ q₁ := by
      have hd : q₂ ∣ r₂ * q₁ := by rw [← h]; exact dvd_mul_left q₂ r₁
      exact hc₂.symm.dvd_of_dvd_mul_left hd
    have heq : q₁ = q₂ := Nat.dvd_antisymm hd₁ hd₂
    have h₁ : r₁ * q₂ = r₂ * q₂ := by rw [heq] at h; exact h
    have h₂ : r₁ = r₂ := by
      rcases Nat.eq_zero_or_pos q₂ with h0 | h0
      · omega
      · exact Nat.eq_of_mul_eq_mul_right h0 h₁
    exact hne (by rw [heq, h₂])
  have hq₁R : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂R : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hkey : (r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂
      = ((r₁ : ℝ) * q₂ - (r₂ : ℝ) * q₁) / ((q₁ : ℝ) * q₂) := by
    field_simp
  have hcast : ((r₁ : ℝ) * q₂ - (r₂ : ℝ) * q₁)
      = (((r₁ : ℤ) * q₂ - (r₂ : ℤ) * q₁ : ℤ) : ℝ) := by
    push_cast
    ring
  have hne0 : ((r₁ : ℤ) * q₂ - (r₂ : ℤ) * q₁ : ℤ) ≠ 0 := by
    intro h
    apply hmul
    have h' : (r₁ : ℤ) * (q₂ : ℤ) = (r₂ : ℤ) * (q₁ : ℤ) := by linarith
    exact_mod_cast h'
  have hge : (1 : ℝ) ≤ |((r₁ : ℤ) * q₂ - (r₂ : ℤ) * q₁ : ℤ)| := by
    have h := Int.one_le_abs hne0
    exact_mod_cast h
  have hq₁q₂ : (0 : ℝ) < (q₁ : ℝ) * q₂ := mul_pos hq₁R hq₂R
  have hge' : (1 : ℝ) ≤ |(((r₁ : ℤ) * q₂ - (r₂ : ℤ) * q₁ : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact hge
  calc (1 : ℝ) / ((q₁ : ℝ) * q₂)
      ≤ |(((r₁ : ℤ) * q₂ - (r₂ : ℤ) * q₁ : ℤ) : ℝ)| / ((q₁ : ℝ) * q₂) :=
        div_le_div_of_nonneg_right hge' hq₁q₂.le
    _ = |(r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂| := by
        rw [hkey, abs_div, abs_of_pos hq₁q₂, ← hcast]

/-- LEAF. Containment step.  Every arc of the major arcs lies inside the complete
period of the circle.  The left end of the period is the reciprocal of the Farey order,
which eventually dominates the modulus cutoff, so the reduced centres sit at distance at
least `1/(M*(M+1))` above it while the half width of an arc is a logarithm power over
the block length; the right end is the same bound from below.  Only the elementary
growth of the order and the decay of the half width are used. -/
theorem leaf561_arcs_inside_period561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) ⊆
          period512 ε x := by
  by_cases ha : (0 : ℝ) < 11 / 20 + ε
  · obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
      (eventually_log_small561 (11 / 20 + ε) ((1 : ℝ) / 16 - 1 / 10 ^ 5) D ha (by norm_num))
    refine ⟨max X 2, ?_⟩
    intro x hx q hq r hr
    obtain ⟨hlog4, hu2, hlog2⟩ := hX x (le_trans (le_max_left _ _) hx)
    have hxgt : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hx)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hxgt
    have hx0 : (0 : ℝ) < x := by linarith
    have hLpos : 0 < length512 ε x := length512_pos561 hx0
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq2 : q ≤ min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊ := (Finset.mem_Icc.mp hq).2
    have hqord : q ≤ order512 ε x := le_trans hq2 (min_le_left _ _)
    have hqlog : q ≤ ⌊Real.log x ^ (2 * D)⌋₊ := le_trans hq2 (min_le_right _ _)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hordpos : (0 : ℝ) < (order512 ε x : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hq1 hqord
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    have hrle : r ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2
    have hqo : q < order512 ε x := by
      have hqle : (q : ℝ) ≤ Real.log x ^ (2 * D) := by
        calc (q : ℝ) ≤ (⌊Real.log x ^ (2 * D)⌋₊ : ℝ) := by exact_mod_cast hqlog
          _ ≤ Real.log x ^ (2 * D) :=
              Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg hx1) _)
      have hlb := order512_ge561 ε x hx0
      have hLb : (length512 ε x) ^ ((1 : ℝ) / 16 - 1 / 10 ^ 5)
          = x ^ ((11 / 20 + ε) * ((1 : ℝ) / 16 - 1 / 10 ^ 5)) :=
        (Real.rpow_mul hx0.le (11 / 20 + ε) ((1 : ℝ) / 16 - 1 / 10 ^ 5)).symm
      rw [hLb] at hlb
      have : (q : ℝ) < (order512 ε x : ℝ) := by linarith
      exact_mod_cast this
    have hqordR : (q : ℝ) + 1 ≤ (order512 ε x : ℝ) := by
      have h' : q + 1 ≤ order512 ε x := hqo
      exact_mod_cast h'
    have hW := arc_width_lt561 ε D x hxgt ha hlog4 hu2 q hq1 hqord
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have h1 : (1 : ℝ) / q ≤ (r : ℝ) / q := by
      have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      gcongr
    have h2 : (1 : ℝ) / (order512 ε x : ℝ)
        ≤ (1 : ℝ) / q - 1 / ((q : ℝ) * (order512 ε x : ℝ)) := by
      have heq : (1 : ℝ) / q - 1 / ((q : ℝ) * (order512 ε x : ℝ))
          = ((order512 ε x : ℝ) - 1) / ((q : ℝ) * (order512 ε x : ℝ)) := by
        field_simp
      rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hrq : (r : ℝ) / q ≤ 1 := by
      rw [div_le_one hqpos]
      exact_mod_cast hrle
    have hWle : Real.log x ^ (4 * D) / (q * length512 ε x)
        ≤ 1 / (order512 ε x : ℝ) := by
      have hle1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      have h1 : (1 : ℝ) / ((q : ℝ) * (order512 ε x : ℝ))
          ≤ 1 / (order512 ε x : ℝ) := by
        apply one_div_le_one_div_of_le hordpos
        calc (order512 ε x : ℝ) = 1 * (order512 ε x : ℝ) := by ring
          _ ≤ (q : ℝ) * (order512 ε x : ℝ) :=
              mul_le_mul_of_nonneg_right hle1 (le_of_lt hordpos)
      linarith
    unfold period512
    exact Set.mem_Ioc.mpr ⟨by linarith, by linarith⟩
  · push_neg at ha
    refine ⟨1, ?_⟩
    intro x hx q hq r hr
    have hL1 : length512 ε x ≤ 1 := by
      show x ^ (11 / 20 + ε) ≤ 1
      exact Real.rpow_le_one_of_one_le_of_nonpos hx ha
    have hnn : (0 : ℝ) ≤ length512 ε x := by
      show (0 : ℝ) ≤ x ^ (11 / 20 + ε)
      exact Real.rpow_nonneg (by linarith) _
    have hord : order512 ε x = 0 := order512_eq_zero561 ε x hnn hL1
    rw [hord] at hq
    simp only [Finset.mem_Icc, Nat.zero_min] at hq
    omega

/-- LEAF. Separation step.  Two distinct arcs are disjoint.  Two different reduced
fractions with moduli at most the Farey order differ by at least the reciprocal of the
product of their moduli, while twice the half width of an arc is a logarithm power over
the block length, which is smaller than that reciprocal from some point on.  Reducedness
is what makes the two centres different rationals. -/
theorem leaf561_arcs_pairwise_disjoint561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ q₁ ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r₁ ∈ (Finset.Icc 1 q₁).filter (fun r => Nat.Coprime r q₁),
      ∀ q₂ ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r₂ ∈ (Finset.Icc 1 q₂).filter (fun r => Nat.Coprime r q₂),
        (q₁, r₁) ≠ (q₂, r₂) →
          Disjoint
            (Set.Icc ((r₁ : ℝ) / q₁ - Real.log x ^ (4 * D) / (q₁ * length512 ε x))
              ((r₁ : ℝ) / q₁ + Real.log x ^ (4 * D) / (q₁ * length512 ε x)))
            (Set.Icc ((r₂ : ℝ) / q₂ - Real.log x ^ (4 * D) / (q₂ * length512 ε x))
              ((r₂ : ℝ) / q₂ + Real.log x ^ (4 * D) / (q₂ * length512 ε x))) := by
  by_cases ha : (0 : ℝ) < 11 / 20 + ε
  · obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
      (eventually_log_small561 (11 / 20 + ε) ((1 : ℝ) / 16 - 1 / 10 ^ 5) D ha (by norm_num))
    refine ⟨max X 2, ?_⟩
    intro x hx q₁ hq₁ r₁ hr₁ q₂ hq₂ r₂ hr₂ hne
    obtain ⟨hlog4, hu2, hlog2⟩ := hX x (le_trans (le_max_left _ _) hx)
    have hxgt : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hx)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hxgt
    have hx0 : (0 : ℝ) < x := by linarith
    have hLpos : 0 < length512 ε x := length512_pos561 hx0
    have hq₁1 : 1 ≤ q₁ := (Finset.mem_Icc.mp hq₁).1
    have hq₁o : q₁ ≤ order512 ε x := le_trans (Finset.mem_Icc.mp hq₁).2 (min_le_left _ _)
    have hq₂1 : 1 ≤ q₂ := (Finset.mem_Icc.mp hq₂).1
    have hq₂o : q₂ ≤ order512 ε x := le_trans (Finset.mem_Icc.mp hq₂).2 (min_le_left _ _)
    have hq₁pos : (0 : ℝ) < q₁ := by exact_mod_cast hq₁1
    have hq₂pos : (0 : ℝ) < q₂ := by exact_mod_cast hq₂1
    have hr₁1 : 1 ≤ r₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr₁).1).1
    have hr₁le : r₁ ≤ q₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr₁).1).2
    have hr₂1 : 1 ≤ r₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr₂).1).1
    have hr₂le : r₂ ≤ q₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr₂).1).2
    have hcop₁ : Nat.Coprime r₁ q₁ := (Finset.mem_filter.mp hr₁).2
    have hcop₂ : Nat.Coprime r₂ q₂ := (Finset.mem_filter.mp hr₂).2
    have hsep := rational_separation561 q₁ q₂ r₁ r₂ hq₁1 hq₂1 hr₁le hr₂le hcop₁ hcop₂ hne
    have hWsum := arc_widths_sum_lt561 ε D x hxgt ha hlog4 hu2 q₁ q₂ hq₁o hq₂o
    have hsum : Real.log x ^ (4 * D) / (q₁ * length512 ε x)
          + Real.log x ^ (4 * D) / (q₂ * length512 ε x)
        < |(r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂| := by
      have heq : Real.log x ^ (4 * D) / (q₁ * length512 ε x)
            + Real.log x ^ (4 * D) / (q₂ * length512 ε x)
          = Real.log x ^ (4 * D) / length512 ε x * ((q₁ : ℝ) + q₂) / ((q₁ : ℝ) * q₂) := by
        field_simp
        ring
      rw [heq]
      calc Real.log x ^ (4 * D) / length512 ε x * ((q₁ : ℝ) + q₂) / ((q₁ : ℝ) * q₂)
          < 1 / ((q₁ : ℝ) * q₂) := by
            rw [div_lt_div_iff₀ (by positivity) (by positivity)]
            simpa using mul_lt_mul_of_pos_right hWsum
              (mul_pos hq₁pos hq₂pos : (0 : ℝ) < (q₁ : ℝ) * q₂)
        _ ≤ |(r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂| := hsep
    rw [Set.disjoint_left]
    intro s hs1 hs2
    obtain ⟨ha1, ha2⟩ := hs1
    obtain ⟨hb1, hb2⟩ := hs2
    have h₁ : |s - (r₁ : ℝ) / q₁| ≤ Real.log x ^ (4 * D) / (q₁ * length512 ε x) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have h₂ : |s - (r₂ : ℝ) / q₂| ≤ Real.log x ^ (4 * D) / (q₂ * length512 ε x) := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have htri : |(r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂|
        ≤ Real.log x ^ (4 * D) / (q₁ * length512 ε x)
          + Real.log x ^ (4 * D) / (q₂ * length512 ε x) := by
      calc |(r₁ : ℝ) / q₁ - (r₂ : ℝ) / q₂|
          = |((r₁ : ℝ) / q₁ - s) + (s - (r₂ : ℝ) / q₂)| := by ring_nf
        _ ≤ |(r₁ : ℝ) / q₁ - s| + |s - (r₂ : ℝ) / q₂| := abs_add_le _ _
        _ = |s - (r₁ : ℝ) / q₁| + |s - (r₂ : ℝ) / q₂| := by
            rw [abs_sub_comm ((r₁ : ℝ) / q₁) s]
        _ ≤ _ := by linarith
    linarith
  · push_neg at ha
    refine ⟨1, ?_⟩
    intro x hx q₁ hq₁ r₁ hr₁ q₂ hq₂ r₂ hr₂ hne
    have hL1 : length512 ε x ≤ 1 := by
      show x ^ (11 / 20 + ε) ≤ 1
      exact Real.rpow_le_one_of_one_le_of_nonpos hx ha
    have hnn : (0 : ℝ) ≤ length512 ε x := by
      show (0 : ℝ) ≤ x ^ (11 / 20 + ε)
      exact Real.rpow_nonneg (by linarith) _
    have hord : order512 ε x = 0 := order512_eq_zero561 ε x hnn hL1
    rw [hord] at hq₁
    simp only [Finset.mem_Icc, Nat.zero_min] at hq₁
    omega

/-- LEAF. Union additivity step.  For a continuous integrand and a two level family of
closed arcs that is pairwise disjoint, the integral over the union is the iterated sum of
the integrals over the single arcs.  This is the only measure theoretic step: the arcs
are measurable, their union is a finite one, and continuity makes the integrand
integrable on each arc and on the union.  No arithmetic and no distribution hypothesis
is used. -/
theorem leaf561_union_integral561 (f : ℝ → ℂ) (hf : Continuous f)
    (S : Finset ℕ) (T : ℕ → Finset ℕ) (c w : ℕ → ℕ → ℝ)
    (hdisj : ∀ q₁ ∈ S, ∀ r₁ ∈ T q₁, ∀ q₂ ∈ S, ∀ r₂ ∈ T q₂, (q₁, r₁) ≠ (q₂, r₂) →
      Disjoint (Set.Icc (c q₁ r₁ - w q₁ r₁) (c q₁ r₁ + w q₁ r₁))
        (Set.Icc (c q₂ r₂ - w q₂ r₂) (c q₂ r₂ + w q₂ r₂))) :
    (∫ t in (⋃ q ∈ S, ⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t) =
      ∑ q ∈ S, ∑ r ∈ T q, ∫ t in Set.Icc (c q r - w q r) (c q r + w q r), f t := by
  classical
  have hint : ∀ q r, IntegrableOn f (Set.Icc (c q r - w q r) (c q r + w q r)) :=
    fun q r => hf.integrableOn_Icc
  have hinner : ∀ q ∈ S,
      (∫ t in (⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t) =
        ∑ r ∈ T q, ∫ t in Set.Icc (c q r - w q r) (c q r + w q r), f t := by
    intro q hq
    refine integral_biUnion_finset (T q) (fun r _ => measurableSet_Icc) ?_
      (fun r _ => hint q r)
    intro r₁ hr₁ r₂ hr₂ hne
    exact hdisj q hq r₁ hr₁ q hq r₂ hr₂ (fun h => hne (Prod.mk.inj h).2)
  have hdisj' : Set.Pairwise (↑S) (fun q₁ q₂ =>
      Disjoint (⋃ r ∈ T q₁, Set.Icc (c q₁ r - w q₁ r) (c q₁ r + w q₁ r))
        (⋃ r ∈ T q₂, Set.Icc (c q₂ r - w q₂ r) (c q₂ r + w q₂ r))) := by
    intro q₁ hq₁ q₂ hq₂ hne
    rw [Set.disjoint_left]
    rintro s hs1 hs2
    simp only [Set.mem_iUnion] at hs1 hs2
    obtain ⟨r₁, hr₁, hs1⟩ := hs1
    obtain ⟨r₂, hr₂, hs2⟩ := hs2
    exact Set.disjoint_left.mp
      (hdisj q₁ hq₁ r₁ hr₁ q₂ hq₂ r₂ hr₂ (fun h => hne (Prod.mk.inj h).1)) hs1 hs2
  rw [integral_biUnion_finset S
    (fun q _ => Finset.measurableSet_biUnion _ (fun r _ => measurableSet_Icc))
    hdisj' (fun q _ => integrableOn_finset_iUnion.2 (fun r _ => hint q r))]
  exact Finset.sum_congr rfl (fun q hq => hinner q hq)

/-- A single arc: the set integral over the closed interval equals the integral in the
local variable of the arc, with the centre moved into the integrand. -/
private theorem arc_translate561 (f : ℝ → ℂ) (c w : ℝ) (hw : 0 ≤ w) :
    ∫ t in Set.Icc (c - w) (c + w), f t = ∫ s in (-w)..w, f (c + s) := by
  have hle : c - w ≤ c + w := by linarith
  have h1 : ∫ t in Set.Icc (c - w) (c + w), f t = ∫ t in (c - w)..(c + w), f t := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h2 : ∫ t in (c - w)..(c + w), f t = ∫ t in (-w)..w, f (t + c) := by
    rw [intervalIntegral.integral_comp_add_right (f := f) (a := -w) (b := w) (d := c)]
    rw [show -w + c = c - w by ring, show w + c = c + w by ring]
  have h3 : ∫ t in (-w)..w, f (t + c) = ∫ s in (-w)..w, f (c + s) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrArg f (add_comm s c)
  rw [h1, h2, h3]

/-- The single frequency arc decomposition, assembled from the continuity of the
integrand, the containment of the arcs in the complete period, their pairwise
disjointness and the additivity of the integral over a finite disjoint union.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_arc_decomposition561_split (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  obtain ⟨Xc, hXc⟩ := leaf561_arcs_inside_period561 ε D
  obtain ⟨Xd, hXd⟩ := leaf561_arcs_pairwise_disjoint561 ε D
  refine ⟨max (max Xc Xd) 1 + 1, ?_⟩
  intro x hx a b N
  have hbig : (max (max Xc Xd) 1 : ℝ) ≤ x := by linarith
  have hone : (1 : ℝ) ≤ max (max Xc Xd) 1 := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := le_trans hone hbig
  have hxm : max Xc Xd ≤ x := le_trans (le_max_left (max Xc Xd) (1 : ℝ)) hbig
  have hxc : Xc ≤ x := le_trans (le_max_left Xc Xd) hxm
  have hxd : Xd ≤ x := le_trans (le_max_right Xc Xd) hxm
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < length512 ε x := Real.rpow_pos_of_pos hxpos _
  have hWnn : ∀ q : ℕ, 1 ≤ q → 0 ≤ Real.log x ^ (4 * D) / (q * length512 ε x) := by
    intro q hq
    apply div_nonneg (Real.rpow_nonneg (le_of_lt hlog) _)
    exact mul_nonneg (Nat.cast_nonneg q) (le_of_lt hLpos)
  have hsub : (⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x))) ⊆
      period512 ε x := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨q, hq, r, hr, ht⟩ := ht
    exact hXc x hxc q hq r hr ht
  have hunion : major512 ε D x =
      ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) := by
    have hmaj : major512 ε D x =
        period512 ε x ∩
          ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
            ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
              Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
                ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) := rfl
    rw [hmaj]
    ext t
    constructor
    · rintro ⟨-, ht⟩
      exact ht
    · intro ht
      exact ⟨hsub ht, ht⟩
  rw [hunion]
  rw [leaf561_union_integral561 (fun t : ℝ => integrand512 ε x (a x) (b x) N t)
    (leaf561_integrand_continuous561 ε x (a x) (b x) N)
    (Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊))
    (fun q => (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    (fun q r => (r : ℝ) / q)
    (fun q r => Real.log x ^ (4 * D) / (q * length512 ε x))
    (hXd x hxd)]
  refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => ?_))
  exact arc_translate561 (fun t : ℝ => integrand512 ε x (a x) (b x) N t)
    ((r : ℝ) / q) (Real.log x ^ (4 * D) / (q * length512 ε x))
    (hWnn q (Finset.mem_Icc.mp hq).1)

end LeanLab.BHP1997.Decomp561n
