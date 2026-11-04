import LeanLab.Zinoviev1997.ArcArithmetic
import LeanLab.Zinoviev1997.ModelFormula
import LeanLab.Zinoviev1997.State1546

namespace LeanLab.Zinoviev1997.Decomp120
open Real Finset ArithmeticFunction LeanLab.CircleOrth MeasureTheory
open scoped ArithmeticFunction.Moebius

/-- The continuous model on page 352, evaluated as exp of minus 3x over x. -/
noncomputable def continuousModel (N : ℕ) (z : ℝ) : ℂ :=
  let x : ℂ := (1 / (N : ℝ) : ℝ) + 2 * Real.pi * Complex.I * z
  Complex.exp (-3 * x) / x

/-- LEAF. Page 352, elementary supporting step in the geometric model comparison. -/
theorem reciprocal_model_error (x : ℂ) (hx : x ≠ 0) (hsmall : ‖x‖ ≤ 1 / 2) :
    ‖1 / x - 1 / (1 - Complex.exp (-x))‖ ≤ 2 := by
  have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : ‖Complex.exp (-x) - 1 + x‖ ≤ ‖x‖ ^ 2 := by
    simpa using Complex.norm_exp_sub_one_sub_id_le (x := -x) (by simpa using (show ‖x‖ ≤ 1 by linarith))
  have hlo : ‖x‖ - ‖x‖ ^ 2 ≤ ‖1 - Complex.exp (-x)‖ := by
    have hh := norm_sub_norm_le x (1 - Complex.exp (-x))
    have he : x - (1 - Complex.exp (-x)) = Complex.exp (-x) - 1 + x := by ring
    rw [he] at hh
    linarith
  have hdpos : 0 < ‖1 - Complex.exp (-x)‖ := by nlinarith
  have hd : 1 - Complex.exp (-x) ≠ 0 := norm_pos_iff.mp hdpos
  have he : 1 / x - 1 / (1 - Complex.exp (-x)) =
      -(Complex.exp (-x) - 1 + x) / (x * (1 - Complex.exp (-x))) := by
    field_simp
    <;> ring
  rw [he, norm_div, norm_neg, norm_mul, div_le_iff₀ (mul_pos ht hdpos)]
  nlinarith [mul_le_mul_of_nonneg_left hlo ht.le]

/-- LEAF. Page 352, elementary supporting step in the geometric model comparison. -/
theorem major_arc_exponent_small (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z‖ ≤ 1 / 2 := by
  have hn : (0 : ℝ) < N := by linarith
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hs : (100 : ℝ) ≤ Real.sqrt N :=
    (Real.le_sqrt (by norm_num) hn.le).mpr (by linarith)
  have hlog : Real.log N ≤ 2 * Real.sqrt N := by
    have h := Real.log_le_rpow_div hn.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hz' : |z| ≤ 2 * Real.log N / N := by
    refine hz.trans ?_
    unfold arcRadius
    apply div_le_div_of_nonneg_left (by positivity) hn
    nlinarith
  have hnorm : ‖(2 : ℂ) * Real.pi * Complex.I * z‖ = 2 * Real.pi * |z| := by
    simp [norm_mul, Real.pi_pos.le, abs_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ)‖ + ‖(2 : ℂ) * Real.pi * Complex.I * z‖ := norm_add_le _ _
    _ = 1 / (N : ℝ) + 2 * Real.pi * |z| := by
      rw [hnorm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 1 / (N : ℝ) + 2 * Real.pi * (2 * Real.log N / N) := by gcongr
    _ ≤ 1 / 2 := by
      have hsq := Real.sq_sqrt hn.le
      have hp := Real.pi_lt_four
      suffices hh : 1 + 2 * Real.pi * (2 * Real.log N) ≤ (1 / 2 : ℝ) * N by
        calc
          _ = (1 + 2 * Real.pi * (2 * Real.log N)) / N := by ring
          _ ≤ 1 / 2 := (div_le_iff₀ hn).mpr hh
      have hh : 2 * Real.pi * (2 * Real.log N) ≤ 32 * Real.sqrt N := by
        nlinarith [mul_le_mul_of_nonneg_right hp.le hl]
      nlinarith

/-- LEAF. Page 352, elementary supporting step in the geometric model comparison. -/
theorem ratio_eq_exp (N : ℕ) (z : ℝ) :
    modelRatio N (-z) = Complex.exp
      (-((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z))) := by
  unfold modelRatio LeanLab.CircleOrth.ee
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The prime tail T of display 3.1, with the lab's reflected Fourier sign. -/
noncomputable def residueTail (N q l : ℕ) (z : ℝ) : ℂ := by
  classical
  exact ∑' n : ℕ, if n.Prime ∧ Real.sqrt N < n ∧ n % q = l % q then
    ((Real.log n * Real.exp (-(n : ℝ) / N) : ℝ) : ℂ) * ee (-(n : ℝ) * z) else 0

/-- The reduced residue expansion in display 3.1 on page 349. -/
noncomputable def residueExpansion (N q a : ℕ) (z : ℝ) : ℂ :=
  ∑ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
    ee (-((a : ℝ) * l / q)) * residueTail N q l z

/-- `1 - exp (-t) ≥ t/4` for `0 ≤ t ≤ 2`. -/
private theorem one_sub_exp_neg_ge_quarter {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2) :
    t / 4 ≤ 1 - Real.exp (-t) := by
  have hge : 1 + t / 2 ≤ Real.exp (t / 2) := by
    have := Real.add_one_le_exp (t / 2)
    linarith
  have hpos : (0 : ℝ) < 1 + t / 2 := by linarith
  have hhalf : Real.exp (-(t / 2)) ≤ 1 / (1 + t / 2) := by
    have hinv : Real.exp (-(t / 2)) = 1 / Real.exp (t / 2) := by
      rw [Real.exp_neg]
      ring
    rw [hinv]
    exact one_div_le_one_div_of_le hpos hge
  have hsq : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hfac : 1 - Real.exp (-t) =
      (1 - Real.exp (-(t / 2))) * (1 + Real.exp (-(t / 2))) := by
    rw [hsq]; ring
  have hnonneg : 0 ≤ Real.exp (-(t / 2)) := (Real.exp_pos _).le
  have hstep : 1 - 1 / (1 + t / 2) ≤ 1 - Real.exp (-(t / 2)) := by linarith
  have hA0 : (0 : ℝ) ≤ 1 - 1 / (1 + t / 2) := by
    rw [show (1 : ℝ) - 1 / (1 + t / 2) = (t / 2) / (1 + t / 2) by field_simp; ring]
    positivity
  have hb : (1 : ℝ) ≤ 1 + Real.exp (-(t / 2)) := by linarith
  have hmono : 1 - 1 / (1 + t / 2) ≤
      (1 - Real.exp (-(t / 2))) * (1 + Real.exp (-(t / 2))) := by
    have h1 : 1 - 1 / (1 + t / 2) ≤
        (1 - 1 / (1 + t / 2)) * (1 + Real.exp (-(t / 2))) := by nlinarith
    have h2 : (1 - 1 / (1 + t / 2)) * (1 + Real.exp (-(t / 2))) ≤
        (1 - Real.exp (-(t / 2))) * (1 + Real.exp (-(t / 2))) :=
      mul_le_mul_of_nonneg_right hstep (by linarith)
    linarith
  have harith : t / 4 ≤ 1 - 1 / (1 + t / 2) := by
    rw [show (1 : ℝ) - 1 / (1 + t / 2) = (t / 2) / (1 + t / 2) by
      field_simp; ring]
    rw [le_div_iff₀ hpos]
    nlinarith [h0, h2]
  rw [hfac]
  linarith

/-- `∑_{m ≥ 1} exp (-(m+1)²/c) ≤ 6 √c`, uniformly in `c > 0`. -/
private theorem sum_shift_exp_sq_le (c : ℝ) (hc : 0 < c) :
    ∑' m : ℕ, Real.exp (-(((m : ℝ) + 1) ^ 2) / c) ≤ 6 * Real.sqrt c := by
  set s := Real.sqrt c with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc.le
  by_cases hc1 : 1 ≤ c
  · have hs1 : 1 ≤ s := by
      rw [hs]
      exact Real.one_le_sqrt.mpr hc1
    set K : ℕ := ⌊s⌋₊ + 1 with hK
    have hKs : s ≤ (K : ℝ) := by
      have h1 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
      have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
      rw [h2]; linarith
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by linarith
    set q : ℝ := Real.exp (-(K : ℝ) / c) with hq
    have hq0 : 0 < q := Real.exp_pos _
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
      exact div_neg_of_neg_of_pos (by linarith) hc)
    have hle : ∀ m : ℕ,
        Real.exp (-(((m : ℝ) + 1) ^ 2) / c) ≤ (if m < K then (1 : ℝ) else q ^ m) := by
      intro m
      by_cases hm : m < K
      · rw [if_pos hm]
        refine Real.exp_le_one_iff.mpr ?_
        exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ((m:ℝ)+1)]) hc.le
      · rw [if_neg hm]
        have hmK : K ≤ m := Nat.le_of_not_lt hm
        have hmR : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmK
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hqeq : q ^ m = Real.exp (-((m : ℝ) * (K : ℝ)) / c) := by
          rw [hq, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
        rw [hqeq]
        apply Real.exp_le_exp.mpr
        have hsq_ge : ((m : ℝ) + 1) ^ 2 ≥ (m : ℝ) * (K : ℝ) := by nlinarith
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_right hsq_ge hc.le
    have hzero : ∀ m : ℕ, m ∉ Finset.range K → (if m < K then (1 : ℝ) else 0) = 0 := by
      intro m hm
      have h : ¬ (m < K) := by simpa using hm
      simp [h]
    have hfin : Summable fun m : ℕ => (if m < K then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero hzero
    have hgeo : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0.le hq1
    have hpart2 : Summable fun m : ℕ => (if m < K then (0 : ℝ) else q ^ m) := by
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hgeo
      · by_cases hm : m < K
        · simp [hm]
        · simp only [hm, if_false]; exact pow_nonneg hq0.le m
      · by_cases hm : m < K
        · simp only [hm, if_true]; exact pow_nonneg hq0.le m
        · simp only [hm, if_false]; exact le_rfl
    have hsplitR : (fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m)) =
        fun m => (if m < K then (1 : ℝ) else 0) + (if m < K then (0 : ℝ) else q ^ m) := by
      funext m; by_cases hm : m < K <;> simp [hm]
    have hsumR : Summable fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m) := by
      rw [hsplitR]; exact hfin.add hpart2
    have hsumL : Summable fun m : ℕ => Real.exp (-(((m : ℝ) + 1) ^ 2) / c) :=
      Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle hsumR
    have hmain := Summable.tsum_le_tsum hle hsumL hsumR
    have h2 : ∑' m : ℕ, (if m < K then (0 : ℝ) else q ^ m) ≤ ∑' m : ℕ, q ^ m :=
      Summable.tsum_le_tsum (fun m => by
        by_cases hm : m < K
        · simp only [hm, if_true]; exact pow_nonneg hq0.le m
        · simp only [hm, if_false]; exact le_rfl) hpart2 hgeo
    rw [tsum_geometric_of_lt_one hq0.le hq1] at h2
    have hval : ∑' m : ℕ, (if m < K then (1 : ℝ) else q ^ m) ≤ (K : ℝ) + (1 - q)⁻¹ := by
      rw [hsplitR, Summable.tsum_add hfin hpart2]
      rw [tsum_eq_sum (s := Finset.range K) hzero]
      have hKsum : (∑ b ∈ Finset.range K, (if b < K then (1 : ℝ) else 0)) = (K : ℝ) := by
        rw [Finset.sum_congr rfl (fun b hb => by rw [if_pos (Finset.mem_range.mp hb)])]
        simp
      rw [hKsum]
      linarith
    have hmain' : ∑' m : ℕ, Real.exp (-(((m : ℝ) + 1) ^ 2) / c) ≤ (K : ℝ) + (1 - q)⁻¹ :=
      hmain.trans hval
    have hKle : (K : ℝ) ≤ s + 1 := by
      have h1 : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs0
      have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
      rw [h2]; linarith
    have hqbound : (1 - q)⁻¹ ≤ 4 * s := by
      have hKc : (K : ℝ) ≤ 2 * c := by
        have hsc : s ≤ c := by nlinarith [hs0, hs1, hs2]
        linarith
      have ht0 : 0 ≤ (K : ℝ) / c := by positivity
      have ht2 : (K : ℝ) / c ≤ 2 := by
        rw [div_le_iff₀ hc]; linarith
      have hge := one_sub_exp_neg_ge_quarter ht0 ht2
      have hsc' : s / c ≤ (K : ℝ) / c := div_le_div_of_nonneg_right hKs hc.le
      have hsb : s / (4 * c) ≤ (K : ℝ) / c / 4 := by
        have e1 : s / (4 * c) = (s / c) / 4 := by field_simp
        have e2 : s / c / 4 ≤ (K : ℝ) / c / 4 :=
          div_le_div_of_nonneg_right hsc' (by norm_num)
        linarith
      have h1q : s / (4 * c) ≤ 1 - Real.exp (-((K : ℝ) / c)) := by linarith
      have hqeq : q = Real.exp (-((K : ℝ) / c)) := by rw [hq]; congr 1; ring
      rw [hqeq]
      have hspos : (0 : ℝ) < s / (4 * c) := by positivity
      have hpos : (0 : ℝ) < 1 - Real.exp (-((K : ℝ) / c)) := by linarith
      rw [inv_le_iff_one_le_mul₀ hpos]
      have hmul := mul_le_mul_of_nonneg_left h1q (by positivity : (0 : ℝ) ≤ 4 * s)
      have hval : 4 * s * (s / (4 * c)) = 1 := by
        field_simp
        nlinarith [hs2]
      linarith
    have htot : (K : ℝ) + (1 - q)⁻¹ ≤ 6 * s := by linarith
    linarith [hmain', htot]
  · push_neg at hc1
    have hle1 : c ≤ 1 := hc1.le
    have hsle : s ≤ 1 := by
      rw [hs]
      exact Real.sqrt_le_one.mpr hle1
    set r : ℝ := Real.exp (-(1 / c)) with hr
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
      have : (0 : ℝ) < 1 / c := by positivity
      linarith)
    have hle : ∀ m : ℕ,
        Real.exp (-(((m : ℝ) + 1) ^ 2) / c) ≤ r ^ (m + 1) := by
      intro m
      rw [hr, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
      have hc1' : -(((m : ℝ) + 1) ^ 2) / c ≤ -((m : ℝ) + 1) / c :=
        div_le_div_of_nonneg_right (by linarith) hc.le
      have hrw : ((m : ℝ) + 1) * (-(1 / c)) = -((m : ℝ) + 1) / c := by field_simp
      rw [hrw]
      linarith
    have hR : Summable fun m : ℕ => r ^ (m + 1) := by
      have hrw : (fun m : ℕ => r ^ (m + 1)) = fun m => r * r ^ m := by
        funext m; rw [pow_succ]; ring
      rw [hrw]
      exact (summable_geometric_of_lt_one hr0.le hr1).mul_left r
    have hL : Summable fun m : ℕ => Real.exp (-(((m : ℝ) + 1) ^ 2) / c) :=
      Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle hR
    have hmain := Summable.tsum_le_tsum hle hL hR
    have hRval : ∑' m : ℕ, r ^ (m + 1) = r * (1 - r)⁻¹ := by
      have hrw : (fun m : ℕ => r ^ (m + 1)) = fun m => r * r ^ m := by
        funext m; rw [pow_succ]; ring
      rw [hrw, tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
    rw [hRval] at hmain
    -- `r ≤ c` and `(1-r)⁻¹ ≤ 2`
    have hu : (1 / c) * Real.exp (-(1 / c)) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (1 / c)) (Real.exp_pos (-(1 / c))).le
      have h2 : Real.exp (1 / c) * Real.exp (-(1 / c)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [h, h2]
    have hrc : r ≤ c := by
      have h1 : (1 / c) * r ≤ 1 := hu
      have hcne : c * (1 / c) = 1 := by field_simp
      nlinarith [h1, hc, hcne]
    have hre1 : r ≤ Real.exp (-1) := by
      rw [hr]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, le_div_iff₀ hc]
      linarith
    have hexp1 : Real.exp (-1) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1
        linarith
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h2
    have hr12 : r ≤ 1 / 2 := hre1.trans hexp1
    have hinv : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]
      linarith
    have hfin : r * (1 - r)⁻¹ ≤ 6 * s := by
      have hcs : c ≤ s := by rw [← hs2]; nlinarith [hs0]
      nlinarith [hrc, hinv, hr0, hcs]
    linarith


/-- Geometric domination of the shifted Gaussian sum. -/
private theorem summable_shift_sq (c : ℝ) (hc : 0 < c) :
    Summable fun m : ℕ => Real.exp (-(((m : ℝ) + 1) ^ 2) / c) := by
  have hq0 : 0 < Real.exp (-(1 / c)) := Real.exp_pos _
  have hq1 : Real.exp (-(1 / c)) < 1 := Real.exp_lt_one_iff.mpr (by
    have : (0 : ℝ) < 1 / c := by positivity
    linarith)
  have hle : ∀ m : ℕ,
      Real.exp (-(((m : ℝ) + 1) ^ 2) / c) ≤ (Real.exp (-(1 / c))) ^ m := by
    intro m
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h1 : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
    have hc' : -(((m : ℝ) + 1) ^ 2) / c ≤ -(m : ℝ) / c :=
      div_le_div_of_nonneg_right (by linarith) hc.le
    have hrw : (m : ℝ) * (-(1 / c)) = -(m : ℝ) / c := by field_simp
    rw [hrw]
    linarith
  exact Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle
    (summable_geometric_of_lt_one hq0.le hq1)

/-- The unshifted Gaussian sum for `c ≥ 1`: `∑_m exp (-m²/c) ≤ 1 + 6 √c`. -/
private theorem sum_exp_sq_le_large (c : ℝ) (hc : 0 < c) (hc1 : 1 ≤ c) :
    ∑' m : ℕ, Real.exp (-((m : ℝ) ^ 2) / c) ≤ 1 + 6 * Real.sqrt c := by
  set s := Real.sqrt c with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc.le
  set K : ℕ := ⌊s⌋₊ + 1 with hK
  have hKs : s ≤ (K : ℝ) := by
    have h1 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
    have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
    rw [h2]; linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by omega)
    exact_mod_cast this
  set q : ℝ := Real.exp (-(K : ℝ) / c) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
    exact div_neg_of_neg_of_pos (by linarith) hc)
  have hle : ∀ m : ℕ,
      Real.exp (-((m : ℝ) ^ 2) / c) ≤ (if m < K then (1 : ℝ) else q ^ m) := by
    intro m
    by_cases hm : m < K
    · rw [if_pos hm]
      refine Real.exp_le_one_iff.mpr ?_
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (m:ℝ)]) hc.le
    · rw [if_neg hm]
      have hmK : K ≤ m := Nat.le_of_not_lt hm
      have hmR : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmK
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hqeq : q ^ m = Real.exp (-((m : ℝ) * (K : ℝ)) / c) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hqeq]
      apply Real.exp_le_exp.mpr
      have hsq_ge : ((m : ℝ)) ^ 2 ≥ (m : ℝ) * (K : ℝ) := by nlinarith
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right hsq_ge hc.le
  have hzero : ∀ m : ℕ, m ∉ Finset.range K → (if m < K then (1 : ℝ) else 0) = 0 := by
    intro m hm
    have h : ¬ (m < K) := by simpa using hm
    simp [h]
  have hfin : Summable fun m : ℕ => (if m < K then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero hzero
  have hgeo : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0.le hq1
  have hpart2 : Summable fun m : ℕ => (if m < K then (0 : ℝ) else q ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hgeo
    · by_cases hm : m < K
      · simp [hm]
      · simp only [hm, if_false]; exact pow_nonneg hq0.le m
    · by_cases hm : m < K
      · simp only [hm, if_true]; exact pow_nonneg hq0.le m
      · simp only [hm, if_false]; exact le_rfl
  have hsplitR : (fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m)) =
      fun m => (if m < K then (1 : ℝ) else 0) + (if m < K then (0 : ℝ) else q ^ m) := by
    funext m; by_cases hm : m < K <;> simp [hm]
  have hsumR : Summable fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m) := by
    rw [hsplitR]; exact hfin.add hpart2
  have hsumL : Summable fun m : ℕ => Real.exp (-((m : ℝ) ^ 2) / c) :=
    Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle hsumR
  have hmain := Summable.tsum_le_tsum hle hsumL hsumR
  have h2 : ∑' m : ℕ, (if m < K then (0 : ℝ) else q ^ m) ≤ ∑' m : ℕ, q ^ m :=
    Summable.tsum_le_tsum (fun m => by
      by_cases hm : m < K
      · simp only [hm, if_true]; exact pow_nonneg hq0.le m
      · simp only [hm, if_false]; exact le_rfl) hpart2 hgeo
  rw [tsum_geometric_of_lt_one hq0.le hq1] at h2
  have hval : ∑' m : ℕ, (if m < K then (1 : ℝ) else q ^ m) ≤ (K : ℝ) + (1 - q)⁻¹ := by
    rw [hsplitR, Summable.tsum_add hfin hpart2]
    rw [tsum_eq_sum (s := Finset.range K) hzero]
    have hKsum : (∑ b ∈ Finset.range K, (if b < K then (1 : ℝ) else 0)) = (K : ℝ) := by
      rw [Finset.sum_congr rfl (fun b hb => by rw [if_pos (Finset.mem_range.mp hb)])]
      simp
    rw [hKsum]
    linarith
  have hmain' : ∑' m : ℕ, Real.exp (-((m : ℝ) ^ 2) / c) ≤ (K : ℝ) + (1 - q)⁻¹ :=
    hmain.trans hval
  have hKle : (K : ℝ) ≤ s + 1 := by
    have h1 : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs0
    have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
    rw [h2]; linarith
  have hqbound : (1 - q)⁻¹ ≤ 4 * s := by
    have hsc' : s / c ≤ (K : ℝ) / c := div_le_div_of_nonneg_right hKs hc.le
    have hsb : s / (4 * c) ≤ (K : ℝ) / c / 4 := by
      have e1 : s / (4 * c) = (s / c) / 4 := by field_simp
      have e2 : s / c / 4 ≤ (K : ℝ) / c / 4 :=
        div_le_div_of_nonneg_right hsc' (by norm_num)
      linarith
    have ht0 : 0 ≤ (K : ℝ) / c := le_of_lt (by positivity)
    have ht2 : (K : ℝ) / c ≤ 2 := by
      rw [div_le_iff₀ hc]
      have hs1 : (1 : ℝ) ≤ s := Real.one_le_sqrt.mpr hc1
      have hsc : s ≤ c := by nlinarith [hs0, hs1, hs2]
      nlinarith [hKle, hsc]
    have hge := one_sub_exp_neg_ge_quarter ht0 ht2
    have h1q : s / (4 * c) ≤ 1 - Real.exp (-((K : ℝ) / c)) := by linarith
    have hqeq : q = Real.exp (-((K : ℝ) / c)) := by rw [hq]; congr 1; ring
    rw [hqeq]
    have hspos : (0 : ℝ) < s / (4 * c) := by
      have : 0 < s / (4 * c) := by
        apply div_pos _ (by positivity)
        rw [hs]; exact Real.sqrt_pos.mpr hc
      exact this
    have hpos : (0 : ℝ) < 1 - Real.exp (-((K : ℝ) / c)) := by linarith
    rw [inv_le_iff_one_le_mul₀ hpos]
    have hmul := mul_le_mul_of_nonneg_left h1q (by positivity : (0 : ℝ) ≤ 4 * s)
    have hv : 4 * s * (s / (4 * c)) = 1 := by
      field_simp
      nlinarith [hs2]
    linarith
  have htot : (K : ℝ) + (1 - q)⁻¹ ≤ 1 + 6 * s := by linarith
  linarith [hmain', htot]

/-- The unshifted Gaussian sum: `∑_m exp (-m²/c) ≤ 1 + 6 √c`. -/
private theorem sum_exp_sq_le (c : ℝ) (hc : 0 < c) :
    ∑' m : ℕ, Real.exp (-((m : ℝ) ^ 2) / c) ≤ 1 + 6 * Real.sqrt c := by
  by_cases hc1 : 1 ≤ c
  · exact sum_exp_sq_le_large c hc hc1
  · push_neg at hc1
    set r : ℝ := Real.exp (-(1 / c)) with hr
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
      have : (0 : ℝ) < 1 / c := by positivity
      linarith)
    have hle : ∀ m : ℕ, Real.exp (-((m : ℝ) ^ 2) / c) ≤ r ^ m := by
      intro m
      rw [hr, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h1 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp
        · have h2 : (1 : ℕ) ≤ m := h0
          have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
          have hm2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg (α := ℝ) m
          nlinarith [h1, hm2]
      have hc' : -((m : ℝ) ^ 2) / c ≤ -(m : ℝ) / c :=
        div_le_div_of_nonneg_right (by linarith) hc.le
      have hrw : (m : ℝ) * (-(1 / c)) = -(m : ℝ) / c := by field_simp
      rw [hrw]
      linarith
    have hR : Summable fun m : ℕ => r ^ m := summable_geometric_of_lt_one hr0.le hr1
    have hL : Summable fun m : ℕ => Real.exp (-((m : ℝ) ^ 2) / c) :=
      Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle hR
    have hmain := Summable.tsum_le_tsum hle hL hR
    rw [tsum_geometric_of_lt_one hr0.le hr1] at hmain
    -- `r ≤ 1/2` and `2 r ≤ 6 √c`
    have hre1 : r ≤ Real.exp (-1) := by
      rw [hr]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, le_div_iff₀ hc]
      linarith
    have hexp1 : Real.exp (-1) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1
        linarith
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h2
    have hr12 : r ≤ 1 / 2 := hre1.trans hexp1
    -- `2 r ≤ 6 √c` via `e^{-u²} u ≤ 1` with `u = 1/√c`
    have hsq : 2 * r ≤ 6 * Real.sqrt c := by
      have hsp : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
      have hu2 : (1 / Real.sqrt c) ^ 2 = 1 / c := by
        rw [div_pow, Real.sq_sqrt hc.le]; norm_num
      have key1 : (1 / Real.sqrt c) * Real.exp (-((1 / Real.sqrt c) ^ 2)) ≤ 1 := by
        have hu : (0 : ℝ) < 1 / Real.sqrt c := by positivity
        have h1 : (1 / Real.sqrt c) ≤ Real.exp ((1 / Real.sqrt c) ^ 2) := by
          have := Real.add_one_le_exp ((1 / Real.sqrt c) ^ 2)
          nlinarith [hu, sq_nonneg (1 / Real.sqrt c)]
        have h2 := mul_le_mul_of_nonneg_right h1
          (Real.exp_pos (-((1 / Real.sqrt c) ^ 2))).le
        have h3 : Real.exp ((1 / Real.sqrt c) ^ 2) *
            Real.exp (-((1 / Real.sqrt c) ^ 2)) = 1 := by
          rw [← Real.exp_add]; simp
        linarith
      have key : (1 / Real.sqrt c) * r ≤ 1 := by
        rw [hr, show -(1 / c) = -((1 / Real.sqrt c) ^ 2) by rw [hu2]]
        exact key1
      have hrc : r ≤ Real.sqrt c := by
        have e : Real.sqrt c * (1 / Real.sqrt c) = 1 := by field_simp
        nlinarith [key, hsp, e, hr0]
      linarith [hrc, Real.sqrt_nonneg c]
    have hfin : (1 - r)⁻¹ ≤ 1 + 6 * Real.sqrt c := by
      have hp : (0 : ℝ) < 1 - r := by linarith
      have hrw : (1 - r)⁻¹ = 1 + r * (1 - r)⁻¹ := by
        field_simp
        ring
      have hinv2 : (1 - r)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ hp]
        linarith
      rw [hrw]
      nlinarith [hr0, hr12, hinv2, hsq, Real.sqrt_nonneg c]
    linarith

/-- The logarithmic transfer: `log x · exp (-x/c) ≤ (log (c+2) + 2) · exp (-x/(2c))`. -/
private theorem log_mul_exp_le {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x * Real.exp (-(x / c)) ≤
      (Real.log (c + 2) + 2) * Real.exp (-(x / (2 * c))) := by
  have h2c : (0 : ℝ) < 2 * c := by linarith
  have hx2c : (0 : ℝ) < x / (2 * c) := by positivity
  have hsplit : Real.log x = Real.log (x / (2 * c)) + Real.log (2 * c) := by
    have h := Real.log_mul (ne_of_gt hx2c) (ne_of_gt h2c)
    rw [← h]
    field_simp
  have hA : Real.log (x / (2 * c)) ≤ x / (2 * c) := Real.log_le_self hx2c.le
  have hB : Real.log (2 * c) ≤ Real.log (c + 2) + 1 := by
    have h1 : Real.log (2 * c) = Real.log 2 + Real.log c := Real.log_mul (by norm_num) (ne_of_gt hc)
    have h2 : Real.log c ≤ Real.log (c + 2) := Real.log_le_log hc (by linarith)
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hlogc : (0 : ℝ) ≤ Real.log (c + 2) := by
    apply Real.log_nonneg
    linarith
  have e1 : (0 : ℝ) < Real.exp (-(x / (2 * c))) := Real.exp_pos _
  have hexp1 : Real.exp (-(x / (2 * c))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0 : ℝ) ≤ x / (2 * c) := by positivity
    linarith
  -- the key intermediate bound
  have key : Real.log x * Real.exp (-(x / (2 * c))) ≤ Real.log (c + 2) + 2 := by
    have h1 : Real.log x ≤ x / (2 * c) + (Real.log (c + 2) + 1) := by linarith
    have h2 : Real.log x * Real.exp (-(x / (2 * c))) ≤
        (x / (2 * c) + (Real.log (c + 2) + 1)) * Real.exp (-(x / (2 * c))) :=
      mul_le_mul_of_nonneg_right h1 e1.le
    have hu : (x / (2 * c)) * Real.exp (-(x / (2 * c))) ≤ 1 := by
      have hge : (0 : ℝ) ≤ x / (2 * c) := by positivity
      have hle : x / (2 * c) ≤ Real.exp (x / (2 * c)) := by
        have := Real.add_one_le_exp (x / (2 * c))
        linarith
      have hm := mul_le_mul_of_nonneg_right hle e1.le
      have h3 : Real.exp (x / (2 * c)) * Real.exp (-(x / (2 * c))) = 1 := by
        rw [← Real.exp_add]; simp
      linarith
    have hneg : (Real.log (c + 2) + 1) * Real.exp (-(x / (2 * c))) ≤ Real.log (c + 2) + 1 := by
      calc (Real.log (c + 2) + 1) * Real.exp (-(x / (2 * c)))
          ≤ (Real.log (c + 2) + 1) * 1 := by
            apply mul_le_mul_of_nonneg_left hexp1 (by linarith)
        _ = Real.log (c + 2) + 1 := by ring
    have expand : (x / (2 * c) + (Real.log (c + 2) + 1)) * Real.exp (-(x / (2 * c))) =
        (x / (2 * c)) * Real.exp (-(x / (2 * c))) +
          (Real.log (c + 2) + 1) * Real.exp (-(x / (2 * c))) := by ring
    rw [expand] at h2
    linarith [h2, hu, hneg]
  -- reassemble
  have hfac : Real.log x * Real.exp (-(x / c)) =
      (Real.log x * Real.exp (-(x / (2 * c)))) * Real.exp (-(x / (2 * c))) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfac]
  exact mul_le_mul_of_nonneg_right key e1.le


/-- Summability of the Gaussian series. -/
private theorem summable_exp_sq (c : ℝ) (hc : 0 < c) :
    Summable fun m : ℕ => Real.exp (-((m : ℝ) ^ 2) / c) := by
  set s := Real.sqrt c with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  set K : ℕ := ⌊s⌋₊ + 1 with hK
  have hKs : s ≤ (K : ℝ) := by
    have h1 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
    have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
    rw [h2]; linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h1 : (1 : ℕ) ≤ K := Nat.one_le_iff_ne_zero.mpr (by omega)
    exact_mod_cast h1
  set q : ℝ := Real.exp (-(K : ℝ) / c) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
    exact div_neg_of_neg_of_pos (by linarith) hc)
  have hle : ∀ m : ℕ,
      Real.exp (-((m : ℝ) ^ 2) / c) ≤ (if m < K then (1 : ℝ) else q ^ m) := by
    intro m
    by_cases hm : m < K
    · rw [if_pos hm]
      refine Real.exp_le_one_iff.mpr ?_
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (m:ℝ)]) hc.le
    · rw [if_neg hm]
      have hmK : K ≤ m := Nat.le_of_not_lt hm
      have hmR : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmK
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg (α := ℝ) m
      have hqeq : q ^ m = Real.exp (-((m : ℝ) * (K : ℝ)) / c) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hqeq]
      apply Real.exp_le_exp.mpr
      have hsq_ge : ((m : ℝ)) ^ 2 ≥ (m : ℝ) * (K : ℝ) := by nlinarith
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right hsq_ge hc.le
  have hzero : ∀ m : ℕ, m ∉ Finset.range K → (if m < K then (1 : ℝ) else 0) = 0 := by
    intro m hm
    have h : ¬ (m < K) := by simpa using hm
    simp [h]
  have hfin : Summable fun m : ℕ => (if m < K then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero hzero
  have hgeo : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0.le hq1
  have hpart2 : Summable fun m : ℕ => (if m < K then (0 : ℝ) else q ^ m) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hgeo
    · by_cases hm : m < K
      · simp [hm]
      · simp only [hm, if_false]; exact pow_nonneg hq0.le m
    · by_cases hm : m < K
      · simp only [hm, if_true]; exact pow_nonneg hq0.le m
      · simp only [hm, if_false]; exact le_rfl
  have hsplitR : (fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m)) =
      fun m => (if m < K then (1 : ℝ) else 0) + (if m < K then (0 : ℝ) else q ^ m) := by
    funext m; by_cases hm : m < K <;> simp [hm]
  have hsumR : Summable fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m) := by
    rw [hsplitR]; exact hfin.add hpart2
  exact Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) hle hsumR

/-- Termwise logarithmic transfer for `m : ℕ`. -/
private theorem log_exp_sq_term {m : ℕ} {c : ℝ} (hc : 0 < c) :
    Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c) ≤
      (Real.log (c + 2) + 2) * Real.exp (-((m : ℝ) ^ 2) / (2 * c)) := by
  have hC0 : (0 : ℝ) ≤ Real.log (c + 2) + 2 := by
    have : (0 : ℝ) ≤ Real.log (c + 2) := by
      apply Real.log_nonneg
      linarith
    linarith
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    have hz : Real.log (((0 : ℕ)) : ℝ) = 0 := by simp
    rw [hz, zero_mul]
    positivity
  · have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h0
    have hsq : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have h1 := log_mul_exp_le (x := (m : ℝ) ^ 2) (c := c) hsq hc
    have hlog : Real.log ((m : ℝ) ^ 2) = 2 * Real.log (m : ℝ) := by
      rw [pow_two, Real.log_mul (ne_of_gt hm) (ne_of_gt hm)]; ring
    rw [hlog] at h1
    rw [show -(↑m ^ 2 / c) = -((m : ℝ) ^ 2) / c by ring,
      show -(↑m ^ 2 / (2 * c)) = -((m : ℝ) ^ 2) / (2 * c) by ring] at h1
    have hexp : (0 : ℝ) ≤ Real.exp (-((m : ℝ) ^ 2) / (2 * c)) := (Real.exp_pos _).le
    have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 1 / 2)
    have e1 : Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c) =
        (1 / 2) * (2 * Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c)) := by ring
    have e2 : (1 / 2) * ((Real.log (c + 2) + 2) * Real.exp (-((m : ℝ) ^ 2) / (2 * c))) ≤
        (Real.log (c + 2) + 2) * Real.exp (-((m : ℝ) ^ 2) / (2 * c)) := by
      nlinarith [hexp, hC0]
    linarith [h1', e1, e2]

/-- `∑_m log m · exp (-m²/c) ≤ (log (c+2) + 2) · (1 + 6 √(2c))`. -/
private theorem sum_log_exp_sq_le (c : ℝ) (hc : 0 < c) :
    ∑' m : ℕ, Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c) ≤
      (Real.log (c + 2) + 2) * (1 + 6 * Real.sqrt (2 * c)) := by
  have hc2 : (0 : ℝ) < 2 * c := by linarith
  have hC0 : (0 : ℝ) ≤ Real.log (c + 2) + 2 := by
    have : (0 : ℝ) ≤ Real.log (c + 2) := by
      apply Real.log_nonneg
      linarith
    linarith
  have hle : ∀ m : ℕ, Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c) ≤
      (Real.log (c + 2) + 2) * Real.exp (-((m : ℝ) ^ 2) / (2 * c)) :=
    fun m => log_exp_sq_term hc
  have hR : Summable fun m : ℕ =>
      (Real.log (c + 2) + 2) * Real.exp (-((m : ℝ) ^ 2) / (2 * c)) :=
    (summable_exp_sq (2 * c) hc2).mul_left _
  have hnn : ∀ m : ℕ, (0 : ℝ) ≤ Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c) :=
    fun m => mul_nonneg (Real.log_natCast_nonneg m) (Real.exp_pos _).le
  have hL : Summable fun m : ℕ => Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c) :=
    Summable.of_nonneg_of_le hnn hle hR
  have hmain := Summable.tsum_le_tsum hle hL hR
  rw [tsum_mul_left] at hmain
  have h2 := mul_le_mul_of_nonneg_left (sum_exp_sq_le (2 * c) hc2) hC0
  linarith [hmain, h2]


/-- `∑_{m ≥ 1} q^m = q (1-q)⁻¹` for `0 ≤ q < 1`. -/
private theorem tsum_pos_geometric {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    ∑' m : ℕ, (if m = 0 then (0 : ℝ) else q ^ m) = q * (1 - q)⁻¹ := by
  have hA : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one h0 h1
  have hB : Summable fun m : ℕ => (if m = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun m hm => by
      have : m ≠ 0 := by simpa using hm
      simp [this])
  have hsplit : (fun m : ℕ => (if m = 0 then (0 : ℝ) else q ^ m)) =
      fun m : ℕ => q ^ m - (if m = 0 then (1 : ℝ) else 0) := by
    funext m
    by_cases h : m = 0
    · subst h; simp
    · simp [h]
  rw [hsplit, Summable.tsum_sub hA hB]
  have hB1 : ∑' m : ℕ, (if m = 0 then (1 : ℝ) else 0) = 1 := by
    rw [tsum_eq_sum (s := {0}) (fun m hm => by
      have : m ≠ 0 := by simpa using hm
      simp [this])]
    simp
  rw [tsum_geometric_of_lt_one h0 h1, hB1]
  field_simp
  ring

/-- `∑_{m ≥ 1} exp (-m²/c) ≤ 5 √c`. -/
private theorem sum_exp_sq_pos (c : ℝ) (hc : 0 < c) :
    ∑' m : ℕ, (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / c)) ≤
      5 * Real.sqrt c := by
  set s := Real.sqrt c with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc.le
  set K : ℕ := ⌊s⌋₊ + 1 with hK
  have hKs : s ≤ (K : ℝ) := by
    have h1 : s < (⌊s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one s
    have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
    rw [h2]; linarith
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h1 : (1 : ℕ) ≤ K := Nat.one_le_iff_ne_zero.mpr (by omega)
    exact_mod_cast h1
  by_cases hc1 : 1 ≤ c
  · set q : ℝ := Real.exp (-(K : ℝ) / c) with hq
    have hq0 : 0 < q := Real.exp_pos _
    have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by
      exact div_neg_of_neg_of_pos (by linarith) hc)
    have hle : ∀ m : ℕ, (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / c)) ≤
        (if m = 0 then (0 : ℝ) else if m < K then (1 : ℝ) else q ^ m) := by
      intro m
      by_cases hm : m = 0
      · simp [hm]
      · simp only [hm, if_false]
        by_cases hK' : m < K
        · rw [if_pos hK']
          refine Real.exp_le_one_iff.mpr ?_
          exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (m:ℝ)]) hc.le
        · rw [if_neg hK']
          have hmK : K ≤ m := Nat.le_of_not_lt hK'
          have hmR : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmK
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg (α := ℝ) m
          have hqeq : q ^ m = Real.exp (-((m : ℝ) * (K : ℝ)) / c) := by
            rw [hq, ← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
          rw [hqeq]
          apply Real.exp_le_exp.mpr
          have hsq_ge : ((m : ℝ)) ^ 2 ≥ (m : ℝ) * (K : ℝ) := by nlinarith
          rw [neg_div, neg_div, neg_le_neg_iff]
          exact div_le_div_of_nonneg_right hsq_ge hc.le
    have hzero : ∀ m : ℕ, m ∉ Finset.range K →
        (if m < K then (1 : ℝ) else 0) = 0 := by
      intro m hm
      have h : ¬ (m < K) := by simpa using hm
      simp [h]
    have hfin : Summable fun m : ℕ => (if m < K then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero hzero
    have hgeo : Summable fun m : ℕ => q ^ m := summable_geometric_of_lt_one hq0.le hq1
    have hpart2 : Summable fun m : ℕ => (if m < K then (0 : ℝ) else q ^ m) := by
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hgeo
      · by_cases hm : m < K
        · simp [hm]
        · simp only [hm, if_false]; exact pow_nonneg hq0.le m
      · by_cases hm : m < K
        · simp only [hm, if_true]; exact pow_nonneg hq0.le m
        · simp only [hm, if_false]; exact le_rfl
    have hsplitR : (fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m)) =
        fun m => (if m < K then (1 : ℝ) else 0) + (if m < K then (0 : ℝ) else q ^ m) := by
      funext m; by_cases hm : m < K <;> simp [hm]
    have hsumA : Summable fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m) := by
      rw [hsplitR]; exact hfin.add hpart2
    have hgsum : Summable fun m : ℕ =>
        (if m = 0 then (0 : ℝ) else if m < K then (1 : ℝ) else q ^ m) := by
      have hsp : (fun m : ℕ => (if m = 0 then (0 : ℝ) else if m < K then (1 : ℝ) else q ^ m)) =
          fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m) - (if m = 0 then (1 : ℝ) else 0) := by
        funext m
        by_cases hm : m = 0
        · subst hm; simp
        · by_cases hK' : m < K <;> simp [hm, hK']
      rw [hsp]
      exact hsumA.sub (summable_of_ne_finset_zero (s := {0}) (fun m hm => by
        have : m ≠ 0 := by simpa using hm
        simp [this]))
    have hL : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / c)) :=
      Summable.of_nonneg_of_le (fun m => by
        by_cases hm : m = 0
        · simp [hm]
        · simp only [hm, if_false]; exact (Real.exp_pos _).le) hle hgsum
    have hmain := Summable.tsum_le_tsum hle hL hgsum
    have hfins : Summable fun m : ℕ => (if m = 0 then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := {0}) (fun m hm => by
        have : m ≠ 0 := by simpa using hm
        simp [this])
    have hB1 : ∑' m : ℕ, (if m = 0 then (1 : ℝ) else 0) = 1 := by
      rw [tsum_eq_sum (s := {0}) (fun m hm => by
        have : m ≠ 0 := by simpa using hm
        simp [this])]
      simp
    have hB2 : ∑' m : ℕ, (if m < K then (0 : ℝ) else q ^ m) ≤ (1 - q)⁻¹ := by
      have h2 : ∑' m : ℕ, (if m < K then (0 : ℝ) else q ^ m) ≤ ∑' m : ℕ, q ^ m :=
        Summable.tsum_le_tsum (fun m => by
          by_cases hm : m < K
          · simp only [hm, if_true]; exact pow_nonneg hq0.le m
          · simp only [hm, if_false]; exact le_rfl) hpart2 hgeo
      rwa [tsum_geometric_of_lt_one hq0.le hq1] at h2
    have hA1 : ∑' m : ℕ, (if m < K then (1 : ℝ) else q ^ m) ≤ (K : ℝ) + (1 - q)⁻¹ := by
      rw [hsplitR, Summable.tsum_add hfin hpart2]
      rw [tsum_eq_sum (s := Finset.range K) hzero]
      have hKsum : (∑ b ∈ Finset.range K, (if b < K then (1 : ℝ) else 0)) = (K : ℝ) := by
        rw [Finset.sum_congr rfl (fun b hb => by rw [if_pos (Finset.mem_range.mp hb)])]
        simp
      rw [hKsum]
      linarith [hB2]
    have hval : ∑' m : ℕ, (if m = 0 then (0 : ℝ) else if m < K then (1 : ℝ) else q ^ m) ≤
        ((K : ℝ) - 1) + (1 - q)⁻¹ := by
      have hsp2 : (fun m : ℕ => (if m = 0 then (0 : ℝ) else if m < K then (1 : ℝ) else q ^ m)) =
          fun m : ℕ => (if m < K then (1 : ℝ) else q ^ m) - (if m = 0 then (1 : ℝ) else 0) := by
        funext m
        by_cases hm : m = 0
        · subst hm; simp
        · by_cases hK' : m < K <;> simp [hm, hK']
      rw [hsp2, Summable.tsum_sub hsumA hfins, hB1]
      linarith [hA1]
    have hmain2 : ∑' m : ℕ, (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / c)) ≤
        ((K : ℝ) - 1) + (1 - q)⁻¹ := hmain.trans hval
    have hKle : (K : ℝ) - 1 ≤ s := by
      have h1 : (⌊s⌋₊ : ℝ) ≤ s := Nat.floor_le hs0
      have h2 : (K : ℝ) = (⌊s⌋₊ : ℝ) + 1 := by rw [hK]; push_cast; ring
      rw [h2]; linarith
    have hqbound : (1 - q)⁻¹ ≤ 4 * s := by
      have hs1 : (1 : ℝ) ≤ s := Real.one_le_sqrt.mpr hc1
      have hsc : s ≤ c := by nlinarith [hs0, hs1, hs2]
      have hKc : (K : ℝ) ≤ 2 * c := by linarith
      have hsc' : s / c ≤ (K : ℝ) / c := div_le_div_of_nonneg_right hKs hc.le
      have hsb : s / (4 * c) ≤ (K : ℝ) / c / 4 := by
        have e1 : s / (4 * c) = (s / c) / 4 := by field_simp
        have e2 : s / c / 4 ≤ (K : ℝ) / c / 4 :=
          div_le_div_of_nonneg_right hsc' (by norm_num)
        linarith
      have ht0 : 0 ≤ (K : ℝ) / c := le_of_lt (by positivity)
      have ht2 : (K : ℝ) / c ≤ 2 := by
        rw [div_le_iff₀ hc]; linarith
      have hge := one_sub_exp_neg_ge_quarter ht0 ht2
      have h1q : s / (4 * c) ≤ 1 - Real.exp (-((K : ℝ) / c)) := by linarith
      have hqeq : q = Real.exp (-((K : ℝ) / c)) := by rw [hq]; congr 1; ring
      rw [hqeq]
      have hspos : (0 : ℝ) < s / (4 * c) := by
        apply div_pos _ (by positivity)
        rw [hs]; exact Real.sqrt_pos.mpr hc
      have hpos : (0 : ℝ) < 1 - Real.exp (-((K : ℝ) / c)) := by linarith
      rw [inv_le_iff_one_le_mul₀ hpos]
      have hmul := mul_le_mul_of_nonneg_left h1q (by positivity : (0 : ℝ) ≤ 4 * s)
      have hv : 4 * s * (s / (4 * c)) = 1 := by
        field_simp
        nlinarith [hs2]
      linarith
    linarith [hmain2, hKle, hqbound]
  · push_neg at hc1
    set r : ℝ := Real.exp (-(1 / c)) with hr
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by
      have : (0 : ℝ) < 1 / c := by positivity
      linarith)
    have hle : ∀ m : ℕ, (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / c)) ≤
        (if m = 0 then (0 : ℝ) else r ^ m) := by
      intro m
      by_cases hm : m = 0
      · simp [hm]
      · simp only [hm, if_false]
        rw [hr, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        push_cast
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg (α := ℝ) m
        have h1 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · subst h0; simp
          · have h2 : (1 : ℕ) ≤ m := h0
            have h3 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2
            nlinarith [h3, hm0]
        have hc' : -((m : ℝ) ^ 2) / c ≤ -(m : ℝ) / c :=
          div_le_div_of_nonneg_right (by linarith) hc.le
        have hrw : (m : ℝ) * (-(1 / c)) = -(m : ℝ) / c := by field_simp
        rw [hrw]
        linarith
    have hR : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else r ^ m) := by
      have hsp : (fun m : ℕ => (if m = 0 then (0 : ℝ) else r ^ m)) =
          fun m : ℕ => r ^ m - (if m = 0 then (1 : ℝ) else 0) := by
        funext m
        by_cases h : m = 0
        · subst h; simp
        · simp [h]
      rw [hsp]
      exact (summable_geometric_of_lt_one hr0.le hr1).sub
        (summable_of_ne_finset_zero (s := {0}) (fun m hm => by
          have : m ≠ 0 := by simpa using hm
          simp [this]))
    have hL : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / c)) :=
      Summable.of_nonneg_of_le (fun m => by
        by_cases hm : m = 0
        · simp [hm]
        · simp only [hm, if_false]; exact (Real.exp_pos _).le) hle hR
    have hmain := Summable.tsum_le_tsum hle hL hR
    rw [tsum_pos_geometric hr0.le hr1] at hmain
    have hsp : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hu2 : (1 / Real.sqrt c) ^ 2 = 1 / c := by
      rw [div_pow, Real.sq_sqrt hc.le]; norm_num
    have key1 : (1 / Real.sqrt c) * Real.exp (-((1 / Real.sqrt c) ^ 2)) ≤ 1 := by
      have hu : (0 : ℝ) < 1 / Real.sqrt c := by positivity
      have h1 : (1 / Real.sqrt c) ≤ Real.exp ((1 / Real.sqrt c) ^ 2) := by
        have := Real.add_one_le_exp ((1 / Real.sqrt c) ^ 2)
        nlinarith [hu, sq_nonneg (1 / Real.sqrt c)]
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-((1 / Real.sqrt c) ^ 2))).le
      have h3 : Real.exp ((1 / Real.sqrt c) ^ 2) *
          Real.exp (-((1 / Real.sqrt c) ^ 2)) = 1 := by
        rw [← Real.exp_add]; simp
      linarith
    have key : (1 / Real.sqrt c) * r ≤ 1 := by
      rw [hr, show -(1 / c) = -((1 / Real.sqrt c) ^ 2) by rw [hu2]]
      exact key1
    have hrc : r ≤ Real.sqrt c := by
      have e : Real.sqrt c * (1 / Real.sqrt c) = 1 := by field_simp
      nlinarith [key, hsp, e, hr0]
    have hre1 : r ≤ Real.exp (-1) := by
      rw [hr]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff, le_div_iff₀ hc]
      linarith
    have hexp1 : Real.exp (-1) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1
        linarith
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h2
    have hr12 : r ≤ 1 / 2 := hre1.trans hexp1
    have hp : (0 : ℝ) < 1 - r := by linarith
    have hinv : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hp]
      linarith
    have hfin : r * (1 - r)⁻¹ ≤ 5 * Real.sqrt c := by
      nlinarith [hrc, Real.sqrt_nonneg c, hr0]
    linarith

/-- `∑_{m ≥ 1} log m · exp (-m²/c) ≤ (log (c+2) + 2) · 5 √(2c)`. -/
private theorem sum_log_exp_sq_pos (c : ℝ) (hc : 0 < c) :
    ∑' m : ℕ, (if m = 0 then (0 : ℝ) else
        Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c)) ≤
      (Real.log (c + 2) + 2) * (5 * Real.sqrt (2 * c)) := by
  have hc2 : (0 : ℝ) < 2 * c := by linarith
  have hC0 : (0 : ℝ) ≤ Real.log (c + 2) + 2 := by
    have : (0 : ℝ) ≤ Real.log (c + 2) := by
      apply Real.log_nonneg
      linarith
    linarith
  have hle : ∀ m : ℕ, (if m = 0 then (0 : ℝ) else
      Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c)) ≤
      (Real.log (c + 2) + 2) * (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / (2 * c))) := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      exact log_exp_sq_term hc
  have hG : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / (2 * c))) := by
    have hsp : (fun m : ℕ => (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / (2 * c)))) =
        fun m : ℕ => Real.exp (-((m : ℝ) ^ 2) / (2 * c)) - (if m = 0 then (1 : ℝ) else 0) := by
      funext m
      by_cases h : m = 0
      · subst h; simp
      · simp [h]
    rw [hsp]
    exact (summable_exp_sq (2 * c) hc2).sub (summable_of_ne_finset_zero (s := {0}) (fun m hm => by
      have : m ≠ 0 := by simpa using hm
      simp [this]))
  have hR : Summable fun m : ℕ =>
      (Real.log (c + 2) + 2) * (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / (2 * c))) :=
    hG.mul_left _
  have hL : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else
      Real.log (m : ℝ) * Real.exp (-((m : ℝ) ^ 2) / c)) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) hle hR
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      exact mul_nonneg (Real.log_natCast_nonneg m) (Real.exp_pos _).le
  have hmain := Summable.tsum_le_tsum hle hL hR
  rw [tsum_mul_left] at hmain
  have h2 := mul_le_mul_of_nonneg_left (sum_exp_sq_pos (2 * c) hc2) hC0
  linarith [hmain, h2]

/-- The prime slice bound: `∑_{p prime} log p · exp (-p²/c) ≤ (log (c+2)+2) · 5 √(2c)`. -/
private theorem prime_slice_le (c : ℝ) (hc : 0 < c) :
    ∑' p : ℕ, (if p.Prime then Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / c) else 0) ≤
      (Real.log (c + 2) + 2) * (5 * Real.sqrt (2 * c)) := by
  have hC0 : (0 : ℝ) ≤ Real.log (c + 2) + 2 := by
    have : (0 : ℝ) ≤ Real.log (c + 2) := by
      apply Real.log_nonneg
      linarith
    linarith
  have hle : ∀ p : ℕ, (if p.Prime then
      Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / c) else 0) ≤
      (if p = 0 then (0 : ℝ) else Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / c)) := by
    intro p
    by_cases hp : p.Prime
    · have hp0 : p ≠ 0 := hp.ne_zero
      simp only [hp, if_true, hp0, if_false]
      exact le_rfl
    · simp only [hp, if_false]
      by_cases hp0 : p = 0
      · simp [hp0]
      · simp only [hp0, if_false]
        exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
  have hR : Summable fun p : ℕ => (if p = 0 then (0 : ℝ) else
      Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / c)) := by
    have hle' : ∀ p : ℕ, (if p = 0 then (0 : ℝ) else
        Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / c)) ≤
        (Real.log (c + 2) + 2) * (if p = 0 then (0 : ℝ) else Real.exp (-((p : ℝ) ^ 2) / (2 * c))) := by
      intro p
      by_cases hp0 : p = 0
      · simp [hp0]
      · simp only [hp0, if_false]
        exact log_exp_sq_term hc
    have hG : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else
        Real.exp (-((m : ℝ) ^ 2) / (2 * c))) := by
      have hsp : (fun m : ℕ => (if m = 0 then (0 : ℝ) else Real.exp (-((m : ℝ) ^ 2) / (2 * c)))) =
          fun m : ℕ => Real.exp (-((m : ℝ) ^ 2) / (2 * c)) - (if m = 0 then (1 : ℝ) else 0) := by
        funext m
        by_cases h : m = 0
        · subst h; simp
        · simp [h]
      rw [hsp]
      exact (summable_exp_sq (2 * c) (by linarith)).sub
        (summable_of_ne_finset_zero (s := {0}) (fun m hm => by
          have : m ≠ 0 := by simpa using hm
          simp [this]))
    exact Summable.of_nonneg_of_le (fun p => by
      by_cases hp0 : p = 0
      · simp [hp0]
      · simp only [hp0, if_false]
        exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le) hle' (hG.mul_left _)
  refine (Summable.tsum_le_tsum hle ?_ hR).trans (sum_log_exp_sq_pos c hc)
  refine Summable.of_nonneg_of_le (fun p => ?_) hle hR
  have h0 : (0 : ℝ) ≤ Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / c) :=
    mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
  by_cases hp : p.Prime
  · simpa [hp] using h0
  · simp [hp]



/-! ## Comparison of series over different index types -/

/-- Monotone comparison of nonnegative series along an injection. -/
private theorem tsum_le_tsum_of_inj {β α : Type*} {f : β → ℝ} {g : α → ℝ}
    (hf : ∀ b, 0 ≤ f b) (hg : ∀ a, 0 ≤ g a) (hgs : Summable g)
    (i : β → α) (hi : Function.Injective i) (hle : ∀ b, f b ≤ g (i b)) :
    ∑' b, f b ≤ ∑' a, g a := by
  classical
  refine Real.tsum_le_of_sum_le hf (fun s => ?_)
  calc ∑ b ∈ s, f b ≤ ∑ b ∈ s, g (i b) := Finset.sum_le_sum (fun b _ => hle b)
    _ = ∑ a ∈ s.image i, g a := (Finset.sum_image (fun a _ b _ h => hi h)).symm
    _ ≤ ∑' a, g a := hgs.sum_le_tsum _ (fun a _ => hg a)

private theorem sqrt_two_pow (j : ℕ) : Real.sqrt ((2 : ℝ) ^ j) = (Real.sqrt 2) ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- `√(A / 2^j) ≤ √A · (3/4)^j`. -/
private theorem sqrt_div_pow_le (A : ℝ) (hA : 0 ≤ A) (j : ℕ) :
    Real.sqrt (A / (2 : ℝ) ^ j) ≤ Real.sqrt A * (3 / 4) ^ j := by
  have h1 : Real.sqrt (A / (2 : ℝ) ^ j) = Real.sqrt A / Real.sqrt ((2 : ℝ) ^ j) :=
    Real.sqrt_div hA ((2 : ℝ) ^ j)
  have hs2 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h34 : (1 / Real.sqrt 2) ≤ 3 / 4 := by
    rw [div_le_iff₀ hs2pos]
    nlinarith [hs2, hs2pos]
  have hinv : (1 : ℝ) / Real.sqrt ((2 : ℝ) ^ j) ≤ (3 / 4) ^ j := by
    rw [sqrt_two_pow]
    have h1' : (1 : ℝ) / (Real.sqrt 2) ^ j = (1 / Real.sqrt 2) ^ j := by
      rw [div_pow]; norm_num
    rw [h1']
    exact pow_le_pow_left₀ (by positivity) h34 j
  rw [h1]
  calc Real.sqrt A / Real.sqrt ((2 : ℝ) ^ j)
      = Real.sqrt A * (1 / Real.sqrt ((2 : ℝ) ^ j)) := by ring
    _ ≤ Real.sqrt A * (3 / 4) ^ j :=
        mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg A)

/-- The prime slice at denominator `N / 2^j`. -/
private noncomputable def primeSlice (N j : ℕ) : ℝ :=
  ∑' p : ℕ, (if p.Prime then
    Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ j)) else 0)

private theorem primeSlice_nonneg (N j : ℕ) : 0 ≤ primeSlice N j :=
  tsum_nonneg (fun p => by
    by_cases hp : p.Prime
    · simp only [hp, if_true]
      exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
    · simp only [hp, if_false]; exact le_refl 0)

private theorem primeSlice_summable (N j : ℕ) (hN : 0 < N) :
    Summable fun p : ℕ => (if p.Prime then
      Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ j)) else 0) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hc : (0 : ℝ) < (N : ℝ) / (2 : ℝ) ^ j := by positivity
  have hle : ∀ p : ℕ, (if p.Prime then
      Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ j)) else 0) ≤
      (if p = 0 then (0 : ℝ) else
        Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ j))) := by
    intro p
    by_cases hp : p.Prime
    · have hp0 : p ≠ 0 := hp.ne_zero
      simp only [hp, if_true, hp0, if_false]
      exact le_rfl
    · simp only [hp, if_false]
      by_cases hp0 : p = 0
      · simp [hp0]
      · simp only [hp0, if_false]
        exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
  have hle' : ∀ p : ℕ, (if p = 0 then (0 : ℝ) else
      Real.log (p : ℝ) * Real.exp (-((p : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ j))) ≤
      (Real.log ((N : ℝ) / (2 : ℝ) ^ j + 2) + 2) *
        (if p = 0 then (0 : ℝ) else Real.exp (-((p : ℝ) ^ 2) / (2 * ((N : ℝ) / (2 : ℝ) ^ j)))) := by
    intro p
    by_cases hp0 : p = 0
    · simp [hp0]
    · simp only [hp0, if_false]
      exact log_exp_sq_term hc
  have hG : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else
      Real.exp (-((m : ℝ) ^ 2) / (2 * ((N : ℝ) / (2 : ℝ) ^ j)))) := by
    have h2c : (0 : ℝ) < 2 * ((N : ℝ) / (2 : ℝ) ^ j) := by positivity
    have hsp : (fun m : ℕ => (if m = 0 then (0 : ℝ) else
        Real.exp (-((m : ℝ) ^ 2) / (2 * ((N : ℝ) / (2 : ℝ) ^ j))))) =
        fun m : ℕ => Real.exp (-((m : ℝ) ^ 2) / (2 * ((N : ℝ) / (2 : ℝ) ^ j))) -
          (if m = 0 then (1 : ℝ) else 0) := by
      funext m
      by_cases h : m = 0
      · subst h; simp
      · simp [h]
    rw [hsp]
    exact (summable_exp_sq _ h2c).sub (summable_of_ne_finset_zero (s := {0}) (fun m hm => by
      have : m ≠ 0 := by simpa using hm
      simp [this]))
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => (hle p).trans (hle' p)) (hG.mul_left _)
  by_cases hp : p.Prime
  · simp only [hp, if_true]
    exact mul_nonneg (Real.log_natCast_nonneg p) (Real.exp_pos _).le
  · simp only [hp, if_false]
    exact le_rfl

private theorem primeSlice_le (N j : ℕ) (hN : 2 ≤ N) :
    primeSlice N j ≤
      (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hc : (0 : ℝ) < (N : ℝ) / (2 : ℝ) ^ j := by positivity
  have hmain := prime_slice_le ((N : ℝ) / (2 : ℝ) ^ j) hc
  have hsqrt : Real.sqrt (2 * ((N : ℝ) / (2 : ℝ) ^ j)) ≤
      Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j := by
    have he : (2 : ℝ) * ((N : ℝ) / (2 : ℝ) ^ j) = 2 * (N : ℝ) / (2 : ℝ) ^ j := by
      field_simp
    rw [he]
    exact sqrt_div_pow_le (2 * (N : ℝ)) (by positivity) j
  have hlog : Real.log ((N : ℝ) / (2 : ℝ) ^ j + 2) + 2 ≤ Real.log (N : ℝ) + 3 := by
    have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) j
    have h1' : (N : ℝ) / (2 : ℝ) ^ j ≤ (N : ℝ) := by
      rw [div_le_iff₀ h2]
      nlinarith [hNpos, hp1]
    have h1 : (N : ℝ) / (2 : ℝ) ^ j + 2 ≤ 2 * (N : ℝ) := by linarith
    have h2' : Real.log ((N : ℝ) / (2 : ℝ) ^ j + 2) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hC0 : (0 : ℝ) ≤ Real.log ((N : ℝ) / (2 : ℝ) ^ j + 2) + 2 := by
    have hpos : (0 : ℝ) < (N : ℝ) / (2 : ℝ) ^ j := hc
    have := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ j + 2 by linarith)
    linarith
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (2 * ((N : ℝ) / (2 : ℝ) ^ j)) := Real.sqrt_nonneg _
  calc primeSlice N j ≤ (Real.log ((N : ℝ) / (2 : ℝ) ^ j + 2) + 2) *
        (5 * Real.sqrt (2 * ((N : ℝ) / (2 : ℝ) ^ j))) := hmain
    _ ≤ (Real.log (N : ℝ) + 3) * (5 * (Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j)) := by
        have hA : 5 * Real.sqrt (2 * ((N : ℝ) / (2 : ℝ) ^ j)) ≤
            5 * (Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) :=
          mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        have hB : (0 : ℝ) ≤ 5 * (Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) := by positivity
        nlinarith [hA, hlog, hC0, hB, hsqrt0]
    _ = (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) := by ring


/-! ## The prime-power tail -/

/-- The prime-power tail of `Λ(n)e^{-n/N}` over proper prime powers is at most
`30 (log N + 3) √N`. -/
private theorem primePowerTail_le (N : ℕ) (hN : 2 ≤ N) :
    ∑' n : ℕ, (if IsPrimePow n ∧ ¬ n.Prime then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) ≤
      30 * (Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set G : ℕ × ℕ → ℝ := fun q => if q.2.Prime then
    Real.log (q.2 : ℝ) * Real.exp (-((q.2 : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ q.1)) else 0 with hGdef
  have hGnn : ∀ q : ℕ × ℕ, 0 ≤ G q := by
    intro q
    by_cases hq : q.2.Prime
    · simp only [hGdef, hq, if_true]
      exact mul_nonneg (Real.log_natCast_nonneg q.2) (Real.exp_pos _).le
    · simp only [hGdef, hq, if_false]; exact le_rfl
  -- summability of the slices
  have hslice_summable : Summable fun j : ℕ => primeSlice N j := by
    have hgeo : Summable fun j : ℕ => (3 / 4 : ℝ) ^ j :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hmaj : Summable fun j : ℕ =>
        (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) := by
      have h := hgeo.mul_left ((Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ))))
      refine h.congr (fun j => ?_)
      ring
    exact Summable.of_nonneg_of_le (primeSlice_nonneg N) (fun j => primeSlice_le N j hN) hmaj
  have hjs : ∑' j : ℕ, primeSlice N j ≤ 30 * (Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ) := by
    have hgeo : Summable fun j : ℕ => (3 / 4 : ℝ) ^ j :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hmaj : Summable fun j : ℕ =>
        (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) := by
      have h := hgeo.mul_left ((Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ))))
      refine h.congr (fun j => ?_)
      ring
    have h1 := hslice_summable.tsum_le_tsum (fun j => primeSlice_le N j hN) hmaj
    have h2 : ∑' j : ℕ, (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j) =
        (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ))) * 4 := by
      rw [show (fun j : ℕ => (Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)) * (3 / 4) ^ j))
          = fun j => ((Real.log (N : ℝ) + 3) * (5 * Real.sqrt (2 * (N : ℝ)))) * (3 / 4) ^ j by
        funext j; ring]
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3:ℝ)/4 < 1)]
      norm_num
    rw [h2] at h1
    have hsN : Real.sqrt (2 * (N : ℝ)) = Real.sqrt 2 * Real.sqrt (N : ℝ) :=
      Real.sqrt_mul (by norm_num) _
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      nlinarith [h]
    have hs2le : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [hsq2, Real.sqrt_nonneg 2]
    have hC0 : (0 : ℝ) ≤ Real.log (N : ℝ) + 3 := by
      have : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
      linarith
    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    rw [hsN] at h1
    have hprod : (0 : ℝ) ≤ (Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ) := mul_nonneg hC0 hsqrt0
    have e1 : (Real.log (N : ℝ) + 3) * (5 * (Real.sqrt 2 * Real.sqrt (N : ℝ))) * 4 =
        20 * Real.sqrt 2 * ((Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ)) := by ring
    rw [e1] at h1
    have hfin : 20 * Real.sqrt 2 * ((Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ)) ≤
        30 * ((Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ)) := by
      have hle : 20 * Real.sqrt 2 ≤ 30 := by nlinarith [hs2le]
      exact mul_le_mul_of_nonneg_right hle hprod
    have etgt : (30 : ℝ) * (Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ) =
        30 * ((Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ)) := by ring
    rw [etgt]
    linarith [h1, hfin]
  -- the box argument at the level of finite sets
  have hbox' : ∀ s : Finset (ℕ × ℕ), ∑ q ∈ s, G q ≤ ∑' j : ℕ, primeSlice N j := by
    intro s
    set J := s.image Prod.fst with hJ
    set P := s.image Prod.snd with hP
    have hsub : s ⊆ J ×ˢ P := by
      intro q hq
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
    have h1 : ∑ q ∈ s, G q ≤ ∑ q ∈ J ×ˢ P, G q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hGnn q)
    have h2 : ∑ q ∈ J ×ˢ P, G q = ∑ j ∈ J, ∑ p ∈ P, G (j, p) := Finset.sum_product ..
    have h3 : ∀ j ∈ J, ∑ p ∈ P, G (j, p) ≤ primeSlice N j := by
      intro j _
      have h := (primeSlice_summable N j (by omega)).sum_le_tsum P (fun p _ => hGnn (j, p))
      simp only [primeSlice, hGdef] at h ⊢
      exact h
    have h4 : ∑ j ∈ J, primeSlice N j ≤ ∑' j : ℕ, primeSlice N j :=
      hslice_summable.sum_le_tsum J (fun j _ => primeSlice_nonneg N j)
    calc ∑ q ∈ s, G q ≤ ∑ j ∈ J, ∑ p ∈ P, G (j, p) := by rw [← h2]; exact h1
      _ ≤ ∑ j ∈ J, primeSlice N j := Finset.sum_le_sum h3
      _ ≤ ∑' j : ℕ, primeSlice N j := h4
  have hGsum : Summable G := summable_of_sum_le hGnn hbox'
  have hbox : ∑' (q : ℕ × ℕ), G q ≤ ∑' j : ℕ, primeSlice N j :=
    Real.tsum_le_of_sum_le hGnn hbox'
  -- the injection from proper prime powers
  have htail_eq : ∑' n : ℕ, (if IsPrimePow n ∧ ¬ n.Prime then
      ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0)
      = ∑' (n : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime}),
          ArithmeticFunction.vonMangoldt (n : ℕ) * Real.exp (-((n : ℕ) : ℝ) / (N : ℝ)) := by
    have h1 := _root_.tsum_subtype {n : ℕ | IsPrimePow n ∧ ¬ n.Prime}
      (fun n => ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)))
    rw [h1]
    apply tsum_congr
    intro n
    by_cases h : IsPrimePow n ∧ ¬ n.Prime
    · simp only [h, if_true, Set.indicator, Set.mem_setOf_eq, if_pos]
    · simp only [h, if_false, Set.indicator, Set.mem_setOf_eq, if_neg (not_not.mpr h)]
  rw [htail_eq]
  have hinj : ∑' (n : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime}),
      ArithmeticFunction.vonMangoldt (n : ℕ) * Real.exp (-((n : ℕ) : ℝ) / (N : ℝ)) ≤
      ∑' (q : ℕ × ℕ), G q := by
    set pf : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime} → ℕ := fun n => Classical.choose n.2.1 with hpfdef
    set kf : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime} → ℕ :=
      fun n => Classical.choose (Classical.choose_spec n.2.1) with hkfdef
    have hspec : ∀ n : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime},
        (pf n).Prime ∧ 0 < kf n ∧ (pf n) ^ (kf n) = (n : ℕ) := by
      intro n
      have h1 : IsPrimePow (n : ℕ) := n.2.1
      have h2 := Classical.choose_spec h1
      exact ⟨Nat.prime_iff.mpr (Classical.choose_spec h2).1, (Classical.choose_spec h2).2.1,
        (Classical.choose_spec h2).2.2⟩
    have hk2 : ∀ n : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime}, 2 ≤ kf n := by
      intro n
      obtain ⟨hp, hk0, hpk⟩ := hspec n
      rcases Nat.lt_or_ge (kf n) 2 with h | h
      · have hk1 : kf n = 1 := by omega
        have hprime : (n : ℕ).Prime := by
          rw [← hpk, hk1, pow_one]; exact hp
        exact absurd hprime n.2.2
      · exact h
    set i : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime} → ℕ × ℕ := fun n => (kf n - 2, pf n) with hidef
    have hi : Function.Injective i := by
      intro a b hab
      have h1 : kf a - 2 = kf b - 2 := congrArg Prod.fst hab
      have h2 : pf a = pf b := congrArg Prod.snd hab
      have hk2a := hk2 a
      have hk2b := hk2 b
      have hkk : kf a = kf b := by omega
      have hpk_a : (pf a) ^ (kf a) = (a : ℕ) := (hspec a).2.2
      have hpk_b : (pf b) ^ (kf b) = (b : ℕ) := (hspec b).2.2
      have : (a : ℕ) = (b : ℕ) := by rw [← hpk_a, ← hpk_b, hkk, h2]
      exact Subtype.ext this
    have hle : ∀ n : {n : ℕ | IsPrimePow n ∧ ¬ n.Prime},
        ArithmeticFunction.vonMangoldt (n : ℕ) * Real.exp (-((n : ℕ) : ℝ) / (N : ℝ)) ≤ G (i n) := by
      intro n
      obtain ⟨hp, hk0, hpk⟩ := hspec n
      have hk2n := hk2 n
      have hkne : kf n ≠ 0 := by omega
      have hLam : ArithmeticFunction.vonMangoldt (n : ℕ) = Real.log (pf n) := by
        rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow hkne,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hp2 : 2 ≤ pf n := hp.two_le
      have hkey : ((pf n : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ (kf n - 2))
          ≤ ((pf n : ℝ) ^ (kf n)) / (N : ℝ) := by
        have h2j : (0 : ℝ) < (2 : ℝ) ^ (kf n - 2) := by positivity
        have hpR : (2 : ℝ) ≤ (pf n : ℝ) := by exact_mod_cast hp2
        have hpow : ((pf n : ℝ) ^ 2) * (2 : ℝ) ^ (kf n - 2) ≤ (pf n : ℝ) ^ (kf n) := by
          have hstep : (2 : ℝ) ^ (kf n - 2) ≤ (pf n : ℝ) ^ (kf n - 2) :=
            pow_le_pow_left₀ (by norm_num) hpR _
          have hpos2 : (0 : ℝ) < (pf n : ℝ) ^ 2 := by positivity
          have hsplit : (pf n : ℝ) ^ (kf n) = (pf n : ℝ) ^ 2 * (pf n : ℝ) ^ (kf n - 2) := by
            rw [← pow_add]
            congr 1
            omega
          rw [hsplit]
          exact mul_le_mul_of_nonneg_left hstep hpos2.le
        have hgoal : ((pf n : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ (kf n - 2)) =
            ((pf n : ℝ) ^ 2 * (2 : ℝ) ^ (kf n - 2)) / (N : ℝ) := by
          field_simp
        rw [hgoal]
        exact div_le_div_of_nonneg_right hpow hNpos.le
      have hexp_le : Real.exp (-((pf n : ℝ) ^ (kf n)) / (N : ℝ)) ≤
          Real.exp (-((pf n : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ (kf n - 2))) := by
        apply Real.exp_le_exp.mpr
        have h := neg_le_neg hkey
        simp only [neg_div]
        simpa using h
      have hlogp : (0 : ℝ) ≤ Real.log (pf n) := by
        apply Real.log_nonneg
        have h1 : (1 : ℝ) ≤ (pf n : ℝ) := by exact_mod_cast hp.one_le
        linarith
      have hnn : ((n : ℕ) : ℝ) = (pf n : ℝ) ^ (kf n) := by
        rw [← hpk]; push_cast; ring
      rw [hLam, hnn]
      have hGval : G (i n) = Real.log (pf n) *
          Real.exp (-((pf n : ℝ) ^ 2) / ((N : ℝ) / (2 : ℝ) ^ (kf n - 2))) := by
        simp only [hGdef, hidef, hp, if_true]
      rw [hGval]
      exact mul_le_mul_of_nonneg_left hexp_le hlogp
    exact tsum_le_tsum_of_inj (fun n => mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
      (Real.exp_pos _).le) hGnn hGsum i hi hle
  linarith [hbox, hjs, hinj]


/-! ## The mass of primes below a cutoff -/

private theorem primeSmall_le (N : ℕ) (hN : 0 < N) (c : ℝ) (hc0 : 0 ≤ c) :
    ∑' n : ℕ, (if n.Prime ∧ (n : ℝ) ≤ c then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) ≤
      (c + 1) * Real.log (c + 1) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set M := ⌊c⌋₊ + 1 with hM
  have hzero : ∀ n : ℕ, n ∉ Finset.range M →
      (if n.Prime ∧ (n : ℝ) ≤ c then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) = 0 := by
    intro n hn
    have h1 : ¬ (n < M) := by simpa using hn
    have hMn : (M : ℝ) ≤ (n : ℝ) := by
      have : M ≤ n := Nat.le_of_not_lt h1
      exact_mod_cast this
    have h3 : c < (M : ℝ) := by
      have hfl := Nat.lt_floor_add_one c
      rw [hM]
      push_cast
      linarith
    have h2 : c < (n : ℝ) := by linarith
    have hconj : ¬ (n.Prime ∧ (n : ℝ) ≤ c) := fun h => absurd h.2 (not_le.mpr h2)
    simp only [hconj, if_false]
  rw [tsum_eq_sum hzero]
  have hsum : ∑ n ∈ Finset.range M, (if n.Prime ∧ (n : ℝ) ≤ c then
      ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) ≤
      ∑ _n ∈ Finset.range M, Real.log (c + 1) := by
    apply Finset.sum_le_sum
    intro n _
    by_cases h : n.Prime ∧ (n : ℝ) ≤ c
    · simp only [h, if_true]
      have hLam : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      have hnN : (n : ℝ) ≤ c + 1 := by linarith [h.2]
      have hlog : Real.log (n : ℝ) ≤ Real.log (c + 1) := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0
          simp only [Nat.cast_zero, Real.log_zero]
          apply Real.log_nonneg
          linarith
        · exact Real.log_le_log (by exact_mod_cast h0) hnN
      have hlogN : (0 : ℝ) ≤ Real.log (c + 1) := by
        apply Real.log_nonneg
        linarith
      have hexp1 : Real.exp (-(n : ℝ) / (N : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hNpos.le
      have hexp0 : (0 : ℝ) < Real.exp (-(n : ℝ) / (N : ℝ)) := Real.exp_pos _
      calc ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ))
          ≤ Real.log (c + 1) * 1 :=
            mul_le_mul (hLam.trans hlog) hexp1 hexp0.le hlogN
        _ = Real.log (c + 1) := by ring
    · simp only [h, if_false]
      apply Real.log_nonneg
      linarith
  refine hsum.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMle : (M : ℝ) ≤ c + 1 := by
    have hfl : (⌊c⌋₊ : ℝ) ≤ c := Nat.floor_le hc0
    rw [hM]; push_cast; linarith
  have hlogN : (0 : ℝ) ≤ Real.log (c + 1) := by
    apply Real.log_nonneg
    linarith
  calc (M : ℝ) * Real.log (c + 1) ≤ (c + 1) * Real.log (c + 1) :=
        mul_le_mul_of_nonneg_right hMle hlogN


/-! ## The residue expansion as a single series -/

/-- The summand of the residue tails. -/
private noncomputable def tailTerm (N : ℕ) (z : ℝ) (n : ℕ) : ℂ :=
  ((Real.log n * Real.exp (-(n : ℝ) / (N : ℝ)) : ℝ) : ℂ) * ee (-(n : ℝ) * z)

private theorem norm_tailTerm (N : ℕ) (z : ℝ) (n : ℕ) :
    ‖tailTerm N z n‖ = Real.log n * Real.exp (-(n : ℝ) / (N : ℝ)) := by
  rw [tailTerm, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.log_natCast_nonneg n) (Real.exp_pos _).le)]

private theorem tailTerm_nonneg (N : ℕ) (z : ℝ) (n : ℕ) :
    (0 : ℝ) ≤ Real.log n * Real.exp (-(n : ℝ) / (N : ℝ)) :=
  mul_nonneg (Real.log_natCast_nonneg n) (Real.exp_pos _).le

private theorem exp_decay_summable (N : ℕ) (hN : 0 < N) :
    Summable fun n : ℕ => (Real.exp (-(1 / (2 * (N : ℝ))))) ^ n := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr ?_)
  have hpos : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  linarith

private theorem norm_tailTerm_le (N : ℕ) (hN : 0 < N) (z : ℝ) (n : ℕ) :
    ‖tailTerm N z n‖ ≤
      (Real.log ((N : ℝ) + 2) + 2) * (Real.exp (-(1 / (2 * (N : ℝ))))) ^ n := by
  rw [norm_tailTerm]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hC0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) + 2 := by
    have : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    linarith
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, Real.log_zero, zero_mul, pow_zero, mul_one]
    exact hC0
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h0
    have h1 := log_mul_exp_le (x := (n : ℝ)) (c := (N : ℝ)) hn hNpos
    have h2 : Real.exp (-((n : ℝ) / (2 * (N : ℝ)))) =
        (Real.exp (-(1 / (2 * (N : ℝ))))) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h2] at h1
    rw [show -(↑n / (N : ℝ)) = -↑n / (N : ℝ) by ring] at h1
    exact h1

private theorem summable_tailTerm_ind (N : ℕ) (hN : 0 < N) (z : ℝ) (P : ℕ → Prop)
    [DecidablePred P] :
    Summable fun n : ℕ => if P n then tailTerm N z n else 0 := by
  classical
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => (Real.log ((N : ℝ) + 2) + 2) * (Real.exp (-(1 / (2 * (N : ℝ))))) ^ n)
    ((exp_decay_summable N hN).mul_left _) (fun n => ?_)
  by_cases hP : P n
  · rw [if_pos hP]; exact norm_tailTerm_le N hN z n
  · rw [if_neg hP, norm_zero]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hC0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) + 2 := by
      have : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
        apply Real.log_nonneg
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      linarith
    positivity

/-- The residue expansion regrouped by residue class: one series over `n`. -/
private theorem residueExpansion_eq (N q a : ℕ) (hN : 0 < N) (hq : 0 < q) (z : ℝ) :
    residueExpansion N q a z = ∑' n : ℕ,
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q then
        tailTerm N z n * ee (-((a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ))) else 0) := by
  classical
  set F : Finset ℕ := (Finset.range q).filter (fun l => Nat.Coprime l q) with hF
  have hres : residueExpansion N q a z =
      ∑ l ∈ F, ee (-((a : ℝ) * l / q)) * residueTail N q l z := by
    simp only [residueExpansion, hF]
  -- each inner series is summable
  have hterm : ∀ l ∈ F, Summable fun n : ℕ => ee (-((a : ℝ) * l / q)) *
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0) := by
    intro l _
    refine Summable.of_norm_bounded (E := ℂ)
      (g := fun n : ℕ => (Real.log ((N : ℝ) + 2) + 2) * (Real.exp (-(1 / (2 * (N : ℝ))))) ^ n)
      ((exp_decay_summable N hN).mul_left _) (fun n => ?_)
    by_cases hc : n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q
    · rw [if_pos hc, norm_mul, norm_ee, one_mul]
      exact norm_tailTerm_le N hN z n
    · rw [if_neg hc, mul_zero, norm_zero]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hC0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) + 2 := by
        have : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
          apply Real.log_nonneg
          have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        linarith
      positivity

  have hstep1 : ∑' n : ℕ, ∑ l ∈ F, ee (-((a : ℝ) * l / q)) *
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0)
      = ∑ l ∈ F, ∑' n : ℕ, ee (-((a : ℝ) * l / q)) *
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0) :=
    Summable.tsum_finsetSum hterm
  have hstep2 : ∑ l ∈ F, ∑' n : ℕ, ee (-((a : ℝ) * l / q)) *
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0)
      = ∑ l ∈ F, ee (-((a : ℝ) * l / q)) * residueTail N q l z := by
    apply Finset.sum_congr rfl
    intro l _
    rw [tsum_mul_left]
    rfl
  have hpoint : ∀ n : ℕ, ∑ l ∈ F, ee (-((a : ℝ) * l / q)) *
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0)
      = (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q then
        tailTerm N z n * ee (-((a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ))) else 0) := by
    intro n
    by_cases hn : n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ)
    · have hite : ∀ l ∈ F, ee (-((a : ℝ) * l / q)) *
          (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0)
          = (if n % q = l then ee (-((a : ℝ) * l / q)) * tailTerm N z n else 0) := by
        intro l hl
        have hlr : l % q = l := by
          have := (Finset.mem_filter.mp (by rw [← hF]; exact hl)).1
          exact Nat.mod_eq_of_lt (Finset.mem_range.mp this)
        by_cases hcl : n % q = l
        · have hcond : n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q :=
            ⟨hn.1, hn.2, by rw [hlr]; exact hcl⟩
          rw [if_pos hcond, if_pos hcl]
        · have hcond : ¬ (n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q) := by
            intro hc
            exact hcl (by rw [← hlr]; exact hc.2.2)
          rw [if_neg hcond, if_neg hcl, mul_zero]
      rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq]
      by_cases hcop : Nat.Coprime (n % q) q
      · have hmem : n % q ∈ F := by
          rw [hF]
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hq), hcop⟩
        rw [if_pos hmem, if_pos ⟨hn.1, hn.2, hcop⟩, mul_comm]
      · have hmem : n % q ∉ F := by
          rw [hF]
          intro hcon
          exact hcop (Finset.mem_filter.mp hcon).2
        rw [if_neg hmem, if_neg (fun h => hcop h.2.2)]
    · have hzero : ∀ l ∈ F, ee (-((a : ℝ) * l / q)) *
          (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q then tailTerm N z n else 0) = 0 := by
        intro l _
        have hnot : ¬ (n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ n % q = l % q) :=
          fun hc => hn ⟨hc.1, hc.2.1⟩
        rw [if_neg hnot, mul_zero]
      rw [Finset.sum_eq_zero hzero]
      rw [if_neg (fun h => hn ⟨h.1, h.2.1⟩)]
  rw [hres]
  rw [← hstep2]
  rw [← hstep1]
  exact tsum_congr hpoint


/-! ## The termwise comparison -/

private theorem ee_int (k : ℤ) : ee (k : ℝ) = 1 := by
  unfold ee
  convert Complex.exp_int_mul_two_pi_mul_I k using 1 <;> push_cast <;> ring

/-- For a prime `n` larger than `q`, the residue `n % q` is coprime to `q`. -/
private theorem prime_coprime_mod (n q : ℕ) (hn : n.Prime) (hq : 0 < q) (hqn : q < n) :
    Nat.Coprime (n % q) q := by
  show Nat.gcd (n % q) q = 1
  rw [← Nat.gcd_rec q n, Nat.gcd_comm q n]
  rcases hn.eq_one_or_self_of_dvd (Nat.gcd n q) (Nat.gcd_dvd_left n q) with h | h
  · exact h
  · exfalso
    have hd : n ∣ q := h ▸ Nat.gcd_dvd_right n q
    have hle := Nat.le_of_dvd hq hd
    omega

/-- The `n`-th term of `SZ` at a major arc equals the residue-expansion term. -/
private theorem szTerm_eq (N q a : ℕ) (hq : 0 < q) (z : ℝ) {n : ℕ} (hn : n.Prime) :
    (aZ N n : ℂ) * ee ((n : ℝ) * -((a : ℝ) / (q : ℝ) + z)) =
      tailTerm N z n * ee (-((a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq' : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hcast : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + ((n % q : ℕ) : ℝ) := by
    have hd := Nat.div_add_mod n q
    have h' : ((q * (n / q) + n % q : ℕ) : ℝ) = (n : ℝ) := by rw [hd]
    push_cast at h'
    linarith
  have hd : (n : ℝ) * ((a : ℝ) / (q : ℝ)) - (a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ) =
      (a : ℝ) * ((n / q : ℕ) : ℝ) := by
    field_simp
    nlinarith [hcast]
  have hkey : -((n : ℝ) * ((a : ℝ) / (q : ℝ))) =
      -((a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ)) + (-((a : ℝ) * ((n / q : ℕ) : ℝ))) := by
    linarith [hd]
  have hint : ee (-((a : ℝ) * ((n / q : ℕ) : ℝ))) = 1 := by
    set k : ℤ := -(a : ℤ) * ((n / q : ℕ) : ℤ) with hkdef
    have harg : (-((a : ℝ) * ((n / q : ℕ) : ℝ))) = (k : ℝ) := by
      rw [hkdef]
      push_cast
      rw [← Int.natCast_div]
      simp only [Int.cast_natCast]
      ring
    rw [harg]
    exact ee_int k
  have hsplit : (n : ℝ) * -((a : ℝ) / (q : ℝ) + z) =
      -((n : ℝ) * ((a : ℝ) / (q : ℝ))) + (-(n : ℝ)) * z := by ring
  rw [hsplit, ee_add, hkey, ee_add, hint, mul_one]
  simp only [aZ, tailTerm, ArithmeticFunction.vonMangoldt_apply_prime hn]
  ring


/-- Pointwise comparison of the `SZ` summand with the residue-expansion summand. -/
private theorem szTerm_diff_le (N q a : ℕ) (hq : 0 < q) (z : ℝ) (n : ℕ) :
    ‖(aZ N n : ℂ) * ee ((n : ℝ) * -((a : ℝ) / (q : ℝ) + z)) -
      (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q then
        tailTerm N z n * ee (-((a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ))) else 0)‖ ≤
      (if n.Prime ∧ (n : ℝ) ≤ Real.sqrt (N : ℝ) then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) +
      (if IsPrimePow n ∧ ¬ n.Prime then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) +
      (if n.Prime ∧ ¬ Nat.Coprime (n % q) q then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) := by
  have key : ‖(aZ N n : ℂ) * ee ((n : ℝ) * -((a : ℝ) / (q : ℝ) + z))‖ =
      ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) := by
    rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (aZ_nonneg N n)]
    rfl
  have hb0 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) :=
    aZ_nonneg N n
  by_cases hn : n.Prime
  · by_cases hbig : Real.sqrt (N : ℝ) < (n : ℝ)
    · by_cases hcop : Nat.Coprime (n % q) q
      · have hcond : n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q :=
          ⟨hn, hbig, hcop⟩
        rw [if_pos hcond, szTerm_eq N q a hq z hn, sub_self, norm_zero]
        have h1 : ¬ (n.Prime ∧ (n : ℝ) ≤ Real.sqrt (N : ℝ)) :=
          fun h => absurd h.2 (not_le.mpr hbig)
        have h2 : ¬ (IsPrimePow n ∧ ¬ n.Prime) := fun h => h.2 hn
        have h3 : ¬ (n.Prime ∧ ¬ Nat.Coprime (n % q) q) := fun h => h.2 hcop
        rw [if_neg h1, if_neg h2, if_neg h3]
        simp
      · have hcond : ¬ (n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q) :=
          fun h => hcop h.2.2
        rw [if_neg hcond, sub_zero, key]
        have h1 : ¬ (n.Prime ∧ (n : ℝ) ≤ Real.sqrt (N : ℝ)) :=
          fun h => absurd h.2 (not_le.mpr hbig)
        have h2 : ¬ (IsPrimePow n ∧ ¬ n.Prime) := fun h => h.2 hn
        rw [if_neg h1, if_neg h2, if_pos ⟨hn, hcop⟩]
        linarith
    · have hbig' : (n : ℝ) ≤ Real.sqrt (N : ℝ) := not_lt.mp hbig
      have hcond : ¬ (n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q) :=
        fun h => hbig h.2.1
      rw [if_neg hcond, sub_zero, key]
      have h2 : ¬ (IsPrimePow n ∧ ¬ n.Prime) := fun h => h.2 hn
      rw [if_pos ⟨hn, hbig'⟩, if_neg h2]
      by_cases hcop : Nat.Coprime (n % q) q
      · rw [if_neg (fun h : n.Prime ∧ ¬ Nat.Coprime (n % q) q => h.2 hcop)]
        linarith
      · rw [if_pos ⟨hn, hcop⟩]
        linarith
  · have hcond : ¬ (n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q) :=
      fun h => hn h.1
    by_cases hLam : ArithmeticFunction.vonMangoldt n = 0
    · have hF0 : (aZ N n : ℂ) * ee ((n : ℝ) * -((a : ℝ) / (q : ℝ) + z)) = 0 := by
        rw [aZ, hLam]
        simp
      rw [if_neg hcond, hF0, sub_zero, norm_zero]
      have h1 : ¬ (n.Prime ∧ (n : ℝ) ≤ Real.sqrt (N : ℝ)) := fun h => hn h.1
      have h2 : ¬ (IsPrimePow n ∧ ¬ n.Prime) := fun h =>
        (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr h.1) hLam
      have h3 : ¬ (n.Prime ∧ ¬ Nat.Coprime (n % q) q) := fun h => hn h.1
      rw [if_neg h1, if_neg h2, if_neg h3]
      simp
    · rw [if_neg hcond, sub_zero, key]
      have hpp : IsPrimePow n := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLam
      have h1 : ¬ (n.Prime ∧ (n : ℝ) ≤ Real.sqrt (N : ℝ)) := fun h => hn h.1
      rw [if_neg h1, if_pos ⟨hpp, hn⟩]
      have h3 : ¬ (n.Prime ∧ ¬ Nat.Coprime (n % q) q) := fun h => hn h.1
      rw [if_neg h3]
      linarith


private theorem summable_ind_aZ (N : ℕ) (hN : 0 < N) (P : ℕ → Prop) [DecidablePred P] :
    Summable fun n : ℕ => (if P n then
      ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_aZ hN)
  · by_cases h : P n
    · rw [if_pos h]
      exact aZ_nonneg N n
    · rw [if_neg h]
  · by_cases h : P n
    · rw [if_pos h]
      exact le_rfl
    · rw [if_neg h]
      exact aZ_nonneg N n

/-- A prime not coprime to `q` modulo `q` is at most `q`. -/
private theorem prime_le_of_not_coprime (n q : ℕ) (hn : n.Prime) (hq : 0 < q)
    (h : ¬ Nat.Coprime (n % q) q) : n ≤ q := by
  have hgcd : Nat.gcd (n % q) q ≠ 1 := h
  have hgpos : 0 < Nat.gcd (n % q) q :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) hq
  obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hgcd
  have hgEq : Nat.gcd (n % q) q = Nat.gcd n q := by
    rw [← Nat.gcd_rec q n, Nat.gcd_comm q n]
  have hrd' : r ∣ Nat.gcd n q := hgEq ▸ hrd
  have hrn : r ∣ n := hrd'.trans (Nat.gcd_dvd_left n q)
  have hrq : r ∣ q := hrd'.trans (Nat.gcd_dvd_right n q)
  have hrn_eq : r = n := by
    rcases hn.eq_one_or_self_of_dvd r hrn with h1 | h1
    · rw [h1] at hrp
      exact absurd hrp (by decide)
    · exact h1
  rw [← hrn_eq]
  exact Nat.le_of_dvd hq hrq

/-- The difference of `SZ` at a major arc and the residue expansion. -/
private theorem sz_diff_le (N : ℕ) (hN : 2 ≤ N) (q a : ℕ) (hq : 0 < q)
    (hqarc : q ≤ arcCutoff N) (z : ℝ) :
    ‖SZ N (-((a : ℝ) / (q : ℝ) + z)) - residueExpansion N q a z‖ ≤
      (Real.sqrt (N : ℝ) + 1) * Real.log (Real.sqrt (N : ℝ) + 1) +
      30 * (Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ) +
      ((arcCutoff N : ℝ) + 1) * Real.log ((arcCutoff N : ℝ) + 1) := by
  classical
  have hN0 : 0 < N := by omega
  set f : ℕ → ℂ := fun n => (aZ N n : ℂ) * ee ((n : ℝ) * -((a : ℝ) / (q : ℝ) + z)) with hf
  set G : ℕ → ℂ := fun n => (if n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧
    Nat.Coprime (n % q) q then
      tailTerm N z n * ee (-((a : ℝ) * ((n % q : ℕ) : ℝ) / (q : ℝ))) else 0) with hG
  have hSZ : SZ N (-((a : ℝ) / (q : ℝ) + z)) = ∑' n : ℕ, f n := rfl
  have hRE : residueExpansion N q a z = ∑' n : ℕ, G n := residueExpansion_eq N q a hN0 hq z
  have hfs : Summable f := summable_term hN0 _
  have hGs : Summable G := by
    rw [hG]
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => (Real.log ((N : ℝ) + 2) + 2) * (Real.exp (-(1 / (2 * (N : ℝ))))) ^ n)
      ((exp_decay_summable N hN0).mul_left _) (fun n => ?_)
    by_cases h : n.Prime ∧ Real.sqrt (N : ℝ) < (n : ℝ) ∧ Nat.Coprime (n % q) q
    · rw [if_pos h, norm_mul, norm_ee, mul_one]
      exact norm_tailTerm_le N hN0 z n
    · rw [if_neg h, norm_zero]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
      have hC0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) + 2 := by
        have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
          Real.log_nonneg (by linarith)
        linarith
      positivity
  -- the three error terms
  set B1 : ℕ → ℝ := fun n => (if n.Prime ∧ (n : ℝ) ≤ Real.sqrt (N : ℝ) then
    ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) with hB1
  set B2 : ℕ → ℝ := fun n => (if IsPrimePow n ∧ ¬ n.Prime then
    ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) with hB2
  set B3 : ℕ → ℝ := fun n => (if n.Prime ∧ ¬ Nat.Coprime (n % q) q then
    ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) with hB3
  have hB1s : Summable B1 := summable_ind_aZ N hN0 _
  have hB2s : Summable B2 := summable_ind_aZ N hN0 _
  have hB3s : Summable B3 := summable_ind_aZ N hN0 _
  -- pointwise bound
  have hpt : ∀ n : ℕ, ‖f n - G n‖ ≤ B1 n + B2 n + B3 n := by
    intro n
    have := szTerm_diff_le N q a hq z n
    rw [hf, hG, hB1, hB2, hB3]
    exact this
  -- summability of the difference and of its norm
  have hdiff : Summable fun n : ℕ => f n - G n := hfs.sub hGs
  have hdiffnorm : Summable fun n : ℕ => ‖f n - G n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt ?_
    exact (hB1s.add hB2s).add hB3s
  rw [hSZ, hRE, ← Summable.tsum_sub hfs hGs]
  refine (norm_tsum_le_tsum_norm hdiffnorm).trans ?_
  have hsum3 : ∑' n : ℕ, (B1 n + B2 n + B3 n) =
      (∑' n : ℕ, B1 n) + (∑' n : ℕ, B2 n) + (∑' n : ℕ, B3 n) := by
    rw [Summable.tsum_add (hB1s.add hB2s) hB3s, Summable.tsum_add hB1s hB2s]
  have hstep : ∑' n : ℕ, ‖f n - G n‖ ≤
      (∑' n : ℕ, B1 n) + (∑' n : ℕ, B2 n) + (∑' n : ℕ, B3 n) := by
    rw [← hsum3]
    exact Summable.tsum_le_tsum hpt hdiffnorm ((hB1s.add hB2s).add hB3s)
  -- bounds for the three pieces
  have hbound1 : ∑' n : ℕ, B1 n ≤
      (Real.sqrt (N : ℝ) + 1) * Real.log (Real.sqrt (N : ℝ) + 1) := by
    rw [hB1]
    exact primeSmall_le N hN0 (Real.sqrt (N : ℝ)) (Real.sqrt_nonneg _)
  have hbound2 : ∑' n : ℕ, B2 n ≤ 30 * (Real.log (N : ℝ) + 3) * Real.sqrt (N : ℝ) := by
    rw [hB2]
    exact primePowerTail_le N hN
  have hbound3 : ∑' n : ℕ, B3 n ≤
      ((arcCutoff N : ℝ) + 1) * Real.log ((arcCutoff N : ℝ) + 1) := by
    rw [hB3]
    have hle : ∀ n : ℕ, (if n.Prime ∧ ¬ Nat.Coprime (n % q) q then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) ≤
        (if n.Prime ∧ (n : ℝ) ≤ (arcCutoff N : ℝ) then
        ArithmeticFunction.vonMangoldt n * Real.exp (-(n : ℝ) / (N : ℝ)) else 0) := by
      intro n
      by_cases h : n.Prime ∧ ¬ Nat.Coprime (n % q) q
      · have hnle : n ≤ q := prime_le_of_not_coprime n q h.1 hq h.2
        have harc : n ≤ arcCutoff N := le_trans hnle hqarc
        rw [if_pos h]
        rw [if_pos ⟨h.1, by exact_mod_cast harc⟩]
      · rw [if_neg h]
        by_cases h' : n.Prime ∧ (n : ℝ) ≤ (arcCutoff N : ℝ)
        · rw [if_pos h']
          exact aZ_nonneg N n
        · rw [if_neg h']
    refine (Summable.tsum_le_tsum hle (summable_ind_aZ N hN0 _)
      (summable_ind_aZ N hN0 _)).trans ?_
    exact primeSmall_le N hN0 ((arcCutoff N : ℝ)) (Nat.cast_nonneg _)
  linarith [hstep, hbound1, hbound2, hbound3]


/-! ## The leaf -/

private theorem rpow_quarter_ge (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    (120 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  have h1 : ((((10 : ℝ) ^ 20)) : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have h2 : ((((10 : ℝ) ^ 20)) : ℝ) ^ (1 / 4 : ℝ) = 100000 := by
    have hb : (0 : ℝ) ≤ (10 : ℝ) := by norm_num
    rw [← Real.rpow_natCast ((10 : ℝ)) 20, ← Real.rpow_mul hb]
    have h3 : ((↑(20 : ℕ) : ℝ) * (1 / 4 : ℝ)) = (5 : ℝ) := by norm_num
    rw [h3, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  linarith

private theorem sqrt_eq_rpow_half (N : ℕ) :
    Real.sqrt (N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]

private theorem log_le_sqrt_div (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    Real.log (N : ℝ) ≤ Real.sqrt (N : ℝ) / 30 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [hN]
  have hA : Real.log (N : ℝ) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (x := (N : ℝ)) (ε := (1 / 4 : ℝ)) hNpos.le (by norm_num)
    have he : (N : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      field_simp
    linarith [h, he]
  have hB : (120 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := rpow_quarter_ge N hN
  have hq0 : (0 : ℝ) < (N : ℝ) ^ (1 / 4 : ℝ) := by
    have : (0:ℝ) < (120:ℝ) := by norm_num
    linarith
  have hsplit : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hs : Real.sqrt (N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := sqrt_eq_rpow_half N
  rw [hs, hsplit]
  have h4 : 4 * (N : ℝ) ^ (1 / 4 : ℝ) ≤
      (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) / 30 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 30)]
    nlinarith [hB, hq0]
  linarith [hA, h4]

private theorem log_sq_le_sqrt (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    Real.log (N : ℝ) ^ 2 ≤ 16 * Real.sqrt (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [hN]
  have hA : Real.log (N : ℝ) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (x := (N : ℝ)) (ε := (1 / 4 : ℝ)) hNpos.le (by norm_num)
    have he : (N : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      field_simp
    linarith [h, he]
  have hlog0 : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg N
    linarith
  have h4 : (0 : ℝ) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have hq : (0:ℝ) < (N:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hNpos _
    linarith
  have hsq : Real.log (N : ℝ) ^ 2 ≤ (4 * (N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
    nlinarith [hA, hlog0, h4]
  have hval : (4 * (N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
      16 * Real.sqrt (N : ℝ) := by
    have hsplit : (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    rw [sqrt_eq_rpow_half, hsplit]
    ring
  linarith [hsq, hval]

private theorem sqrt_large (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) : (100 : ℝ) ≤ Real.sqrt (N : ℝ) :=
  (Real.le_sqrt (by norm_num) (by nlinarith [hN])).mpr (by nlinarith [hN])

/-- The leaf, proved. -/
private theorem prime_reduction_proof (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z‖ ≤
      Real.sqrt N * Real.log N ^ 2 := by
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqarc : q ≤ arcCutoff N := (Finset.mem_Icc.mp hq).2
  have hN2 : 2 ≤ N := by
    have h2 : (2 : ℝ) ≤ (N : ℝ) := by nlinarith [hN]
    exact_mod_cast h2
  have hNpos : (0 : ℝ) < (N : ℝ) := by nlinarith [hN]
  have hdiff := sz_diff_le N hN2 q a hq0 hqarc z
  set x := Real.log (N : ℝ) with hx
  set s := Real.sqrt (N : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hssq : s ^ 2 = (N : ℝ) := by
    rw [hsdef]; exact Real.sq_sqrt hNpos.le
  have hxs : x ≤ s / 30 := log_le_sqrt_div N hN
  have hx46 : 46 ≤ x := log_1e20_ge.trans (Real.log_le_log (by positivity) hN)
  have hx2 : x ^ 2 ≤ 16 * s := log_sq_le_sqrt N hN
  -- bound `log (arcCutoff N + 1)` by `x`
  have harc : (arcCutoff N : ℝ) ≤ 1.1 * x ^ 2 := by
    have h1 : (arcCutoff N : ℝ) ≤ 1.1 * Real.log (N : ℝ) ^ 2 :=
      Nat.floor_le (by positivity)
    rw [hx]; exact h1
  have hlogarc : Real.log ((arcCutoff N : ℝ) + 1) ≤ x := by
    apply Real.log_le_log (by positivity)
    -- arcCutoff N + 1 ≤ N
    have h2 : 1.1 * x ^ 2 + 1 ≤ (N : ℝ) := by
      nlinarith [hx2, sqrt_large N hN, hNpos, hssq, hs0]
    linarith
  -- bound `log (sqrt N + 1)` by `x/2 + 1`
  have hlogsqrt : Real.log (s + 1) ≤ x / 2 + 1 := by
    have hs1 : s + 1 ≤ 2 * s := by linarith [sqrt_large N hN]
    have h1 : Real.log (s + 1) ≤ Real.log (2 * s) := Real.log_le_log (by linarith) hs1
    have h2 : Real.log (2 * s) = Real.log 2 + Real.log s :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log s = x / 2 := by
      rw [hsdef, sqrt_eq_rpow_half, Real.log_rpow hNpos]
      rw [hx]
      ring
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  -- assemble the numbers
  have hT1 : (s + 1) * Real.log (s + 1) ≤ s * (x + 2) := by
    have hs1 : 1 ≤ s := by linarith [sqrt_large N hN]
    have h1 : s + 1 ≤ 2 * s := by linarith
    nlinarith [hlogsqrt, hs0, hs1, hx46, mul_le_mul_of_nonneg_left hlogsqrt (by linarith : (0:ℝ) ≤ s + 1)]
  have hT3 : ((arcCutoff N : ℝ) + 1) * Real.log ((arcCutoff N : ℝ) + 1) ≤ s * x ^ 2 / 10 := by
    have h1 : ((arcCutoff N : ℝ) + 1) * Real.log ((arcCutoff N : ℝ) + 1) ≤
        (1.1 * x ^ 2 + 1) * x := by
      apply mul_le_mul (by linarith [harc]) hlogarc (Real.log_nonneg (by linarith)) (by positivity)
    have h2 : (1.1 * x ^ 2 + 1) * x ≤ s * x ^ 2 / 10 := by
      have h3 : x ≤ s / 30 := hxs
      nlinarith [h3, hs0, hx46, sq_nonneg x, sq_nonneg (x ^ 2)]
    linarith
  have hnum : (s + 1) * Real.log (s + 1) + 30 * (x + 3) * s +
      ((arcCutoff N : ℝ) + 1) * Real.log ((arcCutoff N : ℝ) + 1) ≤ s * x ^ 2 := by
    have hbr : (x + 2) + 30 * (x + 3) + x ^ 2 / 10 ≤ x ^ 2 := by nlinarith [hx46]
    have hstep : s * ((x + 2) + 30 * (x + 3) + x ^ 2 / 10) ≤ s * x ^ 2 :=
      mul_le_mul_of_nonneg_left hbr hs0
    have heq : s * ((x + 2) + 30 * (x + 3) + x ^ 2 / 10) =
        s * (x + 2) + 30 * (x + 3) * s + s * x ^ 2 / 10 := by ring
    linarith [hT1, hT3, hstep, heq]
  rw [hx, hsdef] at hnum ⊢
  linarith [hdiff, hnum]


/-- LEAF. Display 3.1, page 349, prime power and small prime reduction.
The larger remainder sqrt N times log squared N is a supporting variant of the printed
sqrt N remainder. The cited Lemma31Input is unchanged. -/
theorem prime_reduction (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z‖ ≤
      Real.sqrt N * Real.log N ^ 2 := by
  exact prime_reduction_proof N hN q hq a ha hac z hz

/-- LEAF. Displays 3.2 to 3.4, pages 349 to 351, and the Ramanujan identity on page 351.
Partial summation from Proposition 1.4 and the two integrated remainders give this bound.
The constant 3.8 leaves room above the displayed 2.99, 0.14 and 0.001 estimates.
BLOCKED FREE-ms-leanstral task90: requires GRH-based prime sum estimates (weighted partial summation,
explicit formula remainder bounds) not available in Mathlib. The lab's DERZ1997 namespace defines
GRH but provides no lemmas about prime sums under GRH. Depends on lemma12_T, lemma12_zero,
lemma13_explicit_budget, and prop14_error_bound from State1546, all of which have open sorries.
Searches ran: LeanSearch, Loogle, Mathlib docs. -/
theorem residue_integral_approximation (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (hG : LeanLab.DERZ1997.GRH)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖residueExpansion N q a z -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ ≤
        3.8 * lemma31Base N q := by
  sorry

/-- LEAF. Page 352, the conclusion of displays 3.1 to 3.4 and the Ramanujan identity.
This analytic leaf includes partial summation from Proposition 1.4, pages 349 to 351.
CONDITIONAL ON the unproved analytic estimates. -/
theorem continuous_approximation (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (hG : LeanLab.DERZ1997.GRH)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (a : ℕ) (ha : a ∈ Finset.range q) (hac : Nat.Coprime a q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖SZ N (-((a : ℝ) / q + z)) -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ ≤
        3.9 * lemma31Base N q := by
  have hlog : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  have hb : Real.sqrt N * Real.log N ^ 2 ≤ 0.1 * lemma31Base N q := by
    have hφ : (0 : ℝ) ≤ Nat.totient q := Nat.cast_nonneg _
    have hp := Real.pi_gt_three
    have hf : 10 ≤ (Nat.totient q : ℝ) + 4 * Real.pi * Real.log N := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hf
      (show 0 ≤ Real.sqrt N * Real.log N ^ 2 by positivity)
    unfold lemma31Base
    nlinarith
  calc
    _ ≤ ‖SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z‖ +
        ‖residueExpansion N q a z -
          (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ :=
      by
        have he : SZ N (-((a : ℝ) / q + z)) -
            (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z =
            (SZ N (-((a : ℝ) / q + z)) - residueExpansion N q a z) +
            (residueExpansion N q a z -
              (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z) := by ring
        rw [he]
        exact norm_add_le _ _
    _ ≤ Real.sqrt N * Real.log N ^ 2 + 3.8 * lemma31Base N q :=
      add_le_add (prime_reduction N hN q hq a ha hac z hz)
        (residue_integral_approximation N hN hG q hq a ha hac z hz)
    _ ≤ _ := by linarith

/-- LEAF. Page 352, the final integral to geometric series comparison. -/
theorem continuous_model_error (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : q ∈ Finset.Icc 1 (arcCutoff N))
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖continuousModel N z - modelSum N (-z)‖ ≤ 4 := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  have hn : (0 : ℝ) < N := by linarith
  have hn' : 0 < N := by exact_mod_cast hn
  have hxre : x.re = 1 / (N : ℝ) := by simp [x]
  have hxpos : 0 < x.re := by rw [hxre]; positivity
  have hx : x ≠ 0 := by intro h; rw [h] at hxpos; simpa using hxpos
  have hsmall : ‖x‖ ≤ 1 / 2 :=
    major_arc_exponent_small N hN q (Finset.mem_Icc.mp hq).1 z hz
  have hrec := reciprocal_model_error x hx hsmall
  have hmodel : modelSum N (-z) = Complex.exp (-3 * x) / (1 - Complex.exp (-x)) := by
    rw [modelSum_geometric N hn', ratio_eq_exp]
    change Complex.exp (-x) ^ 3 / _ = _
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hexp : ‖Complex.exp (-3 * x)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    norm_num [Complex.mul_re, Complex.mul_im]
    linarith
  have he : continuousModel N z - modelSum N (-z) =
      Complex.exp (-3 * x) * (1 / x - 1 / (1 - Complex.exp (-x))) := by
    rw [hmodel]
    change Complex.exp (-3 * x) / x - _ = _
    ring
  rw [he, norm_mul]
  have : ‖Complex.exp (-3 * x)‖ * ‖1 / x - 1 / (1 - Complex.exp (-x))‖ ≤ 1 * 2 :=
    mul_le_mul hexp hrec (norm_nonneg _) (by norm_num)
  linarith

/-- LEAF. Page 352, scalar slack between 3.9 and 4 absorbs the model error. -/
theorem closing_budget (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) :
    3.9 * lemma31Base N q + 4 / (Nat.totient q : ℝ) ≤ 4 * lemma31Base N q := by
  have hn : (1 : ℝ) ≤ N := by linarith
  have hlog : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  have hs : 1 ≤ Real.sqrt N := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hφ : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hdiv : 4 / (Nat.totient q : ℝ) ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hb : 40 ≤ lemma31Base N q := by
    unfold lemma31Base
    have hfirst : 1 ≤ (Nat.totient q : ℝ) + 4 * Real.pi * Real.log N := by
      have := Real.pi_pos
      nlinarith
    have hprod : 1 ≤ ((Nat.totient q : ℝ) + 4 * Real.pi * Real.log N) * Real.sqrt N :=
      by nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ (Nat.totient q : ℝ) + 4 * Real.pi * Real.log N)]
    nlinarith [mul_le_mul_of_nonneg_right hprod (sq_nonneg (Real.log N))]
  linarith

/-- Lemma 3.1 assembled with exactly the existing cited Prop conclusion.
CONDITIONAL ON the analytic leaves. The assembly contains no sorry. -/
theorem lemma31 (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (hG : LeanLab.DERZ1997.GRH) : Lemma31Input N := by
  intro q hq a ha hac z hz
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hdiff := continuous_model_error N hN q hq z hz
  have hcoef := norm_moebius_ratio q hq0
  have he : SZ N (-((a : ℝ) / q + z)) -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * modelSum N (-z) =
      (SZ N (-((a : ℝ) / q + z)) -
        (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z) +
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) *
        (continuousModel N z - modelSum N (-z)) := by ring
  rw [he]
  refine (norm_add_le _ _).trans ((add_le_add
    (continuous_approximation N hN hG q hq a ha hac z hz) ?_).trans
      (closing_budget N hN q hq0))
  rw [norm_mul]
  calc
    _ ≤ (1 / (Nat.totient q : ℝ)) * 4 :=
      mul_le_mul hcoef hdiff (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A negative diagnostic for display 1.7 on page 338.
Replacing von Mangoldt by log n already exceeds the target at cutoff 11. -/
theorem log_majorant_exceeds_budget : (0.61 : ℝ) < ∑ n ∈ Finset.range 11, Real.log n / (n : ℝ) ^ 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := Real.log_four_eq
  have h6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h7 : Real.log (5 : ℝ) ≤ Real.log 7 := Real.log_le_log (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, h4, h6, h8, h9, Real.log_ten_eq]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]

end LeanLab.Zinoviev1997.Decomp120
