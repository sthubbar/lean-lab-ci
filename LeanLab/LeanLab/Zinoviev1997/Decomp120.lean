import LeanLab.Zinoviev1997.ArcArithmetic
import LeanLab.Zinoviev1997.ModelFormula
import LeanLab.Zinoviev1997.State1546
import LeanLab.Zinoviev1997.LocalBudgets
import LeanLab.PNTPort.Vinogradov.MajorArc

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

/-- Supporting range check for Proposition 1.4 in display 3.2 on page 349.
The modulus condition holds at every point above the prime tail cutoff. -/
theorem residue_modulus_range (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : q ≤ arcCutoff N) {u : ℝ} (hu : Real.sqrt N ≤ u) :
    (10 : ℝ) ^ 9 ≤ u ∧ (q : ℝ) ≤ u ^ (0.37 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  have hbase : (46 : ℝ) ^ 2 < (1 / 1.1) * Real.exp (0.185 * 46) := by
    have he : (2.7182818283 : ℝ) ^ 8 < Real.exp 8 := by
      have hh := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num)
        (by norm_num : (8 : ℕ) ≠ 0)
      simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hh
    have he' : Real.exp 8 ≤ Real.exp (0.185 * 46) := Real.exp_le_exp.mpr (by norm_num)
    have hn : (46 : ℝ) ^ 2 < (1 / 1.1) * (2.7182818283 : ℝ) ^ 8 := by norm_num
    linarith
  have hpow := power_exp_extend 2 46 0.185 (1 / 1.1) (Real.log N)
    (by norm_num) hL (by norm_num) hbase
  have hcut : (arcCutoff N : ℝ) ≤ 1.1 * Real.log N ^ 2 := Nat.floor_le (by positivity)
  have hqR : (q : ℝ) ≤ (arcCutoff N : ℝ) := by exact_mod_cast hq
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqrt : (10 : ℝ) ^ 10 ≤ Real.sqrt N :=
    (Real.le_sqrt (by positivity) hNpos.le).mpr (by nlinarith [hN])
  refine ⟨by linarith, ?_⟩
  have heq : (Real.sqrt (N : ℝ)) ^ (0.37 : ℝ) = Real.exp (0.185 * Real.log N) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le, Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  have hqu : (q : ℝ) ≤ (Real.sqrt (N : ℝ)) ^ (0.37 : ℝ) := by
    rw [heq]
    linarith
  exact hqu.trans (Real.rpow_le_rpow hs.le hu (by norm_num))

/-- The Abel weight in display 3.2 on page 349. -/
noncomputable def residueWeight (x : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-x * u) * (Real.log u : ℂ)

/-- The derivative of the Abel weight used in display 3.3 on page 350. -/
theorem residueWeight_hasDerivAt (x : ℂ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (residueWeight x)
      (Complex.exp (-x * u) * ((1 / u : ℝ) - x * (Real.log u : ℂ))) u := by
  have he := ((Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-x)).cexp
  have hl := (Real.hasDerivAt_log hu).ofReal_comp
  convert he.mul hl using 1
  · funext v
    simp [residueWeight]
  · simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, one_div]
    ring


/-- The pointwise derivative estimate following display 3.3 on page 350. -/
theorem residueWeight_deriv_norm (x : ℂ) {u : ℝ} (hu : 1 ≤ u) :
    ‖deriv (residueWeight x) u‖ ≤
      (1 / u + ‖x‖ * Real.log u) * Real.exp (-x.re * u) := by
  have hu0 : 0 < u := by linarith
  rw [(residueWeight_hasDerivAt x hu0.ne').deriv, norm_mul, Complex.norm_exp]
  have hr : (-x * (u : ℂ)).re = -x.re * u := by simp
  rw [hr]
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have hn : ‖((1 / u : ℝ) : ℂ) - x * (Real.log u : ℂ)‖ ≤
      1 / u + ‖x‖ * Real.log u := by
    calc
      _ ≤ ‖((1 / u : ℝ) : ℂ)‖ + ‖x * (Real.log u : ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0.le,
        abs_of_nonneg hlog]
  exact (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le).trans_eq (mul_comm _ _)


/-- Abel summation for the prime progression count in display 3.2 on pages 349 to 350.
Both endpoint terms are retained. -/
theorem residue_finite_abel (x : ℂ) (q l : ℕ) {A B : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
      if n.Prime ∧ n % q = l % q then residueWeight x n else 0) =
      residueWeight x B * (State1546.piMod B q l : ℂ) -
      residueWeight x A * (State1546.piMod A q l : ℂ) -
      ∫ u in Set.Ioc A B, deriv (residueWeight x) u * (State1546.piMod u q l : ℂ) := by
  classical
  let c : ℕ → ℂ := fun n => if n.Prime ∧ n % q = l % q then 1 else 0
  have hsum : ∀ u : ℝ, (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, c n) =
      (State1546.piMod u q l : ℂ) := by
    intro u
    simp only [c, State1546.piMod, Finset.Iic_eq_Icc]
    simp
  have hd : ∀ u ∈ Set.Icc A B, HasDerivAt (residueWeight x)
      (Complex.exp (-x * u) * ((1 / u : ℝ) - x * (Real.log u : ℂ))) u := by
    intro u hu
    exact residueWeight_hasDerivAt x (by linarith [hu.1])
  have hc : ContinuousOn (fun u : ℝ => Complex.exp (-x * u) *
      ((1 / u : ℝ) - x * (Real.log u : ℂ))) (Set.Icc A B) := by
    have h0 : ∀ u ∈ Set.Icc A B, u ≠ 0 := by intro u hu; linarith [hu.1]
    have hlog : ContinuousOn (fun u : ℝ => (Real.log u : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono (by
        intro u hu
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using h0 u hu))
    have hinv : ContinuousOn (fun u : ℝ => ((1 / u : ℝ) : ℂ)) (Set.Icc A B) :=
      Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.div continuousOn_id h0)
    exact (Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul Complex.continuous_ofReal.continuousOn)).mul
        (hinv.sub (continuousOn_const.mul hlog))
  have hab := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ A) hAB
    (fun u hu => (hd u hu).differentiableAt)
    (hc.integrableOn_Icc.congr_fun (fun u hu => (hd u hu).deriv.symm) measurableSet_Icc)
  simp_rw [hsum] at hab
  convert hab using 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [c]
  split_ifs <;> simp


/-- The upper endpoint term in Abel summation vanishes as stated on page 350. -/
theorem residue_boundary_tendsto (x : ℂ) (hx : 0 < x.re) (q l : ℕ) :
    Filter.Tendsto (fun u : ℝ => residueWeight x u * (State1546.piMod u q l : ℂ))
      Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun u : ℝ => 2 * (u ^ 2 * Real.exp (-x.re * u)))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_ofNat, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 x.re hx).const_mul 2
  apply squeeze_zero_norm' _ ht
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u hu
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlog : Real.log u ≤ u := by linarith [Real.log_le_sub_one_of_pos hu0]
  have hpi : ‖(State1546.piMod u q l : ℂ)‖ ≤ 2 * u := by
    rw [Complex.norm_natCast]
    have hc : State1546.piMod u q l ≤ ⌊u⌋₊ + 1 := by
      unfold State1546.piMod
      exact (Finset.card_filter_le _ _).trans_eq (Nat.card_Iic _)
    have hc' : (State1546.piMod u q l : ℝ) ≤ (⌊u⌋₊ : ℝ) + 1 := by exact_mod_cast hc
    linarith [Nat.floor_le hu0.le]
  have hn : ‖residueWeight x u‖ = Real.exp (-x.re * u) * Real.log u := by
    rw [residueWeight, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog0]
    simp
  rw [norm_mul, hn]
  calc
    _ ≤ (Real.exp (-x.re * u) * u) * (2 * u) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le) hpi
        (norm_nonneg _) (by positivity)
    _ = _ := by ring


/-- The continuous model is the improper integral on page 352. -/
theorem continuousModel_integral (N : ℕ) (hN : 0 < N) (z : ℝ) :
    (∫ u in Set.Ioi (3 : ℝ), Complex.exp
      (-((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z)) * u)) =
      continuousModel N z := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < x.re := by simp [x]; positivity
  have hh := integral_exp_mul_complex_Ioi (a := -x) (by simpa using hx) (3 : ℝ)
  change (∫ u in Set.Ioi (3 : ℝ), Complex.exp (-x * u)) = Complex.exp (-3 * x) / x
  rw [hh]
  norm_num only [Complex.ofReal_ofNat]
  have he : -x * (3 : ℂ) = -3 * x := by ring
  rw [he, div_neg, neg_div, neg_neg]


/-- Corrected increment form of the progression estimate used on page 349.
CONDITIONAL ON the explicit Proposition 1.4 error bound at every valid argument.
The lower endpoint main term is subtracted along with the lower endpoint count. -/
theorem residue_count_increment_bound (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q l : ℕ) (hq : q ≤ arcCutoff N)
    (hcount : ∀ {t : ℝ}, (10 : ℝ) ^ 9 ≤ t → (q : ℝ) ≤ t ^ (0.37 : ℝ) →
      |(State1546.piMod t q l : ℝ) - State1546.zinLi t / (Nat.totient q : ℝ)| ≤
        1.3 * Real.sqrt t * Real.log t + 10 ^ 8)
    {u : ℝ} (hu : Real.sqrt N ≤ u) :
    |((State1546.piMod u q l : ℝ) - State1546.piMod (Real.sqrt N) q l) -
      (State1546.zinLi u - State1546.zinLi (Real.sqrt N)) / (Nat.totient q : ℝ)| ≤
        2.6 * Real.sqrt u * Real.log u + 2 * 10 ^ 8 := by
  obtain ⟨hA9, hqA⟩ := residue_modulus_range N hN q hq (u := Real.sqrt N) le_rfl
  obtain ⟨hu9, hqu⟩ := residue_modulus_range N hN q hq hu
  have hEA := hcount hA9 hqA
  have hEu := hcount hu9 hqu
  have hlogA : 0 ≤ Real.log (Real.sqrt N) := Real.log_nonneg (by linarith)
  have hlogu : Real.log (Real.sqrt N) ≤ Real.log u :=
    Real.log_le_log (by linarith) hu
  have hsqrtu : Real.sqrt (Real.sqrt N) ≤ Real.sqrt u := Real.sqrt_le_sqrt hu
  have hmon : Real.sqrt (Real.sqrt N) * Real.log (Real.sqrt N) ≤
      Real.sqrt u * Real.log u :=
    mul_le_mul hsqrtu hlogu hlogA (Real.sqrt_nonneg _)
  have heq : ((State1546.piMod u q l : ℝ) - State1546.piMod (Real.sqrt N) q l) -
      (State1546.zinLi u - State1546.zinLi (Real.sqrt N)) / (Nat.totient q : ℝ) =
      ((State1546.piMod u q l : ℝ) - State1546.zinLi u / (Nat.totient q : ℝ)) -
      ((State1546.piMod (Real.sqrt N) q l : ℝ) -
        State1546.zinLi (Real.sqrt N) / (Nat.totient q : ℝ)) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)


/-- The reflected Fourier sign of the Ramanujan identity on page 351. -/
theorem residue_phase_sum (q a : ℕ) (hq : 0 < q) (hac : Nat.Coprime a q) :
    (∑ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
      ee (-((a : ℝ) * l / q))) = (μ q : ℂ) := by
  have hc : IsCoprime (-(a : ℤ)) (q : ℤ) := by
    exact (show IsCoprime (a : ℤ) (q : ℤ) by exact_mod_cast hac.isCoprime).neg_left
  have hh := LeanLab.PNTPort.Vinogradov.ramanujan_coprime (by omega : 1 ≤ q) hc
  convert hh using 1
  apply Finset.sum_congr rfl
  intro l hl
  unfold ee LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring


/-- The residue aggregation step of Lemma 3.1 on pages 351 to 352.
CONDITIONAL ON the stated uniform error for each reduced residue tail. -/
theorem residueExpansion_error_of_tail (N q a : ℕ) (hq : 0 < q)
    (hac : Nat.Coprime a q) (z E : ℝ)
    (hE : ∀ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
      ‖residueTail N q l z - continuousModel N z / (Nat.totient q : ℂ)‖ ≤ E) :
    ‖residueExpansion N q a z -
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z‖ ≤
        (Nat.totient q : ℝ) * E := by
  classical
  have hcard : ((Finset.range q).filter (fun l => Nat.Coprime l q)).card = Nat.totient q := by
    simpa only [Nat.coprime_comm] using (Nat.totient_eq_card_coprime q).symm
  have hmain : (∑ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
      ee (-((a : ℝ) * l / q)) * (continuousModel N z / (Nat.totient q : ℂ))) =
      (((μ q : ℝ) / Nat.totient q : ℝ) : ℂ) * continuousModel N z := by
    rw [← Finset.sum_mul, residue_phase_sum q a hq hac]
    push_cast
    ring
  rw [residueExpansion, ← hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
        ‖ee (-((a : ℝ) * l / q)) * residueTail N q l z -
          ee (-((a : ℝ) * l / q)) * (continuousModel N z / (Nat.totient q : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q), E := by
      apply Finset.sum_le_sum
      intro l hl
      rw [← mul_sub, norm_mul, norm_ee, one_mul]
      exact hE l hl
    _ = _ := by simp [hcard, mul_comm]


/-- A polynomial envelope for the first integral of display 3.4 on page 350. -/
theorem residue_log_square_envelope {N u : ℝ} (hN : 1 ≤ N) (hu : 1 ≤ u) :
    Real.sqrt u * Real.log u ^ 2 ≤
      Real.sqrt N / 2 * (1 + u / N) * (Real.log N + u / N) ^ 2 := by
  have hNpos : 0 < N := by linarith
  have hupos : 0 < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlog : Real.log u ≤ Real.log N + u / N := by
    have hh := Real.log_le_sub_one_of_pos (div_pos hupos hNpos)
    rw [Real.log_div hupos.ne' hNpos.ne'] at hh
    linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsU : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hs : Real.sqrt u ≤ Real.sqrt N / 2 * (1 + u / N) := by
    have hsN2 := Real.sq_sqrt hNpos.le
    have hsU2 := Real.sq_sqrt hupos.le
    have hh : 2 * Real.sqrt u * Real.sqrt N ≤ N + u := by
      nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt N)]
    have hdiv : Real.sqrt N / 2 * (1 + u / N) = (N + u) / (2 * Real.sqrt N) := by
      field_simp [hNpos.ne', hsN.ne']
      nlinarith [hsN2]
    rw [hdiv, le_div_iff₀ (by positivity)]
    nlinarith
  exact mul_le_mul hs (pow_le_pow_left₀ hlogu hlog 2) (sq_nonneg _) (by positivity)


/-- Integer Gamma moments for the polynomial envelope of display 3.4 on page 350. -/
theorem residue_exponential_moment (N : ℝ) (hN : 0 < N) (k : ℕ) :
    IntegrableOn (fun u : ℝ => (u / N) ^ k * Real.exp (-u / N)) (Set.Ioi 0) ∧
    (∫ u in Set.Ioi (0 : ℝ), (u / N) ^ k * Real.exp (-u / N)) = N * (k.factorial : ℝ) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
    (s := (k : ℝ)) (b := 1 / N) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k)) (by norm_num) (by positivity)
  have hbase : IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-u / N)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul, neg_div, one_div_mul_eq_div] using hi
  have he := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := ((k + 1 : ℕ) : ℝ))
    (r := 1 / N) (by positivity) (by positivity)
  have hsub : (((k + 1 : ℕ) : ℝ) - 1) = (k : ℝ) := by push_cast; ring
  have hgamma : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial k
  have he' : (∫ u in Set.Ioi (0 : ℝ), u ^ k * Real.exp (-u / N)) =
      N ^ (k + 1) * (k.factorial : ℝ) := by
    simp only [hsub, Real.rpow_natCast, one_div_one_div, hgamma] at he
    convert he using 1
    congr 1
    funext u
    congr 1
    ring
  have hf : (fun u : ℝ => (u / N) ^ k * Real.exp (-u / N)) =
      (fun u : ℝ => (u ^ k * Real.exp (-u / N)) / N ^ k) := by
    funext u
    ring
  rw [hf]
  refine ⟨hbase.div_const _, ?_⟩
  rw [integral_div, he', pow_succ]
  field_simp [hN.ne']


/-- The first integral bound used in display 3.4 on pages 350 to 351.
A polynomial envelope replaces the printed split at N. -/
theorem residue_log_square_integral (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    (∫ u in Set.Ioi (3 : ℝ), Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) ≤
      1.15 * (N : ℝ) * Real.sqrt N * Real.log N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hL : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  let g : ℕ → ℝ → ℝ := fun k u => (u / N) ^ k * Real.exp (-u / N)
  let c : ℕ → ℝ := fun k => if k = 0 then Real.sqrt N / 2 * Real.log N ^ 2
    else if k = 1 then Real.sqrt N / 2 * (Real.log N ^ 2 + 2 * Real.log N)
    else if k = 2 then Real.sqrt N / 2 * (2 * Real.log N + 1)
    else Real.sqrt N / 2
  let P : ℝ → ℝ := fun u => ∑ k ∈ Finset.range 4, c k * g k u
  have hgi : ∀ k : ℕ, IntegrableOn (g k) (Set.Ioi 0) :=
    fun k => (residue_exponential_moment N hNpos k).1
  have hPi : IntegrableOn P (Set.Ioi 0) := by
    exact integrable_finsetSum _ (fun k hk => (hgi k).const_mul _)
  have hPeq : ∀ u : ℝ, P u =
      Real.sqrt N / 2 * (1 + u / N) * (Real.log N + u / N) ^ 2 * Real.exp (-u / N) := by
    intro u
    simp [P, Finset.sum_range_succ, c, g]
    ring
  have hPnonneg : ∀ u : ℝ, 0 < u → 0 ≤ P u := by
    intro u hu
    rw [hPeq]
    positivity
  have hAE : ∀ᵐ u ∂volume.restrict (Set.Ioi (3 : ℝ)),
      ‖Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)‖ ≤ P u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_of_nonneg (by positivity), hPeq]
    exact mul_le_mul_of_nonneg_right (residue_log_square_envelope hN1 (by linarith [Set.mem_Ioi.mp hu]))
      (Real.exp_pos _).le
  have hP3 : IntegrableOn P (Set.Ioi (3 : ℝ)) := hPi.mono_set (by
    intro u hu
    exact lt_trans (by norm_num : (0 : ℝ) < 3) (Set.mem_Ioi.mp hu))
  have hfi : IntegrableOn (fun u : ℝ => Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N))
      (Set.Ioi (3 : ℝ)) := hP3.mono' (by fun_prop) hAE
  have hcomp : (∫ u in Set.Ioi (3 : ℝ), Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) ≤
      ∫ u in Set.Ioi (0 : ℝ), P u := by
    refine (integral_mono_ae hfi hP3 ?_).trans ?_
    · filter_upwards [hAE] with u hu
      exact (le_abs_self _).trans hu
    · apply setIntegral_mono_set hPi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hPnonneg u hu
      · exact ae_of_all _ (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 3) (Set.mem_Ioi.mp hu))
  have hInt : (∫ u in Set.Ioi (0 : ℝ), P u) =
      (N : ℝ) * Real.sqrt N * (Real.log N ^ 2 + 3 * Real.log N + 4) := by
    rw [show P = (fun u : ℝ => ∑ k ∈ Finset.range 4, c k * g k u) from rfl,
      integral_finsetSum _ (fun k hk => (hgi k).const_mul _)]
    simp_rw [integral_const_mul]
    have hm : ∀ k : ℕ, (∫ u in Set.Ioi (0 : ℝ), g k u) = (N : ℝ) * (k.factorial : ℝ) :=
      fun k => (residue_exponential_moment N hNpos k).2
    simp_rw [hm]
    simp [Finset.sum_range_succ, c]
    ring
  rw [hInt] at hcomp
  have hpoly : Real.log N ^ 2 + 3 * Real.log N + 4 ≤ 1.15 * Real.log N ^ 2 := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ (N : ℝ) * Real.sqrt N)
  nlinarith


/-- The second integral estimate in display 3.4 on pages 350 to 351.
The Gamma moments give a bound of square root pi times square root N times log N plus one half. -/
theorem residue_log_half_integral (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N) :
    (∫ u in Set.Ioi (3 : ℝ), Real.log u / Real.sqrt u * Real.exp (-u / N)) ≤
      0.05 * Real.sqrt N * Real.log N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  let J : ℝ → ℝ → ℝ := fun s u => u ^ s * Real.exp (-u / N)
  have hJi : ∀ s : ℝ, -1 < s → IntegrableOn (J s) (Set.Ioi 0) := by
    intro s hs
    simpa only [J, Real.rpow_one, neg_mul, neg_div, one_div_mul_eq_div] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := s)
        (b := 1 / (N : ℝ)) hs (by norm_num) (by positivity)
  have hJv : ∀ s : ℝ, -1 < s →
      (∫ u in Set.Ioi (0 : ℝ), J s u) = (N : ℝ) ^ (s + 1) * Real.Gamma (s + 1) := by
    intro s hs
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s + 1) (r := 1 / (N : ℝ))
      (by linarith) (by positivity)
    simp only [add_sub_cancel_right, one_div_one_div] at hh
    convert hh using 1
    congr 1
    funext u
    dsimp [J]
    congr 1
    ring
  let H : ℝ → ℝ := fun u => Real.log N * J (-1 / 2) u + (1 / (N : ℝ)) * J (1 / 2) u
  have hHi : IntegrableOn H (Set.Ioi 0) :=
    ((hJi (-1 / 2) (by norm_num)).const_mul _).add
      ((hJi (1 / 2) (by norm_num)).const_mul _)
  have hHeq : ∀ u : ℝ, 0 < u → H u =
      (Real.log N + u / N) / Real.sqrt u * Real.exp (-u / N) := by
    intro u hu
    have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
    have hs2 := Real.sq_sqrt hu.le
    dsimp only [H, J]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hu.le,
      ← Real.sqrt_eq_rpow]
    field_simp
    nlinarith [hs2]
  have hHnonneg : ∀ u : ℝ, 0 < u → 0 ≤ H u := by
    intro u hu
    rw [hHeq u hu]
    positivity
  have hAE : ∀ᵐ u ∂volume.restrict (Set.Ioi (3 : ℝ)),
      ‖Real.log u / Real.sqrt u * Real.exp (-u / N)‖ ≤ H u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu3 : 3 < u := hu
    have hu0 : 0 < u := by linarith
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hlog : Real.log u ≤ Real.log N + u / N := by
      have hh := Real.log_le_sub_one_of_pos (div_pos hu0 hNpos)
      rw [Real.log_div hu0.ne' hNpos.ne'] at hh
      linarith
    rw [Real.norm_of_nonneg (by positivity), hHeq u hu0]
    gcongr
  have hH3 : IntegrableOn H (Set.Ioi (3 : ℝ)) :=
    hHi.mono_set (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 3) hu)
  have hfi : IntegrableOn (fun u : ℝ => Real.log u / Real.sqrt u * Real.exp (-u / N))
      (Set.Ioi (3 : ℝ)) := hH3.mono' (by fun_prop) hAE
  have hcomp : (∫ u in Set.Ioi (3 : ℝ), Real.log u / Real.sqrt u * Real.exp (-u / N)) ≤
      ∫ u in Set.Ioi (0 : ℝ), H u := by
    refine (integral_mono_ae hfi hH3 ?_).trans ?_
    · filter_upwards [hAE] with u hu
      exact (le_abs_self _).trans hu
    · apply setIntegral_mono_set hHi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hHnonneg u hu
      · exact ae_of_all _ (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 3) hu)
  have hgamma : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    ring
  have hp1 : (N : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt N := by rw [Real.sqrt_eq_rpow]
  have hp3 : (N : ℝ) ^ (3 / 2 : ℝ) = N * Real.sqrt N := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hNpos, Real.rpow_one, hp1]
  have hInt : (∫ u in Set.Ioi (0 : ℝ), H u) =
      Real.sqrt N * Real.sqrt Real.pi * (Real.log N + 1 / 2) := by
    rw [show H = (fun u => Real.log N * J (-1 / 2) u + (1 / (N : ℝ)) * J (1 / 2) u) from rfl,
      integral_add ((hJi (-1 / 2) (by norm_num)).const_mul _)
        ((hJi (1 / 2) (by norm_num)).const_mul _)]
    simp_rw [integral_const_mul]
    rw [hJv (-1 / 2) (by norm_num), hJv (1 / 2) (by norm_num)]
    norm_num only [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
    rw [Real.Gamma_one_half_eq, hgamma, hp1, hp3]
    field_simp [hNpos.ne']
  rw [hInt] at hcomp
  have hpi : Real.sqrt Real.pi ≤ 2 := (Real.sqrt_le_iff).mpr
    ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
  have hpoly : 2 * (Real.log N + 1 / 2) ≤ 0.05 * Real.log N ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hpoly (Real.sqrt_nonneg (N : ℝ))
  have hh' := mul_le_mul_of_nonneg_left hpi
    (show 0 ≤ Real.sqrt N * (Real.log N + 1 / 2) by positivity)
  nlinarith


/-- Supporting diagnostic for the uncentered tail count printed on page 349.
At N equal to 10 to the twentieth power the tail count at its lower endpoint is zero.
Its difference from Li of the endpoint exceeds the printed error budget at q equal to one.
This does not refute Lemma 3.1 or the sealed approximation target. -/
theorem lower_cutoff_uncentered_error :
    2.6 * Real.sqrt ((10 : ℝ) ^ 10) * Real.log ((10 : ℝ) ^ 10) + 2 * 10 ^ 8 <
      |(0 : ℝ) - State1546.zinLi ((10 : ℝ) ^ 10)| := by
  have hlogpos : 0 < Real.log ((10 : ℝ) ^ 10) := Real.log_pos (by norm_num)
  have hlog : Real.log ((10 : ℝ) ^ 10) < 24 := by
    rw [Real.log_pow]
    have h10 : Real.log (10 : ℝ) < 2.4 := by
      rw [Real.log_ten_eq]
      linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hs : Real.sqrt ((10 : ℝ) ^ 10) = 100000 := by norm_num
  have hdiv : (10 : ℝ) ^ 10 / 24 ≤ (10 : ℝ) ^ 10 / Real.log ((10 : ℝ) ^ 10) :=
    div_le_div_of_nonneg_left (by positivity) hlogpos hlog.le
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htwo : (2 : ℝ) / Real.log 2 ≤ 3 := by
    rw [div_le_iff₀ hlog2]
    linarith [Real.log_two_gt_d9]
  have hi : 0 ≤ ∫ u in (2 : ℝ)..((10 : ℝ) ^ 10), 1 / Real.log u ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (by intro u; positivity)
  have hli := State1546.zinLi_by_parts (x := (10 : ℝ) ^ 10) (by norm_num)
  norm_num only [show (10 : ℝ) ^ 10 = 10000000000 by norm_num,
    show (10 : ℝ) ^ 8 = 100000000 by norm_num] at *
  have hli0 : 0 < State1546.zinLi (10000000000 : ℝ) := by linarith
  rw [zero_sub, abs_neg, abs_of_pos hli0]
  linarith


/-- The logarithmic integral in the constant remainder after display 3.4 on page 351. -/
theorem residue_log_integral (N : ℝ) (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u / N)) (Set.Ioi 3) ∧
    (∫ u in Set.Ioi (3 : ℝ), Real.log u * Real.exp (-u / N)) ≤ N * (Real.log N + 1) := by
  have hNpos : 0 < N := by linarith
  let H : ℝ → ℝ := fun u => Real.log N * Real.exp (-u / N) + (u / N) * Real.exp (-u / N)
  have h0 : IntegrableOn (fun u : ℝ => Real.exp (-u / N)) (Set.Ioi 0) := by
    simpa using (residue_exponential_moment N hNpos 0).1
  have h1 : IntegrableOn (fun u : ℝ => (u / N) * Real.exp (-u / N)) (Set.Ioi 0) := by
    simpa using (residue_exponential_moment N hNpos 1).1
  have hHi : IntegrableOn H (Set.Ioi 0) := (h0.const_mul _).add h1
  have hHpos : ∀ u : ℝ, 0 < u → 0 ≤ H u := by
    intro u hu
    dsimp [H]
    exact add_nonneg (mul_nonneg (Real.log_nonneg hN) (Real.exp_pos _).le) (by positivity)
  have hAE : ∀ᵐ u ∂volume.restrict (Set.Ioi (3 : ℝ)), ‖Real.log u * Real.exp (-u / N)‖ ≤ H u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 3) hu
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith [Set.mem_Ioi.mp hu])
    have hlog : Real.log u ≤ Real.log N + u / N := by
      have hh := Real.log_le_sub_one_of_pos (div_pos hu0 hNpos)
      rw [Real.log_div hu0.ne' hNpos.ne'] at hh
      linarith
    rw [Real.norm_of_nonneg (by positivity)]
    dsimp [H]
    nlinarith [Real.exp_pos (-u / N)]
  have hH3 : IntegrableOn H (Set.Ioi (3 : ℝ)) :=
    hHi.mono_set (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 3) hu)
  have hfi : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u / N)) (Set.Ioi 3) :=
    hH3.mono' (by fun_prop) hAE
  refine ⟨hfi, ?_⟩
  have hcomp : (∫ u in Set.Ioi (3 : ℝ), Real.log u * Real.exp (-u / N)) ≤
      ∫ u in Set.Ioi (0 : ℝ), H u := by
    refine (integral_mono_ae hfi hH3 ?_).trans ?_
    · filter_upwards [hAE] with u hu
      exact (le_abs_self _).trans hu
    · apply setIntegral_mono_set hHi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact hHpos u hu
      · exact ae_of_all _ (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 3) hu)
  have hm0 : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u / N)) = N := by
    simpa using (residue_exponential_moment N hNpos 0).2
  have hm1 : (∫ u in Set.Ioi (0 : ℝ), (u / N) * Real.exp (-u / N)) = N := by
    simpa using (residue_exponential_moment N hNpos 1).2
  have hInt : (∫ u in Set.Ioi (0 : ℝ), H u) = N * (Real.log N + 1) := by
    rw [show H = (fun u => Real.log N * Real.exp (-u / N) + (u / N) * Real.exp (-u / N)) from rfl,
      integral_add (h0.const_mul _) h1, integral_const_mul, hm0, hm1]
    ring
  rwa [hInt] at hcomp


/-- The reciprocal integral in the constant remainder after display 3.4 on page 351. -/
theorem residue_inv_integral (N : ℝ) (hN : 3 ≤ N) :
    IntegrableOn (fun u : ℝ => 1 / u * Real.exp (-u / N)) (Set.Ioi 3) ∧
    (∫ u in Set.Ioi (3 : ℝ), 1 / u * Real.exp (-u / N)) ≤ Real.log N + 1 := by
  have hNpos : 0 < N := by linarith
  let f : ℝ → ℝ := fun u => 1 / u * Real.exp (-u / N)
  have hEi : IntegrableOn (fun u : ℝ => Real.exp (-u / N)) (Set.Ioi 0) := by
    simpa using (residue_exponential_moment N hNpos 0).1
  have hEv : (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u / N)) = N := by
    simpa using (residue_exponential_moment N hNpos 0).2
  have hf : IntegrableOn f (Set.Ioi (3 : ℝ)) := by
    apply (hEi.mono_set (fun u hu => lt_trans (by norm_num : (0 : ℝ) < 3) hu)).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 3) hu
    dsimp [f]
    rw [abs_of_nonneg (by positivity)]
    have hi : 1 / u ≤ 1 := (div_le_one hu0).mpr (by linarith [Set.mem_Ioi.mp hu])
    nlinarith [Real.exp_pos (-u / N)]
  have hfN : IntegrableOn f (Set.Ioi N) := hf.mono_set (fun u hu => lt_of_le_of_lt hN hu)
  have hi : IntervalIntegrable (fun u : ℝ => 1 / u) volume 3 N := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le hN] at hu
    change u ≠ 0
    linarith [hu.1]
  have hfc : IntervalIntegrable f volume 3 N :=
    hi.mul_continuousOn (by fun_prop)
  have hlo : (∫ u in (3 : ℝ)..N, f u) ≤ Real.log N := by
    have hh : (∫ u in (3 : ℝ)..N, f u) ≤ ∫ u in (3 : ℝ)..N, 1 / u := by
      apply intervalIntegral.integral_mono_on hN hfc hi
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      have he : Real.exp (-u / N) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hNpos.le)
      dsimp [f]
      exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)
    rw [integral_one_div_of_pos (by norm_num) hNpos,
      Real.log_div hNpos.ne' (by norm_num)] at hh
    exact hh.trans (sub_le_self _ (Real.log_nonneg (by norm_num)))
  have htail : (∫ u in Set.Ioi N, f u) ≤ 1 := by
    have hH : IntegrableOn (fun u : ℝ => (1 / N) * Real.exp (-u / N)) (Set.Ioi 0) :=
      hEi.const_mul _
    have hHN := hH.mono_set (fun u (hu : u ∈ Set.Ioi N) => lt_trans hNpos hu)
    have h1 : (∫ u in Set.Ioi N, f u) ≤ ∫ u in Set.Ioi N, (1 / N) * Real.exp (-u / N) := by
      apply integral_mono_ae hfN hHN
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      dsimp [f]
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hNpos (le_of_lt hu)) (Real.exp_pos _).le
    have h2 : (∫ u in Set.Ioi N, (1 / N) * Real.exp (-u / N)) ≤
        ∫ u in Set.Ioi (0 : ℝ), (1 / N) * Real.exp (-u / N) := by
      apply setIntegral_mono_set hH
      · exact ae_of_all _ (fun u => by positivity)
      · exact ae_of_all _ (fun u (hu : u ∈ Set.Ioi N) => lt_trans hNpos hu)
    have h3 : (∫ u in Set.Ioi (0 : ℝ), (1 / N) * Real.exp (-u / N)) = 1 := by
      rw [integral_const_mul, hEv]
      field_simp
    exact h1.trans (h2.trans_eq h3)
  refine ⟨hf, ?_⟩
  have hsplit := intervalIntegral.integral_interval_add_Ioi hf hfN
  change (∫ u in Set.Ioi (3 : ℝ), f u) ≤ Real.log N + 1
  linarith


/-- Combined real integral budget for displays 3.3 to 3.4 on pages 350 to 351.
The last term reserves the omitted model segment from 3 to square root N.
The constant remainder keeps the phase factor throughout. -/
theorem residue_remainder_budget (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) :
    2.6 / (N : ℝ) * (1 + 4 * Real.pi * Real.log N / Nat.totient q) *
        (∫ u in Set.Ioi (3 : ℝ), Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) +
      2.6 * (∫ u in Set.Ioi (3 : ℝ), Real.log u / Real.sqrt u * Real.exp (-u / N)) +
      (2 * 10 ^ 8 : ℝ) / N * (1 + 4 * Real.pi * Real.log N / Nat.totient q) *
        (∫ u in Set.Ioi (3 : ℝ), Real.log u * Real.exp (-u / N)) +
      (2 * 10 ^ 8 : ℝ) * (∫ u in Set.Ioi (3 : ℝ), 1 / u * Real.exp (-u / N)) +
      Real.sqrt N / Nat.totient q ≤
        3.8 * (1 + 4 * Real.pi * Real.log N / Nat.totient q) * Real.sqrt N * Real.log N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by linarith
  have hN3 : (3 : ℝ) ≤ N := by linarith
  have hL : 46 ≤ Real.log N := log_1e20_ge.trans
    (Real.log_le_log (by positivity) hN)
  have hs : (10000000000 : ℝ) ≤ Real.sqrt N :=
    (Real.le_sqrt (by norm_num) hNpos.le).mpr (by nlinarith [hN])
  have hp : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hp0 : (0 : ℝ) < Nat.totient q := by linarith
  let K : ℝ := 1 + 4 * Real.pi * Real.log N / Nat.totient q
  have hK : 1 ≤ K := by
    have hh : 0 ≤ 4 * Real.pi * Real.log N / (Nat.totient q : ℝ) := by positivity
    dsimp [K]
    linarith
  have hK0 : 0 ≤ K := by linarith
  have hE : (2 * 10 ^ 8 : ℝ) ≤ 0.02 * Real.sqrt N := by linarith
  have hsmall : 0.02 * (Real.log N + 1) ≤ 0.001 * Real.log N ^ 2 := by nlinarith
  have hunit : (1 : ℝ) ≤ 0.001 * Real.log N ^ 2 := by nlinarith
  have h1 : 2.6 / (N : ℝ) * K *
      (∫ u in Set.Ioi (3 : ℝ), Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) ≤
        2.99 * K * Real.sqrt N * Real.log N ^ 2 := by
    calc
      _ ≤ 2.6 / (N : ℝ) * K * (1.15 * N * Real.sqrt N * Real.log N ^ 2) :=
        mul_le_mul_of_nonneg_left (residue_log_square_integral N hN) (by positivity)
      _ = _ := by field_simp [hNpos.ne'] <;> ring
  have h2 : 2.6 * (∫ u in Set.Ioi (3 : ℝ), Real.log u / Real.sqrt u * Real.exp (-u / N)) ≤
      0.13 * Real.sqrt N * Real.log N ^ 2 := by
    nlinarith [residue_log_half_integral N hN]
  have h3 : (2 * 10 ^ 8 : ℝ) / N * K *
      (∫ u in Set.Ioi (3 : ℝ), Real.log u * Real.exp (-u / N)) ≤
        0.001 * K * Real.sqrt N * Real.log N ^ 2 := by
    calc
      _ ≤ (2 * 10 ^ 8 : ℝ) / N * K * ((N : ℝ) * (Real.log N + 1)) :=
        mul_le_mul_of_nonneg_left (residue_log_integral N (by linarith)).2 (by positivity)
      _ = (2 * 10 ^ 8 : ℝ) * K * (Real.log N + 1) := by field_simp [hNpos.ne'] <;> ring
      _ ≤ 0.02 * Real.sqrt N * K * (Real.log N + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE hK0) (by linarith)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hsmall
          (show 0 ≤ Real.sqrt N * K by positivity)
        nlinarith
  have h4 : (2 * 10 ^ 8 : ℝ) * (∫ u in Set.Ioi (3 : ℝ), 1 / u * Real.exp (-u / N)) ≤
      0.001 * Real.sqrt N * Real.log N ^ 2 := by
    calc
      _ ≤ (2 * 10 ^ 8 : ℝ) * (Real.log N + 1) :=
        mul_le_mul_of_nonneg_left (residue_inv_integral N hN3).2 (by norm_num)
      _ ≤ 0.02 * Real.sqrt N * (Real.log N + 1) :=
        mul_le_mul_of_nonneg_right hE (by linarith)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg (N : ℝ))
        nlinarith
  have h5 : Real.sqrt N / Nat.totient q ≤ 0.001 * Real.sqrt N * Real.log N ^ 2 := by
    calc
      _ ≤ Real.sqrt N := (div_le_self (Real.sqrt_nonneg _) hp)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hunit (Real.sqrt_nonneg (N : ℝ))
        nlinarith
  have hclose : 2.99 * K + 0.13 + 0.001 * K + 0.001 + 0.001 ≤ 3.8 * K := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hclose
    (show 0 ≤ Real.sqrt N * Real.log N ^ 2 by positivity)
  change 2.6 / (N : ℝ) * K * _ + 2.6 * _ + (2 * 10 ^ 8 : ℝ) / N * K * _ +
    (2 * 10 ^ 8 : ℝ) * _ + Real.sqrt N / Nat.totient q ≤ 3.8 * K * Real.sqrt N * Real.log N ^ 2
  nlinarith


/-- Integrability of the two real remainder kernels in display 3.4 on page 350. -/
theorem residue_error_kernels_integrable (N : ℝ) (hN : 0 < N) :
    IntegrableOn (fun u : ℝ => Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) (Set.Ioi 3) ∧
    IntegrableOn (fun u : ℝ => Real.log u / Real.sqrt u * Real.exp (-u / N)) (Set.Ioi 3) := by
  have hm : ∀ k : ℕ, IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-u / N)) (Set.Ioi 0) := by
    intro k
    simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul, neg_div, one_div_mul_eq_div] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (k : ℝ)) (b := 1 / N)
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k))
        (by norm_num) (by positivity)
  have h3 := (hm 3).mono_set (fun u (hu : u ∈ Set.Ioi (3 : ℝ)) => lt_trans (by norm_num : (0 : ℝ) < 3) hu)
  have h1 := (hm 1).mono_set (fun u (hu : u ∈ Set.Ioi (3 : ℝ)) => lt_trans (by norm_num : (0 : ℝ) < 3) hu)
  constructor
  · apply h3.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := by linarith [Set.mem_Ioi.mp hu]
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hlog : Real.log u ≤ u := Real.log_le_self (by linarith)
    have hs : Real.sqrt u ≤ u := Real.sqrt_le_self_iff.mpr (Or.inr hu1)
    have hb : Real.sqrt u * Real.log u ^ 2 ≤ u ^ 3 := by
      calc
        _ ≤ u * u ^ 2 := mul_le_mul hs (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by linarith)
        _ = _ := by ring
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  · apply h1.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := by linarith [Set.mem_Ioi.mp hu]
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hs : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr hu1
    have hb : Real.log u / Real.sqrt u ≤ u :=
      (div_le_self hlog0 hs).trans (Real.log_le_self (by linarith))
    rw [Real.norm_of_nonneg (by positivity), pow_one]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le


/-- Absolute convergence and the inclusive finite tail limit for display 3.2 on page 349. -/
theorem residueTail_partial_limit (N : ℕ) (hN : 0 < N) (q l : ℕ) (z : ℝ) :
    Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ioc ⌊Real.sqrt (N : ℝ)⌋₊ M,
      if n.Prime ∧ n % q = l % q then
        residueWeight ((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z)) n else 0)
      Filter.atTop (nhds (residueTail N q l z)) := by
  classical
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  let A : ℝ := Real.sqrt N
  let F : ℕ → ℂ := fun n => if n.Prime ∧ A < n ∧ n % q = l % q then tailTerm N z n else 0
  have hs : Summable F := by
    refine Summable.of_norm_bounded (summable_aZ hN) (fun n => ?_)
    by_cases h : n.Prime ∧ A < n ∧ n % q = l % q
    · rw [show F n = tailTerm N z n from if_pos h, tailTerm, norm_mul, norm_ee, mul_one,
        Complex.norm_real, Real.norm_of_nonneg
          (mul_nonneg (Real.log_natCast_nonneg n) (Real.exp_pos _).le)]
      unfold aZ
      rw [ArithmeticFunction.vonMangoldt_apply_prime h.1]
    · rw [show F n = 0 from if_neg h, norm_zero]
      exact aZ_nonneg N n
  have htail : residueTail N q l z = ∑' n : ℕ, F n := rfl
  have hw : ∀ n : ℕ, residueWeight x n = tailTerm N z n := by
    intro n
    have he : -x * (n : ℂ) = (((-(n : ℝ) / (N : ℝ) : ℝ)) : ℂ) +
        2 * Real.pi * Complex.I * (-(n : ℝ) * z) := by
      dsimp [x]
      push_cast
      ring
    rw [residueWeight]
    simp only [Complex.ofReal_natCast]
    rw [he, Complex.exp_add]
    simp only [tailTerm, ee, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
    ring
  have heq : ∀ M : ℕ,
      (∑ n ∈ Finset.Ioc ⌊A⌋₊ M, if n.Prime ∧ n % q = l % q then residueWeight x n else 0) =
      ∑ n ∈ Finset.range (M + 1), F n := by
    intro M
    calc
      _ = ∑ n ∈ Finset.Ioc ⌊A⌋₊ M, F n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hAn : A < (n : ℝ) := (Nat.floor_lt (Real.sqrt_nonneg (N : ℝ))).mp (Finset.mem_Ioc.mp hn).1
        simp only [F, hAn, hw]
        by_cases hp : n.Prime <;> by_cases hmod : n % q = l % q <;> simp [hp, hmod]
      _ = _ := by
        apply Finset.sum_subset
        · intro n hn
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hn).2)
        · intro n hn hnnot
          have hnM : n ≤ M := by have := Finset.mem_range.mp hn; omega
          have hnA : n ≤ ⌊A⌋₊ := by
            simp only [Finset.mem_Ioc, not_and, not_le] at hnnot
            omega
          have hAn : ¬ A < (n : ℝ) := not_lt_of_ge
            ((show (n : ℝ) ≤ (⌊A⌋₊ : ℝ) by exact_mod_cast hnA).trans (Nat.floor_le (Real.sqrt_nonneg _)))
          simp [F, hAn]
  have hh := hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  rw [← htail] at hh
  convert hh using 1
  funext M
  exact heq M


/-- Integrability of the progression count term in Abel summation on page 350. -/
theorem residue_count_deriv_integrable (x : ℂ) (hx : 0 < x.re) (q l : ℕ)
    {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (fun u : ℝ => deriv (residueWeight x) u * (State1546.piMod u q l : ℂ))
      (Set.Ioi A) := by
  have hpiM : Measurable (fun u : ℝ => (State1546.piMod u q l : ℂ)) := by
    let P : ℕ → ℂ := fun n => (((Finset.Iic n).filter
      (fun p => p.Prime ∧ p % q = l % q)).card : ℂ)
    have hP : Measurable P := Measurable.of_discrete
    change Measurable (P ∘ (Nat.floor : ℝ → ℕ))
    exact hP.comp Nat.measurable_floor
  have h0 : IntegrableOn (fun u : ℝ => Real.exp (-x.re * u)) (Set.Ioi 0) := by
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (0 : ℝ)) (b := x.re)
        (by norm_num) (by norm_num) hx
  have h2 : IntegrableOn (fun u : ℝ => u ^ 2 * Real.exp (-x.re * u)) (Set.Ioi 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (2 : ℝ)) (b := x.re)
        (by norm_num) (by norm_num) hx
  let H : ℝ → ℝ := fun u => 2 * Real.exp (-x.re * u) +
    (2 * ‖x‖) * (u ^ 2 * Real.exp (-x.re * u))
  have hH : IntegrableOn H (Set.Ioi 0) := (h0.const_mul _).add (h2.const_mul _)
  have hHA : IntegrableOn H (Set.Ioi A) := hH.mono_set (fun u hu =>
    lt_trans (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hA) (Set.mem_Ioi.mp hu))
  apply hHA.mono'
  · have hm : AEStronglyMeasurable (fun u : ℝ =>
        (Complex.exp (-x * u) * (((1 / u : ℝ) : ℂ) - x * (Real.log u : ℂ))) *
          (State1546.piMod u q l : ℂ)) (volume.restrict (Set.Ioi A)) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    apply hm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : u ≠ 0 := by have huA : A < u := hu; linarith
    rw [(residueWeight_hasDerivAt x hu0).deriv]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := by have huA : A < u := hu; linarith
    have hu0 : 0 < u := by linarith
    have hp : ‖(State1546.piMod u q l : ℂ)‖ ≤ 2 * u := by
      rw [Complex.norm_natCast]
      have hc : State1546.piMod u q l ≤ ⌊u⌋₊ + 1 := by
        unfold State1546.piMod
        exact (Finset.card_filter_le _ _).trans_eq (Nat.card_Iic _)
      have hc' : (State1546.piMod u q l : ℝ) ≤ (⌊u⌋₊ : ℝ) + 1 := by exact_mod_cast hc
      linarith [Nat.floor_le hu0.le]
    have hl : Real.log u ≤ u := Real.log_le_self hu0.le
    have hl0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    rw [norm_mul]
    calc
      _ ≤ ((1 / u + ‖x‖ * Real.log u) * Real.exp (-x.re * u)) * (2 * u) :=
        mul_le_mul (residueWeight_deriv_norm x hu1) hp (norm_nonneg _) (by positivity)
      _ ≤ ((1 / u + ‖x‖ * u) * Real.exp (-x.re * u)) * (2 * u) := by gcongr
      _ = H u := by dsimp [H]; field_simp [hu0.ne'] <;> ring


/-- The improper Abel identity for the actual residue tail, supporting display 3.3 on page 350.
The lower progression count term is retained explicitly. -/
theorem residueTail_abel (N : ℕ) (hN : 0 < N) (q l : ℕ) (z : ℝ) :
    residueTail N q l z =
      -residueWeight ((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z)) (Real.sqrt N) *
        (State1546.piMod (Real.sqrt N) q l : ℂ) -
      ∫ u in Set.Ioi (Real.sqrt (N : ℝ)),
        deriv (residueWeight ((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z))) u *
          (State1546.piMod u q l : ℂ) := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  let A : ℝ := Real.sqrt N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 1 ≤ A := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  have hx : 0 < x.re := by simp [x]; positivity
  have hi := residue_count_deriv_integrable x hx q l hA
  have hb := (residue_boundary_tendsto x hx q l).comp tendsto_natCast_atTop_atTop
  have hI := intervalIntegral_tendsto_integral_Ioi A hi tendsto_natCast_atTop_atTop
  have hh := (hb.sub_const (residueWeight x A * (State1546.piMod A q l : ℂ))).sub hI
  simp only [zero_sub] at hh
  have he : ∀ᶠ M : ℕ in Filter.atTop, A ≤ (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop A)
  have hlim : Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.Ioc ⌊A⌋₊ M,
      if n.Prime ∧ n % q = l % q then residueWeight x n else 0) Filter.atTop
        (nhds (-(residueWeight x A * (State1546.piMod A q l : ℂ)) -
          ∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.piMod u q l : ℂ))) := by
    apply hh.congr'
    filter_upwards [he] with M hAM
    have hfin := residue_finite_abel x q l hA hAM
    rw [Nat.floor_natCast] at hfin
    rw [← intervalIntegral.integral_of_le hAM] at hfin
    simpa only [neg_mul, Function.comp_apply] using hfin.symm
  simpa only [neg_mul] using tendsto_nhds_unique (residueTail_partial_limit N hN q l z) hlim


/-- The derivative of the logarithmic integral used in Abel summation on pages 349 to 350. -/
theorem residue_zinLi_hasDerivAt {u : ℝ} (hu : 2 < u) :
    HasDerivAt State1546.zinLi (1 / Real.log u) u := by
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc (2 : ℝ) u) := by
    apply continuousOn_const.div
    · apply Real.continuousOn_log.mono
      intro t ht
      rw [Set.uIcc_of_le hu.le] at ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (show t ≠ 0 by linarith [ht.1])
    · intro t ht
      rw [Set.uIcc_of_le hu.le] at ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
  have hm : Measurable (fun t : ℝ => 1 / Real.log t) := by fun_prop
  have hu0 : u ≠ 0 := by linarith
  have hlog : Real.log u ≠ 0 := (Real.log_pos (by linarith)).ne'
  exact intervalIntegral.integral_hasDerivAt_right hc.intervalIntegrable
    hm.stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_const.div (Real.continuousAt_log hu0) hlog)


/-- Elementary growth bounds for the Li main term in display 3.3 on page 350. -/
theorem residue_zinLi_bounds {u : ℝ} (hu : 2 ≤ u) :
    0 ≤ State1546.zinLi u ∧ State1546.zinLi u ≤ 2 * u := by
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.uIcc (2 : ℝ) u) := by
    apply continuousOn_const.div
    · apply Real.continuousOn_log.mono
      intro t ht
      rw [Set.uIcc_of_le hu] at ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (show t ≠ 0 by linarith [ht.1])
    · intro t ht
      rw [Set.uIcc_of_le hu] at ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  constructor
  · apply intervalIntegral.integral_nonneg hu
    intro t ht
    have htlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
    positivity
  · have hh : (∫ t in (2 : ℝ)..u, 1 / Real.log t) ≤ ∫ t in (2 : ℝ)..u, (2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hu hc.intervalIntegrable intervalIntegrable_const
      intro t ht
      have hlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
      have hpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      rw [div_le_iff₀ hpos]
      linarith
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
    change (∫ t in (2 : ℝ)..u, 1 / Real.log t) ≤ 2 * u
    linarith


/-- Polynomial domination for the weighted improper integrals in display 3.3 on page 350. -/
theorem residueWeight_deriv_mul_integrable (x : ℂ) (hx : 0 < x.re) {A : ℝ} (hA : 1 ≤ A)
    (g : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hgm : AEStronglyMeasurable g (volume.restrict (Set.Ioi A)))
    (hg : ∀ u ∈ Set.Ioi A, ‖g u‖ ≤ C * u) :
    IntegrableOn (fun u : ℝ => deriv (residueWeight x) u * g u) (Set.Ioi A) := by
  have h0 : IntegrableOn (fun u : ℝ => Real.exp (-x.re * u)) (Set.Ioi 0) := by
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (0 : ℝ)) (b := x.re)
        (by norm_num) (by norm_num) hx
  have h2 : IntegrableOn (fun u : ℝ => u ^ 2 * Real.exp (-x.re * u)) (Set.Ioi 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (2 : ℝ)) (b := x.re)
        (by norm_num) (by norm_num) hx
  let H : ℝ → ℝ := fun u => C * Real.exp (-x.re * u) +
    (C * ‖x‖) * (u ^ 2 * Real.exp (-x.re * u))
  have hH : IntegrableOn H (Set.Ioi 0) := (h0.const_mul _).add (h2.const_mul _)
  have hHA : IntegrableOn H (Set.Ioi A) := hH.mono_set (fun u hu =>
    lt_trans (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hA) (Set.mem_Ioi.mp hu))
  apply hHA.mono'
  · have hm : AEStronglyMeasurable (fun u : ℝ =>
        (Complex.exp (-x * u) * (((1 / u : ℝ) : ℂ) - x * (Real.log u : ℂ))) * g u)
          (volume.restrict (Set.Ioi A)) := by
      have hf : Measurable (fun u : ℝ => Complex.exp (-x * u) *
          (((1 / u : ℝ) : ℂ) - x * (Real.log u : ℂ))) := by fun_prop
      exact hf.aestronglyMeasurable.mul hgm
    apply hm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : u ≠ 0 := by have huA : A < u := hu; linarith
    rw [(residueWeight_hasDerivAt x hu0).deriv]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := by have huA : A < u := hu; linarith
    have hu0 : 0 < u := by linarith
    have hl : Real.log u ≤ u := Real.log_le_self hu0.le
    have hl0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    rw [norm_mul]
    calc
      _ ≤ ((1 / u + ‖x‖ * Real.log u) * Real.exp (-x.re * u)) * (C * u) :=
        mul_le_mul (residueWeight_deriv_norm x hu1) (hg u hu) (norm_nonneg _) (by positivity)
      _ ≤ ((1 / u + ‖x‖ * u) * Real.exp (-x.re * u)) * (C * u) := by gcongr
      _ = H u := by dsimp [H]; field_simp [hu0.ne'] <;> ring


/-- The upper endpoint vanishes for linearly bounded factors in display 3.3 on page 350. -/
theorem residueWeight_mul_tendsto (x : ℂ) (hx : 0 < x.re) {A : ℝ} (hA : 1 ≤ A)
    (g : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ u ∈ Set.Ioi A, ‖g u‖ ≤ C * u) :
    Filter.Tendsto (fun u : ℝ => residueWeight x u * g u) Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun u : ℝ => C * (u ^ 2 * Real.exp (-x.re * u)))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_ofNat, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 x.re hx).const_mul C
  apply squeeze_zero_norm' _ ht
  filter_upwards [Filter.eventually_gt_atTop A] with u hu
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hlog : Real.log u ≤ u := Real.log_le_self hu0.le
  have hn : ‖residueWeight x u‖ = Real.exp (-x.re * u) * Real.log u := by
    rw [residueWeight, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog0]
    simp
  rw [norm_mul, hn]
  calc
    _ ≤ (Real.exp (-x.re * u) * u) * (C * u) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le) (hg u hu)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring


/-- The Li main term in the improper Abel identity on page 350. -/
theorem residue_zinLi_abel (x : ℂ) (hx : 0 < x.re) {A : ℝ} (hA : 3 ≤ A) :
    IntegrableOn (fun u : ℝ => deriv (residueWeight x) u * (State1546.zinLi u : ℂ)) (Set.Ioi A) ∧
    (∫ u in Set.Ioi A, Complex.exp (-x * u)) =
      -residueWeight x A * (State1546.zinLi A : ℂ) -
        ∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.zinLi u : ℂ) := by
  have hA1 : 1 ≤ A := by linarith
  have hc : ContinuousOn (fun u : ℝ => (State1546.zinLi u : ℂ)) (Set.Ioi A) := by
    intro u hu
    exact Complex.continuous_ofReal.continuousAt.comp
      (residue_zinLi_hasDerivAt (by linarith [Set.mem_Ioi.mp hu])).continuousAt |>.continuousWithinAt
  have hg : ∀ u ∈ Set.Ioi A, ‖(State1546.zinLi u : ℂ)‖ ≤ 2 * u := by
    intro u hu
    have hb := residue_zinLi_bounds (u := u) (by linarith [Set.mem_Ioi.mp hu])
    simpa only [Complex.norm_real, Real.norm_of_nonneg hb.1] using hb.2
  have hi := residueWeight_deriv_mul_integrable x hx hA1 (fun u => (State1546.zinLi u : ℂ))
    2 (by norm_num) (hc.aestronglyMeasurable measurableSet_Ioi) hg
  refine ⟨hi, ?_⟩
  have he : IntegrableOn (fun u : ℝ => Complex.exp (-x * u)) (Set.Ioi A) :=
    integrableOn_exp_mul_complex_Ioi (a := -x) (by simpa using hx) A
  have hd : ∀ u ∈ Set.Ici A, HasDerivAt
      (fun u : ℝ => residueWeight x u * (State1546.zinLi u : ℂ))
      (deriv (residueWeight x) u * (State1546.zinLi u : ℂ) + Complex.exp (-x * u)) u := by
    intro u hu
    have hu2 : 2 < u := by have huA : A ≤ u := hu; linarith
    have hu0 : u ≠ 0 := by linarith
    have hlog : Real.log u ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hcanc : residueWeight x u * ((1 / Real.log u : ℝ) : ℂ) = Complex.exp (-x * u) := by
      rw [residueWeight]
      simp only [Complex.ofReal_div, Complex.ofReal_one]
      field_simp [Complex.ofReal_ne_zero.mpr hlog]
    convert (residueWeight_hasDerivAt x hu0).mul (residue_zinLi_hasDerivAt hu2).ofReal_comp using 1
    rw [(residueWeight_hasDerivAt x hu0).deriv, hcanc]
  have hEq := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hi.add he)
    (residueWeight_mul_tendsto x hx hA1 (fun u => (State1546.zinLi u : ℂ)) 2 (by norm_num) hg)
  rw [integral_add hi he] at hEq
  simp only [zero_sub] at hEq
  have hsum : (∫ u in Set.Ioi A, Complex.exp (-x * u)) +
      (∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.zinLi u : ℂ)) =
        -(residueWeight x A * (State1546.zinLi A : ℂ)) := by
    rw [add_comm]
    exact hEq
  simpa only [neg_mul] using (eq_sub_iff_add_eq.mpr hsum)


/-- The phase-dependent exponent bound following display 3.3 on page 350. -/
theorem residue_exponent_norm_bound (N : ℕ) (hN : 0 < N) (q : ℕ) (hq : 0 < q)
    (z : ℝ) (hz : |z| ≤ arcRadius N q) :
    ‖(((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z)‖ ≤
      (1 + 4 * Real.pi * Real.log N / Nat.totient q) / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hn : ‖(2 : ℂ) * Real.pi * Complex.I * z‖ = 2 * Real.pi * |z| := by
    simp [norm_mul, Real.pi_pos.le, abs_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ)‖ + ‖(2 : ℂ) * Real.pi * Complex.I * z‖ := norm_add_le _ _
    _ = 1 / (N : ℝ) + 2 * Real.pi * |z| := by
      rw [hn, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ 1 / (N : ℝ) + 2 * Real.pi * arcRadius N q := by gcongr
    _ = _ := by unfold arcRadius; field_simp [hNr.ne', hp.ne'] <;> ring


/-- Integrating the derivative of the Abel weight gives its lower endpoint on page 350. -/
theorem residueWeight_integral_deriv (x : ℂ) (hx : 0 < x.re) {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (deriv (residueWeight x)) (Set.Ioi A) ∧
    (∫ u in Set.Ioi A, deriv (residueWeight x) u) = -residueWeight x A := by
  have hg : ∀ u ∈ Set.Ioi A, ‖(1 : ℂ)‖ ≤ (1 : ℝ) * u := by
    intro u hu
    simp only [norm_one, one_mul]
    have huA : A < u := hu
    linarith
  have hi : IntegrableOn (deriv (residueWeight x)) (Set.Ioi A) := by
    simpa only [mul_one] using residueWeight_deriv_mul_integrable x hx hA (fun _ => (1 : ℂ))
      1 (by norm_num) aestronglyMeasurable_const hg
  have ht : Filter.Tendsto (residueWeight x) Filter.atTop (nhds 0) := by
    simpa only [mul_one] using residueWeight_mul_tendsto x hx hA (fun _ => (1 : ℂ)) 1 (by norm_num) hg
  have hd : ∀ u ∈ Set.Ici A, HasDerivAt (residueWeight x) (deriv (residueWeight x) u) u := by
    intro u hu
    have hu0 : u ≠ 0 := by have huA : A ≤ u := hu; linarith
    exact (residueWeight_hasDerivAt x hu0).differentiableAt.hasDerivAt
  refine ⟨hi, ?_⟩
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht


/-- The centered progression error in display 3.3 on page 350.
The Li term at the lower endpoint is subtracted with the lower progression count. -/
theorem residueTail_centered_abel (N : ℕ) (hN : 9 ≤ N) (q l : ℕ) (z : ℝ) :
    let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
    let A : ℝ := Real.sqrt N
    let G : ℝ → ℂ := fun u => (State1546.piMod u q l : ℂ) - State1546.piMod A q l -
      ((State1546.zinLi u : ℂ) - State1546.zinLi A) / (Nat.totient q : ℂ)
    IntegrableOn (fun u => deriv (residueWeight x) u * G u) (Set.Ioi A) ∧
      residueTail N q l z - (∫ u in Set.Ioi A, Complex.exp (-x * u)) / (Nat.totient q : ℂ) =
        -(∫ u in Set.Ioi A, deriv (residueWeight x) u * G u) := by
  dsimp only
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  let A : ℝ := Real.sqrt N
  let φ : ℂ := Nat.totient q
  let c : ℂ := (State1546.piMod A q l : ℂ) - (State1546.zinLi A : ℂ) / φ
  let G : ℝ → ℂ := fun u => (State1546.piMod u q l : ℂ) - State1546.piMod A q l -
    ((State1546.zinLi u : ℂ) - State1546.zinLi A) / φ
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hx : 0 < x.re := by simp [x]; positivity
  have hA3 : 3 ≤ A := (Real.le_sqrt (by norm_num) hNr.le).mpr (by exact_mod_cast hN)
  have hA1 : 1 ≤ A := by linarith
  have hpi := residue_count_deriv_integrable x hx q l hA1
  have hLi := (residue_zinLi_abel x hx hA3).1
  have hmodel := (residue_zinLi_abel x hx hA3).2
  have hD := residueWeight_integral_deriv x hx hA1
  have hdiv := hLi.div_const φ
  have hconst := hD.1.mul_const c
  have hfun : (fun u : ℝ => deriv (residueWeight x) u * G u) =
      (fun u => deriv (residueWeight x) u * (State1546.piMod u q l : ℂ) -
        (deriv (residueWeight x) u * (State1546.zinLi u : ℂ)) / φ -
        deriv (residueWeight x) u * c) := by
    funext u
    dsimp [G, c]
    ring
  have hG : IntegrableOn (fun u : ℝ => deriv (residueWeight x) u * G u) (Set.Ioi A) := by
    rw [hfun]
    exact (hpi.sub hdiv).sub hconst
  have hInt : (∫ u in Set.Ioi A, deriv (residueWeight x) u * G u) =
      (∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.piMod u q l : ℂ)) -
      (∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.zinLi u : ℂ)) / φ -
      (-residueWeight x A) * c := by
    have ho := integral_sub (hpi.sub hdiv) hconst
    have hin := integral_sub hpi hdiv
    simp only [Pi.sub_apply] at ho hin
    rw [hfun, ho, hin, integral_div, integral_mul_const, hD.2]
  change IntegrableOn (fun u => deriv (residueWeight x) u * G u) (Set.Ioi A) ∧
    residueTail N q l z - (∫ u in Set.Ioi A, Complex.exp (-x * u)) / φ =
      -(∫ u in Set.Ioi A, deriv (residueWeight x) u * G u)
  refine ⟨hG, ?_⟩
  rw [residueTail_abel N hN0 q l z, hmodel, hInt]
  change -residueWeight x A * (State1546.piMod A q l : ℂ) -
    (∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.piMod u q l : ℂ)) -
    (-residueWeight x A * (State1546.zinLi A : ℂ) -
      ∫ u in Set.Ioi A, deriv (residueWeight x) u * (State1546.zinLi u : ℂ)) / φ = _
  dsimp [c]
  ring


/-- The lower model segment omitted from the prime tail in display 3.3 on page 350. -/
theorem residue_model_segment (N : ℕ) (hN : 9 ≤ N) (z : ℝ) :
    let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
    ‖(∫ u in Set.Ioi (Real.sqrt (N : ℝ)), Complex.exp (-x * u)) - continuousModel N z‖ ≤
      Real.sqrt N := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  let A : ℝ := Real.sqrt N
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hx : 0 < x.re := by simp [x]; positivity
  have hA3 : 3 ≤ A := (Real.le_sqrt (by norm_num) hNr.le).mpr (by exact_mod_cast hN)
  have hi3 := integrableOn_exp_mul_complex_Ioi (a := -x) (by simpa using hx) (3 : ℝ)
  have hiA := integrableOn_exp_mul_complex_Ioi (a := -x) (by simpa using hx) A
  have hmodel : (∫ u in Set.Ioi (3 : ℝ), Complex.exp (-x * u)) = continuousModel N z :=
    continuousModel_integral N hN0 z
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi3 hiA
  rw [hmodel] at hsplit
  have heq : (∫ u in Set.Ioi A, Complex.exp (-x * u)) - continuousModel N z =
      -(∫ u in (3 : ℝ)..A, Complex.exp (-x * u)) := by
    rw [← hsplit]
    ring
  change ‖(∫ u in Set.Ioi A, Complex.exp (-x * u)) - continuousModel N z‖ ≤ A
  rw [heq, norm_neg]
  have hb : ∀ u ∈ Set.uIoc (3 : ℝ) A, ‖Complex.exp (-x * u)‖ ≤ 1 := by
    intro u hu
    rw [Set.uIoc_of_le hA3] at hu
    have hu0 : 0 ≤ u := by linarith [hu.1]
    have hxre : x.re = 1 / (N : ℝ) := by simp [x]
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    have he : (-x * (u : ℂ)).re = -(1 / (N : ℝ)) * u := by simp [hxre]
    rw [he]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (one_div_nonneg.mpr hNr.le)) hu0
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [one_mul, abs_of_nonneg (by linarith : 0 ≤ A - 3)] at hh
  linarith


/-- The four real kernels control any centered error with the Proposition 1.4 increment budget.
CONDITIONAL ON the supplied pointwise centered error inequality. -/
theorem residue_remainder_integral_bound (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) (z : ℝ) (hz : |z| ≤ arcRadius N q) (G : ℝ → ℂ)
    (hi : IntegrableOn (fun u : ℝ => deriv (residueWeight
      ((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z))) u * G u)
      (Set.Ioi (Real.sqrt (N : ℝ))))
    (hG : ∀ u ∈ Set.Ioi (Real.sqrt (N : ℝ)), ‖G u‖ ≤
      2.6 * Real.sqrt u * Real.log u + 2 * 10 ^ 8) :
    ‖∫ u in Set.Ioi (Real.sqrt (N : ℝ)), deriv (residueWeight
      ((((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z))) u * G u‖ +
      Real.sqrt N / (Nat.totient q : ℝ) ≤
        3.8 * (1 + 4 * Real.pi * Real.log N / Nat.totient q) * Real.sqrt N * Real.log N ^ 2 := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  let A : ℝ := Real.sqrt N
  let K : ℝ := 1 + 4 * Real.pi * Real.log N / Nat.totient q
  let H : ℝ → ℝ := fun u =>
    (2.6 / (N : ℝ) * K) * (Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) +
    2.6 * (Real.log u / Real.sqrt u * Real.exp (-u / N)) +
    ((2 * 10 ^ 8 : ℝ) / N * K) * (Real.log u * Real.exp (-u / N)) +
    (2 * 10 ^ 8 : ℝ) * (1 / u * Real.exp (-u / N))
  have hN0 : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hA3 : 3 ≤ A := (Real.le_sqrt (by norm_num) hNr.le).mpr (by nlinarith [hN])
  have hp : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hxnorm : ‖x‖ ≤ K / (N : ℝ) := residue_exponent_norm_bound N hN0 q hq z hz
  have hxre : x.re = 1 / (N : ℝ) := by simp [x]
  have h1 := (residue_error_kernels_integrable N hNr).1.const_mul (2.6 / (N : ℝ) * K)
  have h2 := (residue_error_kernels_integrable N hNr).2.const_mul (2.6 : ℝ)
  have h3 := (residue_log_integral N (by linarith)).1.const_mul ((2 * 10 ^ 8 : ℝ) / N * K)
  have h4 := (residue_inv_integral N (by linarith)).1.const_mul (2 * 10 ^ 8 : ℝ)
  have hH : IntegrableOn H (Set.Ioi (3 : ℝ)) := by
    exact (((h1.add h2).add h3).add h4).congr (Filter.Eventually.of_forall (fun u => by rfl))
  have hHA : IntegrableOn H (Set.Ioi A) :=
    hH.mono_set (fun u hu => lt_of_le_of_lt hA3 hu)
  have hpt : ∀ u ∈ Set.Ioi A, ‖deriv (residueWeight x) u * G u‖ ≤ H u := by
    intro u hu
    have hu3 : 3 < u := lt_of_le_of_lt hA3 hu
    have hu1 : 1 ≤ u := by linarith
    have hu0 : 0 < u := by linarith
    have hl : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
    have hrat : Real.log u / Real.sqrt u = Real.sqrt u * Real.log u / u := by
      calc
        _ = Real.sqrt u * Real.log u / Real.sqrt u ^ 2 := by field_simp [hs.ne'] <;> ring
        _ = _ := by rw [Real.sq_sqrt hu0.le]
    have he : Real.exp (-x.re * u) = Real.exp (-u / N) := by
      rw [hxre]
      congr 1
      ring
    rw [norm_mul]
    calc
      _ ≤ ((1 / u + ‖x‖ * Real.log u) * Real.exp (-x.re * u)) *
          (2.6 * Real.sqrt u * Real.log u + 2 * 10 ^ 8) :=
        mul_le_mul (residueWeight_deriv_norm x hu1) (hG u hu) (norm_nonneg _) (by positivity)
      _ ≤ ((1 / u + (K / N) * Real.log u) * Real.exp (-u / N)) *
          (2.6 * Real.sqrt u * Real.log u + 2 * 10 ^ 8) := by rw [he]; gcongr
      _ = H u := by
        dsimp [H]
        rw [hrat]
        field_simp [hNr.ne', hu0.ne'] <;> ring
  have hcomp : ‖∫ u in Set.Ioi A, deriv (residueWeight x) u * G u‖ ≤
      ∫ u in Set.Ioi (3 : ℝ), H u := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_ae hi.norm hHA ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpt u hu
    · apply setIntegral_mono_set hH
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 3) hu
        have hl : 0 ≤ Real.log u := Real.log_nonneg (by linarith [Set.mem_Ioi.mp hu])
        dsimp [H]
        positivity
      · exact ae_of_all _ (fun u hu => lt_of_le_of_lt hA3 hu)
  have hInt : (∫ u in Set.Ioi (3 : ℝ), H u) =
      2.6 / (N : ℝ) * K * (∫ u in Set.Ioi (3 : ℝ), Real.sqrt u * Real.log u ^ 2 * Real.exp (-u / N)) +
      2.6 * (∫ u in Set.Ioi (3 : ℝ), Real.log u / Real.sqrt u * Real.exp (-u / N)) +
      (2 * 10 ^ 8 : ℝ) / N * K * (∫ u in Set.Ioi (3 : ℝ), Real.log u * Real.exp (-u / N)) +
      (2 * 10 ^ 8 : ℝ) * (∫ u in Set.Ioi (3 : ℝ), 1 / u * Real.exp (-u / N)) := by
    have h12 := integral_add h1 h2
    have h123 := integral_add (h1.add h2) h3
    have h1234 := integral_add ((h1.add h2).add h3) h4
    simp only [Pi.add_apply] at h12 h123 h1234
    dsimp only [H]
    rw [h1234, h123, h12]
    simp only [integral_const_mul]
  rw [hInt] at hcomp
  have hb := residue_remainder_budget N hN q hq
  dsimp only [x, A, K] at hcomp
  linarith


/-- The per-residue approximation behind display 3.3 on page 350.
CONDITIONAL ON the explicit progression error bound of Proposition 1.4. -/
theorem residueTail_error_of_count (N : ℕ) (hN : (10 : ℝ) ^ 20 ≤ N)
    (q : ℕ) (hq : 0 < q) (hQ : q ≤ arcCutoff N) (l : ℕ) (z : ℝ)
    (hz : |z| ≤ arcRadius N q)
    (hcount : ∀ {t : ℝ}, (10 : ℝ) ^ 9 ≤ t → (q : ℝ) ≤ t ^ (0.37 : ℝ) →
      |(State1546.piMod t q l : ℝ) - State1546.zinLi t / (Nat.totient q : ℝ)| ≤
        1.3 * Real.sqrt t * Real.log t + 10 ^ 8) :
    ‖residueTail N q l z - continuousModel N z / (Nat.totient q : ℂ)‖ ≤
      3.8 * (1 + 4 * Real.pi * Real.log N / Nat.totient q) * Real.sqrt N * Real.log N ^ 2 := by
  let x : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + 2 * Real.pi * Complex.I * z
  let A : ℝ := Real.sqrt N
  let φ : ℂ := Nat.totient q
  let G : ℝ → ℂ := fun u => (State1546.piMod u q l : ℂ) - State1546.piMod A q l -
    ((State1546.zinLi u : ℂ) - State1546.zinLi A) / φ
  let J : ℂ := ∫ u in Set.Ioi A, Complex.exp (-x * u)
  let I : ℂ := ∫ u in Set.Ioi A, deriv (residueWeight x) u * G u
  have hN9 : 9 ≤ N := by exact_mod_cast (show (9 : ℝ) ≤ N by linarith)
  have hc := residueTail_centered_abel N hN9 q l z
  have hi : IntegrableOn (fun u => deriv (residueWeight x) u * G u) (Set.Ioi A) := hc.1
  have hcenter : residueTail N q l z - J / φ = -I := hc.2
  have hg : ∀ u ∈ Set.Ioi A, ‖G u‖ ≤ 2.6 * Real.sqrt u * Real.log u + 2 * 10 ^ 8 := by
    intro u hu
    have huA : Real.sqrt N ≤ u := (Set.mem_Ioi.mp hu).le
    have hb := residue_count_increment_bound N hN q l hQ hcount huA
    have heq : G u = ((((State1546.piMod u q l : ℝ) - State1546.piMod A q l) -
      (State1546.zinLi u - State1546.zinLi A) / (Nat.totient q : ℝ) : ℝ) : ℂ) := by
      dsimp [G, φ]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact hb
  have hb := residue_remainder_integral_bound N hN q hq z hz G hi hg
  have hseg : ‖J - continuousModel N z‖ ≤ Real.sqrt N := residue_model_segment N hN9 z
  have hp : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hseg' : ‖(J - continuousModel N z) / φ‖ ≤ Real.sqrt N / (Nat.totient q : ℝ) := by
    simp only [norm_div, φ, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right hseg hp.le
  have heq : residueTail N q l z - continuousModel N z / φ =
      (residueTail N q l z - J / φ) + (J - continuousModel N z) / φ := by ring
  have hfirst : ‖residueTail N q l z - J / φ‖ = ‖I‖ := by rw [hcenter, norm_neg]
  rw [heq]
  calc
    _ ≤ ‖residueTail N q l z - J / φ‖ + ‖(J - continuousModel N z) / φ‖ := norm_add_le _ _
    _ ≤ ‖I‖ + Real.sqrt N / (Nat.totient q : ℝ) := add_le_add (le_of_eq hfirst) hseg'
    _ ≤ _ := hb


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
  -- CONDITIONAL ON State1546.prop14_error_bound in the separate unit.
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hQ : q ≤ arcCutoff N := (Finset.mem_Icc.mp hq).2
  have hp : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  let E : ℝ := 3.8 * (1 + 4 * Real.pi * Real.log N / Nat.totient q) *
    Real.sqrt N * Real.log N ^ 2
  have he : ∀ l ∈ (Finset.range q).filter (fun l => Nat.Coprime l q),
      ‖residueTail N q l z - continuousModel N z / (Nat.totient q : ℂ)‖ ≤ E := by
    intro l hl
    have hcl : Nat.Coprime l q := (Finset.mem_filter.mp hl).2
    exact residueTail_error_of_count N hN q hq0 hQ l z hz
      (fun {t} ht hqt => State1546.prop14_error_bound hG (by omega) hcl ht hqt)
  have hh := residueExpansion_error_of_tail N q a hq0 hac z E he
  refine hh.trans_eq ?_
  dsimp [E]
  unfold lemma31Base
  field_simp [hp.ne'] <;> ring

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
