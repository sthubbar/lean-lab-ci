/-
P0069, pages 26 and 27, display 4.12. CODEX task528.
Finite interval counting for the concrete intermediate divisor band.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp528a
import LeanLab.BHP1997.Decomp528e

namespace LeanLab.BHP1997.Decomp528f
open Classical Decomp528a Decomp528e Decomp312c
open scoped BigOperators

/-- Page 27, exact count of multiples in a natural half open interval. -/
theorem multiples_Ioc_card {a b : ℕ} (hab : a ≤ b) (d : ℕ) :
    ((Finset.Ioc a b).filter (fun n => d ∣ n)).card = b / d - a / d := by
  have he : (Finset.Ioc a b).filter (fun n => d ∣ n) =
      ((Finset.Ioc 0 b).filter (fun n => d ∣ n)) \
        ((Finset.Ioc 0 a).filter (fun n => d ∣ n)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  have hsub : (Finset.Ioc 0 a).filter (fun n => d ∣ n) ⊆
      (Finset.Ioc 0 b).filter (fun n => d ∣ n) := by
    intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hab⟩, hd⟩
  rw [he, Finset.card_sdiff_of_subset hsub,
    Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]

/-- Page 27, the multiples count is at most interval length over d plus one. -/
theorem interval_multiples_card_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    {d : ℕ} (hd : 0 < d) :
    (((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n => d ∣ n)).card : ℝ) ≤
      (v - u) / (d : ℝ) + 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hquot : ⌊u⌋₊ / d ≤ ⌊v⌋₊ / d := Nat.div_le_div_right (Nat.floor_mono huv)
  rw [multiples_Ioc_card (Nat.floor_mono huv), Nat.cast_sub hquot,
    ← Nat.floor_div_natCast u d, ← Nat.floor_div_natCast v d]
  have hv' := Nat.floor_le (div_nonneg (hu.trans huv) hdR.le)
  have hu' := Nat.lt_floor_add_one (u / (d : ℝ))
  rw [sub_div]
  linarith

/-- Page 27, summing positive divisor incidences separates the reciprocal tail
from the one per divisor endpoint rounding error. -/
theorem sum_divisor_counts_le (D : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, ((D.filter (fun d => d ∣ n)).card : ℝ)) ≤
      (v - u) * (∑ d ∈ D, 1 / (d : ℝ)) + (D.card : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, ∑ d ∈ D, if d ∣ n then (1 : ℝ) else 0 := by
      simp only [Finset.sum_boole]
    _ = ∑ d ∈ D, (((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun n => d ∣ n)).card : ℝ) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_boole]
    _ ≤ ∑ d ∈ D, ((v - u) / (d : ℝ) + 1) :=
      Finset.sum_le_sum (fun d hd => interval_multiples_card_le hu huv (hD d hd))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- Pages 26 and 27, the concrete band sum has a reciprocal tail main term
and at most ceiling of gamma z for the endpoint rounding error. -/
theorem roughBand_interval_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (z γ : ℝ) :
    (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, roughBand n z γ) ≤
      (v - u) * (∑ d ∈ (Thm2.primorialBelow z).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ)) + (⌈γ * z⌉₊ : ℝ) := by
  let P := Thm2.primorialBelow z
  let D := P.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)
  have hP : P ≠ 0 := (primorial_squarefree z).ne_zero
  have he (n : ℕ) : roughBand n z γ = ((D.filter (fun d => d ∣ n)).card : ℝ) := by
    have hg : Nat.gcd n P ≠ 0 := by
      intro h
      exact hP (Nat.gcd_eq_zero_iff.mp h).2
    have hset : (Nat.gcd n P).divisors.filter
        (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z) = D.filter (fun d => d ∣ n) := by
      ext d
      simp only [D, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, hg, hP,
        ne_eq, not_false_eq_true, and_true]
      tauto
    simpa only [roughBand, P] using congrArg (fun s : Finset ℕ => (s.card : ℝ)) hset
  have hDpos (d : ℕ) (hd : d ∈ D) : 0 < d :=
    Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hcard : (D.card : ℝ) ≤ (⌈γ * z⌉₊ : ℝ) := by
    apply Nat.cast_le.mpr
    have hsub : D ⊆ Finset.range ⌈γ * z⌉₊ := by
      intro d hd
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (Finset.mem_filter.mp hd).2.2)
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hrecip : (∑ d ∈ D, 1 / (d : ℝ)) ≤
      ∑ d ∈ P.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hd, hlo, hhi⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨hd, hlo⟩
    · intro d hd hnot
      positivity
  simp_rw [he]
  exact (sum_divisor_counts_le D hDpos hu huv).trans
    (add_le_add (mul_le_mul_of_nonneg_left hrecip (sub_nonneg.mpr huv)) hcard)

/-- Page 27, the paper roughness cutoff is eventually below every positive power. -/
theorem roughness_eventually_le_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ x ^ δ := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
    (eventually_lt_nhds hδ)
  filter_upwards [Real.tendsto_log_atTop.eventually h,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (9 / 10 : ℝ) = Real.log x * Real.log x ^ (-(1 / 10 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + -(1 / 10 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  have hb : Real.log x ^ (9 / 10 : ℝ) ≤ δ * Real.log x := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hx.le hl.le]
  rw [Real.rpow_def_of_pos hx0]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Pages 24 and 33, the reference width eventually exceeds every fixed sublinear power. -/
theorem referenceWidth_eventually_ge_power {β : ℝ} (hβ : β < 1) :
    ∀ᶠ x : ℝ in Filter.atTop, x ^ β ≤ referenceWidth x := by
  have hc : 0 < (1 - β) / 3 := by linarith
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually
    (eventually_lt_nhds hc)
  filter_upwards [Real.tendsto_log_atTop.eventually h,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (1 / 3 : ℝ) = Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  have hb : Real.log x * β ≤ Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ) := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hx.le hl.le]
  calc
    _ = Real.exp (Real.log x * β) := Real.rpow_def_of_pos hx0 _
    _ ≤ Real.exp (Real.log x - 3 * Real.log x ^ (1 / 3 : ℝ)) := Real.exp_le_exp.mpr hb
    _ = _ := by
      rw [referenceWidth, sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]
      congr 2
      ring

/-- Page 27, the unweighted intermediate band sum on I1 has every logarithmic saving.
This is the one variable remainder before summing the outer factor coefficients. -/
theorem roughBand_reference_bound {ε A : ℝ} (hε : 0 < ε) (hεu : ε < 1 / 10) (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (∑ n ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        roughBand n (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12))) ≤
        2 * referenceWidth x * Real.log x ^ (-A) := by
  have hr := roughness_eventually_le_power (by norm_num : (0 : ℝ) < 1 / 4)
  have hw := referenceWidth_eventually_ge_power (by norm_num : (3 / 4 : ℝ) < 1)
  have hl := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [reciprocal_tail_every_log hε hA, hr, hw, hl,
    Filter.eventually_ge_atTop (3 : ℝ)] with x htail hr hw hl hx3
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogpow : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have hlogneg : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog.le _
  have hl' : Real.log x ^ A ≤ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hl
  have hγw : x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ x ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (ε / 12) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hx0.le _)
      _ = x ^ (ε / 12 + 1 / 4) := (Real.rpow_add hx0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hceil : (⌈x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) ≤
      2 * x ^ (1 / 2 : ℝ) := by
    have hc := Nat.ceil_lt_add_one (mul_nonneg (Real.rpow_nonneg hx0.le (ε / 12)) (Real.exp_pos (Real.log x ^ (9 / 10 : ℝ))).le)
    have hs : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hsave : 2 * x ^ (1 / 2 : ℝ) ≤ x ^ (3 / 4 : ℝ) * Real.log x ^ (-A) := by
    rw [Real.rpow_neg hlog.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ hlogpow).mpr
    calc
      _ ≤ (2 * x ^ (1 / 2 : ℝ)) * ((1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hl' (by positivity)
      _ = _ := by
        have he : x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hx0]
          norm_num
        nlinarith
  have herr : (⌈x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) ≤
      referenceWidth x * Real.log x ^ (-A) :=
    hceil.trans (hsave.trans (mul_le_mul_of_nonneg_right hw hlogneg))
  have hwidth : 0 < referenceWidth x := referenceWidth_pos hx0
  have hu : 0 ≤ x - referenceWidth x := by linarith [referenceWidth_lt_quarter hx3]
  have hcount := roughBand_interval_le hu (by linarith : x - referenceWidth x ≤ x)
    (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12))
  rw [sub_sub_cancel] at hcount
  have hm := mul_le_mul_of_nonneg_left htail hwidth.le
  nlinarith

/-- Page 27, displays 4.12 and 4.13, the unweighted inner band on the actual interval I.
The factor two in the definition of I is retained.
Outer factor coefficient summation is not asserted. -/
theorem roughBand_short_bound {ε A : ℝ} (hε : 0 < ε) (hεu : ε < 1 / 10) (hA : 0 < A) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (∑ n ∈ DecompC165b.leftInterval ε x,
        roughBand n (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12))) ≤
        3 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  have hr := roughness_eventually_le_power (by norm_num : (0 : ℝ) < 1 / 4)
  have hw := short_width_eventually (show ε < 9 / 20 by linarith)
  have hl := (isLittleO_log_rpow_rpow_atTop A (by norm_num : (0 : ℝ) < 1 / 20)).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [reciprocal_tail_every_log hε hA, hr, hw, hl,
    Filter.eventually_ge_atTop (3 : ℝ)] with x htail hr hw hl hx3
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogpow : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlog _
  have hlogneg : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog.le _
  have hl' : Real.log x ^ A ≤ (1 / 2 : ℝ) * x ^ (1 / 20 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hl
  have hγw : x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ)) ≤ x ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (ε / 12) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hx0.le _)
      _ = x ^ (ε / 12 + 1 / 4) := (Real.rpow_add hx0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hceil : (⌈x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) ≤
      2 * x ^ (1 / 2 : ℝ) := by
    have hc := Nat.ceil_lt_add_one (mul_nonneg (Real.rpow_nonneg hx0.le (ε / 12)) (Real.exp_pos (Real.log x ^ (9 / 10 : ℝ))).le)
    have hs : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have hsave : 2 * x ^ (1 / 2 : ℝ) ≤ x ^ (11 / 20 : ℝ) * Real.log x ^ (-A) := by
    rw [Real.rpow_neg hlog.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ hlogpow).mpr
    calc
      _ ≤ (2 * x ^ (1 / 2 : ℝ)) * ((1 / 2 : ℝ) * x ^ (1 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left hl' (by positivity)
      _ = _ := by
        have he : x ^ (1 / 2 : ℝ) * x ^ (1 / 20 : ℝ) = x ^ (11 / 20 : ℝ) := by
          rw [← Real.rpow_add hx0]
          norm_num
        nlinarith
  have herr : (⌈x ^ (ε / 12) * Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊ : ℝ) ≤
      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have hp : x ^ (11 / 20 : ℝ) ≤ x ^ (11 / 20 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    exact hceil.trans (hsave.trans (mul_le_mul_of_nonneg_right hp hlogneg))
  have hwidth : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hu : 0 ≤ x - 2 * x ^ (11 / 20 + ε) := by linarith
  have hcount := roughBand_interval_le hu
    (by linarith : x - 2 * x ^ (11 / 20 + ε) ≤ x)
    (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12))
  change (∑ n ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊, _) ≤ _
  rw [sub_sub_cancel] at hcount
  have hm := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2 * x ^ (11 / 20 + ε) by positivity)
  nlinarith

end LeanLab.BHP1997.Decomp528f
