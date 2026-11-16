/-
Jia 1996 page 283 display 60.
Source https://doi.org/10.4064/aa-77-3-207-287.
An elementary route to the reciprocal prime power limit from the lab Mertens bounds.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTSieve.MertensLower

namespace LeanLab.Languasco2004.Decomp588d
open Real Finset LeanLab.PNTSieve.Mertens
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 283 display 60 support: finite partial summation on an arbitrary prime block. -/
theorem abel_block (y v : ℕ) (hy : 2 ≤ y) (hyv : y ≤ v) :
    E v - E y = C v / log v - C y / log y +
      ∑ n ∈ Ico y v, C n * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
  induction v, hyv using Nat.le_induction with
  | base => simp
  | succ v hyv ih =>
    have hE : E (v + 1) = E v + c (v + 1) / log ((v : ℝ) + 1) := by
      unfold E
      rw [sum_Icc_succ_top (by omega)]
      push_cast
      ring
    have hC : C (v + 1) = C v + c (v + 1) := by
      unfold C
      rw [sum_Icc_succ_top (by omega)]
    rw [hE, hC, sum_Ico_succ_top hyv]
    push_cast
    linear_combination ih

/-- Page 283 display 60 support: compare the discrete logarithmic kernel with its integral. -/
theorem log_kernel_bounds {l L U : ℝ} (hl : 0 < l) (hlL : l ≤ L) (hLU : L ≤ U)
    (hU : U ≤ L + log 2) :
    l / (l + log 2) * (log U - log L) ≤ L * (1 / L - 1 / U) ∧
      L * (1 / L - 1 / U) ≤ log U - log L := by
  have hL : 0 < L := hl.trans_le hlL
  have hU0 : 0 < U := hL.trans_le hLU
  have h2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hc : l / (l + log 2) ≤ L / U := by
    rw [div_le_div_iff₀ (by positivity) hU0]
    nlinarith
  have hc0 : 0 ≤ l / (l + log 2) := by positivity
  have hδ : 0 ≤ U / L - 1 := by rw [sub_nonneg, le_div_iff₀ hL]; linarith
  have hlog : log U - log L = log (U / L) := (Real.log_div hU0.ne' hL.ne').symm
  have he : L * (1 / L - 1 / U) = 1 - L / U := by field_simp
  constructor
  · rw [hlog]
    calc l / (l + log 2) * log (U / L) ≤ l / (l + log 2) * (U / L - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hU0 hL)) hc0
      _ ≤ (L / U) * (U / L - 1) := mul_le_mul_of_nonneg_right hc hδ
      _ = L * (1 / L - 1 / U) := by field_simp
  · rw [he, hlog]
    simpa only [inv_div] using Real.one_sub_inv_le_log_of_pos (div_pos hU0 hL)

/-- Page 283 display 60 support: reciprocal block sums have two sided logarithmic bounds.
Only the clean elementary estimates log n less seven at most C n at most log n plus seven occur. -/
theorem reciprocal_block_bounds (y v : ℕ) (hy : 2 ≤ y) (hyv : y ≤ v) :
    (log y / (log y + log 2)) * (log (log v) - log (log y)) - 14 / log y ≤ E v - E y ∧
      E v - E y ≤ (log (log v) - log (log y)) + 14 / log y := by
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hvR : (y : ℝ) ≤ v := by exact_mod_cast hyv
  have hly : 0 < log y := Real.log_pos (by linarith)
  have hlv : 0 < log v := Real.log_pos (by linarith)
  have hbL : -(7 / log v) - 7 / log y ≤ C v / log v - C y / log y := by
    have h1 := (div_le_div_of_nonneg_right (C_ge v) hlv.le)
    have h2 := (div_le_div_of_nonneg_right (C_le y (by omega)) hly.le)
    rw [sub_div, div_self hlv.ne'] at h1
    rw [add_div, div_self hly.ne'] at h2
    linarith
  have hbU : C v / log v - C y / log y ≤ 7 / log v + 7 / log y := by
    have h1 := (div_le_div_of_nonneg_right (C_le v (by omega)) hlv.le)
    have h2 := (div_le_div_of_nonneg_right (C_ge y) hly.le)
    rw [add_div, div_self hlv.ne'] at h1
    rw [sub_div, div_self hly.ne'] at h2
    linarith
  have hterms : ∀ n ∈ Ico y v,
      (log y / (log y + log 2)) * (log (log ((n : ℝ) + 1)) - log (log n)) -
        7 * (1 / log n - 1 / log ((n : ℝ) + 1)) ≤
          C n * (1 / log n - 1 / log ((n : ℝ) + 1)) ∧
      C n * (1 / log n - 1 / log ((n : ℝ) + 1)) ≤
        (log (log ((n : ℝ) + 1)) - log (log n)) +
          7 * (1 / log n - 1 / log ((n : ℝ) + 1)) := by
    intro n hn
    have hn' := mem_Ico.mp hn
    have hn2 : 2 ≤ n := hy.trans hn'.1
    have hnR : (y : ℝ) ≤ n := by exact_mod_cast hn'.1
    have hln : log y ≤ log n := Real.log_le_log (by linarith) hnR
    have hln1 : log n ≤ log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
    have hupper : log ((n : ℝ) + 1) ≤ log n + log 2 := by
      rw [← Real.log_mul (by linarith : (n : ℝ) ≠ 0) (by norm_num)]
      apply Real.log_le_log (by linarith)
      linarith
    have hk := log_kernel_bounds hly hln hln1 hupper
    have hd := diff_nonneg hn2
    have hL := mul_le_mul_of_nonneg_right (C_ge n) hd
    have hU := mul_le_mul_of_nonneg_right (C_le n (by omega)) hd
    constructor <;> nlinarith [hk.1, hk.2]
  have hsL := sum_le_sum (fun n hn => (hterms n hn).1)
  have hsU := sum_le_sum (fun n hn => (hterms n hn).2)
  have htel1 : (∑ n ∈ Ico y v, (log (log ((n : ℝ) + 1)) - log (log n))) =
      log (log v) - log (log y) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (sum_Ico_sub (fun n : ℕ => log (log n)) hyv)
  have htel2 : (∑ n ∈ Ico y v, (1 / log n - 1 / log ((n : ℝ) + 1))) =
      1 / log y - 1 / log v := by
    have h := sum_Ico_sub (fun n : ℕ => -(1 / log n)) hyv
    push_cast at h
    simpa only [sub_eq_add_neg, neg_neg, add_comm] using h
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, htel1, htel2] at hsL
  rw [sum_add_distrib, ← mul_sum, htel1, htel2] at hsU
  rw [abel_block y v hy hyv]
  simp only [div_eq_mul_inv] at hbL hbU hsL hsU ⊢
  constructor <;> linarith

/-- Page 283 display 60 support: the partial summation block is exactly the reciprocal prime sum. -/
theorem E_block_eq (y v : ℕ) (hyv : y ≤ v) :
    E v - E y = ∑ p ∈ (Ioc y v).filter Nat.Prime, (1 : ℝ) / p := by
  have hsplit := sum_Ioc_consecutive (fun m : ℕ => c m / log m) (Nat.zero_le y) hyv
  have hinterval (N : ℕ) : Ioc 0 N = Icc 1 N := by
    ext m
    simp only [mem_Ioc, mem_Icc]
    omega
  simp only [hinterval] at hsplit
  change E y + _ = E v at hsplit
  have hE : E v - E y = ∑ m ∈ Ioc y v, c m / log m := by linarith
  rw [hE, sum_filter]
  apply sum_congr rfl
  intro n hn
  unfold c
  split_ifs with hp
  · have hl : 0 < log n := Real.log_pos (by exact_mod_cast hp.one_lt)
    field_simp
  · simp

/-- Page 283 display 60 support: taking natural floors does not change a fixed logarithmic exponent. -/
theorem log_floor_power_ratio (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun Y : ℝ => log (⌊Y ^ a⌋₊ : ℝ) / log Y) Filter.atTop (nhds a) := by
  have hP := tendsto_rpow_atTop ha
  have hF := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hP
  have hLF := hF.log (by norm_num : (1 : ℝ) ≠ 0)
  have hI := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hA := (tendsto_const_nhds (x := a)).add (hLF.mul hI)
  simp only [log_one, zero_mul, add_zero] at hA
  apply hA.congr'
  have hfloor := tendsto_nat_floor_atTop.comp hP
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hfloor.eventually (Filter.eventually_ge_atTop (1 : ℕ))] with Y hY hf
  dsimp only [Function.comp_def] at hf ⊢
  have hY0 : 0 < Y := by linarith
  have hfloor0 : (0 : ℝ) < (⌊Y ^ a⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊Y ^ a⌋₊)
  have hlY := Real.log_pos hY
  rw [Real.log_div hfloor0.ne' (Real.rpow_pos_of_pos hY0 a).ne', Real.log_rpow hY0]
  field_simp
  <;> ring

/-- Jia page 283 display 60: the reciprocal prime power limit follows from elementary Mertens bounds.
No rough count or pair asymptotic is used. -/
theorem reciprocal_power_limit (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Filter.Tendsto (fun Y : ℝ =>
      ∑ p ∈ (Ioc ⌊Y ^ a⌋₊ ⌊Y ^ b⌋₊).filter Nat.Prime, (1 : ℝ) / p)
      Filter.atTop (nhds (log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hA := log_floor_power_ratio a ha
  have hB := log_floor_power_ratio b hb
  have hRatio := hB.div hA ha.ne'
  have hRatio' : Filter.Tendsto (fun Y : ℝ =>
      log (⌊Y ^ b⌋₊ : ℝ) / log (⌊Y ^ a⌋₊ : ℝ)) Filter.atTop (nhds (b / a)) := by
    apply hRatio.congr'
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with Y hY
    have hlY := (Real.log_pos hY).ne'
    change (log (⌊Y ^ b⌋₊ : ℝ) / log Y) / (log (⌊Y ^ a⌋₊ : ℝ) / log Y) = _
    simp only [div_div_div_cancel_right₀ hlY]
  have hLa : Filter.Tendsto (fun Y : ℝ => log (⌊Y ^ a⌋₊ : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp
      (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop ha)))
  have hLb : Filter.Tendsto (fun Y : ℝ => log (⌊Y ^ b⌋₊ : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp
      (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hb)))
  have hR : Filter.Tendsto (fun Y : ℝ =>
      log (log (⌊Y ^ b⌋₊ : ℝ)) - log (log (⌊Y ^ a⌋₊ : ℝ)))
      Filter.atTop (nhds (log (b / a))) := by
    have h := hRatio'.log (div_ne_zero hb.ne' ha.ne')
    apply h.congr'
    filter_upwards [hLa.eventually (Filter.eventually_gt_atTop (0 : ℝ)),
      hLb.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with Y hya hyb
    exact Real.log_div hyb.ne' hya.ne'
  have hInv := tendsto_inv_atTop_zero.comp hLa
  have hErr := hInv.const_mul 14
  simp only [mul_zero] at hErr
  have hCoeff : Filter.Tendsto (fun Y : ℝ => log (⌊Y ^ a⌋₊ : ℝ) /
      (log (⌊Y ^ a⌋₊ : ℝ) + log 2)) Filter.atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (log 2) hLa)).const_mul (log 2))
    simp only [mul_zero, sub_zero] at h
    apply h.congr'
    filter_upwards [hLa.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with Y hy
    have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    change (1 : ℝ) - log 2 * (log (⌊Y ^ a⌋₊ : ℝ) + log 2)⁻¹ = _
    field_simp
    <;> ring
  have hLow := (hCoeff.mul hR).sub hErr
  have hUp := hR.add hErr
  simp only [one_mul, sub_zero, add_zero] at hLow hUp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hUp
  · have hfloor := tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop ha)
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      hfloor.eventually (Filter.eventually_ge_atTop (2 : ℕ))] with Y hY hy
    dsimp only [Function.comp_def] at hy
    have hyv : ⌊Y ^ a⌋₊ ≤ ⌊Y ^ b⌋₊ := Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le hY.le hab)
    have h := (reciprocal_block_bounds _ _ hy hyv).1
    rw [E_block_eq _ _ hyv] at h
    simpa only [Function.comp_def, div_eq_mul_inv] using h
  · have hfloor := tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop ha)
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
      hfloor.eventually (Filter.eventually_ge_atTop (2 : ℕ))] with Y hY hy
    dsimp only [Function.comp_def] at hy
    have hyv : ⌊Y ^ a⌋₊ ≤ ⌊Y ^ b⌋₊ := Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le hY.le hab)
    have h := (reciprocal_block_bounds _ _ hy hyv).2
    rw [E_block_eq _ _ hyv] at h
    simpa only [Function.comp_def, div_eq_mul_inv] using h

#print axioms E_block_eq
#print axioms log_floor_power_ratio
#print axioms reciprocal_power_limit
#print axioms abel_block
#print axioms log_kernel_bounds
#print axioms reciprocal_block_bounds
end
end LeanLab.Languasco2004.Decomp588d
