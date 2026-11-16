/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Separate the two prime summations in journal Lemma 14, pp. 1238 and 1239.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.MassInputs236
import LeanLab.BS2022GRH.Decomp543a

namespace LeanLab.BS2022GRH.Decomp374g
open Real Finset Classical ChenThresholdGRH SliceMass236
open MeasureTheory intervalIntegral
noncomputable section

/-- `n^{1/3} < n` for `1 < n`, so the inner weight's pole lies beyond the slice. -/
private lemma cube_lt_self {N : ℝ} (hN : 1 < N) : N ^ (1 / 3 : ℝ) < N := by
  have h := (Real.rpow_lt_rpow_left_iff hN).mpr (show (1 / 3 : ℝ) < 1 by norm_num)
  rwa [Real.rpow_one] at h

/-! ## 1. Elementary facts at the scale `n ≥ exp (exp 10)` -/

private lemma one_lt_n {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) : (1 : ℝ) < n := by
  have h1 : (1 : ℝ) < exp (exp 10) := by
    have h2 := Real.add_one_le_exp (exp 10)
    have h3 := Real.exp_pos 10
    linarith
  linarith

private lemma n_pos {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) : (0 : ℝ) < n :=
  lt_trans zero_lt_one (one_lt_n hn)

private lemma log_n_pos {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) : (0 : ℝ) < log n := by
  have h1 : (1 : ℝ) < exp 10 := by
    have h2 := Real.add_one_le_exp (10 : ℝ)
    linarith
  have h2 : exp 10 ≤ log n := by
    calc exp 10 = log (exp (exp 10)) := by rw [Real.log_exp]
      _ ≤ log n := Real.log_le_log (Real.exp_pos _) hn
  linarith

private lemma cube_le_n {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) := by
  have h := (Real.rpow_le_rpow_left_iff (one_lt_n hn)).mpr (show (1 / 3 : ℝ) ≤ 1 by norm_num)
  simpa using h

/-! ## 2. `pairWeightSum` splits over the first prime coordinate -/

private lemma fst_mem_Qset {n : ℕ} {ε₁ : ℝ} (hn : exp (exp 10) ≤ (n : ℝ))
    {q : ℕ × ℕ} (hq : q ∈ pairRange n ε₁) : q.1 ∈ U7153.Qset n := by
  obtain ⟨-, hq1, -, hz, hy, -⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨?_, hq1, hz, hy⟩
  rw [Finset.mem_range]
  have hlt : (q.1 : ℝ) < (n : ℝ) :=
    lt_of_lt_of_le hy (by rw [U7153.yy]; exact cube_le_n hn)
  have h2 : q.1 < n := by exact_mod_cast hlt
  omega

/-- The reciprocal pair sum of journal p. 1238, split over `Qset n`: the two prime
summations of Lemma 14 are separate. -/
theorem pairWeightSum_eq_sum_fiber (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    pairWeightSum n ε₁ =
      ∑ p ∈ U7153.Qset n,
        ∑ q ∈ (pairRange n ε₁).filter (fun q => q.1 = p),
          1 / ((q.1 : ℝ) * q.2 * log ((n : ℝ) / ((q.1 : ℝ) * q.2))) := by
  rw [pairWeightSum]
  exact (Finset.sum_fiberwise_of_maps_to (f := fun q : ℕ × ℕ =>
      1 / ((q.1 : ℝ) * q.2 * log ((n : ℝ) / ((q.1 : ℝ) * q.2))))
    (g := fun q : ℕ × ℕ => q.1) (fun q hq => fst_mem_Qset hn hq)).symm

/-! ## 3. The inner weight is `H` on the prime interval -/

/-- `n^{1/3} ≤ √((1+ε)n/p)` for `p ≤ n^{1/3}`, `0 < ε`. -/
private lemma cube_le_sqrt (N p ε : ℝ) (hN : 1 < N) (hp : 1 < p)
    (hpN : p ≤ N ^ (1 / 3 : ℝ)) (hε : 0 < ε) :
    N ^ (1 / 3 : ℝ) ≤ √((1 + ε) * N / p) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hmul : N ^ (2 / 3 : ℝ) * p ≤ N := by
    have h1 : N ^ (2 / 3 : ℝ) * p ≤ N ^ (2 / 3 : ℝ) * N ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hpN (Real.rpow_pos_of_pos hN0 _).le
    have h2 : N ^ (2 / 3 : ℝ) * N ^ (1 / 3 : ℝ) = N := by
      rw [← Real.rpow_add hN0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one]
    linarith
  have hsq : (N ^ (1 / 3 : ℝ)) ^ 2 ≤ (1 + ε) * N / p := by
    have h2 : (N ^ (1 / 3 : ℝ)) ^ 2 = N ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast (N ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hN0.le]
      norm_num
    rw [h2, le_div_iff₀ hp0]
    nlinarith [hN0, hmul]
  calc N ^ (1 / 3 : ℝ) = √((N ^ (1 / 3 : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ √((1 + ε) * N / p) := Real.sqrt_le_sqrt hsq

/-- `√((1+ε)n/p) < n/p`, i.e. the `ε`-boundary lies below the pole of the inner weight. -/
private lemma sqrt_lt_div (N p ε : ℝ) (hN : 1 < N) (hp : 1 < p) (hε : 0 < ε)
    (hx : 1 + ε < N / p) : √((1 + ε) * N / p) < N / p := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hR : (0 : ℝ) < N / p := div_pos hN0 hp0
  have hsq : (1 + ε) * N / p < (N / p) ^ 2 := by
    have : (1 + ε) * (N / p) < N / p * (N / p) := by
      exact mul_lt_mul_of_pos_right hx hR
    calc (1 + ε) * N / p = (1 + ε) * (N / p) := by ring
      _ < N / p * (N / p) := this
      _ = (N / p) ^ 2 := by ring
  have hε0 : (0 : ℝ) < 1 + ε := by linarith
  have hL0 : (0 : ℝ) < (1 + ε) * N / p := by positivity
  calc √((1 + ε) * N / p) < √((N / p) ^ 2) := Real.sqrt_lt_sqrt hL0.le hsq
    _ = N / p := Real.sqrt_sq hR.le

/-- The exact value of the inner integral up to a real upper limit `Y` below `n/p`. -/
private theorem integral_inner_to (N p Y : ℝ) (hN : 1 < N) (hp : 1 < p)
    (hy1 : 1 < N ^ (1 / 3 : ℝ)) (hy : N ^ (1 / 3 : ℝ) ≤ Y) (hY : Y < N / p) :
    (∫ t in N ^ (1 / 3 : ℝ)..Y, 1 / (t * log t * (log N - log p - log t)))
      = kernelPrimitive N p Y - kernelPrimitive N p (N ^ (1 / 3 : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (by linarith : (0 : ℝ) < N ^ (1 / 3 : ℝ)) hy
  have hmem : ∀ t ∈ Set.uIcc (N ^ (1 / 3 : ℝ)) Y,
      1 < t ∧ 0 < log N - log p - log t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hy1 ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlt : t < N / p := lt_of_le_of_lt ht.2 hY
    have hlog : log t < log (N / p) := (log_lt_log_iff ht0 (div_pos hN0 hp0)).mpr hlt
    rw [log_div hN0.ne' hp0.ne'] at hlog
    exact ⟨ht1, by linarith⟩
  have hint : IntervalIntegrable
      (fun t : ℝ => 1 / (t * log t * (log N - log p - log t))) volume (N ^ (1 / 3 : ℝ)) Y := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    obtain ⟨ht1, hgt⟩ := hmem t ht
    have ht0 : t ≠ 0 := by linarith
    have hlt : log t ≠ 0 := (log_pos ht1).ne'
    have hgap : log N - log p - log t ≠ 0 := hgt.ne'
    fun_prop (disch := first | assumption | positivity)
  exact integral_eq_sub_of_hasDerivAt
    (fun t ht => kernelPrimitive_hasDeriv N p t (hmem t ht).1 (hmem t ht).2) hint

/-- The inner integral over `[n^{1/3}, √(n/p)]` is exactly `H n p`, journal p. 1238. -/
private theorem integral_inner_eq_H (N p : ℝ) (hN : 1 < N) (hp : 1 < p)
    (hpN : p ≤ N ^ (1 / 3 : ℝ)) :
    (∫ t in N ^ (1 / 3 : ℝ)..√(N / p), 1 / (t * log t * (log N - log p - log t)))
      = H N p := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hy1 : 1 < N ^ (1 / 3 : ℝ) := by
    have h := (Real.rpow_lt_rpow_left_iff hN).mpr (show (0 : ℝ) < 1 / 3 by norm_num)
    simpa using h
  have hy : N ^ (1 / 3 : ℝ) ≤ √(N / p) := by
    have hmul : N ^ (2 / 3 : ℝ) * p ≤ N := by
      have h1 : N ^ (2 / 3 : ℝ) * p ≤ N ^ (2 / 3 : ℝ) * N ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hpN (Real.rpow_pos_of_pos hN0 _).le
      have h2 : N ^ (2 / 3 : ℝ) * N ^ (1 / 3 : ℝ) = N := by
        rw [← Real.rpow_add hN0, show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one]
      linarith
    have hsq : (N ^ (1 / 3 : ℝ)) ^ 2 ≤ N / p := by
      have h2 : (N ^ (1 / 3 : ℝ)) ^ 2 = N ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_natCast (N ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hN0.le]
        norm_num
      rw [h2, le_div_iff₀ hp0]
      linarith
    calc N ^ (1 / 3 : ℝ) = √((N ^ (1 / 3 : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(N / p) := Real.sqrt_le_sqrt hsq
  have hpNlt : p < N := lt_of_le_of_lt hpN (cube_lt_self hN)
  have h := integral_inner_to N p (√(N / p)) hN hp hy1 hy
    (by
      have hR : (0 : ℝ) < N / p := div_pos hN0 hp0
      have h1 : (1 : ℝ) < N / p := (one_lt_div hp0).mpr hpNlt
      calc √(N / p) < √((N / p) ^ 2) := Real.sqrt_lt_sqrt hR.le (by nlinarith)
        _ = N / p := Real.sqrt_sq hR.le)
  rw [h]
  simp only [kernelPrimitive]
  rw [H]
  have hAY : log N - log p - log (√(N / p)) = log (√(N / p)) := by
    rw [Real.log_sqrt (le_of_lt (div_pos hN0 hp0)), log_div hN0.ne' hp0.ne']
    ring
  rw [hAY]
  have hA : log N - log p ≠ 0 := by
    have hpos : (0 : ℝ) < log N - log p := by
      rw [← log_div hN0.ne' hp0.ne']
      exact log_pos ((one_lt_div hp0).mpr hpNlt)
    exact hpos.ne'
  field_simp
  ring

/-! ## 4. A two-sided logarithm bound -/

/-- `log ((1+s)/(1-s)) ≤ 2s/(1-s²)` for `0 ≤ s ≤ 1/5`, from the third-order Taylor
expansion of `log (1 ± s)` at zero. -/
private lemma log_ratio_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 5) :
    log ((1 + s) / (1 - s)) ≤ 2 * s / (1 - s ^ 2) := by
  have h1 : (0 : ℝ) < 1 - s := by linarith
  have h2 : (0 : ℝ) < 1 + s := by linarith
  have hs1 : |s| < 1 := by rw [abs_of_nonneg hs0]; linarith
  have hneg : |(-s)| < 1 := by rwa [abs_neg]
  have hA := Real.abs_log_sub_add_sum_range_le hneg 4
  have hB := Real.abs_log_sub_add_sum_range_le hs1 4
  have hAsum : (∑ i ∈ Finset.range 4, (-s) ^ (i + 1) / ((i : ℝ) + 1)) =
      -s + s ^ 2 / 2 - s ^ 3 / 3 + s ^ 4 / 4 := by
    simp [Finset.sum_range_succ]
    ring
  have hBsum : (∑ i ∈ Finset.range 4, s ^ (i + 1) / ((i : ℝ) + 1)) =
      s + s ^ 2 / 2 + s ^ 3 / 3 + s ^ 4 / 4 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hAsum, show (1 : ℝ) - -s = 1 + s by ring, abs_neg, abs_of_nonneg hs0] at hA
  rw [hBsum, abs_of_nonneg hs0] at hB
  have hle1 : log (1 + s) ≤ s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / (1 - s) := by
    have := (abs_le.mp hA).2
    linarith
  have hle2 : -log (1 - s) ≤ s + s ^ 2 / 2 + s ^ 3 / 3 + s ^ 4 / 4 + s ^ 5 / (1 - s) := by
    have := (abs_le.mp hB).1
    linarith
  have hq4 : s / (1 - s) ≤ 1 / 4 := by
    rw [div_le_iff₀ h1]
    linarith
  have hrem : s ^ 5 / (1 - s) ≤ s ^ 4 / 4 := by
    have h4 : (0 : ℝ) ≤ s ^ 4 := by positivity
    calc s ^ 5 / (1 - s) = s ^ 4 * (s / (1 - s)) := by field_simp
      _ ≤ s ^ 4 * (1 / 4) := mul_le_mul_of_nonneg_left hq4 h4
      _ = s ^ 4 / 4 := by ring
  have hsum : log ((1 + s) / (1 - s)) ≤ 2 * s + 2 * s ^ 3 / 3 + s ^ 4 / 2 := by
    rw [Real.log_div h2.ne' h1.ne']
    linarith
  have hfin : 2 * s + 2 * s ^ 3 / 3 + s ^ 4 / 2 ≤ 2 * s / (1 - s ^ 2) := by
    have hden : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
    rw [le_div_iff₀ hden]
    nlinarith [hs0, hs, sq_nonneg s, pow_nonneg hs0 3, pow_nonneg hs0 4,
      mul_nonneg hs0 hs0]
  linarith

/-! ## 5. The `ε`-boundary correction, in abstract form -/

/-- The inner boundary term at `√((1+ε)n/p)`, bounded by the first term of `massErrorTail`. -/
private lemma ratio_bound {A c L : ℝ} (hL : 0 < L) (hc0 : 0 < c) (hcL : 15 * c ≤ 2 * L)
    (hA2 : 2 * L / 3 ≤ A) :
    log ((A + c) / (A - c)) / A ≤ (c / 2) / ((L / 3) ^ 2 - (c / 2) ^ 2) := by
  have hA0 : 0 < A := by linarith
  have hcA : c < A := by nlinarith
  set u := c / A with hu
  set s := 3 * c / (2 * L) with hs
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hs_nn : 0 ≤ s := by rw [hs]; positivity
  have hs_half : s ≤ 1 / 5 := by
    rw [hs]
    exact (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)
      (by norm_num : (0 : ℝ) < 5)).mpr (by linarith)
  have hus : u ≤ s := by
    rw [hu, hs]
    exact (div_le_div_iff₀ (by positivity : (0 : ℝ) < A)
      (by positivity : (0 : ℝ) < 2 * L)).mpr (by nlinarith)
  have h1u : (0 : ℝ) < 1 - u := by rw [hu]; rw [sub_pos]; rw [div_lt_one hA0]; exact hcA
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have hrw : (A + c) / (A - c) = (1 + u) / (1 - u) := by
    rw [hu]; field_simp
  have hmono : log ((1 + u) / (1 - u)) ≤ log ((1 + s) / (1 - s)) := by
    apply log_le_log _ _
    · positivity
    · exact (div_le_div_iff₀ h1u h1s).mpr (by nlinarith)
  have hbound := log_ratio_le hs_nn hs_half
  have hdenL : (0 : ℝ) < (L / 3) ^ 2 - (c / 2) ^ 2 := by nlinarith
  have hsval : (c / 2) / ((L / 3) ^ 2 - (c / 2) ^ 2) = 3 * s / (L * (1 - s ^ 2)) := by
    rw [hs]; field_simp
  rw [hrw, hsval]
  have h1 : log ((1 + u) / (1 - u)) / A ≤ log ((1 + s) / (1 - s)) / A :=
    div_le_div_of_nonneg_right hmono hA0.le
  have h2 : log ((1 + s) / (1 - s)) / A ≤ (2 * s / (1 - s ^ 2)) / A :=
    div_le_div_of_nonneg_right hbound hA0.le
  have h3 : (2 * s / (1 - s ^ 2)) / A ≤ 3 * s / (L * (1 - s ^ 2)) := by
    have hpos : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
    refine (div_le_div_iff₀ (by positivity : (0 : ℝ) < A)
      (by positivity : (0 : ℝ) < L * (1 - s ^ 2))).mpr ?_
    have e : 2 * s / (1 - s ^ 2) * (L * (1 - s ^ 2)) = 2 * s * L := by
      field_simp
    rw [e]
    nlinarith [hs_nn, hA2]
  linarith

/-! ## 6. The `ε₁`-extension of the inner integral -/

/-- Extending the inner integral to the slice boundary `√((1+ε)n/p)` costs at most the first
term of `massErrorTail`; journal p. 1238. -/
private theorem integral_inner_le (N p ε : ℝ) (hN : 1 < N) (hp : 1 < p) (hε : 0 < ε)
    (hpN : p ≤ N ^ (1 / 3 : ℝ)) (hx : 1 + ε < N / p)
    (hcL : 15 * log (1 + ε) ≤ 2 * log N) :
    (∫ t in N ^ (1 / 3 : ℝ)..√((1 + ε) * N / p),
        1 / (t * log t * (log N - log p - log t)))
      ≤ H N p + log (√(1 + ε)) / (log (N ^ (1 / 3 : ℝ)) ^ 2 - log (√(1 + ε)) ^ 2) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hL : 0 < log N := log_pos hN
  have hc0 : 0 < log (1 + ε) := log_pos (by linarith)
  have hy1 : 1 < N ^ (1 / 3 : ℝ) := by
    have h := (Real.rpow_lt_rpow_left_iff hN).mpr (show (0 : ℝ) < 1 / 3 by norm_num)
    simpa using h
  have hy : N ^ (1 / 3 : ℝ) ≤ √((1 + ε) * N / p) := cube_le_sqrt N p ε hN hp hpN hε
  have hY : √((1 + ε) * N / p) < N / p := sqrt_lt_div N p ε hN hp hε hx
  have hylog : log (N ^ (1 / 3 : ℝ)) = log N / 3 := by
    rw [Real.log_rpow hN0]; ring
  have hYlog : log (√((1 + ε) * N / p)) = (log N - log p + log (1 + ε)) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_div (by positivity) hp0.ne',
      Real.log_mul (by linarith : (1 + ε) ≠ 0) hN0.ne']
    ring
  have hpNlt : p < N := lt_of_le_of_lt hpN (cube_lt_self hN)
  have hlogp : log p ≤ log N / 3 := by
    have h1 : log p ≤ log (N ^ (1 / 3 : ℝ)) := log_le_log hp0 hpN
    rwa [hylog] at h1
  have hApos : 0 < log N - log p := by
    have hpos : (0 : ℝ) < log N - log p := by
      rw [← log_div hN0.ne' hp0.ne']
      exact log_pos ((one_lt_div hp0).mpr hpNlt)
    exact hpos
  have hAcpos : 0 < (log N - log p) - log (1 + ε) := by
    have h3 : log (1 + ε) ≤ log N / 3 := by linarith
    linarith
  have hcomb : log (((log N - log p) + log (1 + ε)) / 2) -
      log (((log N - log p) - log (1 + ε)) / 2) =
      log (((log N - log p) + log (1 + ε)) / ((log N - log p) - log (1 + ε))) := by
    have hx0 : ((log N - log p) + log (1 + ε)) ≠ 0 := by linarith
    have hy0 : ((log N - log p) - log (1 + ε)) ≠ 0 := hAcpos.ne'
    rw [Real.log_div hx0 (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hy0 (by norm_num : (2 : ℝ) ≠ 0), Real.log_div hx0 hy0]
    ring
  have hclosed : (∫ t in N ^ (1 / 3 : ℝ)..√((1 + ε) * N / p),
        1 / (t * log t * (log N - log p - log t)))
      = H N p + log ((log N - log p + log (1 + ε)) / (log N - log p - log (1 + ε))) /
          (log N - log p) := by
    rw [integral_inner_to N p (√((1 + ε) * N / p)) hN hp hy1 hy hY]
    simp only [kernelPrimitive]
    rw [H, hYlog, hylog]
    have e1 : (log N - log p) - (log N - log p + log (1 + ε)) / 2 =
        ((log N - log p) - log (1 + ε)) / 2 := by ring
    rw [e1, hcomb]
    field_simp
    ring
  rw [hclosed]
  have hlogsqrt : log (√(1 + ε)) = log (1 + ε) / 2 := Real.log_sqrt (by linarith)
  have hA2 : 2 * log N / 3 ≤ log N - log p := by
    have h3 : log p ≤ log (N ^ (1 / 3 : ℝ)) := log_le_log hp0 hpN
    rw [hylog] at h3
    linarith
  have hb := ratio_bound (A := log N - log p) (c := log (1 + ε)) (L := log N) hL hc0 hcL hA2
  rw [hlogsqrt, hylog]
  linarith
/-! ## 7. The inner bound at the leaf's scale, in `massErrorTail` form -/

private lemma log_yy_eq {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    log (U7153.yy n) = log n / 3 := by
  rw [U7153.yy, Real.log_rpow (n_pos hn)]; ring

private lemma log_zz_eq {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    log (U7153.zz n) = log n / 8 := by
  rw [U7153.zz, Real.log_rpow (n_pos hn)]; ring

/-- `exp 10 ≥ 3000`, by the Taylor series. -/
private lemma exp_ten_ge_3000 : (3000 : ℝ) ≤ exp 10 := by
  have h := Real.sum_le_exp_of_nonneg (x := (10 : ℝ)) (by norm_num) 8
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma log_n_ge_3000 {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    (3000 : ℝ) ≤ log n := by
  have h2 : exp 10 ≤ log n := by
    calc exp 10 = log (exp (exp 10)) := by rw [Real.log_exp]
      _ ≤ log n := Real.log_le_log (Real.exp_pos _) hn
  have h3 := exp_ten_ge_3000
  linarith

private lemma log_arg_small {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ))
    {ε₁ : ℝ} (hε : 0 < ε₁) (hε1 : ε₁ < 1) : 15 * log (1 + ε₁) ≤ 2 * log n := by
  have hL : (3000 : ℝ) ≤ log n := log_n_ge_3000 hn
  have hc : log (1 + ε₁) ≤ log 2 := by
    apply log_le_log (by linarith) (by linarith)
  have h2 : log 2 ≤ 0.7 := by
    have h := Real.log_two_lt_d9
    linarith
  nlinarith

/-- The inner integral over the `ε₁`-slice boundary is at most `H n p` plus one
`massErrorTail`, journal p. 1238. -/
private theorem integral_inner_le_tail (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ))
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (p : ℕ) (hp : p ∈ U7153.Qset n) :
    (∫ t in U7153.yy n..√((1 + ε₁) * (n : ℝ) / p),
        1 / (t * log t * (log n - log p - log t)))
      ≤ H n p + massErrorTail n ε₁ := by
  obtain ⟨-, hpp, hzp, hyp⟩ := Finset.mem_filter.mp hp
  have hN1 : (1 : ℝ) < n := one_lt_n hn
  have hN0 : (0 : ℝ) < n := n_pos hn
  have hp1 : (1 : ℝ) < p := by
    have := hpp.two_le
    exact_mod_cast this
  have hpN : (p : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := le_of_lt (by rw [← U7153.yy]; exact hyp)
  have hpnn : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hlogp : log p ≤ log n / 3 := by
    have h1 : log (p : ℝ) ≤ log ((n : ℝ) ^ (1 / 3 : ℝ)) := log_le_log hpnn hpN
    rwa [Real.log_rpow hN0, show (1 / 3 : ℝ) * log n = log n / 3 by ring] at h1
  have hx : 1 + ε₁ < (n : ℝ) / p := by
    have hR : (0 : ℝ) < (n : ℝ) / p := div_pos hN0 hpnn
    have h1 : (0 : ℝ) < 1 + ε₁ := by linarith
    rw [← Real.log_lt_log_iff h1 hR, log_div hN0.ne' hpnn.ne']
    have hc : log (1 + ε₁) ≤ log 2 := log_le_log (by linarith) (by linarith)
    have h2 : log 2 ≤ 0.7 := by
      have h := Real.log_two_lt_d9
      linarith
    have hL := log_n_ge_3000 hn
    linarith
  have hcL := log_arg_small hn hε hε1
  have h := integral_inner_le (n : ℝ) p ε₁ hN1 hp1 hε hpN hx hcL
  change (∫ t in (n : ℝ) ^ (1 / 3 : ℝ)..√((1 + ε₁) * (n : ℝ) / p),
        1 / (t * log t * (log n - log p - log t)))
      ≤ H (n : ℝ) p + massErrorTail n ε₁
  have htail : massErrorTail n ε₁ =
      log (√(1 + ε₁)) / (log ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 - log (√(1 + ε₁)) ^ 2) +
        27 / (log n) ^ 3 := by
    unfold massErrorTail
    simp only [U7153.yy]
  have h27 : 0 ≤ 27 / (log n) ^ 3 := by
    have := log_n_pos hn
    positivity
  linarith

/-! ## 8. The `Qset` reciprocal sum from the two-sided Mertens input -/

private lemma zz_le_yy' {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) : U7153.zz n ≤ U7153.yy n := by
  rw [U7153.zz, U7153.yy, Real.rpow_le_rpow_left_iff (one_lt_n hn)]
  norm_num

/-- `⌊zz n⌋₊ ≥ log³ n` at the leaf's scale (`zz n = exp (log n / 8)`); the boundary index
costs less than `27/log²n`. -/
private lemma floor_zz_ge_log_cube {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    (log n) ^ 3 ≤ (⌊U7153.zz n⌋₊ : ℝ) := by
  have hL : (3000 : ℝ) ≤ log n := log_n_ge_3000 hn
  have hLpos : (0 : ℝ) < log n := by linarith
  have hzz : U7153.zz n = exp (log n / 8) := by
    rw [U7153.zz, Real.rpow_def_of_pos (n_pos hn)]
    norm_num
    ring
  have hE : 2 * (log n) ^ 3 ≤ exp (log n / 8) := by
    have h1 := Real.pow_div_factorial_le_exp (x := log n / 8) (by linarith) 5
    have hfac : (Nat.factorial 5 : ℝ) = 120 := by norm_num
    rw [hfac] at h1
    have h5 : (log n / 8) ^ 5 = (log n) ^ 5 / 32768 := by
      rw [div_pow]
      norm_num
    have h2 : 2 * (log n) ^ 3 ≤ (log n / 8) ^ 5 / 120 := by
      rw [h5]
      have hL2 : (7864320 : ℝ) ≤ (log n) ^ 2 := by nlinarith [hL]
      have hL3 : (0 : ℝ) < (log n) ^ 3 := by positivity
      have hmul : (7864320 : ℝ) * (log n) ^ 3 ≤ (log n) ^ 2 * (log n) ^ 3 :=
        mul_le_mul_of_nonneg_right hL2 hL3.le
      have he : (log n) ^ 2 * (log n) ^ 3 = (log n) ^ 5 := by ring
      rw [he] at hmul
      linarith
    linarith
  have hzz2 : 2 ≤ U7153.zz n := by
    rw [hzz]
    have h1 : log n / 8 + 1 ≤ exp (log n / 8) := Real.add_one_le_exp _
    have h2 : (0 : ℝ) < log n / 8 := by linarith
    linarith
  have h1 : (log n) ^ 3 ≤ U7153.zz n / 2 := by
    rw [hzz]
    linarith
  have h2 : U7153.zz n - 1 < (⌊U7153.zz n⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (U7153.zz n)
    linarith
  have h3 : U7153.zz n / 2 ≤ U7153.zz n - 1 := by linarith
  linarith

private lemma log_ratio_zz_yy {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    log (log (U7153.yy n)) - log (log (U7153.zz n)) = log (8 / 3) := by
  have hL := log_n_pos hn
  rw [log_yy_eq hn, log_zz_eq hn, ← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- `Qset n` is the prime range `(⌊n^{1/8}⌋, ⌊n^{1/3}⌋]` up to the single boundary index. -/
private lemma Qset_subset_insert {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) :
    U7153.Qset n ⊆ insert ⌊U7153.zz n⌋₊
      ((Finset.Ioc ⌊U7153.zz n⌋₊ ⌊U7153.yy n⌋₊).filter Nat.Prime) := by
  intro p hp
  obtain ⟨-, hpp, hzp, hyp⟩ := Finset.mem_filter.mp hp
  have hzz0 : (0 : ℝ) < U7153.zz n := Real.rpow_pos_of_pos (n_pos hn) _
  by_cases hle : p ≤ ⌊U7153.zz n⌋₊
  · have hge : ⌊U7153.zz n⌋₊ ≤ p := by
      have h1 : (⌊U7153.zz n⌋₊ : ℝ) ≤ U7153.zz n := Nat.floor_le hzz0.le
      exact_mod_cast le_trans h1 hzp
    rw [le_antisymm hle hge]
    exact Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpp⟩)
    · exact Nat.lt_of_not_le hle
    · exact Nat.le_floor (le_of_lt (by simpa only [U7153.yy] using hyp))

/-- `Σ_{p ∈ Qset n} 1/p ≤ log (8/3) + 64/log²n` from the two-sided Mertens bound with `2κ ≤ 1`.
The slack `64/log²n = 1/log²(n^{1/8})` is exactly the `2κ/log²` of the input at `n^{1/8}`. -/
private theorem sum_Qset_recip_le (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (c κ : ℝ)
    (hκ : 0 ≤ κ) (hκ1 : 2 * κ ≤ 1)
    (hS : ∀ t : ℝ, U7153.zz n ≤ t → t ≤ U7153.yy n →
      |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then (1 : ℝ) / k else 0)) - (log (log t) + c)| ≤
        κ / log t ^ 2) :
    (∑ p ∈ U7153.Qset n, (1 : ℝ) / p) ≤ log (8 / 3) + 64 / (log n) ^ 2 := by
  have hn1 : (1 : ℝ) < n := one_lt_n hn
  have hL := log_n_pos hn
  have hL22 := log_n_ge_3000 hn
  have hzy : U7153.zz n ≤ U7153.yy n := zz_le_yy' hn
  have hzz0 : (0 : ℝ) < U7153.zz n := Real.rpow_pos_of_pos (n_pos hn) _
  have hcube := floor_zz_ge_log_cube hn
  -- step 1: the boundary index plus the half-open prime range
  have hstep1 : (∑ p ∈ U7153.Qset n, (1 : ℝ) / p) ≤
      1 / (⌊U7153.zz n⌋₊ : ℝ) +
        ∑ p ∈ (Finset.Ioc ⌊U7153.zz n⌋₊ ⌊U7153.yy n⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg (Qset_subset_insert hn)
      (fun x _ _ => (div_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (Nat.cast_nonneg x) :
        (0 : ℝ) ≤ 1 / (x : ℝ)))
    rwa [Finset.sum_insert (by simp)] at h1
  -- step 2: the half-open prime sum is `S (yy n) - S (zz n)`
  have hsplit : (∑ k ∈ Finset.Icc 0 ⌊U7153.yy n⌋₊, (if k.Prime then (1 : ℝ) / k else 0)) =
      (∑ k ∈ Finset.Icc 0 ⌊U7153.zz n⌋₊, (if k.Prime then (1 : ℝ) / k else 0)) +
        ∑ p ∈ (Finset.Ioc ⌊U7153.zz n⌋₊ ⌊U7153.yy n⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    have hle : ⌊U7153.zz n⌋₊ ≤ ⌊U7153.yy n⌋₊ := Nat.floor_mono hzy
    have hun : Finset.Icc 0 ⌊U7153.yy n⌋₊ =
        Finset.Icc 0 ⌊U7153.zz n⌋₊ ∪ Finset.Ioc ⌊U7153.zz n⌋₊ ⌊U7153.yy n⌋₊ := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    rw [hun, Finset.sum_union (Finset.disjoint_left.mpr (by
      intro k hk hk'
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_Ioc] at hk'
      omega))]
    congr 1
    rw [Finset.sum_filter]
  -- step 3: the two endpoint bounds and the log ratio
  have hy := hS (U7153.yy n) hzy le_rfl
  have hz := hS (U7153.zz n) le_rfl hzy
  have e1 := log_ratio_zz_yy hn
  have e2 : κ / log (U7153.yy n) ^ 2 + κ / log (U7153.zz n) ^ 2 = κ * 73 / (log n) ^ 2 := by
    have hL := log_n_pos hn
    rw [log_yy_eq hn, log_zz_eq hn]
    field_simp
    ring
  have hIoc : (∑ p ∈ (Finset.Ioc ⌊U7153.zz n⌋₊ ⌊U7153.yy n⌋₊).filter Nat.Prime,
      (1 : ℝ) / p) ≤ log (8 / 3) + 36.5 / (log n) ^ 2 := by
    have h1 := (abs_le.mp hy).2
    have h2 := (abs_le.mp hz).1
    have h3 : κ * 73 ≤ 36.5 := by nlinarith
    have hpos : (0 : ℝ) < (log n) ^ 2 := by positivity
    have h4 : κ * 73 / (log n) ^ 2 ≤ 36.5 / (log n) ^ 2 :=
      div_le_div_of_nonneg_right h3 hpos.le
    linarith
  have hb : 1 / (⌊U7153.zz n⌋₊ : ℝ) ≤ 27 / (log n) ^ 2 := by
    have hpos : (0 : ℝ) < (log n) ^ 2 := by positivity
    have hb0 : (0 : ℝ) < (⌊U7153.zz n⌋₊ : ℝ) := by
      have h1 : (1 : ℝ) ≤ (log n) ^ 3 := by
        have h3 : (1 : ℝ) ≤ log n := by linarith
        nlinarith
      linarith
    rw [div_le_div_iff₀ hb0 hpos]
    have h2 : (log n) ^ 2 ≤ (log n) ^ 3 := by
      have h3 : (1 : ℝ) ≤ log n := by linarith
      calc (log n) ^ 2 = (log n) ^ 2 * 1 := by ring
        _ ≤ (log n) ^ 2 * log n := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (log n) ^ 3 := by ring
    nlinarith [h2, hcube]
  have hpos : (0 : ℝ) < (log n) ^ 2 := by positivity
  have hsum : 27 / (log n) ^ 2 + 36.5 / (log n) ^ 2 = 63.5 / (log n) ^ 2 := by
    rw [← add_div]; norm_num
  have hfin : (63.5 : ℝ) / (log n) ^ 2 ≤ 64 / (log n) ^ 2 := by
    apply div_le_div_of_nonneg_right (by norm_num) hpos.le
  linarith

/-! ## 9. The two-sided Mertens inequality, pointwise in the summation endpoint

The file's import proves Rosser-Schoenfeld Theorem 5 for the floor cumulative prime sum.
`greaves_prime_variation` then uses one uniform error `1/(2 log²a)` on the whole interval.
For the inner variable the endpoint error has to be taken at `log b` (the `ε₁`-boundary
`√((1+ε₁)n/p)`), because with `b = √(n/p)` the `27/log³n` of `massErrorTail` is exactly
`H b / log²(n^{1/3})`; see `inner_fiber_error` below. -/

private theorem mertens_pointwise (B : ℝ)
    (hlo : ∀ y : ℝ, 1 < y → log (log y) + B - 1 / (2 * log y ^ 2) <
      ∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p)
    (hup : ∀ y : ℝ, 286 ≤ y → (∑ p ∈ Nat.primesLE ⌊y⌋₊, (1 : ℝ) / p) <
      log (log y) + B + 1 / (2 * log y ^ 2)) :
    ∀ t : ℝ, 286 ≤ t →
      |(∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)| ≤
        1 / (2 * log t ^ 2) :=
  fun t ht => by
    simpa only [sub_sub] using Decomp543a.mertens_strict_error B t ht hlo hup

/-- Abel summation over the primes with the Mertens error kept pointwise: the lower endpoint
costs `H b / (2 log²b)`, the upper one `H b / (2 log²a)`. This is
`greaves_prime_variation` with the uniform error replaced by the pointwise one at `b`,
which is what the `ε₁`-boundary of the inner prime sum needs. -/
private theorem prime_abel_pointwise (H H' : ℝ → ℝ) (a b B : ℝ)
    (ha : 286 ≤ a) (hab : a ≤ b)
    (hd : ∀ t ∈ Set.uIcc a b, HasDerivAt H (H' t) t)
    (hi : IntervalIntegrable H' volume a b)
    (hH0 : ∀ t ∈ Set.Icc a b, 0 ≤ H t)
    (hH'0 : ∀ t ∈ Set.Icc a b, 0 ≤ H' t)
    (hm : ∀ t : ℝ, 286 ≤ t →
      |(∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)| ≤ 1 / (2 * log t ^ 2)) :
    (∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p) ≤
      (∫ t in a..b, H t / (t * log t)) + H b / (2 * log b ^ 2) + H b / (2 * log a ^ 2) := by
  have ha1 : 1 < a := by linarith
  have hdA : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => log (log t) + B) (1 / (t * log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha1.trans_le ht.1
    have ht0 : 0 < t := by linarith
    convert (hasDerivAt_log_log ht0.ne' (by linarith) (by linarith)).add_const B using 1
    simp only [div_eq_mul_inv, mul_inv, one_mul]
  have hAc : ContinuousOn (fun t : ℝ => log (log t) + B) (Set.uIcc a b) :=
    continuousOn_of_forall_continuousAt (fun t ht => (hdA t ht).continuousAt)
  have hiA : IntervalIntegrable (fun t : ℝ => 1 / (t * log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha1.trans_le ht.1
    have ht0 : t ≠ 0 := ne_of_gt (by linarith)
    have hlt : log t ≠ 0 := (log_pos ht1).ne'
    have hden : t * log t ≠ 0 := mul_ne_zero ht0 hlt
    fun_prop
  have hiHA : IntervalIntegrable (fun t : ℝ => H' t * (log (log t) + B)) volume a b :=
    hi.mul_continuousOn hAc
  have hiS : IntervalIntegrable
      (fun t : ℝ => H' t * ∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) volume a b := by
    have hs := IntervalIntegrable.sum (Nat.primesBelow ⌈b⌉₊)
      (fun p _ => Decomp543a.abel_atom_integrable H' a b p (1 / p) hi)
    apply hs.congr
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    simp only [Finset.sum_apply]
    rw [← Decomp543a.prime_cumulative_restrict t b ht.2, mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    split_ifs <;> simp
  have hbd : ∀ t ∈ Set.Icc a b,
      |(∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)| ≤
        1 / (2 * log t ^ 2) := fun t ht => hm t (ha.trans ht.1)
  have habel := Decomp543a.prime_abel_strict H H' a b hab hd hi
  have hip := integral_mul_deriv_eq_deriv_mul hd hdA hi hiA
  have hid : (∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p)
        - (∫ t in a..b, H t * (1 / (t * log t)))
      = H b * ((∑ p ∈ Nat.primesBelow ⌈b⌉₊, (1 : ℝ) / p) - (log (log b) + B))
        - H a * ((∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) - (log (log a) + B))
        - ∫ t in a..b, H' t *
            ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)) := by
    have hsplit : (∫ t in a..b, H' t *
          ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)))
        = (∫ t in a..b, H' t * (∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p))
          - ∫ t in a..b, H' t * (log (log t) + B) := by
      rw [← integral_sub hiS hiHA]
      congr 1
      ext t
      ring
    have hmodel : (∫ t in a..b, H t * (1 / (t * log t)))
        = H b * (log (log b) + B) - H a * (log (log a) + B)
          - ∫ t in a..b, H' t * (log (log t) + B) := by linarith [hip]
    rw [hsplit, hmodel, habel]
    ring
  have hb0 : 0 ≤ H b := hH0 b ⟨hab, le_rfl⟩
  have ha0 : 0 ≤ H a := hH0 a ⟨le_rfl, hab⟩
  have hlow : H b * ((∑ p ∈ Nat.primesBelow ⌈b⌉₊, (1 : ℝ) / p) - (log (log b) + B)) ≤
      H b / (2 * log b ^ 2) := by
    have h1 := hbd b ⟨hab, le_rfl⟩
    calc H b * ((∑ p ∈ Nat.primesBelow ⌈b⌉₊, (1 : ℝ) / p) - (log (log b) + B))
        ≤ H b * |(∑ p ∈ Nat.primesBelow ⌈b⌉₊, (1 : ℝ) / p) - (log (log b) + B)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hb0
      _ ≤ H b * (1 / (2 * log b ^ 2)) := mul_le_mul_of_nonneg_left h1 hb0
      _ = H b / (2 * log b ^ 2) := by ring
  have hhigh : -H a * ((∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) - (log (log a) + B)) ≤
      H a / (2 * log a ^ 2) := by
    have h1 := hbd a ⟨le_rfl, hab⟩
    calc -H a * ((∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) - (log (log a) + B))
        = -(H a * ((∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) - (log (log a) + B))) := by ring
      _ ≤ |H a * ((∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) - (log (log a) + B))| :=
          neg_le_abs _
      _ = H a * |(∑ p ∈ Nat.primesBelow ⌈a⌉₊, (1 : ℝ) / p) - (log (log a) + B)| := by
          rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ H a * (1 / (2 * log a ^ 2)) := mul_le_mul_of_nonneg_left h1 ha0
      _ = H a / (2 * log a ^ 2) := by ring
  have hint : -(∫ t in a..b, H' t *
        ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)))
      ≤ (H b - H a) / (2 * log a ^ 2) := by
    have hla : 0 < log a := log_pos ha1
    have hint_eq : (∫ t in a..b, H' t) = H b - H a :=
      integral_eq_sub_of_hasDerivAt hd hi
    have hstep : |(∫ t in a..b, H' t *
        ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)))|
        ≤ ∫ t in a..b, H' t * (1 / (2 * log a ^ 2)) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (μ := volume) (f := fun t => H' t *
        ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)))
        (g := fun t => H' t * (1 / (2 * log a ^ 2))) hab
        (Filter.Eventually.of_forall ?_) (hi.mul_const _)
      intro t ht
      have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, ht.2⟩
      have h1 := hbd t htI
      have hh : 0 ≤ H' t := hH'0 t htI
      have hla' : 0 < log a := hla
      have hle : log a ≤ log t := log_le_log (by linarith) ht.1.le
      have h4 : 1 / (2 * log t ^ 2) ≤ 1 / (2 * log a ^ 2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left (h1.trans h4) hh
    rw [intervalIntegral.integral_mul_const, hint_eq] at hstep
    have hfin : (H b - H a) * (1 / (2 * log a ^ 2)) = (H b - H a) / (2 * log a ^ 2) := by ring
    rw [hfin] at hstep
    calc -(∫ t in a..b, H' t * ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)))
        ≤ |(∫ t in a..b, H' t * ((∑ p ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / p) - (log (log t) + B)))| :=
          neg_le_abs _
      _ ≤ _ := hstep
  have hsum := hid
  have hmain : (∑ p ∈ (Nat.primesBelow ⌈b⌉₊).filter (fun p : ℕ => a ≤ (p : ℝ)), H p / p)
      ≤ (∫ t in a..b, H t * (1 / (t * log t))) + H b / (2 * log b ^ 2) + H a / (2 * log a ^ 2)
        + (H b - H a) / (2 * log a ^ 2) := by linarith [hid, hlow, hhigh, hint]
  have hcollapse : H a / (2 * log a ^ 2) + (H b - H a) / (2 * log a ^ 2) = H b / (2 * log a ^ 2) := by
    rw [← add_div]
    ring
  have hdiv : (∫ t in a..b, H t * (1 / (t * log t))) = ∫ t in a..b, H t / (t * log t) := by
    congr 1
    ext t
    ring
  rw [hdiv] at hmain
  linarith [hcollapse]


/-! ## 10. The inner prime sum in the second prime variable, journal p. 1238 -/

/-- `286 ≤ n^{1/3}` at the file's scale. -/
private lemma yy_ge_286 {n : ℕ} (hn : exp (exp 10) ≤ (n : ℝ)) : 286 ≤ U7153.yy n := by
  have hL3 : (3000 : ℝ) ≤ log (n : ℝ) := log_n_ge_3000 hn
  have h4 : (1000 : ℝ) ≤ log (n : ℝ) / 3 := by linarith
  have h5 : (286 : ℝ) ≤ exp (1000 : ℝ) := by
    have h := Real.add_one_le_exp (1000 : ℝ)
    linarith
  have h6 : exp (1000 : ℝ) ≤ exp (log (n : ℝ) / 3) := Real.exp_le_exp.mpr h4
  have hpn : (0 : ℝ) < (n : ℝ) := n_pos hn
  rw [U7153.yy, Real.rpow_def_of_pos hpn]
  calc (286 : ℝ) ≤ exp (1000 : ℝ) := h5
    _ ≤ exp (log (n : ℝ) / 3) := h6
    _ = exp (log (n : ℝ) * (1 / 3)) := by
        congr 1
        ring

/-- `1 + ε₁ < n/p` at the file's scale, so the `ε₁`-boundary stays below the pole. -/
private lemma one_add_eps_lt_div {n p : ℕ} {ε₁ : ℝ}
    (hn : exp (exp 10) ≤ (n : ℝ)) (hp : (1 : ℝ) < (p : ℝ))
    (hlogp : log (p : ℝ) ≤ log (n : ℝ) / 3) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    1 + ε₁ < (n : ℝ) / p := by
  have hN0 : (0 : ℝ) < n := n_pos hn
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hR : (0 : ℝ) < (n : ℝ) / p := div_pos hN0 hp0
  rw [← Real.log_lt_log_iff (by linarith) hR, Real.log_div hN0.ne' (ne_of_gt hp0)]
  have hc : log (1 + ε₁) ≤ log 2 := log_le_log (by linarith) (by linarith)
  have h2 : log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hL := log_n_ge_3000 hn
  linarith

set_option maxHeartbeats 2000000 in
/-- The inner prime summation of journal p. 1238: for one `p` in `Qset n` the sum over the
second prime variable is at most `H n p` plus one `massErrorTail`, up to a `c²/log⁵n` slack
(`c = log (1+ε₁)`), which the `64/log²n` of the reciprocal sum absorbs. -/
private theorem inner_fiber_le (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ))
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (B : ℝ)
    (hm : ∀ t : ℝ, 286 ≤ t →
      |(∑ k ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / k) - (log (log t) + B)| ≤ 1 / (2 * log t ^ 2))
    (p : ℕ) (hp : p ∈ U7153.Qset n) :
    (∑ q ∈ (Nat.primesBelow ⌈√((1 + ε₁) * (n : ℝ) / p)⌉₊).filter
        (fun q : ℕ => U7153.yy n ≤ (q : ℝ)),
        1 / ((q : ℝ) * log ((n : ℝ) / ((p : ℝ) * (q : ℝ)))))
      ≤ H (n : ℝ) (p : ℝ) + massErrorTail n ε₁ + 100 * log (1 + ε₁) ^ 2 / (log n) ^ 5 := by
  obtain ⟨-, hpp, hzp, hyp⟩ := Finset.mem_filter.mp hp
  have hn1 : (1 : ℝ) < n := one_lt_n hn
  have hn0 : (0 : ℝ) < n := n_pos hn
  have hL : 0 < log n := log_n_pos hn
  have hL3 : (3000 : ℝ) ≤ log n := log_n_ge_3000 hn
  have hp2 : 2 ≤ p := hpp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hc07 : log (1 + ε₁) ≤ 0.7 := by
    have h1 : log (1 + ε₁) ≤ log 2 := log_le_log (by linarith) (by linarith)
    linarith [Real.log_two_lt_d9]
  have hlogp : log (p : ℝ) < log n / 3 := by
    have h1 : log (p : ℝ) < log (U7153.yy n) := log_lt_log (by linarith) hyp
    rwa [log_yy_eq hn] at h1
  have hpN : (p : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := le_of_lt (by rw [← U7153.yy]; exact hyp)
  have hpNn : (p : ℝ) ≤ (n : ℝ) := by
    have := cube_le_n hn
    linarith
  have hone : (1 : ℝ) < U7153.yy n := by
    have := yy_ge_286 hn
    linarith
  have hX : U7153.yy n ≤ √((1 + ε₁) * (n : ℝ) / p) := by
    rw [U7153.yy]
    exact cube_le_sqrt (n : ℝ) p ε₁ hn1 hp1 hpN hε
  have hXn : (n : ℝ) ^ (1 / 3 : ℝ) ≤ √((1 + ε₁) * (n : ℝ) / p) := by
    rw [← U7153.yy]; exact hX
  have hx : 1 + ε₁ < (n : ℝ) / p :=
    one_add_eps_lt_div hn hp1 (le_of_lt hlogp) hε hε1
  have hb : √((1 + ε₁) * (n : ℝ) / p) < (n : ℝ) / p :=
    sqrt_lt_div (n : ℝ) p ε₁ hn1 hp1 hε hx
  have hlogX : log (√((1 + ε₁) * (n : ℝ) / p)) =
      (log (n : ℝ) - log (p : ℝ) + log (1 + ε₁)) / 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_div (by positivity) (ne_of_gt hp0),
      Real.log_mul (by linarith : (1 + ε₁) ≠ 0) (ne_of_gt hn0)]
    ring
  have hlogyy : log (U7153.yy n) = log n / 3 := log_yy_eq hn
  have hgt : ∀ t ∈ Set.Icc (U7153.yy n) (√((1 + ε₁) * (n : ℝ) / p)),
      0 < log (n : ℝ) - log (p : ℝ) - log t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (lt_of_lt_of_le hone ht.1)
    have hlt : t < (n : ℝ) / p := lt_of_le_of_lt ht.2 hb
    have hlogt : log t < log ((n : ℝ) / p) :=
      (log_lt_log_iff ht0 (div_pos hn0 hp0)).mpr hlt
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hp0)] at hlogt
    linarith
  have hdv : ∀ t ∈ Set.uIcc (U7153.yy n) (√((1 + ε₁) * (n : ℝ) / p)),
      HasDerivAt (fun t : ℝ => 1 / (log (n : ℝ) - log (p : ℝ) - log t))
        (1 / (t * (log (n : ℝ) - log (p : ℝ) - log t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have hne : log (n : ℝ) - log (p : ℝ) - log t ≠ 0 := ne_of_gt (hgt t ht)
    have ht0 : t ≠ 0 :=
      ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le hone ht.1))
    have hin : HasDerivAt (fun t : ℝ => log (n : ℝ) - log (p : ℝ) - log t) (-(1 / t)) t := by
      have h1 : HasDerivAt (fun t : ℝ => log (n : ℝ) - log (p : ℝ) - log t) (0 - 0 - t⁻¹) t :=
        ((hasDerivAt_const t (log (n : ℝ))).sub (hasDerivAt_const t (log (p : ℝ)))).sub
          (hasDerivAt_log ht0)
      simpa using h1
    have hinv := hin.inv hne
    have hfun : (fun t : ℝ => 1 / (log (n : ℝ) - log (p : ℝ) - log t))
        = fun t : ℝ => (log (n : ℝ) - log (p : ℝ) - log t)⁻¹ := by
      funext x
      simp only [one_div]
    rw [hfun]
    convert hinv using 1
    field_simp
  have hiI : IntervalIntegrable
      (fun t : ℝ => 1 / (t * (log (n : ℝ) - log (p : ℝ) - log t) ^ 2)) volume
      (U7153.yy n) (√((1 + ε₁) * (n : ℝ) / p)) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have hne : log (n : ℝ) - log (p : ℝ) - log t ≠ 0 := ne_of_gt (hgt t ht)
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le hone ht.1))
    have hlogt : log t ≠ 0 := (log_pos (lt_of_lt_of_le hone ht.1)).ne'
    fun_prop (disch := first | exact hne | exact ht0 | exact hlogt | positivity)
  have hH0 : ∀ t ∈ Set.Icc (U7153.yy n) (√((1 + ε₁) * (n : ℝ) / p)),
      0 ≤ 1 / (log (n : ℝ) - log (p : ℝ) - log t) := by
    intro t ht
    exact le_of_lt (one_div_pos.mpr (hgt t ht))
  have hH'0 : ∀ t ∈ Set.Icc (U7153.yy n) (√((1 + ε₁) * (n : ℝ) / p)),
      0 ≤ 1 / (t * (log (n : ℝ) - log (p : ℝ) - log t) ^ 2) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (lt_of_lt_of_le hone ht.1)
    have hpos : (0 : ℝ) < log (n : ℝ) - log (p : ℝ) - log t := hgt t ht
    exact le_of_lt (one_div_pos.mpr (mul_pos ht0 (pow_pos hpos 2)))
  have habel := prime_abel_pointwise
    (fun t : ℝ => 1 / (log (n : ℝ) - log (p : ℝ) - log t))
    (fun t : ℝ => 1 / (t * (log (n : ℝ) - log (p : ℝ) - log t) ^ 2))
    (U7153.yy n) (√((1 + ε₁) * (n : ℝ) / p)) B
    (yy_ge_286 hn) hX hdv hiI hH0 hH'0 hm
  have hint := integral_inner_le (n : ℝ) (p : ℝ) ε₁ hn1 hp1 hε hpN hx
    (log_arg_small hn hε hε1)
  have hint' : (∫ t in U7153.yy n..√((1 + ε₁) * (n : ℝ) / p),
        1 / (log (n : ℝ) - log (p : ℝ) - log t) / (t * log t))
      ≤ H (n : ℝ) (p : ℝ) +
        log (√(1 + ε₁)) / (log ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 - log (√(1 + ε₁)) ^ 2) := by
    have heq : (∫ t in U7153.yy n..√((1 + ε₁) * (n : ℝ) / p),
          1 / (log (n : ℝ) - log (p : ℝ) - log t) / (t * log t))
        = ∫ t in (n : ℝ) ^ (1 / 3 : ℝ)..√((1 + ε₁) * (n : ℝ) / p),
            1 / (t * log t * (log (n : ℝ) - log (p : ℝ) - log t)) := by
      apply integral_congr
      intro t ht
      rw [Set.uIcc_of_le hX] at ht
      have hne : log (n : ℝ) - log (p : ℝ) - log t ≠ 0 := ne_of_gt (hgt t ht)
      have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one (lt_of_lt_of_le hone ht.1))
      have hlogt : log t ≠ 0 := (log_pos (lt_of_lt_of_le hone ht.1)).ne'
      field_simp
    rw [heq]
    exact hint
  have herr : 1 / (log (n : ℝ) - log (p : ℝ) - log (√((1 + ε₁) * (n : ℝ) / p))) /
        (2 * log (√((1 + ε₁) * (n : ℝ) / p)) ^ 2) +
      1 / (log (n : ℝ) - log (p : ℝ) - log (√((1 + ε₁) * (n : ℝ) / p))) /
        (2 * log (U7153.yy n) ^ 2)
      ≤ 27 / (log n) ^ 3 + 100 * log (1 + ε₁) ^ 2 / (log n) ^ 5 := by
    set c := log (1 + ε₁) with hcdef
    set A := log (n : ℝ) - log (p : ℝ) with hAdef
    set P := 2 * log n / 3 with hPdef
    have hP : 0 < P := by rw [hPdef]; positivity
    have hAP : P ≤ A := by rw [hAdef, hPdef]; linarith
    have hAc : 0 < A - c := by linarith [hAP, hPdef, hL3, hc07]
    have hPc : 0 < P - c := by linarith [hAP, hPdef, hL3, hc07]
    have hlnX : log (√((1 + ε₁) * (n : ℝ) / p)) = (A + c) / 2 := by
      rw [hAdef, hcdef]; exact hlogX
    have hlyy : log (U7153.yy n) = P / 2 := by rw [hlogyy, hPdef]; ring
    have hAX : A - log (√((1 + ε₁) * (n : ℝ) / p)) = (A - c) / 2 := by rw [hlnX]; ring
    have hv5 : 5 * c ≤ P := by linarith [hPdef, hL3, hc07]
    have hcnn : 0 ≤ c := by rw [hcdef]; exact le_of_lt (log_pos (by linarith))
    have hAX2 : A - (A + c) / 2 = (A - c) / 2 := by ring
    rw [hlnX, hlyy, hAX2]
    have hfac : 1 / (P - c) * (1 / (P + c) ^ 2 + 1 / P ^ 2) =
        (1 / P ^ 3) * ((1 + 1 / (1 + c / P) ^ 2) / (1 - c / P)) := by
      have h1 : P - c = P * (1 - c / P) := by field_simp
      have h2 : P + c = P * (1 + c / P) := by field_simp
      rw [h1, h2]
      field_simp
      ring
    have hratio : (1 + 1 / (1 + c / P) ^ 2) / (1 - c / P) ≤ 2 + 3 * (c / P) ^ 2 := by
      have hcpos : 0 < c := by rw [hcdef]; exact log_pos (by linarith)
      have hv : 0 < c / P := div_pos hcpos hP
      have hv5' : c / P ≤ 1 / 5 := by
        rw [div_le_iff₀ hP]
        linarith
      have h1v : 0 < 1 - c / P := by linarith
      have hkey : (1 : ℝ) ≤ (1 - 2 * (c / P) + 3 * (c / P) ^ 2 - 3 * (c / P) ^ 3) *
          (1 + c / P) ^ 2 := by
        have hv' : 0 < c / P := hv
        have h5 : c / P ≤ 1 / 5 := hv5'
        nlinarith [hv', h5, sq_nonneg (c / P), pow_pos hv' 3]
      have hsq : (0 : ℝ) < (1 + c / P) ^ 2 := by
        have h1cp : (0 : ℝ) < 1 + c / P := by linarith
        exact pow_pos h1cp 2
      have hcomp : 1 / (1 + c / P) ^ 2 ≤
          1 - 2 * (c / P) + 3 * (c / P) ^ 2 - 3 * (c / P) ^ 3 := by
        rw [div_le_iff₀ hsq]
        nlinarith [hkey]
      rw [div_le_iff₀ h1v]
      nlinarith [hcomp]
    have hmono : 1 / (A - c) * (1 / (A + c) ^ 2 + 1 / P ^ 2) ≤
        1 / (P - c) * (1 / (P + c) ^ 2 + 1 / P ^ 2) := by
      have h1 : 1 / (A - c) ≤ 1 / (P - c) :=
        div_le_div_of_nonneg_left (by norm_num) hPc (by linarith)
      have h2 : 1 / (A + c) ^ 2 ≤ 1 / (P + c) ^ 2 := by
        have h3 : P + c ≤ A + c := by linarith [hAP]
        have hPc0 : (0 : ℝ) < P + c := by linarith [hP, hcnn]
        have h4 : (P + c) ^ 2 ≤ (A + c) ^ 2 := by
          have h5 := mul_self_le_mul_self hPc0.le h3
          simpa only [pow_two] using h5
        exact one_div_le_one_div_of_le (by positivity) h4
      calc 1 / (A - c) * (1 / (A + c) ^ 2 + 1 / P ^ 2)
          ≤ 1 / (P - c) * (1 / (A + c) ^ 2 + 1 / P ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ 1 / (P - c) * (1 / (P + c) ^ 2 + 1 / P ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hrew : 1 / ((A - c) / 2) / (2 * ((A + c) / 2) ^ 2) +
        1 / ((A - c) / 2) / (2 * (P / 2) ^ 2)
        = 4 * (1 / (A - c) * (1 / (A + c) ^ 2 + 1 / P ^ 2)) := by
      field_simp
      ring
    have h6 : 4 * ((1 / P ^ 3) * (2 + 3 * (c / P) ^ 2)) = 8 / P ^ 3 + 12 * c ^ 2 / P ^ 5 := by
      field_simp
      ring
    have h7 : 8 / P ^ 3 = 27 / (log n) ^ 3 := by
      rw [hPdef]
      field_simp
      ring
    have h8 : 12 * c ^ 2 / P ^ 5 ≤ 100 * c ^ 2 / (log n) ^ 5 := by
      have hP5 : P ^ 5 = 32 / 243 * (log n) ^ 5 := by
        rw [hPdef]
        field_simp
        ring
      rw [hP5]
      have he : 12 * c ^ 2 / (32 / 243 * (log n) ^ 5)
          = (12 * 243 / 32 : ℝ) * (c ^ 2 / (log n) ^ 5) := by
        field_simp
      rw [he]
      have hpos : (0 : ℝ) ≤ c ^ 2 / (log n) ^ 5 := by positivity
      calc (12 * 243 / 32 : ℝ) * (c ^ 2 / (log n) ^ 5)
          ≤ 100 * (c ^ 2 / (log n) ^ 5) := by
            apply mul_le_mul_of_nonneg_right (by norm_num) hpos
        _ = 100 * c ^ 2 / (log n) ^ 5 := by ring
    rw [hrew]
    have hstep : 4 * (1 / (A - c) * (1 / (A + c) ^ 2 + 1 / P ^ 2)) ≤
        4 * ((1 / P ^ 3) * ((1 + 1 / (1 + c / P) ^ 2) / (1 - c / P))) := by
      rw [← hfac]
      linarith [hmono]
    have hstep2 : 4 * ((1 / P ^ 3) * ((1 + 1 / (1 + c / P) ^ 2) / (1 - c / P))) ≤
        4 * ((1 / P ^ 3) * (2 + 3 * (c / P) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    nlinarith [hstep, hstep2, h6, h7, h8]
  have hmass : massErrorTail n ε₁ = log (√(1 + ε₁)) /
        (log ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 - log (√(1 + ε₁)) ^ 2) + 27 / (log n) ^ 3 := by
    unfold massErrorTail
    rw [U7153.yy]
  have hint'' : (∫ t in U7153.yy n..√((1 + ε₁) * (n : ℝ) / p),
        1 / (log (n : ℝ) - log (p : ℝ) - log t) / (t * log t))
      ≤ H (n : ℝ) (p : ℝ) + (massErrorTail n ε₁ - 27 / (log n) ^ 3) := by
    linarith [hint', hmass]
  have hconv : ∀ q ∈ (Nat.primesBelow ⌈√((1 + ε₁) * (n : ℝ) / p)⌉₊).filter
        (fun q : ℕ => U7153.yy n ≤ (q : ℝ)),
      1 / ((q : ℝ) * log ((n : ℝ) / ((p : ℝ) * (q : ℝ))))
        = 1 / (log (n : ℝ) - log (p : ℝ) - log (q : ℝ)) / (q : ℝ) := by
    intro q hq
    obtain ⟨-, hqy⟩ := Finset.mem_filter.mp hq
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (by linarith) hqy
    have hpq0 : ((p : ℝ) * (q : ℝ)) ≠ 0 := ne_of_gt (mul_pos hp0 hq0)
    rw [Real.log_div (ne_of_gt hn0) hpq0, Real.log_mul (ne_of_gt hp0) (ne_of_gt hq0)]
    field_simp
    ring
  rw [← Finset.sum_congr rfl hconv] at habel
  linarith [habel, hint'', herr]

/-! ## 11. The fibre of `pairRange` over the first prime coordinate -/

/-- The fibre of `pairRange n ε₁` over `q.1 = p` is a subset of the prime interval that the
Abel estimate of `inner_fiber_le` is stated on. -/
private theorem fiber_le (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ))
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) (p : ℕ) (hp : p ∈ U7153.Qset n) :
    (∑ q ∈ (pairRange n ε₁).filter (fun q => q.1 = p),
        1 / ((q.1 : ℝ) * (q.2 : ℝ) * log ((n : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)))))
      ≤ (1 / (p : ℝ)) *
        ∑ q ∈ (Nat.primesBelow ⌈√((1 + ε₁) * (n : ℝ) / p)⌉₊).filter
            (fun q : ℕ => U7153.yy n ≤ (q : ℝ)),
          1 / ((q : ℝ) * log ((n : ℝ) / ((p : ℝ) * (q : ℝ)))) := by
  obtain ⟨-, hpp, hzp, hyp⟩ := Finset.mem_filter.mp hp
  have hn1 : (1 : ℝ) < n := one_lt_n hn
  have hn0 : (0 : ℝ) < n := n_pos hn
  have hp2 : 2 ≤ p := hpp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  set T := (Nat.primesBelow ⌈√((1 + ε₁) * (n : ℝ) / p)⌉₊).filter
    (fun q : ℕ => U7153.yy n ≤ (q : ℝ)) with hT
  have hTmem : ∀ q ∈ T, q.Prime ∧ (q : ℝ) < √((1 + ε₁) * (n : ℝ) / p) := by
    intro q hq
    rw [hT] at hq
    obtain ⟨hq1, -⟩ := Finset.mem_filter.mp hq
    exact ⟨(Nat.mem_primesBelow.mp hq1).2, Nat.lt_ceil.mp (Nat.mem_primesBelow.mp hq1).1⟩
  have hsub : (pairRange n ε₁).filter (fun q => q.1 = p) ⊆
      T.image (fun q => (p, q)) := by
    intro x hx
    obtain ⟨a, b⟩ := x
    obtain ⟨hxf, hxe⟩ := Finset.mem_filter.mp hx
    have hae : a = p := hxe
    subst hae
    unfold pairRange at hxf
    obtain ⟨-, hpa, hpb, hz, hy, hyb, hprod⟩ := Finset.mem_filter.mp hxf
    refine Finset.mem_image.mpr ⟨b, ?_, rfl⟩
    rw [hT]
    refine Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨?_, hpb⟩, hyb⟩
    rw [Nat.lt_ceil, Real.lt_sqrt (by positivity), lt_div_iff₀ hp0]
    nlinarith [hprod]
  have hnn : ∀ x ∈ T.image (fun q => (p, q)),
      0 ≤ 1 / ((x.1 : ℝ) * (x.2 : ℝ) * log ((n : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)))) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hkp, hkX⟩ := hTmem k hk
    have hk2 : 2 ≤ k := hkp.two_le
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hksq : (k : ℝ) ^ 2 < (1 + ε₁) * (n : ℝ) / p :=
      (Real.lt_sqrt (by positivity)).mp hkX
    have hprod : (p : ℝ) * (k : ℝ) ^ 2 < (1 + ε₁) * (n : ℝ) := by
      have h := (lt_div_iff₀ hp0).mp hksq
      nlinarith [h]
    have hpk : (p : ℝ) * (k : ℝ) < (n : ℝ) := by
      have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have hε2 : 1 + ε₁ < 2 := by linarith
      nlinarith [hprod, hk0, hk2R, hε2, hn0]
    have hratio : (1 : ℝ) < (n : ℝ) / ((p : ℝ) * (k : ℝ)) := by
      rw [lt_div_iff₀ (mul_pos hp0 hk0)]
      linarith
    have hlogpos : 0 < log ((n : ℝ) / ((p : ℝ) * (k : ℝ))) := log_pos hratio
    exact le_of_lt (one_div_pos.mpr (mul_pos (mul_pos hp0 hk0) hlogpos))
  have hstep := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => hnn x hx)
  have hmap : (∑ q ∈ T.image (fun q => (p, q)),
        1 / ((q.1 : ℝ) * (q.2 : ℝ) * log ((n : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)))))
      = ∑ k ∈ T, 1 / ((p : ℝ) * (k : ℝ) * log ((n : ℝ) / ((p : ℝ) * (k : ℝ)))) := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact (Prod.mk.inj h).2
  have hfactor : (∑ k ∈ T, 1 / ((p : ℝ) * (k : ℝ) * log ((n : ℝ) / ((p : ℝ) * (k : ℝ)))))
      = (1 / (p : ℝ)) *
        ∑ k ∈ T, 1 / ((k : ℝ) * log ((n : ℝ) / ((p : ℝ) * (k : ℝ)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    field_simp
  calc (∑ q ∈ (pairRange n ε₁).filter (fun q => q.1 = p),
        1 / ((q.1 : ℝ) * (q.2 : ℝ) * log ((n : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)))))
      ≤ ∑ q ∈ T.image (fun q => (p, q)),
          1 / ((q.1 : ℝ) * (q.2 : ℝ) * log ((n : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)))) := hstep
    _ = ∑ k ∈ T, 1 / ((p : ℝ) * (k : ℝ) * log ((n : ℝ) / ((p : ℝ) * (k : ℝ)))) := hmap
    _ = (1 / (p : ℝ)) *
          ∑ k ∈ T, 1 / ((k : ℝ) * log ((n : ℝ) / ((p : ℝ) * (k : ℝ)))) := hfactor

/-! ## 12. The reciprocal sum over `Qset n` -/

/-- `Σ_{p ∈ Qset n} 1/p = log (8/3) + O(1/log²n)`, from the pointwise Mertens bound at the
two endpoints `n^{1/8}` and `n^{1/3}`. -/
private theorem Qset_recip_le (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (B : ℝ)
    (hm : ∀ t : ℝ, 286 ≤ t →
      |(∑ k ∈ Nat.primesBelow ⌈t⌉₊, (1 : ℝ) / k) - (log (log t) + B)| ≤ 1 / (2 * log t ^ 2)) :
    (∑ p ∈ U7153.Qset n, (1 : ℝ) / p) ≤ log (8 / 3) + 36.5 / (log n) ^ 2 := by
  have hn0 : (0 : ℝ) < n := n_pos hn
  have hL : 0 < log n := log_n_pos hn
  have hL3 : (3000 : ℝ) ≤ log n := log_n_ge_3000 hn
  have hzy : U7153.zz n ≤ U7153.yy n := zz_le_yy' hn
  have hzz286 : 286 ≤ U7153.zz n := by
    rw [U7153.zz, Real.rpow_def_of_pos hn0]
    have h1 : (375 : ℝ) ≤ log (n : ℝ) / 8 := by linarith
    have h2 : (286 : ℝ) ≤ exp (375 : ℝ) := by
      have h := Real.add_one_le_exp (375 : ℝ)
      linarith
    calc (286 : ℝ) ≤ exp (375 : ℝ) := h2
      _ ≤ exp (log (n : ℝ) / 8) := Real.exp_le_exp.mpr h1
      _ = exp (log (n : ℝ) * (1 / 8)) := by
          congr 1
          ring
  have hyy286 : 286 ≤ U7153.yy n := yy_ge_286 hn
  have hQ : U7153.Qset n = Nat.primesBelow ⌈U7153.yy n⌉₊ \ Nat.primesBelow ⌈U7153.zz n⌉₊ := by
    ext q
    simp only [U7153.Qset, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff,
      Nat.mem_primesBelow]
    constructor
    · rintro ⟨-, hqp, hqz, hqy⟩
      exact ⟨⟨Nat.lt_ceil.mpr hqy, hqp⟩,
        fun h => absurd (Nat.lt_ceil.mp h.1) (not_lt.mpr hqz)⟩
    · rintro ⟨⟨hqy, hqp⟩, hqs⟩
      have hqy' : (q : ℝ) < U7153.yy n := Nat.lt_ceil.mp hqy
      have hqn : q < n + 1 := by
        have h1 : (q : ℝ) < (n : ℝ) := lt_of_lt_of_le hqy' (cube_le_n hn)
        have h2 : q ≤ n := by exact_mod_cast le_of_lt h1
        omega
      refine ⟨hqn, hqp, ?_, hqy'⟩
      by_contra hc
      push_neg at hc
      exact hqs ⟨Nat.lt_ceil.mpr hc, hqp⟩
  have hsub : Nat.primesBelow ⌈U7153.zz n⌉₊ ⊆ Nat.primesBelow ⌈U7153.yy n⌉₊ := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Nat.mem_primesBelow.mp hq
    exact Nat.mem_primesBelow.mpr ⟨lt_of_lt_of_le (Nat.lt_ceil.mp hq1) (Nat.ceil_mono hzy), hq2⟩
  have hy := hm (U7153.yy n) hyy286
  have hz := hm (U7153.zz n) hzz286
  have hmain : (∑ p ∈ U7153.Qset n, (1 : ℝ) / p)
      ≤ log (log (U7153.yy n)) - log (log (U7153.zz n)) +
        1 / (2 * log (U7153.yy n) ^ 2) + 1 / (2 * log (U7153.zz n) ^ 2) := by
    rw [hQ]
    have hsdiff := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hsub
    have h1 := (abs_le.mp hy).2
    have h2 := (abs_le.mp hz).1
    linarith [hsdiff]
  have hratio : log (log (U7153.yy n)) - log (log (U7153.zz n)) = log (8 / 3) :=
    log_ratio_zz_yy hn
  have hyy : log (U7153.yy n) = log n / 3 := log_yy_eq hn
  have hzz : log (U7153.zz n) = log n / 8 := log_zz_eq hn
  have e1 : 1 / (2 * (log n / 3) ^ 2) = 4.5 / (log n) ^ 2 := by
    field_simp
    ring
  have e2 : 1 / (2 * (log n / 8) ^ 2) = 32 / (log n) ^ 2 := by
    field_simp
    ring
  rw [hratio, hyy, hzz, e1, e2] at hmain
  have hsum : 4.5 / (log n) ^ 2 + 32 / (log n) ^ 2 = 36.5 / (log n) ^ 2 := by
    rw [← add_div]
    norm_num
  linarith [hmain, hsum]

/-! ## 13. The leaf `inner_prime_sum`, from the pointwise Mertens bound -/

set_option maxHeartbeats 2000000 in
/-- `inner_prime_sum` of the target file, proved from `Decomp543a.rosser_schoenfeld_theorem5`
(the journal's cited input) and `Mathlib` only. -/
theorem inner_prime_sum_via_mertens (n : ℕ) (ε₁ : ℝ) (hn : exp (exp 10) ≤ (n : ℝ))
    (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    pairWeightSum n ε₁ ≤
      (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) +
        (log (8 / 3) + 64 / (log n) ^ 2) * massErrorTail n ε₁ := by
  obtain ⟨B, hlo, hup⟩ := Decomp543a.rosser_schoenfeld_theorem5
  have hm := mertens_pointwise B hlo hup
  have hn0 : (0 : ℝ) < n := n_pos hn
  have hL : 0 < log n := log_n_pos hn
  have hL3 : (3000 : ℝ) ≤ log n := log_n_ge_3000 hn
  have hc : log (1 + ε₁) ≤ 0.7 := by
    have h1 : log (1 + ε₁) ≤ log 2 := log_le_log (by linarith) (by linarith)
    linarith [Real.log_two_lt_d9]
  have hc0 : 0 ≤ log (1 + ε₁) := le_of_lt (log_pos (by linarith))
  rw [pairWeightSum_eq_sum_fiber n ε₁ hn]
  set M := massErrorTail n ε₁ with hM
  set E := 100 * log (1 + ε₁) ^ 2 / (log n) ^ 5 with hE
  set R := ∑ p ∈ U7153.Qset n, (1 : ℝ) / p with hRdef
  set Rp := log (8 / 3) + 64 / (log n) ^ 2 with hRp
  have hM0 : 0 ≤ M := by
    rw [hM]
    unfold massErrorTail
    have h1 : 0 ≤ log (√(1 + ε₁)) := by
      rw [Real.log_sqrt (by linarith)]
      linarith
    have h2 : 0 < log (U7153.yy n) ^ 2 - log (√(1 + ε₁)) ^ 2 := by
      have h3 : log (U7153.yy n) = log n / 3 := log_yy_eq hn
      have h4 : log (√(1 + ε₁)) ≤ 0.7 := by
        rw [Real.log_sqrt (by linarith)]
        linarith
      have h5 : (1000 : ℝ) ≤ log (U7153.yy n) := by rw [h3]; linarith
      nlinarith [h1, h4, h5]
    have h6 : 0 < 27 / (log n) ^ 3 := by positivity
    have := div_nonneg h1 (le_of_lt h2)
    linarith
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    exact Finset.sum_nonneg (fun p _ => by positivity)
  have hRle : R ≤ log (8 / 3) + 36.5 / (log n) ^ 2 := Qset_recip_le n hn B hm
  have hstep1 : (∑ p ∈ U7153.Qset n,
        ∑ q ∈ (pairRange n ε₁).filter (fun q => q.1 = p),
          1 / ((q.1 : ℝ) * (q.2 : ℝ) * log ((n : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)))))
      ≤ ∑ p ∈ U7153.Qset n, (1 / (p : ℝ)) * (H (n : ℝ) (p : ℝ) + M + E) := by
    apply Finset.sum_le_sum
    intro p hp
    refine (fiber_le n ε₁ hn hε hε1 p hp).trans ?_
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := inner_fiber_le n ε₁ hn hε hε1 B hm p hp
    rw [hM, hE]
    linarith [this]
  have hstep2 : (∑ p ∈ U7153.Qset n, (1 / (p : ℝ)) * (H (n : ℝ) (p : ℝ) + M + E))
      = (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) + R * (M + E) := by
    have hsp : ∀ p ∈ U7153.Qset n,
        (1 / (p : ℝ)) * (H (n : ℝ) (p : ℝ) + M + E)
          = H (n : ℝ) (p : ℝ) / p + (1 / (p : ℝ)) * (M + E) := by
      intro p hp
      ring
    rw [Finset.sum_congr rfl hsp, Finset.sum_add_distrib, ← Finset.sum_mul, ← hRdef]
  have hexp : R * E ≤ 100 / (log n) ^ 5 := by
    have hR2 : R ≤ 5 / 3 + 36.5 / (log n) ^ 2 := by
      have h2 : log (8 / 3) ≤ 5 / 3 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8 / 3 by norm_num)
        linarith
      linarith [hRle]
    have h49 : E ≤ 49 / (log n) ^ 5 := by
      rw [hE]
      have hsq : log (1 + ε₁) ^ 2 ≤ 0.49 := by nlinarith [hc, hc0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hL5 : (0 : ℝ) < (log n) ^ 5 := by positivity
    have hL7 : (0 : ℝ) < (log n) ^ 7 := by positivity
    have hA : R * E ≤ (5 / 3 + 36.5 / (log n) ^ 2) * (49 / (log n) ^ 5) :=
      mul_le_mul hR2 h49 hE0 (by positivity)
    have hB : (5 / 3 + 36.5 / (log n) ^ 2) * (49 / (log n) ^ 5)
        = 49 * (5 / 3) / (log n) ^ 5 + 49 * 36.5 / (log n) ^ 7 := by
      field_simp
    have hB2 : 49 * 36.5 / (log n) ^ 7 ≤ 18 / (log n) ^ 5 := by
      have hnum : (49 * 36.5 : ℝ) ≤ 18 * (log n) ^ 2 := by
        have h9 : (9000000 : ℝ) ≤ (log n) ^ 2 := by nlinarith [hL3]
        nlinarith [h9]
      rw [div_le_div_iff₀ hL7 hL5]
      nlinarith [hnum, pow_pos hL 5]
    have hD : 49 * (5 / 3) / (log n) ^ 5 + 18 / (log n) ^ 5 ≤ 100 / (log n) ^ 5 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hL5.le
      norm_num
    linarith [hA, hB, hB2, hD]
  have hgap : 27.5 / (log n) ^ 2 ≤ Rp - R := by
    have e : Rp - (log (8 / 3) + 36.5 / (log n) ^ 2) = 27.5 / (log n) ^ 2 := by
      rw [hRp]
      have hL2 : (log n) ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    linarith [hRle, e]
  have hMl : 27 / (log n) ^ 3 ≤ M := by
    rw [hM]
    unfold massErrorTail
    have h1 : 0 ≤ log (√(1 + ε₁)) /
        (log (U7153.yy n) ^ 2 - log (√(1 + ε₁)) ^ 2) := by
      have h3 : log (U7153.yy n) = log n / 3 := log_yy_eq hn
      have h4 : log (√(1 + ε₁)) ≤ 0.7 := by
        rw [Real.log_sqrt (by linarith)]
        linarith
      have h5 : (1000 : ℝ) ≤ log (U7153.yy n) := by rw [h3]; linarith
      have h7 : 0 ≤ log (√(1 + ε₁)) := by
        rw [Real.log_sqrt (by linarith)]
        linarith
      have h6 : 0 < log (U7153.yy n) ^ 2 - log (√(1 + ε₁)) ^ 2 := by nlinarith [h4, h5, h7]
      exact div_nonneg h7 (le_of_lt h6)
    linarith
  have hbig : R * E ≤ (Rp - R) * M := by
    have h1 : (742 : ℝ) / (log n) ^ 5 ≤ (Rp - R) * M := by
      have h2 : (Rp - R) * M ≥ 27.5 / (log n) ^ 2 * (27 / (log n) ^ 3) := by
        have hb : (0 : ℝ) ≤ Rp - R := by
          have hp27 : (0 : ℝ) < 27.5 / (log n) ^ 2 := by positivity
          linarith [hgap]
        exact mul_le_mul hgap hMl (by positivity) hb
      have h3 : 27.5 / (log n) ^ 2 * (27 / (log n) ^ 3) = 742.5 / (log n) ^ 5 := by
        have hL0 : (log n) ≠ 0 := ne_of_gt hL
        field_simp
        ring
      have h45 : (742 : ℝ) / (log n) ^ 5 ≤ 742.5 / (log n) ^ 5 := by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
      linarith [h2, h3, h45]
    have h4 : 100 / (log n) ^ 5 ≤ 742 / (log n) ^ 5 := by
      apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith [hexp, h4, h1]
  calc (∑ p ∈ U7153.Qset n,
        ∑ q ∈ (pairRange n ε₁).filter (fun q => q.1 = p),
          1 / ((q.1 : ℝ) * (q.2 : ℝ) * log ((n : ℝ) / ((q.1 : ℝ) * (q.2 : ℝ)))))
      ≤ ∑ p ∈ U7153.Qset n, (1 / (p : ℝ)) * (H (n : ℝ) (p : ℝ) + M + E) := hstep1
    _ = (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) + R * (M + E) := hstep2
    _ = (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) + (R * M + R * E) := by ring
    _ ≤ (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) + (R * M + (Rp - R) * M) := by
        linarith [hbig]
    _ = (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) + Rp * M := by ring
    _ = (∑ p ∈ U7153.Qset n, H (n : ℝ) (p : ℝ) / p) +
          (log (8 / 3) + 64 / (log n) ^ 2) * massErrorTail n ε₁ := by
        rw [hRp, hM]


/-- LEAF. Journal p. 1238, first apply Greaves Lemma 1 part ii and
Rosser and Schoenfeld Theorem 5 to the inner prime variable.
The short endpoint integral and the 27 over log cubed error are massErrorTail.
The remaining H prime sum is not yet estimated. -/
theorem inner_prime_sum (n : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    pairWeightSum n ε₁ ≤
      (∑ p ∈ U7153.Qset n, H n p / p) +
        (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁ :=
  inner_prime_sum_via_mertens n ε₁ hn hε hε1

/-- LEAF. Journal pp. 1238 and 1239, the outer weighted prime summation.
Apply Greaves Lemma 1 part ii and Rosser and Schoenfeld Theorem 5 to H.
Use H at y equal to zero and H at z at most 0.56 over log N.
This estimate is independent of the slice width epsilon one. -/
theorem outer_prime_sum (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    (∑ p ∈ U7153.Qset n, H n p / p) ≤
      (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) + 36 / log n ^ 3 := by
  obtain ⟨B, hlo, hup⟩ := Decomp543a.rosser_schoenfeld_theorem5
  exact Decomp543a.outer_prime_sum_of_mertens n hn B hlo hup

/-- Exact statement of SliceMass236.pair_weight_mertens from the two separate prime steps.
CONDITIONAL ON inner_prime_sum and outer_prime_sum. No direct sorry. -/
theorem pair_weight_mertens (n : ℕ) (ε₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hε : 0 < ε₁) (hε1 : ε₁ < 1) :
    pairWeightSum n ε₁ ≤
      (∫ u in U7153.zz n..U7153.yy n, H n u / (u * log u)) + 36 / log n ^ 3 +
        (log (8 / 3) + 64 / log n ^ 2) * massErrorTail n ε₁ := by
  linarith only [inner_prime_sum n ε₁ hn hε hε1, outer_prime_sum n hn]

end
end LeanLab.BS2022GRH.Decomp374g

#print axioms LeanLab.BS2022GRH.Decomp374g.inner_prime_sum
#print axioms LeanLab.BS2022GRH.Decomp374g.outer_prime_sum
#print axioms LeanLab.BS2022GRH.Decomp374g.pair_weight_mertens
