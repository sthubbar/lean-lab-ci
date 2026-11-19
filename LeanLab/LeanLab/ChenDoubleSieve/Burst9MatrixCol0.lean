import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Burst 9: the `j = 0` column of Wu's Section 7 matrix

Source: the same source as `LeanLab.ChenDoubleSieve.Burst9Matrix`, displays 7.1 and 7.2, page 30,
and the kernel `Xi1` of display 3.21, page 14. This module holds the whole `j = 0` development
(the `sigma0` quadrature on `[1, 11/5]` and the two certified entries) and is imported by
`LeanLab.ChenDoubleSieve.Burst9Matrix`, which keeps the 81 statements. The split is by module
size: the matrix file with its statements and the rest of its helper chain no longer fits one
compile unit.

The private lemmas copied at the top are the file's own toolkit (`integral_one_div_exp`, the
`sigma` bounds, `log_enclosure`, the logarithm series and the second-order derivative helpers);
they are repeated here because a `private` declaration does not cross modules, and the copies go
into a second namespace for that reason.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Burst9MatrixCol0
open Wu04Table
open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LeanLab.ChenDoubleSieve.Wu04Integral LeanLab.ChenDoubleSieve.Wu04Functional

/-- `∫ 1/x dx = log (b/a)` on a positive interval, from the fundamental theorem of calculus. -/
private theorem integral_one_div_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, (1 : ℝ) / x) = log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hderiv : ∀ x ∈ uIcc a b, DifferentiableAt ℝ Real.log x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le ha hx.1))
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hint : IntervalIntegrable (deriv Real.log) volume a b := by
    have hd : deriv Real.log = fun x : ℝ => x⁻¹ := funext fun x => Real.deriv_log x
    rw [hd]
    exact hcont.intervalIntegrable
  calc (∫ x in a..b, (1 : ℝ) / x) = ∫ x in a..b, deriv Real.log x := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [Real.deriv_log, one_div]
    _ = Real.log b - Real.log a := intervalIntegral.integral_deriv_eq_sub hderiv hint
    _ = log (b / a) := by rw [log_div (ne_of_gt hb) (ne_of_gt ha)]

/-- `sigma 3 (t+2) (t+1)`, with the constant `t+1` of the integrand taken out of the integral. -/
private theorem sigma_diagonal_eq {t : ℝ} (ht : 1 < t) :
    Wu04Integral.sigma 3 (t + 2) (t + 1) =
      log (t + 1) * log ((t + 2) / 3) -
        ∫ u in (3 : ℝ)..(t + 2), log (u - 1) / u := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hb : (3 : ℝ) ≤ t + 2 := by linarith
  have hpos : ∀ u ∈ uIcc (3 : ℝ) (t + 2), (0 : ℝ) < u := by
    intro u hu
    rw [uIcc_of_le hb] at hu
    linarith [hu.1]
  have hu1 : ∀ u ∈ uIcc (3 : ℝ) (t + 2), (0 : ℝ) < u - 1 := by
    intro u hu
    rw [uIcc_of_le hb] at hu
    linarith [hu.1]
  have hc1 : ContinuousOn (fun u : ℝ => log (t + 1) * (1 / u)) (uIcc (3 : ℝ) (t + 2)) :=
    (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt (hpos u hu))).const_mul _
  have hc2 : ContinuousOn (fun u : ℝ => log (u - 1) / u) (uIcc (3 : ℝ) (t + 2)) :=
    (continuousOn_id.sub continuousOn_const).log (fun u hu => ne_of_gt (hu1 u hu)) |>.div
      continuousOn_id (fun u hu => ne_of_gt (hpos u hu))
  have hcongr : ∀ u ∈ uIcc (3 : ℝ) (t + 2),
      log ((t + 1) / (u - 1)) / u = log (t + 1) * (1 / u) - log (u - 1) / u := by
    intro u hu
    rw [log_div (ne_of_gt ht1) (ne_of_gt (hu1 u hu)), sub_div]
    ring
  unfold Wu04Integral.sigma
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_sub
    (f := fun u : ℝ => log (t + 1) * (1 / u)) (g := fun u : ℝ => log (u - 1) / u)
    hc1.intervalIntegrable hc2.intervalIntegrable]
  rw [intervalIntegral.integral_const_mul, integral_one_div_exp (by norm_num) hb]

/-- Derivative of `t ↦ sigma 3 (t+2) (t+1)`. -/
private theorem hasDerivAt_sigma_diagonal {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => Wu04Integral.sigma 3 (s + 2) (s + 1))
      (log ((t + 2) / 3) / (t + 1)) t := by
  have ht2 : (0 : ℝ) < t + 2 := by linarith
  have hcontOn : ContinuousOn (fun u : ℝ => log (u - 1) / u) (Ioi (1 : ℝ)) := by
    have h1 : ContinuousOn (fun u : ℝ => u - 1) (Ioi (1 : ℝ)) :=
      continuousOn_id.sub continuousOn_const
    have h2 : ContinuousOn (fun u : ℝ => log (u - 1)) (Ioi (1 : ℝ)) :=
      h1.log (fun u hu => by
        have hu' : (1 : ℝ) < u := hu
        exact ne_of_gt (by linarith : (0 : ℝ) < u - 1))
    exact h2.div continuousOn_id (fun u hu => by
      have hu' : (1 : ℝ) < u := hu
      exact ne_of_gt (by linarith : (0 : ℝ) < u))
  have hmem : t + 2 ∈ Ioi (1 : ℝ) := by
    show (1 : ℝ) < t + 2
    linarith
  have hmeas : StronglyMeasurableAtFilter (fun u : ℝ => log (u - 1) / u) (𝓝 (t + 2)) :=
    hcontOn.stronglyMeasurableAtFilter isOpen_Ioi (t + 2) hmem
  have hcont : ContinuousAt (fun u : ℝ => log (u - 1) / u) (t + 2) :=
    hcontOn.continuousAt (isOpen_Ioi.mem_nhds hmem)
  have hint : IntervalIntegrable (fun u : ℝ => log (u - 1) / u) volume 3 (t + 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : (3 : ℝ) ≤ t + 2)]
    have h1 : ContinuousOn (fun u : ℝ => u - 1) (Icc (3 : ℝ) (t + 2)) :=
      continuousOn_id.sub continuousOn_const
    have h2 : ContinuousOn (fun u : ℝ => log (u - 1)) (Icc (3 : ℝ) (t + 2)) :=
      h1.log (fun u hu => ne_of_gt (by linarith [hu.1] : (0 : ℝ) < u - 1))
    exact h2.div continuousOn_id (fun u hu => ne_of_gt (by linarith [hu.1] : (0 : ℝ) < u))
  have hFTC : HasDerivAt (fun s : ℝ => ∫ u in (3 : ℝ)..s, log (u - 1) / u)
      (log (t + 1) / (t + 2)) (t + 2) := by
    have h := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
    have hb : ((t + 2) - 1) = t + 1 := by ring
    simpa only [hb] using h
  have hB : HasDerivAt (fun s : ℝ => ∫ u in (3 : ℝ)..(s + 2), log (u - 1) / u)
      (log (t + 1) / (t + 2)) t := by
    have h := hFTC.comp t ((hasDerivAt_id t).add_const 2)
    simpa [Function.comp_def] using h
  have hA : HasDerivAt (fun s : ℝ => log (s + 1) * log ((s + 2) / 3))
      (1 / (t + 1) * log ((t + 2) / 3) + log (t + 1) * ((1 / 3) / ((t + 2) / 3))) t := by
    have h1 : HasDerivAt (fun s : ℝ => log (s + 1)) (1 / (t + 1)) t := by
      have h := ((hasDerivAt_id (x := t)).add_const 1).log (by show t + 1 ≠ 0; linarith)
      simpa [Function.comp_def] using h
    have h2 : HasDerivAt (fun s : ℝ => log ((s + 2) / 3)) ((1 / 3) / ((t + 2) / 3)) t := by
      have hid : HasDerivAt (fun s : ℝ => (s + 2) / 3) (1 / 3) t := by
        have h := ((hasDerivAt_id (x := t)).add_const 2).div_const 3
        simpa using h
      have h := hid.log (by positivity : ((t + 2) / 3) ≠ 0)
      simpa [Function.comp_def] using h
    exact h1.mul h2
  have hfun : (fun s : ℝ => Wu04Integral.sigma 3 (s + 2) (s + 1))
      =ᶠ[𝓝 t] (fun s : ℝ => log (s + 1) * log ((s + 2) / 3) -
        ∫ u in (3 : ℝ)..(s + 2), log (u - 1) / u) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact sigma_diagonal_eq hs
  have hmain : HasDerivAt (fun s : ℝ => log (s + 1) * log ((s + 2) / 3) -
      ∫ u in (3 : ℝ)..(s + 2), log (u - 1) / u)
      (1 / (t + 1) * log ((t + 2) / 3) + log (t + 1) * ((1 / 3) / ((t + 2) / 3))
        - log (t + 1) / (t + 2)) t := hA.sub hB
  have hval : 1 / (t + 1) * log ((t + 2) / 3) + log (t + 1) * ((1 / 3) / ((t + 2) / 3))
      - log (t + 1) / (t + 2) = log ((t + 2) / 3) / (t + 1) := by
    have h3 : (1 / 3 : ℝ) / ((t + 2) / 3) = 1 / (t + 2) := by
      field_simp
    rw [h3]
    have h1' : (t + 1) ≠ 0 := by linarith
    have h2' : (t + 2) ≠ 0 := by linarith
    field_simp
    ring
  simpa only [hval] using hmain.congr_of_eventuallyEq hfun

/-- `σ₀` has the explicit derivative `log((t+2)/3) / ((t+1)(1-σ(3,5,4)))` on `(1,∞)`. -/
private theorem sigma0_hasDerivAt {t : ℝ} (ht : 1 < t) (_hD : 0 < 1 - Wu04Integral.sigma 3 5 4) :
    HasDerivAt Wu04Integral.sigma0
      ((log ((t + 2) / 3) / (t + 1)) / (1 - Wu04Integral.sigma 3 5 4)) t := by
  have h := (hasDerivAt_sigma_diagonal ht).div_const (1 - Wu04Integral.sigma 3 5 4)
  exact h

/-- Exact value of `∫ (c-t)^m / t`: expand the binomial and divide by `t`. -/
private theorem integral_sub_pow_div {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (m : ℕ) :
    (∫ t in a..b, (c - t) ^ m / t) =
      c ^ m * log (b / a) + ∑ j ∈ Finset.range m,
        (-1) ^ (j + m) * c ^ j * (m.choose j : ℝ) *
          ((b ^ (m - j) - a ^ (m - j)) / ((m : ℝ) - j)) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hpt : ∀ t ∈ uIcc a b, (c - t) ^ m / t =
      c ^ m * (1 / t) + ∑ j ∈ Finset.range m,
        ((-1) ^ (j + m) * c ^ j * (m.choose j : ℝ) * t ^ (m - 1 - j)) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    rw [sub_pow c t m, Finset.sum_range_succ]
    have hlast : (-1) ^ (m + m) * c ^ m * t ^ (m - m) * (m.choose m : ℝ) = c ^ m := by
      simp
    rw [hlast, add_div]
    have : (∑ j ∈ Finset.range m, (-1) ^ (j + m) * c ^ j * t ^ (m - j) * (m.choose j : ℝ)) / t =
        ∑ j ∈ Finset.range m, ((-1) ^ (j + m) * c ^ j * (m.choose j : ℝ) * t ^ (m - 1 - j)) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have h1 : m - 1 - j + 1 = m - j := by omega
      rw [← h1, pow_succ]
      field_simp
    rw [this]
    field_simp
    ring
  calc (∫ t in a..b, (c - t) ^ m / t)
      = ∫ t in a..b, (c ^ m * (1 / t) + ∑ j ∈ Finset.range m,
          ((-1) ^ (j + m) * c ^ j * (m.choose j : ℝ) * t ^ (m - 1 - j))) :=
        intervalIntegral.integral_congr hpt
    _ = (∫ t in a..b, c ^ m * (1 / t)) +
          ∫ t in a..b, ∑ j ∈ Finset.range m,
            ((-1) ^ (j + m) * c ^ j * (m.choose j : ℝ) * t ^ (m - 1 - j)) := by
        rw [intervalIntegral.integral_add]
        · exact ContinuousOn.intervalIntegrable ((continuousOn_const.mul
            (continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hmem t ht)))))
        · refine ContinuousOn.intervalIntegrable ?_
          refine continuousOn_finsetSum _ (fun j hj => ?_)
          exact (continuousOn_const.mul (continuousOn_id.pow _))
    _ = c ^ m * log (b / a) + ∑ j ∈ Finset.range m,
        ((-1) ^ (j + m) * c ^ j * (m.choose j : ℝ) *
          ((b ^ (m - j) - a ^ (m - j)) / ((m : ℝ) - j))) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_exp ha hab,
          intervalIntegral.integral_finsetSum]
        · congr 1
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [intervalIntegral.integral_const_mul, integral_pow]
          have hj' : j < m := Finset.mem_range.mp hj
          have hsub : m - 1 - j + 1 = m - j := by omega
          have hcast : ((m - 1 - j : ℕ) : ℝ) + 1 = (m : ℝ) - j := by
            have hle : j + 1 ≤ m := by omega
            have h1 : m - 1 - j = m - (j + 1) := by omega
            rw [h1, Nat.cast_sub hle]
            push_cast
            ring
          rw [hsub, hcast]
        · intro j hj
          exact ContinuousOn.intervalIntegrable (continuousOn_const.mul (continuousOn_id.pow _))

/-- Exact value of `∫ log v · v^j` on a positive interval. -/
private theorem integral_log_mul_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
    (∫ v in a..b, log v * v ^ j) =
      b ^ (j + 1) * (log b / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 1) ^ 2) -
        a ^ (j + 1) * (log a / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 1) ^ 2) := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt
      (fun v : ℝ => v ^ (j + 1) * (log v / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 1) ^ 2))
      (log x * x ^ j) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have hp : HasDerivAt (fun v : ℝ => v ^ (j + 1)) (((j : ℝ) + 1) * x ^ j) x := by
      simpa using hasDerivAt_pow (j + 1) x
    have hq : HasDerivAt (fun v : ℝ => log v / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 1) ^ 2)
        (1 / x / ((j : ℝ) + 1)) x := by
      have hl : HasDerivAt (fun v : ℝ => log v) (1 / x) x := by
        simpa using Real.hasDerivAt_log (ne_of_gt hx0)
      exact (hl.div_const ((j : ℝ) + 1)).sub_const _
    have hmul := hp.mul hq
    refine hmul.congr_deriv ?_
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hjne : ((j : ℝ) + 1) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    ring
  have hint : IntervalIntegrable (fun v : ℝ => log v * v ^ j) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    have hsub : uIcc a b ⊆ {0}ᶜ := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    exact (Real.continuousOn_log.mono hsub).mul (continuousOn_id.pow j)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

/-- Pointwise lower bound for `log (t+1)` from the logarithm's power series. -/
private theorem log_succ_lower_pointwise {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c + 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : ∀ t ∈ uIcc a b, |(c - t) / (c + 1)| ≤ r) (n : ℕ) :
    ∀ t ∈ uIcc a b, log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) -
      r ^ (n + 1) / (1 - r) ≤ log (t + 1) := by
  intro t ht
  have hxr' : |(c - t) / (c + 1)| ≤ r := hxr t ht
  have hx1 : |(c - t) / (c + 1)| < 1 := lt_of_le_of_lt hxr' hr1
  have hS := Real.abs_log_sub_add_sum_range_le hx1 n
  have hbound : |(c - t) / (c + 1)| ^ (n + 1) / (1 - |(c - t) / (c + 1)|) ≤
      r ^ (n + 1) / (1 - r) := by
    refine div_le_div₀ (by positivity)
      (pow_le_pow_left₀ (abs_nonneg _) hxr' _) (by linarith) (by linarith)
  have harg : 1 - (c - t) / (c + 1) = (t + 1) / (c + 1) := by
    field_simp
    ring
  have ht1 : (0 : ℝ) < t + 1 := by
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hlog1mx : log (1 - (c - t) / (c + 1)) = log (t + 1) - log (c + 1) := by
    rw [harg, log_div (ne_of_gt ht1) (ne_of_gt hc)]
  have := (abs_le.mp (le_trans hS hbound)).1
  linarith [hlog1mx]

/-- The integral of the series lower bound, in closed form. -/
private theorem integral_log_series_lower {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ)
    (E : ℝ) :
    (∫ t in a..b, (log (c + 1) -
        (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) - E) / t) =
      (log (c + 1) * log (b / a) - E * log (b / a)) -
        ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
          (c ^ (i + 1) * log (b / a) + ∑ j ∈ Finset.range (i + 1),
            (-1) ^ (j + (i + 1)) * c ^ j * ((i + 1).choose j : ℝ) *
              ((b ^ (i + 1 - j) - a ^ (i + 1 - j)) / (((i : ℝ) + 1) - j))) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht)))
  have hterm : ∀ i ∈ Finset.range n, IntervalIntegrable
      (fun t : ℝ => (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
        ((c - t) ^ (i + 1) / t)) volume a b := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ?_
    have hbase : ContinuousOn (fun t : ℝ => c - t) (uIcc a b) :=
      continuousOn_const.sub continuousOn_id
    exact (hbase.pow (i + 1)).div continuousOn_id (fun t ht => ne_of_gt (hmem t ht))
  have hsum_eq : ∀ t ∈ uIcc a b,
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) / t =
      ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
        ((c - t) ^ (i + 1) / t) := by
    intro t _
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow]
    field_simp
  have hcongr : ∀ t ∈ uIcc a b, (log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) - E) / t =
      (log (c + 1) * (1 / t) - E * (1 / t)) -
        ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
          ((c - t) ^ (i + 1) / t) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    rw [sub_div, sub_div, hsum_eq t ht]
    field_simp
    ring
  have hA : IntervalIntegrable (fun t : ℝ => log (c + 1) * (1 / t)) volume a b :=
    hinv.const_mul _
  have hE : IntervalIntegrable (fun t : ℝ => E * (1 / t)) volume a b := hinv.const_mul _
  have hS : IntervalIntegrable (fun t : ℝ => ∑ i ∈ Finset.range n,
      (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) * ((c - t) ^ (i + 1) / t)) volume a b := by
    have h := IntervalIntegrable.sum (Finset.range n) hterm
    convert h using 1
    ext t
    simp
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_sub (hA.sub hE) hS]
  rw [intervalIntegral.integral_sub hA hE]
  rw [intervalIntegral.integral_const_mul, integral_one_div_exp ha hab]
  have hsum : (∑ i ∈ Finset.range n, (∫ x in a..b,
      (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) * ((c - x) ^ (i + 1) / x))) =
      ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
        (c ^ (i + 1) * log (b / a) + ∑ j ∈ Finset.range (i + 1),
          (-1) ^ (j + (i + 1)) * c ^ j * ((i + 1).choose j : ℝ) *
            ((b ^ (i + 1 - j) - a ^ (i + 1 - j)) / (((i : ℝ) + 1) - j))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, integral_sub_pow_div ha hab (i + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [intervalIntegral.integral_finsetSum hterm, hsum,
    intervalIntegral.integral_const_mul, integral_one_div_exp ha hab]

/-- Lower bound for `∫ log (t+1)/t` from the logarithm series, with all error terms. -/
private theorem log_succ_integral_lower {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c + 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : ∀ t ∈ uIcc a b, |(c - t) / (c + 1)| ≤ r) (n : ℕ) :
    (log (c + 1) * log (b / a) - (r ^ (n + 1) / (1 - r)) * log (b / a)) -
      ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
        (c ^ (i + 1) * log (b / a) + ∑ j ∈ Finset.range (i + 1),
          (-1) ^ (j + (i + 1)) * c ^ j * ((i + 1).choose j : ℝ) *
            ((b ^ (i + 1 - j) - a ^ (i + 1 - j)) / (((i : ℝ) + 1) - j)))
      ≤ ∫ t in a..b, log (t + 1) / t := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hpt := log_succ_lower_pointwise ha hab hc hr0 hr1 hxr n
  have hdiv : ∀ t ∈ Icc a b, (log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) -
      r ^ (n + 1) / (1 - r)) / t ≤ log (t + 1) / t := by
    intro t ht
    have htu : t ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ht
    exact div_le_div_of_nonneg_right (hpt t htu) (hmem t htu).le
  have hcont1 : ContinuousOn (fun t : ℝ => (log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) -
      r ^ (n + 1) / (1 - r)) / t) (uIcc a b) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (hmem t ht))
    refine (continuousOn_const.sub ?_).sub continuousOn_const
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact (((continuousOn_const.sub continuousOn_id).div_const (c + 1)).pow (i + 1)).div_const
      ((i : ℝ) + 1)
  have hcont2 : ContinuousOn (fun t : ℝ => log (t + 1) / t) (uIcc a b) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (hmem t ht))
    have h1 : ContinuousOn (fun t : ℝ => t + 1) (uIcc a b) :=
      continuousOn_id.add continuousOn_const
    exact Real.continuousOn_log.comp h1 (fun t ht => by
      have := hmem t ht
      exact ne_of_gt (by linarith : (0:ℝ) < t + 1))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    hcont1.intervalIntegrable hcont2.intervalIntegrable hdiv
  rw [← integral_log_series_lower ha hab n (r ^ (n + 1) / (1 - r))]
  exact hmono

/-- Exact geometric remainder for `1/(M+s)`. -/
private theorem inv_series_exact {M s : ℝ} (hM : 0 < M) (hM1 : M + s ≠ 0) (n : ℕ) :
    1 / (M + s) - ∑ k ∈ Finset.range n, (-1) ^ k * s ^ k / M ^ (k + 1) =
      (-1) ^ n * s ^ n / (M ^ n * (M + s)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    have hMne : M ≠ 0 := ne_of_gt hM
    have hMn : M ^ n ≠ 0 := pow_ne_zero n hMne
    field_simp
    ring

/-- Remainder bound for the geometric expansion of `1/(M+s)`. -/
private theorem inv_series_remainder {M s : ℝ} (hM : 0 < M) (hs : |s| < M) (n : ℕ) :
    |1 / (M + s) - ∑ k ∈ Finset.range n, (-1) ^ k * s ^ k / M ^ (k + 1)| ≤
      |s| ^ n / (M ^ n * (M - |s|)) := by
  have hMs : 0 < M + s := by
    have := neg_abs_le s
    linarith
  rw [inv_series_exact hM (ne_of_gt hMs) n]
  have hM0 : (0 : ℝ) < M ^ n := pow_pos hM n
  have hpos : 0 < M ^ n * (M - |s|) := mul_pos hM0 (by linarith)
  have hMn0 : (0 : ℝ) < M ^ n := hM0
  have hkey : M - |s| ≤ |M + s| := by
    have h1 : M + s ≤ |M + s| := le_abs_self _
    have h2 : -|s| ≤ s := neg_abs_le s
    linarith
  have hstep : |(-1) ^ n * s ^ n / (M ^ n * (M + s))| = |s| ^ n / (M ^ n * |M + s|) := by
    rw [abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, abs_mul, abs_of_pos hMn0]
    simp only [one_pow, one_mul]
  rw [hstep]
  exact div_le_div_of_nonneg_left (by positivity) hpos (mul_le_mul_of_nonneg_left hkey hMn0.le)

/-- `∫ log v * (v-m)^k` in closed form. -/
private theorem integral_log_mul_sub_pow {a b m : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (k : ℕ) :
    (∫ v in a..b, log v * (v - m) ^ k) =
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * (-m) ^ (k - i)) *
        (b ^ (i + 1) * (log b / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 1) ^ 2) -
          a ^ (i + 1) * (log a / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 1) ^ 2)) := by
  have hmem : ∀ v ∈ uIcc a b, (0 : ℝ) < v := by
    intro v hv
    rw [uIcc_of_le hab] at hv
    exact lt_of_lt_of_le (by linarith) hv.1
  have hterm : ∀ i ∈ Finset.range (k + 1), IntervalIntegrable
      (fun v : ℝ => ((k.choose i : ℝ) * (-m) ^ (k - i)) * (log v * v ^ i)) volume a b := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ?_
    have hsub : uIcc a b ⊆ {0}ᶜ := by
      intro v hv
      exact ne_of_gt (hmem v hv)
    exact (Real.continuousOn_log.mono hsub).mul (continuousOn_id.pow i)
  have hpt : ∀ v ∈ uIcc a b, log v * (v - m) ^ k =
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * (-m) ^ (k - i)) * (log v * v ^ i) := by
    intro v _
    rw [sub_pow v m k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hik : i ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have hpar : (-1 : ℝ) ^ (i + k) = (-1) ^ (k - i) := by
      rw [show i + k = 2 * i + (k - i) by omega, pow_add, pow_mul]
      norm_num
    rw [hpar]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_finsetSum hterm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_log_mul_pow (by linarith) hab i]

/-- `sigma a b c` in terms of a `log v / (v+1)` integral over `[a-1, b-1]`. -/
private theorem sigma_eq_log_sub {a b c : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 < c) :
    Wu04Integral.sigma a b c =
      log c * log (b / a) - ∫ v in (a - 1)..(b - 1), log v / (v + 1) := by
  have hmem : ∀ t ∈ uIcc a b, (1 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hpt : ∀ t ∈ uIcc a b, log (c / (t - 1)) / t = log c * (1 / t) - log (t - 1) / t := by
    intro t ht
    have ht1 : 0 < t - 1 := by linarith [hmem t ht]
    rw [log_div (ne_of_gt hc) (ne_of_gt ht1), sub_div]
    ring
  have hsub : (∫ v in (a - 1)..(b - 1), log v / (v + 1)) = ∫ t in a..b, log (t - 1) / t := by
    have h := intervalIntegral.integral_comp_add_right (a := a - 1) (b := b - 1)
      (f := fun u : ℝ => log (u - 1) / u) 1
    simpa only [sub_add_cancel, add_sub_cancel_right] using h
  have hcont1 : ContinuousOn (fun t : ℝ => log c * (1 / t)) (uIcc a b) :=
    continuousOn_const.mul (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (by linarith [hmem t ht])))
  have hcont2 : ContinuousOn (fun t : ℝ => log (t - 1) / t) (uIcc a b) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (by linarith [hmem t ht]))
    have h2 : ContinuousOn (fun t : ℝ => t - 1) (uIcc a b) :=
      continuousOn_id.sub continuousOn_const
    exact Real.continuousOn_log.comp h2 (fun t ht => ne_of_gt (by linarith [hmem t ht]))
  unfold Wu04Integral.sigma
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub hcont1.intervalIntegrable hcont2.intervalIntegrable,
    intervalIntegral.integral_const_mul, integral_one_div_exp (by linarith) hab, ← hsub]

/-- Two-sided bounds for `∫ log v/(v+1)` over `[a-1,b-1]` from the geometric expansion. -/
private theorem integral_log_div_one_add_bounds {a b m : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hm : m = (a + b) / 2 - 1) (n : ℕ) :
    (∫ v in (a - 1)..(b - 1), log v / (v + 1)) ≤
      (∑ k ∈ Finset.range n, (-1) ^ k / (m + 1) ^ (k + 1) *
        (∫ v in (a - 1)..(b - 1), log v * (v - m) ^ k)) +
      (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * (∫ v in (a - 1)..(b - 1), log v) ∧
    (∑ k ∈ Finset.range n, (-1) ^ k / (m + 1) ^ (k + 1) *
        (∫ v in (a - 1)..(b - 1), log v * (v - m) ^ k)) -
      (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * (∫ v in (a - 1)..(b - 1), log v)
      ≤ (∫ v in (a - 1)..(b - 1), log v / (v + 1)) := by
  have hab' : a - 1 ≤ b - 1 := by linarith
  have hM0 : (0 : ℝ) < m + 1 := by
    rw [hm]; linarith
  have hrM : (b - a) / 2 < m + 1 := by
    rw [hm]; linarith
  have hMrho : m + 1 - (b - a) / 2 = a := by
    rw [hm]; ring
  have hmem : ∀ v ∈ Icc (a - 1) (b - 1), (0 : ℝ) < v := by
    intro v hv
    linarith [hv.1]
  have hdist : ∀ v ∈ Icc (a - 1) (b - 1), |v - m| ≤ (b - a) / 2 := by
    intro v hv
    rw [abs_le]
    constructor <;> [linarith [hv.1, hm]; linarith [hv.2, hm]]
  have htail : ∀ v ∈ Icc (a - 1) (b - 1),
      |1 / (v + 1) - ∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)| ≤
        ((b - a) / 2) ^ n / ((m + 1) ^ n * a) := by
    intro v hv
    have hlt : |v - m| < m + 1 := lt_of_le_of_lt (hdist v hv) hrM
    have h := inv_series_remainder hM0 hlt n
    have hvs : (m + 1) + (v - m) = v + 1 := by ring
    rw [hvs] at h
    refine le_trans h ?_
    have hnum : |v - m| ^ n ≤ ((b - a) / 2) ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) (hdist v hv) n
    have hD1 : (0 : ℝ) < (m + 1) ^ n * (m + 1 - |v - m|) := by
      have h1 : 0 < m + 1 - |v - m| := by linarith [hdist v hv, hMrho, ha]
      exact mul_pos (pow_pos hM0 n) h1
    have hD2 : (0 : ℝ) < (m + 1) ^ n * a := mul_pos (pow_pos hM0 n) (by linarith)
    have hden : (m + 1) ^ n * a ≤ (m + 1) ^ n * (m + 1 - |v - m|) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hdist v hv, hMrho]
    refine le_trans (div_le_div_of_nonneg_right hnum hD1.le) ?_
    exact div_le_div_of_nonneg_left (by positivity) hD2 hden
  have hlog : ∀ v ∈ Icc (a - 1) (b - 1), (0 : ℝ) ≤ log v := by
    intro v hv
    exact Real.log_nonneg (by linarith [hmem v hv, hv.1, ha])
  have hmemu : ∀ v ∈ uIcc (a - 1) (b - 1), (0 : ℝ) < v := by
    intro v hv
    rw [uIcc_of_le hab'] at hv
    exact hmem v hv
  have hsub : uIcc (a - 1) (b - 1) ⊆ {0}ᶜ := fun v hv => ne_of_gt (hmemu v hv)
  have hinvint : IntervalIntegrable (fun v : ℝ => log v / (v + 1)) volume (a - 1) (b - 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (Real.continuousOn_log.mono hsub).div (continuousOn_id.add continuousOn_const) ?_
    intro v hv
    have := hmemu v hv
    linarith
  have hlogint : IntervalIntegrable (fun v : ℝ => log v) volume (a - 1) (b - 1) :=
    ContinuousOn.intervalIntegrable (Real.continuousOn_log.mono hsub)
  have hpart : ∀ k : ℕ, IntervalIntegrable
      (fun v : ℝ => log v * ((-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)))
      volume (a - 1) (b - 1) := by
    intro k
    refine ContinuousOn.intervalIntegrable ?_
    refine (Real.continuousOn_log.mono hsub).mul ?_
    have hb : ContinuousOn (fun v : ℝ => (v - m) ^ k) (uIcc (a - 1) (b - 1)) :=
      (continuousOn_id.sub continuousOn_const).pow k
    exact (continuousOn_const.mul hb).div_const ((m + 1) ^ (k + 1))
  have hlin : IntervalIntegrable
      (fun v : ℝ => log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)))
      volume (a - 1) (b - 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine (Real.continuousOn_log.mono hsub).mul ?_
    refine continuousOn_finsetSum _ (fun k _ => ?_)
    have hb : ContinuousOn (fun v : ℝ => (v - m) ^ k) (uIcc (a - 1) (b - 1)) :=
      (continuousOn_id.sub continuousOn_const).pow k
    exact (continuousOn_const.mul hb).div_const ((m + 1) ^ (k + 1))
  have key : ∀ v : ℝ,
      log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) =
      ∑ k ∈ Finset.range n, log v * ((-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) := by
    intro v
    rw [Finset.mul_sum]
  have key2 : ∀ (v : ℝ),
      log v * (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) =
      ((b - a) / 2) ^ n / ((m + 1) ^ n * a) * log v := by
    intro v; ring
  constructor
  · have hpt2 : ∀ v ∈ Icc (a - 1) (b - 1), log v / (v + 1) ≤
        log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) +
          (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * log v := by
      intro v hv
      have h1 := (abs_le.mp (htail v hv)).2
      have h2 := hlog v hv
      have h3 : (1 : ℝ) / (v + 1) ≤
          (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) +
            ((b - a) / 2) ^ n / ((m + 1) ^ n * a) := by linarith
      calc log v / (v + 1) = log v * (1 / (v + 1)) := by ring
        _ ≤ log v * ((∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) +
              ((b - a) / 2) ^ n / ((m + 1) ^ n * a)) :=
            mul_le_mul_of_nonneg_left h3 h2
        _ = log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) +
              (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * log v := by ring
    have hmono := integral_mono_on hab' hinvint (hlin.add (hlogint.const_mul _)) hpt2
    rw [intervalIntegral.integral_add hlin (hlogint.const_mul _)] at hmono
    rw [intervalIntegral.integral_const_mul] at hmono
    have e1 : (∫ v in (a - 1)..(b - 1),
        log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1))) =
        ∑ k ∈ Finset.range n, ((-1) ^ k / (m + 1) ^ (k + 1)) *
          (∫ v in (a - 1)..(b - 1), log v * (v - m) ^ k) := by
      rw [intervalIntegral.integral_congr (fun v _ => key v),
        intervalIntegral.integral_finsetSum (fun k _ => hpart k)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hcw : (∫ x in (a - 1)..(b - 1), log x * ((-1) ^ k * (x - m) ^ k / (m + 1) ^ (k + 1)))
          = ∫ x in (a - 1)..(b - 1),
              ((-1) ^ k / (m + 1) ^ (k + 1)) * (log x * (x - m) ^ k) :=
        intervalIntegral.integral_congr (fun x _ => by ring)
      rw [hcw, intervalIntegral.integral_const_mul]
    rw [e1] at hmono
    simpa using hmono
  · have hpt2 : ∀ v ∈ Icc (a - 1) (b - 1),
        log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) -
          (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * log v ≤ log v / (v + 1) := by
      intro v hv
      have h1 := (abs_le.mp (htail v hv)).1
      have h2 := hlog v hv
      have h3 : (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) -
            ((b - a) / 2) ^ n / ((m + 1) ^ n * a) ≤ (1 : ℝ) / (v + 1) := by linarith
      calc log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) -
            (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * log v
          = log v * ((∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1)) -
              ((b - a) / 2) ^ n / ((m + 1) ^ n * a)) := by ring
        _ ≤ log v * (1 / (v + 1)) := mul_le_mul_of_nonneg_left h3 h2
        _ = log v / (v + 1) := by ring
    have hmono := integral_mono_on hab' (hlin.sub (hlogint.const_mul _)) hinvint hpt2
    rw [intervalIntegral.integral_sub hlin (hlogint.const_mul _)] at hmono
    rw [intervalIntegral.integral_const_mul] at hmono
    have e1 : (∫ v in (a - 1)..(b - 1),
        log v * (∑ k ∈ Finset.range n, (-1) ^ k * (v - m) ^ k / (m + 1) ^ (k + 1))) =
        ∑ k ∈ Finset.range n, ((-1) ^ k / (m + 1) ^ (k + 1)) *
          (∫ v in (a - 1)..(b - 1), log v * (v - m) ^ k) := by
      rw [intervalIntegral.integral_congr (fun v _ => key v),
        intervalIntegral.integral_finsetSum (fun k _ => hpart k)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hcw : (∫ x in (a - 1)..(b - 1), log x * ((-1) ^ k * (x - m) ^ k / (m + 1) ^ (k + 1)))
          = ∫ x in (a - 1)..(b - 1),
              ((-1) ^ k / (m + 1) ^ (k + 1)) * (log x * (x - m) ^ k) :=
        intervalIntegral.integral_congr (fun x _ => by ring)
      rw [hcw, intervalIntegral.integral_const_mul]
    rw [e1] at hmono
    simpa using hmono

/-- `sigma` lower bound: subtract the *upper* bound of the `log v/(v+1)` integral. -/
private theorem sigma_lower_bound {a b c m : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hm : m = (a + b) / 2 - 1) (n : ℕ) :
    log c * log (b / a) -
      ((∑ k ∈ Finset.range n, (-1) ^ k / (m + 1) ^ (k + 1) *
          (∫ v in (a - 1)..(b - 1), log v * (v - m) ^ k)) +
        (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * (∫ v in (a - 1)..(b - 1), log v))
      ≤ Wu04Integral.sigma a b c := by
  have h := (integral_log_div_one_add_bounds ha hab hm n).1
  rw [sigma_eq_log_sub ha hab hc]
  linarith

/-- `sigma` upper bound: subtract the *lower* bound of the `log v/(v+1)` integral. -/
private theorem sigma_upper_bound {a b c m : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 < c)
    (hm : m = (a + b) / 2 - 1) (n : ℕ) :
    Wu04Integral.sigma a b c ≤
      log c * log (b / a) -
        ((∑ k ∈ Finset.range n, (-1) ^ k / (m + 1) ^ (k + 1) *
            (∫ v in (a - 1)..(b - 1), log v * (v - m) ^ k)) -
          (((b - a) / 2) ^ n / ((m + 1) ^ n * a)) * (∫ v in (a - 1)..(b - 1), log v)) := by
  have h := (integral_log_div_one_add_bounds ha hab hm n).2
  rw [sigma_eq_log_sub ha hab hc]
  linarith

/-- Two-sided rational enclosure of `log y` from the atanh series, with `x = (y-1)/(y+1)`. -/
private theorem log_enclosure {y x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy : y = (1 + x) / (1 - x)) (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) ≤ log y ∧
      log y ≤ 2 * (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        2 * (x ^ (2 * n + 1) / (1 - x ^ 2)) := by
  have hxabs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hlo := Real.sum_range_le_log_div hx0 hx1 n
  have hhi := (abs_le.mp (Real.sum_range_sub_log_div_le hxabs n)).2
  rw [abs_of_nonneg hx0] at hhi
  have hlog : (1 / 2 : ℝ) * log ((1 + x) / (1 - x)) = 1 / 2 * log y := by rw [hy]
  constructor
  · linarith
  · linarith

private theorem log_2_2_bounds : (0.78845736036 : ℝ) ≤ log (11/5) ∧ log (11/5) ≤ (0.78845736037 : ℝ) := by
  have h := log_enclosure (y := 11/5) (x := (3/8 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_three_bounds : (1.09861228866 : ℝ) ≤ log 3 ∧ log 3 ≤ (1.09861228867 : ℝ) := by
  have h := log_enclosure (y := 3) (x := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_two_bounds : (0.69314718055 : ℝ) ≤ log 2 ∧ log 2 ≤ (0.69314718056 : ℝ) := by
  have h := log_enclosure (y := 2) (x := (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_four_bounds : (1.3862943611 : ℝ) ≤ log 4 ∧ log 4 ≤ (1.3862943615 : ℝ) := by
  have h := log_enclosure (y := 4) (x := (3/5 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_five_bounds : (1.6094379124 : ℝ) ≤ log 5 ∧ log 5 ≤ (1.6094379125 : ℝ) := by
  have h := log_enclosure (y := 5) (x := (2/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 30
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 1000000 in
/-- `sigma 3 5 4`, the normalising constant of `sigma0`, to `1e-8`. -/
private theorem sigma_3_5_4_bounds_exact :
    (0.171693415 : ℝ) ≤ Wu04Integral.sigma 3 5 4 ∧
      Wu04Integral.sigma 3 5 4 ≤ (0.171693425 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 5) (c := 4) (m := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 14
  have hupp := sigma_upper_bound (a := 3) (b := 5) (c := 4) (m := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 14
  rw [log_div (by norm_num : (5 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((5 : ℝ) - 1) = 4 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 4) (m := 3) (by norm_num) (by norm_num),
    integral_log_mul_pow (a := 2) (b := 4) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.51082562373 : ℝ) ≤ log 5 - log 3 := by
    linarith [log_five_bounds.1, log_three_bounds.2]
  have hdiff_hi : log 5 - log 3 ≤ (0.51082562384 : ℝ) := by
    linarith [log_five_bounds.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log 4 := by linarith [log_four_bounds.1]
  have hp : (0 : ℝ) ≤ (0.51082562373 : ℝ) := by norm_num
  have hlo : (0.70815468168 : ℝ) ≤ log 4 * (log 5 - log 3) := by
    have hm := mul_le_mul log_four_bounds.1 hdiff_lo hp hq
    have hc : (0.70815468168 : ℝ) ≤ (1.3862943611 : ℝ) * (0.51082562373 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi : log 4 * (log 5 - log 3) ≤ (0.70815468204 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log 5 - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_four_bounds.2 hdiff_hi h0 (by norm_num)
    have hc : (1.3862943615 : ℝ) * (0.51082562384 : ℝ) ≤ (0.70815468204 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo, log_four_bounds.1, log_four_bounds.2,
      log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi, log_four_bounds.1, log_four_bounds.2,
      log_two_bounds.1, log_two_bounds.2]

/-- The derivative of `sigma0'` (i.e. `sigma0''`), in closed form. -/
private theorem hasDerivAt_sigma0' {t : ℝ} (ht : 1 < t) (hK : 0 < 1 - Wu04Integral.sigma 3 5 4) :
    HasDerivAt (fun s : ℝ => (log ((s + 2) / 3) / (s + 1)) / (1 - Wu04Integral.sigma 3 5 4))
      (((1 / (t + 2) * (t + 1) - log ((t + 2) / 3)) / (t + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4)) t := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have ht2 : (0 : ℝ) < t + 2 := by linarith
  have hn : HasDerivAt (fun s : ℝ => log ((s + 2) / 3)) (1 / (t + 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s + 2) / 3) (1 / 3) t := by
      have h := ((hasDerivAt_id (x := t)).add_const 2).div_const 3
      simpa using h
    have h := h1.log (by positivity : ((t + 2) / 3) ≠ 0)
    have hval : (1 / 3) / ((t + 2) / 3) = 1 / (t + 2) := by
      field_simp
    rw [← hval]
    exact h
  have hd : HasDerivAt (fun s : ℝ => s + 1) 1 t := (hasDerivAt_id t).add_const 1
  have hq := hn.div hd (ne_of_gt ht1)
  have hq' : HasDerivAt (fun s : ℝ => log ((s + 2) / 3) / (s + 1))
      ((1 / (t + 2) * (t + 1) - log ((t + 2) / 3)) / (t + 1) ^ 2) t := by
    refine hq.congr_deriv ?_
    field_simp
  exact hq'.div_const _

/-- `∫ 1/t` is interval integrable on `[a,b]` with `0 < a`. -/
private theorem inv_integrable_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))

/-- `log (t+1)/t` is interval integrable on `[a,b]` with `0 < a`. -/
private theorem log_succ_div_integrable_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))
  exact Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) (fun t ht => by
    have := lt_of_lt_of_le ha ht.1
    exact ne_of_gt (by linarith : (0 : ℝ) < t + 1))

/-- Derivative of `C (s - a)^2`. -/
private theorem hasDerivAt_const_mul_sq_sub {a C x : ℝ} :
    HasDerivAt (fun s : ℝ => C * (s - a) ^ 2) (2 * C * (x - a)) x := by
  have h2 : HasDerivAt (fun s : ℝ => (s - a) ^ 2) (2 * (x - a)) x := by
    have hlin : HasDerivAt (fun y : ℝ => y ^ 2) (2 * (x - a)) (x - a) := by
      simpa using hasDerivAt_pow 2 (x - a)
    have hcomp := hlin.comp x ((hasDerivAt_id x).sub_const a)
    have hval : 2 * (x - a) * 1 = 2 * (x - a) := by ring
    rw [hval] at hcomp
    simpa [Function.comp_def] using hcomp
  have h3 : HasDerivAt (fun s : ℝ => C * (s - a) ^ 2) (C * (2 * (x - a))) x := h2.const_mul C
  rw [show C * (2 * (x - a)) = 2 * C * (x - a) by ring] at h3
  exact h3

/-- Derivative of `s ↦ 2 * C * (s - a)`. -/
private theorem hasDerivAt_two_mul_const_sub {a C x : ℝ} :
    HasDerivAt (fun s : ℝ => 2 * C * (s - a)) (2 * C) x := by
  have h1 : HasDerivAt (fun s : ℝ => s - a) 1 x := (hasDerivAt_id x).sub_const a
  have h2 := h1.const_mul (2 * C)
  simpa using h2

/-! ### The `j = 0` column: a midpoint quadratic sandwich for `∫ sigma0 t / (2 t)` on `[1, 11/5]`

All nine open entries live on the panel `[1, 11/5]`, and every `sigma0` bound in the file starts
at `11/5`, so that panel needs its own `sigma0` quadrature.  The `sigma0` coefficient is common to
the whole panel, so one quadrature serves all nine rows.

The first-order tangent sandwich is hopeless on `[1, 11/5]` (`sigma0'` vanishes at `t = 1`); the
second-order one taken from the *left* node of a panel loses `O(h^2)`, which needs ~800 panels.
Expanding at the *midpoint* makes the linear term integrate to zero and the loss `O(h^3)`: against
`mpmath` at 35 digits, 100 panels lose `2.0e-9` on `∫ sigma0 t/(2t) = 0.011195954628881546283`,
and 40 panels lose `2.9e-8`.
-/

/-- `sigma0 1 = 0`. -/
private theorem sigma0_one : Wu04Integral.sigma0 1 = 0 := by
  have h : Wu04Integral.sigma 3 3 2 = 0 := by
    unfold Wu04Integral.sigma
    rw [intervalIntegral.integral_same]
  unfold Wu04Integral.sigma0
  rw [show (1 : ℝ) + 2 = 3 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num, h]
  simp

/-- `|sigma0 t| ≤ 2 (t-1)` on `[1, 11/5]`: the squeeze that makes `sigma0` continuous at `1`. -/
private theorem sigma0_abs_le_one {t : ℝ} (ht : t ∈ Set.Icc (1 : ℝ) (11/5)) :
    |Wu04Integral.sigma0 t| ≤ 2 * (t - 1) := by
  have ht1 : (1 : ℝ) ≤ t := ht.1
  have ht2 : t ≤ 11/5 := ht.2
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hsplit := sigma_eq_log_sub (a := 3) (b := t + 2) (c := t + 1)
    (by norm_num) (by linarith) (by linarith)
  have hval : Wu04Integral.sigma0 t =
      (log (t + 1) * log ((t + 2) / 3) - ∫ v in (2 : ℝ)..(t + 1), log v / (v + 1)) /
        (1 - Wu04Integral.sigma 3 5 4) := by
    unfold Wu04Integral.sigma0
    have he : (t : ℝ) + 2 - 1 = t + 1 := by ring
    rw [hsplit, he]
    norm_num
  have h1 : (0 : ℝ) ≤ log (t + 1) := Real.log_nonneg (by linarith)
  have h2 : (0 : ℝ) ≤ log ((t + 2) / 3) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    linarith
  have h3 : log (t + 1) ≤ 11/5 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t + 1 by linarith)
    linarith
  have h4 : log ((t + 2) / 3) ≤ (t - 1) / 3 := by
    have hp : (0 : ℝ) < (t + 2) / 3 := by linarith
    have := Real.log_le_sub_one_of_pos hp
    have he : (t + 2) / 3 - 1 = (t - 1) / 3 := by ring
    linarith
  have hA : log (t + 1) * log ((t + 2) / 3) ≤ (3/4 : ℝ) * (t - 1) := by
    have hm := mul_le_mul h3 h4 h2 (by norm_num)
    nlinarith
  have hQcont : IntervalIntegrable (fun v : ℝ => log v / (v + 1)) volume 2 (t + 1) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by linarith)]
    refine ContinuousOn.div ?_ (continuousOn_id.add continuousOn_const) ?_
    · refine Real.continuousOn_log.mono ?_
      intro v hv
      exact ne_of_gt (by linarith [hv.1])
    · intro v hv
      have : (0 : ℝ) < v := by linarith [hv.1]
      linarith
  have hQ0 : (0 : ℝ) ≤ ∫ v in (2 : ℝ)..(t + 1), log v / (v + 1) := by
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro v hv
    have hv1 : (1 : ℝ) ≤ v := by linarith [hv.1]
    have hlv : (0 : ℝ) ≤ log v := Real.log_nonneg hv1
    have hv0 : (0 : ℝ) < v := by linarith
    positivity
  have hQ1 : (∫ v in (2 : ℝ)..(t + 1), log v / (v + 1)) ≤ (1/2 : ℝ) * (t - 1) := by
    have hstep : (∫ v in (2 : ℝ)..(t + 1), log v / (v + 1)) ≤
        ∫ v in (2 : ℝ)..(t + 1), (1/2 : ℝ) := by
      refine intervalIntegral.integral_mono_on (by linarith) hQcont intervalIntegrable_const ?_
      intro v hv
      have hv0 : (0 : ℝ) < v := by linarith [hv.1]
      have hv2 : (0 : ℝ) < v / 2 := by linarith
      have hl2 : log v = log 2 + log (v / 2) := by
        have hm := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (ne_of_gt hv2)
        rw [show (2 : ℝ) * (v / 2) = v by ring] at hm
        linarith [hm]
      have hb : log (v / 2) ≤ v / 2 - 1 := Real.log_le_sub_one_of_pos hv2
      have hl2b : log 2 ≤ (0.69314718056 : ℝ) := log_two_bounds.2
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < v + 1)]
      nlinarith [hl2, hb, hl2b, hv.2]
    have hconst : (∫ v in (2 : ℝ)..(t + 1), (1/2 : ℝ)) = (1/2) * (t - 1) := by
      rw [intervalIntegral.integral_const]
      ring
    linarith [hstep, hconst]
  rw [hval, abs_div, abs_of_pos hK, div_le_iff₀ hK]
  have hA0 : (0 : ℝ) ≤ log (t + 1) * log ((t + 2) / 3) := mul_nonneg h1 h2
  have habs : |log (t + 1) * log ((t + 2) / 3) - ∫ v in (2 : ℝ)..(t + 1), log v / (v + 1)| ≤
      (3/4 : ℝ) * (t - 1) := by
    rw [abs_le]
    constructor <;> linarith [hA, hA0, hQ0, hQ1]
  have hf : (3/4 : ℝ) * (t - 1) ≤ 2 * (t - 1) * (1 - Wu04Integral.sigma 3 5 4) := by
    have hKl : (828306575 / 10 ^ 9 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by
      linarith [sigma_3_5_4_bounds_exact.2]
    nlinarith [ht1, hKl]
  linarith [habs, hf]

/-- `sigma0` is continuous at `1` from within `[1, 11/5]`. -/
private theorem continuousWithinAt_sigma0_one :
    ContinuousWithinAt Wu04Integral.sigma0 (Set.Icc (1 : ℝ) (11/5)) 1 := by
  have hz : Wu04Integral.sigma0 1 = 0 := sigma0_one
  have hnorm : ∀ᶠ t in 𝓝[Set.Icc (1 : ℝ) (11/5)] 1, ‖Wu04Integral.sigma0 t‖ ≤ 2 * (t - 1) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Real.norm_eq_abs]
    exact sigma0_abs_le_one ht
  have hlim : Tendsto (fun t : ℝ => 2 * (t - 1)) (𝓝[Set.Icc (1 : ℝ) (11/5)] 1) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t) (𝓝[Set.Icc (1 : ℝ) (11/5)] 1) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 : Tendsto (fun t : ℝ => t - 1) (𝓝[Set.Icc (1 : ℝ) (11/5)] 1) (𝓝 (1 - 1)) :=
      h1.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) _ (𝓝 1))
    have h3 := h2.const_mul (2 : ℝ)
    simpa using h3
  have h0 : ∀ᶠ t in 𝓝[Set.Icc (1 : ℝ) (11/5)] 1, 0 ≤ ‖Wu04Integral.sigma0 t‖ :=
    Eventually.of_forall (fun t => norm_nonneg _)
  have hsq : Tendsto Wu04Integral.sigma0 (𝓝[Set.Icc (1 : ℝ) (11/5)] 1) (𝓝 0) := by
    have hs := tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' h0 hnorm hlim)
    simpa using hs
  show Tendsto Wu04Integral.sigma0 (𝓝[Set.Icc (1 : ℝ) (11/5)] 1) (𝓝 (Wu04Integral.sigma0 1))
  rw [hz]
  exact hsq

/-- `sigma0` is continuous on `[1, 11/5]`. -/
private theorem continuousOn_sigma0_Icc :
    ContinuousOn Wu04Integral.sigma0 (Set.Icc (1 : ℝ) (11/5)) := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h1 | h1
  · rw [← h1]
    exact continuousWithinAt_sigma0_one
  · exact ((sigma0_hasDerivAt h1 hK).continuousAt).continuousWithinAt

/-- `log ((t+2)/3) ≤ (t+1)/(t+2)` on `[1, 11/5]`: this is what makes `sigma0'` increasing there. -/
private theorem log_shift_le1 {t : ℝ} (h1 : (1 : ℝ) ≤ t) (h2 : t ≤ 11/5) :
    log ((t + 2) / 3) ≤ (t + 1) / (t + 2) := by
  have hu : (0 : ℝ) < (t + 2) / 3 := by linarith
  have htp : (0 : ℝ) < t + 2 := by linarith
  have hlog : log ((t + 2) / 3) ≤ (t + 2) / 3 - 1 := Real.log_le_sub_one_of_pos hu
  have hstep : (t + 2) / 3 - 1 ≤ (t + 1) / (t + 2) := by
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hsplit : (t + 2) / 3 - 1 = (t - 1) / 3 := by
      field_simp
      ring
    rw [hsplit]
    have hkey : (t - 1) * (t + 2) ≤ (t + 1) * 3 := by nlinarith
    rw [div_le_div_iff₀ h3 htp]
    exact hkey
  linarith

/-- `sigma0'' ≥ 0` on `[1, 11/5]`, i.e. `sigma0` is convex there. -/
private theorem sigma0_second_deriv_nonneg1 {t : ℝ} (h1 : (1 : ℝ) < t) (h2 : t < 11/5) :
    0 ≤ ((1 / (t + 2) * (t + 1) - log ((t + 2) / 3)) / (t + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hle := log_shift_le1 h1.le h2.le
  have hnum : 0 ≤ 1 / (t + 2) * (t + 1) - log ((t + 2) / 3) := by
    have h1' : 1 / (t + 2) * (t + 1) = (t + 1) / (t + 2) := by field_simp
    rw [h1']
    linarith
  exact div_nonneg (div_nonneg hnum (by positivity)) hK.le

/-- `sigma0` is convex on `[1, 11/5]`. -/
private theorem convexOn_sigma0_1 :
    ConvexOn ℝ (Set.Icc (1 : ℝ) (11/5)) Wu04Integral.sigma0 := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc (1 : ℝ) (11/5))
    (f := Wu04Integral.sigma0)
    (f' := fun s : ℝ => (log ((s + 2) / 3) / (s + 1)) / (1 - Wu04Integral.sigma 3 5 4))
    (f'' := fun s : ℝ => ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
      (1 - Wu04Integral.sigma 3 5 4))
    (convex_Icc _ _) ?_ ?_ ?_ ?_
  · exact continuousOn_sigma0_Icc
  · intro x hx
    have hxi : x ∈ Set.Ioo (1 : ℝ) (11/5) := by rwa [interior_Icc] at hx
    exact (sigma0_hasDerivAt hxi.1 hK).hasDerivWithinAt
  · intro x hx
    have hxi : x ∈ Set.Ioo (1 : ℝ) (11/5) := by rwa [interior_Icc] at hx
    exact (hasDerivAt_sigma0' hxi.1 hK).hasDerivWithinAt
  · intro x hx
    have hxi : x ∈ Set.Ioo (1 : ℝ) (11/5) := by rwa [interior_Icc] at hx
    exact sigma0_second_deriv_nonneg1 hxi.1 hxi.2

/-- Second-order Taylor expansion of `sigma0` at an interior point `m` of `[a,b] ⊆ [1, 11/5]`,
valid on both sides of `m`. -/
private theorem sigma0_mid_taylor1 {a b m C t : ℝ} (ha : (1 : ℝ) ≤ a) (hb : b ≤ 11/5)
    (hab : a < b) (hm : m = (a + b) / 2) (ht : t ∈ Set.Icc a b)
    (hC : ∀ s ∈ Set.Icc a b,
      2 * C ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4)) :
    Wu04Integral.sigma0 m +
        ((log ((m + 2) / 3) / (m + 1)) / (1 - Wu04Integral.sigma 3 5 4)) * (t - m) +
        C * (t - m) ^ 2 ≤ Wu04Integral.sigma0 t := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have h3 : a ≤ m := by rw [hm]; linarith
  have h4 : m ≤ b := by rw [hm]; linarith
  have hmgt : a < m := by rw [hm]; linarith
  have hconv : ConvexOn ℝ (Set.Icc a b)
      (fun s : ℝ => Wu04Integral.sigma0 s - C * (s - m) ^ 2) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc a b)
      (f := fun s : ℝ => Wu04Integral.sigma0 s - C * (s - m) ^ 2)
      (f' := fun s : ℝ => ((log ((s + 2) / 3) / (s + 1)) / (1 - Wu04Integral.sigma 3 5 4))
        - 2 * C * (s - m))
      (f'' := fun s : ℝ => ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4) - 2 * C)
      (convex_Icc _ _) ?_ ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · exact continuousOn_sigma0_Icc.mono (fun x hx => ⟨le_trans ha hx.1, le_trans hx.2 hb⟩)
      · exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)
    · intro x hx
      have hxi : x ∈ Set.Ioo a b := by rwa [interior_Icc] at hx
      have hx1 : (1 : ℝ) < x := lt_of_le_of_lt ha hxi.1
      exact ((sigma0_hasDerivAt hx1 hK).sub
        (hasDerivAt_const_mul_sq_sub (a := m) (C := C) (x := x))).hasDerivWithinAt
    · intro x hx
      have hxi : x ∈ Set.Ioo a b := by rwa [interior_Icc] at hx
      have hx1 : (1 : ℝ) < x := lt_of_le_of_lt ha hxi.1
      exact ((hasDerivAt_sigma0' hx1 hK).sub
        (hasDerivAt_two_mul_const_sub (a := m) (C := C) (x := x))).hasDerivWithinAt
    · intro x hx
      have hxi : x ∈ Set.Ioo a b := by rwa [interior_Icc] at hx
      have hmem : x ∈ Set.Icc a b := ⟨le_of_lt hxi.1, le_of_lt hxi.2⟩
      have hcx := hC x hmem
      linarith
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt ha hmgt
  have hgm : HasDerivAt (fun s : ℝ => Wu04Integral.sigma0 s - C * (s - m) ^ 2)
      ((log ((m + 2) / 3) / (m + 1)) / (1 - Wu04Integral.sigma 3 5 4)) m := by
    have h := (sigma0_hasDerivAt hm1 hK).sub
      (hasDerivAt_const_mul_sq_sub (a := m) (C := C) (x := m))
    have hzero : 2 * C * (m - m) = 0 := by ring
    rw [hzero, sub_zero] at h
    exact h
  have hmD : m ∈ Set.Icc a b := ⟨h3, h4⟩
  rcases lt_trichotomy t m with hlt | heq | hgt
  · have htD : t ∈ Set.Icc a b := ht
    have hslope := hconv.slope_le_of_hasDerivAt htD hmD hlt hgm
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < m - t := by linarith
    rw [div_le_iff₀ hpos] at hslope
    have hgt' : t - m = -(m - t) := by ring
    rw [hgt']
    linarith
  · subst heq
    simp
  · have htD : t ∈ Set.Icc a b := ht
    have hslope := hconv.le_slope_of_hasDerivAt hmD htD hgt hgm
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < t - m := by linarith
    rw [le_div_iff₀ hpos] at hslope
    linarith

/-- `∫ (X + B(t-m) + C(t-m)^2)/t` in closed form. -/
private theorem integral_quad_shift_div {a b m X B C : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (X + B * (t - m) + C * (t - m) ^ 2) / t) =
      (X - B * m + C * m ^ 2) * log (b / a) + (B - 2 * C * m) * (b - a) +
        C * (b ^ 2 - a ^ 2) / 2 := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hpt : ∀ t ∈ uIcc a b, (X + B * (t - m) + C * (t - m) ^ 2) / t =
      (X - B * m + C * m ^ 2) * (1 / t) + (B - 2 * C * m) + C * t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => (X - B * m + C * m ^ 2) * (1 / t)) (uIcc a b) :=
    continuousOn_const.mul (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht)))
  have hi1 : IntervalIntegrable (fun t : ℝ => (X - B * m + C * m ^ 2) * (1 / t)) volume a b :=
    hcont.intervalIntegrable
  have hi2 : IntervalIntegrable (fun _ : ℝ => (B - 2 * C * m)) volume a b :=
    intervalIntegrable_const
  have hi3 : IntervalIntegrable (fun t : ℝ => C * t) volume a b := by
    have hc : ContinuousOn (fun t : ℝ => C * t) (uIcc a b) :=
      continuousOn_const.mul continuousOn_id
    exact hc.intervalIntegrable
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add (hi1.add hi2) hi3,
    intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_one_div_exp ha hab,
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  ring

/-- **The midpoint quadratic panel bound** for `∫ sigma0 t/(2t)` on a panel `[a,b] ⊆ [1, 11/5]`. -/
private theorem sigma0_mid_panel {a b m A B C : ℝ} (ha : (1 : ℝ) ≤ a) (hb : b ≤ 11/5)
    (hab : a < b) (hm : m = (a + b) / 2)
    (hA : A ≤ Wu04Integral.sigma0 m)
    (hB : ((log ((m + 2) / 3) / (m + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ B)
    (hC : ∀ s ∈ Set.Icc a b,
      2 * C ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4))
    (hL0 : b - a ≤ m * log (b / a)) :
    (1 / 2) * (A * log (b / a) + B * ((b - a) - m * log (b / a)) +
        C * (m ^ 2 * log (b / a) - m * (b - a))) ≤
      ∫ t in a..b, Wu04Integral.sigma0 t / (2 * t) := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have ha0 : (0 : ℝ) < a := by linarith
  have h3 : a ≤ m := by rw [hm]; linarith
  have h4 : m ≤ b := by rw [hm]; linarith
  have hlogb : 0 ≤ log (b / a) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ ha0]
    linarith
  have hpt : ∀ t ∈ Set.Icc a b,
      (Wu04Integral.sigma0 m + ((log ((m + 2) / 3) / (m + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - m) + C * (t - m) ^ 2) / (2 * t) ≤
        Wu04Integral.sigma0 t / (2 * t) := by
    intro t ht
    have htan := sigma0_mid_taylor1 ha hb hab hm ht hC
    have h2t : (0 : ℝ) < 2 * t := by linarith [ht.1]
    exact div_le_div_of_nonneg_right htan h2t.le
  have hc1 : ContinuousOn (fun t : ℝ => (Wu04Integral.sigma0 m + ((log ((m + 2) / 3) / (m + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - m) + C * (t - m) ^ 2) / (2 * t))
      (Set.Icc a b) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_const.add (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))).add
          (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      positivity
  have hc2 : ContinuousOn (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine continuousOn_sigma0_Icc.mono ?_
      intro t ht
      exact ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
    · intro t ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      positivity
  have hc1' : ContinuousOn (fun t : ℝ => (Wu04Integral.sigma0 m + ((log ((m + 2) / 3) / (m + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - m) + C * (t - m) ^ 2) / (2 * t)) (uIcc a b) := by
    rw [uIcc_of_le (le_of_lt hab)]
    exact hc1
  have hc2' : ContinuousOn (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) (uIcc a b) := by
    rw [uIcc_of_le (le_of_lt hab)]
    exact hc2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hab)
    hc1'.intervalIntegrable hc2'.intervalIntegrable hpt
  have hdiv : (∫ t in a..b, (Wu04Integral.sigma0 m + ((log ((m + 2) / 3) / (m + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - m) + C * (t - m) ^ 2) / (2 * t)) =
      (1 / 2) * (∫ t in a..b, (Wu04Integral.sigma0 m + ((log ((m + 2) / 3) / (m + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - m) + C * (t - m) ^ 2) / t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    field_simp
  rw [hdiv, integral_quad_shift_div (by linarith) (le_of_lt hab)] at hmono
  have hLneg : (b - a) - m * log (b / a) ≤ 0 := by linarith [hL0]
  have hstep : (1 / 2) * (A * log (b / a) + B * ((b - a) - m * log (b / a)) +
      C * (m ^ 2 * log (b / a) - m * (b - a))) ≤
      (1 / 2) * (Wu04Integral.sigma0 m * log (b / a) +
        ((log ((m + 2) / 3) / (m + 1)) / (1 - Wu04Integral.sigma 3 5 4)) *
          ((b - a) - m * log (b / a)) + C * (m ^ 2 * log (b / a) - m * (b - a))) := by
    have h1 : A * log (b / a) ≤ Wu04Integral.sigma0 m * log (b / a) :=
      mul_le_mul_of_nonneg_right hA hlogb
    have h2 : B * ((b - a) - m * log (b / a)) ≤
        ((log ((m + 2) / 3) / (m + 1)) / (1 - Wu04Integral.sigma 3 5 4)) *
          ((b - a) - m * log (b / a)) :=
      mul_le_mul_of_nonpos_right hB hLneg
    linarith
  have hmono' : (1 / 2) * (Wu04Integral.sigma0 m * log (b / a) +
        ((log ((m + 2) / 3) / (m + 1)) / (1 - Wu04Integral.sigma 3 5 4)) *
          ((b - a) - m * log (b / a)) + C * (m ^ 2 * log (b / a) - m * (b - a))) ≤
      ∫ t in a..b, Wu04Integral.sigma0 t / (2 * t) := by
    convert hmono using 2
    rw [hm]
    ring
  exact le_trans hstep hmono'


/-- `sigma0''` bounded on a panel from its *right* endpoint: the numerator
`(s+1)/(s+2) - log ((s+2)/3)` is antitone in `s`, so its value at `b` bounds it below, and
`(s+1)^2 ≤ (b+1)^2`. This is the sharp form of `sigma0_second_lower`, whose proxy uses the left
endpoint and therefore loses a little on every panel. -/
private theorem sigma0_second_lower_sharp {a b C : ℝ} (ha : (1 : ℝ) ≤ a) (hab : a ≤ b)
    (hX : 0 < 1 / (b + 2) * (b + 1) - log ((b + 2) / 3))
    (hC : 2 * C ≤ ((1 / (b + 2) * (b + 1) - log ((b + 2) / 3)) / (b + 1) ^ 2) /
      (1 - Wu04Integral.sigma 3 5 4)) :
    ∀ s ∈ Set.Icc a b,
      2 * C ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4) := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  intro s hs
  have hs2 : (0 : ℝ) < s + 2 := by linarith [hs.1, ha]
  have hb2 : (0 : ℝ) < b + 2 := by linarith [hs.2, hs.1, ha]
  have hq : (0 : ℝ) < (b + 2) / (s + 2) := div_pos hb2 hs2
  have hlog1 : 1 - ((b + 2) / (s + 2))⁻¹ ≤ log ((b + 2) / (s + 2)) :=
    Real.one_sub_inv_le_log_of_pos hq
  have hinv : ((b + 2) / (s + 2))⁻¹ = (s + 2) / (b + 2) := by rw [inv_div]
  rw [hinv] at hlog1
  have hsplit : log ((b + 2) / (s + 2)) = log ((b + 2) / 3) - log ((s + 2) / 3) := by
    rw [Real.log_div hb2.ne' hs2.ne',
      Real.log_div hb2.ne' (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div hs2.ne' (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [hsplit] at hlog1
  have hnum : 1 / (b + 2) * (b + 1) - log ((b + 2) / 3) ≤
      1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
    have e1 : 1 / (b + 2) * (b + 1) = (b + 1) / (b + 2) := by ring
    have e2 : 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) := by ring
    rw [e1, e2]
    have key : (b + 1) / (b + 2) - (s + 1) / (s + 2) = (b - s) / ((b + 2) * (s + 2)) := by
      field_simp
      ring
    have hbs : (0 : ℝ) ≤ b - s := by linarith [hs.2]
    have hs1 : (0 : ℝ) ≤ s + 1 := by linarith [hs.1]
    have hden : (b + 2) ≤ (b + 2) * (s + 2) := by
      nlinarith [hb2, mul_nonneg (le_of_lt hb2) hs1, hs2]
    have hmono : (b - s) / ((b + 2) * (s + 2)) ≤ (b - s) / (b + 2) :=
      div_le_div_of_nonneg_left hbs hb2 hden
    have e3 : 1 - (s + 2) / (b + 2) = (b - s) / (b + 2) := by
      field_simp
      ring
    linarith [key, hlog1, hmono, e3]
  have hdenB : (0 : ℝ) < (b + 1) ^ 2 := by nlinarith [ha, hab]
  have hdens : (0 : ℝ) < (s + 1) ^ 2 := by nlinarith [hs.1, ha]
  have hdens2 : (s + 1) ^ 2 ≤ (b + 1) ^ 2 := by nlinarith [hs.2, hs.1, ha]
  have hstep : (1 / (b + 2) * (b + 1) - log ((b + 2) / 3)) / (b + 1) ^ 2 ≤
      (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2 := by
    rw [div_le_div_iff₀ hdenB hdens]
    nlinarith [hnum, hX.le, hdens2, hdens]
  exact le_trans hC (div_le_div_of_nonneg_right hstep hK.le)

/-- The `(b+1)`-endpoint lower bound for `sigma0''` on `[a,b]` implies the pointwise one. -/
private theorem sigma0_second_lower {a b C : ℝ} (ha : (1 : ℝ) ≤ a) (hab : a ≤ b)
    (hX : 0 < 1 / (a + 2) * (a + 1) - log ((b + 2) / 3))
    (hC : 2 * C ≤ ((1 / (a + 2) * (a + 1) - log ((b + 2) / 3)) / (b + 1) ^ 2) /
      (1 - Wu04Integral.sigma 3 5 4)) :
    ∀ s ∈ Set.Icc a b,
      2 * C ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4) := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  intro s hs
  have h1 : 1 / (a + 2) * (a + 1) ≤ 1 / (s + 2) * (s + 1) := by
    rw [show 1 / (a + 2) * (a + 1) = (a + 1) / (a + 2) by ring,
      show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
      div_le_div_iff₀ (by linarith : (0:ℝ) < a + 2) (by linarith [hs.1] : (0:ℝ) < s + 2)]
    nlinarith [hs.1, ha]
  have h2 : log ((s + 2) / 3) ≤ log ((b + 2) / 3) := by
    refine Real.log_le_log (by linarith [hs.1, ha] : (0:ℝ) < (s + 2) / 3) ?_
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) (by norm_num : (0:ℝ) < 3)]
    linarith [hs.2]
  have hnum : (1 / (a + 2) * (a + 1) - log ((b + 2) / 3)) ≤
      (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) := by linarith
  have hden : (0 : ℝ) < (b + 1) ^ 2 := by nlinarith [ha, hab]
  have hden2 : (s + 1) ^ 2 ≤ (b + 1) ^ 2 := by nlinarith [hs.2, hs.1, ha]
  have hstep : (1 / (a + 2) * (a + 1) - log ((b + 2) / 3)) / (b + 1) ^ 2 ≤
      (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2 := by
    rw [div_le_div_iff₀ hden (by nlinarith [hs.1] : (0:ℝ) < (s + 1) ^ 2)]
    have hs1 : (0:ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := le_trans hX.le hnum
    nlinarith [hnum, hX.le, hs1, hden2]
  exact le_trans hC (div_le_div_of_nonneg_right hstep hK.le)

/-- `sigma0 t/(2t)` is interval integrable on any `[a,b] ⊆ [1, 11/5]`. -/
private theorem sigma0_div_two_integrable_Icc {a b : ℝ} (ha : (1 : ℝ) ≤ a) (hb : b ≤ 11/5)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
  · exact continuousOn_sigma0_Icc.mono (fun t ht => ⟨le_trans ha ht.1, le_trans ht.2 hb⟩)
  · intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    positivity

/-- Tight two-sided bound for `log 2`. -/
private theorem b9_log_two_tight :
    ((346573590279972654708616060729/500000000000000000000000000000 : ℝ) : ℝ) ≤ log 2 ∧ log 2 ≤ ((693147180559945309417232121459/1000000000000000000000000000000 : ℝ) : ℝ) := by
  have h := log_enclosure (y := 2) (x := (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 40
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Log bounds for panel 0 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_0 :
    ((70061919539864630452943673/100000000000000000000000000 : ℝ) ≤ log ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) ∧ log ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) ≤ (2802476781594585218117747/4000000000000000000000000 : ℝ)) ∧
    ((24937707555195368060511/5000000000000000000000000 : ℝ) ≤ log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) ≤ (498754151103907361210221/100000000000000000000000000 : ℝ)) ∧
    (log (((103/100 : ℝ) + 2) / 3) ≤ (31094783916150258900673/3125000000000000000000000 : ℝ)) ∧
    ((147794011207722013663097/5000000000000000000000000 : ℝ) ≤ log ((103/100 : ℝ) / (1 : ℝ)) ∧ log ((103/100 : ℝ) / (1 : ℝ)) ≤ (2955880224154440273261941/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) = (403/200 : ℝ) by norm_num]
    have hkey : log (403/200 : ℝ) = log (2 : ℝ) + log (403/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (403/400 : ℝ)) (x := (3/803 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 6).1
    have hnum : (3736007419350497556102304271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 6, (3/803 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) = (403/200 : ℝ) by norm_num]
    have hkey : log (403/200 : ℝ) = log (2 : ℝ) + log (403/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (403/400 : ℝ)) (x := (3/803 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 6).2
    have hnum : 2 * (∑ i ∈ Finset.range 6, (3/803 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/803 : ℝ) ^ (2 * 6 + 1) / (1 - (3/803 : ℝ) ^ 2)) ≤ (7472014838700995112204628541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) = (201/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (201/200 : ℝ)) (x := (1/401 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 6).1
    have hnum : (24937707555195368060511/5000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 6, (1/401 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) = (201/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (201/200 : ℝ)) (x := (1/401 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 6).2
    have hnum : 2 * (∑ i ∈ Finset.range 6, (1/401 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/401 : ℝ) ^ (2 * 6 + 1) / (1 - (1/401 : ℝ) ^ 2)) ≤ (498754151103907361210221/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((103/100 : ℝ) + 2) / 3) = (101/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (101/100 : ℝ)) (x := (1/201 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (1/201 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/201 : ℝ) ^ (2 * 7 + 1) / (1 - (1/201 : ℝ) ^ 2)) ≤ (31094783916150258900673/3125000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((103/100 : ℝ) / (1 : ℝ)) = (103/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (103/100 : ℝ)) (x := (3/203 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (147794011207722013663097/5000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/203 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((103/100 : ℝ) / (1 : ℝ)) = (103/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (103/100 : ℝ)) (x := (3/203 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/203 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/203 : ℝ) ^ (2 * 8 + 1) / (1 - (3/203 : ℝ) ^ 2)) ≤ (2955880224154440273261941/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 0, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_0 : (449731456848523/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((1 : ℝ) + (103/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2)) (c := ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1)) (m := (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) - 1 = ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1)) (m := (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_0.1
  have hq := b9_lgs_0.2.1
  have hprod : (70061919539864630452943673/100000000000000000000000000 : ℝ) * (24937707555195368060511/5000000000000000000000000 : ℝ) ≤ log ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) * log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((29350748739229070281728126931979549/26662788260971264520435978031205800 : ℝ) : ℝ) * log ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) ≤ ((29350748739229070281728126931979549/26662788260971264520435978031205800 : ℝ) : ℝ) * (2802476781594585218117747/4000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-146088834879887153936541093170686/133313941304856322602179890156029 : ℝ) : ℝ) * log 2 ≤ ((-146088834879887153936541093170686/133313941304856322602179890156029 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (965640533022251029272745330499740929016323598807809228726478249027466049249701/51844310507444125456403290616233500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) * log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) -
      ((29350748739229070281728126931979549/26662788260971264520435978031205800 : ℝ) * log ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) + (-146088834879887153936541093170686/133313941304856322602179890156029 : ℝ) * log 2 + (-102112361647090596890295691810093/12442634521786590109536789747896040 : ℝ)) := by
    have e : (965640533022251029272745330499740929016323598807809228726478249027466049249701/51844310507444125456403290616233500000000000000000000000000000000000000000000000000 : ℝ) = (70061919539864630452943673/100000000000000000000000000 : ℝ) * (24937707555195368060511/5000000000000000000000000 : ℝ) - (((29350748739229070281728126931979549/26662788260971264520435978031205800 : ℝ) : ℝ) * (2802476781594585218117747/4000000000000000000000000 : ℝ) + ((-146088834879887153936541093170686/133313941304856322602179890156029 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-102112361647090596890295691810093/12442634521786590109536789747896040 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (965640533022251029272745330499740929016323598807809228726478249027466049249701/51844310507444125456403290616233500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (449731456848523/20000000000000000000 : ℝ) ≤ (965640533022251029272745330499740929016323598807809228726478249027466049249701/51844310507444125456403290616233500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (965640533022251029272745330499740929016323598807809228726478249027466049249701/51844310507444125456403290616233500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 0 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[1, 103/100]`. -/
private theorem b9_pan_0 : (436247405734118921/1000000000000000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(103/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (449731456848523/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((1 : ℝ) + (103/100 : ℝ)) / 2) := b9_sig_0
  have hB0 : ((log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (298827364159255827/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_0.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) ≤ (498754151103907361210221/100000000000000000000000000 : ℝ) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((1 : ℝ) + (103/100 : ℝ)) / 2) + 2) / 3) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (498754151103907361210221/100000000000000000000000000 : ℝ) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (498754151103907361210221/100000000000000000000000000 : ℝ) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (498754151103907361210221/100000000000000000000000000 : ℝ) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (498754151103907361210221/100000000000000000000000000 : ℝ) / ((((1 : ℝ) + (103/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (298827364159255827/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (1 : ℝ) (103/100 : ℝ), 2 * (120851412125156217/1250000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_0.2.2.1
    have hX : (624953280473406471553096081/946875000000000000000000000 : ℝ) ≤ (1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (624953280473406471553096081/946875000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((103/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (120851412125156217/1250000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (624953280473406471553096081/946875000000000000000000000 : ℝ) / ((103/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (120851412125156217/1250000000000000000 : ℝ) ≤ ((1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) / ((103/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (120851412125156217/1250000000000000000 : ℝ) ≤ (624953280473406471553096081/946875000000000000000000000 : ℝ) / ((103/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (624953280473406471553096081/946875000000000000000000000 : ℝ) / ((103/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) / ((103/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) / ((103/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) / ((103/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((103/100 : ℝ) + 2) * ((103/100 : ℝ) + 1) - log (((103/100 : ℝ) + 2) / 3)) / ((103/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (1 : ℝ)) (b := (103/100 : ℝ)) (C := (120851412125156217/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (103/100 : ℝ) - (1 : ℝ) ≤ (((1 : ℝ) + (103/100 : ℝ)) / 2) * log ((103/100 : ℝ) / (1 : ℝ)) := by
    have hl := b9_lgs_0.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (1 : ℝ)) (b := (103/100 : ℝ)) (m := (((1 : ℝ) + (103/100 : ℝ)) / 2)) (A := (449731456848523/20000000000000000000 : ℝ)) (B := (298827364159255827/100000000000000000000 : ℝ)) (C := (120851412125156217/1250000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_0.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 1 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_1 :
    ((71539778949476506826030717/100000000000000000000000000 : ℝ) ≤ log ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) ∧ log ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) ≤ (71539778949476506826030719/100000000000000000000000000 : ℝ)) ∧
    ((744430624687532741770487/50000000000000000000000000 : ℝ) ≤ log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) ≤ (59554449975002619341639/4000000000000000000000000 : ℝ)) ∧
    (log (((53/50 : ℝ) + 2) / 3) ≤ (1980262729617971302602907/100000000000000000000000000 : ℝ)) ∧
    ((1435505294121568639654947/50000000000000000000000000 : ℝ) ≤ log ((53/50 : ℝ) / (103/100 : ℝ)) ∧ log ((53/50 : ℝ) / (103/100 : ℝ)) ≤ (574202117648627455861979/20000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) = (409/200 : ℝ) by norm_num]
    have hkey : log (409/200 : ℝ) = log (2 : ℝ) + log (409/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (409/400 : ℝ)) (x := (9/809 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (11125304467409879421537524271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (9/809 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) = (409/200 : ℝ) by norm_num]
    have hkey : log (409/200 : ℝ) = log (2 : ℝ) + log (409/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (409/400 : ℝ)) (x := (9/809 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (9/809 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/809 : ℝ) ^ (2 * 8 + 1) / (1 - (9/809 : ℝ) ^ 2)) ≤ (22250608934819758843075068541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) = (203/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (203/200 : ℝ)) (x := (3/403 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (744430624687532741770487/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/403 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) = (203/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (203/200 : ℝ)) (x := (3/403 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/403 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/403 : ℝ) ^ (2 * 7 + 1) / (1 - (3/403 : ℝ) ^ 2)) ≤ (59554449975002619341639/4000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((53/50 : ℝ) + 2) / 3) = (51/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (51/50 : ℝ)) (x := (1/101 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (1/101 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/101 : ℝ) ^ (2 * 8 + 1) / (1 - (1/101 : ℝ) ^ 2)) ≤ (1980262729617971302602907/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((53/50 : ℝ) / (103/100 : ℝ)) = (106/103 : ℝ) by norm_num]
    have h := (log_enclosure (y := (106/103 : ℝ)) (x := (3/209 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (1435505294121568639654947/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/209 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((53/50 : ℝ) / (103/100 : ℝ)) = (106/103 : ℝ) by norm_num]
    have h := (log_enclosure (y := (106/103 : ℝ)) (x := (3/209 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/209 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/209 : ℝ) ^ (2 * 8 + 1) / (1 - (3/209 : ℝ) ^ 2)) ≤ (574202117648627455861979/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 1, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_1 : (4993232903864017/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((103/100 : ℝ) + (53/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2)) (c := ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1)) (m := (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) - 1 = ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1)) (m := (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_1.1
  have hq := b9_lgs_1.2.1
  have hprod : (71539778949476506826030717/100000000000000000000000000 : ℝ) * (744430624687532741770487/50000000000000000000000000 : ℝ) ≤ log ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) * log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((501205148944667364794935093045479383093413/450565138283094764627104272530231308942200 : ℝ) : ℝ) * log ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) ≤ ((501205148944667364794935093045479383093413/450565138283094764627104272530231308942200 : ℝ) : ℝ) * (71539778949476506826030719/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-2472484295987885943059429141098524416474/2252825691415473823135521362651156544711 : ℝ) : ℝ) * log 2 ≤ ((-2472484295987885943059429141098524416474/2252825691415473823135521362651156544711 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (143489872194557261255288043710923129778877557682128968075185585572502030072274125672354713/867337891194957421907175724620695269713735000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) * log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) -
      ((501205148944667364794935093045479383093413/450565138283094764627104272530231308942200 : ℝ) * log ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) + (-2472484295987885943059429141098524416474/2252825691415473823135521362651156544711 : ℝ) * log 2 + (-94773280540825563524549784224746496359121/3854835071977588541809669887203090087616600 : ℝ)) := by
    have e : (143489872194557261255288043710923129778877557682128968075185585572502030072274125672354713/867337891194957421907175724620695269713735000000000000000000000000000000000000000000000000000 : ℝ) = (71539778949476506826030717/100000000000000000000000000 : ℝ) * (744430624687532741770487/50000000000000000000000000 : ℝ) - (((501205148944667364794935093045479383093413/450565138283094764627104272530231308942200 : ℝ) : ℝ) * (71539778949476506826030719/100000000000000000000000000 : ℝ) + ((-2472484295987885943059429141098524416474/2252825691415473823135521362651156544711 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-94773280540825563524549784224746496359121/3854835071977588541809669887203090087616600 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (143489872194557261255288043710923129778877557682128968075185585572502030072274125672354713/867337891194957421907175724620695269713735000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (4993232903864017/25000000000000000000 : ℝ) ≤ (143489872194557261255288043710923129778877557682128968075185585572502030072274125672354713/867337891194957421907175724620695269713735000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (143489872194557261255288043710923129778877557682128968075185585572502030072274125672354713/867337891194957421907175724620695269713735000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 1 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[103/100, 53/50]`. -/
private theorem b9_pan_1 : (1479070486070721801/500000000000000000000000 : ℝ) ≤ ∫ t in (103/100 : ℝ)..(53/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (4993232903864017/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((103/100 : ℝ) + (53/50 : ℝ)) / 2) := b9_sig_1
  have hB0 : ((log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (878961404715220977/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_1.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) ≤ (59554449975002619341639/4000000000000000000000000 : ℝ) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 2) / 3) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (59554449975002619341639/4000000000000000000000000 : ℝ) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (59554449975002619341639/4000000000000000000000000 : ℝ) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (59554449975002619341639/4000000000000000000000000 : ℝ) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (59554449975002619341639/4000000000000000000000000 : ℝ) / ((((103/100 : ℝ) + (53/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (878961404715220977/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (103/100 : ℝ) (53/50 : ℝ), 2 * (9294447339996615403/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_1.2.2.1
    have hX : (9997019802368450390701755229/15300000000000000000000000000 : ℝ) ≤ (1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9997019802368450390701755229/15300000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((53/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (9294447339996615403/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9997019802368450390701755229/15300000000000000000000000000 : ℝ) / ((53/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (9294447339996615403/100000000000000000000 : ℝ) ≤ ((1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) / ((53/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (9294447339996615403/100000000000000000000 : ℝ) ≤ (9997019802368450390701755229/15300000000000000000000000000 : ℝ) / ((53/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9997019802368450390701755229/15300000000000000000000000000 : ℝ) / ((53/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) / ((53/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) / ((53/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) / ((53/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((53/50 : ℝ) + 2) * ((53/50 : ℝ) + 1) - log (((53/50 : ℝ) + 2) / 3)) / ((53/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (103/100 : ℝ)) (b := (53/50 : ℝ)) (C := (9294447339996615403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (53/50 : ℝ) - (103/100 : ℝ) ≤ (((103/100 : ℝ) + (53/50 : ℝ)) / 2) * log ((53/50 : ℝ) / (103/100 : ℝ)) := by
    have hl := b9_lgs_1.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (103/100 : ℝ)) (b := (53/50 : ℝ)) (m := (((103/100 : ℝ) + (53/50 : ℝ)) / 2)) (A := (4993232903864017/25000000000000000000 : ℝ)) (B := (878961404715220977/100000000000000000000 : ℝ)) (C := (9294447339996615403/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_1.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 2 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_2 :
    ((18249028842066540515575413/25000000000000000000000000 : ℝ) ≤ log ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) ∧ log ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) ≤ (36498057684133081031150827/50000000000000000000000000 : ℝ)) ∧
    ((2469261259037150101430767/100000000000000000000000000 : ℝ) ≤ log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) ≤ (154328828689821881339423/6250000000000000000000000 : ℝ)) ∧
    (log (((109/100 : ℝ) + 2) / 3) ≤ (2955880224154440273261941/100000000000000000000000000 : ℝ)) ∧
    ((2790878811707655681561519/100000000000000000000000000 : ℝ) ≤ log ((109/100 : ℝ) / (53/50 : ℝ)) ∧ log ((109/100 : ℝ) / (53/50 : ℝ)) ≤ (34885985146345696019519/1250000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) = (83/40 : ℝ) by norm_num]
    have hkey : log (83/40 : ℝ) = log (2 : ℝ) + log (83/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (83/80 : ℝ)) (x := (3/163 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).1
    have hnum : (18406986561358155602892199271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 9, (3/163 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) = (83/40 : ℝ) by norm_num]
    have hkey : log (83/40 : ℝ) = log (2 : ℝ) + log (83/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (83/80 : ℝ)) (x := (3/163 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).2
    have hnum : 2 * (∑ i ∈ Finset.range 9, (3/163 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/163 : ℝ) ^ (2 * 9 + 1) / (1 - (3/163 : ℝ) ^ 2)) ≤ (36813973122716311205784418541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) = (41/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (41/40 : ℝ)) (x := (1/81 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2469261259037150101430767/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (1/81 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) = (41/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (41/40 : ℝ)) (x := (1/81 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (1/81 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/81 : ℝ) ^ (2 * 8 + 1) / (1 - (1/81 : ℝ) ^ 2)) ≤ (154328828689821881339423/6250000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((109/100 : ℝ) + 2) / 3) = (103/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (103/100 : ℝ)) (x := (3/203 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/203 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/203 : ℝ) ^ (2 * 8 + 1) / (1 - (3/203 : ℝ) ^ 2)) ≤ (2955880224154440273261941/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((109/100 : ℝ) / (53/50 : ℝ)) = (109/106 : ℝ) by norm_num]
    have h := (log_enclosure (y := (109/106 : ℝ)) (x := (3/215 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2790878811707655681561519/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/215 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((109/100 : ℝ) / (53/50 : ℝ)) = (109/106 : ℝ) by norm_num]
    have h := (log_enclosure (y := (109/106 : ℝ)) (x := (3/215 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/215 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/215 : ℝ) ^ (2 * 8 + 1) / (1 - (3/215 : ℝ) ^ 2)) ≤ (34885985146345696019519/1250000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 2, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_2 : (1095242717896511/2000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((53/50 : ℝ) + (109/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2)) (c := ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1)) (m := (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 13
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) - 1 = ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1)) (m := (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_2.1
  have hq := b9_lgs_2.2.1
  have hprod : (18249028842066540515575413/25000000000000000000000000 : ℝ) * (2469261259037150101430767/100000000000000000000000000 : ℝ) ≤ log ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) * log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((463014328854293644808287768471444811/412454100493536599657100832604433720 : ℝ) : ℝ) * log ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) ≤ ((463014328854293644808287768471444811/412454100493536599657100832604433720 : ℝ) : ℝ) * (36498057684133081031150827/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-11320743988487414765932008510801362/10311352512338414991427520815110843 : ℝ) : ℝ) * log 2 ≤ ((-11320743988487414765932008510801362/10311352512338414991427520815110843 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (1300524995638061977304066290561993888083816149815087384305957643832982934198992916217/2867128851347431501783041204423876067500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) * log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) -
      ((463014328854293644808287768471444811/412454100493536599657100832604433720 : ℝ) * log ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) + (-11320743988487414765932008510801362/10311352512338414991427520815110843 : ℝ) * log 2 + (-28124014431369752764250452075571084269/688110924323383560427929889061730256200 : ℝ)) := by
    have e : (1300524995638061977304066290561993888083816149815087384305957643832982934198992916217/2867128851347431501783041204423876067500000000000000000000000000000000000000000000000000 : ℝ) = (18249028842066540515575413/25000000000000000000000000 : ℝ) * (2469261259037150101430767/100000000000000000000000000 : ℝ) - (((463014328854293644808287768471444811/412454100493536599657100832604433720 : ℝ) : ℝ) * (36498057684133081031150827/50000000000000000000000000 : ℝ) + ((-11320743988487414765932008510801362/10311352512338414991427520815110843 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-28124014431369752764250452075571084269/688110924323383560427929889061730256200 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (1300524995638061977304066290561993888083816149815087384305957643832982934198992916217/2867128851347431501783041204423876067500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (1095242717896511/2000000000000000000 : ℝ) ≤ (1300524995638061977304066290561993888083816149815087384305957643832982934198992916217/2867128851347431501783041204423876067500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (1300524995638061977304066290561993888083816149815087384305957643832982934198992916217/2867128851347431501783041204423876067500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 2 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[53/50, 109/100]`. -/
private theorem b9_pan_2 : (772129058782387393/100000000000000000000000 : ℝ) ≤ ∫ t in (53/50 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (1095242717896511/2000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((53/50 : ℝ) + (109/100 : ℝ)) / 2) := b9_sig_2
  have hB0 : ((log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1436672678883419523/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_2.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) ≤ (154328828689821881339423/6250000000000000000000000 : ℝ) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 2) / 3) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (154328828689821881339423/6250000000000000000000000 : ℝ) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (154328828689821881339423/6250000000000000000000000 : ℝ) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (154328828689821881339423/6250000000000000000000000 : ℝ) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (154328828689821881339423/6250000000000000000000000 : ℝ) / ((((53/50 : ℝ) + (109/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1436672678883419523/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (53/50 : ℝ) (109/100 : ℝ), 2 * (2234639573679929043/25000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_2.2.2.1
    have hX : (19986633010736277955562060231/30900000000000000000000000000 : ℝ) ≤ (1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (19986633010736277955562060231/30900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((109/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2234639573679929043/25000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (19986633010736277955562060231/30900000000000000000000000000 : ℝ) / ((109/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2234639573679929043/25000000000000000000 : ℝ) ≤ ((1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) / ((109/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2234639573679929043/25000000000000000000 : ℝ) ≤ (19986633010736277955562060231/30900000000000000000000000000 : ℝ) / ((109/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (19986633010736277955562060231/30900000000000000000000000000 : ℝ) / ((109/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) / ((109/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) / ((109/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) / ((109/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((109/100 : ℝ) + 2) * ((109/100 : ℝ) + 1) - log (((109/100 : ℝ) + 2) / 3)) / ((109/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (53/50 : ℝ)) (b := (109/100 : ℝ)) (C := (2234639573679929043/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (109/100 : ℝ) - (53/50 : ℝ) ≤ (((53/50 : ℝ) + (109/100 : ℝ)) / 2) * log ((109/100 : ℝ) / (53/50 : ℝ)) := by
    have hl := b9_lgs_2.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (53/50 : ℝ)) (b := (109/100 : ℝ)) (m := (((53/50 : ℝ) + (109/100 : ℝ)) / 2)) (A := (1095242717896511/2000000000000000000 : ℝ)) (B := (1436672678883419523/100000000000000000000 : ℝ)) (C := (2234639573679929043/25000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_2.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 3 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_3 :
    ((74431546713434474013550119/100000000000000000000000000 : ℝ) ≤ log ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) ∧ log ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) ≤ (74431546713434474013550121/100000000000000000000000000 : ℝ)) ∧
    ((3440142671733239614402827/100000000000000000000000000 : ℝ) ≤ log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) ≤ (860035667933309903600707/25000000000000000000000000 : ℝ)) ∧
    (log (((28/25 : ℝ) + 2) / 3) ≤ (392207131532812962692009/10000000000000000000000000 : ℝ)) ∧
    ((2715098906595084239696477/100000000000000000000000000 : ℝ) ≤ log ((28/25 : ℝ) / (109/100 : ℝ)) ∧ log ((28/25 : ℝ) / (109/100 : ℝ)) ≤ (1357549453297542119848239/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) = (421/200 : ℝ) by norm_num]
    have hkey : log (421/200 : ℝ) = log (2 : ℝ) + log (421/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (421/400 : ℝ)) (x := (21/821 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).1
    have hnum : (25584143287199715359134534271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 10, (21/821 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) = (421/200 : ℝ) by norm_num]
    have hkey : log (421/200 : ℝ) = log (2 : ℝ) + log (421/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (421/400 : ℝ)) (x := (21/821 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).2
    have hnum : 2 * (∑ i ∈ Finset.range 10, (21/821 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((21/821 : ℝ) ^ (2 * 10 + 1) / (1 - (21/821 : ℝ) ^ 2)) ≤ (51168286574399430718269088541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) = (207/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (207/200 : ℝ)) (x := (7/407 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).1
    have hnum : (3440142671733239614402827/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 9, (7/407 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) = (207/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (207/200 : ℝ)) (x := (7/407 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).2
    have hnum : 2 * (∑ i ∈ Finset.range 9, (7/407 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((7/407 : ℝ) ^ (2 * 9 + 1) / (1 - (7/407 : ℝ) ^ 2)) ≤ (860035667933309903600707/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((28/25 : ℝ) + 2) / 3) = (26/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (26/25 : ℝ)) (x := (1/51 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).2
    have hnum : 2 * (∑ i ∈ Finset.range 9, (1/51 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/51 : ℝ) ^ (2 * 9 + 1) / (1 - (1/51 : ℝ) ^ 2)) ≤ (392207131532812962692009/10000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((28/25 : ℝ) / (109/100 : ℝ)) = (112/109 : ℝ) by norm_num]
    have h := (log_enclosure (y := (112/109 : ℝ)) (x := (3/221 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2715098906595084239696477/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/221 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((28/25 : ℝ) / (109/100 : ℝ)) = (112/109 : ℝ) by norm_num]
    have h := (log_enclosure (y := (112/109 : ℝ)) (x := (3/221 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/221 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/221 : ℝ) ^ (2 * 8 + 1) / (1 - (3/221 : ℝ) ^ 2)) ≤ (1357549453297542119848239/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 3, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_3 : (105959752630635927/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((109/100 : ℝ) + (28/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2)) (c := ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1)) (m := (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 14
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) - 1 = ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1)) (m := (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_3.1
  have hq := b9_lgs_3.2.1
  have hprod : (74431546713434474013550119/100000000000000000000000000 : ℝ) * (3440142671733239614402827/100000000000000000000000000 : ℝ) ≤ log ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) * log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((337399549002308766369269255572032723412271605477/297913842591698264689093102803068031947101354200 : ℝ) : ℝ) * log ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) ≤ ((337399549002308766369269255572032723412271605477/297913842591698264689093102803068031947101354200 : ℝ) : ℝ) * (74431546713434474013550121/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-1635754438891557798757306107717280215627724514/1489569212958491323445465514015340159735506771 : ℝ) : ℝ) * log 2 ≤ ((-1635754438891557798757306107717280215627724514/1489569212958491323445465514015340159735506771 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (89024487054453442637245271878090428427735692618591606355370153127627243529002818771334159440309/101432570215744885358429318335330306115322603930000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) * log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) -
      ((337399549002308766369269255572032723412271605477/297913842591698264689093102803068031947101354200 : ℝ) * log ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) + (-1635754438891557798757306107717280215627724514/1489569212958491323445465514015340159735506771 : ℝ) * log 2 + (-115770218511760796876504517915551839540222204703/2028651404314897707168586366706606122306452078600 : ℝ)) := by
    have e : (89024487054453442637245271878090428427735692618591606355370153127627243529002818771334159440309/101432570215744885358429318335330306115322603930000000000000000000000000000000000000000000000000000 : ℝ) = (74431546713434474013550119/100000000000000000000000000 : ℝ) * (3440142671733239614402827/100000000000000000000000000 : ℝ) - (((337399549002308766369269255572032723412271605477/297913842591698264689093102803068031947101354200 : ℝ) : ℝ) * (74431546713434474013550121/100000000000000000000000000 : ℝ) + ((-1635754438891557798757306107717280215627724514/1489569212958491323445465514015340159735506771 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-115770218511760796876504517915551839540222204703/2028651404314897707168586366706606122306452078600 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (89024487054453442637245271878090428427735692618591606355370153127627243529002818771334159440309/101432570215744885358429318335330306115322603930000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (105959752630635927/100000000000000000000 : ℝ) ≤ (89024487054453442637245271878090428427735692618591606355370153127627243529002818771334159440309/101432570215744885358429318335330306115322603930000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (89024487054453442637245271878090428427735692618591606355370153127627243529002818771334159440309/101432570215744885358429318335330306115322603930000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 3 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[109/100, 28/25]`. -/
private theorem b9_pan_3 : (14453939870904481897/1000000000000000000000000 : ℝ) ≤ ∫ t in (109/100 : ℝ)..(28/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (105959752630635927/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((109/100 : ℝ) + (28/25 : ℝ)) / 2) := b9_sig_3
  have hB0 : ((log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1973027985537750691/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_3.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) ≤ (860035667933309903600707/25000000000000000000000000 : ℝ) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 2) / 3) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (860035667933309903600707/25000000000000000000000000 : ℝ) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (860035667933309903600707/25000000000000000000000000 : ℝ) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (860035667933309903600707/25000000000000000000000000 : ℝ) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (860035667933309903600707/25000000000000000000000000 : ℝ) / ((((109/100 : ℝ) + (28/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1973027985537750691/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (109/100 : ℝ) (28/25 : ℝ), 2 * (8599395532055117599/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_3.2.2.1
    have hX : (249703921870220294455011649/390000000000000000000000000 : ℝ) ≤ (1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (249703921870220294455011649/390000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((28/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (8599395532055117599/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (249703921870220294455011649/390000000000000000000000000 : ℝ) / ((28/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (8599395532055117599/100000000000000000000 : ℝ) ≤ ((1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) / ((28/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (8599395532055117599/100000000000000000000 : ℝ) ≤ (249703921870220294455011649/390000000000000000000000000 : ℝ) / ((28/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (249703921870220294455011649/390000000000000000000000000 : ℝ) / ((28/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) / ((28/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) / ((28/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) / ((28/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((28/25 : ℝ) + 2) * ((28/25 : ℝ) + 1) - log (((28/25 : ℝ) + 2) / 3)) / ((28/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (109/100 : ℝ)) (b := (28/25 : ℝ)) (C := (8599395532055117599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (28/25 : ℝ) - (109/100 : ℝ) ≤ (((109/100 : ℝ) + (28/25 : ℝ)) / 2) * log ((28/25 : ℝ) / (109/100 : ℝ)) := by
    have hl := b9_lgs_3.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (109/100 : ℝ)) (b := (28/25 : ℝ)) (m := (((109/100 : ℝ) + (28/25 : ℝ)) / 2)) (A := (105959752630635927/100000000000000000000 : ℝ)) (B := (1973027985537750691/100000000000000000000 : ℝ)) (C := (8599395532055117599/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_3.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 4 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_4 :
    ((75846664668058787640352681/100000000000000000000000000 : ℝ) ≤ log ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) ∧ log ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) ≤ (75846664668058787640352683/100000000000000000000000000 : ℝ)) ∧
    ((4401688541677432661775597/100000000000000000000000000 : ℝ) ≤ log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) ∧ log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) ≤ (2200844270838716330887799/50000000000000000000000000 : ℝ)) ∧
    (log (((23/20 : ℝ) + 2) / 3) ≤ (4879016416943200306537441/100000000000000000000000000 : ℝ)) ∧
    ((2643325706815552263323093/100000000000000000000000000 : ℝ) ≤ log ((23/20 : ℝ) / (28/25 : ℝ)) ∧ log ((23/20 : ℝ) / (28/25 : ℝ)) ≤ (1321662853407776131661547/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) = (427/200 : ℝ) by norm_num]
    have hkey : log (427/200 : ℝ) = log (2 : ℝ) + log (427/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (427/400 : ℝ)) (x := (27/827 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).1
    have hnum : (32659733060321283493147344271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 10, (27/827 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) = (427/200 : ℝ) by norm_num]
    have hkey : log (427/200 : ℝ) = log (2 : ℝ) + log (427/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (427/400 : ℝ)) (x := (27/827 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).2
    have hnum : 2 * (∑ i ∈ Finset.range 10, (27/827 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((27/827 : ℝ) ^ (2 * 10 + 1) / (1 - (27/827 : ℝ) ^ 2)) ≤ (65319466120642566986294708541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) = (209/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (209/200 : ℝ)) (x := (9/409 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).1
    have hnum : (4401688541677432661775597/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 9, (9/409 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) = (209/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (209/200 : ℝ)) (x := (9/409 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).2
    have hnum : 2 * (∑ i ∈ Finset.range 9, (9/409 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/409 : ℝ) ^ (2 * 9 + 1) / (1 - (9/409 : ℝ) ^ 2)) ≤ (2200844270838716330887799/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((23/20 : ℝ) + 2) / 3) = (21/20 : ℝ) by norm_num]
    have h := (log_enclosure (y := (21/20 : ℝ)) (x := (1/41 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 9).2
    have hnum : 2 * (∑ i ∈ Finset.range 9, (1/41 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/41 : ℝ) ^ (2 * 9 + 1) / (1 - (1/41 : ℝ) ^ 2)) ≤ (4879016416943200306537441/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((23/20 : ℝ) / (28/25 : ℝ)) = (115/112 : ℝ) by norm_num]
    have h := (log_enclosure (y := (115/112 : ℝ)) (x := (3/227 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2643325706815552263323093/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/227 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((23/20 : ℝ) / (28/25 : ℝ)) = (115/112 : ℝ) by norm_num]
    have h := (log_enclosure (y := (115/112 : ℝ)) (x := (3/227 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/227 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/227 : ℝ) ^ (2 * 8 + 1) / (1 - (3/227 : ℝ) ^ 2)) ≤ (1321662853407776131661547/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 4, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_4 : (43235077765899673/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((28/25 : ℝ) + (23/20 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2)) (c := ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1)) (m := (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 15
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) - 1 = ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1)) (m := (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_4.1
  have hq := b9_lgs_4.2.1
  have hprod : (75846664668058787640352681/100000000000000000000000000 : ℝ) * (4401688541677432661775597/100000000000000000000000000 : ℝ) ≤ log ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) * log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((2108347059835510275092392853634515488691798081302303/1845677121051850485790684185826110056185866043169400 : ℝ) : ℝ) * log ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) ≤ ((2108347059835510275092392853634515488691798081302303/1845677121051850485790684185826110056185866043169400 : ℝ) : ℝ) * (75846664668058787640352683/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-70948713551863316887968834087487551956992374607286/64598699236814767002673946503913851966505311510929 : ℝ) : ℝ) * log 2 ≤ ((-70948713551863316887968834087487551956992374607286/64598699236814767002673946503913851966505311510929 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (926286213822613284581569449080693725375408169141254108252331206109447907939083951579475828801186965453/646632979360515817696766204504177658184718168224399290000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) * log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) -
      ((2108347059835510275092392853634515488691798081302303/1845677121051850485790684185826110056185866043169400 : ℝ) * log ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) + (-70948713551863316887968834087487551956992374607286/64598699236814767002673946503913851966505311510929 : ℝ) * log 2 + (-35048852182426115036537423782439580735714728717733923/478987392118900605701308299632724191247939383869925400 : ℝ)) := by
    have e : (926286213822613284581569449080693725375408169141254108252331206109447907939083951579475828801186965453/646632979360515817696766204504177658184718168224399290000000000000000000000000000000000000000000000000000 : ℝ) = (75846664668058787640352681/100000000000000000000000000 : ℝ) * (4401688541677432661775597/100000000000000000000000000 : ℝ) - (((2108347059835510275092392853634515488691798081302303/1845677121051850485790684185826110056185866043169400 : ℝ) : ℝ) * (75846664668058787640352683/100000000000000000000000000 : ℝ) + ((-70948713551863316887968834087487551956992374607286/64598699236814767002673946503913851966505311510929 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-35048852182426115036537423782439580735714728717733923/478987392118900605701308299632724191247939383869925400 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (926286213822613284581569449080693725375408169141254108252331206109447907939083951579475828801186965453/646632979360515817696766204504177658184718168224399290000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (43235077765899673/25000000000000000000 : ℝ) ≤ (926286213822613284581569449080693725375408169141254108252331206109447907939083951579475828801186965453/646632979360515817696766204504177658184718168224399290000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (926286213822613284581569449080693725375408169141254108252331206109447907939083951579475828801186965453/646632979360515817696766204504177658184718168224399290000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 4 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[28/25, 23/20]`. -/
private theorem b9_pan_4 : (1432323682237029531/62500000000000000000000 : ℝ) ≤ ∫ t in (28/25 : ℝ)..(23/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (43235077765899673/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((28/25 : ℝ) + (23/20 : ℝ)) / 2) := b9_sig_4
  have hB0 : ((log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (248903108824649031/10000000000000000000 : ℝ) := by
    have hp := b9_lgs_4.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) ≤ (2200844270838716330887799/50000000000000000000000000 : ℝ) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 2) / 3) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (2200844270838716330887799/50000000000000000000000000 : ℝ) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (2200844270838716330887799/50000000000000000000000000 : ℝ) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (2200844270838716330887799/50000000000000000000000000 : ℝ) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (2200844270838716330887799/50000000000000000000000000 : ℝ) / ((((28/25 : ℝ) + (23/20 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (248903108824649031/10000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (28/25 : ℝ) (23/20 : ℝ), 2 * (4137991718264899331/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_4.2.2.1
    have hX : (3992621965732578380688141217/6300000000000000000000000000 : ℝ) ≤ (1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (3992621965732578380688141217/6300000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((23/20 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (4137991718264899331/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (3992621965732578380688141217/6300000000000000000000000000 : ℝ) / ((23/20 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (4137991718264899331/50000000000000000000 : ℝ) ≤ ((1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) / ((23/20 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (4137991718264899331/50000000000000000000 : ℝ) ≤ (3992621965732578380688141217/6300000000000000000000000000 : ℝ) / ((23/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (3992621965732578380688141217/6300000000000000000000000000 : ℝ) / ((23/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) / ((23/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) / ((23/20 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) / ((23/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((23/20 : ℝ) + 2) * ((23/20 : ℝ) + 1) - log (((23/20 : ℝ) + 2) / 3)) / ((23/20 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (28/25 : ℝ)) (b := (23/20 : ℝ)) (C := (4137991718264899331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (23/20 : ℝ) - (28/25 : ℝ) ≤ (((28/25 : ℝ) + (23/20 : ℝ)) / 2) * log ((23/20 : ℝ) / (28/25 : ℝ)) := by
    have hl := b9_lgs_4.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (28/25 : ℝ)) (b := (23/20 : ℝ)) (m := (((28/25 : ℝ) + (23/20 : ℝ)) / 2)) (A := (43235077765899673/25000000000000000000 : ℝ)) (B := (248903108824649031/10000000000000000000 : ℝ)) (C := (4137991718264899331/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_4.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 5 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_5 :
    ((38621018072722658463353477/50000000000000000000000000 : ℝ) ≤ log ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) ∧ log ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) ≤ (19310509036361329231676739/25000000000000000000000000 : ℝ)) ∧
    ((5354076692802981828874123/100000000000000000000000000 : ℝ) ≤ log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) ≤ (1338519173200745457218531/25000000000000000000000000 : ℝ)) ∧
    (log (((59/50 : ℝ) + 2) / 3) ≤ (1456722703099394388142959/25000000000000000000000000 : ℝ)) ∧
    ((2575249610241469462577033/100000000000000000000000000 : ℝ) ≤ log ((59/50 : ℝ) / (23/20 : ℝ)) ∧ log ((59/50 : ℝ) / (23/20 : ℝ)) ≤ (1287624805120734731288517/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) = (433/200 : ℝ) by norm_num]
    have hkey : log (433/200 : ℝ) = log (2 : ℝ) + log (433/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (433/400 : ℝ)) (x := (33/833 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).1
    have hnum : (39636590447253929924918709271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 11, (33/833 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) = (433/200 : ℝ) by norm_num]
    have hkey : log (433/200 : ℝ) = log (2 : ℝ) + log (433/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (433/400 : ℝ)) (x := (33/833 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (33/833 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((33/833 : ℝ) ^ (2 * 11 + 1) / (1 - (33/833 : ℝ) ^ 2)) ≤ (79273180894507859849837438541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) = (211/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (211/200 : ℝ)) (x := (11/411 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).1
    have hnum : (5354076692802981828874123/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 10, (11/411 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) = (211/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (211/200 : ℝ)) (x := (11/411 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).2
    have hnum : 2 * (∑ i ∈ Finset.range 10, (11/411 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((11/411 : ℝ) ^ (2 * 10 + 1) / (1 - (11/411 : ℝ) ^ 2)) ≤ (1338519173200745457218531/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((59/50 : ℝ) + 2) / 3) = (53/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (53/50 : ℝ)) (x := (3/103 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).2
    have hnum : 2 * (∑ i ∈ Finset.range 10, (3/103 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/103 : ℝ) ^ (2 * 10 + 1) / (1 - (3/103 : ℝ) ^ 2)) ≤ (1456722703099394388142959/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((59/50 : ℝ) / (23/20 : ℝ)) = (118/115 : ℝ) by norm_num]
    have h := (log_enclosure (y := (118/115 : ℝ)) (x := (3/233 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2575249610241469462577033/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/233 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((59/50 : ℝ) / (23/20 : ℝ)) = (118/115 : ℝ) by norm_num]
    have h := (log_enclosure (y := (118/115 : ℝ)) (x := (3/233 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/233 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/233 : ℝ) ^ (2 * 8 + 1) / (1 - (3/233 : ℝ) ^ 2)) ≤ (1287624805120734731288517/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 5, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_5 : (51021512866134821/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((23/20 : ℝ) + (59/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2)) (c := ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1)) (m := (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 16
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) - 1 = ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1)) (m := (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_5.1
  have hq := b9_lgs_5.2.1
  have hprod : (38621018072722658463353477/50000000000000000000000000 : ℝ) * (5354076692802981828874123/100000000000000000000000000 : ℝ) ≤ log ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) * log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((6581196578810102399565057534182080891307590897700164531/5713119374793353360019379322081638766283031534397896200 : ℝ) : ℝ) * log ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) ≤ ((6581196578810102399565057534182080891307590897700164531/5713119374793353360019379322081638766283031534397896200 : ℝ) : ℝ) * (19310509036361329231676739/25000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-4482365561380200024078273944101038765887054352608522/4080799553423823828585270944344027690202165381712783 : ℝ) : ℝ) * log 2 ≤ ((-4482365561380200024078273944101038765887054352608522/4080799553423823828585270944344027690202165381712783 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (27464338929930283676739204378325601931637828817819133948920467571260229162378311573993379858055265824341/12997346577654878894044087957735728193293896740755213855000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) * log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) -
      ((6581196578810102399565057534182080891307590897700164531/5713119374793353360019379322081638766283031534397896200 : ℝ) * log ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) + (-4482365561380200024078273944101038765887054352608522/4080799553423823828585270944344027690202165381712783 : ℝ) * log 2 + (-1405084571435790055326786809007379388254856070078833617/15754359488066519871568591463922094779750177867582077400 : ℝ)) := by
    have e : (27464338929930283676739204378325601931637828817819133948920467571260229162378311573993379858055265824341/12997346577654878894044087957735728193293896740755213855000000000000000000000000000000000000000000000000000 : ℝ) = (38621018072722658463353477/50000000000000000000000000 : ℝ) * (5354076692802981828874123/100000000000000000000000000 : ℝ) - (((6581196578810102399565057534182080891307590897700164531/5713119374793353360019379322081638766283031534397896200 : ℝ) : ℝ) * (19310509036361329231676739/25000000000000000000000000 : ℝ) + ((-4482365561380200024078273944101038765887054352608522/4080799553423823828585270944344027690202165381712783 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-1405084571435790055326786809007379388254856070078833617/15754359488066519871568591463922094779750177867582077400 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (27464338929930283676739204378325601931637828817819133948920467571260229162378311573993379858055265824341/12997346577654878894044087957735728193293896740755213855000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (51021512866134821/20000000000000000000 : ℝ) ≤ (27464338929930283676739204378325601931637828817819133948920467571260229162378311573993379858055265824341/12997346577654878894044087957735728193293896740755213855000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (27464338929930283676739204378325601931637828817819133948920467571260229162378311573993379858055265824341/12997346577654878894044087957735728193293896740755213855000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 5 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[23/20, 59/50]`. -/
private theorem b9_pan_5 : (16450239373946894663/500000000000000000000000 : ℝ) ≤ ∫ t in (23/20 : ℝ)..(59/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (51021512866134821/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((23/20 : ℝ) + (59/50 : ℝ)) / 2) := b9_sig_5
  have hB0 : ((log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2985627198127788311/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_5.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) ≤ (1338519173200745457218531/25000000000000000000000000 : ℝ) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 2) / 3) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (1338519173200745457218531/25000000000000000000000000 : ℝ) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (1338519173200745457218531/25000000000000000000000000 : ℝ) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (1338519173200745457218531/25000000000000000000000000 : ℝ) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (1338519173200745457218531/25000000000000000000000000 : ℝ) / ((((23/20 : ℝ) + (59/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2985627198127788311/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (23/20 : ℝ) (59/50 : ℝ), 2 * (995926858228800847/12500000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_5.2.2.1
    have hX : (2493381090207196292285269519/3975000000000000000000000000 : ℝ) ≤ (1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (2493381090207196292285269519/3975000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((59/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (995926858228800847/12500000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (2493381090207196292285269519/3975000000000000000000000000 : ℝ) / ((59/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (995926858228800847/12500000000000000000 : ℝ) ≤ ((1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) / ((59/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (995926858228800847/12500000000000000000 : ℝ) ≤ (2493381090207196292285269519/3975000000000000000000000000 : ℝ) / ((59/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (2493381090207196292285269519/3975000000000000000000000000 : ℝ) / ((59/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) / ((59/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) / ((59/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) / ((59/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((59/50 : ℝ) + 2) * ((59/50 : ℝ) + 1) - log (((59/50 : ℝ) + 2) / 3)) / ((59/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (23/20 : ℝ)) (b := (59/50 : ℝ)) (C := (995926858228800847/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (59/50 : ℝ) - (23/20 : ℝ) ≤ (((23/20 : ℝ) + (59/50 : ℝ)) / 2) * log ((59/50 : ℝ) / (23/20 : ℝ)) := by
    have hl := b9_lgs_5.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (23/20 : ℝ)) (b := (59/50 : ℝ)) (m := (((23/20 : ℝ) + (59/50 : ℝ)) / 2)) (A := (51021512866134821/20000000000000000000 : ℝ)) (B := (2985627198127788311/100000000000000000000 : ℝ)) (C := (995926858228800847/12500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_5.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 6 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_6 :
    ((78618204652713467253999709/100000000000000000000000000 : ℝ) ≤ log ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) ∧ log ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) ≤ (78618204652713467253999711/100000000000000000000000000 : ℝ)) ∧
    ((6297479916138843527148473/100000000000000000000000000 : ℝ) ≤ log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) ≤ (3148739958069421763574237/50000000000000000000000000 : ℝ)) ∧
    (log (((121/100 : ℝ) + 2) / 3) ≤ (6765864847381480526841591/100000000000000000000000000 : ℝ)) ∧
    ((1255296056553816404530233/50000000000000000000000000 : ℝ) ≤ log ((121/100 : ℝ) / (59/50 : ℝ)) ∧ log ((121/100 : ℝ) / (59/50 : ℝ)) ≤ (2510592113107632809060467/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) = (439/200 : ℝ) by norm_num]
    have hkey : log (439/200 : ℝ) = log (2 : ℝ) + log (439/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (439/400 : ℝ)) (x := (39/839 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).1
    have hnum : (46517432983594681561382484271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 11, (39/839 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) = (439/200 : ℝ) by norm_num]
    have hkey : log (439/200 : ℝ) = log (2 : ℝ) + log (439/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (439/400 : ℝ)) (x := (39/839 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (39/839 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((39/839 : ℝ) ^ (2 * 11 + 1) / (1 - (39/839 : ℝ) ^ 2)) ≤ (93034865967189363122764988541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) = (213/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (213/200 : ℝ)) (x := (13/413 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).1
    have hnum : (6297479916138843527148473/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 10, (13/413 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) = (213/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (213/200 : ℝ)) (x := (13/413 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).2
    have hnum : 2 * (∑ i ∈ Finset.range 10, (13/413 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((13/413 : ℝ) ^ (2 * 10 + 1) / (1 - (13/413 : ℝ) ^ 2)) ≤ (3148739958069421763574237/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((121/100 : ℝ) + 2) / 3) = (107/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (107/100 : ℝ)) (x := (7/207 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 10).2
    have hnum : 2 * (∑ i ∈ Finset.range 10, (7/207 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((7/207 : ℝ) ^ (2 * 10 + 1) / (1 - (7/207 : ℝ) ^ 2)) ≤ (6765864847381480526841591/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((121/100 : ℝ) / (59/50 : ℝ)) = (121/118 : ℝ) by norm_num]
    have h := (log_enclosure (y := (121/118 : ℝ)) (x := (3/239 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (1255296056553816404530233/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/239 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((121/100 : ℝ) / (59/50 : ℝ)) = (121/118 : ℝ) by norm_num]
    have h := (log_enclosure (y := (121/118 : ℝ)) (x := (3/239 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/239 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/239 : ℝ) ^ (2 * 8 + 1) / (1 - (3/239 : ℝ) ^ 2)) ≤ (2510592113107632809060467/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 6, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_6 : (17594639771291423/5000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((59/50 : ℝ) + (121/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2)) (c := ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1)) (m := (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 17
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) - 1 = ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1)) (m := (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_6.1
  have hq := b9_lgs_6.2.1
  have hprod : (78618204652713467253999709/100000000000000000000000000 : ℝ) * (6297479916138843527148473/100000000000000000000000000 : ℝ) ≤ log ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) * log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((3082680789906092954198361358374806625560249645476662703571/2654172364142759289085422996786690784426367718125040041400 : ℝ) : ℝ) * log ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) ≤ ((3082680789906092954198361358374806625560249645476662703571/2654172364142759289085422996786690784426367718125040041400 : ℝ) : ℝ) * (78618204652713467253999711/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-102043718641707330455555231613830185303246873814272480966/92896032744996575117989804887534177454922870134376401449 : ℝ) : ℝ) * log 2 ≤ ((-102043718641707330455555231613830185303246873814272480966/92896032744996575117989804887534177454922870134376401449 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (3544363887935691634710163194028533603846520646830562682359209313200559851462943555710360911470773040783690537/1216009068632005168294486545977822382884940370058987094967410000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) * log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) -
      ((3082680789906092954198361358374806625560249645476662703571/2654172364142759289085422996786690784426367718125040041400 : ℝ) * log ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) + (-102043718641707330455555231613830185303246873814272480966/92896032744996575117989804887534177454922870134376401449 : ℝ) * log 2 + (-65546614331207507247403193270551304123539237555286840077847/623594394170259060663839254347601221992277112850762612803800 : ℝ)) := by
    have e : (3544363887935691634710163194028533603846520646830562682359209313200559851462943555710360911470773040783690537/1216009068632005168294486545977822382884940370058987094967410000000000000000000000000000000000000000000000000000 : ℝ) = (78618204652713467253999709/100000000000000000000000000 : ℝ) * (6297479916138843527148473/100000000000000000000000000 : ℝ) - (((3082680789906092954198361358374806625560249645476662703571/2654172364142759289085422996786690784426367718125040041400 : ℝ) : ℝ) * (78618204652713467253999711/100000000000000000000000000 : ℝ) + ((-102043718641707330455555231613830185303246873814272480966/92896032744996575117989804887534177454922870134376401449 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-65546614331207507247403193270551304123539237555286840077847/623594394170259060663839254347601221992277112850762612803800 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (3544363887935691634710163194028533603846520646830562682359209313200559851462943555710360911470773040783690537/1216009068632005168294486545977822382884940370058987094967410000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (17594639771291423/5000000000000000000 : ℝ) ≤ (3544363887935691634710163194028533603846520646830562682359209313200559851462943555710360911470773040783690537/1216009068632005168294486545977822382884940370058987094967410000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (3544363887935691634710163194028533603846520646830562682359209313200559851462943555710360911470773040783690537/1216009068632005168294486545977822382884940370058987094967410000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 6 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[59/50, 121/100]`. -/
private theorem b9_pan_6 : (22108957431577971909/500000000000000000000000 : ℝ) ≤ ∫ t in (59/50 : ℝ)..(121/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (17594639771291423/5000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((59/50 : ℝ) + (121/100 : ℝ)) / 2) := b9_sig_6
  have hB0 : ((log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1731853541858038393/50000000000000000000 : ℝ) := by
    have hp := b9_lgs_6.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) ≤ (3148739958069421763574237/50000000000000000000000000 : ℝ) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 2) / 3) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (3148739958069421763574237/50000000000000000000000000 : ℝ) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (3148739958069421763574237/50000000000000000000000000 : ℝ) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (3148739958069421763574237/50000000000000000000000000 : ℝ) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (3148739958069421763574237/50000000000000000000000000 : ℝ) / ((((59/50 : ℝ) + (121/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1731853541858038393/50000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (59/50 : ℝ) (121/100 : ℝ), 2 * (306913821145204693/4000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_6.2.2.1
    have hX : (19928157383990544750883849289/32100000000000000000000000000 : ℝ) ≤ (1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (19928157383990544750883849289/32100000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((121/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (306913821145204693/4000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (19928157383990544750883849289/32100000000000000000000000000 : ℝ) / ((121/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (306913821145204693/4000000000000000000 : ℝ) ≤ ((1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) / ((121/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (306913821145204693/4000000000000000000 : ℝ) ≤ (19928157383990544750883849289/32100000000000000000000000000 : ℝ) / ((121/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (19928157383990544750883849289/32100000000000000000000000000 : ℝ) / ((121/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) / ((121/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) / ((121/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) / ((121/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((121/100 : ℝ) + 2) * ((121/100 : ℝ) + 1) - log (((121/100 : ℝ) + 2) / 3)) / ((121/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (59/50 : ℝ)) (b := (121/100 : ℝ)) (C := (306913821145204693/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (121/100 : ℝ) - (59/50 : ℝ) ≤ (((59/50 : ℝ) + (121/100 : ℝ)) / 2) * log ((121/100 : ℝ) / (59/50 : ℝ)) := by
    have hl := b9_lgs_6.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (59/50 : ℝ)) (b := (121/100 : ℝ)) (m := (((59/50 : ℝ) + (121/100 : ℝ)) / 2)) (A := (17594639771291423/5000000000000000000 : ℝ)) (B := (1731853541858038393/50000000000000000000 : ℝ)) (C := (306913821145204693/4000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_6.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 7 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_7 :
    ((4998480722613772096658499/6250000000000000000000000 : ℝ) ≤ log ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) ∧ log ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) ≤ (39987845780910176773267993/50000000000000000000000000 : ℝ)) ∧
    ((7232066157962612062038681/100000000000000000000000000 : ℝ) ≤ log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) ≤ (3616033078981306031019341/50000000000000000000000000 : ℝ)) ∧
    (log (((31/25 : ℝ) + 2) / 3) ≤ (1539220822722566499684341/20000000000000000000000000 : ℝ)) ∧
    ((2449102000829577663974141/100000000000000000000000000 : ℝ) ≤ log ((31/25 : ℝ) / (121/100 : ℝ)) ∧ log ((31/25 : ℝ) / (121/100 : ℝ)) ≤ (1224551000414788831987071/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) = (89/40 : ℝ) by norm_num]
    have hkey : log (89/40 : ℝ) = log (2 : ℝ) + log (89/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (89/80 : ℝ)) (x := (9/169 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    have hnum : (53304867529129113024063859271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 12, (9/169 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) = (89/40 : ℝ) by norm_num]
    have hkey : log (89/40 : ℝ) = log (2 : ℝ) + log (89/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (89/80 : ℝ)) (x := (9/169 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (9/169 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/169 : ℝ) ^ (2 * 12 + 1) / (1 - (9/169 : ℝ) ^ 2)) ≤ (106609735058258226048127738541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) = (43/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (43/40 : ℝ)) (x := (3/83 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).1
    have hnum : (7232066157962612062038681/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 11, (3/83 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) = (43/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (43/40 : ℝ)) (x := (3/83 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (3/83 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/83 : ℝ) ^ (2 * 11 + 1) / (1 - (3/83 : ℝ) ^ 2)) ≤ (3616033078981306031019341/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((31/25 : ℝ) + 2) / 3) = (27/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (27/25 : ℝ)) (x := (1/26 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (1/26 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/26 : ℝ) ^ (2 * 11 + 1) / (1 - (1/26 : ℝ) ^ 2)) ≤ (1539220822722566499684341/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((31/25 : ℝ) / (121/100 : ℝ)) = (124/121 : ℝ) by norm_num]
    have h := (log_enclosure (y := (124/121 : ℝ)) (x := (3/245 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2449102000829577663974141/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/245 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((31/25 : ℝ) / (121/100 : ℝ)) = (124/121 : ℝ) by norm_num]
    have h := (log_enclosure (y := (124/121 : ℝ)) (x := (3/245 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/245 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/245 : ℝ) ^ (2 * 8 + 1) / (1 - (3/245 : ℝ) ^ 2)) ≤ (1224551000414788831987071/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 7, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_7 : (92550648262134667/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((121/100 : ℝ) + (31/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2)) (c := ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1)) (m := (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 18
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) - 1 = ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1)) (m := (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_7.1
  have hq := b9_lgs_7.2.1
  have hprod : (4998480722613772096658499/6250000000000000000000000 : ℝ) * (7232066157962612062038681/100000000000000000000000000 : ℝ) ≤ log ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) * log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((13873071980189375947944557206712394676633146539189/11848836515524563543988331701308485996949780155160 : ℝ) : ℝ) * log ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) ≤ ((13873071980189375947944557206712394676633146539189/11848836515524563543988331701308485996949780155160 : ℝ) : ℝ) * (39987845780910176773267993/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-2277827349776616331285923447303040807121347149302/2073546390216798620197958047728985049466211527153 : ℝ) : ℝ) * log 2 ≤ ((-2277827349776616331285923447303040807121347149302/2073546390216798620197958047728985049466211527153 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (3130787502032788735532909290236576339867084922833968485378235962250241094457242403042011146292835897/816794882461094030553441020791762467286262073091726875000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) * log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) -
      ((13873071980189375947944557206712394676633146539189/11848836515524563543988331701308485996949780155160 : ℝ) * log ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) + (-2277827349776616331285923447303040807121347149302/2073546390216798620197958047728985049466211527153 : ℝ) * log 2 + (-18967262090403321393026231878908113613635971558727131/156824617432530053866260675992018393718962318033611560 : ℝ)) := by
    have e : (3130787502032788735532909290236576339867084922833968485378235962250241094457242403042011146292835897/816794882461094030553441020791762467286262073091726875000000000000000000000000000000000000000000000000 : ℝ) = (4998480722613772096658499/6250000000000000000000000 : ℝ) * (7232066157962612062038681/100000000000000000000000000 : ℝ) - (((13873071980189375947944557206712394676633146539189/11848836515524563543988331701308485996949780155160 : ℝ) : ℝ) * (39987845780910176773267993/50000000000000000000000000 : ℝ) + ((-2277827349776616331285923447303040807121347149302/2073546390216798620197958047728985049466211527153 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-18967262090403321393026231878908113613635971558727131/156824617432530053866260675992018393718962318033611560 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (3130787502032788735532909290236576339867084922833968485378235962250241094457242403042011146292835897/816794882461094030553441020791762467286262073091726875000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (92550648262134667/20000000000000000000 : ℝ) ≤ (3130787502032788735532909290236576339867084922833968485378235962250241094457242403042011146292835897/816794882461094030553441020791762467286262073091726875000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (3130787502032788735532909290236576339867084922833968485378235962250241094457242403042011146292835897/816794882461094030553441020791762467286262073091726875000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 7 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[121/100, 31/25]`. -/
private theorem b9_pan_7 : (56704960366603059517/1000000000000000000000000 : ℝ) ≤ ∫ t in (121/100 : ℝ)..(31/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (92550648262134667/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((121/100 : ℝ) + (31/25 : ℝ)) / 2) := b9_sig_7
  have hB0 : ((log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (245256927708761253/6250000000000000000 : ℝ) := by
    have hp := b9_lgs_7.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) ≤ (3616033078981306031019341/50000000000000000000000000 : ℝ) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 2) / 3) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (3616033078981306031019341/50000000000000000000000000 : ℝ) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (3616033078981306031019341/50000000000000000000000000 : ℝ) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (3616033078981306031019341/50000000000000000000000000 : ℝ) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (3616033078981306031019341/50000000000000000000000000 : ℝ) / ((((121/100 : ℝ) + (31/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (245256927708761253/6250000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (121/100 : ℝ) (31/25 : ℝ), 2 * (7391488890494032541/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_7.2.2.1
    have hX : (995323113359472113525568379/1620000000000000000000000000 : ℝ) ≤ (1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (995323113359472113525568379/1620000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((31/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (7391488890494032541/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (995323113359472113525568379/1620000000000000000000000000 : ℝ) / ((31/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (7391488890494032541/100000000000000000000 : ℝ) ≤ ((1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) / ((31/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (7391488890494032541/100000000000000000000 : ℝ) ≤ (995323113359472113525568379/1620000000000000000000000000 : ℝ) / ((31/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (995323113359472113525568379/1620000000000000000000000000 : ℝ) / ((31/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) / ((31/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) / ((31/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) / ((31/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((31/25 : ℝ) + 2) * ((31/25 : ℝ) + 1) - log (((31/25 : ℝ) + 2) / 3)) / ((31/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (121/100 : ℝ)) (b := (31/25 : ℝ)) (C := (7391488890494032541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (31/25 : ℝ) - (121/100 : ℝ) ≤ (((121/100 : ℝ) + (31/25 : ℝ)) / 2) * log ((31/25 : ℝ) / (121/100 : ℝ)) := by
    have hl := b9_lgs_7.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (121/100 : ℝ)) (b := (31/25 : ℝ)) (m := (((121/100 : ℝ) + (31/25 : ℝ)) / 2)) (A := (92550648262134667/20000000000000000000 : ℝ)) (B := (245256927708761253/6250000000000000000 : ℝ)) (C := (7391488890494032541/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_7.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 8 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_8 :
    ((81314997295464167047549191/100000000000000000000000000 : ℝ) ≤ log ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) ∧ log ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) ≤ (81314997295464167047549193/100000000000000000000000000 : ℝ)) ∧
    ((8157998699242287358130203/100000000000000000000000000 : ℝ) ≤ log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) ≤ (2039499674810571839532551/25000000000000000000000000 : ℝ)) ∧
    (log (((127/100 : ℝ) + 2) / 3) ≤ (1723553924821046646826671/20000000000000000000000000 : ℝ)) ∧
    ((298819010669430103547653/12500000000000000000000000 : ℝ) ≤ log ((127/100 : ℝ) / (31/25 : ℝ)) ∧ log ((127/100 : ℝ) / (31/25 : ℝ)) ≤ (95622083414217633135249/4000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) = (451/200 : ℝ) by norm_num]
    have hkey : log (451/200 : ℝ) = log (2 : ℝ) + log (451/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (451/400 : ℝ)) (x := (51/851 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    have hnum : (60001396197348180529129894271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 12, (51/851 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) = (451/200 : ℝ) by norm_num]
    have hkey : log (451/200 : ℝ) = log (2 : ℝ) + log (451/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (451/400 : ℝ)) (x := (51/851 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (51/851 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((51/851 : ℝ) ^ (2 * 12 + 1) / (1 - (51/851 : ℝ) ^ 2)) ≤ (120002792394696361058259808541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) = (217/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (217/200 : ℝ)) (x := (17/417 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).1
    have hnum : (8157998699242287358130203/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 11, (17/417 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) = (217/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (217/200 : ℝ)) (x := (17/417 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (17/417 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((17/417 : ℝ) ^ (2 * 11 + 1) / (1 - (17/417 : ℝ) ^ 2)) ≤ (2039499674810571839532551/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((127/100 : ℝ) + 2) / 3) = (109/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (109/100 : ℝ)) (x := (9/209 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (9/209 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/209 : ℝ) ^ (2 * 11 + 1) / (1 - (9/209 : ℝ) ^ 2)) ≤ (1723553924821046646826671/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((127/100 : ℝ) / (31/25 : ℝ)) = (127/124 : ℝ) by norm_num]
    have h := (log_enclosure (y := (127/124 : ℝ)) (x := (3/251 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (298819010669430103547653/12500000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/251 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((127/100 : ℝ) / (31/25 : ℝ)) = (127/124 : ℝ) by norm_num]
    have h := (log_enclosure (y := (127/124 : ℝ)) (x := (3/251 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/251 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/251 : ℝ) ^ (2 * 8 + 1) / (1 - (3/251 : ℝ) ^ 2)) ≤ (95622083414217633135249/4000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 8, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_8 : (587170625534791297/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((31/25 : ℝ) + (127/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2)) (c := ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1)) (m := (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 18
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) - 1 = ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1)) (m := (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_8.1
  have hq := b9_lgs_8.2.1
  have hprod : (81314997295464167047549191/100000000000000000000000000 : ℝ) * (8157998699242287358130203/100000000000000000000000000 : ℝ) ≤ log ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) * log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((185059189009529783682348188129959490485335668610004875054940811/156817452074608261031770100022014698888422457749168881093784600 : ℝ) : ℝ) * log ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) ≤ ((185059189009529783682348188129959490485335668610004875054940811/156817452074608261031770100022014698888422457749168881093784600 : ℝ) : ℝ) * (81314997295464167047549193/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-9474631282000408940697115531119444520476471966328276405652102/8624959864103454356747355501210808438863235176204288460158153 : ℝ) : ℝ) * log 2 ≤ ((-9474631282000408940697115531119444520476471966328276405652102/8624959864103454356747355501210808438863235176204288460158153 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (2856467324313895687648034358175873635474410209710170250599034147192250855502548858031744640588922238041476140927/587318695507997130007081826987212193694020300093911071334578990000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) * log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) -
      ((185059189009529783682348188129959490485335668610004875054940811/156817452074608261031770100022014698888422457749168881093784600 : ℝ) * log ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) + (-9474631282000408940697115531119444520476471966328276405652102/8624959864103454356747355501210808438863235176204288460158153 : ℝ) * log 2 + (-661125637326809728244010454289016497809272953022294544643147813/4836742198301152835352438575188806301009578941949855881578885800 : ℝ)) := by
    have e : (2856467324313895687648034358175873635474410209710170250599034147192250855502548858031744640588922238041476140927/587318695507997130007081826987212193694020300093911071334578990000000000000000000000000000000000000000000000000000 : ℝ) = (81314997295464167047549191/100000000000000000000000000 : ℝ) * (8157998699242287358130203/100000000000000000000000000 : ℝ) - (((185059189009529783682348188129959490485335668610004875054940811/156817452074608261031770100022014698888422457749168881093784600 : ℝ) : ℝ) * (81314997295464167047549193/100000000000000000000000000 : ℝ) + ((-9474631282000408940697115531119444520476471966328276405652102/8624959864103454356747355501210808438863235176204288460158153 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-661125637326809728244010454289016497809272953022294544643147813/4836742198301152835352438575188806301009578941949855881578885800 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (2856467324313895687648034358175873635474410209710170250599034147192250855502548858031744640588922238041476140927/587318695507997130007081826987212193694020300093911071334578990000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (587170625534791297/100000000000000000000 : ℝ) ≤ (2856467324313895687648034358175873635474410209710170250599034147192250855502548858031744640588922238041476140927/587318695507997130007081826987212193694020300093911071334578990000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (2856467324313895687648034358175873635474410209710170250599034147192250855502548858031744640588922238041476140927/587318695507997130007081826987212193694020300093911071334578990000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 8 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[31/25, 127/100]`. -/
private theorem b9_pan_8 : (35107876102636064007/500000000000000000000000 : ℝ) ≤ ∫ t in (31/25 : ℝ)..(127/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (587170625534791297/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((31/25 : ℝ) + (127/100 : ℝ)) / 2) := b9_sig_8
  have hB0 : ((log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (4367631371716547467/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_8.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) ≤ (2039499674810571839532551/25000000000000000000000000 : ℝ) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 2) / 3) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (2039499674810571839532551/25000000000000000000000000 : ℝ) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (2039499674810571839532551/25000000000000000000000000 : ℝ) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (2039499674810571839532551/25000000000000000000000000 : ℝ) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (2039499674810571839532551/25000000000000000000000000 : ℝ) / ((((31/25 : ℝ) + (127/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (4367631371716547467/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (31/25 : ℝ) (127/100 : ℝ), 2 * (445163222007215137/6250000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_8.2.2.1
    have hX : (3976397866583517746487678583/6540000000000000000000000000 : ℝ) ≤ (1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (3976397866583517746487678583/6540000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((127/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (445163222007215137/6250000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (3976397866583517746487678583/6540000000000000000000000000 : ℝ) / ((127/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (445163222007215137/6250000000000000000 : ℝ) ≤ ((1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) / ((127/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (445163222007215137/6250000000000000000 : ℝ) ≤ (3976397866583517746487678583/6540000000000000000000000000 : ℝ) / ((127/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (3976397866583517746487678583/6540000000000000000000000000 : ℝ) / ((127/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) / ((127/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) / ((127/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) / ((127/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((127/100 : ℝ) + 2) * ((127/100 : ℝ) + 1) - log (((127/100 : ℝ) + 2) / 3)) / ((127/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (31/25 : ℝ)) (b := (127/100 : ℝ)) (C := (445163222007215137/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (127/100 : ℝ) - (31/25 : ℝ) ≤ (((31/25 : ℝ) + (127/100 : ℝ)) / 2) * log ((127/100 : ℝ) / (31/25 : ℝ)) := by
    have hl := b9_lgs_8.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (31/25 : ℝ)) (b := (127/100 : ℝ)) (m := (((31/25 : ℝ) + (127/100 : ℝ)) / 2)) (A := (587170625534791297/100000000000000000000 : ℝ)) (B := (4367631371716547467/100000000000000000000 : ℝ)) (C := (445163222007215137/6250000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_8.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 9 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_9 :
    ((41318301217308401086995817/50000000000000000000000000 : ℝ) ≤ log ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) ∧ log ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) ≤ (20659150608654200543497909/25000000000000000000000000 : ℝ)) ∧
    ((4537718163423207151706953/50000000000000000000000000 : ℝ) ≤ log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) ∧ log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) ≤ (9075436326846414303413907/100000000000000000000000000 : ℝ)) ∧
    (log (((13/10 : ℝ) + 2) / 3) ≤ (9531017980432486004395213/100000000000000000000000000 : ℝ)) ∧
    ((72960512490597334450119/3125000000000000000000000 : ℝ) ≤ log ((13/10 : ℝ) / (127/100 : ℝ)) ∧ log ((13/10 : ℝ) / (127/100 : ℝ)) ≤ (2334736399699114702403809/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) = (457/200 : ℝ) by norm_num]
    have hkey : log (457/200 : ℝ) = log (2 : ℝ) + log (457/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (457/400 : ℝ)) (x := (57/857 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).1
    have hnum : (66609421893111356161342109271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 13, (57/857 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) = (457/200 : ℝ) by norm_num]
    have hkey : log (457/200 : ℝ) = log (2 : ℝ) + log (457/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (457/400 : ℝ)) (x := (57/857 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (57/857 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((57/857 : ℝ) ^ (2 * 13 + 1) / (1 - (57/857 : ℝ) ^ 2)) ≤ (133218843786222712322684238541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) = (219/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (219/200 : ℝ)) (x := (19/419 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).1
    have hnum : (4537718163423207151706953/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 11, (19/419 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) = (219/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (219/200 : ℝ)) (x := (19/419 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (19/419 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((19/419 : ℝ) ^ (2 * 11 + 1) / (1 - (19/419 : ℝ) ^ 2)) ≤ (9075436326846414303413907/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((13/10 : ℝ) + 2) / 3) = (11/10 : ℝ) by norm_num]
    have h := (log_enclosure (y := (11/10 : ℝ)) (x := (1/21 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 11).2
    have hnum : 2 * (∑ i ∈ Finset.range 11, (1/21 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/21 : ℝ) ^ (2 * 11 + 1) / (1 - (1/21 : ℝ) ^ 2)) ≤ (9531017980432486004395213/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((13/10 : ℝ) / (127/100 : ℝ)) = (130/127 : ℝ) by norm_num]
    have h := (log_enclosure (y := (130/127 : ℝ)) (x := (3/257 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (72960512490597334450119/3125000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/257 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((13/10 : ℝ) / (127/100 : ℝ)) = (130/127 : ℝ) by norm_num]
    have h := (log_enclosure (y := (130/127 : ℝ)) (x := (3/257 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/257 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/257 : ℝ) ^ (2 * 8 + 1) / (1 - (3/257 : ℝ) ^ 2)) ≤ (2334736399699114702403809/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 9, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_9 : (724649790625397709/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((127/100 : ℝ) + (13/10 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2)) (c := ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1)) (m := (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 19
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) - 1 = ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1)) (m := (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_9.1
  have hq := b9_lgs_9.2.1
  have hprod : (41318301217308401086995817/50000000000000000000000000 : ℝ) * (4537718163423207151706953/50000000000000000000000000 : ℝ) ≤ log ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) * log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((17801196660523797931363426389006663085033715340531303210754528219403/14967805333294218161872350987740651945080449974797819822114000763400 : ℝ) : ℝ) * log ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) ≤ ((17801196660523797931363426389006663085033715340531303210754528219403/14967805333294218161872350987740651945080449974797819822114000763400 : ℝ) : ℝ) * (20659150608654200543497909/25000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-82214015089871797192975108712948018597540960497088123626431095878/74839026666471090809361754938703259725402249873989099110570003817 : ℝ) : ℝ) * log 2 ≤ ((-82214015089871797192975108712948018597540960497088123626431095878/74839026666471090809361754938703259725402249873989099110570003817 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (19110428416258022124398831198263858967687611829476804735343765215110139223272933038465314733310422568084909192626822289/3183839291958346380757272459479783426867925215264181248911424387384722500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) * log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) -
      ((17801196660523797931363426389006663085033715340531303210754528219403/14967805333294218161872350987740651945080449974797819822114000763400 : ℝ) * log ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) + (-82214015089871797192975108712948018597540960497088123626431095878/74839026666471090809361754938703259725402249873989099110570003817 : ℝ) * log 2 + (-680779353281044313760102825490500252819250440326022023938961211639443/4468546374678380885273364855410222353498842407388324559875683350715400 : ℝ)) := by
    have e : (19110428416258022124398831198263858967687611829476804735343765215110139223272933038465314733310422568084909192626822289/3183839291958346380757272459479783426867925215264181248911424387384722500000000000000000000000000000000000000000000000000 : ℝ) = (41318301217308401086995817/50000000000000000000000000 : ℝ) * (4537718163423207151706953/50000000000000000000000000 : ℝ) - (((17801196660523797931363426389006663085033715340531303210754528219403/14967805333294218161872350987740651945080449974797819822114000763400 : ℝ) : ℝ) * (20659150608654200543497909/25000000000000000000000000 : ℝ) + ((-82214015089871797192975108712948018597540960497088123626431095878/74839026666471090809361754938703259725402249873989099110570003817 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-680779353281044313760102825490500252819250440326022023938961211639443/4468546374678380885273364855410222353498842407388324559875683350715400 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (19110428416258022124398831198263858967687611829476804735343765215110139223272933038465314733310422568084909192626822289/3183839291958346380757272459479783426867925215264181248911424387384722500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (724649790625397709/100000000000000000000 : ℝ) ≤ (19110428416258022124398831198263858967687611829476804735343765215110139223272933038465314733310422568084909192626822289/3183839291958346380757272459479783426867925215264181248911424387384722500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (19110428416258022124398831198263858967687611829476804735343765215110139223272933038465314733310422568084909192626822289/3183839291958346380757272459479783426867925215264181248911424387384722500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 9 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[127/100, 13/10]`. -/
private theorem b9_pan_9 : (42310376064248111717/500000000000000000000000 : ℝ) ≤ ∫ t in (127/100 : ℝ)..(13/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (724649790625397709/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((127/100 : ℝ) + (13/10 : ℝ)) / 2) := b9_sig_9
  have hB0 : ((log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1198754387278435309/25000000000000000000 : ℝ) := by
    have hp := b9_lgs_9.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) ≤ (9075436326846414303413907/100000000000000000000000000 : ℝ) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 2) / 3) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (9075436326846414303413907/100000000000000000000000000 : ℝ) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (9075436326846414303413907/100000000000000000000000000 : ℝ) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (9075436326846414303413907/100000000000000000000000000 : ℝ) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (9075436326846414303413907/100000000000000000000000000 : ℝ) / ((((127/100 : ℝ) + (13/10 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1198754387278435309/25000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (127/100 : ℝ) (13/10 : ℝ), 2 * (6865529050656983913/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_9.2.2.1
    have hX : (1985476406645727961854957971/3300000000000000000000000000 : ℝ) ≤ (1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (1985476406645727961854957971/3300000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((13/10 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (6865529050656983913/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (1985476406645727961854957971/3300000000000000000000000000 : ℝ) / ((13/10 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (6865529050656983913/100000000000000000000 : ℝ) ≤ ((1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) / ((13/10 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (6865529050656983913/100000000000000000000 : ℝ) ≤ (1985476406645727961854957971/3300000000000000000000000000 : ℝ) / ((13/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (1985476406645727961854957971/3300000000000000000000000000 : ℝ) / ((13/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) / ((13/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) / ((13/10 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) / ((13/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((13/10 : ℝ) + 2) * ((13/10 : ℝ) + 1) - log (((13/10 : ℝ) + 2) / 3)) / ((13/10 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (127/100 : ℝ)) (b := (13/10 : ℝ)) (C := (6865529050656983913/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (13/10 : ℝ) - (127/100 : ℝ) ≤ (((127/100 : ℝ) + (13/10 : ℝ)) / 2) * log ((13/10 : ℝ) / (127/100 : ℝ)) := by
    have hl := b9_lgs_9.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (127/100 : ℝ)) (b := (13/10 : ℝ)) (m := (((127/100 : ℝ) + (13/10 : ℝ)) / 2)) (A := (724649790625397709/100000000000000000000 : ℝ)) (B := (1198754387278435309/25000000000000000000 : ℝ)) (C := (6865529050656983913/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_9.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 10 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_10 :
    ((41970484376909869831331607/50000000000000000000000000 : ℝ) ≤ log ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) ∧ log ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) ≤ (5246310547113733728916451/6250000000000000000000000 : ℝ)) ∧
    ((4992266748485806942490351/50000000000000000000000000 : ℝ) ≤ log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) ≤ (9984533496971613884980703/100000000000000000000000000 : ℝ)) ∧
    (log (((133/100 : ℝ) + 2) / 3) ≤ (52180007662121383863679/500000000000000000000000 : ℝ)) ∧
    ((2281467776617134504290127/100000000000000000000000000 : ℝ) ≤ log ((133/100 : ℝ) / (13/10 : ℝ)) ∧ log ((133/100 : ℝ) / (13/10 : ℝ)) ≤ (142591736038570906518133/6250000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) = (463/200 : ℝ) by norm_num]
    have hkey : log (463/200 : ℝ) = log (2 : ℝ) + log (463/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (463/400 : ℝ)) (x := (63/863 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).1
    have hnum : (73131253489126043604700009271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 13, (63/863 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) = (463/200 : ℝ) by norm_num]
    have hkey : log (463/200 : ℝ) = log (2 : ℝ) + log (463/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (463/400 : ℝ)) (x := (63/863 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (63/863 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((63/863 : ℝ) ^ (2 * 13 + 1) / (1 - (63/863 : ℝ) ^ 2)) ≤ (146262506978252087209400038541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) = (221/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (221/200 : ℝ)) (x := (21/421 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    have hnum : (4992266748485806942490351/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 12, (21/421 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) = (221/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (221/200 : ℝ)) (x := (21/421 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (21/421 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((21/421 : ℝ) ^ (2 * 12 + 1) / (1 - (21/421 : ℝ) ^ 2)) ≤ (9984533496971613884980703/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((133/100 : ℝ) + 2) / 3) = (111/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (111/100 : ℝ)) (x := (11/211 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (11/211 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((11/211 : ℝ) ^ (2 * 12 + 1) / (1 - (11/211 : ℝ) ^ 2)) ≤ (52180007662121383863679/500000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((133/100 : ℝ) / (13/10 : ℝ)) = (133/130 : ℝ) by norm_num]
    have h := (log_enclosure (y := (133/130 : ℝ)) (x := (3/263 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2281467776617134504290127/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/263 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((133/100 : ℝ) / (13/10 : ℝ)) = (133/130 : ℝ) by norm_num]
    have h := (log_enclosure (y := (133/130 : ℝ)) (x := (3/263 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/263 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/263 : ℝ) ^ (2 * 8 + 1) / (1 - (3/263 : ℝ) ^ 2)) ≤ (142591736038570906518133/6250000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 10, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_10 : (874717422311424731/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((13/10 : ℝ) + (133/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2)) (c := ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1)) (m := (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 20
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) - 1 = ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1)) (m := (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_10.1
  have hq := b9_lgs_10.2.1
  have hprod : (41970484376909869831331607/50000000000000000000000000 : ℝ) * (4992266748485806942490351/50000000000000000000000000 : ℝ) ≤ log ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) * log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((8266839237341728840611717816213970646981081234556302252204286957769703/6898165450458521042094853413021046561656829797897187761177123021144600 : ℝ) : ℝ) * log ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) ≤ ((8266839237341728840611717816213970646981081234556302252204286957769703/6898165450458521042094853413021046561656829797897187761177123021144600 : ℝ) : ℝ) * (5246310547113733728916451/6250000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-37890447986320874941259761363824727410858548944655310598223923670482/34490827252292605210474267065105232808284148989485938805885615105723 : ℝ) : ℝ) * log 2 ≤ ((-37890447986320874941259761363824727410858548944655310598223923670482/34490827252292605210474267065105232808284148989485938805885615105723 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (3206258698407777120612381111143329310599476279021340746499122032957903998217237210799055755336169185898204321797074976431/442526894432261983907387755963929332828287932687601674306958521143955457500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) * log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) -
      ((8266839237341728840611717816213970646981081234556302252204286957769703/6898165450458521042094853413021046561656829797897187761177123021144600 : ℝ) * log ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) + (-37890447986320874941259761363824727410858548944655310598223923670482/34490827252292605210474267065105232808284148989485938805885615105723 : ℝ) * log 2 + (-849269041981621884618709835752632178627479351504875566110195273355914077/5057450222082994101798717211016335232323290659286876277793811670216633800 : ℝ)) := by
    have e : (3206258698407777120612381111143329310599476279021340746499122032957903998217237210799055755336169185898204321797074976431/442526894432261983907387755963929332828287932687601674306958521143955457500000000000000000000000000000000000000000000000000 : ℝ) = (41970484376909869831331607/50000000000000000000000000 : ℝ) * (4992266748485806942490351/50000000000000000000000000 : ℝ) - (((8266839237341728840611717816213970646981081234556302252204286957769703/6898165450458521042094853413021046561656829797897187761177123021144600 : ℝ) : ℝ) * (5246310547113733728916451/6250000000000000000000000 : ℝ) + ((-37890447986320874941259761363824727410858548944655310598223923670482/34490827252292605210474267065105232808284148989485938805885615105723 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-849269041981621884618709835752632178627479351504875566110195273355914077/5057450222082994101798717211016335232323290659286876277793811670216633800 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (3206258698407777120612381111143329310599476279021340746499122032957903998217237210799055755336169185898204321797074976431/442526894432261983907387755963929332828287932687601674306958521143955457500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (874717422311424731/100000000000000000000 : ℝ) ≤ (3206258698407777120612381111143329310599476279021340746499122032957903998217237210799055755336169185898204321797074976431/442526894432261983907387755963929332828287932687601674306958521143955457500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (3206258698407777120612381111143329310599476279021340746499122032957903998217237210799055755336169185898204321797074976431/442526894432261983907387755963929332828287932687601674306958521143955457500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 10 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[13/10, 133/100]`. -/
private theorem b9_pan_10 : (99804738409365479323/1000000000000000000000000 : ℝ) ≤ ∫ t in (13/10 : ℝ)..(133/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (874717422311424731/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((13/10 : ℝ) + (133/100 : ℝ)) / 2) := b9_sig_10
  have hB0 : ((log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (325436073655541717/6250000000000000000 : ℝ) := by
    have hp := b9_lgs_10.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) ≤ (9984533496971613884980703/100000000000000000000000000 : ℝ) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 2) / 3) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (9984533496971613884980703/100000000000000000000000000 : ℝ) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (9984533496971613884980703/100000000000000000000000000 : ℝ) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (9984533496971613884980703/100000000000000000000000000 : ℝ) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (9984533496971613884980703/100000000000000000000000000 : ℝ) / ((((13/10 : ℝ) + (133/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (325436073655541717/6250000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (13/10 : ℝ) (133/100 : ℝ), 2 * (3309801020328295677/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_10.2.2.1
    have hX : (99124057448513579173394893/166500000000000000000000000 : ℝ) ≤ (1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (99124057448513579173394893/166500000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((133/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3309801020328295677/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (99124057448513579173394893/166500000000000000000000000 : ℝ) / ((133/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3309801020328295677/50000000000000000000 : ℝ) ≤ ((1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) / ((133/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3309801020328295677/50000000000000000000 : ℝ) ≤ (99124057448513579173394893/166500000000000000000000000 : ℝ) / ((133/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (99124057448513579173394893/166500000000000000000000000 : ℝ) / ((133/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) / ((133/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) / ((133/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) / ((133/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((133/100 : ℝ) + 2) * ((133/100 : ℝ) + 1) - log (((133/100 : ℝ) + 2) / 3)) / ((133/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (13/10 : ℝ)) (b := (133/100 : ℝ)) (C := (3309801020328295677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (133/100 : ℝ) - (13/10 : ℝ) ≤ (((13/10 : ℝ) + (133/100 : ℝ)) / 2) * log ((133/100 : ℝ) / (13/10 : ℝ)) := by
    have hl := b9_lgs_10.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (13/10 : ℝ)) (b := (133/100 : ℝ)) (m := (((13/10 : ℝ) + (133/100 : ℝ)) / 2)) (A := (874717422311424731/100000000000000000000 : ℝ)) (B := (325436073655541717/6250000000000000000 : ℝ)) (C := (3309801020328295677/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_10.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 11 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_11 :
    ((8522854018982426873222097/10000000000000000000000000 : ℝ) ≤ log ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) ∧ log ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) ≤ (21307135047456067183055243/25000000000000000000000000 : ℝ)) ∧
    ((10885440491208208118289017/100000000000000000000000000 : ℝ) ≤ log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) ≤ (5442720245604104059144509/50000000000000000000000000 : ℝ)) ∧
    (log (((34/25 : ℝ) + 2) / 3) ≤ (1416608566337539684228729/12500000000000000000000000 : ℝ)) ∧
    ((55764393785745608467127/2500000000000000000000000 : ℝ) ≤ log ((34/25 : ℝ) / (133/100 : ℝ)) ∧ log ((34/25 : ℝ) / (133/100 : ℝ)) ≤ (2230575751429824338685081/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) = (469/200 : ℝ) by norm_num]
    have hkey : log (469/200 : ℝ) = log (2 : ℝ) + log (469/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (469/400 : ℝ)) (x := (69/869 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).1
    have hnum : (79569110669148688952488789271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 14, (69/869 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) = (469/200 : ℝ) by norm_num]
    have hkey : log (469/200 : ℝ) = log (2 : ℝ) + log (469/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (469/400 : ℝ)) (x := (69/869 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (69/869 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((69/869 : ℝ) ^ (2 * 14 + 1) / (1 - (69/869 : ℝ) ^ 2)) ≤ (159138221338297377904977598541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) = (223/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (223/200 : ℝ)) (x := (23/423 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    have hnum : (10885440491208208118289017/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 12, (23/423 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) = (223/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (223/200 : ℝ)) (x := (23/423 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (23/423 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((23/423 : ℝ) ^ (2 * 12 + 1) / (1 - (23/423 : ℝ) ^ 2)) ≤ (5442720245604104059144509/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((34/25 : ℝ) + 2) / 3) = (28/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (28/25 : ℝ)) (x := (3/53 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (3/53 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/53 : ℝ) ^ (2 * 12 + 1) / (1 - (3/53 : ℝ) ^ 2)) ≤ (1416608566337539684228729/12500000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((34/25 : ℝ) / (133/100 : ℝ)) = (136/133 : ℝ) by norm_num]
    have h := (log_enclosure (y := (136/133 : ℝ)) (x := (3/269 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (55764393785745608467127/2500000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/269 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((34/25 : ℝ) / (133/100 : ℝ)) = (136/133 : ℝ) by norm_num]
    have h := (log_enclosure (y := (136/133 : ℝ)) (x := (3/269 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/269 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/269 : ℝ) ^ (2 * 8 + 1) / (1 - (3/269 : ℝ) ^ 2)) ≤ (2230575751429824338685081/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 11, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_11 : (207384171673823709/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((133/100 : ℝ) + (34/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2)) (c := ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1)) (m := (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 20
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) - 1 = ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1)) (m := (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_11.1
  have hq := b9_lgs_11.2.1
  have hprod : (8522854018982426873222097/10000000000000000000000000 : ℝ) * (10885440491208208118289017/100000000000000000000000000 : ℝ) ≤ log ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) * log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((1308153261226620570250773063360041399027034508114964469029706831024907/1083430350237506937473806282350658953825748431825889536553976150917800 : ℝ) : ℝ) * log ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) ≤ ((1308153261226620570250773063360041399027034508114964469029706831024907/1083430350237506937473806282350658953825748431825889536553976150917800 : ℝ) : ℝ) * (21307135047456067183055243/25000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-41657598331573982991270228325882850671258792120937054119648084588082/37920062258312742811583219882273063383901195113906133779389165282123 : ℝ) : ℝ) * log 2 ≤ ((-41657598331573982991270228325882850671258792120937054119648084588082/37920062258312742811583219882273063383901195113906133779389165282123 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (11700377035301875302259529815382540023351609360480120074619886959567511326022703881248776432187013245709703542478313194569/1362269809949383438229946822444019296941454011979274765772604787390206081000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) * log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) -
      ((1308153261226620570250773063360041399027034508114964469029706831024907/1083430350237506937473806282350658953825748431825889536553976150917800 : ℝ) * log ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) + (-41657598331573982991270228325882850671258792120937054119648084588082/37920062258312742811583219882273063383901195113906133779389165282123 : ℝ) * log 2 + (-29982850185575495068715454882757803878875235196294331202680993900030992601/163472377193926012587593618693282315632974481437512971892712574486824729720 : ℝ)) := by
    have e : (11700377035301875302259529815382540023351609360480120074619886959567511326022703881248776432187013245709703542478313194569/1362269809949383438229946822444019296941454011979274765772604787390206081000000000000000000000000000000000000000000000000000 : ℝ) = (8522854018982426873222097/10000000000000000000000000 : ℝ) * (10885440491208208118289017/100000000000000000000000000 : ℝ) - (((1308153261226620570250773063360041399027034508114964469029706831024907/1083430350237506937473806282350658953825748431825889536553976150917800 : ℝ) : ℝ) * (21307135047456067183055243/25000000000000000000000000 : ℝ) + ((-41657598331573982991270228325882850671258792120937054119648084588082/37920062258312742811583219882273063383901195113906133779389165282123 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-29982850185575495068715454882757803878875235196294331202680993900030992601/163472377193926012587593618693282315632974481437512971892712574486824729720 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (11700377035301875302259529815382540023351609360480120074619886959567511326022703881248776432187013245709703542478313194569/1362269809949383438229946822444019296941454011979274765772604787390206081000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (207384171673823709/20000000000000000000 : ℝ) ≤ (11700377035301875302259529815382540023351609360480120074619886959567511326022703881248776432187013245709703542478313194569/1362269809949383438229946822444019296941454011979274765772604787390206081000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (11700377035301875302259529815382540023351609360480120074619886959567511326022703881248776432187013245709703542478313194569/1362269809949383438229946822444019296941454011979274765772604787390206081000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 11 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[133/100, 34/25]`. -/
private theorem b9_pan_11 : (11566507586054147703/100000000000000000000000 : ℝ) ≤ ∫ t in (133/100 : ℝ)..(34/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (207384171673823709/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((133/100 : ℝ) + (34/25 : ℝ)) / 2) := b9_sig_11
  have hB0 : ((log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2802089846690418191/50000000000000000000 : ℝ) := by
    have hp := b9_lgs_11.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) ≤ (5442720245604104059144509/50000000000000000000000000 : ℝ) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 2) / 3) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (5442720245604104059144509/50000000000000000000000000 : ℝ) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (5442720245604104059144509/50000000000000000000000000 : ℝ) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (5442720245604104059144509/50000000000000000000000000 : ℝ) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (5442720245604104059144509/50000000000000000000000000 : ℝ) / ((((133/100 : ℝ) + (34/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2802089846690418191/50000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (133/100 : ℝ) (34/25 : ℝ), 2 * (3192116407962185789/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_11.2.2.1
    have hX : (154626220106911666631196691/262500000000000000000000000 : ℝ) ≤ (1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (154626220106911666631196691/262500000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((34/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3192116407962185789/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (154626220106911666631196691/262500000000000000000000000 : ℝ) / ((34/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3192116407962185789/50000000000000000000 : ℝ) ≤ ((1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) / ((34/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3192116407962185789/50000000000000000000 : ℝ) ≤ (154626220106911666631196691/262500000000000000000000000 : ℝ) / ((34/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (154626220106911666631196691/262500000000000000000000000 : ℝ) / ((34/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) / ((34/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) / ((34/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) / ((34/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((34/25 : ℝ) + 2) * ((34/25 : ℝ) + 1) - log (((34/25 : ℝ) + 2) / 3)) / ((34/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (133/100 : ℝ)) (b := (34/25 : ℝ)) (C := (3192116407962185789/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (34/25 : ℝ) - (133/100 : ℝ) ≤ (((133/100 : ℝ) + (34/25 : ℝ)) / 2) * log ((34/25 : ℝ) / (133/100 : ℝ)) := by
    have hl := b9_lgs_11.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (133/100 : ℝ)) (b := (34/25 : ℝ)) (m := (((133/100 : ℝ) + (34/25 : ℝ)) / 2)) (A := (207384171673823709/20000000000000000000 : ℝ)) (B := (2802089846690418191/50000000000000000000 : ℝ)) (C := (3192116407962185789/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_11.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 12 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_12 :
    ((43249871874330226587866553/50000000000000000000000000 : ℝ) ≤ log ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) ∧ log ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) ≤ (21624935937165113293933277/25000000000000000000000000 : ℝ)) ∧
    ((1177830356563834545387941/10000000000000000000000000 : ℝ) ≤ log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) ≤ (11778303565638345453879411/100000000000000000000000000 : ℝ)) ∧
    (log (((139/100 : ℝ) + 2) / 3) ≤ (12221763272424920054614859/100000000000000000000000000 : ℝ)) ∧
    ((2181904739463974868755393/100000000000000000000000000 : ℝ) ≤ log ((139/100 : ℝ) / (34/25 : ℝ)) ∧ log ((139/100 : ℝ) / (34/25 : ℝ)) ≤ (1090952369731987434377697/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) = (19/8 : ℝ) by norm_num]
    have hkey : log (19/8 : ℝ) = log (2 : ℝ) + log (19/16 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (19/16 : ℝ)) (x := (3/35 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).1
    have hnum : (85925128463329611170049469271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 14, (3/35 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) = (19/8 : ℝ) by norm_num]
    have hkey : log (19/8 : ℝ) = log (2 : ℝ) + log (19/16 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (19/16 : ℝ)) (x := (3/35 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (3/35 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/35 : ℝ) ^ (2 * 14 + 1) / (1 - (3/35 : ℝ) ^ 2)) ≤ (171850256926659222340098958541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) = (9/8 : ℝ) by norm_num]
    have h := (log_enclosure (y := (9/8 : ℝ)) (x := (1/17 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).1
    have hnum : (1177830356563834545387941/10000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 12, (1/17 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) = (9/8 : ℝ) by norm_num]
    have h := (log_enclosure (y := (9/8 : ℝ)) (x := (1/17 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (1/17 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/17 : ℝ) ^ (2 * 12 + 1) / (1 - (1/17 : ℝ) ^ 2)) ≤ (11778303565638345453879411/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((139/100 : ℝ) + 2) / 3) = (113/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (113/100 : ℝ)) (x := (13/213 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 12).2
    have hnum : 2 * (∑ i ∈ Finset.range 12, (13/213 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((13/213 : ℝ) ^ (2 * 12 + 1) / (1 - (13/213 : ℝ) ^ 2)) ≤ (12221763272424920054614859/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((139/100 : ℝ) / (34/25 : ℝ)) = (139/136 : ℝ) by norm_num]
    have h := (log_enclosure (y := (139/136 : ℝ)) (x := (3/275 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2181904739463974868755393/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/275 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((139/100 : ℝ) / (34/25 : ℝ)) = (139/136 : ℝ) by norm_num]
    have h := (log_enclosure (y := (139/136 : ℝ)) (x := (3/275 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/275 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/275 : ℝ) ^ (2 * 8 + 1) / (1 - (3/275 : ℝ) ^ 2)) ≤ (1090952369731987434377697/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 12, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_12 : (48433079020975731/4000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((34/25 : ℝ) + (139/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2)) (c := ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1)) (m := (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 21
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) - 1 = ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1)) (m := (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_12.1
  have hq := b9_lgs_12.2.1
  have hprod : (43249871874330226587866553/50000000000000000000000000 : ℝ) * (1177830356563834545387941/10000000000000000000000000 : ℝ) ≤ log ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) * log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((105597039745092941687169122659341616899589/86813850988873635309514719483859389246120 : ℝ) : ℝ) * log ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) ≤ ((105597039745092941687169122659341616899589/86813850988873635309514719483859389246120 : ℝ) : ℝ) * (21624935937165113293933277/25000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-226508121991680885903216035216381339922314/206182896098574883860097458774166049459535 : ℝ) : ℝ) * log 2 ≤ ((-226508121991680885903216035216381339922314/206182896098574883860097458774166049459535 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (22286464733137340498869208180296889537780734627581646642419986639883128857809586140526718491151/2222122417175984239143276355441322986980174493500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) * log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) -
      ((105597039745092941687169122659341616899589/86813850988873635309514719483859389246120 : ℝ) * log ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) + (-226508121991680885903216035216381339922314/206182896098574883860097458774166049459535 : ℝ) * log 2 + (-176721287678100712973875075417832195698429269947/888848966870393695657310542176529194792069797400 : ℝ)) := by
    have e : (22286464733137340498869208180296889537780734627581646642419986639883128857809586140526718491151/2222122417175984239143276355441322986980174493500000000000000000000000000000000000000000000000000 : ℝ) = (43249871874330226587866553/50000000000000000000000000 : ℝ) * (1177830356563834545387941/10000000000000000000000000 : ℝ) - (((105597039745092941687169122659341616899589/86813850988873635309514719483859389246120 : ℝ) : ℝ) * (21624935937165113293933277/25000000000000000000000000 : ℝ) + ((-226508121991680885903216035216381339922314/206182896098574883860097458774166049459535 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-176721287678100712973875075417832195698429269947/888848966870393695657310542176529194792069797400 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (22286464733137340498869208180296889537780734627581646642419986639883128857809586140526718491151/2222122417175984239143276355441322986980174493500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (48433079020975731/4000000000000000000 : ℝ) ≤ (22286464733137340498869208180296889537780734627581646642419986639883128857809586140526718491151/2222122417175984239143276355441322986980174493500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (22286464733137340498869208180296889537780734627581646642419986639883128857809586140526718491151/2222122417175984239143276355441322986980174493500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 12 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[34/25, 139/100]`. -/
private theorem b9_pan_12 : (13211022090982803231/100000000000000000000000 : ℝ) ≤ ∫ t in (34/25 : ℝ)..(139/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (48433079020975731/4000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((34/25 : ℝ) + (139/100 : ℝ)) / 2) := b9_sig_12
  have hB0 : ((log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (5987258657034956413/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_12.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) ≤ (11778303565638345453879411/100000000000000000000000000 : ℝ) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 2) / 3) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (11778303565638345453879411/100000000000000000000000000 : ℝ) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (11778303565638345453879411/100000000000000000000000000 : ℝ) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (11778303565638345453879411/100000000000000000000000000 : ℝ) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (11778303565638345453879411/100000000000000000000000000 : ℝ) / ((((34/25 : ℝ) + (139/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (5987258657034956413/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (34/25 : ℝ) (139/100 : ℝ), 2 * (6158862138202062543/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_12.2.2.1
    have hX : (19756822250647952101485562799/33900000000000000000000000000 : ℝ) ≤ (1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (19756822250647952101485562799/33900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((139/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (6158862138202062543/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (19756822250647952101485562799/33900000000000000000000000000 : ℝ) / ((139/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (6158862138202062543/100000000000000000000 : ℝ) ≤ ((1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) / ((139/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (6158862138202062543/100000000000000000000 : ℝ) ≤ (19756822250647952101485562799/33900000000000000000000000000 : ℝ) / ((139/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (19756822250647952101485562799/33900000000000000000000000000 : ℝ) / ((139/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) / ((139/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) / ((139/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) / ((139/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((139/100 : ℝ) + 2) * ((139/100 : ℝ) + 1) - log (((139/100 : ℝ) + 2) / 3)) / ((139/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (34/25 : ℝ)) (b := (139/100 : ℝ)) (C := (6158862138202062543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (139/100 : ℝ) - (34/25 : ℝ) ≤ (((34/25 : ℝ) + (139/100 : ℝ)) / 2) * log ((139/100 : ℝ) / (34/25 : ℝ)) := by
    have hl := b9_lgs_12.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (34/25 : ℝ)) (b := (139/100 : ℝ)) (m := (((34/25 : ℝ) + (139/100 : ℝ)) / 2)) (A := (48433079020975731/4000000000000000000 : ℝ)) (B := (5987258657034956413/100000000000000000000 : ℝ)) (C := (6158862138202062543/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_12.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 13 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_13 :
    ((10969373794471556287104601/12500000000000000000000000 : ℝ) ≤ log ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) ∧ log ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) ≤ (8775499035577245029683681/10000000000000000000000000 : ℝ)) ∧
    ((6331632546668299878008327/50000000000000000000000000 : ℝ) ≤ log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) ≤ (2532653018667319951203331/20000000000000000000000000 : ℝ)) ∧
    (log (((71/50 : ℝ) + 2) / 3) ≤ (13102826240640409278552189/100000000000000000000000000 : ℝ)) ∧
    ((2135312447056897355790173/100000000000000000000000000 : ℝ) ≤ log ((71/50 : ℝ) / (139/100 : ℝ)) ∧ log ((71/50 : ℝ) / (139/100 : ℝ)) ≤ (1067656223528448677895087/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) = (481/200 : ℝ) by norm_num]
    have hkey : log (481/200 : ℝ) = log (2 : ℝ) + log (481/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (481/400 : ℝ)) (x := (81/881 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (92201361498889596775567979271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (81/881 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) = (481/200 : ℝ) by norm_num]
    have hkey : log (481/200 : ℝ) = log (2 : ℝ) + log (481/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (481/400 : ℝ)) (x := (81/881 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (81/881 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((81/881 : ℝ) ^ (2 * 15 + 1) / (1 - (81/881 : ℝ) ^ 2)) ≤ (184402722997779193551135978541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) = (227/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (227/200 : ℝ)) (x := (27/427 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).1
    have hnum : (6331632546668299878008327/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 13, (27/427 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) = (227/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (227/200 : ℝ)) (x := (27/427 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (27/427 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((27/427 : ℝ) ^ (2 * 13 + 1) / (1 - (27/427 : ℝ) ^ 2)) ≤ (2532653018667319951203331/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((71/50 : ℝ) + 2) / 3) = (57/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (57/50 : ℝ)) (x := (7/107 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (7/107 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((7/107 : ℝ) ^ (2 * 13 + 1) / (1 - (7/107 : ℝ) ^ 2)) ≤ (13102826240640409278552189/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((71/50 : ℝ) / (139/100 : ℝ)) = (142/139 : ℝ) by norm_num]
    have h := (log_enclosure (y := (142/139 : ℝ)) (x := (3/281 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2135312447056897355790173/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/281 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((71/50 : ℝ) / (139/100 : ℝ)) = (142/139 : ℝ) by norm_num]
    have h := (log_enclosure (y := (142/139 : ℝ)) (x := (3/281 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/281 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/281 : ℝ) ^ (2 * 8 + 1) / (1 - (3/281 : ℝ) ^ 2)) ≤ (1067656223528448677895087/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 13, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_13 : (11168169187438869/800000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((139/100 : ℝ) + (71/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2)) (c := ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1)) (m := (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 21
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) - 1 = ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1)) (m := (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_13.1
  have hq := b9_lgs_13.2.1
  have hprod : (10969373794471556287104601/12500000000000000000000000 : ℝ) * (6331632546668299878008327/50000000000000000000000000 : ℝ) ≤ log ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) * log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((473683808027811106125183486943303380490177371190787712117730902860990593/386614539412229391816827986217300783157505073471079992137589773068115800 : ℝ) : ℝ) * log ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) ≤ ((473683808027811106125183486943303380490177371190787712117730902860990593/386614539412229391816827986217300783157505073471079992137589773068115800 : ℝ) : ℝ) * (8775499035577245029683681/10000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-193250231725759476714705545446818948362169087485691516714286571096795126/175909615432564373276656733728871856336664808429341396422603346745992689 : ℝ) : ℝ) * log 2 ≤ ((-193250231725759476714705545446818948362169087485691516714286571096795126/175909615432564373276656733728871856336664808429341396422603346745992689 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (6738441661748456751946624563759643748913679866771839612621016486353009223753498994196691887461792266557963444151760263415529/582742055230563635870168904912090524655117580489753568806817437294616743704375000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) * log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) -
      ((473683808027811106125183486943303380490177371190787712117730902860990593/386614539412229391816827986217300783157505073471079992137589773068115800 : ℝ) * log ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) + (-193250231725759476714705545446818948362169087485691516714286571096795126/175909615432564373276656733728871856336664808429341396422603346745992689 : ℝ) * log 2 + (-30073007315472347264096399203524875544501874796870431476141518840155096269073/140433640964204965088712308936839593102072779890864069914926868839394059717400 : ℝ)) := by
    have e : (6738441661748456751946624563759643748913679866771839612621016486353009223753498994196691887461792266557963444151760263415529/582742055230563635870168904912090524655117580489753568806817437294616743704375000000000000000000000000000000000000000000000000 : ℝ) = (10969373794471556287104601/12500000000000000000000000 : ℝ) * (6331632546668299878008327/50000000000000000000000000 : ℝ) - (((473683808027811106125183486943303380490177371190787712117730902860990593/386614539412229391816827986217300783157505073471079992137589773068115800 : ℝ) : ℝ) * (8775499035577245029683681/10000000000000000000000000 : ℝ) + ((-193250231725759476714705545446818948362169087485691516714286571096795126/175909615432564373276656733728871856336664808429341396422603346745992689 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-30073007315472347264096399203524875544501874796870431476141518840155096269073/140433640964204965088712308936839593102072779890864069914926868839394059717400 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (6738441661748456751946624563759643748913679866771839612621016486353009223753498994196691887461792266557963444151760263415529/582742055230563635870168904912090524655117580489753568806817437294616743704375000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (11168169187438869/800000000000000000 : ℝ) ≤ (6738441661748456751946624563759643748913679866771839612621016486353009223753498994196691887461792266557963444151760263415529/582742055230563635870168904912090524655117580489753568806817437294616743704375000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (6738441661748456751946624563759643748913679866771839612621016486353009223753498994196691887461792266557963444151760263415529/582742055230563635870168904912090524655117580489753568806817437294616743704375000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 13 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[139/100, 71/50]`. -/
private theorem b9_pan_13 : (149058425951214627181/1000000000000000000000000 : ℝ) ≤ ∫ t in (139/100 : ℝ)..(71/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (11168169187438869/800000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((139/100 : ℝ) + (71/50 : ℝ)) / 2) := b9_sig_13
  have hB0 : ((log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1271362814233425439/20000000000000000000 : ℝ) := by
    have hp := b9_lgs_13.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) ≤ (2532653018667319951203331/20000000000000000000000000 : ℝ) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 2) / 3) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (2532653018667319951203331/20000000000000000000000000 : ℝ) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (2532653018667319951203331/20000000000000000000000000 : ℝ) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (2532653018667319951203331/20000000000000000000000000 : ℝ) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (2532653018667319951203331/20000000000000000000000000 : ℝ) / ((((139/100 : ℝ) + (71/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1271362814233425439/20000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (139/100 : ℝ) (71/50 : ℝ), 2 * (2971483171082857723/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_13.2.2.1
    have hX : (9859416712850490013367575681/17100000000000000000000000000 : ℝ) ≤ (1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9859416712850490013367575681/17100000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((71/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2971483171082857723/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9859416712850490013367575681/17100000000000000000000000000 : ℝ) / ((71/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2971483171082857723/50000000000000000000 : ℝ) ≤ ((1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) / ((71/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2971483171082857723/50000000000000000000 : ℝ) ≤ (9859416712850490013367575681/17100000000000000000000000000 : ℝ) / ((71/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9859416712850490013367575681/17100000000000000000000000000 : ℝ) / ((71/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) / ((71/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) / ((71/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) / ((71/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((71/50 : ℝ) + 2) * ((71/50 : ℝ) + 1) - log (((71/50 : ℝ) + 2) / 3)) / ((71/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (139/100 : ℝ)) (b := (71/50 : ℝ)) (C := (2971483171082857723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (71/50 : ℝ) - (139/100 : ℝ) ≤ (((139/100 : ℝ) + (71/50 : ℝ)) / 2) * log ((71/50 : ℝ) / (139/100 : ℝ)) := by
    have hl := b9_lgs_13.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (139/100 : ℝ)) (b := (71/50 : ℝ)) (m := (((139/100 : ℝ) + (71/50 : ℝ)) / 2)) (A := (11168169187438869/800000000000000000 : ℝ)) (B := (1271362814233425439/20000000000000000000 : ℝ)) (C := (2971483171082857723/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_13.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 14 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_14 :
    ((88994675653455311327669579/100000000000000000000000000 : ℝ) ≤ log ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) ∧ log ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) ≤ (88994675653455311327669581/100000000000000000000000000 : ℝ)) ∧
    ((13540463700620297098802057/100000000000000000000000000 : ℝ) ≤ log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) ∧ log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) ≤ (6770231850310148549401029/50000000000000000000000000 : ℝ)) ∧
    (log (((29/20 : ℝ) + 2) / 3) ≤ (6988097118757934868576463/50000000000000000000000000 : ℝ)) ∧
    ((2090668481931367103734471/100000000000000000000000000 : ℝ) ≤ log ((29/20 : ℝ) / (71/50 : ℝ)) ∧ log ((29/20 : ℝ) / (71/50 : ℝ)) ≤ (261333560241420887966809/12500000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) = (487/200 : ℝ) by norm_num]
    have hkey : log (487/200 : ℝ) = log (2 : ℝ) + log (487/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (487/400 : ℝ)) (x := (87/887 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (98399787987303901929731834271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (87/887 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) = (487/200 : ℝ) by norm_num]
    have hkey : log (487/200 : ℝ) = log (2 : ℝ) + log (487/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (487/400 : ℝ)) (x := (87/887 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (87/887 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((87/887 : ℝ) ^ (2 * 15 + 1) / (1 - (87/887 : ℝ) ^ 2)) ≤ (196799575974607803859463688541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) = (229/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (229/200 : ℝ)) (x := (29/429 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).1
    have hnum : (13540463700620297098802057/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 13, (29/429 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) = (229/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (229/200 : ℝ)) (x := (29/429 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (29/429 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((29/429 : ℝ) ^ (2 * 13 + 1) / (1 - (29/429 : ℝ) ^ 2)) ≤ (6770231850310148549401029/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((29/20 : ℝ) + 2) / 3) = (23/20 : ℝ) by norm_num]
    have h := (log_enclosure (y := (23/20 : ℝ)) (x := (3/43 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (3/43 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/43 : ℝ) ^ (2 * 13 + 1) / (1 - (3/43 : ℝ) ^ 2)) ≤ (6988097118757934868576463/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((29/20 : ℝ) / (71/50 : ℝ)) = (145/142 : ℝ) by norm_num]
    have h := (log_enclosure (y := (145/142 : ℝ)) (x := (3/287 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (2090668481931367103734471/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/287 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((29/20 : ℝ) / (71/50 : ℝ)) = (145/142 : ℝ) by norm_num]
    have h := (log_enclosure (y := (145/142 : ℝ)) (x := (3/287 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/287 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/287 : ℝ) ^ (2 * 8 + 1) / (1 - (3/287 : ℝ) ^ 2)) ≤ (261333560241420887966809/12500000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 14, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_14 : (796053137629483173/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((71/50 : ℝ) + (29/20 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2)) (c := ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1)) (m := (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 22
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) - 1 = ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1)) (m := (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_14.1
  have hq := b9_lgs_14.2.1
  have hprod : (88994675653455311327669579/100000000000000000000000000 : ℝ) * (13540463700620297098802057/100000000000000000000000000 : ℝ) ≤ log ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) * log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((1580387968484596470642646684877551518650406709271546680868967251848631561531/1280711399223131622566639430003898805276958410735665909469631471627387319800 : ℝ) : ℝ) * log ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) ≤ ((1580387968484596470642646684877551518650406709271546680868967251848631561531/1280711399223131622566639430003898805276958410735665909469631471627387319800 : ℝ) : ℝ) * (88994675653455311327669581/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-7034868531815410178161907709558796130509762158557713693820113901051611066/6403556996115658112833197150019494026384792053678329547348157358136936599 : ℝ) : ℝ) * log 2 ≤ ((-7034868531815410178161907709558796130509762158557713693820113901051611066/6403556996115658112833197150019494026384792053678329547348157358136936599 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (273036713219341735317402130880943669963727515974713767989929960733231244660199881454504533661490492514979547299853450418274943431/20704172586551029280155678021357528670928101211714385442372482815049087519984770000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) * log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) -
      ((1580387968484596470642646684877551518650406709271546680868967251848631561531/1280711399223131622566639430003898805276958410735665909469631471627387319800 : ℝ) * log ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) + (-7034868531815410178161907709558796130509762158557713693820113901051611066/6403556996115658112833197150019494026384792053678329547348157358136936599 : ℝ) * log 2 + (-31662077011283742405996283005092965015705857023026053930560215824605555342738659/138027817243673528534371186809050191139520674744762569615816552100327250133231800 : ℝ)) := by
    have e : (273036713219341735317402130880943669963727515974713767989929960733231244660199881454504533661490492514979547299853450418274943431/20704172586551029280155678021357528670928101211714385442372482815049087519984770000000000000000000000000000000000000000000000000000 : ℝ) = (88994675653455311327669579/100000000000000000000000000 : ℝ) * (13540463700620297098802057/100000000000000000000000000 : ℝ) - (((1580387968484596470642646684877551518650406709271546680868967251848631561531/1280711399223131622566639430003898805276958410735665909469631471627387319800 : ℝ) : ℝ) * (88994675653455311327669581/100000000000000000000000000 : ℝ) + ((-7034868531815410178161907709558796130509762158557713693820113901051611066/6403556996115658112833197150019494026384792053678329547348157358136936599 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-31662077011283742405996283005092965015705857023026053930560215824605555342738659/138027817243673528534371186809050191139520674744762569615816552100327250133231800 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (273036713219341735317402130880943669963727515974713767989929960733231244660199881454504533661490492514979547299853450418274943431/20704172586551029280155678021357528670928101211714385442372482815049087519984770000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (796053137629483173/50000000000000000000 : ℝ) ≤ (273036713219341735317402130880943669963727515974713767989929960733231244660199881454504533661490492514979547299853450418274943431/20704172586551029280155678021357528670928101211714385442372482815049087519984770000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (273036713219341735317402130880943669963727515974713767989929960733231244660199881454504533661490492514979547299853450418274943431/20704172586551029280155678021357528670928101211714385442372482815049087519984770000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 14 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[71/50, 29/20]`. -/
private theorem b9_pan_14 : (83218306614485251731/500000000000000000000000 : ℝ) ≤ ∫ t in (71/50 : ℝ)..(29/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (796053137629483173/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((71/50 : ℝ) + (29/20 : ℝ)) / 2) := b9_sig_14
  have hB0 : ((log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (6713414510963575111/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_14.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) ≤ (6770231850310148549401029/50000000000000000000000000 : ℝ) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 2) / 3) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6770231850310148549401029/50000000000000000000000000 : ℝ) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (6770231850310148549401029/50000000000000000000000000 : ℝ) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6770231850310148549401029/50000000000000000000000000 : ℝ) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (6770231850310148549401029/50000000000000000000000000 : ℝ) / ((((71/50 : ℝ) + (29/20 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (6713414510963575111/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (71/50 : ℝ) (29/20 : ℝ), 2 * (5736054689696643681/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_14.2.2.1
    have hX : (1967821298805702494068224053/3450000000000000000000000000 : ℝ) ≤ (1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (1967821298805702494068224053/3450000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((29/20 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (5736054689696643681/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (1967821298805702494068224053/3450000000000000000000000000 : ℝ) / ((29/20 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (5736054689696643681/100000000000000000000 : ℝ) ≤ ((1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) / ((29/20 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (5736054689696643681/100000000000000000000 : ℝ) ≤ (1967821298805702494068224053/3450000000000000000000000000 : ℝ) / ((29/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (1967821298805702494068224053/3450000000000000000000000000 : ℝ) / ((29/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) / ((29/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) / ((29/20 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) / ((29/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((29/20 : ℝ) + 2) * ((29/20 : ℝ) + 1) - log (((29/20 : ℝ) + 2) / 3)) / ((29/20 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (71/50 : ℝ)) (b := (29/20 : ℝ)) (C := (5736054689696643681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (29/20 : ℝ) - (71/50 : ℝ) ≤ (((71/50 : ℝ) + (29/20 : ℝ)) / 2) * log ((29/20 : ℝ) / (71/50 : ℝ)) := by
    have hl := b9_lgs_14.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (71/50 : ℝ)) (b := (29/20 : ℝ)) (m := (((71/50 : ℝ) + (29/20 : ℝ)) / 2)) (A := (796053137629483173/50000000000000000000 : ℝ)) (B := (6713414510963575111/100000000000000000000 : ℝ)) (C := (5736054689696643681/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_14.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 15 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_15 :
    ((90219180749465342997959161/100000000000000000000000000 : ℝ) ≤ log ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) ∧ log ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) ≤ (90219180749465342997959163/100000000000000000000000000 : ℝ)) ∧
    ((3602508599343921577733163/25000000000000000000000000 : ℝ) ≤ log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) ≤ (14410034397375686310932653/100000000000000000000000000 : ℝ)) ∧
    (log (((37/25 : ℝ) + 2) / 3) ≤ (14842000511827327798175337/100000000000000000000000000 : ℝ)) ∧
    ((1023926567177033070926427/50000000000000000000000000 : ℝ) ≤ log ((37/25 : ℝ) / (29/20 : ℝ)) ∧ log ((37/25 : ℝ) / (29/20 : ℝ)) ≤ (409570626870813228370571/20000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) = (493/200 : ℝ) by norm_num]
    have hkey : log (493/200 : ℝ) = log (2 : ℝ) + log (493/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (493/400 : ℝ)) (x := (93/893 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (104522313467354060281179744271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (93/893 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) = (493/200 : ℝ) by norm_num]
    have hkey : log (493/200 : ℝ) = log (2 : ℝ) + log (493/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (493/400 : ℝ)) (x := (93/893 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (93/893 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((93/893 : ℝ) ^ (2 * 15 + 1) / (1 - (93/893 : ℝ) ^ 2)) ≤ (209044626934708120562359508541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) = (231/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (231/200 : ℝ)) (x := (31/431 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).1
    have hnum : (3602508599343921577733163/25000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 13, (31/431 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) = (231/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (231/200 : ℝ)) (x := (31/431 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (31/431 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((31/431 : ℝ) ^ (2 * 13 + 1) / (1 - (31/431 : ℝ) ^ 2)) ≤ (14410034397375686310932653/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((37/25 : ℝ) + 2) / 3) = (29/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (29/25 : ℝ)) (x := (2/27 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 13).2
    have hnum : 2 * (∑ i ∈ Finset.range 13, (2/27 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((2/27 : ℝ) ^ (2 * 13 + 1) / (1 - (2/27 : ℝ) ^ 2)) ≤ (14842000511827327798175337/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((37/25 : ℝ) / (29/20 : ℝ)) = (148/145 : ℝ) by norm_num]
    have h := (log_enclosure (y := (148/145 : ℝ)) (x := (3/293 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (1023926567177033070926427/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/293 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((37/25 : ℝ) / (29/20 : ℝ)) = (148/145 : ℝ) by norm_num]
    have h := (log_enclosure (y := (148/145 : ℝ)) (x := (3/293 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/293 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/293 : ℝ) ^ (2 * 8 + 1) / (1 - (3/293 : ℝ) ^ 2)) ≤ (409570626870813228370571/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 15, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_15 : (1798701864932536123/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((29/20 : ℝ) + (37/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2)) (c := ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1)) (m := (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 22
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) - 1 = ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1)) (m := (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_15.1
  have hq := b9_lgs_15.2.1
  have hprod : (90219180749465342997959161/100000000000000000000000000 : ℝ) * (3602508599343921577733163/25000000000000000000000000 : ℝ) ≤ log ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) * log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((1348176822279824946863895628071929327272256633641247796288505558289795097101/1084888789364052748447356474988872508672919797705997081287393865340782026200 : ℝ) : ℝ) * log ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) ≤ ((1348176822279824946863895628071929327272256633641247796288505558289795097101/1084888789364052748447356474988872508672919797705997081287393865340782026200 : ℝ) : ℝ) * (90219180749465342997959163/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-101306737837531344615058534709483936488888679085806540792127233677560474818/92215547095944483618025300374054163237198182805009751909428478553966472227 : ℝ) : ℝ) * log 2 ≤ ((-101306737837531344615058534709483936488888679085806540792127233677560474818/92215547095944483618025300374054163237198182805009751909428478553966472227 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (1110531942034132765221077951842510549638950756963287492021861734816364207264639618259962107206090228286370940394980620120686904003/74538518334255145692076985482100785550851570147660420041530359928760254249625802500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) * log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) -
      ((1348176822279824946863895628071929327272256633641247796288505558289795097101/1084888789364052748447356474988872508672919797705997081287393865340782026200 : ℝ) * log ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) + (-101306737837531344615058534709483936488888679085806540792127233677560474818/92215547095944483618025300374054163237198182805009751909428478553966472227 : ℝ) * log 2 + (-486095159214170537216474943399394414236274020963260529138704826156595453504700821/1987693822246803885122052946189354281356041870604277867774142931433606779990021400 : ℝ)) := by
    have e : (1110531942034132765221077951842510549638950756963287492021861734816364207264639618259962107206090228286370940394980620120686904003/74538518334255145692076985482100785550851570147660420041530359928760254249625802500000000000000000000000000000000000000000000000000 : ℝ) = (90219180749465342997959161/100000000000000000000000000 : ℝ) * (3602508599343921577733163/25000000000000000000000000 : ℝ) - (((1348176822279824946863895628071929327272256633641247796288505558289795097101/1084888789364052748447356474988872508672919797705997081287393865340782026200 : ℝ) : ℝ) * (90219180749465342997959163/100000000000000000000000000 : ℝ) + ((-101306737837531344615058534709483936488888679085806540792127233677560474818/92215547095944483618025300374054163237198182805009751909428478553966472227 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-486095159214170537216474943399394414236274020963260529138704826156595453504700821/1987693822246803885122052946189354281356041870604277867774142931433606779990021400 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (1110531942034132765221077951842510549638950756963287492021861734816364207264639618259962107206090228286370940394980620120686904003/74538518334255145692076985482100785550851570147660420041530359928760254249625802500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (1798701864932536123/100000000000000000000 : ℝ) ≤ (1110531942034132765221077951842510549638950756963287492021861734816364207264639618259962107206090228286370940394980620120686904003/74538518334255145692076985482100785550851570147660420041530359928760254249625802500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (1110531942034132765221077951842510549638950756963287492021861734816364207264639618259962107206090228286370940394980620120686904003/74538518334255145692076985482100785550851570147660420041530359928760254249625802500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 15 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[29/20, 37/25]`. -/
private theorem b9_pan_15 : (184179393434979955123/1000000000000000000000000 : ℝ) ≤ ∫ t in (29/20 : ℝ)..(37/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (1798701864932536123/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((29/20 : ℝ) + (37/25 : ℝ)) / 2) := b9_sig_15
  have hB0 : ((log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (7057599101275371697/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_15.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) ≤ (14410034397375686310932653/100000000000000000000000000 : ℝ) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 2) / 3) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (14410034397375686310932653/100000000000000000000000000 : ℝ) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (14410034397375686310932653/100000000000000000000000000 : ℝ) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (14410034397375686310932653/100000000000000000000000000 : ℝ) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (14410034397375686310932653/100000000000000000000000000 : ℝ) / ((((29/20 : ℝ) + (37/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (7057599101275371697/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (29/20 : ℝ) (37/25 : ℝ), 2 * (2768833474643506791/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_15.2.2.1
    have hX : (4908745955471022481558745681/8700000000000000000000000000 : ℝ) ≤ (1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (4908745955471022481558745681/8700000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((37/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2768833474643506791/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (4908745955471022481558745681/8700000000000000000000000000 : ℝ) / ((37/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2768833474643506791/50000000000000000000 : ℝ) ≤ ((1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) / ((37/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2768833474643506791/50000000000000000000 : ℝ) ≤ (4908745955471022481558745681/8700000000000000000000000000 : ℝ) / ((37/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (4908745955471022481558745681/8700000000000000000000000000 : ℝ) / ((37/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) / ((37/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) / ((37/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) / ((37/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((37/25 : ℝ) + 2) * ((37/25 : ℝ) + 1) - log (((37/25 : ℝ) + 2) / 3)) / ((37/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (29/20 : ℝ)) (b := (37/25 : ℝ)) (C := (2768833474643506791/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (37/25 : ℝ) - (29/20 : ℝ) ≤ (((29/20 : ℝ) + (37/25 : ℝ)) / 2) * log ((37/25 : ℝ) / (29/20 : ℝ)) := by
    have hl := b9_lgs_15.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (29/20 : ℝ)) (b := (37/25 : ℝ)) (m := (((29/20 : ℝ) + (37/25 : ℝ)) / 2)) (A := (1798701864932536123/100000000000000000000 : ℝ)) (B := (7057599101275371697/100000000000000000000 : ℝ)) (C := (2768833474643506791/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_15.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 16 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_16 :
    ((9142887292034819878318761/10000000000000000000000000 : ℝ) ≤ log ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) ∧ log ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) ≤ (22857218230087049695796903/25000000000000000000000000 : ℝ)) ∧
    ((1909013587720798598112623/12500000000000000000000000 : ℝ) ≤ log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) ≤ (3054421740353277756980197/20000000000000000000000000 : ℝ)) ∧
    (log (((151/100 : ℝ) + 2) / 3) ≤ (15700374880966475080799501/100000000000000000000000000 : ℝ)) ∧
    ((1003378152540463279683819/50000000000000000000000000 : ℝ) ≤ log ((151/100 : ℝ) / (37/25 : ℝ)) ∧ log ((151/100 : ℝ) / (37/25 : ℝ)) ≤ (2006756305080926559367639/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) = (499/200 : ℝ) by norm_num]
    have hkey : log (499/200 : ℝ) = log (2 : ℝ) + log (499/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (499/400 : ℝ)) (x := (99/899 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).1
    have hnum : (110570774321768339207321989271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 16, (99/899 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) = (499/200 : ℝ) by norm_num]
    have hkey : log (499/200 : ℝ) = log (2 : ℝ) + log (499/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (499/400 : ℝ)) (x := (99/899 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (99/899 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((99/899 : ℝ) ^ (2 * 16 + 1) / (1 - (99/899 : ℝ) ^ 2)) ≤ (221141548643536678414643998541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) = (233/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (233/200 : ℝ)) (x := (33/433 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).1
    have hnum : (1909013587720798598112623/12500000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 14, (33/433 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) = (233/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (233/200 : ℝ)) (x := (33/433 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (33/433 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((33/433 : ℝ) ^ (2 * 14 + 1) / (1 - (33/433 : ℝ) ^ 2)) ≤ (3054421740353277756980197/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((151/100 : ℝ) + 2) / 3) = (117/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (117/100 : ℝ)) (x := (17/217 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (17/217 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((17/217 : ℝ) ^ (2 * 14 + 1) / (1 - (17/217 : ℝ) ^ 2)) ≤ (15700374880966475080799501/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((151/100 : ℝ) / (37/25 : ℝ)) = (151/148 : ℝ) by norm_num]
    have h := (log_enclosure (y := (151/148 : ℝ)) (x := (3/299 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (1003378152540463279683819/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/299 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((151/100 : ℝ) / (37/25 : ℝ)) = (151/148 : ℝ) by norm_num]
    have h := (log_enclosure (y := (151/148 : ℝ)) (x := (3/299 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/299 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/299 : ℝ) ^ (2 * 8 + 1) / (1 - (3/299 : ℝ) ^ 2)) ≤ (2006756305080926559367639/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 16, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_16 : (2015443181419677433/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((37/25 : ℝ) + (151/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2)) (c := ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1)) (m := (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 23
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) - 1 = ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1)) (m := (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_16.1
  have hq := b9_lgs_16.2.1
  have hprod : (9142887292034819878318761/10000000000000000000000000 : ℝ) * (1909013587720798598112623/12500000000000000000000000 : ℝ) ≤ log ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) * log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((763434213166359540765039374404119741491449775427129822944938842370953920967601183/610105452332782048610218243949201427710399958498059597177377513735136283452134200 : ℝ) : ℝ) * log ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) ≤ ((763434213166359540765039374404119741491449775427129822944938842370953920967601183/610105452332782048610218243949201427710399958498059597177377513735136283452134200 : ℝ) : ℝ) * (22857218230087049695796903/25000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-3351291226453467731405621598122287211442181083337615569421570103814036175667114/3050527261663910243051091219746007138551999792490297985886887568675681417260671 : ℝ) : ℝ) * log 2 ≤ ((-3351291226453467731405621598122287211442181083337615569421570103814036175667114/3050527261663910243051091219746007138551999792490297985886887568675681417260671 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (53129206360381061087079499382786562421496831937565853284250747078901123827788177608287676925743573939779234130671480005879977951647/3182523764580259593830272618990541543116597820548377407532385162098671280314022781125000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) * log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) -
      ((763434213166359540765039374404119741491449775427129822944938842370953920967601183/610105452332782048610218243949201427710399958498059597177377513735136283452134200 : ℝ) * log ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) + (-3351291226453467731405621598122287211442181083337615569421570103814036175667114/3050527261663910243051091219746007138551999792490297985886887568675681417260671 : ℝ) * log 2 + (-216342144517129752416073892716963561601000333980545043983201250510151618803583642967/833242585635558875475562285699341785834163793016302448517569933349470298845853237240 : ℝ)) := by
    have e : (53129206360381061087079499382786562421496831937565853284250747078901123827788177608287676925743573939779234130671480005879977951647/3182523764580259593830272618990541543116597820548377407532385162098671280314022781125000000000000000000000000000000000000000000000000 : ℝ) = (9142887292034819878318761/10000000000000000000000000 : ℝ) * (1909013587720798598112623/12500000000000000000000000 : ℝ) - (((763434213166359540765039374404119741491449775427129822944938842370953920967601183/610105452332782048610218243949201427710399958498059597177377513735136283452134200 : ℝ) : ℝ) * (22857218230087049695796903/25000000000000000000000000 : ℝ) + ((-3351291226453467731405621598122287211442181083337615569421570103814036175667114/3050527261663910243051091219746007138551999792490297985886887568675681417260671 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-216342144517129752416073892716963561601000333980545043983201250510151618803583642967/833242585635558875475562285699341785834163793016302448517569933349470298845853237240 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (53129206360381061087079499382786562421496831937565853284250747078901123827788177608287676925743573939779234130671480005879977951647/3182523764580259593830272618990541543116597820548377407532385162098671280314022781125000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (2015443181419677433/100000000000000000000 : ℝ) ≤ (53129206360381061087079499382786562421496831937565853284250747078901123827788177608287676925743573939779234130671480005879977951647/3182523764580259593830272618990541543116597820548377407532385162098671280314022781125000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (53129206360381061087079499382786562421496831937565853284250747078901123827788177608287676925743573939779234130671480005879977951647/3182523764580259593830272618990541543116597820548377407532385162098671280314022781125000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 16 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[37/25, 151/100]`. -/
private theorem b9_pan_16 : (20222820822813262459/100000000000000000000000 : ℝ) ≤ ∫ t in (37/25 : ℝ)..(151/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (2015443181419677433/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((37/25 : ℝ) + (151/100 : ℝ)) / 2) := b9_sig_16
  have hB0 : ((log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1477975869504736617/20000000000000000000 : ℝ) := by
    have hp := b9_lgs_16.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) ≤ (3054421740353277756980197/20000000000000000000000000 : ℝ) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 2) / 3) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (3054421740353277756980197/20000000000000000000000000 : ℝ) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (3054421740353277756980197/20000000000000000000000000 : ℝ) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (3054421740353277756980197/20000000000000000000000000 : ℝ) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (3054421740353277756980197/20000000000000000000000000 : ℝ) / ((((37/25 : ℝ) + (151/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1477975869504736617/20000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (37/25 : ℝ) (151/100 : ℝ), 2 * (534737117903747509/10000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_16.2.2.1
    have hX : (19589168416780767246639375149/35100000000000000000000000000 : ℝ) ≤ (1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (19589168416780767246639375149/35100000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((151/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (534737117903747509/10000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (19589168416780767246639375149/35100000000000000000000000000 : ℝ) / ((151/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (534737117903747509/10000000000000000000 : ℝ) ≤ ((1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) / ((151/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (534737117903747509/10000000000000000000 : ℝ) ≤ (19589168416780767246639375149/35100000000000000000000000000 : ℝ) / ((151/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (19589168416780767246639375149/35100000000000000000000000000 : ℝ) / ((151/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) / ((151/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) / ((151/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) / ((151/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((151/100 : ℝ) + 2) * ((151/100 : ℝ) + 1) - log (((151/100 : ℝ) + 2) / 3)) / ((151/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (37/25 : ℝ)) (b := (151/100 : ℝ)) (C := (534737117903747509/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (151/100 : ℝ) - (37/25 : ℝ) ≤ (((37/25 : ℝ) + (151/100 : ℝ)) / 2) * log ((151/100 : ℝ) / (37/25 : ℝ)) := by
    have hl := b9_lgs_16.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (37/25 : ℝ)) (b := (151/100 : ℝ)) (m := (((37/25 : ℝ) + (151/100 : ℝ)) / 2)) (A := (2015443181419677433/100000000000000000000 : ℝ)) (B := (1477975869504736617/20000000000000000000 : ℝ)) (C := (534737117903747509/10000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_16.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 17 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_17 :
    ((5789006642045769675198391/6250000000000000000000000 : ℝ) ≤ log ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) ∧ log ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) ≤ (46312053136366157401587129/50000000000000000000000000 : ℝ)) ∧
    ((16126814759612228396849497/100000000000000000000000000 : ℝ) ≤ log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) ≤ (8063407379806114198424749/50000000000000000000000000 : ℝ)) ∧
    (log (((77/50 : ℝ) + 2) / 3) ≤ (16551443847757339199729959/100000000000000000000000000 : ℝ)) ∧
    ((983638279935241489414607/50000000000000000000000000 : ℝ) ≤ log ((77/50 : ℝ) / (151/100 : ℝ)) ∧ log ((77/50 : ℝ) / (151/100 : ℝ)) ≤ (393455311974096595765843/20000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) = (101/40 : ℝ) by norm_num]
    have hkey : log (101/40 : ℝ) = log (2 : ℝ) + log (101/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (101/80 : ℝ)) (x := (21/181 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).1
    have hnum : (116546941083688919307255219271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 16, (21/181 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) = (101/40 : ℝ) by norm_num]
    have hkey : log (101/40 : ℝ) = log (2 : ℝ) + log (101/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (101/80 : ℝ)) (x := (21/181 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (21/181 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((21/181 : ℝ) ^ (2 * 16 + 1) / (1 - (21/181 : ℝ) ^ 2)) ≤ (233093882167377838614510458541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) = (47/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (47/40 : ℝ)) (x := (7/87 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).1
    have hnum : (16126814759612228396849497/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 14, (7/87 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) = (47/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (47/40 : ℝ)) (x := (7/87 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (7/87 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((7/87 : ℝ) ^ (2 * 14 + 1) / (1 - (7/87 : ℝ) ^ 2)) ≤ (8063407379806114198424749/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((77/50 : ℝ) + 2) / 3) = (59/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (59/50 : ℝ)) (x := (9/109 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (9/109 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/109 : ℝ) ^ (2 * 14 + 1) / (1 - (9/109 : ℝ) ^ 2)) ≤ (16551443847757339199729959/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((77/50 : ℝ) / (151/100 : ℝ)) = (154/151 : ℝ) by norm_num]
    have h := (log_enclosure (y := (154/151 : ℝ)) (x := (3/305 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (983638279935241489414607/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/305 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((77/50 : ℝ) / (151/100 : ℝ)) = (154/151 : ℝ) by norm_num]
    have h := (log_enclosure (y := (154/151 : ℝ)) (x := (3/305 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/305 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/305 : ℝ) ^ (2 * 8 + 1) / (1 - (3/305 : ℝ) ^ 2)) ≤ (393455311974096595765843/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 17, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_17 : (2241980440940795729/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((151/100 : ℝ) + (77/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2)) (c := ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1)) (m := (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 23
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) - 1 = ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1)) (m := (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_17.1
  have hq := b9_lgs_17.2.1
  have hprod : (5789006642045769675198391/6250000000000000000000000 : ℝ) * (16126814759612228396849497/100000000000000000000000000 : ℝ) ≤ log ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) * log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((260685048655765452239262791177106716152299016736253144108373369/206915681830002475723588385623531044913645313455810104837939672 : ℝ) : ℝ) * log ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) ≤ ((260685048655765452239262791177106716152299016736253144108373369/206915681830002475723588385623531044913645313455810104837939672 : ℝ) : ℝ) * (46312053136366157401587129/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-312559692415371960807198107252890180301455570437165646122952966/284509062516253404119934030232355186756262306001738894152167049 : ℝ) : ℝ) * log 2 ≤ ((-312559692415371960807198107252890180301455570437165646122952966/284509062516253404119934030232355186756262306001738894152167049 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (3508047387214687530115812115859282247749683193319218985379077000060536069997368784680369144399180394718536306783985981/188904593148096409441624723259532397240596869996268318116170130002501875000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) * log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) -
      ((260685048655765452239262791177106716152299016736253144108373369/206915681830002475723588385623531044913645313455810104837939672 : ℝ) * log ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) + (-312559692415371960807198107252890180301455570437165646122952966/284509062516253404119934030232355186756262306001738894152167049 : ℝ) * log 2 + (-790580623911851379994258361216810649326462109250055374924439832769541/2878546181304326239110471973478588910332904685657421990341640076228600 : ℝ)) := by
    have e : (3508047387214687530115812115859282247749683193319218985379077000060536069997368784680369144399180394718536306783985981/188904593148096409441624723259532397240596869996268318116170130002501875000000000000000000000000000000000000000000000000 : ℝ) = (5789006642045769675198391/6250000000000000000000000 : ℝ) * (16126814759612228396849497/100000000000000000000000000 : ℝ) - (((260685048655765452239262791177106716152299016736253144108373369/206915681830002475723588385623531044913645313455810104837939672 : ℝ) : ℝ) * (46312053136366157401587129/50000000000000000000000000 : ℝ) + ((-312559692415371960807198107252890180301455570437165646122952966/284509062516253404119934030232355186756262306001738894152167049 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-790580623911851379994258361216810649326462109250055374924439832769541/2878546181304326239110471973478588910332904685657421990341640076228600 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (3508047387214687530115812115859282247749683193319218985379077000060536069997368784680369144399180394718536306783985981/188904593148096409441624723259532397240596869996268318116170130002501875000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (2241980440940795729/100000000000000000000 : ℝ) ≤ (3508047387214687530115812115859282247749683193319218985379077000060536069997368784680369144399180394718536306783985981/188904593148096409441624723259532397240596869996268318116170130002501875000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (3508047387214687530115812115859282247749683193319218985379077000060536069997368784680369144399180394718536306783985981/188904593148096409441624723259532397240596869996268318116170130002501875000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 17 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[151/100, 77/50]`. -/
private theorem b9_pan_17 : (220530579195642520429/1000000000000000000000000 : ℝ) ≤ ∫ t in (151/100 : ℝ)..(77/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (2241980440940795729/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((151/100 : ℝ) + (77/50 : ℝ)) / 2) := b9_sig_17
  have hB0 : ((log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1927685208384195307/25000000000000000000 : ℝ) := by
    have hp := b9_lgs_17.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) ≤ (8063407379806114198424749/50000000000000000000000000 : ℝ) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 2) / 3) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (8063407379806114198424749/50000000000000000000000000 : ℝ) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (8063407379806114198424749/50000000000000000000000000 : ℝ) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (8063407379806114198424749/50000000000000000000000000 : ℝ) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (8063407379806114198424749/50000000000000000000000000 : ℝ) / ((((151/100 : ℝ) + (77/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1927685208384195307/25000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (151/100 : ℝ) (77/50 : ℝ), 2 * (2582380846995128347/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_17.2.2.1
    have hX : (9770394438946950961647797257/17700000000000000000000000000 : ℝ) ≤ (1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9770394438946950961647797257/17700000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((77/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2582380846995128347/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9770394438946950961647797257/17700000000000000000000000000 : ℝ) / ((77/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2582380846995128347/50000000000000000000 : ℝ) ≤ ((1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) / ((77/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2582380846995128347/50000000000000000000 : ℝ) ≤ (9770394438946950961647797257/17700000000000000000000000000 : ℝ) / ((77/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9770394438946950961647797257/17700000000000000000000000000 : ℝ) / ((77/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) / ((77/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) / ((77/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) / ((77/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((77/50 : ℝ) + 2) * ((77/50 : ℝ) + 1) - log (((77/50 : ℝ) + 2) / 3)) / ((77/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (151/100 : ℝ)) (b := (77/50 : ℝ)) (C := (2582380846995128347/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (77/50 : ℝ) - (151/100 : ℝ) ≤ (((151/100 : ℝ) + (77/50 : ℝ)) / 2) * log ((77/50 : ℝ) / (151/100 : ℝ)) := by
    have hl := b9_lgs_17.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (151/100 : ℝ)) (b := (77/50 : ℝ)) (m := (((151/100 : ℝ) + (77/50 : ℝ)) / 2)) (A := (2241980440940795729/100000000000000000000 : ℝ)) (B := (1927685208384195307/25000000000000000000 : ℝ)) (C := (2582380846995128347/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_17.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 18 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_18 :
    ((5862826397847923479651541/6250000000000000000000000 : ℝ) ≤ log ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) ∧ log ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) ≤ (46902611182783387837212329/50000000000000000000000000 : ℝ)) ∧
    ((8487138729354725405748787/50000000000000000000000000 : ℝ) ≤ log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) ≤ (678971098348378032459903/4000000000000000000000000 : ℝ)) ∧
    (log (((157/100 : ℝ) + 2) / 3) ≤ (8697665356171900865945223/50000000000000000000000000 : ℝ)) ∧
    ((1929320293467889883991679/100000000000000000000000000 : ℝ) ≤ log ((157/100 : ℝ) / (77/50 : ℝ)) ∧ log ((157/100 : ℝ) / (77/50 : ℝ)) ≤ (3014562958543577943737/156250000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) = (511/200 : ℝ) by norm_num]
    have hkey : log (511/200 : ℝ) = log (2 : ℝ) + log (511/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (511/400 : ℝ)) (x := (111/911 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (122452521547861223663507219271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (111/911 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) = (511/200 : ℝ) by norm_num]
    have hkey : log (511/200 : ℝ) = log (2 : ℝ) + log (511/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (511/400 : ℝ)) (x := (111/911 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (111/911 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((111/911 : ℝ) ^ (2 * 17 + 1) / (1 - (111/911 : ℝ) ^ 2)) ≤ (244905043095722447327014458541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) = (237/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (237/200 : ℝ)) (x := (37/437 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).1
    have hnum : (8487138729354725405748787/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 14, (37/437 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) = (237/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (237/200 : ℝ)) (x := (37/437 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (37/437 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((37/437 : ℝ) ^ (2 * 14 + 1) / (1 - (37/437 : ℝ) ^ 2)) ≤ (678971098348378032459903/4000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((157/100 : ℝ) + 2) / 3) = (119/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (119/100 : ℝ)) (x := (19/219 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (19/219 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((19/219 : ℝ) ^ (2 * 14 + 1) / (1 - (19/219 : ℝ) ^ 2)) ≤ (8697665356171900865945223/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((157/100 : ℝ) / (77/50 : ℝ)) = (157/154 : ℝ) by norm_num]
    have h := (log_enclosure (y := (157/154 : ℝ)) (x := (3/311 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).1
    have hnum : (1929320293467889883991679/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 8, (3/311 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((157/100 : ℝ) / (77/50 : ℝ)) = (157/154 : ℝ) by norm_num]
    have h := (log_enclosure (y := (157/154 : ℝ)) (x := (3/311 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 8).2
    have hnum : 2 * (∑ i ∈ Finset.range 8, (3/311 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/311 : ℝ) ^ (2 * 8 + 1) / (1 - (3/311 : ℝ) ^ 2)) ≤ (3014562958543577943737/156250000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 18, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_18 : (2477978058249345107/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((77/50 : ℝ) + (157/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2)) (c := ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1)) (m := (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 24
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) - 1 = ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1)) (m := (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_18.1
  have hq := b9_lgs_18.2.1
  have hprod : (5862826397847923479651541/6250000000000000000000000 : ℝ) * (8487138729354725405748787/50000000000000000000000000 : ℝ) ≤ log ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) * log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((1229240960498373849491102973774218590798074915106204761772592585699866826816774401/969171891071349673283406839177482940094411326129816045478495264359972531393202600 : ℝ) : ℝ) * log ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) ≤ ((1229240960498373849491102973774218590798074915106204761772592585699866826816774401/969171891071349673283406839177482940094411326129816045478495264359972531393202600 : ℝ) : ℝ) * (46902611182783387837212329/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-37265586212963557027480611972566713257049382403017450615871778936775090008561394/33921016187497238564919239371211902903304396414543561591747334252599038598762091 : ℝ) : ℝ) * log 2 ≤ ((-37265586212963557027480611972566713257049382403017450615871778936775090008561394/33921016187497238564919239371211902903304396414543561591747334252599038598762091 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (231139325783331743571858087460770091630123274381836198444665294980246861624323091729197568839217186110129175887996128583309942973281559/11261215557418477780539455996340266066755223630562846570721251656639322143212222214867812500000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) * log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) -
      ((1229240960498373849491102973774218590798074915106204761772592585699866826816774401/969171891071349673283406839177482940094411326129816045478495264359972531393202600 : ℝ) * log ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) + (-37265586212963557027480611972566713257049382403017450615871778936775090008561394/33921016187497238564919239371211902903304396414543561591747334252599038598762091 : ℝ) * log 2 + (-695679173715488226481116710050688530613567681889093848513422665033410609737359138097391/2402392652249275259848417279219256760907781041186740601753867020083055390551940739171800 : ℝ)) := by
    have e : (231139325783331743571858087460770091630123274381836198444665294980246861624323091729197568839217186110129175887996128583309942973281559/11261215557418477780539455996340266066755223630562846570721251656639322143212222214867812500000000000000000000000000000000000000000000000 : ℝ) = (5862826397847923479651541/6250000000000000000000000 : ℝ) * (8487138729354725405748787/50000000000000000000000000 : ℝ) - (((1229240960498373849491102973774218590798074915106204761772592585699866826816774401/969171891071349673283406839177482940094411326129816045478495264359972531393202600 : ℝ) : ℝ) * (46902611182783387837212329/50000000000000000000000000 : ℝ) + ((-37265586212963557027480611972566713257049382403017450615871778936775090008561394/33921016187497238564919239371211902903304396414543561591747334252599038598762091 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-695679173715488226481116710050688530613567681889093848513422665033410609737359138097391/2402392652249275259848417279219256760907781041186740601753867020083055390551940739171800 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (231139325783331743571858087460770091630123274381836198444665294980246861624323091729197568839217186110129175887996128583309942973281559/11261215557418477780539455996340266066755223630562846570721251656639322143212222214867812500000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (2477978058249345107/100000000000000000000 : ℝ) ≤ (231139325783331743571858087460770091630123274381836198444665294980246861624323091729197568839217186110129175887996128583309942973281559/11261215557418477780539455996340266066755223630562846570721251656639322143212222214867812500000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (231139325783331743571858087460770091630123274381836198444665294980246861624323091729197568839217186110129175887996128583309942973281559/11261215557418477780539455996340266066755223630562846570721251656639322143212222214867812500000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 18 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[77/50, 157/100]`. -/
private theorem b9_pan_18 : (29879931063572367413/125000000000000000000000 : ℝ) ≤ ∫ t in (77/50 : ℝ)..(157/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (2477978058249345107/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((77/50 : ℝ) + (157/100 : ℝ)) / 2) := b9_sig_18
  have hB0 : ((log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (401032239869199451/5000000000000000000 : ℝ) := by
    have hp := b9_lgs_18.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) ≤ (678971098348378032459903/4000000000000000000000000 : ℝ) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 2) / 3) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (678971098348378032459903/4000000000000000000000000 : ℝ) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (678971098348378032459903/4000000000000000000000000 : ℝ) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (678971098348378032459903/4000000000000000000000000 : ℝ) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (678971098348378032459903/4000000000000000000000000 : ℝ) / ((((77/50 : ℝ) + (157/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (401032239869199451/5000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (77/50 : ℝ) (157/100 : ℝ), 2 * (2494728600280587897/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_18.2.2.1
    have hX : (9744933467846631390857555389/17850000000000000000000000000 : ℝ) ≤ (1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9744933467846631390857555389/17850000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((157/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2494728600280587897/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9744933467846631390857555389/17850000000000000000000000000 : ℝ) / ((157/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2494728600280587897/50000000000000000000 : ℝ) ≤ ((1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) / ((157/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2494728600280587897/50000000000000000000 : ℝ) ≤ (9744933467846631390857555389/17850000000000000000000000000 : ℝ) / ((157/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9744933467846631390857555389/17850000000000000000000000000 : ℝ) / ((157/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) / ((157/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) / ((157/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) / ((157/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((157/100 : ℝ) + 2) * ((157/100 : ℝ) + 1) - log (((157/100 : ℝ) + 2) / 3)) / ((157/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (77/50 : ℝ)) (b := (157/100 : ℝ)) (C := (2494728600280587897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (157/100 : ℝ) - (77/50 : ℝ) ≤ (((77/50 : ℝ) + (157/100 : ℝ)) / 2) * log ((157/100 : ℝ) / (77/50 : ℝ)) := by
    have hl := b9_lgs_18.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (77/50 : ℝ)) (b := (157/100 : ℝ)) (m := (((77/50 : ℝ) + (157/100 : ℝ)) / 2)) (A := (2477978058249345107/100000000000000000000 : ℝ)) (B := (401032239869199451/5000000000000000000 : ℝ)) (C := (2494728600280587897/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_18.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 19 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_19 :
    ((94972550796039245342967921/100000000000000000000000000 : ℝ) ≤ log ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) ∧ log ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) ≤ (94972550796039245342967923/100000000000000000000000000 : ℝ)) ∧
    ((2226827317293424868874357/12500000000000000000000000 : ℝ) ≤ log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) ∧ log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) ≤ (17814618538347398950994857/100000000000000000000000000 : ℝ)) ∧
    (log (((8/5 : ℝ) + 2) / 3) ≤ (18232155679395462621171803/100000000000000000000000000 : ℝ)) ∧
    ((189280098855188642624747/10000000000000000000000000 : ℝ) ≤ log ((8/5 : ℝ) / (157/100 : ℝ)) ∧ log ((8/5 : ℝ) / (157/100 : ℝ)) ≤ (1892800988551886426247471/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) = (517/200 : ℝ) by norm_num]
    have hkey : log (517/200 : ℝ) = log (2 : ℝ) + log (517/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (517/400 : ℝ)) (x := (117/917 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (128289163700223572006223544271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (117/917 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) = (517/200 : ℝ) by norm_num]
    have hkey : log (517/200 : ℝ) = log (2 : ℝ) + log (517/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (517/400 : ℝ)) (x := (117/917 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (117/917 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((117/917 : ℝ) ^ (2 * 17 + 1) / (1 - (117/917 : ℝ) ^ 2)) ≤ (256578327400447144012447108541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) = (239/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (239/200 : ℝ)) (x := (39/439 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).1
    have hnum : (2226827317293424868874357/12500000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 14, (39/439 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) = (239/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (239/200 : ℝ)) (x := (39/439 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14).2
    have hnum : 2 * (∑ i ∈ Finset.range 14, (39/439 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((39/439 : ℝ) ^ (2 * 14 + 1) / (1 - (39/439 : ℝ) ^ 2)) ≤ (17814618538347398950994857/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((8/5 : ℝ) + 2) / 3) = (6/5 : ℝ) by norm_num]
    have h := (log_enclosure (y := (6/5 : ℝ)) (x := (1/11 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (1/11 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/11 : ℝ) ^ (2 * 15 + 1) / (1 - (1/11 : ℝ) ^ 2)) ≤ (18232155679395462621171803/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((8/5 : ℝ) / (157/100 : ℝ)) = (160/157 : ℝ) by norm_num]
    have h := (log_enclosure (y := (160/157 : ℝ)) (x := (3/317 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (189280098855188642624747/10000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/317 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((8/5 : ℝ) / (157/100 : ℝ)) = (160/157 : ℝ) by norm_num]
    have h := (log_enclosure (y := (160/157 : ℝ)) (x := (3/317 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/317 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/317 : ℝ) ^ (2 * 7 + 1) / (1 - (3/317 : ℝ) ^ 2)) ≤ (1892800988551886426247471/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 19, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_19 : (544622787697027667/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((157/100 : ℝ) + (8/5 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2)) (c := ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1)) (m := (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 24
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) - 1 = ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1)) (m := (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_19.1
  have hq := b9_lgs_19.2.1
  have hprod : (94972550796039245342967921/100000000000000000000000000 : ℝ) * (2226827317293424868874357/12500000000000000000000000 : ℝ) ≤ log ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) * log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((383959564615295290946220081782337024633608025212543671332252768673073441088213716803/300733355557425649470028657174524130761669961108712173480348665477389944363669271400 : ℝ) : ℝ) * log ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) ≤ ((383959564615295290946220081782337024633608025212543671332252768673073441088213716803/300733355557425649470028657174524130761669961108712173480348665477389944363669271400 : ℝ) : ℝ) * (94972550796039245342967923/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-18171178547784236889071702949272375628367624302407768082623876804770082872726966618/16540334555658410720851576144598827191891847860979169541419176601256446940001809927 : ℝ) : ℝ) * log 2 ≤ ((-18171178547784236889071702949272375628367624302407768082623876804770082872726966618/16540334555658410720851576144598827191891847860979169541419176601256446940001809927 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (88922376015487070889117678746402329000844937914983216824081383633037753764082964629613984459948520918994784765934903209064100949553483009/3942340498698728191617037356968042047941445586441457204286098270311053796845856390821496250000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) * log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) -
      ((383959564615295290946220081782337024633608025212543671332252768673073441088213716803/300733355557425649470028657174524130761669961108712173480348665477389944363669271400 : ℝ) * log ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) + (-18171178547784236889071702949272375628367624302407768082623876804770082872726966618/16540334555658410720851576144598827191891847860979169541419176601256446940001809927 : ℝ) * log 2 + (-4923796003068298660785575195172456096321681316147565837946821822759515604117001783630973/16173704610046064375864768643971454555657212662323926991942967262814579679367615962344600 : ℝ)) := by
    have e : (88922376015487070889117678746402329000844937914983216824081383633037753764082964629613984459948520918994784765934903209064100949553483009/3942340498698728191617037356968042047941445586441457204286098270311053796845856390821496250000000000000000000000000000000000000000000000000 : ℝ) = (94972550796039245342967921/100000000000000000000000000 : ℝ) * (2226827317293424868874357/12500000000000000000000000 : ℝ) - (((383959564615295290946220081782337024633608025212543671332252768673073441088213716803/300733355557425649470028657174524130761669961108712173480348665477389944363669271400 : ℝ) : ℝ) * (94972550796039245342967923/100000000000000000000000000 : ℝ) + ((-18171178547784236889071702949272375628367624302407768082623876804770082872726966618/16540334555658410720851576144598827191891847860979169541419176601256446940001809927 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-4923796003068298660785575195172456096321681316147565837946821822759515604117001783630973/16173704610046064375864768643971454555657212662323926991942967262814579679367615962344600 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (88922376015487070889117678746402329000844937914983216824081383633037753764082964629613984459948520918994784765934903209064100949553483009/3942340498698728191617037356968042047941445586441457204286098270311053796845856390821496250000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (544622787697027667/20000000000000000000 : ℝ) ≤ (88922376015487070889117678746402329000844937914983216824081383633037753764082964629613984459948520918994784765934903209064100949553483009/3942340498698728191617037356968042047941445586441457204286098270311053796845856390821496250000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (88922376015487070889117678746402329000844937914983216824081383633037753764082964629613984459948520918994784765934903209064100949553483009/3942340498698728191617037356968042047941445586441457204286098270311053796845856390821496250000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 19 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[157/100, 8/5]`. -/
private theorem b9_pan_19 : (128856299393790895121/500000000000000000000000 : ℝ) ≤ ∫ t in (157/100 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (544622787697027667/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((157/100 : ℝ) + (8/5 : ℝ)) / 2) := b9_sig_19
  have hB0 : ((log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1664005919047391673/20000000000000000000 : ℝ) := by
    have hp := b9_lgs_19.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) ≤ (17814618538347398950994857/100000000000000000000000000 : ℝ) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 2) / 3) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (17814618538347398950994857/100000000000000000000000000 : ℝ) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (17814618538347398950994857/100000000000000000000000000 : ℝ) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (17814618538347398950994857/100000000000000000000000000 : ℝ) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (17814618538347398950994857/100000000000000000000000000 : ℝ) / ((((157/100 : ℝ) + (8/5 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1664005919047391673/20000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (157/100 : ℝ) (8/5 : ℝ), 2 * (24105495413108331/500000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_19.2.2.1
    have hX : (485910598885440836409453773/900000000000000000000000000 : ℝ) ≤ (1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (485910598885440836409453773/900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((8/5 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (24105495413108331/500000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (485910598885440836409453773/900000000000000000000000000 : ℝ) / ((8/5 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (24105495413108331/500000000000000000 : ℝ) ≤ ((1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) / ((8/5 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (24105495413108331/500000000000000000 : ℝ) ≤ (485910598885440836409453773/900000000000000000000000000 : ℝ) / ((8/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (485910598885440836409453773/900000000000000000000000000 : ℝ) / ((8/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) / ((8/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) / ((8/5 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) / ((8/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((8/5 : ℝ) + 2) * ((8/5 : ℝ) + 1) - log (((8/5 : ℝ) + 2) / 3)) / ((8/5 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (157/100 : ℝ)) (b := (8/5 : ℝ)) (C := (24105495413108331/500000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (8/5 : ℝ) - (157/100 : ℝ) ≤ (((157/100 : ℝ) + (8/5 : ℝ)) / 2) * log ((8/5 : ℝ) / (157/100 : ℝ)) := by
    have hl := b9_lgs_19.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (157/100 : ℝ)) (b := (8/5 : ℝ)) (m := (((157/100 : ℝ) + (8/5 : ℝ)) / 2)) (A := (544622787697027667/20000000000000000000 : ℝ)) (B := (1664005919047391673/20000000000000000000 : ℝ)) (C := (24105495413108331/500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_19.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 20 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_20 :
    ((48063204875844311167846407/50000000000000000000000000 : ℝ) ≤ log ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) ∧ log ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) ≤ (6007900609480538895980801/6250000000000000000000000 : ℝ)) ∧
    ((4661989173565457950329907/25000000000000000000000000 : ℝ) ≤ log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) ≤ (18647956694261831801319629/100000000000000000000000000 : ℝ)) ∧
    (log (((163/100 : ℝ) + 2) / 3) ≤ (762481438434598880351617/4000000000000000000000000 : ℝ)) ∧
    ((928819278646770618900621/50000000000000000000000000 : ℝ) ≤ log ((163/100 : ℝ) / (8/5 : ℝ)) ∧ log ((163/100 : ℝ) / (8/5 : ℝ)) ≤ (1857638557293541237801243/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) = (523/200 : ℝ) by norm_num]
    have hkey : log (523/200 : ℝ) = log (2 : ℝ) + log (523/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (523/400 : ℝ)) (x := (123/923 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (134058458478470456969848009271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (123/923 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) = (523/200 : ℝ) by norm_num]
    have hkey : log (523/200 : ℝ) = log (2 : ℝ) + log (523/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (523/400 : ℝ)) (x := (123/923 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (123/923 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((123/923 : ℝ) ^ (2 * 17 + 1) / (1 - (123/923 : ℝ) ^ 2)) ≤ (268116916956940913939696038541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) = (241/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (241/200 : ℝ)) (x := (41/441 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (4661989173565457950329907/25000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (41/441 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) = (241/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (241/200 : ℝ)) (x := (41/441 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (41/441 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((41/441 : ℝ) ^ (2 * 15 + 1) / (1 - (41/441 : ℝ) ^ 2)) ≤ (18647956694261831801319629/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((163/100 : ℝ) + 2) / 3) = (121/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (121/100 : ℝ)) (x := (21/221 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (21/221 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((21/221 : ℝ) ^ (2 * 15 + 1) / (1 - (21/221 : ℝ) ^ 2)) ≤ (762481438434598880351617/4000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((163/100 : ℝ) / (8/5 : ℝ)) = (163/160 : ℝ) by norm_num]
    have h := (log_enclosure (y := (163/160 : ℝ)) (x := (3/323 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (928819278646770618900621/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/323 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((163/100 : ℝ) / (8/5 : ℝ)) = (163/160 : ℝ) by norm_num]
    have h := (log_enclosure (y := (163/160 : ℝ)) (x := (3/323 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/323 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/323 : ℝ) ^ (2 * 7 + 1) / (1 - (3/323 : ℝ) ^ 2)) ≤ (1857638557293541237801243/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 20, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_20 : (744269702844693269/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((8/5 : ℝ) + (163/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2)) (c := ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1)) (m := (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 25
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) - 1 = ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1)) (m := (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_20.1
  have hq := b9_lgs_20.2.1
  have hprod : (48063204875844311167846407/50000000000000000000000000 : ℝ) * (4661989173565457950329907/25000000000000000000000000 : ℝ) ≤ log ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) * log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((298691760177670713008104210696257614896463344624518630063031255880271260224896279856337/232430168025443745104061095554420058328641711573221718813072660861538049084436950744200 : ℝ) : ℝ) * log ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) ≤ ((298691760177670713008104210696257614896463344624518630063031255880271260224896279856337/232430168025443745104061095554420058328641711573221718813072660861538049084436950744200 : ℝ) : ℝ) * (6007900609480538895980801/6250000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-1276741415499429762120079461840488930925597922722129512080236673399156519728293835814/1162150840127218725520305477772100291643208557866108594065363304307690245422184753721 : ℝ) : ℝ) * log 2 ≤ ((-1276741415499429762120079461840488930925597922722129512080236673399156519728293835814/1162150840127218725520305477772100291643208557866108594065363304307690245422184753721 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (29598921414739246379814337956134547823754779031636540076833120479887661485561157779913657027818474950618746622259354600436570772092659354449/1200312806930057363861422186633791944400557468439403898063457718290212870010368325823430876250000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) * log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) -
      ((298691760177670713008104210696257614896463344624518630063031255880271260224896279856337/232430168025443745104061095554420058328641711573221718813072660861538049084436950744200 : ℝ) * log ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) + (-1276741415499429762120079461840488930925597922722129512080236673399156519728293835814/1162150840127218725520305477772100291643208557866108594065363304307690245422184753721 : ℝ) * log 2 + (-4597867760145757669135040627138899883112917473467297650428011944602425534141092699981690705543/14403753683160688366337066239605503332806689621272846776761492619482554440124419909881170515000 : ℝ)) := by
    have e : (29598921414739246379814337956134547823754779031636540076833120479887661485561157779913657027818474950618746622259354600436570772092659354449/1200312806930057363861422186633791944400557468439403898063457718290212870010368325823430876250000000000000000000000000000000000000000000000000 : ℝ) = (48063204875844311167846407/50000000000000000000000000 : ℝ) * (4661989173565457950329907/25000000000000000000000000 : ℝ) - (((298691760177670713008104210696257614896463344624518630063031255880271260224896279856337/232430168025443745104061095554420058328641711573221718813072660861538049084436950744200 : ℝ) : ℝ) * (6007900609480538895980801/6250000000000000000000000 : ℝ) + ((-1276741415499429762120079461840488930925597922722129512080236673399156519728293835814/1162150840127218725520305477772100291643208557866108594065363304307690245422184753721 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-4597867760145757669135040627138899883112917473467297650428011944602425534141092699981690705543/14403753683160688366337066239605503332806689621272846776761492619482554440124419909881170515000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (29598921414739246379814337956134547823754779031636540076833120479887661485561157779913657027818474950618746622259354600436570772092659354449/1200312806930057363861422186633791944400557468439403898063457718290212870010368325823430876250000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (744269702844693269/25000000000000000000 : ℝ) ≤ (29598921414739246379814337956134547823754779031636540076833120479887661485561157779913657027818474950618746622259354600436570772092659354449/1200312806930057363861422186633791944400557468439403898063457718290212870010368325823430876250000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (29598921414739246379814337956134547823754779031636540076833120479887661485561157779913657027818474950618746622259354600436570772092659354449/1200312806930057363861422186633791944400557468439403898063457718290212870010368325823430876250000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 20 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[8/5, 163/100]`. -/
private theorem b9_pan_20 : (276512141577121339729/1000000000000000000000000 : ℝ) ≤ ∫ t in (8/5 : ℝ)..(163/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (744269702844693269/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((8/5 : ℝ) + (163/100 : ℝ)) / 2) := b9_sig_20
  have hB0 : ((log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (8609312062361238671/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_20.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) ≤ (18647956694261831801319629/100000000000000000000000000 : ℝ) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 2) / 3) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (18647956694261831801319629/100000000000000000000000000 : ℝ) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (18647956694261831801319629/100000000000000000000000000 : ℝ) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (18647956694261831801319629/100000000000000000000000000 : ℝ) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (18647956694261831801319629/100000000000000000000000000 : ℝ) / ((((8/5 : ℝ) + (163/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (8609312062361238671/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (8/5 : ℝ) (163/100 : ℝ), 2 * (145604682042695039/3125000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_20.2.2.1
    have hX : (775219237848240606432363029/1452000000000000000000000000 : ℝ) ≤ (1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (775219237848240606432363029/1452000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((163/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (145604682042695039/3125000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (775219237848240606432363029/1452000000000000000000000000 : ℝ) / ((163/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (145604682042695039/3125000000000000000 : ℝ) ≤ ((1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) / ((163/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (145604682042695039/3125000000000000000 : ℝ) ≤ (775219237848240606432363029/1452000000000000000000000000 : ℝ) / ((163/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (775219237848240606432363029/1452000000000000000000000000 : ℝ) / ((163/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) / ((163/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) / ((163/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) / ((163/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((163/100 : ℝ) + 2) * ((163/100 : ℝ) + 1) - log (((163/100 : ℝ) + 2) / 3)) / ((163/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (8/5 : ℝ)) (b := (163/100 : ℝ)) (C := (145604682042695039/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (163/100 : ℝ) - (8/5 : ℝ) ≤ (((8/5 : ℝ) + (163/100 : ℝ)) / 2) * log ((163/100 : ℝ) / (8/5 : ℝ)) := by
    have hl := b9_lgs_20.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (8/5 : ℝ)) (b := (163/100 : ℝ)) (m := (((8/5 : ℝ) + (163/100 : ℝ)) / 2)) (A := (744269702844693269/25000000000000000000 : ℝ)) (B := (8609312062361238671/100000000000000000000 : ℝ)) (C := (145604682042695039/3125000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_20.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 21 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_21 :
    ((97267106531026270416029063/100000000000000000000000000 : ℝ) ≤ log ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) ∧ log ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) ≤ (19453421306205254083205813/20000000000000000000000000 : ℝ)) ∧
    ((3894881535850235590460223/20000000000000000000000000 : ℝ) ≤ log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) ≤ (4868601919812794488075279/25000000000000000000000000 : ℝ)) ∧
    (log (((83/50 : ℝ) + 2) / 3) ≤ (2485635734314564876657979/12500000000000000000000000 : ℝ)) ∧
    ((1823758754978089882777197/100000000000000000000000000 : ℝ) ≤ log ((83/50 : ℝ) / (163/100 : ℝ)) ∧ log ((83/50 : ℝ) / (163/100 : ℝ)) ≤ (911879377489044941388599/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) = (529/200 : ℝ) by norm_num]
    have hkey : log (529/200 : ℝ) = log (2 : ℝ) + log (529/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (529/400 : ℝ)) (x := (129/929 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (139761942375158697371529254271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (129/929 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) = (529/200 : ℝ) by norm_num]
    have hkey : log (529/200 : ℝ) = log (2 : ℝ) + log (529/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (529/400 : ℝ)) (x := (129/929 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (129/929 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((129/929 : ℝ) ^ (2 * 18 + 1) / (1 - (129/929 : ℝ) ^ 2)) ≤ (279523884750317394743058528541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) = (243/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (243/200 : ℝ)) (x := (43/443 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (3894881535850235590460223/20000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (43/443 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) = (243/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (243/200 : ℝ)) (x := (43/443 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (43/443 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((43/443 : ℝ) ^ (2 * 15 + 1) / (1 - (43/443 : ℝ) ^ 2)) ≤ (4868601919812794488075279/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((83/50 : ℝ) + 2) / 3) = (61/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (61/50 : ℝ)) (x := (11/111 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (11/111 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((11/111 : ℝ) ^ (2 * 15 + 1) / (1 - (11/111 : ℝ) ^ 2)) ≤ (2485635734314564876657979/12500000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((83/50 : ℝ) / (163/100 : ℝ)) = (166/163 : ℝ) by norm_num]
    have h := (log_enclosure (y := (166/163 : ℝ)) (x := (3/329 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1823758754978089882777197/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/329 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((83/50 : ℝ) / (163/100 : ℝ)) = (166/163 : ℝ) by norm_num]
    have h := (log_enclosure (y := (166/163 : ℝ)) (x := (3/329 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/329 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/329 : ℝ) ^ (2 * 7 + 1) / (1 - (3/329 : ℝ) ^ 2)) ≤ (911879377489044941388599/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 21, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_21 : (809893901211778331/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((163/100 : ℝ) + (83/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2)) (c := ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1)) (m := (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 25
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) - 1 = ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1)) (m := (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_21.1
  have hq := b9_lgs_21.2.1
  have hprod : (97267106531026270416029063/100000000000000000000000000 : ℝ) * (3894881535850235590460223/20000000000000000000000000 : ℝ) ≤ log ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) * log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((34149509788279364401988717528524218776321773392857108487602328191894029031060680518691/26404008526449060840216155920200603291015670776164387929924635086028758355017903761800 : ℝ) : ℝ) * log ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) ≤ ((34149509788279364401988717528524218776321773392857108487602328191894029031060680518691/26404008526449060840216155920200603291015670776164387929924635086028758355017903761800 : ℝ) : ℝ) * (19453421306205254083205813/20000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-3335860835280059760931955365323239861764705855905180563174523454770000971769964621738/3036460980541641996624857930823069378466802139258904611941333034893307210827058932607 : ℝ) : ℝ) * log 2 ≤ ((-3335860835280059760931955365323239861764705855905180563174523454770000971769964621738/3036460980541641996624857930823069378466802139258904611941333034893307210827058932607 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (1211829080339061178237812841650370633118844705695954192668083676677734212976897459211491310262908761035771008525821885678466915529464704062747/45160852986136604502637991275305333990085005931293913528948550558677203297006910062295480806000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) * log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) -
      ((34149509788279364401988717528524218776321773392857108487602328191894029031060680518691/26404008526449060840216155920200603291015670776164387929924635086028758355017903761800 : ℝ) * log ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) + (-3335860835280059760931955365323239861764705855905180563174523454770000971769964621738/3036460980541641996624857930823069378466802139258904611941333034893307210827058932607 : ℝ) * log 2 + (-12566722386654870909062896296000504441843681006195685119501286473624484477327974987745371645331/37634044155113837085531659396087778325070838276078261274123792132231002747505758385246234005000 : ℝ)) := by
    have e : (1211829080339061178237812841650370633118844705695954192668083676677734212976897459211491310262908761035771008525821885678466915529464704062747/45160852986136604502637991275305333990085005931293913528948550558677203297006910062295480806000000000000000000000000000000000000000000000000000 : ℝ) = (97267106531026270416029063/100000000000000000000000000 : ℝ) * (3894881535850235590460223/20000000000000000000000000 : ℝ) - (((34149509788279364401988717528524218776321773392857108487602328191894029031060680518691/26404008526449060840216155920200603291015670776164387929924635086028758355017903761800 : ℝ) : ℝ) * (19453421306205254083205813/20000000000000000000000000 : ℝ) + ((-3335860835280059760931955365323239861764705855905180563174523454770000971769964621738/3036460980541641996624857930823069378466802139258904611941333034893307210827058932607 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-12566722386654870909062896296000504441843681006195685119501286473624484477327974987745371645331/37634044155113837085531659396087778325070838276078261274123792132231002747505758385246234005000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (1211829080339061178237812841650370633118844705695954192668083676677734212976897459211491310262908761035771008525821885678466915529464704062747/45160852986136604502637991275305333990085005931293913528948550558677203297006910062295480806000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (809893901211778331/25000000000000000000 : ℝ) ≤ (1211829080339061178237812841650370633118844705695954192668083676677734212976897459211491310262908761035771008525821885678466915529464704062747/45160852986136604502637991275305333990085005931293913528948550558677203297006910062295480806000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (1211829080339061178237812841650370633118844705695954192668083676677734212976897459211491310262908761035771008525821885678466915529464704062747/45160852986136604502637991275305333990085005931293913528948550558677203297006910062295480806000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 21 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[163/100, 83/50]`. -/
private theorem b9_pan_21 : (295404065397585916007/1000000000000000000000000 : ℝ) ≤ ∫ t in (163/100 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (809893901211778331/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((163/100 : ℝ) + (83/50 : ℝ)) / 2) := b9_sig_21
  have hB0 : ((log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (8888888779508773459/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_21.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) ≤ (4868601919812794488075279/25000000000000000000000000 : ℝ) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 2) / 3) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (4868601919812794488075279/25000000000000000000000000 : ℝ) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (4868601919812794488075279/25000000000000000000000000 : ℝ) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (4868601919812794488075279/25000000000000000000000000 : ℝ) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (4868601919812794488075279/25000000000000000000000000 : ℝ) / ((((163/100 : ℝ) + (83/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (8888888779508773459/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (163/100 : ℝ) (83/50 : ℝ), 2 * (1125972891126730861/25000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_21.2.2.1
    have hX : (1207628660620434627571589843/2287500000000000000000000000 : ℝ) ≤ (1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (1207628660620434627571589843/2287500000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((83/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (1125972891126730861/25000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (1207628660620434627571589843/2287500000000000000000000000 : ℝ) / ((83/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (1125972891126730861/25000000000000000000 : ℝ) ≤ ((1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) / ((83/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (1125972891126730861/25000000000000000000 : ℝ) ≤ (1207628660620434627571589843/2287500000000000000000000000 : ℝ) / ((83/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (1207628660620434627571589843/2287500000000000000000000000 : ℝ) / ((83/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) / ((83/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) / ((83/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) / ((83/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((83/50 : ℝ) + 2) * ((83/50 : ℝ) + 1) - log (((83/50 : ℝ) + 2) / 3)) / ((83/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (163/100 : ℝ)) (b := (83/50 : ℝ)) (C := (1125972891126730861/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (83/50 : ℝ) - (163/100 : ℝ) ≤ (((163/100 : ℝ) + (83/50 : ℝ)) / 2) * log ((83/50 : ℝ) / (163/100 : ℝ)) := by
    have hl := b9_lgs_21.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (163/100 : ℝ)) (b := (83/50 : ℝ)) (m := (((163/100 : ℝ) + (83/50 : ℝ)) / 2)) (A := (809893901211778331/25000000000000000000 : ℝ)) (B := (8888888779508773459/100000000000000000000 : ℝ)) (C := (1125972891126730861/25000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_21.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 22 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_22 :
    ((98394938034796987045194311/100000000000000000000000000 : ℝ) ≤ log ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) ∧ log ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) ≤ (98394938034796987045194313/100000000000000000000000000 : ℝ)) ∧
    ((10147042199834515367912489/50000000000000000000000000 : ℝ) ≤ log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) ≤ (20294084399669030735824979/100000000000000000000000000 : ℝ)) ∧
    (log (((169/100 : ℝ) + 2) / 3) ≤ (20701416938432612722602571/100000000000000000000000000 : ℝ)) ∧
    ((1791092656653023921427053/100000000000000000000000000 : ℝ) ≤ log ((169/100 : ℝ) / (83/50 : ℝ)) ∧ log ((169/100 : ℝ) / (83/50 : ℝ)) ≤ (895546328326511960713527/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) = (107/40 : ℝ) by norm_num]
    have hkey : log (107/40 : ℝ) = log (2 : ℝ) + log (107/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (107/80 : ℝ)) (x := (27/187 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (145401099894012280517355494271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (27/187 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) = (107/40 : ℝ) by norm_num]
    have hkey : log (107/40 : ℝ) = log (2 : ℝ) + log (107/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (107/80 : ℝ)) (x := (27/187 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (27/187 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((27/187 : ℝ) ^ (2 * 18 + 1) / (1 - (27/187 : ℝ) ^ 2)) ≤ (290802199788024561034711008541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) = (49/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (49/40 : ℝ)) (x := (9/89 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (10147042199834515367912489/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (9/89 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) = (49/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (49/40 : ℝ)) (x := (9/89 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (9/89 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/89 : ℝ) ^ (2 * 15 + 1) / (1 - (9/89 : ℝ) ^ 2)) ≤ (20294084399669030735824979/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((169/100 : ℝ) + 2) / 3) = (123/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (123/100 : ℝ)) (x := (23/223 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (23/223 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((23/223 : ℝ) ^ (2 * 15 + 1) / (1 - (23/223 : ℝ) ^ 2)) ≤ (20701416938432612722602571/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((169/100 : ℝ) / (83/50 : ℝ)) = (169/166 : ℝ) by norm_num]
    have h := (log_enclosure (y := (169/166 : ℝ)) (x := (3/335 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1791092656653023921427053/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/335 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((169/100 : ℝ) / (83/50 : ℝ)) = (169/166 : ℝ) by norm_num]
    have h := (log_enclosure (y := (169/166 : ℝ)) (x := (3/335 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/335 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/335 : ℝ) ^ (2 * 7 + 1) / (1 - (3/335 : ℝ) ^ 2)) ≤ (895546328326511960713527/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 22, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_22 : (3510318855256466931/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((83/50 : ℝ) + (169/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2)) (c := ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1)) (m := (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 26
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) - 1 = ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1)) (m := (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_22.1
  have hq := b9_lgs_22.2.1
  have hprod : (98394938034796987045194311/100000000000000000000000000 : ℝ) * (10147042199834515367912489/50000000000000000000000000 : ℝ) ≤ log ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) * log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((2377642626708868440041919375025294985999219583814366095239660594058260801/1826784116995824301212438263255349012057286364979494413043235263853940200 : ℝ) : ℝ) * log ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) ≤ ((2377642626708868440041919375025294985999219583814366095239660594058260801/1826784116995824301212438263255349012057286364979494413043235263853940200 : ℝ) : ℝ) * (98394938034796987045194313/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-912233416457266911740110982275489482436105019804440637224768387941194/830356416816283773278381028752431369116948347717952005928743301751791 : ℝ) : ℝ) * log 2 ≤ ((-912233416457266911740110982275489482436105019804440637224768387941194/830356416816283773278381028752431369116948347717952005928743301751791 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (9874823736376462124026119108457568673480102445632325317522121630519270108221132185350593380344024599253899533802467889719530591/339618759609178517811022776539542794959603849645952416462317324248652316688645000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) * log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) -
      ((2377642626708868440041919375025294985999219583814366095239660594058260801/1826784116995824301212438263255349012057286364979494413043235263853940200 : ℝ) * log ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) + (-912233416457266911740110982275489482436105019804440637224768387941194/830356416816283773278381028752431369116948347717952005928743301751791 : ℝ) * log 2 + (-4384262461648994719159067800301780958793205616425890681045408610177541267526487/12578472578117722881889732464427510924429772209109348757863604601801937655135000 : ℝ)) := by
    have e : (9874823736376462124026119108457568673480102445632325317522121630519270108221132185350593380344024599253899533802467889719530591/339618759609178517811022776539542794959603849645952416462317324248652316688645000000000000000000000000000000000000000000000000000 : ℝ) = (98394938034796987045194311/100000000000000000000000000 : ℝ) * (10147042199834515367912489/50000000000000000000000000 : ℝ) - (((2377642626708868440041919375025294985999219583814366095239660594058260801/1826784116995824301212438263255349012057286364979494413043235263853940200 : ℝ) : ℝ) * (98394938034796987045194313/100000000000000000000000000 : ℝ) + ((-912233416457266911740110982275489482436105019804440637224768387941194/830356416816283773278381028752431369116948347717952005928743301751791 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-4384262461648994719159067800301780958793205616425890681045408610177541267526487/12578472578117722881889732464427510924429772209109348757863604601801937655135000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (9874823736376462124026119108457568673480102445632325317522121630519270108221132185350593380344024599253899533802467889719530591/339618759609178517811022776539542794959603849645952416462317324248652316688645000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (3510318855256466931/100000000000000000000 : ℝ) ≤ (9874823736376462124026119108457568673480102445632325317522121630519270108221132185350593380344024599253899533802467889719530591/339618759609178517811022776539542794959603849645952416462317324248652316688645000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (9874823736376462124026119108457568673480102445632325317522121630519270108221132185350593380344024599253899533802467889719530591/339618759609178517811022776539542794959603849645952416462317324248652316688645000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 22 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[83/50, 169/100]`. -/
private theorem b9_pan_22 : (314357835659984939409/1000000000000000000000000 : ℝ) ≤ ∫ t in (83/50 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (3510318855256466931/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((83/50 : ℝ) + (169/100 : ℝ)) / 2) := b9_sig_22
  have hB0 : ((log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2289784313058516011/25000000000000000000 : ℝ) := by
    have hp := b9_lgs_22.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) ≤ (20294084399669030735824979/100000000000000000000000000 : ℝ) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 2) / 3) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (20294084399669030735824979/100000000000000000000000000 : ℝ) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (20294084399669030735824979/100000000000000000000000000 : ℝ) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (20294084399669030735824979/100000000000000000000000000 : ℝ) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (20294084399669030735824979/100000000000000000000000000 : ℝ) / ((((83/50 : ℝ) + (169/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2289784313058516011/25000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (83/50 : ℝ) (169/100 : ℝ), 2 * (4354424749585860903/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_22.2.2.1
    have hX : (19261177149718365905359651301/36900000000000000000000000000 : ℝ) ≤ (1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (19261177149718365905359651301/36900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((169/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (4354424749585860903/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (19261177149718365905359651301/36900000000000000000000000000 : ℝ) / ((169/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (4354424749585860903/100000000000000000000 : ℝ) ≤ ((1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) / ((169/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (4354424749585860903/100000000000000000000 : ℝ) ≤ (19261177149718365905359651301/36900000000000000000000000000 : ℝ) / ((169/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (19261177149718365905359651301/36900000000000000000000000000 : ℝ) / ((169/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) / ((169/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) / ((169/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) / ((169/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((169/100 : ℝ) + 2) * ((169/100 : ℝ) + 1) - log (((169/100 : ℝ) + 2) / 3)) / ((169/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (83/50 : ℝ)) (b := (169/100 : ℝ)) (C := (4354424749585860903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (169/100 : ℝ) - (83/50 : ℝ) ≤ (((83/50 : ℝ) + (169/100 : ℝ)) / 2) * log ((169/100 : ℝ) / (83/50 : ℝ)) := by
    have hl := b9_lgs_22.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (83/50 : ℝ)) (b := (169/100 : ℝ)) (m := (((83/50 : ℝ) + (169/100 : ℝ)) / 2)) (A := (3510318855256466931/100000000000000000000 : ℝ)) (B := (2289784313058516011/25000000000000000000 : ℝ)) (C := (4354424749585860903/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_22.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 23 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_23 :
    ((49755095614922242205848529/50000000000000000000000000 : ℝ) ≤ log ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) ∧ log ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) ≤ (4975509561492224220584853/5000000000000000000000000 : ℝ)) ∧
    ((329798390749907060327031/1562500000000000000000000 : ℝ) ≤ log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) ≤ (4221419401598810372185997/20000000000000000000000000 : ℝ)) ∧
    (log (((43/25 : ℝ) + 2) / 3) ≤ (10755568980847274836382283/50000000000000000000000000 : ℝ)) ∧
    ((1759576189037957020033187/100000000000000000000000000 : ℝ) ≤ log ((43/25 : ℝ) / (169/100 : ℝ)) ∧ log ((43/25 : ℝ) / (169/100 : ℝ)) ≤ (439894047259489255008297/25000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) = (541/200 : ℝ) by norm_num]
    have hkey : log (541/200 : ℝ) = log (2 : ℝ) + log (541/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (541/400 : ℝ)) (x := (141/941 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (150977365869249767349869229271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (141/941 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) = (541/200 : ℝ) by norm_num]
    have hkey : log (541/200 : ℝ) = log (2 : ℝ) + log (541/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (541/400 : ℝ)) (x := (141/941 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (141/941 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((141/941 : ℝ) ^ (2 * 18 + 1) / (1 - (141/941 : ℝ) ^ 2)) ≤ (301954731738499534699738478541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) = (247/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (247/200 : ℝ)) (x := (47/447 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).1
    have hnum : (329798390749907060327031/1562500000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 15, (47/447 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) = (247/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (247/200 : ℝ)) (x := (47/447 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 15).2
    have hnum : 2 * (∑ i ∈ Finset.range 15, (47/447 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((47/447 : ℝ) ^ (2 * 15 + 1) / (1 - (47/447 : ℝ) ^ 2)) ≤ (4221419401598810372185997/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((43/25 : ℝ) + 2) / 3) = (31/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (31/25 : ℝ)) (x := (3/28 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (3/28 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/28 : ℝ) ^ (2 * 16 + 1) / (1 - (3/28 : ℝ) ^ 2)) ≤ (10755568980847274836382283/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((43/25 : ℝ) / (169/100 : ℝ)) = (172/169 : ℝ) by norm_num]
    have h := (log_enclosure (y := (172/169 : ℝ)) (x := (3/341 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1759576189037957020033187/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/341 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((43/25 : ℝ) / (169/100 : ℝ)) = (172/169 : ℝ) by norm_num]
    have h := (log_enclosure (y := (172/169 : ℝ)) (x := (3/341 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/341 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/341 : ℝ) ^ (2 * 7 + 1) / (1 - (3/341 : ℝ) ^ 2)) ≤ (439894047259489255008297/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 23, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_23 : (1894517075922756239/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((169/100 : ℝ) + (43/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2)) (c := ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1)) (m := (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 26
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) - 1 = ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1)) (m := (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_23.1
  have hq := b9_lgs_23.2.1
  have hprod : (49755095614922242205848529/50000000000000000000000000 : ℝ) * (329798390749907060327031/1562500000000000000000000 : ℝ) ≤ log ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) * log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((4005956710883725895141960327883505502006821872449521027756115387303137704392908710411230267/3058740655838436439775319118553713037266323704669168848898306098335390989319147540350557800 : ℝ) : ℝ) * log ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) ≤ ((4005956710883725895141960327883505502006821872449521027756115387303137704392908710411230267/3058740655838436439775319118553713037266323704669168848898306098335390989319147540350557800 : ℝ) : ℝ) * (4975509561492224220584853/5000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-16801726767164768190980812901603583294441034253044880397045926210423094623025898977168526/15293703279192182198876595592768565186331618523345844244491530491676954946595737701752789 : ℝ) : ℝ) * log 2 ≤ ((-16801726767164768190980812901603583294441034253044880397045926210423094623025898977168526/15293703279192182198876595592768565186331618523345844244491530491676954946595737701752789 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (278860344709299284794539394697773752201140541480246673024409089651314273902119163334262619502238936227212915017130677037402345939283530167288919/8885198326779675021641381475573152221877097781558297903845305281460216124731093368883421168006328125000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) * log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) -
      ((4005956710883725895141960327883505502006821872449521027756115387303137704392908710411230267/3058740655838436439775319118553713037266323704669168848898306098335390989319147540350557800 : ℝ) * log ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) + (-16801726767164768190980812901603583294441034253044880397045926210423094623025898977168526/15293703279192182198876595592768565186331618523345844244491530491676954946595737701752789 : ℝ) * log 2 + (-68828500878345596699292271280245927386495522333427848777770418542315478982892230913786731722853637/189550897637966400461682804812227247400044752673243688615366512671151277327596658536179651584135000 : ℝ)) := by
    have e : (278860344709299284794539394697773752201140541480246673024409089651314273902119163334262619502238936227212915017130677037402345939283530167288919/8885198326779675021641381475573152221877097781558297903845305281460216124731093368883421168006328125000000000000000000000000000000000000000000000 : ℝ) = (49755095614922242205848529/50000000000000000000000000 : ℝ) * (329798390749907060327031/1562500000000000000000000 : ℝ) - (((4005956710883725895141960327883505502006821872449521027756115387303137704392908710411230267/3058740655838436439775319118553713037266323704669168848898306098335390989319147540350557800 : ℝ) : ℝ) * (4975509561492224220584853/5000000000000000000000000 : ℝ) + ((-16801726767164768190980812901603583294441034253044880397045926210423094623025898977168526/15293703279192182198876595592768565186331618523345844244491530491676954946595737701752789 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-68828500878345596699292271280245927386495522333427848777770418542315478982892230913786731722853637/189550897637966400461682804812227247400044752673243688615366512671151277327596658536179651584135000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (278860344709299284794539394697773752201140541480246673024409089651314273902119163334262619502238936227212915017130677037402345939283530167288919/8885198326779675021641381475573152221877097781558297903845305281460216124731093368883421168006328125000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (1894517075922756239/50000000000000000000 : ℝ) ≤ (278860344709299284794539394697773752201140541480246673024409089651314273902119163334262619502238936227212915017130677037402345939283530167288919/8885198326779675021641381475573152221877097781558297903845305281460216124731093368883421168006328125000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (278860344709299284794539394697773752201140541480246673024409089651314273902119163334262619502238936227212915017130677037402345939283530167288919/8885198326779675021641381475573152221877097781558297903845305281460216124731093368883421168006328125000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 23 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[169/100, 43/25]`. -/
private theorem b9_pan_23 : (333346039833305012237/1000000000000000000000000 : ℝ) ≤ ∫ t in (169/100 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (1894517075922756239/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((169/100 : ℝ) + (43/25 : ℝ)) / 2) := b9_sig_23
  have hB0 : ((log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (4710208504991934557/50000000000000000000 : ℝ) := by
    have hp := b9_lgs_23.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) ≤ (4221419401598810372185997/20000000000000000000000000 : ℝ) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 2) / 3) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (4221419401598810372185997/20000000000000000000000000 : ℝ) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (4221419401598810372185997/20000000000000000000000000 : ℝ) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (4221419401598810372185997/20000000000000000000000000 : ℝ) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (4221419401598810372185997/20000000000000000000000000 : ℝ) / ((((169/100 : ℝ) + (43/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (4710208504991934557/50000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (169/100 : ℝ) (43/25 : ℝ), 2 * (842133382261905609/20000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_23.2.2.1
    have hX : (2399732084781203440216447681/4650000000000000000000000000 : ℝ) ≤ (1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (2399732084781203440216447681/4650000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((43/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (842133382261905609/20000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (2399732084781203440216447681/4650000000000000000000000000 : ℝ) / ((43/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (842133382261905609/20000000000000000000 : ℝ) ≤ ((1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) / ((43/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (842133382261905609/20000000000000000000 : ℝ) ≤ (2399732084781203440216447681/4650000000000000000000000000 : ℝ) / ((43/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (2399732084781203440216447681/4650000000000000000000000000 : ℝ) / ((43/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) / ((43/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) / ((43/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) / ((43/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((43/25 : ℝ) + 2) * ((43/25 : ℝ) + 1) - log (((43/25 : ℝ) + 2) / 3)) / ((43/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (169/100 : ℝ)) (b := (43/25 : ℝ)) (C := (842133382261905609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (43/25 : ℝ) - (169/100 : ℝ) ≤ (((169/100 : ℝ) + (43/25 : ℝ)) / 2) * log ((43/25 : ℝ) / (169/100 : ℝ)) := by
    have hl := b9_lgs_23.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (169/100 : ℝ)) (b := (43/25 : ℝ)) (m := (((169/100 : ℝ) + (43/25 : ℝ)) / 2)) (A := (1894517075922756239/50000000000000000000 : ℝ)) (B := (4710208504991934557/50000000000000000000 : ℝ)) (C := (842133382261905609/20000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_23.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 24 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_24 :
    ((50306571793697226408975879/50000000000000000000000000 : ℝ) ≤ log ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) ∧ log ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) ≤ (1257664294842430660224397/1250000000000000000000000 : ℝ)) ∧
    ((10956776495833546870875121/50000000000000000000000000 : ℝ) ≤ log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) ∧ log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) ≤ (21913552991667093741750243/100000000000000000000000000 : ℝ)) ∧
    (log (((7/4 : ℝ) + 2) / 3) ≤ (2231435513142097557662951/10000000000000000000000000 : ℝ)) ∧
    ((345829942201220239991293/20000000000000000000000000 : ℝ) ≤ log ((7/4 : ℝ) / (43/25 : ℝ)) ∧ log ((7/4 : ℝ) / (43/25 : ℝ)) ≤ (864574855503050599978233/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) = (547/200 : ℝ) by norm_num]
    have hkey : log (547/200 : ℝ) = log (2 : ℝ) + log (547/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (547/400 : ℝ)) (x := (147/947 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (156492127656999609381142729271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (147/947 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) = (547/200 : ℝ) by norm_num]
    have hkey : log (547/200 : ℝ) = log (2 : ℝ) + log (547/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (547/400 : ℝ)) (x := (147/947 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (147/947 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((147/947 : ℝ) ^ (2 * 19 + 1) / (1 - (147/947 : ℝ) ^ 2)) ≤ (312984255313999218762285478541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) = (249/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (249/200 : ℝ)) (x := (49/449 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).1
    have hnum : (10956776495833546870875121/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 16, (49/449 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) = (249/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (249/200 : ℝ)) (x := (49/449 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (49/449 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((49/449 : ℝ) ^ (2 * 16 + 1) / (1 - (49/449 : ℝ) ^ 2)) ≤ (21913552991667093741750243/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((7/4 : ℝ) + 2) / 3) = (5/4 : ℝ) by norm_num]
    have h := (log_enclosure (y := (5/4 : ℝ)) (x := (1/9 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (1/9 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/9 : ℝ) ^ (2 * 16 + 1) / (1 - (1/9 : ℝ) ^ 2)) ≤ (2231435513142097557662951/10000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((7/4 : ℝ) / (43/25 : ℝ)) = (175/172 : ℝ) by norm_num]
    have h := (log_enclosure (y := (175/172 : ℝ)) (x := (3/347 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (345829942201220239991293/20000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/347 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((7/4 : ℝ) / (43/25 : ℝ)) = (175/172 : ℝ) by norm_num]
    have h := (log_enclosure (y := (175/172 : ℝ)) (x := (3/347 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/347 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/347 : ℝ) ^ (2 * 7 + 1) / (1 - (3/347 : ℝ) ^ 2)) ≤ (864574855503050599978233/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 24, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_24 : (2037728806498137943/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((43/25 : ℝ) + (7/4 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2)) (c := ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1)) (m := (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 27
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) - 1 = ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1)) (m := (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_24.1
  have hq := b9_lgs_24.2.1
  have hprod : (50306571793697226408975879/50000000000000000000000000 : ℝ) * (10956776495833546870875121/50000000000000000000000000 : ℝ) ≤ log ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) * log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((32926355986736718824929282384143777675710999573007772276799909858673378819397907770156014223249/24986951615159028921431437875465017177791409814395391177281314232044966258667171859428989769160 : ℝ) : ℝ) * log ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) ≤ ((32926355986736718824929282384143777675710999573007772276799909858673378819397907770156014223249/24986951615159028921431437875465017177791409814395391177281314232044966258667171859428989769160 : ℝ) : ℝ) * (1257664294842430660224397/1250000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-686270677588665706070787532394447121715413366617127799673254988410653157960967680126055749486/624673790378975723035785946886625429444785245359884779432032855801124156466679296485724744229 : ℝ) : ℝ) * log 2 ≤ ((-686270677588665706070787532394447121715413366617127799673254988410653157960967680126055749486/624673790378975723035785946886625429444785245359884779432032855801124156466679296485724744229 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (1697122704945622498490324722273120980783956884977684662493376432587499554577893367001771729917129962833465975668280262309628303277479534425227827249/50274267211191948669689249493724686749574187200934660286006197595587639715902072013918198852836777500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) * log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) -
      ((32926355986736718824929282384143777675710999573007772276799909858673378819397907770156014223249/24986951615159028921431437875465017177791409814395391177281314232044966258667171859428989769160 : ℝ) * log ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) + (-686270677588665706070787532394447121715413366617127799673254988410653157960967680126055749486/624673790378975723035785946886625429444785245359884779432032855801124156466679296485724744229 : ℝ) * log 2 + (-493084550022561585563990835783710558344672817026056414218879239845527523294629221313857121437323283/1305825122368622043368551934901939915573355511712588578857303833651627005607846026335537632541215000 : ℝ)) := by
    have e : (1697122704945622498490324722273120980783956884977684662493376432587499554577893367001771729917129962833465975668280262309628303277479534425227827249/50274267211191948669689249493724686749574187200934660286006197595587639715902072013918198852836777500000000000000000000000000000000000000000000000000 : ℝ) = (50306571793697226408975879/50000000000000000000000000 : ℝ) * (10956776495833546870875121/50000000000000000000000000 : ℝ) - (((32926355986736718824929282384143777675710999573007772276799909858673378819397907770156014223249/24986951615159028921431437875465017177791409814395391177281314232044966258667171859428989769160 : ℝ) : ℝ) * (1257664294842430660224397/1250000000000000000000000 : ℝ) + ((-686270677588665706070787532394447121715413366617127799673254988410653157960967680126055749486/624673790378975723035785946886625429444785245359884779432032855801124156466679296485724744229 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-493084550022561585563990835783710558344672817026056414218879239845527523294629221313857121437323283/1305825122368622043368551934901939915573355511712588578857303833651627005607846026335537632541215000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (1697122704945622498490324722273120980783956884977684662493376432587499554577893367001771729917129962833465975668280262309628303277479534425227827249/50274267211191948669689249493724686749574187200934660286006197595587639715902072013918198852836777500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (2037728806498137943/50000000000000000000 : ℝ) ≤ (1697122704945622498490324722273120980783956884977684662493376432587499554577893367001771729917129962833465975668280262309628303277479534425227827249/50274267211191948669689249493724686749574187200934660286006197595587639715902072013918198852836777500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (1697122704945622498490324722273120980783956884977684662493376432587499554577893367001771729917129962833465975668280262309628303277479534425227827249/50274267211191948669689249493724686749574187200934660286006197595587639715902072013918198852836777500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 24 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[43/25, 7/4]`. -/
private theorem b9_pan_24 : (88086018046525895221/250000000000000000000000 : ℝ) ≤ ∫ t in (43/25 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (2037728806498137943/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((43/25 : ℝ) + (7/4 : ℝ)) / 2) := b9_sig_24
  have hB0 : ((log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1934614126240842119/20000000000000000000 : ℝ) := by
    have hp := b9_lgs_24.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) ≤ (21913552991667093741750243/100000000000000000000000000 : ℝ) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 2) / 3) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (21913552991667093741750243/100000000000000000000000000 : ℝ) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (21913552991667093741750243/100000000000000000000000000 : ℝ) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (21913552991667093741750243/100000000000000000000000000 : ℝ) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (21913552991667093741750243/100000000000000000000000000 : ℝ) / ((((43/25 : ℝ) + (7/4 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1934614126240842119/20000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (43/25 : ℝ) (7/4 : ℝ), 2 * (4072351523799018519/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_24.2.2.1
    have hX : (15305693460573707327011147/30000000000000000000000000 : ℝ) ≤ (1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (15305693460573707327011147/30000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((7/4 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (4072351523799018519/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (15305693460573707327011147/30000000000000000000000000 : ℝ) / ((7/4 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (4072351523799018519/100000000000000000000 : ℝ) ≤ ((1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) / ((7/4 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (4072351523799018519/100000000000000000000 : ℝ) ≤ (15305693460573707327011147/30000000000000000000000000 : ℝ) / ((7/4 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (15305693460573707327011147/30000000000000000000000000 : ℝ) / ((7/4 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) / ((7/4 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) / ((7/4 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) / ((7/4 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((7/4 : ℝ) + 2) * ((7/4 : ℝ) + 1) - log (((7/4 : ℝ) + 2) / 3)) / ((7/4 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (43/25 : ℝ)) (b := (7/4 : ℝ)) (C := (4072351523799018519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (7/4 : ℝ) - (43/25 : ℝ) ≤ (((43/25 : ℝ) + (7/4 : ℝ)) / 2) * log ((7/4 : ℝ) / (43/25 : ℝ)) := by
    have hl := b9_lgs_24.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (43/25 : ℝ)) (b := (7/4 : ℝ)) (m := (((43/25 : ℝ) + (7/4 : ℝ)) / 2)) (A := (2037728806498137943/50000000000000000000 : ℝ)) (B := (1934614126240842119/20000000000000000000 : ℝ)) (C := (4072351523799018519/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_24.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 25 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_25 :
    ((4068162539897192487300333/4000000000000000000000000 : ℝ) ≤ log ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) ∧ log ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) ≤ (101704063497429812182508327/100000000000000000000000000 : ℝ)) ∧
    ((1135677862918736043826851/5000000000000000000000000 : ℝ) ≤ log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) ≤ (22713557258374720876537021/100000000000000000000000000 : ℝ)) ∧
    (log (((89/50 : ℝ) + 2) / 3) ≤ (23111172096338662927709243/100000000000000000000000000 : ℝ)) ∧
    ((13598061094856874742541/800000000000000000000000 : ℝ) ≤ log ((89/50 : ℝ) / (7/4 : ℝ)) ∧ log ((89/50 : ℝ) / (7/4 : ℝ)) ≤ (849878818428554671408813/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) = (553/200 : ℝ) by norm_num]
    have hkey : log (553/200 : ℝ) = log (2 : ℝ) + log (553/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (553/400 : ℝ)) (x := (153/953 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (161946727207176406203925564271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (153/953 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) = (553/200 : ℝ) by norm_num]
    have hkey : log (553/200 : ℝ) = log (2 : ℝ) + log (553/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (553/400 : ℝ)) (x := (153/953 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (153/953 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((153/953 : ℝ) ^ (2 * 19 + 1) / (1 - (153/953 : ℝ) ^ 2)) ≤ (323893454414352812407851148541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) = (251/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (251/200 : ℝ)) (x := (51/451 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).1
    have hnum : (1135677862918736043826851/5000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 16, (51/451 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) = (251/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (251/200 : ℝ)) (x := (51/451 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (51/451 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((51/451 : ℝ) ^ (2 * 16 + 1) / (1 - (51/451 : ℝ) ^ 2)) ≤ (22713557258374720876537021/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((89/50 : ℝ) + 2) / 3) = (63/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (63/50 : ℝ)) (x := (13/113 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (13/113 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((13/113 : ℝ) ^ (2 * 16 + 1) / (1 - (13/113 : ℝ) ^ 2)) ≤ (23111172096338662927709243/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((89/50 : ℝ) / (7/4 : ℝ)) = (178/175 : ℝ) by norm_num]
    have h := (log_enclosure (y := (178/175 : ℝ)) (x := (3/353 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (13598061094856874742541/800000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/353 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((89/50 : ℝ) / (7/4 : ℝ)) = (178/175 : ℝ) by norm_num]
    have h := (log_enclosure (y := (178/175 : ℝ)) (x := (3/353 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/353 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/353 : ℝ) ^ (2 * 7 + 1) / (1 - (3/353 : ℝ) ^ 2)) ≤ (849878818428554671408813/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 25, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_25 : (546166924027553871/12500000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((7/4 : ℝ) + (89/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2)) (c := ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1)) (m := (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 27
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) - 1 = ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1)) (m := (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_25.1
  have hq := b9_lgs_25.2.1
  have hprod : (4068162539897192487300333/4000000000000000000000000 : ℝ) * (1135677862918736043826851/5000000000000000000000000 : ℝ) ≤ log ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) * log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((2425308017822655463584272545788210937710045641964453249426662250817198567133777961837835535161/1829397067639912309414268796751514435186052680592755756595451336230371318314347994485569184600 : ℝ) : ℝ) * log ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) ≤ ((2425308017822655463584272545788210937710045641964453249426662250817198567133777961837835535161/1829397067639912309414268796751514435186052680592755756595451336230371318314347994485569184600 : ℝ) : ℝ) * (101704063497429812182508327/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-6394776396213023188354948823788395071538643602443845126474229252976499152691945051140414634/5820808851581539166318127989663909566501076710976950134621890615278454194636561800635901951 : ℝ) : ℝ) * log 2 ≤ ((-6394776396213023188354948823788395071538643602443845126474229252976499152691945051140414634/5820808851581539166318127989663909566501076710976950134621890615278454194636561800635901951 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (965403202097073335084928790463561927589147132189405519740753189230156063956299553887919127546010355133857762475068845189491301546029394522800811/26674865502573344029774983321486407332816044214681776663261481538886831278982448122126130913462340000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) * log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) -
      ((2425308017822655463584272545788210937710045641964453249426662250817198567133777961837835535161/1829397067639912309414268796751514435186052680592755756595451336230371318314347994485569184600 : ℝ) * log ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) + (-6394776396213023188354948823788395071538643602443845126474229252976499152691945051140414634/5820808851581539166318127989663909566501076710976950134621890615278454194636561800635901951 : ℝ) * log 2 + (-51260570366931764668663472982378229129587780480015379481062893620681838576343992909024080933670877/130759144620457568773406780987678467317725706934714591486575889896504074896972784912382994673835000 : ℝ)) := by
    have e : (965403202097073335084928790463561927589147132189405519740753189230156063956299553887919127546010355133857762475068845189491301546029394522800811/26674865502573344029774983321486407332816044214681776663261481538886831278982448122126130913462340000000000000000000000000000000000000000000000000 : ℝ) = (4068162539897192487300333/4000000000000000000000000 : ℝ) * (1135677862918736043826851/5000000000000000000000000 : ℝ) - (((2425308017822655463584272545788210937710045641964453249426662250817198567133777961837835535161/1829397067639912309414268796751514435186052680592755756595451336230371318314347994485569184600 : ℝ) : ℝ) * (101704063497429812182508327/100000000000000000000000000 : ℝ) + ((-6394776396213023188354948823788395071538643602443845126474229252976499152691945051140414634/5820808851581539166318127989663909566501076710976950134621890615278454194636561800635901951 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-51260570366931764668663472982378229129587780480015379481062893620681838576343992909024080933670877/130759144620457568773406780987678467317725706934714591486575889896504074896972784912382994673835000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (965403202097073335084928790463561927589147132189405519740753189230156063956299553887919127546010355133857762475068845189491301546029394522800811/26674865502573344029774983321486407332816044214681776663261481538886831278982448122126130913462340000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (546166924027553871/12500000000000000000 : ℝ) ≤ (965403202097073335084928790463561927589147132189405519740753189230156063956299553887919127546010355133857762475068845189491301546029394522800811/26674865502573344029774983321486407332816044214681776663261481538886831278982448122126130913462340000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (965403202097073335084928790463561927589147132189405519740753189230156063956299553887919127546010355133857762475068845189491301546029394522800811/26674865502573344029774983321486407332816044214681776663261481538886831278982448122126130913462340000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 25 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[7/4, 89/50]`. -/
private theorem b9_pan_25 : (23208115825716357913/62500000000000000000000 : ℝ) ≤ ∫ t in (7/4 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (546166924027553871/12500000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((7/4 : ℝ) + (89/50 : ℝ)) / 2) := b9_sig_25
  have hB0 : ((log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1239678087520232513/12500000000000000000 : ℝ) := by
    have hp := b9_lgs_25.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) ≤ (22713557258374720876537021/100000000000000000000000000 : ℝ) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 2) / 3) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (22713557258374720876537021/100000000000000000000000000 : ℝ) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (22713557258374720876537021/100000000000000000000000000 : ℝ) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (22713557258374720876537021/100000000000000000000000000 : ℝ) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (22713557258374720876537021/100000000000000000000000000 : ℝ) / ((((7/4 : ℝ) + (89/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1239678087520232513/12500000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (7/4 : ℝ) (89/50 : ℝ), 2 * (157569078141412271/4000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_25.2.2.1
    have hX : (9531988473791992706662953073/18900000000000000000000000000 : ℝ) ≤ (1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9531988473791992706662953073/18900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((89/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (157569078141412271/4000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9531988473791992706662953073/18900000000000000000000000000 : ℝ) / ((89/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (157569078141412271/4000000000000000000 : ℝ) ≤ ((1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) / ((89/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (157569078141412271/4000000000000000000 : ℝ) ≤ (9531988473791992706662953073/18900000000000000000000000000 : ℝ) / ((89/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9531988473791992706662953073/18900000000000000000000000000 : ℝ) / ((89/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) / ((89/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) / ((89/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) / ((89/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((89/50 : ℝ) + 2) * ((89/50 : ℝ) + 1) - log (((89/50 : ℝ) + 2) / 3)) / ((89/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (7/4 : ℝ)) (b := (89/50 : ℝ)) (C := (157569078141412271/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (89/50 : ℝ) - (7/4 : ℝ) ≤ (((7/4 : ℝ) + (89/50 : ℝ)) / 2) * log ((89/50 : ℝ) / (7/4 : ℝ)) := by
    have hl := b9_lgs_25.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (7/4 : ℝ)) (b := (89/50 : ℝ)) (m := (((7/4 : ℝ) + (89/50 : ℝ)) / 2)) (A := (546166924027553871/12500000000000000000 : ℝ)) (B := (1239678087520232513/12500000000000000000 : ℝ)) (C := (157569078141412271/4000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_25.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 26 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_26 :
    ((25695802665176562051827873/25000000000000000000000000 : ℝ) ≤ log ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) ∧ log ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) ≤ (51391605330353124103655747/50000000000000000000000000 : ℝ)) ∧
    ((23507212217948355741548137/100000000000000000000000000 : ℝ) ≤ log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) ≤ (11753606108974177870774069/50000000000000000000000000 : ℝ)) ∧
    (log (((181/100 : ℝ) + 2) / 3) ≤ (2390169004704999050114579/10000000000000000000000000 : ℝ)) ∧
    ((1671348097374059910403937/100000000000000000000000000 : ℝ) ≤ log ((181/100 : ℝ) / (89/50 : ℝ)) ∧ log ((181/100 : ℝ) / (89/50 : ℝ)) ≤ (835674048687029955201969/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) = (559/200 : ℝ) by norm_num]
    have hkey : log (559/200 : ℝ) = log (2 : ℝ) + log (559/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (559/400 : ℝ)) (x := (159/959 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (167342463023558586327941399271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (159/959 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) = (559/200 : ℝ) by norm_num]
    have hkey : log (559/200 : ℝ) = log (2 : ℝ) + log (559/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (559/400 : ℝ)) (x := (159/959 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (159/959 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((159/959 : ℝ) ^ (2 * 19 + 1) / (1 - (159/959 : ℝ) ^ 2)) ≤ (334684926047117172655882818541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) = (253/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (253/200 : ℝ)) (x := (53/453 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).1
    have hnum : (23507212217948355741548137/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 16, (53/453 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) = (253/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (253/200 : ℝ)) (x := (53/453 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (53/453 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((53/453 : ℝ) ^ (2 * 16 + 1) / (1 - (53/453 : ℝ) ^ 2)) ≤ (11753606108974177870774069/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((181/100 : ℝ) + 2) / 3) = (127/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (127/100 : ℝ)) (x := (27/227 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16).2
    have hnum : 2 * (∑ i ∈ Finset.range 16, (27/227 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((27/227 : ℝ) ^ (2 * 16 + 1) / (1 - (27/227 : ℝ) ^ 2)) ≤ (2390169004704999050114579/10000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((181/100 : ℝ) / (89/50 : ℝ)) = (181/178 : ℝ) by norm_num]
    have h := (log_enclosure (y := (181/178 : ℝ)) (x := (3/359 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1671348097374059910403937/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/359 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((181/100 : ℝ) / (89/50 : ℝ)) = (181/178 : ℝ) by norm_num]
    have h := (log_enclosure (y := (181/178 : ℝ)) (x := (3/359 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/359 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/359 : ℝ) ^ (2 * 7 + 1) / (1 - (3/359 : ℝ) ^ 2)) ≤ (835674048687029955201969/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 26, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_26 : (934084642378317093/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((89/50 : ℝ) + (181/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2)) (c := ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1)) (m := (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 28
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) - 1 = ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1)) (m := (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_26.1
  have hq := b9_lgs_26.2.1
  have hprod : (25695802665176562051827873/25000000000000000000000000 : ℝ) * (23507212217948355741548137/100000000000000000000000000 : ℝ) ≤ log ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) * log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((2459057894078621959450041222393855495951636811208126258917969126900843038327229058825603080428911/1843814060214020835010931866474269514345998556476496529967608947308415179820262929107214690675800 : ℝ) : ℝ) * log ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) ≤ ((2459057894078621959450041222393855495951636811208126258917969126900843038327229058825603080428911/1843814060214020835010931866474269514345998556476496529967608947308415179820262929107214690675800 : ℝ) : ℝ) * (51391605330353124103655747/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-131665859652583230056674443962645914346730073023788416802820576386396029999650418327373839582618/119847913913911354275710571320827518432489906170972274447894581575046986688317090391968954893927 : ℝ) : ℝ) * log 2 ≤ ((-131665859652583230056674443962645914346730073023788416802820576386396029999650418327373839582618/119847913913911354275710571320827518432489906170972274447894581575046986688317090391968954893927 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (86195039621911765148263404123451778293691606200746675265919557820296208558696821122845048841114226458228089504101162347153866394293228862238405865102483/2228101256547284745912920220441925155173506201142742949750705638418862720429037930466148258182226666707500000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) * log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) -
      ((2459057894078621959450041222393855495951636811208126258917969126900843038327229058825603080428911/1843814060214020835010931866474269514345998556476496529967608947308415179820262929107214690675800 : ℝ) * log ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) + (-131665859652583230056674443962645914346730073023788416802820576386396029999650418327373839582618/119847913913911354275710571320827518432489906170972274447894581575046986688317090391968954893927 : ℝ) * log 2 + (-603626663570925279761976039564776854832011841707578889972227668256840917538595541711620017412573503154541/1485400837698189830608613480294616770115670800761828633167137092279241813619358620310765505454817777805000 : ℝ)) := by
    have e : (86195039621911765148263404123451778293691606200746675265919557820296208558696821122845048841114226458228089504101162347153866394293228862238405865102483/2228101256547284745912920220441925155173506201142742949750705638418862720429037930466148258182226666707500000000000000000000000000000000000000000000000000 : ℝ) = (25695802665176562051827873/25000000000000000000000000 : ℝ) * (23507212217948355741548137/100000000000000000000000000 : ℝ) - (((2459057894078621959450041222393855495951636811208126258917969126900843038327229058825603080428911/1843814060214020835010931866474269514345998556476496529967608947308415179820262929107214690675800 : ℝ) : ℝ) * (51391605330353124103655747/50000000000000000000000000 : ℝ) + ((-131665859652583230056674443962645914346730073023788416802820576386396029999650418327373839582618/119847913913911354275710571320827518432489906170972274447894581575046986688317090391968954893927 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-603626663570925279761976039564776854832011841707578889972227668256840917538595541711620017412573503154541/1485400837698189830608613480294616770115670800761828633167137092279241813619358620310765505454817777805000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (86195039621911765148263404123451778293691606200746675265919557820296208558696821122845048841114226458228089504101162347153866394293228862238405865102483/2228101256547284745912920220441925155173506201142742949750705638418862720429037930466148258182226666707500000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (934084642378317093/20000000000000000000 : ℝ) ≤ (86195039621911765148263404123451778293691606200746675265919557820296208558696821122845048841114226458228089504101162347153866394293228862238405865102483/2228101256547284745912920220441925155173506201142742949750705638418862720429037930466148258182226666707500000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (86195039621911765148263404123451778293691606200746675265919557820296208558696821122845048841114226458228089504101162347153866394293228862238405865102483/2228101256547284745912920220441925155173506201142742949750705638418862720429037930466148258182226666707500000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 26 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[89/50, 181/100]`. -/
private theorem b9_pan_26 : (390283579512161981773/1000000000000000000000000 : ℝ) ≤ ∫ t in (89/50 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (934084642378317093/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((89/50 : ℝ) + (181/100 : ℝ)) / 2) := b9_sig_26
  have hB0 : ((log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2030758140136795513/20000000000000000000 : ℝ) := by
    have hp := b9_lgs_26.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) ≤ (11753606108974177870774069/50000000000000000000000000 : ℝ) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 2) / 3) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (11753606108974177870774069/50000000000000000000000000 : ℝ) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (11753606108974177870774069/50000000000000000000000000 : ℝ) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (11753606108974177870774069/50000000000000000000000000 : ℝ) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (11753606108974177870774069/50000000000000000000000000 : ℝ) / ((((89/50 : ℝ) + (181/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2030758140136795513/20000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (89/50 : ℝ) (181/100 : ℝ), 2 * (1905527743784238791/50000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_26.2.2.1
    have hX : (1899345609207395361906345401/3810000000000000000000000000 : ℝ) ≤ (1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (1899345609207395361906345401/3810000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((181/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (1905527743784238791/50000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (1899345609207395361906345401/3810000000000000000000000000 : ℝ) / ((181/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (1905527743784238791/50000000000000000000 : ℝ) ≤ ((1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) / ((181/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (1905527743784238791/50000000000000000000 : ℝ) ≤ (1899345609207395361906345401/3810000000000000000000000000 : ℝ) / ((181/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (1899345609207395361906345401/3810000000000000000000000000 : ℝ) / ((181/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) / ((181/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) / ((181/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) / ((181/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((181/100 : ℝ) + 2) * ((181/100 : ℝ) + 1) - log (((181/100 : ℝ) + 2) / 3)) / ((181/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (89/50 : ℝ)) (b := (181/100 : ℝ)) (C := (1905527743784238791/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (181/100 : ℝ) - (89/50 : ℝ) ≤ (((89/50 : ℝ) + (181/100 : ℝ)) / 2) * log ((181/100 : ℝ) / (89/50 : ℝ)) := by
    have hl := b9_lgs_26.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (89/50 : ℝ)) (b := (181/100 : ℝ)) (m := (((89/50 : ℝ) + (181/100 : ℝ)) / 2)) (A := (934084642378317093/20000000000000000000 : ℝ)) (B := (2030758140136795513/20000000000000000000 : ℝ)) (C := (1905527743784238791/50000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_26.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 27 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_27 :
    ((103850836459840426572967579/100000000000000000000000000 : ℝ) ≤ log ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) ∧ log ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) ≤ (103850836459840426572967581/100000000000000000000000000 : ℝ)) ∧
    ((4858923572207789375846483/20000000000000000000000000 : ℝ) ≤ log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) ≤ (759206808157467089976013/3125000000000000000000000 : ℝ)) ∧
    (log (((46/25 : ℝ) + 2) / 3) ≤ (4937201558630515957692839/20000000000000000000000000 : ℝ)) ∧
    ((328774526863197444387243/20000000000000000000000000 : ℝ) ≤ log ((46/25 : ℝ) / (181/100 : ℝ)) ∧ log ((46/25 : ℝ) / (181/100 : ℝ)) ≤ (205484079289498402742027/12500000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) = (113/40 : ℝ) by norm_num]
    have hkey : log (113/40 : ℝ) = log (2 : ℝ) + log (113/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (113/80 : ℝ)) (x := (33/193 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20).1
    have hnum : (172680592019229478156221834271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 20, (33/193 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) = (113/40 : ℝ) by norm_num]
    have hkey : log (113/40 : ℝ) = log (2 : ℝ) + log (113/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (113/80 : ℝ)) (x := (33/193 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20).2
    have hnum : 2 * (∑ i ∈ Finset.range 20, (33/193 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((33/193 : ℝ) ^ (2 * 20 + 1) / (1 - (33/193 : ℝ) ^ 2)) ≤ (345361184038458956312443688541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) = (51/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (51/40 : ℝ)) (x := (11/91 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (4858923572207789375846483/20000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (11/91 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) = (51/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (51/40 : ℝ)) (x := (11/91 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (11/91 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((11/91 : ℝ) ^ (2 * 17 + 1) / (1 - (11/91 : ℝ) ^ 2)) ≤ (759206808157467089976013/3125000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((46/25 : ℝ) + 2) / 3) = (32/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (32/25 : ℝ)) (x := (7/57 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (7/57 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((7/57 : ℝ) ^ (2 * 17 + 1) / (1 - (7/57 : ℝ) ^ 2)) ≤ (4937201558630515957692839/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((46/25 : ℝ) / (181/100 : ℝ)) = (184/181 : ℝ) by norm_num]
    have h := (log_enclosure (y := (184/181 : ℝ)) (x := (3/365 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (328774526863197444387243/20000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/365 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((46/25 : ℝ) / (181/100 : ℝ)) = (184/181 : ℝ) by norm_num]
    have h := (log_enclosure (y := (184/181 : ℝ)) (x := (3/365 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/365 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/365 : ℝ) ^ (2 * 7 + 1) / (1 - (3/365 : ℝ) ^ 2)) ≤ (205484079289498402742027/12500000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 27, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_27 : (248924296145176059/5000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((181/100 : ℝ) + (46/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2)) (c := ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1)) (m := (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 28
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) - 1 = ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1)) (m := (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_27.1
  have hq := b9_lgs_27.2.1
  have hprod : (103850836459840426572967579/100000000000000000000000000 : ℝ) * (4858923572207789375846483/20000000000000000000000000 : ℝ) ≤ log ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) * log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((225349080764452566349158312250701593207259364088782675471081619486536580632927/167976181995349368685586342924896637495223112982538164725756805305310462171400 : ℝ) : ℝ) * log ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) ≤ ((225349080764452566349158312250701593207259364088782675471081619486536580632927/167976181995349368685586342924896637495223112982538164725756805305310462171400 : ℝ) : ℝ) * (103850836459840426572967581/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-922699546255595654771890795941211676362928717914360832205245527251336962438/839880909976746843427931714624483187476115564912690823628784026526552310857 : ℝ) : ℝ) * log 2 ≤ ((-922699546255595654771890795941211676362928717914360832205245527251336962438/839880909976746843427931714624483187476115564912690823628784026526552310857 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (46828241983416876228793729364652994784042064050168423930446745667745411262650200580795842144646441153015488131102757518660765814911/1135584500999539918568351056846041979156331380776021183430359049017967795358910846000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) * log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) -
      ((225349080764452566349158312250701593207259364088782675471081619486536580632927/167976181995349368685586342924896637495223112982538164725756805305310462171400 : ℝ) * log ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) + (-922699546255595654771890795941211676362928717914360832205245527251336962438/839880909976746843427931714624483187476115564912690823628784026526552310857 : ℝ) * log 2 + (-36188458149797254998522030204275134239927703160988789146873526443069614276489405961/86029128863601508982450837639851665087600862180001604805330230986209681466584155000 : ℝ)) := by
    have e : (46828241983416876228793729364652994784042064050168423930446745667745411262650200580795842144646441153015488131102757518660765814911/1135584500999539918568351056846041979156331380776021183430359049017967795358910846000000000000000000000000000000000000000000000000000 : ℝ) = (103850836459840426572967579/100000000000000000000000000 : ℝ) * (4858923572207789375846483/20000000000000000000000000 : ℝ) - (((225349080764452566349158312250701593207259364088782675471081619486536580632927/167976181995349368685586342924896637495223112982538164725756805305310462171400 : ℝ) : ℝ) * (103850836459840426572967581/100000000000000000000000000 : ℝ) + ((-922699546255595654771890795941211676362928717914360832205245527251336962438/839880909976746843427931714624483187476115564912690823628784026526552310857 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-36188458149797254998522030204275134239927703160988789146873526443069614276489405961/86029128863601508982450837639851665087600862180001604805330230986209681466584155000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (46828241983416876228793729364652994784042064050168423930446745667745411262650200580795842144646441153015488131102757518660765814911/1135584500999539918568351056846041979156331380776021183430359049017967795358910846000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (248924296145176059/5000000000000000000 : ℝ) ≤ (46828241983416876228793729364652994784042064050168423930446745667745411262650200580795842144646441153015488131102757518660765814911/1135584500999539918568351056846041979156331380776021183430359049017967795358910846000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (46828241983416876228793729364652994784042064050168423930446745667745411262650200580795842144646441153015488131102757518660765814911/1135584500999539918568351056846041979156331380776021183430359049017967795358910846000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 27 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[181/100, 46/25]`. -/
private theorem b9_pan_27 : (409187500490729130113/1000000000000000000000000 : ℝ) ≤ ∫ t in (181/100 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (248924296145176059/5000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((181/100 : ℝ) + (46/25 : ℝ)) / 2) := b9_sig_27
  have hB0 : ((log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (5191232925786752707/50000000000000000000 : ℝ) := by
    have hp := b9_lgs_27.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) ≤ (759206808157467089976013/3125000000000000000000000 : ℝ) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 2) / 3) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (759206808157467089976013/3125000000000000000000000 : ℝ) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (759206808157467089976013/3125000000000000000000000 : ℝ) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (759206808157467089976013/3125000000000000000000000 : ℝ) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (759206808157467089976013/3125000000000000000000000 : ℝ) / ((((181/100 : ℝ) + (46/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (5191232925786752707/50000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (181/100 : ℝ) (46/25 : ℝ), 2 * (3687612434266718853/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_27.2.2.1
    have hX : (29563395324108452126921483/60000000000000000000000000 : ℝ) ≤ (1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (29563395324108452126921483/60000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((46/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3687612434266718853/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (29563395324108452126921483/60000000000000000000000000 : ℝ) / ((46/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3687612434266718853/100000000000000000000 : ℝ) ≤ ((1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) / ((46/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3687612434266718853/100000000000000000000 : ℝ) ≤ (29563395324108452126921483/60000000000000000000000000 : ℝ) / ((46/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (29563395324108452126921483/60000000000000000000000000 : ℝ) / ((46/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) / ((46/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) / ((46/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) / ((46/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((46/25 : ℝ) + 2) * ((46/25 : ℝ) + 1) - log (((46/25 : ℝ) + 2) / 3)) / ((46/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (181/100 : ℝ)) (b := (46/25 : ℝ)) (C := (3687612434266718853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (46/25 : ℝ) - (181/100 : ℝ) ≤ (((181/100 : ℝ) + (46/25 : ℝ)) / 2) * log ((46/25 : ℝ) / (181/100 : ℝ)) := by
    have hl := b9_lgs_27.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (181/100 : ℝ)) (b := (46/25 : ℝ)) (m := (((181/100 : ℝ) + (46/25 : ℝ)) / 2)) (A := (248924296145176059/5000000000000000000 : ℝ)) (B := (5191232925786752707/50000000000000000000 : ℝ)) (C := (3687612434266718853/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_27.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 28 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_28 :
    ((26226796077699338481918779/25000000000000000000000000 : ℝ) ≤ log ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) ∧ log ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) ≤ (52453592155398676963837559/50000000000000000000000000 : ℝ)) ∧
    ((3134483979339789011232241/12500000000000000000000000 : ℝ) ≤ log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) ≤ (25075871834718312089857929/100000000000000000000000000 : ℝ)) ∧
    (log (((187/100 : ℝ) + 2) / 3) ≤ (5092844367471614936642097/20000000000000000000000000 : ℝ)) ∧
    ((1617285924560100525302899/100000000000000000000000000 : ℝ) ≤ log ((187/100 : ℝ) / (46/25 : ℝ)) ∧ log ((187/100 : ℝ) / (46/25 : ℝ)) ≤ (16172859245601005253029/1000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) = (571/200 : ℝ) by norm_num]
    have hkey : log (571/200 : ℝ) = log (2 : ℝ) + log (571/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (571/400 : ℝ)) (x := (171/971 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20).1
    have hnum : (177962331274014114929759519271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 20, (171/971 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) = (571/200 : ℝ) by norm_num]
    have hkey : log (571/200 : ℝ) = log (2 : ℝ) + log (571/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (571/400 : ℝ)) (x := (171/971 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20).2
    have hnum : 2 * (∑ i ∈ Finset.range 20, (171/971 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((171/971 : ℝ) ^ (2 * 20 + 1) / (1 - (171/971 : ℝ) ^ 2)) ≤ (355924662548028229859519058541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) = (257/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (257/200 : ℝ)) (x := (57/457 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (3134483979339789011232241/12500000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (57/457 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) = (257/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (257/200 : ℝ)) (x := (57/457 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (57/457 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((57/457 : ℝ) ^ (2 * 17 + 1) / (1 - (57/457 : ℝ) ^ 2)) ≤ (25075871834718312089857929/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((187/100 : ℝ) + 2) / 3) = (129/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (129/100 : ℝ)) (x := (29/229 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (29/229 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((29/229 : ℝ) ^ (2 * 17 + 1) / (1 - (29/229 : ℝ) ^ 2)) ≤ (5092844367471614936642097/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((187/100 : ℝ) / (46/25 : ℝ)) = (187/184 : ℝ) by norm_num]
    have h := (log_enclosure (y := (187/184 : ℝ)) (x := (3/371 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1617285924560100525302899/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/371 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((187/100 : ℝ) / (46/25 : ℝ)) = (187/184 : ℝ) by norm_num]
    have h := (log_enclosure (y := (187/184 : ℝ)) (x := (3/371 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/371 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/371 : ℝ) ^ (2 * 7 + 1) / (1 - (3/371 : ℝ) ^ 2)) ≤ (16172859245601005253029/1000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 28, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_28 : (5293297088570930083/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((46/25 : ℝ) + (187/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2)) (c := ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1)) (m := (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 29
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) - 1 = ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1)) (m := (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_28.1
  have hq := b9_lgs_28.2.1
  have hprod : (26226796077699338481918779/25000000000000000000000000 : ℝ) * (3134483979339789011232241/12500000000000000000000000 : ℝ) ≤ log ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) * log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((149533144304699840616730322045464881771730130083121088619875488008739106382743628093987997520939913379/110817203861458725349275936809268053734512641754316731890879429567215853042369768081415449137857096600 : ℝ) : ℝ) * log ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) ≤ ((149533144304699840616730322045464881771730130083121088619875488008739106382743628093987997520939913379/110817203861458725349275936809268053734512641754316731890879429567215853042369768081415449137857096600 : ℝ) : ℝ) * (52453592155398676963837559/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-6695962036147006609379604970035746736555614486925635313738380922142694988398662548505594393366653542/6094946212380229894210176524509742955398195296487420253998368626196871917330337244477849702582140313 : ℝ) : ℝ) * log 2 ≤ ((-6695962036147006609379604970035746736555614486925635313738380922142694988398662548505594393366653542/6094946212380229894210176524509742955398195296487420253998368626196871917330337244477849702582140313 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (947864188596543328030066089540389056313177764912255085102209018875165251023334947051062902279520565289704069958288434273507501932861177057568320381348174073/21618658030400501936631137750946059795822311438543040349483621673218367812899782096609210036048896218161283437500000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) * log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) -
      ((149533144304699840616730322045464881771730130083121088619875488008739106382743628093987997520939913379/110817203861458725349275936809268053734512641754316731890879429567215853042369768081415449137857096600 : ℝ) * log ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) + (-6695962036147006609379604970035746736555614486925635313738380922142694988398662548505594393366653542/6094946212380229894210176524509742955398195296487420253998368626196871917330337244477849702582140313 : ℝ) * log 2 + (-879647717762670676150113360737761222393705531395031389605322810559360354925484348105350928996389539216363177/2022798412201216555474258503012496823000918029337360500536479220885929152084190137694429009220949353746085000 : ℝ)) := by
    have e : (947864188596543328030066089540389056313177764912255085102209018875165251023334947051062902279520565289704069958288434273507501932861177057568320381348174073/21618658030400501936631137750946059795822311438543040349483621673218367812899782096609210036048896218161283437500000000000000000000000000000000000000000000000 : ℝ) = (26226796077699338481918779/25000000000000000000000000 : ℝ) * (3134483979339789011232241/12500000000000000000000000 : ℝ) - (((149533144304699840616730322045464881771730130083121088619875488008739106382743628093987997520939913379/110817203861458725349275936809268053734512641754316731890879429567215853042369768081415449137857096600 : ℝ) : ℝ) * (52453592155398676963837559/50000000000000000000000000 : ℝ) + ((-6695962036147006609379604970035746736555614486925635313738380922142694988398662548505594393366653542/6094946212380229894210176524509742955398195296487420253998368626196871917330337244477849702582140313 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-879647717762670676150113360737761222393705531395031389605322810559360354925484348105350928996389539216363177/2022798412201216555474258503012496823000918029337360500536479220885929152084190137694429009220949353746085000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (947864188596543328030066089540389056313177764912255085102209018875165251023334947051062902279520565289704069958288434273507501932861177057568320381348174073/21618658030400501936631137750946059795822311438543040349483621673218367812899782096609210036048896218161283437500000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (5293297088570930083/100000000000000000000 : ℝ) ≤ (947864188596543328030066089540389056313177764912255085102209018875165251023334947051062902279520565289704069958288434273507501932861177057568320381348174073/21618658030400501936631137750946059795822311438543040349483621673218367812899782096609210036048896218161283437500000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (947864188596543328030066089540389056313177764912255085102209018875165251023334947051062902279520565289704069958288434273507501932861177057568320381348174073/21618658030400501936631137750946059795822311438543040349483621673218367812899782096609210036048896218161283437500000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 28 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[46/25, 187/100]`. -/
private theorem b9_pan_28 : (428025718673053520581/1000000000000000000000000 : ℝ) ≤ ∫ t in (46/25 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (5293297088570930083/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((46/25 : ℝ) + (187/100 : ℝ)) / 2) := b9_sig_28
  have hB0 : ((log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2650933472013571331/25000000000000000000 : ℝ) := by
    have hp := b9_lgs_28.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) ≤ (25075871834718312089857929/100000000000000000000000000 : ℝ) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 2) / 3) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (25075871834718312089857929/100000000000000000000000000 : ℝ) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (25075871834718312089857929/100000000000000000000000000 : ℝ) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (25075871834718312089857929/100000000000000000000000000 : ℝ) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (25075871834718312089857929/100000000000000000000000000 : ℝ) / ((((46/25 : ℝ) + (187/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2650933472013571331/25000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (46/25 : ℝ) (187/100 : ℝ), 2 * (3568685290513896209/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_28.2.2.1
    have hX : (3769069229788485019519508461/7740000000000000000000000000 : ℝ) ≤ (1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (3769069229788485019519508461/7740000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((187/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3568685290513896209/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (3769069229788485019519508461/7740000000000000000000000000 : ℝ) / ((187/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3568685290513896209/100000000000000000000 : ℝ) ≤ ((1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) / ((187/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3568685290513896209/100000000000000000000 : ℝ) ≤ (3769069229788485019519508461/7740000000000000000000000000 : ℝ) / ((187/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (3769069229788485019519508461/7740000000000000000000000000 : ℝ) / ((187/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) / ((187/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) / ((187/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) / ((187/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((187/100 : ℝ) + 2) * ((187/100 : ℝ) + 1) - log (((187/100 : ℝ) + 2) / 3)) / ((187/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (46/25 : ℝ)) (b := (187/100 : ℝ)) (C := (3568685290513896209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (187/100 : ℝ) - (46/25 : ℝ) ≤ (((46/25 : ℝ) + (187/100 : ℝ)) / 2) * log ((187/100 : ℝ) / (46/25 : ℝ)) := by
    have hl := b9_lgs_28.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (46/25 : ℝ)) (b := (187/100 : ℝ)) (m := (((46/25 : ℝ) + (187/100 : ℝ)) / 2)) (A := (5293297088570930083/100000000000000000000 : ℝ)) (B := (2650933472013571331/25000000000000000000 : ℝ)) (C := (3568685290513896209/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_28.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 29 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_29 :
    ((105952489996006288402336027/100000000000000000000000000 : ℝ) ≤ log ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) ∧ log ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) ≤ (105952489996006288402336029/100000000000000000000000000 : ℝ)) ∧
    ((12925534757575053601011669/50000000000000000000000000 : ℝ) ≤ log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) ∧ log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) ≤ (25851069515150107202023339/100000000000000000000000000 : ℝ)) ∧
    (log (((19/10 : ℝ) + 2) / 3) ≤ (26236426446749105203549599/100000000000000000000000000 : ℝ)) ∧
    ((1591545530589951971554069/100000000000000000000000000 : ℝ) ≤ log ((19/10 : ℝ) / (187/100 : ℝ)) ∧ log ((19/10 : ℝ) / (187/100 : ℝ)) ≤ (159154553058995197155407/10000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) = (577/200 : ℝ) by norm_num]
    have hkey : log (577/200 : ℝ) = log (2 : ℝ) + log (577/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (577/400 : ℝ)) (x := (177/977 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20).1
    have hnum : (183188859700058787303064074271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 20, (177/977 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) = (577/200 : ℝ) by norm_num]
    have hkey : log (577/200 : ℝ) = log (2 : ℝ) + log (577/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (577/400 : ℝ)) (x := (177/977 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20).2
    have hnum : 2 * (∑ i ∈ Finset.range 20, (177/977 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((177/977 : ℝ) ^ (2 * 20 + 1) / (1 - (177/977 : ℝ) ^ 2)) ≤ (366377719400117574606128168541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) = (259/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (259/200 : ℝ)) (x := (59/459 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (12925534757575053601011669/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (59/459 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) = (259/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (259/200 : ℝ)) (x := (59/459 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (59/459 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((59/459 : ℝ) ^ (2 * 17 + 1) / (1 - (59/459 : ℝ) ^ 2)) ≤ (25851069515150107202023339/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((19/10 : ℝ) + 2) / 3) = (13/10 : ℝ) by norm_num]
    have h := (log_enclosure (y := (13/10 : ℝ)) (x := (3/23 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (3/23 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/23 : ℝ) ^ (2 * 17 + 1) / (1 - (3/23 : ℝ) ^ 2)) ≤ (26236426446749105203549599/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((19/10 : ℝ) / (187/100 : ℝ)) = (190/187 : ℝ) by norm_num]
    have h := (log_enclosure (y := (190/187 : ℝ)) (x := (3/377 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1591545530589951971554069/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/377 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((19/10 : ℝ) / (187/100 : ℝ)) = (190/187 : ℝ) by norm_num]
    have h := (log_enclosure (y := (190/187 : ℝ)) (x := (3/377 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/377 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/377 : ℝ) ^ (2 * 7 + 1) / (1 - (3/377 : ℝ) ^ 2)) ≤ (159154553058995197155407/10000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 29, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_29 : (1122927718242846573/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((187/100 : ℝ) + (19/10 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2)) (c := ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1)) (m := (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 29
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) - 1 = ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1)) (m := (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_29.1
  have hq := b9_lgs_29.2.1
  have hprod : (105952489996006288402336027/100000000000000000000000000 : ℝ) * (12925534757575053601011669/50000000000000000000000000 : ℝ) ≤ log ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) * log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((7363356394428726401866254295512738931971154270947027220425949520505490248600134434028219068197787943/5425724914171940416137144929369657658294088652275845538748310837584496649021578459843650659705736040 : ℝ) : ℝ) * log ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) ≤ ((7363356394428726401866254295512738931971154270947027220425949520505490248600134434028219068197787943/5425724914171940416137144929369657658294088652275845538748310837584496649021578459843650659705736040 : ℝ) : ℝ) * (105952489996006288402336029/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-8765806581125469991776638209148232306211959144156479605929326813733482811090829218161112770641702/7979007226723441788436977837308320085726600959229184615806339467036024483855262440946545087802553 : ℝ) : ℝ) * log 2 ≤ ((-8765806581125469991776638209148232306211959144156479605929326813733482811090829218161112770641702/7979007226723441788436977837308320085726600959229184615806339467036024483855262440946545087802553 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (523238613208529715266488787780839501547235592090424251835113094914637784400863404748660567131069733494621440243504118978405891843321937411398555202172876691/11250889661878376271232650417010160999770166250848994222617195288415399847157882142809068439610010977613785000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) * log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) -
      ((7363356394428726401866254295512738931971154270947027220425949520505490248600134434028219068197787943/5425724914171940416137144929369657658294088652275845538748310837584496649021578459843650659705736040 : ℝ) * log ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) + (-8765806581125469991776638209148232306211959144156479605929326813733482811090829218161112770641702/7979007226723441788436977837308320085726600959229184615806339467036024483855262440946545087802553 : ℝ) * log 2 + (-1683928768090415156674813748497009741548851152341496277631699932326078796502328758234904552095376024500736589/3750296553959458757077550139003386999923388750282998074205731762805133282385960714269689479870003659204595000 : ℝ)) := by
    have e : (523238613208529715266488787780839501547235592090424251835113094914637784400863404748660567131069733494621440243504118978405891843321937411398555202172876691/11250889661878376271232650417010160999770166250848994222617195288415399847157882142809068439610010977613785000000000000000000000000000000000000000000000000000 : ℝ) = (105952489996006288402336027/100000000000000000000000000 : ℝ) * (12925534757575053601011669/50000000000000000000000000 : ℝ) - (((7363356394428726401866254295512738931971154270947027220425949520505490248600134434028219068197787943/5425724914171940416137144929369657658294088652275845538748310837584496649021578459843650659705736040 : ℝ) : ℝ) * (105952489996006288402336029/100000000000000000000000000 : ℝ) + ((-8765806581125469991776638209148232306211959144156479605929326813733482811090829218161112770641702/7979007226723441788436977837308320085726600959229184615806339467036024483855262440946545087802553 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-1683928768090415156674813748497009741548851152341496277631699932326078796502328758234904552095376024500736589/3750296553959458757077550139003386999923388750282998074205731762805133282385960714269689479870003659204595000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (523238613208529715266488787780839501547235592090424251835113094914637784400863404748660567131069733494621440243504118978405891843321937411398555202172876691/11250889661878376271232650417010160999770166250848994222617195288415399847157882142809068439610010977613785000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (1122927718242846573/20000000000000000000 : ℝ) ≤ (523238613208529715266488787780839501547235592090424251835113094914637784400863404748660567131069733494621440243504118978405891843321937411398555202172876691/11250889661878376271232650417010160999770166250848994222617195288415399847157882142809068439610010977613785000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (523238613208529715266488787780839501547235592090424251835113094914637784400863404748660567131069733494621440243504118978405891843321937411398555202172876691/11250889661878376271232650417010160999770166250848994222617195288415399847157882142809068439610010977613785000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 29 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[187/100, 19/10]`. -/
private theorem b9_pan_29 : (446784010908126278011/1000000000000000000000000 : ℝ) ≤ ∫ t in (187/100 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (1122927718242846573/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((187/100 : ℝ) + (19/10 : ℝ)) / 2) := b9_sig_29
  have hB0 : ((log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1352233224154278771/12500000000000000000 : ℝ) := by
    have hp := b9_lgs_29.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) ≤ (25851069515150107202023339/100000000000000000000000000 : ℝ) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 2) / 3) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (25851069515150107202023339/100000000000000000000000000 : ℝ) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (25851069515150107202023339/100000000000000000000000000 : ℝ) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (25851069515150107202023339/100000000000000000000000000 : ℝ) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (25851069515150107202023339/100000000000000000000000000 : ℝ) / ((((187/100 : ℝ) + (19/10 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1352233224154278771/12500000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (187/100 : ℝ) (19/10 : ℝ), 2 * (690814593966430061/20000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_29.2.2.1
    have hX : (1876779368576784897061565639/3900000000000000000000000000 : ℝ) ≤ (1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (1876779368576784897061565639/3900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((19/10 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (690814593966430061/20000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (1876779368576784897061565639/3900000000000000000000000000 : ℝ) / ((19/10 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (690814593966430061/20000000000000000000 : ℝ) ≤ ((1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) / ((19/10 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (690814593966430061/20000000000000000000 : ℝ) ≤ (1876779368576784897061565639/3900000000000000000000000000 : ℝ) / ((19/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (1876779368576784897061565639/3900000000000000000000000000 : ℝ) / ((19/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) / ((19/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) / ((19/10 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) / ((19/10 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((19/10 : ℝ) + 2) * ((19/10 : ℝ) + 1) - log (((19/10 : ℝ) + 2) / 3)) / ((19/10 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (187/100 : ℝ)) (b := (19/10 : ℝ)) (C := (690814593966430061/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (19/10 : ℝ) - (187/100 : ℝ) ≤ (((187/100 : ℝ) + (19/10 : ℝ)) / 2) * log ((19/10 : ℝ) / (187/100 : ℝ)) := by
    have hl := b9_lgs_29.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (187/100 : ℝ)) (b := (19/10 : ℝ)) (m := (((187/100 : ℝ) + (19/10 : ℝ)) / 2)) (A := (1122927718242846573/20000000000000000000 : ℝ)) (B := (1352233224154278771/12500000000000000000 : ℝ)) (C := (690814593966430061/20000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_29.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 30 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_30 :
    ((13373372747530696259414971/12500000000000000000000000 : ℝ) ≤ log ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) ∧ log ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) ≤ (10698698198024557007531977/10000000000000000000000000 : ℝ)) ∧
    ((26620304077465673252054747/100000000000000000000000000 : ℝ) ≤ log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) ≤ (6655076019366418313013687/25000000000000000000000000 : ℝ)) ∧
    (log (((193/100 : ℝ) + 2) / 3) ≤ (27002713721306017611344111/100000000000000000000000000 : ℝ)) ∧
    ((97913229652496298924451/6250000000000000000000000 : ℝ) ≤ log ((193/100 : ℝ) / (19/10 : ℝ)) ∧ log ((193/100 : ℝ) / (19/10 : ℝ)) ≤ (1566611674439940782791217/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) = (583/200 : ℝ) by norm_num]
    have hkey : log (583/200 : ℝ) = log (2 : ℝ) + log (583/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (583/400 : ℝ)) (x := (183/983 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21).1
    have hnum : (188361319621255195667982779271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 21, (183/983 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) = (583/200 : ℝ) by norm_num]
    have hkey : log (583/200 : ℝ) = log (2 : ℝ) + log (583/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (583/400 : ℝ)) (x := (183/983 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21).2
    have hnum : 2 * (∑ i ∈ Finset.range 21, (183/983 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((183/983 : ℝ) ^ (2 * 21 + 1) / (1 - (183/983 : ℝ) ^ 2)) ≤ (376722639242510391335965578541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) = (261/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (261/200 : ℝ)) (x := (61/461 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (26620304077465673252054747/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (61/461 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) = (261/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (261/200 : ℝ)) (x := (61/461 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (61/461 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((61/461 : ℝ) ^ (2 * 17 + 1) / (1 - (61/461 : ℝ) ^ 2)) ≤ (6655076019366418313013687/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((193/100 : ℝ) + 2) / 3) = (131/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (131/100 : ℝ)) (x := (31/231 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (31/231 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((31/231 : ℝ) ^ (2 * 17 + 1) / (1 - (31/231 : ℝ) ^ 2)) ≤ (27002713721306017611344111/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((193/100 : ℝ) / (19/10 : ℝ)) = (193/190 : ℝ) by norm_num]
    have h := (log_enclosure (y := (193/190 : ℝ)) (x := (3/383 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (97913229652496298924451/6250000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/383 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((193/100 : ℝ) / (19/10 : ℝ)) = (193/190 : ℝ) by norm_num]
    have h := (log_enclosure (y := (193/190 : ℝ)) (x := (3/383 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/383 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/383 : ℝ) ^ (2 * 7 + 1) / (1 - (3/383 : ℝ) ^ 2)) ≤ (1566611674439940782791217/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 30, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_30 : (1188460051996932479/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((19/10 : ℝ) + (193/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2)) (c := ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1)) (m := (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 29
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) - 1 = ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1)) (m := (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_30.1
  have hq := b9_lgs_30.2.1
  have hprod : (13373372747530696259414971/12500000000000000000000000 : ℝ) * (26620304077465673252054747/100000000000000000000000000 : ℝ) ≤ log ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) * log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((194731808560385823990118381723524483291186791576407639693144783779111010799467894944912767738053217243/142680368435627649734470787360948865325674614644825153814014619289661632077583425606663146030743175800 : ℝ) : ℝ) * log ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) ≤ ((194731808560385823990118381723524483291186791576407639693144783779111010799467894944912767738053217243/142680368435627649734470787360948865325674614644825153814014619289661632077583425606663146030743175800 : ℝ) : ℝ) * (10698698198024557007531977/10000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-8621242334318536522356673993424519794118249589048677479826495593600310850425838846682212873946236446/7847420263959520735395893304852187592912103805465383459770804060931389764267088408366473031690874669 : ℝ) : ℝ) * log 2 ≤ ((-8621242334318536522356673993424519794118249589048677479826495593600310850425838846682212873946236446/7847420263959520735395893304852187592912103805465383459770804060931389764267088408366473031690874669 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (104122614575077080194980330904953948879359364678137565023119442589914557504331797744739338326170469298009487004999678790268246253202199777086855296963840943773/2115433406445988512326476345175188509189726415636526182043047849361013327182086574475835247171167804116991286250000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) * log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) -
      ((194731808560385823990118381723524483291186791576407639693144783779111010799467894944912767738053217243/142680368435627649734470787360948865325674614644825153814014619289661632077583425606663146030743175800 : ℝ) * log ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) + (-8621242334318536522356673993424519794118249589048677479826495593600310850425838846682212873946236446/7847420263959520735395893304852187592912103805465383459770804060931389764267088408366473031690874669 : ℝ) * log 2 + (-1306184637734845381321484852656754250514685107676112109073859544450671303237367464027722208178156566325322977483/2820577875261318016435301793566918012252968554182034909390730465814684436242782099301113662894890405489321715000 : ℝ)) := by
    have e : (104122614575077080194980330904953948879359364678137565023119442589914557504331797744739338326170469298009487004999678790268246253202199777086855296963840943773/2115433406445988512326476345175188509189726415636526182043047849361013327182086574475835247171167804116991286250000000000000000000000000000000000000000000000000 : ℝ) = (13373372747530696259414971/12500000000000000000000000 : ℝ) * (26620304077465673252054747/100000000000000000000000000 : ℝ) - (((194731808560385823990118381723524483291186791576407639693144783779111010799467894944912767738053217243/142680368435627649734470787360948865325674614644825153814014619289661632077583425606663146030743175800 : ℝ) : ℝ) * (10698698198024557007531977/10000000000000000000000000 : ℝ) + ((-8621242334318536522356673993424519794118249589048677479826495593600310850425838846682212873946236446/7847420263959520735395893304852187592912103805465383459770804060931389764267088408366473031690874669 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-1306184637734845381321484852656754250514685107676112109073859544450671303237367464027722208178156566325322977483/2820577875261318016435301793566918012252968554182034909390730465814684436242782099301113662894890405489321715000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (104122614575077080194980330904953948879359364678137565023119442589914557504331797744739338326170469298009487004999678790268246253202199777086855296963840943773/2115433406445988512326476345175188509189726415636526182043047849361013327182086574475835247171167804116991286250000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (1188460051996932479/20000000000000000000 : ℝ) ≤ (104122614575077080194980330904953948879359364678137565023119442589914557504331797744739338326170469298009487004999678790268246253202199777086855296963840943773/2115433406445988512326476345175188509189726415636526182043047849361013327182086574475835247171167804116991286250000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (104122614575077080194980330904953948879359364678137565023119442589914557504331797744739338326170469298009487004999678790268246253202199777086855296963840943773/2115433406445988512326476345175188509189726415636526182043047849361013327182086574475835247171167804116991286250000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 30 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[19/10, 193/100]`. -/
private theorem b9_pan_30 : (465449668041049259029/1000000000000000000000000 : ℝ) ≤ ∫ t in (19/10 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (1188460051996932479/20000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((19/10 : ℝ) + (193/100 : ℝ)) / 2) := b9_sig_30
  have hB0 : ((log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2205024096648665081/20000000000000000000 : ℝ) := by
    have hp := b9_lgs_30.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) ≤ (6655076019366418313013687/25000000000000000000000000 : ℝ) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 2) / 3) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6655076019366418313013687/25000000000000000000000000 : ℝ) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (6655076019366418313013687/25000000000000000000000000 : ℝ) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6655076019366418313013687/25000000000000000000000000 : ℝ) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (6655076019366418313013687/25000000000000000000000000 : ℝ) / ((((19/10 : ℝ) + (193/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2205024096648665081/20000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (19/10 : ℝ) (193/100 : ℝ), 2 * (3343585086415527127/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_30.2.2.1
    have hX : (18687933507526735078741764377/39300000000000000000000000000 : ℝ) ≤ (1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (18687933507526735078741764377/39300000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((193/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3343585086415527127/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (18687933507526735078741764377/39300000000000000000000000000 : ℝ) / ((193/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3343585086415527127/100000000000000000000 : ℝ) ≤ ((1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) / ((193/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3343585086415527127/100000000000000000000 : ℝ) ≤ (18687933507526735078741764377/39300000000000000000000000000 : ℝ) / ((193/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (18687933507526735078741764377/39300000000000000000000000000 : ℝ) / ((193/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) / ((193/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) / ((193/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) / ((193/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((193/100 : ℝ) + 2) * ((193/100 : ℝ) + 1) - log (((193/100 : ℝ) + 2) / 3)) / ((193/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (19/10 : ℝ)) (b := (193/100 : ℝ)) (C := (3343585086415527127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (193/100 : ℝ) - (19/10 : ℝ) ≤ (((19/10 : ℝ) + (193/100 : ℝ)) / 2) * log ((193/100 : ℝ) / (19/10 : ℝ)) := by
    have hl := b9_lgs_30.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (19/10 : ℝ)) (b := (193/100 : ℝ)) (m := (((19/10 : ℝ) + (193/100 : ℝ)) / 2)) (A := (1188460051996932479/20000000000000000000 : ℝ)) (B := (2205024096648665081/20000000000000000000 : ℝ)) (C := (3343585086415527127/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_30.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 31 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_31 :
    ((13501360213794375356062209/12500000000000000000000000 : ℝ) ≤ log ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) ∧ log ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) ≤ (54005440855177501424248837/50000000000000000000000000 : ℝ)) ∧
    ((27383666562972787363271123/100000000000000000000000000 : ℝ) ≤ log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) ≤ (6845916640743196840817781/25000000000000000000000000 : ℝ)) ∧
    (log (((49/25 : ℝ) + 2) / 3) ≤ (5552634731965589725113403/20000000000000000000000000 : ℝ)) ∧
    ((1542447032563167719023867/100000000000000000000000000 : ℝ) ≤ log ((49/25 : ℝ) / (193/100 : ℝ)) ∧ log ((49/25 : ℝ) / (193/100 : ℝ)) ≤ (385611758140791929755967/25000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) = (589/200 : ℝ) by norm_num]
    have hkey : log (589/200 : ℝ) = log (2 : ℝ) + log (589/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (589/400 : ℝ)) (x := (189/989 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21).1
    have hnum : (193480818271802359533872299271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 21, (189/989 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) = (589/200 : ℝ) by norm_num]
    have hkey : log (589/200 : ℝ) = log (2 : ℝ) + log (589/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (589/400 : ℝ)) (x := (189/989 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21).2
    have hnum : 2 * (∑ i ∈ Finset.range 21, (189/989 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((189/989 : ℝ) ^ (2 * 21 + 1) / (1 - (189/989 : ℝ) ^ 2)) ≤ (386961636543604719067744618541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) = (263/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (263/200 : ℝ)) (x := (63/463 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).1
    have hnum : (27383666562972787363271123/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 17, (63/463 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) = (263/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (263/200 : ℝ)) (x := (63/463 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 17).2
    have hnum : 2 * (∑ i ∈ Finset.range 17, (63/463 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((63/463 : ℝ) ^ (2 * 17 + 1) / (1 - (63/463 : ℝ) ^ 2)) ≤ (6845916640743196840817781/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((49/25 : ℝ) + 2) / 3) = (33/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (33/25 : ℝ)) (x := (4/29 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (4/29 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((4/29 : ℝ) ^ (2 * 18 + 1) / (1 - (4/29 : ℝ) ^ 2)) ≤ (5552634731965589725113403/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((49/25 : ℝ) / (193/100 : ℝ)) = (196/193 : ℝ) by norm_num]
    have h := (log_enclosure (y := (196/193 : ℝ)) (x := (3/389 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1542447032563167719023867/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/389 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((49/25 : ℝ) / (193/100 : ℝ)) = (196/193 : ℝ) by norm_num]
    have h := (log_enclosure (y := (196/193 : ℝ)) (x := (3/389 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/389 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/389 : ℝ) ^ (2 * 7 + 1) / (1 - (3/389 : ℝ) ^ 2)) ≤ (385611758140791929755967/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 31, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_31 : (392254969911931923/6250000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((193/100 : ℝ) + (49/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2)) (c := ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1)) (m := (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 30
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) - 1 = ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1)) (m := (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_31.1
  have hq := b9_lgs_31.2.1
  have hprod : (13501360213794375356062209/12500000000000000000000000 : ℝ) * (27383666562972787363271123/100000000000000000000000000 : ℝ) ≤ log ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) * log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((25504965001350563897293773116508964892980244191477415921215549133151583043254303994597320532727952551689/18583581441322450118981622245081129170359045928625156731733553527984907106633500519646994006327934046200 : ℝ) : ℝ) * log ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) ≤ ((25504965001350563897293773116508964892980244191477415921215549133151583043254303994597320532727952551689/18583581441322450118981622245081129170359045928625156731733553527984907106633500519646994006327934046200 : ℝ) : ℝ) * (54005440855177501424248837/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-1939529407280031515448075632759340303633730516565115372962706842822982684903224309715757726235248622926/1765440236925632761303254113282707271184109363219389889514687585158566175130182549366464430601153734389 : ℝ) : ℝ) * log 2 ≤ ((-1939529407280031515448075632759340303633730516565115372962706842822982684903224309715757726235248622926/1765440236925632761303254113282707271184109363219389889514687585158566175130182549366464430601153734389 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (1178109679063470682180487037479667853192788503064715893544569025979652718787457033744981003750129927326737822517216786244652784651903716603330468651871070011483/22662414184141591843789422844592826008832552442063686057388139395367904880449873825992769277174780050725657711250000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) * log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) -
      ((25504965001350563897293773116508964892980244191477415921215549133151583043254303994597320532727952551689/18583581441322450118981622245081129170359045928625156731733553527984907106633500519646994006327934046200 : ℝ) * log ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) + (-1939529407280031515448075632759340303633730516565115372962706842822982684903224309715757726235248622926/1765440236925632761303254113282707271184109363219389889514687585158566175130182549366464430601153734389 : ℝ) * log 2 + (-4805488460432957542101138399713668848469312781919136006304191623444585094877128203829889755006202079732911802551/10072184081840707486128632375374589337258912196472749358839173064607957724644388367107897456522124466989181205000 : ℝ)) := by
    have e : (1178109679063470682180487037479667853192788503064715893544569025979652718787457033744981003750129927326737822517216786244652784651903716603330468651871070011483/22662414184141591843789422844592826008832552442063686057388139395367904880449873825992769277174780050725657711250000000000000000000000000000000000000000000000000 : ℝ) = (13501360213794375356062209/12500000000000000000000000 : ℝ) * (27383666562972787363271123/100000000000000000000000000 : ℝ) - (((25504965001350563897293773116508964892980244191477415921215549133151583043254303994597320532727952551689/18583581441322450118981622245081129170359045928625156731733553527984907106633500519646994006327934046200 : ℝ) : ℝ) * (54005440855177501424248837/50000000000000000000000000 : ℝ) + ((-1939529407280031515448075632759340303633730516565115372962706842822982684903224309715757726235248622926/1765440236925632761303254113282707271184109363219389889514687585158566175130182549366464430601153734389 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-4805488460432957542101138399713668848469312781919136006304191623444585094877128203829889755006202079732911802551/10072184081840707486128632375374589337258912196472749358839173064607957724644388367107897456522124466989181205000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (1178109679063470682180487037479667853192788503064715893544569025979652718787457033744981003750129927326737822517216786244652784651903716603330468651871070011483/22662414184141591843789422844592826008832552442063686057388139395367904880449873825992769277174780050725657711250000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (392254969911931923/6250000000000000000 : ℝ) ≤ (1178109679063470682180487037479667853192788503064715893544569025979652718787457033744981003750129927326737822517216786244652784651903716603330468651871070011483/22662414184141591843789422844592826008832552442063686057388139395367904880449873825992769277174780050725657711250000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (1178109679063470682180487037479667853192788503064715893544569025979652718787457033744981003750129927326737822517216786244652784651903716603330468651871070011483/22662414184141591843789422844592826008832552442063686057388139395367904880449873825992769277174780050725657711250000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 31 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[193/100, 49/25]`. -/
private theorem b9_pan_31 : (484011350961145314213/1000000000000000000000000 : ℝ) ≤ ∫ t in (193/100 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (392254969911931923/6250000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((193/100 : ℝ) + (49/25 : ℝ)) / 2) := b9_sig_31
  have hB0 : ((log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (11225745449402265833/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_31.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) ≤ (6845916640743196840817781/25000000000000000000000000 : ℝ) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 2) / 3) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6845916640743196840817781/25000000000000000000000000 : ℝ) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (6845916640743196840817781/25000000000000000000000000 : ℝ) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6845916640743196840817781/25000000000000000000000000 : ℝ) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (6845916640743196840817781/25000000000000000000000000 : ℝ) / ((((193/100 : ℝ) + (49/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (11225745449402265833/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (193/100 : ℝ) (49/25 : ℝ), 2 * (404630161314827979/12500000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_31.2.2.1
    have hX : (930289161535406617213773103/1980000000000000000000000000 : ℝ) ≤ (1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (930289161535406617213773103/1980000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((49/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (404630161314827979/12500000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (930289161535406617213773103/1980000000000000000000000000 : ℝ) / ((49/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (404630161314827979/12500000000000000000 : ℝ) ≤ ((1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) / ((49/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (404630161314827979/12500000000000000000 : ℝ) ≤ (930289161535406617213773103/1980000000000000000000000000 : ℝ) / ((49/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (930289161535406617213773103/1980000000000000000000000000 : ℝ) / ((49/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) / ((49/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) / ((49/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) / ((49/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((49/25 : ℝ) + 2) * ((49/25 : ℝ) + 1) - log (((49/25 : ℝ) + 2) / 3)) / ((49/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (193/100 : ℝ)) (b := (49/25 : ℝ)) (C := (404630161314827979/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (49/25 : ℝ) - (193/100 : ℝ) ≤ (((193/100 : ℝ) + (49/25 : ℝ)) / 2) * log ((49/25 : ℝ) / (193/100 : ℝ)) := by
    have hl := b9_lgs_31.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (193/100 : ℝ)) (b := (49/25 : ℝ)) (m := (((193/100 : ℝ) + (49/25 : ℝ)) / 2)) (A := (392254969911931923/6250000000000000000 : ℝ)) (B := (11225745449402265833/100000000000000000000 : ℝ)) (C := (404630161314827979/12500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_31.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 32 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_32 :
    ((54512201949879654125121583/50000000000000000000000000 : ℝ) ≤ log ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) ∧ log ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) ≤ (3407012621867478382820099/3125000000000000000000000 : ℝ)) ∧
    ((439706967872164892643771/1562500000000000000000000 : ℝ) ≤ log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) ≤ (5628249188763710625840269/20000000000000000000000000 : ℝ)) ∧
    (log (((199/100 : ℝ) + 2) / 3) ≤ (28517894223366239707839727/100000000000000000000000000 : ℝ)) ∧
    ((379754137349379159123789/25000000000000000000000000 : ℝ) ≤ log ((199/100 : ℝ) / (49/25 : ℝ)) ∧ log ((199/100 : ℝ) / (49/25 : ℝ)) ≤ (1519016549397516636495157/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) = (119/40 : ℝ) by norm_num]
    have hkey : log (119/40 : ℝ) = log (2 : ℝ) + log (119/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (119/80 : ℝ)) (x := (39/199 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21).1
    have hnum : (198548429218823886542599769271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 21, (39/199 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) = (119/40 : ℝ) by norm_num]
    have hkey : log (119/40 : ℝ) = log (2 : ℝ) + log (119/80 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (119/80 : ℝ)) (x := (39/199 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21).2
    have hnum : 2 * (∑ i ∈ Finset.range 21, (39/199 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((39/199 : ℝ) ^ (2 * 21 + 1) / (1 - (39/199 : ℝ) ^ 2)) ≤ (397096858437647773085199558541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) = (53/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (53/40 : ℝ)) (x := (13/93 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (439706967872164892643771/1562500000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (13/93 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) = (53/40 : ℝ) by norm_num]
    have h := (log_enclosure (y := (53/40 : ℝ)) (x := (13/93 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (13/93 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((13/93 : ℝ) ^ (2 * 18 + 1) / (1 - (13/93 : ℝ) ^ 2)) ≤ (5628249188763710625840269/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((199/100 : ℝ) + 2) / 3) = (133/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (133/100 : ℝ)) (x := (33/233 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (33/233 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((33/233 : ℝ) ^ (2 * 18 + 1) / (1 - (33/233 : ℝ) ^ 2)) ≤ (28517894223366239707839727/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((199/100 : ℝ) / (49/25 : ℝ)) = (199/196 : ℝ) by norm_num]
    have h := (log_enclosure (y := (199/196 : ℝ)) (x := (3/395 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (379754137349379159123789/25000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/395 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((199/100 : ℝ) / (49/25 : ℝ)) = (199/196 : ℝ) by norm_num]
    have h := (log_enclosure (y := (199/196 : ℝ)) (x := (3/395 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/395 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/395 : ℝ) ^ (2 * 7 + 1) / (1 - (3/395 : ℝ) ^ 2)) ≤ (1519016549397516636495157/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 32, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_32 : (206743157865160799/3125000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((49/25 : ℝ) + (199/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2)) (c := ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1)) (m := (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 30
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) - 1 = ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1)) (m := (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_32.1
  have hq := b9_lgs_32.2.1
  have hprod : (54512201949879654125121583/50000000000000000000000000 : ℝ) * (439706967872164892643771/1562500000000000000000000 : ℝ) ≤ log ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) * log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((35025050019734093200373522369169544884569223415435220937168682557422881016042191357/25380070312726168968974910690977947963940437651092792375679589754832266370908383400 : ℝ) : ℝ) * log ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) ≤ ((35025050019734093200373522369169544884569223415435220937168682557422881016042191357/25380070312726168968974910690977947963940437651092792375679589754832266370908383400 : ℝ) : ℝ) * (3407012621867478382820099/3125000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-16590255297327867324757763145588059819676232888860384043580777984030324583745296082/15101141836072070536540071861131879038544560402400211463529355904125198490690488123 : ℝ) : ℝ) * log 2 ≤ ((-16590255297327867324757763145588059819676232888860384043580777984030324583745296082/15101141836072070536540071861131879038544560402400211463529355904125198490690488123 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (1072484776572686163464091770308952390959552768354323430032656042151592117478560087150236015907554190350547138700285797067579401319906650523/19571265044492236486846107881345836929657582429634359746827777604002268779572609982926383671875000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) * log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) -
      ((35025050019734093200373522369169544884569223415435220937168682557422881016042191357/25380070312726168968974910690977947963940437651092792375679589754832266370908383400 : ℝ) * log ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) + (-16590255297327867324757763145588059819676232888860384043580777984030324583745296082/15101141836072070536540071861131879038544560402400211463529355904125198490690488123 : ℝ) * log 2 + (-15771132005312951367783423703880489085462387103325900250606408852292199755669514299684170289/32116947765320593209183356523234193935848340397348692917871224786055005176734539459161245000 : ℝ)) := by
    have e : (1072484776572686163464091770308952390959552768354323430032656042151592117478560087150236015907554190350547138700285797067579401319906650523/19571265044492236486846107881345836929657582429634359746827777604002268779572609982926383671875000000000000000000000000000000000000000000000 : ℝ) = (54512201949879654125121583/50000000000000000000000000 : ℝ) * (439706967872164892643771/1562500000000000000000000 : ℝ) - (((35025050019734093200373522369169544884569223415435220937168682557422881016042191357/25380070312726168968974910690977947963940437651092792375679589754832266370908383400 : ℝ) : ℝ) * (3407012621867478382820099/3125000000000000000000000 : ℝ) + ((-16590255297327867324757763145588059819676232888860384043580777984030324583745296082/15101141836072070536540071861131879038544560402400211463529355904125198490690488123 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-15771132005312951367783423703880489085462387103325900250606408852292199755669514299684170289/32116947765320593209183356523234193935848340397348692917871224786055005176734539459161245000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (1072484776572686163464091770308952390959552768354323430032656042151592117478560087150236015907554190350547138700285797067579401319906650523/19571265044492236486846107881345836929657582429634359746827777604002268779572609982926383671875000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (206743157865160799/3125000000000000000 : ℝ) ≤ (1072484776572686163464091770308952390959552768354323430032656042151592117478560087150236015907554190350547138700285797067579401319906650523/19571265044492236486846107881345836929657582429634359746827777604002268779572609982926383671875000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (1072484776572686163464091770308952390959552768354323430032656042151592117478560087150236015907554190350547138700285797067579401319906650523/19571265044492236486846107881345836929657582429634359746827777604002268779572609982926383671875000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 32 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[49/25, 199/100]`. -/
private theorem b9_pan_32 : (502458961189343310441/1000000000000000000000000 : ℝ) ≤ ∫ t in (49/25 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (206743157865160799/3125000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((49/25 : ℝ) + (199/100 : ℝ)) / 2) := b9_sig_32
  have hB0 : ((log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (228399547210081159/2000000000000000000 : ℝ) := by
    have hp := b9_lgs_32.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) ≤ (5628249188763710625840269/20000000000000000000000000 : ℝ) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 2) / 3) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (5628249188763710625840269/20000000000000000000000000 : ℝ) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (5628249188763710625840269/20000000000000000000000000 : ℝ) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (5628249188763710625840269/20000000000000000000000000 : ℝ) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (5628249188763710625840269/20000000000000000000000000 : ℝ) / ((((49/25 : ℝ) + (199/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (228399547210081159/2000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (49/25 : ℝ) (199/100 : ℝ), 2 * (3134270651056290099/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_32.2.2.1
    have hX : (18521360204876870356571948927/39900000000000000000000000000 : ℝ) ≤ (1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (18521360204876870356571948927/39900000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((199/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3134270651056290099/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (18521360204876870356571948927/39900000000000000000000000000 : ℝ) / ((199/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3134270651056290099/100000000000000000000 : ℝ) ≤ ((1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) / ((199/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3134270651056290099/100000000000000000000 : ℝ) ≤ (18521360204876870356571948927/39900000000000000000000000000 : ℝ) / ((199/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (18521360204876870356571948927/39900000000000000000000000000 : ℝ) / ((199/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) / ((199/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) / ((199/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) / ((199/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((199/100 : ℝ) + 2) * ((199/100 : ℝ) + 1) - log (((199/100 : ℝ) + 2) / 3)) / ((199/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (49/25 : ℝ)) (b := (199/100 : ℝ)) (C := (3134270651056290099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (199/100 : ℝ) - (49/25 : ℝ) ≤ (((49/25 : ℝ) + (199/100 : ℝ)) / 2) * log ((199/100 : ℝ) / (49/25 : ℝ)) := by
    have hl := b9_lgs_32.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (49/25 : ℝ)) (b := (199/100 : ℝ)) (m := (((49/25 : ℝ) + (199/100 : ℝ)) / 2)) (A := (206743157865160799/3125000000000000000 : ℝ)) (B := (228399547210081159/2000000000000000000 : ℝ)) (C := (3134270651056290099/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_32.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 33 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_33 :
    ((110027756798717090181986547/100000000000000000000000000 : ℝ) ≤ log ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) ∧ log ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) ≤ (110027756798717090181986549/100000000000000000000000000 : ℝ)) ∧
    ((14446564592610642612992287/50000000000000000000000000 : ℝ) ≤ log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) ≤ (1155725167408851409039383/4000000000000000000000000 : ℝ)) ∧
    (log (((101/50 : ℝ) + 2) / 3) ≤ (29266961396282000105132121/100000000000000000000000000 : ℝ)) ∧
    ((1496287267671236489130909/100000000000000000000000000 : ℝ) ≤ log ((101/50 : ℝ) / (199/100 : ℝ)) ∧ log ((101/50 : ℝ) / (199/100 : ℝ)) ≤ (149628726767123648913091/10000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) = (601/200 : ℝ) by norm_num]
    have hkey : log (601/200 : ℝ) = log (2 : ℝ) + log (601/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (601/400 : ℝ)) (x := (201/1001 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22).1
    have hnum : (203565193713612796201316674271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 22, (201/1001 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) = (601/200 : ℝ) by norm_num]
    have hkey : log (601/200 : ℝ) = log (2 : ℝ) + log (601/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (601/400 : ℝ)) (x := (201/1001 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22).2
    have hnum : 2 * (∑ i ∈ Finset.range 22, (201/1001 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((201/1001 : ℝ) ^ (2 * 22 + 1) / (1 - (201/1001 : ℝ) ^ 2)) ≤ (407130387427225592402633368541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) = (267/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (267/200 : ℝ)) (x := (67/467 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (14446564592610642612992287/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (67/467 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) = (267/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (267/200 : ℝ)) (x := (67/467 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (67/467 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((67/467 : ℝ) ^ (2 * 18 + 1) / (1 - (67/467 : ℝ) ^ 2)) ≤ (1155725167408851409039383/4000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((101/50 : ℝ) + 2) / 3) = (67/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (67/50 : ℝ)) (x := (17/117 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (17/117 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((17/117 : ℝ) ^ (2 * 18 + 1) / (1 - (17/117 : ℝ) ^ 2)) ≤ (29266961396282000105132121/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((101/50 : ℝ) / (199/100 : ℝ)) = (202/199 : ℝ) by norm_num]
    have h := (log_enclosure (y := (202/199 : ℝ)) (x := (3/401 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1496287267671236489130909/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/401 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((101/50 : ℝ) / (199/100 : ℝ)) = (202/199 : ℝ) by norm_num]
    have h := (log_enclosure (y := (202/199 : ℝ)) (x := (3/401 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/401 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/401 : ℝ) ^ (2 * 7 + 1) / (1 - (3/401 : ℝ) ^ 2)) ≤ (149628726767123648913091/10000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 33, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_33 : (6961216488754881113/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((199/100 : ℝ) + (101/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2)) (c := ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1)) (m := (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 31
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) - 1 = ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1)) (m := (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_33.1
  have hq := b9_lgs_33.2.1
  have hprod : (110027756798717090181986547/100000000000000000000000000 : ℝ) * (14446564592610642612992287/50000000000000000000000000 : ℝ) ≤ log ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) * log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((64266147912870008166019102457091794242026559967833929541510892688606393537927316114760470946795215438546931933/46316562225320941668702661236628390277048151617955503789866266942617572194956460957479777256730745378094214200 : ℝ) : ℝ) * log ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) ≤ ((64266147912870008166019102457091794242026559967833929541510892688606393537927316114760470946795215438546931933/46316562225320941668702661236628390277048151617955503789866266942617572194956460957479777256730745378094214200 : ℝ) : ℝ) * (110027756798717090181986549/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-1779155376047364545434746857522779309546725340230775112404789574651645796855847248853188101137666535466998/1619460217668564394010582560721272387309375930697744887757561781210404622201274858653139064920655432800497 : ℝ) : ℝ) * log 2 ≤ ((-1779155376047364545434746857522779309546725340230775112404789574651645796855847248853188101137666535466998/1619460217668564394010582560721272387309375930697744887757561781210404622201274858653139064920655432800497 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (148783733616563493479904668132429350519937566691601597983735997760207333113423871350707916493077209219424641696274007423399084058773366348712960603752363573778461512983/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) * log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) -
      ((64266147912870008166019102457091794242026559967833929541510892688606393537927316114760470946795215438546931933/46316562225320941668702661236628390277048151617955503789866266942617572194956460957479777256730745378094214200 : ℝ) * log ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) + (-1779155376047364545434746857522779309546725340230775112404789574651645796855847248853188101137666535466998/1619460217668564394010582560721272387309375930697744887757561781210404622201274858653139064920655432800497 : ℝ) * log 2 + (-1302917933369185828217980709126673348126483947915418831254845498429746752839234318045439649473572178871073870444606330817/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000 : ℝ)) := by
    have e : (148783733616563493479904668132429350519937566691601597983735997760207333113423871350707916493077209219424641696274007423399084058773366348712960603752363573778461512983/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000000000000000000000000000000000000000000000000000 : ℝ) = (110027756798717090181986547/100000000000000000000000000 : ℝ) * (14446564592610642612992287/50000000000000000000000000 : ℝ) - (((64266147912870008166019102457091794242026559967833929541510892688606393537927316114760470946795215438546931933/46316562225320941668702661236628390277048151617955503789866266942617572194956460957479777256730745378094214200 : ℝ) : ℝ) * (110027756798717090181986549/100000000000000000000000000 : ℝ) + ((-1779155376047364545434746857522779309546725340230775112404789574651645796855847248853188101137666535466998/1619460217668564394010582560721272387309375930697744887757561781210404622201274858653139064920655432800497 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-1302917933369185828217980709126673348126483947915418831254845498429746752839234318045439649473572178871073870444606330817/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (148783733616563493479904668132429350519937566691601597983735997760207333113423871350707916493077209219424641696274007423399084058773366348712960603752363573778461512983/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (6961216488754881113/100000000000000000000 : ℝ) ≤ (148783733616563493479904668132429350519937566691601597983735997760207333113423871350707916493077209219424641696274007423399084058773366348712960603752363573778461512983/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (148783733616563493479904668132429350519937566691601597983735997760207333113423871350707916493077209219424641696274007423399084058773366348712960603752363573778461512983/2580353450290836543785596060792650517399362160585474541285180840323554684603091034345098115603651426241891045908112735000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 33 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[199/100, 101/50]`. -/
private theorem b9_pan_33 : (260391762197720020767/500000000000000000000000 : ℝ) ≤ ∫ t in (199/100 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (6961216488754881113/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((199/100 : ℝ) + (101/50 : ℝ)) / 2) := b9_sig_33
  have hB0 : ((log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (2902010657010544591/25000000000000000000 : ℝ) := by
    have hp := b9_lgs_33.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) ≤ (1155725167408851409039383/4000000000000000000000000 : ℝ) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 2) / 3) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (1155725167408851409039383/4000000000000000000000000 : ℝ) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (1155725167408851409039383/4000000000000000000000000 : ℝ) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (1155725167408851409039383/4000000000000000000000000 : ℝ) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (1155725167408851409039383/4000000000000000000000000 : ℝ) / ((((199/100 : ℝ) + (101/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (2902010657010544591/25000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (199/100 : ℝ) (101/50 : ℝ), 2 * (3035111081641573767/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_33.2.2.1
    have hX : (9217340759347317978868443679/20100000000000000000000000000 : ℝ) ≤ (1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9217340759347317978868443679/20100000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((101/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (3035111081641573767/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9217340759347317978868443679/20100000000000000000000000000 : ℝ) / ((101/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (3035111081641573767/100000000000000000000 : ℝ) ≤ ((1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) / ((101/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (3035111081641573767/100000000000000000000 : ℝ) ≤ (9217340759347317978868443679/20100000000000000000000000000 : ℝ) / ((101/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9217340759347317978868443679/20100000000000000000000000000 : ℝ) / ((101/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) / ((101/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) / ((101/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) / ((101/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((101/50 : ℝ) + 2) * ((101/50 : ℝ) + 1) - log (((101/50 : ℝ) + 2) / 3)) / ((101/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (199/100 : ℝ)) (b := (101/50 : ℝ)) (C := (3035111081641573767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (101/50 : ℝ) - (199/100 : ℝ) ≤ (((199/100 : ℝ) + (101/50 : ℝ)) / 2) * log ((101/50 : ℝ) / (199/100 : ℝ)) := by
    have hl := b9_lgs_33.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (199/100 : ℝ)) (b := (101/50 : ℝ)) (m := (((199/100 : ℝ) + (101/50 : ℝ)) / 2)) (A := (6961216488754881113/100000000000000000000 : ℝ)) (B := (2902010657010544591/25000000000000000000 : ℝ)) (C := (3035111081641573767/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_33.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 34 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_34 :
    ((2775528561278653961741893/2500000000000000000000000 : ℝ) ≤ log ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) ∧ log ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) ≤ (55510571225573079234837861/50000000000000000000000000 : ℝ)) ∧
    ((14819700652690121438336907/50000000000000000000000000 : ℝ) ≤ log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) ∧ log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) ≤ (5927880261076048575334763/20000000000000000000000000 : ℝ)) ∧
    (log (((41/20 : ℝ) + 2) / 3) ≤ (15005229622516904037525607/50000000000000000000000000 : ℝ)) ∧
    ((1474228173720341816609231/100000000000000000000000000 : ℝ) ≤ log ((41/20 : ℝ) / (101/50 : ℝ)) ∧ log ((41/20 : ℝ) / (101/50 : ℝ)) ≤ (92139260857521363538077/6250000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) = (607/200 : ℝ) by norm_num]
    have hkey : log (607/200 : ℝ) = log (2 : ℝ) + log (607/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (607/400 : ℝ)) (x := (207/1007 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22).1
    have hnum : (208532121975758137639762539271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 22, (207/1007 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) = (607/200 : ℝ) by norm_num]
    have hkey : log (607/200 : ℝ) = log (2 : ℝ) + log (607/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (607/400 : ℝ)) (x := (207/1007 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22).2
    have hnum : 2 * (∑ i ∈ Finset.range 22, (207/1007 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((207/1007 : ℝ) ^ (2 * 22 + 1) / (1 - (207/1007 : ℝ) ^ 2)) ≤ (417064243951516275279525098541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) = (269/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (269/200 : ℝ)) (x := (69/469 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (14819700652690121438336907/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (69/469 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) = (269/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (269/200 : ℝ)) (x := (69/469 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (69/469 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((69/469 : ℝ) ^ (2 * 18 + 1) / (1 - (69/469 : ℝ) ^ 2)) ≤ (5927880261076048575334763/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((41/20 : ℝ) + 2) / 3) = (27/20 : ℝ) by norm_num]
    have h := (log_enclosure (y := (27/20 : ℝ)) (x := (7/47 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (7/47 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((7/47 : ℝ) ^ (2 * 18 + 1) / (1 - (7/47 : ℝ) ^ 2)) ≤ (15005229622516904037525607/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((41/20 : ℝ) / (101/50 : ℝ)) = (205/202 : ℝ) by norm_num]
    have h := (log_enclosure (y := (205/202 : ℝ)) (x := (3/407 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1474228173720341816609231/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/407 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((41/20 : ℝ) / (101/50 : ℝ)) = (205/202 : ℝ) by norm_num]
    have h := (log_enclosure (y := (205/202 : ℝ)) (x := (3/407 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/407 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/407 : ℝ) ^ (2 * 7 + 1) / (1 - (3/407 : ℝ) ^ 2)) ≤ (92139260857521363538077/6250000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 34, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_34 : (1828051026112187107/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((101/50 : ℝ) + (41/20 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2)) (c := ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1)) (m := (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 31
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) - 1 = ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1)) (m := (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_34.1
  have hq := b9_lgs_34.2.1
  have hprod : (2775528561278653961741893/2500000000000000000000000 : ℝ) * (14819700652690121438336907/50000000000000000000000000 : ℝ) ≤ log ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) * log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((3602655086838408523188101478283734573971393108655654770462592674351978667823681999741838048560839125190311/2582541048970100898791184906471438076786715145031345539711071516627794139243966497092346816245516005417496 : ℝ) : ℝ) * log ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) ≤ ((3602655086838408523188101478283734573971393108655654770462592674351978667823681999741838048560839125190311/2582541048970100898791184906471438076786715145031345539711071516627794139243966497092346816245516005417496 : ℝ) : ℝ) * (55510571225573079234837861/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-4610458744869223707428636902576558565780776658582963544049049170363908472363380353478801666532598393068954/4196629204576413960535675473016086874778412110675936502030491214520165476271445557775063576398963508803431 : ℝ) : ℝ) * log 2 ≤ ((-4610458744869223707428636902576558565780776658582963544049049170363908472363380353478801666532598393068954/4196629204576413960535675473016086874778412110675936502030491214520165476271445557775063576398963508803431 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (9235200368828829119612749150469994725290766859589660887895799602472436245671279270842153752340686255530409645482128796718437966334338598736075809819057045222061137/152477900391977830246885788083102531336996063054401020007969756918265101574222102534597460720015728577826212171310875000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) * log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) -
      ((3602655086838408523188101478283734573971393108655654770462592674351978667823681999741838048560839125190311/2582541048970100898791184906471438076786715145031345539711071516627794139243966497092346816245516005417496 : ℝ) * log ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) + (-4610458744869223707428636902576558565780776658582963544049049170363908472363380353478801666532598393068954/4196629204576413960535675473016086874778412110675936502030491214520165476271445557775063576398963508803431 : ℝ) * log 2 + (-15284868263690265534735499330000113881814127343980880494085906883224916533476350100271058419720031638470919482176901/29464328578159967197465852769681648567535471121623385508786426457635768420139536721661345066669706005377045830205000 : ℝ)) := by
    have e : (9235200368828829119612749150469994725290766859589660887895799602472436245671279270842153752340686255530409645482128796718437966334338598736075809819057045222061137/152477900391977830246885788083102531336996063054401020007969756918265101574222102534597460720015728577826212171310875000000000000000000000000000000000000000000000000 : ℝ) = (2775528561278653961741893/2500000000000000000000000 : ℝ) * (14819700652690121438336907/50000000000000000000000000 : ℝ) - (((3602655086838408523188101478283734573971393108655654770462592674351978667823681999741838048560839125190311/2582541048970100898791184906471438076786715145031345539711071516627794139243966497092346816245516005417496 : ℝ) : ℝ) * (55510571225573079234837861/50000000000000000000000000 : ℝ) + ((-4610458744869223707428636902576558565780776658582963544049049170363908472363380353478801666532598393068954/4196629204576413960535675473016086874778412110675936502030491214520165476271445557775063576398963508803431 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-15284868263690265534735499330000113881814127343980880494085906883224916533476350100271058419720031638470919482176901/29464328578159967197465852769681648567535471121623385508786426457635768420139536721661345066669706005377045830205000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (9235200368828829119612749150469994725290766859589660887895799602472436245671279270842153752340686255530409645482128796718437966334338598736075809819057045222061137/152477900391977830246885788083102531336996063054401020007969756918265101574222102534597460720015728577826212171310875000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (1828051026112187107/25000000000000000000 : ℝ) ≤ (9235200368828829119612749150469994725290766859589660887895799602472436245671279270842153752340686255530409645482128796718437966334338598736075809819057045222061137/152477900391977830246885788083102531336996063054401020007969756918265101574222102534597460720015728577826212171310875000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (9235200368828829119612749150469994725290766859589660887895799602472436245671279270842153752340686255530409645482128796718437966334338598736075809819057045222061137/152477900391977830246885788083102531336996063054401020007969756918265101574222102534597460720015728577826212171310875000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 34 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[101/50, 41/20]`. -/
private theorem b9_pan_34 : (538977085431695409683/1000000000000000000000000 : ℝ) ≤ ∫ t in (101/50 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (1828051026112187107/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((101/50 : ℝ) + (41/20 : ℝ)) / 2) := b9_sig_34
  have hB0 : ((log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (11790157936992418903/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_34.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) ≤ (5927880261076048575334763/20000000000000000000000000 : ℝ) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 2) / 3) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (5927880261076048575334763/20000000000000000000000000 : ℝ) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (5927880261076048575334763/20000000000000000000000000 : ℝ) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (5927880261076048575334763/20000000000000000000000000 : ℝ) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (5927880261076048575334763/20000000000000000000000000 : ℝ) / ((((101/50 : ℝ) + (41/20 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (11790157936992418903/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (101/50 : ℝ) (41/20 : ℝ), 2 * (2939408806623757337/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_34.2.2.1
    have hX : (1834576400576130772960425833/4050000000000000000000000000 : ℝ) ≤ (1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (1834576400576130772960425833/4050000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((41/20 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2939408806623757337/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (1834576400576130772960425833/4050000000000000000000000000 : ℝ) / ((41/20 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2939408806623757337/100000000000000000000 : ℝ) ≤ ((1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) / ((41/20 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2939408806623757337/100000000000000000000 : ℝ) ≤ (1834576400576130772960425833/4050000000000000000000000000 : ℝ) / ((41/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (1834576400576130772960425833/4050000000000000000000000000 : ℝ) / ((41/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) / ((41/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) / ((41/20 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) / ((41/20 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((41/20 : ℝ) + 2) * ((41/20 : ℝ) + 1) - log (((41/20 : ℝ) + 2) / 3)) / ((41/20 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (101/50 : ℝ)) (b := (41/20 : ℝ)) (C := (2939408806623757337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (41/20 : ℝ) - (101/50 : ℝ) ≤ (((101/50 : ℝ) + (41/20 : ℝ)) / 2) * log ((41/20 : ℝ) / (101/50 : ℝ)) := by
    have hl := b9_lgs_34.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (101/50 : ℝ)) (b := (41/20 : ℝ)) (m := (((101/50 : ℝ) + (41/20 : ℝ)) / 2)) (A := (1828051026112187107/25000000000000000000 : ℝ)) (B := (11790157936992418903/100000000000000000000 : ℝ)) (C := (2939408806623757337/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_34.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 35 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_35 :
    ((28001189234704368049662939/25000000000000000000000000 : ℝ) ≤ log ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) ∧ log ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) ≤ (56002378469408736099325879/50000000000000000000000000 : ℝ)) ∧
    ((474689772393225347880711/1562500000000000000000000 : ℝ) ≤ log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) ∧ log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) ≤ (6076029086633284452873101/20000000000000000000000000 : ℝ)) ∧
    (log (((52/25 : ℝ) + 2) / 3) ≤ (3843558746849508005815601/12500000000000000000000000 : ℝ)) ∧
    ((726405028145489762744661/50000000000000000000000000 : ℝ) ≤ log ((52/25 : ℝ) / (41/20 : ℝ)) ∧ log ((52/25 : ℝ) / (41/20 : ℝ)) ≤ (1452810056290979525489323/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) = (613/200 : ℝ) by norm_num]
    have hkey : log (613/200 : ℝ) = log (2 : ℝ) + log (613/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (613/400 : ℝ)) (x := (213/1013 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22).1
    have hnum : (213450194414114706284642719271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 22, (213/1013 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) = (613/200 : ℝ) by norm_num]
    have hkey : log (613/200 : ℝ) = log (2 : ℝ) + log (613/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (613/400 : ℝ)) (x := (213/1013 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22).2
    have hnum : 2 * (∑ i ∈ Finset.range 22, (213/1013 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((213/1013 : ℝ) ^ (2 * 22 + 1) / (1 - (213/1013 : ℝ) ^ 2)) ≤ (426900388828229412569285458541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) = (271/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (271/200 : ℝ)) (x := (71/471 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).1
    have hnum : (474689772393225347880711/1562500000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 18, (71/471 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) = (271/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (271/200 : ℝ)) (x := (71/471 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 18).2
    have hnum : 2 * (∑ i ∈ Finset.range 18, (71/471 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((71/471 : ℝ) ^ (2 * 18 + 1) / (1 - (71/471 : ℝ) ^ 2)) ≤ (6076029086633284452873101/20000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((52/25 : ℝ) + 2) / 3) = (34/25 : ℝ) by norm_num]
    have h := (log_enclosure (y := (34/25 : ℝ)) (x := (9/59 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (9/59 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/59 : ℝ) ^ (2 * 19 + 1) / (1 - (9/59 : ℝ) ^ 2)) ≤ (3843558746849508005815601/12500000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((52/25 : ℝ) / (41/20 : ℝ)) = (208/205 : ℝ) by norm_num]
    have h := (log_enclosure (y := (208/205 : ℝ)) (x := (3/413 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (726405028145489762744661/50000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/413 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((52/25 : ℝ) / (41/20 : ℝ)) = (208/205 : ℝ) by norm_num]
    have h := (log_enclosure (y := (208/205 : ℝ)) (x := (3/413 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/413 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/413 : ℝ) ^ (2 * 7 + 1) / (1 - (3/413 : ℝ) ^ 2)) ≤ (1452810056290979525489323/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 35, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_35 : (3834284267169639191/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((41/20 : ℝ) + (52/25 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2)) (c := ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1)) (m := (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 32
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) - 1 = ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1)) (m := (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_35.1
  have hq := b9_lgs_35.2.1
  have hprod : (28001189234704368049662939/25000000000000000000000000 : ℝ) * (474689772393225347880711/1562500000000000000000000 : ℝ) ≤ log ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) * log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((119558080757691793749547195510672746220008252062633550336832490699074438956527440198554359265406763404194611138977/85251749935236022108214756292155140109675721838215751170088274316356025535220401821884027568036997057353192430200 : ℝ) : ℝ) * log ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) ≤ ((119558080757691793749547195510672746220008252062633550336832490699074438956527440198554359265406763404194611138977/85251749935236022108214756292155140109675721838215751170088274316356025535220401821884027568036997057353192430200 : ℝ) : ℝ) * (56002378469408736099325879/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-468292375715238645143070413397995218150682292193083032763034506454048298583760782069160764776623035285145521434/426258749676180110541073781460775700548378609191078755850441371581780127676102009109420137840184985286765962151 : ℝ) : ℝ) * log 2 ≤ ((-468292375715238645143070413397995218150682292193083032763034506454048298583760782069160764776623035285145521434/426258749676180110541073781460775700548378609191078755850441371581780127676102009109420137840184985286765962151 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (71421290248830373967882828212905293766394230035788180190532051329199142022577993401930400505628861684560338845884206418255573957329002819022960783916448750844265110191/1124403721554814574866836820105556632365016356746770808301703578246939128059409154498935022692019942379269517724189671054687500000000000000000000000000000000000000000000 : ℝ) ≤ log ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) * log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) -
      ((119558080757691793749547195510672746220008252062633550336832490699074438956527440198554359265406763404194611138977/85251749935236022108214756292155140109675721838215751170088274316356025535220401821884027568036997057353192430200 : ℝ) * log ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) + (-468292375715238645143070413397995218150682292193083032763034506454048298583760782069160764776623035285145521434/426258749676180110541073781460775700548378609191078755850441371581780127676102009109420137840184985286765962151 : ℝ) * log 2 + (-229925216819426621091203566142717255657365796746362376404993560686719151551088321023837093262280652344290466122002706839007/431771029077048796748865338920533746828166280990759990387854174046824625174813115327591048713735657873639494806088833685000 : ℝ)) := by
    have e : (71421290248830373967882828212905293766394230035788180190532051329199142022577993401930400505628861684560338845884206418255573957329002819022960783916448750844265110191/1124403721554814574866836820105556632365016356746770808301703578246939128059409154498935022692019942379269517724189671054687500000000000000000000000000000000000000000000 : ℝ) = (28001189234704368049662939/25000000000000000000000000 : ℝ) * (474689772393225347880711/1562500000000000000000000 : ℝ) - (((119558080757691793749547195510672746220008252062633550336832490699074438956527440198554359265406763404194611138977/85251749935236022108214756292155140109675721838215751170088274316356025535220401821884027568036997057353192430200 : ℝ) : ℝ) * (56002378469408736099325879/50000000000000000000000000 : ℝ) + ((-468292375715238645143070413397995218150682292193083032763034506454048298583760782069160764776623035285145521434/426258749676180110541073781460775700548378609191078755850441371581780127676102009109420137840184985286765962151 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-229925216819426621091203566142717255657365796746362376404993560686719151551088321023837093262280652344290466122002706839007/431771029077048796748865338920533746828166280990759990387854174046824625174813115327591048713735657873639494806088833685000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (71421290248830373967882828212905293766394230035788180190532051329199142022577993401930400505628861684560338845884206418255573957329002819022960783916448750844265110191/1124403721554814574866836820105556632365016356746770808301703578246939128059409154498935022692019942379269517724189671054687500000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (3834284267169639191/50000000000000000000 : ℝ) ≤ (71421290248830373967882828212905293766394230035788180190532051329199142022577993401930400505628861684560338845884206418255573957329002819022960783916448750844265110191/1124403721554814574866836820105556632365016356746770808301703578246939128059409154498935022692019942379269517724189671054687500000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (71421290248830373967882828212905293766394230035788180190532051329199142022577993401930400505628861684560338845884206418255573957329002819022960783916448750844265110191/1124403721554814574866836820105556632365016356746770808301703578246939128059409154498935022692019942379269517724189671054687500000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 35 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[41/20, 52/25]`. -/
private theorem b9_pan_35 : (557032613638986942339/1000000000000000000000000 : ℝ) ≤ ∫ t in (41/20 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (3834284267169639191/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((41/20 : ℝ) + (52/25 : ℝ)) / 2) := b9_sig_35
  have hB0 : ((log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (11966530744549178473/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_35.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) ≤ (6076029086633284452873101/20000000000000000000000000 : ℝ) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 2) / 3) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6076029086633284452873101/20000000000000000000000000 : ℝ) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (6076029086633284452873101/20000000000000000000000000 : ℝ) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (6076029086633284452873101/20000000000000000000000000 : ℝ) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (6076029086633284452873101/20000000000000000000000000 : ℝ) / ((((41/20 : ℝ) + (52/25 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (11966530744549178473/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (41/20 : ℝ) (52/25 : ℝ), 2 * (2847017863990401099/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_35.2.2.1
    have hX : (285228503910675091703404349/637500000000000000000000000 : ℝ) ≤ (1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (285228503910675091703404349/637500000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((52/25 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2847017863990401099/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (285228503910675091703404349/637500000000000000000000000 : ℝ) / ((52/25 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2847017863990401099/100000000000000000000 : ℝ) ≤ ((1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) / ((52/25 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2847017863990401099/100000000000000000000 : ℝ) ≤ (285228503910675091703404349/637500000000000000000000000 : ℝ) / ((52/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (285228503910675091703404349/637500000000000000000000000 : ℝ) / ((52/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) / ((52/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) / ((52/25 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) / ((52/25 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((52/25 : ℝ) + 2) * ((52/25 : ℝ) + 1) - log (((52/25 : ℝ) + 2) / 3)) / ((52/25 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (41/20 : ℝ)) (b := (52/25 : ℝ)) (C := (2847017863990401099/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (52/25 : ℝ) - (41/20 : ℝ) ≤ (((41/20 : ℝ) + (52/25 : ℝ)) / 2) * log ((52/25 : ℝ) / (41/20 : ℝ)) := by
    have hl := b9_lgs_35.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (41/20 : ℝ)) (b := (52/25 : ℝ)) (m := (((41/20 : ℝ) + (52/25 : ℝ)) / 2)) (A := (3834284267169639191/50000000000000000000 : ℝ)) (B := (11966530744549178473/100000000000000000000 : ℝ)) (C := (2847017863990401099/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_35.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 36 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_36 :
    ((22595758122731188495496407/20000000000000000000000000 : ℝ) ≤ log ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) ∧ log ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) ≤ (112978790613655942477482037/100000000000000000000000000 : ℝ)) ∧
    ((31115442863692305510087039/100000000000000000000000000 : ℝ) ≤ log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) ≤ (48617879474519227359511/156250000000000000000000 : ℝ)) ∧
    (log (((211/100 : ℝ) + 2) / 3) ≤ (15740536992001677363960361/50000000000000000000000000 : ℝ)) ∧
    ((1432005377474852201954033/100000000000000000000000000 : ℝ) ≤ log ((211/100 : ℝ) / (52/25 : ℝ)) ∧ log ((211/100 : ℝ) / (52/25 : ℝ)) ≤ (716002688737426100977017/50000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) = (619/200 : ℝ) by norm_num]
    have hkey : log (619/200 : ℝ) = log (2 : ℝ) + log (619/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (619/400 : ℝ)) (x := (219/1019 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23).1
    have hnum : (218320362788307057678794114271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 23, (219/1019 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) = (619/200 : ℝ) by norm_num]
    have hkey : log (619/200 : ℝ) = log (2 : ℝ) + log (619/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (619/400 : ℝ)) (x := (219/1019 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23).2
    have hnum : 2 * (∑ i ∈ Finset.range 23, (219/1019 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((219/1019 : ℝ) ^ (2 * 23 + 1) / (1 - (219/1019 : ℝ) ^ 2)) ≤ (436640725576614115357588248541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) = (273/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (273/200 : ℝ)) (x := (73/473 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (31115442863692305510087039/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (73/473 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) = (273/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (273/200 : ℝ)) (x := (73/473 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (73/473 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((73/473 : ℝ) ^ (2 * 19 + 1) / (1 - (73/473 : ℝ) ^ 2)) ≤ (48617879474519227359511/156250000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((211/100 : ℝ) + 2) / 3) = (137/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (137/100 : ℝ)) (x := (37/237 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (37/237 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((37/237 : ℝ) ^ (2 * 19 + 1) / (1 - (37/237 : ℝ) ^ 2)) ≤ (15740536992001677363960361/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((211/100 : ℝ) / (52/25 : ℝ)) = (211/208 : ℝ) by norm_num]
    have h := (log_enclosure (y := (211/208 : ℝ)) (x := (3/419 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1432005377474852201954033/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/419 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((211/100 : ℝ) / (52/25 : ℝ)) = (211/208 : ℝ) by norm_num]
    have h := (log_enclosure (y := (211/208 : ℝ)) (x := (3/419 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/419 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/419 : ℝ) ^ (2 * 7 + 1) / (1 - (3/419 : ℝ) ^ 2)) ≤ (716002688737426100977017/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 36, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_36 : (8030140505194968577/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((52/25 : ℝ) + (211/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2)) (c := ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1)) (m := (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 32
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) - 1 = ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1)) (m := (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_36.1
  have hq := b9_lgs_36.2.1
  have hprod : (22595758122731188495496407/20000000000000000000000000 : ℝ) * (31115442863692305510087039/100000000000000000000000000 : ℝ) ≤ log ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) * log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((12512520162811589674662139017711918699972426859739850584396234942279428471642908008126627314159784700934031876909/8875607586515384718026411532120487567325233181173188984731510037873191765000735100984834655535434281469389124200 : ℝ) : ℝ) * log ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) ≤ ((12512520162811589674662139017711918699972426859739850584396234942279428471642908008126627314159784700934031876909/8875607586515384718026411532120487567325233181173188984731510037873191765000735100984834655535434281469389124200 : ℝ) : ℝ) * (112978790613655942477482037/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-48754177777119277648224239835174469816283410546154118670485916274050253456733575635784051441119937812254550414/44378037932576923590132057660602437836626165905865944923657550189365958825003675504924173277677171407346945621 : ℝ) : ℝ) * log 2 ≤ ((-48754177777119277648224239835174469816283410546154118670485916274050253456733575635784051441119937812254550414/44378037932576923590132057660602437836626165905865944923657550189365958825003675504924173277677171407346945621 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (39467214729658877625158929477411095232471494950475521633322938534773436157412107935599710898550921009719382747711217366398212841597782048641880528671405489212349742811243/593365402584357312610962981055723074905773379977544623730956246550287401058675737221271161403732139024635019780414481382000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) * log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) -
      ((12512520162811589674662139017711918699972426859739850584396234942279428471642908008126627314159784700934031876909/8875607586515384718026411532120487567325233181173188984731510037873191765000735100984834655535434281469389124200 : ℝ) * log ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) + (-48754177777119277648224239835174469816283410546154118670485916274050253456733575635784051441119937812254550414/44378037932576923590132057660602437836626165905865944923657550189365958825003675504924173277677171407346945621 : ℝ) * log 2 + (-270086215561852793960625633887805251973652587595019645588088711251744533034287349373526455705760993302217644956218431837617/494471168820297760509135817546435895754811149981287186442463538791906167548896447684392634503110115853862516483678734485000 : ℝ)) := by
    have e : (39467214729658877625158929477411095232471494950475521633322938534773436157412107935599710898550921009719382747711217366398212841597782048641880528671405489212349742811243/593365402584357312610962981055723074905773379977544623730956246550287401058675737221271161403732139024635019780414481382000000000000000000000000000000000000000000000000000 : ℝ) = (22595758122731188495496407/20000000000000000000000000 : ℝ) * (31115442863692305510087039/100000000000000000000000000 : ℝ) - (((12512520162811589674662139017711918699972426859739850584396234942279428471642908008126627314159784700934031876909/8875607586515384718026411532120487567325233181173188984731510037873191765000735100984834655535434281469389124200 : ℝ) : ℝ) * (112978790613655942477482037/100000000000000000000000000 : ℝ) + ((-48754177777119277648224239835174469816283410546154118670485916274050253456733575635784051441119937812254550414/44378037932576923590132057660602437836626165905865944923657550189365958825003675504924173277677171407346945621 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-270086215561852793960625633887805251973652587595019645588088711251744533034287349373526455705760993302217644956218431837617/494471168820297760509135817546435895754811149981287186442463538791906167548896447684392634503110115853862516483678734485000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (39467214729658877625158929477411095232471494950475521633322938534773436157412107935599710898550921009719382747711217366398212841597782048641880528671405489212349742811243/593365402584357312610962981055723074905773379977544623730956246550287401058675737221271161403732139024635019780414481382000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (8030140505194968577/100000000000000000000 : ℝ) ≤ (39467214729658877625158929477411095232471494950475521633322938534773436157412107935599710898550921009719382747711217366398212841597782048641880528671405489212349742811243/593365402584357312610962981055723074905773379977544623730956246550287401058675737221271161403732139024635019780414481382000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (39467214729658877625158929477411095232471494950475521633322938534773436157412107935599710898550921009719382747711217366398212841597782048641880528671405489212349742811243/593365402584357312610962981055723074905773379977544623730956246550287401058675737221271161403732139024635019780414481382000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 36 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[52/25, 211/100]`. -/
private theorem b9_pan_36 : (574943917329212145501/1000000000000000000000000 : ℝ) ≤ ∫ t in (52/25 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (8030140505194968577/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((52/25 : ℝ) + (211/100 : ℝ)) / 2) := b9_sig_36
  have hB0 : ((log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1213735974902872387/10000000000000000000 : ℝ) := by
    have hp := b9_lgs_36.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) ≤ (48617879474519227359511/156250000000000000000000 : ℝ) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 2) / 3) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (48617879474519227359511/156250000000000000000000 : ℝ) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (48617879474519227359511/156250000000000000000000 : ℝ) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (48617879474519227359511/156250000000000000000000 : ℝ) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (48617879474519227359511/156250000000000000000000 : ℝ) / ((((52/25 : ℝ) + (211/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1213735974902872387/10000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (52/25 : ℝ) (211/100 : ℝ), 2 * (2757799642270241409/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_36.2.2.1
    have hX : (9080639296287310603412291629/20550000000000000000000000000 : ℝ) ≤ (1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9080639296287310603412291629/20550000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((211/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2757799642270241409/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9080639296287310603412291629/20550000000000000000000000000 : ℝ) / ((211/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2757799642270241409/100000000000000000000 : ℝ) ≤ ((1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) / ((211/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2757799642270241409/100000000000000000000 : ℝ) ≤ (9080639296287310603412291629/20550000000000000000000000000 : ℝ) / ((211/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9080639296287310603412291629/20550000000000000000000000000 : ℝ) / ((211/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) / ((211/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) / ((211/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) / ((211/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((211/100 : ℝ) + 2) * ((211/100 : ℝ) + 1) - log (((211/100 : ℝ) + 2) / 3)) / ((211/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (52/25 : ℝ)) (b := (211/100 : ℝ)) (C := (2757799642270241409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (211/100 : ℝ) - (52/25 : ℝ) ≤ (((52/25 : ℝ) + (211/100 : ℝ)) / 2) * log ((211/100 : ℝ) / (52/25 : ℝ)) := by
    have hl := b9_lgs_36.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (52/25 : ℝ)) (b := (211/100 : ℝ)) (m := (((52/25 : ℝ) + (211/100 : ℝ)) / 2)) (A := (8030140505194968577/100000000000000000000 : ℝ)) (B := (1213735974902872387/10000000000000000000 : ℝ)) (C := (2757799642270241409/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_36.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 37 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_37 :
    ((11394342831883648209498223/10000000000000000000000000 : ℝ) ≤ log ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) ∧ log ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) ≤ (14242928539854560261872779/12500000000000000000000000 : ℝ)) ∧
    ((31845373111853461581024721/100000000000000000000000000 : ℝ) ≤ log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) ∧ log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) ≤ (15922686555926730790512361/50000000000000000000000000 : ℝ)) ∧
    (log (((107/50 : ℝ) + 2) / 3) ≤ (32208349916911332358324729/100000000000000000000000000 : ℝ)) ∧
    ((1411788154578498697967467/100000000000000000000000000 : ℝ) ≤ log ((107/50 : ℝ) / (211/100 : ℝ)) ∧ log ((107/50 : ℝ) / (211/100 : ℝ)) ≤ (352947038644624674491867/25000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) = (25/8 : ℝ) by norm_num]
    have hkey : log (25/8 : ℝ) = log (2 : ℝ) + log (25/16 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (25/16 : ℝ)) (x := (9/41 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23).1
    have hnum : (223143551314209755766295089271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 23, (9/41 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) = (25/8 : ℝ) by norm_num]
    have hkey : log (25/8 : ℝ) = log (2 : ℝ) + log (25/16 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (25/16 : ℝ)) (x := (9/41 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23).2
    have hnum : 2 * (∑ i ∈ Finset.range 23, (9/41 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((9/41 : ℝ) ^ (2 * 23 + 1) / (1 - (9/41 : ℝ) ^ 2)) ≤ (446287102628419511532590198541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) = (11/8 : ℝ) by norm_num]
    have h := (log_enclosure (y := (11/8 : ℝ)) (x := (3/19 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (31845373111853461581024721/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (3/19 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) = (11/8 : ℝ) by norm_num]
    have h := (log_enclosure (y := (11/8 : ℝ)) (x := (3/19 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (3/19 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/19 : ℝ) ^ (2 * 19 + 1) / (1 - (3/19 : ℝ) ^ 2)) ≤ (15922686555926730790512361/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((107/50 : ℝ) + 2) / 3) = (69/50 : ℝ) by norm_num]
    have h := (log_enclosure (y := (69/50 : ℝ)) (x := (19/119 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (19/119 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((19/119 : ℝ) ^ (2 * 19 + 1) / (1 - (19/119 : ℝ) ^ 2)) ≤ (32208349916911332358324729/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((107/50 : ℝ) / (211/100 : ℝ)) = (214/211 : ℝ) by norm_num]
    have h := (log_enclosure (y := (214/211 : ℝ)) (x := (3/425 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (1411788154578498697967467/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/425 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((107/50 : ℝ) / (211/100 : ℝ)) = (214/211 : ℝ) by norm_num]
    have h := (log_enclosure (y := (214/211 : ℝ)) (x := (3/425 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/425 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/425 : ℝ) ^ (2 * 7 + 1) / (1 - (3/425 : ℝ) ^ 2)) ≤ (352947038644624674491867/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 37, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_37 : (4198378289448831767/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((211/100 : ℝ) + (107/50 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2)) (c := ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1)) (m := (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 32
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) - 1 = ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1)) (m := (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_37.1
  have hq := b9_lgs_37.2.1
  have hprod : (11394342831883648209498223/10000000000000000000000000 : ℝ) * (31845373111853461581024721/100000000000000000000000000 : ℝ) ≤ log ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) * log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((614957911641027380121625534795725665450474510578150517517364565575/433966189866678990728641332227383042332365733993375514455103140072 : ℝ) : ℝ) * log ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) ≤ ((614957911641027380121625534795725665450474510578150517517364565575/433966189866678990728641332227383042332365733993375514455103140072 : ℝ) : ℝ) * (14242928539854560261872779/12500000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-78414434095179119630640082044519191911143475682800571640730057466/71376018070177465580368640168977474067823311512068341193273542775 : ℝ) : ℝ) * log 2 ≤ ((-78414434095179119630640082044519191911143475682800571640730057466/71376018070177465580368640168977474067823311512068341193273542775 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (25222766121242371396566607344567136481825368823608124674926863177825474574495396509876835651726629813342964515906913900114037/362651965581290740566291797585417114905957541550535813967734940218926514539000000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) * log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) -
      ((614957911641027380121625534795725665450474510578150517517364565575/433966189866678990728641332227383042332365733993375514455103140072 : ℝ) * log ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) + (-78414434095179119630640082044519191911143475682800571640730057466/71376018070177465580368640168977474067823311512068341193273542775 : ℝ) * log 2 + (-112794135764039739491153575010105589545575034762290288393445070203550740400937/201473314211828189203495443103009508281087523083631007759852744566070285855000 : ℝ)) := by
    have e : (25222766121242371396566607344567136481825368823608124674926863177825474574495396509876835651726629813342964515906913900114037/362651965581290740566291797585417114905957541550535813967734940218926514539000000000000000000000000000000000000000000000000000 : ℝ) = (11394342831883648209498223/10000000000000000000000000 : ℝ) * (31845373111853461581024721/100000000000000000000000000 : ℝ) - (((614957911641027380121625534795725665450474510578150517517364565575/433966189866678990728641332227383042332365733993375514455103140072 : ℝ) : ℝ) * (14242928539854560261872779/12500000000000000000000000 : ℝ) + ((-78414434095179119630640082044519191911143475682800571640730057466/71376018070177465580368640168977474067823311512068341193273542775 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-112794135764039739491153575010105589545575034762290288393445070203550740400937/201473314211828189203495443103009508281087523083631007759852744566070285855000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (25222766121242371396566607344567136481825368823608124674926863177825474574495396509876835651726629813342964515906913900114037/362651965581290740566291797585417114905957541550535813967734940218926514539000000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (4198378289448831767/50000000000000000000 : ℝ) ≤ (25222766121242371396566607344567136481825368823608124674926863177825474574495396509876835651726629813342964515906913900114037/362651965581290740566291797585417114905957541550535813967734940218926514539000000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (25222766121242371396566607344567136481825368823608124674926863177825474574495396509876835651726629813342964515906913900114037/362651965581290740566291797585417114905957541550535813967734940218926514539000000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 37 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[211/100, 107/50]`. -/
private theorem b9_pan_37 : (118541113295193778003/200000000000000000000000 : ℝ) ≤ ∫ t in (211/100 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (4198378289448831767/50000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((211/100 : ℝ) + (107/50 : ℝ)) / 2) := b9_sig_37
  have hB0 : ((log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (12302835330980087543/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_37.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) ≤ (15922686555926730790512361/50000000000000000000000000 : ℝ) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 2) / 3) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (15922686555926730790512361/50000000000000000000000000 : ℝ) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (15922686555926730790512361/50000000000000000000000000 : ℝ) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (15922686555926730790512361/50000000000000000000000000 : ℝ) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (15922686555926730790512361/50000000000000000000000000 : ℝ) / ((((211/100 : ℝ) + (107/50 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (12302835330980087543/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (211/100 : ℝ) (107/50 : ℝ), 2 * (2671622448820646257/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_37.2.2.1
    have hX : (9032871567199354201826781097/20700000000000000000000000000 : ℝ) ≤ (1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (9032871567199354201826781097/20700000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((107/50 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2671622448820646257/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (9032871567199354201826781097/20700000000000000000000000000 : ℝ) / ((107/50 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2671622448820646257/100000000000000000000 : ℝ) ≤ ((1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) / ((107/50 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2671622448820646257/100000000000000000000 : ℝ) ≤ (9032871567199354201826781097/20700000000000000000000000000 : ℝ) / ((107/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (9032871567199354201826781097/20700000000000000000000000000 : ℝ) / ((107/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) / ((107/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) / ((107/50 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) / ((107/50 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((107/50 : ℝ) + 2) * ((107/50 : ℝ) + 1) - log (((107/50 : ℝ) + 2) / 3)) / ((107/50 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (211/100 : ℝ)) (b := (107/50 : ℝ)) (C := (2671622448820646257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (107/50 : ℝ) - (211/100 : ℝ) ≤ (((211/100 : ℝ) + (107/50 : ℝ)) / 2) * log ((107/50 : ℝ) / (211/100 : ℝ)) := by
    have hl := b9_lgs_37.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (211/100 : ℝ)) (b := (107/50 : ℝ)) (m := (((211/100 : ℝ) + (107/50 : ℝ)) / 2)) (A := (4198378289448831767/50000000000000000000 : ℝ)) (B := (12302835330980087543/100000000000000000000 : ℝ)) (C := (2671622448820646257/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_37.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 38 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_38 :
    ((1148988495993176479825523/1000000000000000000000000 : ℝ) ≤ log ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) ∧ log ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) ≤ (57449424799658823991276151/50000000000000000000000000 : ℝ)) ∧
    ((32570013963930182241618251/100000000000000000000000000 : ℝ) ≤ log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) ∧ log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) ≤ (8142503490982545560404563/25000000000000000000000000 : ℝ)) ∧
    (log (((217/100 : ℝ) + 2) / 3) ≤ (32930374714260038915280201/100000000000000000000000000 : ℝ)) ∧
    ((348033462965201707822153/25000000000000000000000000 : ℝ) ≤ log ((217/100 : ℝ) / (107/50 : ℝ)) ∧ log ((217/100 : ℝ) / (107/50 : ℝ)) ≤ (1392133851860806831288613/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) = (631/200 : ℝ) by norm_num]
    have hkey : log (631/200 : ℝ) = log (2 : ℝ) + log (631/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (631/400 : ℝ)) (x := (231/1031 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23).1
    have hnum : (227920657716615585204145439271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 23, (231/1031 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) = (631/200 : ℝ) by norm_num]
    have hkey : log (631/200 : ℝ) = log (2 : ℝ) + log (631/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (631/400 : ℝ)) (x := (231/1031 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23).2
    have hnum : 2 * (∑ i ∈ Finset.range 23, (231/1031 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((231/1031 : ℝ) ^ (2 * 23 + 1) / (1 - (231/1031 : ℝ) ^ 2)) ≤ (455841315433231170408290898541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) = (277/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (277/200 : ℝ)) (x := (77/477 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (32570013963930182241618251/100000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (77/477 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) = (277/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (277/200 : ℝ)) (x := (77/477 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (77/477 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((77/477 : ℝ) ^ (2 * 19 + 1) / (1 - (77/477 : ℝ) ^ 2)) ≤ (8142503490982545560404563/25000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((217/100 : ℝ) + 2) / 3) = (139/100 : ℝ) by norm_num]
    have h := (log_enclosure (y := (139/100 : ℝ)) (x := (39/239 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (39/239 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((39/239 : ℝ) ^ (2 * 19 + 1) / (1 - (39/239 : ℝ) ^ 2)) ≤ (32930374714260038915280201/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((217/100 : ℝ) / (107/50 : ℝ)) = (217/214 : ℝ) by norm_num]
    have h := (log_enclosure (y := (217/214 : ℝ)) (x := (3/431 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (348033462965201707822153/25000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/431 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((217/100 : ℝ) / (107/50 : ℝ)) = (217/214 : ℝ) by norm_num]
    have h := (log_enclosure (y := (217/214 : ℝ)) (x := (3/431 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/431 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/431 : ℝ) ^ (2 * 7 + 1) / (1 - (3/431 : ℝ) ^ 2)) ≤ (1392133851860806831288613/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 38, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_38 : (2192064727300026747/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((107/50 : ℝ) + (217/100 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2)) (c := ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1)) (m := (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 33
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) - 1 = ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1)) (m := (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_38.1
  have hq := b9_lgs_38.2.1
  have hprod : (1148988495993176479825523/1000000000000000000000000 : ℝ) * (32570013963930182241618251/100000000000000000000000000 : ℝ) ≤ log ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) * log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((111658061342909494095822321993775462089737130175767773027687601383321768820005652258424251819728400439034747552079377/78394438170819670839269972240454578854468661201293067686891896892427927823204788695369718115506153950149086801773800 : ℝ) : ℝ) * log ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) ≤ ((111658061342909494095822321993775462089737130175767773027687601383321768820005652258424251819728400439034747552079377/78394438170819670839269972240454578854468661201293067686891896892427927823204788695369718115506153950149086801773800 : ℝ) : ℝ) * (57449424799658823991276151/50000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-430624909418644571848200438131947261686747526082365157918565751479361098588153838692219934438751582257400501179246/391972190854098354196349861202272894272343306006465338434459484462139639116023943476848590577530769750745434008869 : ℝ) : ℝ) * log 2 ≤ ((-430624909418644571848200438131947261686747526082365157918565751479361098588153838692219934438751582257400501179246/391972190854098354196349861202272894272343306006465338434459484462139639116023943476848590577530769750745434008869 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (247168509068686168040215157371384487780700163048049706096052442404020475285740925359068137911018536123337060139848017600271999233285062220844858279936845267683888719908351/3403209295022851482114557161025338646981594941830357628799632947417915387429051170585808209265336404604574986046681273028700000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) * log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) -
      ((111658061342909494095822321993775462089737130175767773027687601383321768820005652258424251819728400439034747552079377/78394438170819670839269972240454578854468661201293067686891896892427927823204788695369718115506153950149086801773800 : ℝ) * log ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) + (-430624909418644571848200438131947261686747526082365157918565751479361098588153838692219934438751582257400501179246/391972190854098354196349861202272894272343306006465338434459484462139639116023943476848590577530769750745434008869 : ℝ) * log 2 + (-2956771606584524085172073369819151014861070664961325407824773640172898634053996782282117326645065772537875182038368954440779/5156377719731593154719026001553543404517568093682360043635807496087750587013713894826982135250509703946325736434365565195000 : ℝ)) := by
    have e : (247168509068686168040215157371384487780700163048049706096052442404020475285740925359068137911018536123337060139848017600271999233285062220844858279936845267683888719908351/3403209295022851482114557161025338646981594941830357628799632947417915387429051170585808209265336404604574986046681273028700000000000000000000000000000000000000000000000000 : ℝ) = (1148988495993176479825523/1000000000000000000000000 : ℝ) * (32570013963930182241618251/100000000000000000000000000 : ℝ) - (((111658061342909494095822321993775462089737130175767773027687601383321768820005652258424251819728400439034747552079377/78394438170819670839269972240454578854468661201293067686891896892427927823204788695369718115506153950149086801773800 : ℝ) : ℝ) * (57449424799658823991276151/50000000000000000000000000 : ℝ) + ((-430624909418644571848200438131947261686747526082365157918565751479361098588153838692219934438751582257400501179246/391972190854098354196349861202272894272343306006465338434459484462139639116023943476848590577530769750745434008869 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-2956771606584524085172073369819151014861070664961325407824773640172898634053996782282117326645065772537875182038368954440779/5156377719731593154719026001553543404517568093682360043635807496087750587013713894826982135250509703946325736434365565195000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (247168509068686168040215157371384487780700163048049706096052442404020475285740925359068137911018536123337060139848017600271999233285062220844858279936845267683888719908351/3403209295022851482114557161025338646981594941830357628799632947417915387429051170585808209265336404604574986046681273028700000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (2192064727300026747/25000000000000000000 : ℝ) ≤ (247168509068686168040215157371384487780700163048049706096052442404020475285740925359068137911018536123337060139848017600271999233285062220844858279936845267683888719908351/3403209295022851482114557161025338646981594941830357628799632947417915387429051170585808209265336404604574986046681273028700000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (247168509068686168040215157371384487780700163048049706096052442404020475285740925359068137911018536123337060139848017600271999233285062220844858279936845267683888719908351/3403209295022851482114557161025338646981594941830357628799632947417915387429051170585808209265336404604574986046681273028700000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 38 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[107/50, 217/100]`. -/
private theorem b9_pan_38 : (305156411378729513511/500000000000000000000000 : ℝ) ≤ ∫ t in (107/50 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (2192064727300026747/25000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((107/50 : ℝ) + (217/100 : ℝ)) / 2) := b9_sig_38
  have hB0 : ((log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (12463139968387234053/100000000000000000000 : ℝ) := by
    have hp := b9_lgs_38.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) ≤ (8142503490982545560404563/25000000000000000000000000 : ℝ) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 2) / 3) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (8142503490982545560404563/25000000000000000000000000 : ℝ) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (8142503490982545560404563/25000000000000000000000000 : ℝ) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (8142503490982545560404563/25000000000000000000000000 : ℝ) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (8142503490982545560404563/25000000000000000000000000 : ℝ) / ((((107/50 : ℝ) + (217/100 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (12463139968387234053/100000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (107/50 : ℝ) (217/100 : ℝ), 2 * (647090276776703939/25000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_38.2.2.1
    have hX : (17968033744153563772328156183/41700000000000000000000000000 : ℝ) ≤ (1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (17968033744153563772328156183/41700000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((217/100 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (647090276776703939/25000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (17968033744153563772328156183/41700000000000000000000000000 : ℝ) / ((217/100 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (647090276776703939/25000000000000000000 : ℝ) ≤ ((1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) / ((217/100 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (647090276776703939/25000000000000000000 : ℝ) ≤ (17968033744153563772328156183/41700000000000000000000000000 : ℝ) / ((217/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (17968033744153563772328156183/41700000000000000000000000000 : ℝ) / ((217/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) / ((217/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) / ((217/100 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) / ((217/100 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((217/100 : ℝ) + 2) * ((217/100 : ℝ) + 1) - log (((217/100 : ℝ) + 2) / 3)) / ((217/100 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (107/50 : ℝ)) (b := (217/100 : ℝ)) (C := (647090276776703939/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (217/100 : ℝ) - (107/50 : ℝ) ≤ (((107/50 : ℝ) + (217/100 : ℝ)) / 2) * log ((217/100 : ℝ) / (107/50 : ℝ)) := by
    have hl := b9_lgs_38.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (107/50 : ℝ)) (b := (217/100 : ℝ)) (m := (((107/50 : ℝ) + (217/100 : ℝ)) / 2)) (A := (2192064727300026747/25000000000000000000 : ℝ)) (B := (12463139968387234053/100000000000000000000 : ℝ)) (C := (647090276776703939/25000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_38.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

/-- Log bounds for panel 39 of the `[1, 11/5]` quadrature. -/
private theorem b9_lgs_39 :
    ((115845228902412666881097789/100000000000000000000000000 : ℝ) ≤ log ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) ∧ log ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) ≤ (115845228902412666881097791/100000000000000000000000000 : ℝ)) ∧
    ((4161180190916611890830497/12500000000000000000000000 : ℝ) ≤ log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) ∧ log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) ≤ (33289441527332895126643977/100000000000000000000000000 : ℝ)) ∧
    (log (((11/5 : ℝ) + 2) / 3) ≤ (16823611831060646525229671/50000000000000000000000000 : ℝ)) ∧
    ((85813705074387415391563/6250000000000000000000000 : ℝ) ≤ log ((11/5 : ℝ) / (217/100 : ℝ)) ∧ log ((11/5 : ℝ) / (217/100 : ℝ)) ≤ (1373019281190198646265009/100000000000000000000000000 : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · rw [show ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) = (637/200 : ℝ) by norm_num]
    have hkey : log (637/200 : ℝ) = log (2 : ℝ) + log (637/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (637/400 : ℝ)) (x := (237/1037 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 24).1
    have hnum : (232652554232090679696872884271/500000000000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 24, (237/1037 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.1]
  · rw [show ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) = (637/200 : ℝ) by norm_num]
    have hkey : log (637/200 : ℝ) = log (2 : ℝ) + log (637/400 : ℝ) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [hkey]
    have h := (log_enclosure (y := (637/400 : ℝ)) (x := (237/1037 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 24).2
    have hnum : 2 * (∑ i ∈ Finset.range 24, (237/1037 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((237/1037 : ℝ) ^ (2 * 24 + 1) / (1 - (237/1037 : ℝ) ^ 2)) ≤ (465305108464181359393745788541/1000000000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith [b9_log_two_tight.2]
  · rw [show (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) = (279/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (279/200 : ℝ)) (x := (79/479 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).1
    have hnum : (4161180190916611890830497/12500000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 19, (79/479 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) = (279/200 : ℝ) by norm_num]
    have h := (log_enclosure (y := (279/200 : ℝ)) (x := (79/479 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (79/479 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((79/479 : ℝ) ^ (2 * 19 + 1) / (1 - (79/479 : ℝ) ^ 2)) ≤ (33289441527332895126643977/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show (((11/5 : ℝ) + 2) / 3) = (7/5 : ℝ) by norm_num]
    have h := (log_enclosure (y := (7/5 : ℝ)) (x := (1/6 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 19).2
    have hnum : 2 * (∑ i ∈ Finset.range 19, (1/6 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((1/6 : ℝ) ^ (2 * 19 + 1) / (1 - (1/6 : ℝ) ^ 2)) ≤ (16823611831060646525229671/50000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((11/5 : ℝ) / (217/100 : ℝ)) = (220/217 : ℝ) by norm_num]
    have h := (log_enclosure (y := (220/217 : ℝ)) (x := (3/437 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).1
    have hnum : (85813705074387415391563/6250000000000000000000000 : ℝ) ≤ 2 * (∑ i ∈ Finset.range 7, (3/437 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) := by
      norm_num [Finset.sum_range_succ]
    linarith
  · rw [show ((11/5 : ℝ) / (217/100 : ℝ)) = (220/217 : ℝ) by norm_num]
    have h := (log_enclosure (y := (220/217 : ℝ)) (x := (3/437 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 7).2
    have hnum : 2 * (∑ i ∈ Finset.range 7, (3/437 : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) + 2 * ((3/437 : ℝ) ^ (2 * 7 + 1) / (1 - (3/437 : ℝ) ^ 2)) ≤ (1373019281190198646265009/100000000000000000000000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    linarith

set_option maxHeartbeats 4000000 in
/-- `sigma0` at the midpoint of panel 39, from the atanh series for `log v/(v+1)`. -/
private theorem b9_sig_39 : (9144495010572847821/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((217/100 : ℝ) + (11/5 : ℝ)) / 2) := by
  have hlow := sigma_lower_bound (a := 3) (b := ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2)) (c := ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1)) (m := (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 3) / 2))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 33
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) - 1 = ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1)) (m := (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 3) / 2)) (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  ring_nf at hlow
  have hp := b9_lgs_39.1
  have hq := b9_lgs_39.2.1
  have hprod : (115845228902412666881097789/100000000000000000000000000 : ℝ) * (4161180190916611890830497/12500000000000000000000000 : ℝ) ≤ log ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) * log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) := by
    refine mul_le_mul hp.1 hq.1 (by norm_num) (by linarith [hp.1])
  have hA1 : ((1982121440483345057723324836641508318107820201369819879691022340325707733975233309029140550898509549792456028013257/1384641454476570422890746089088758890529167581959113096899185283969397395841121285828465511804242163591476710446840 : ℝ) : ℝ) * log ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) ≤ ((1982121440483345057723324836641508318107820201369819879691022340325707733975233309029140550898509549792456028013257/1384641454476570422890746089088758890529167581959113096899185283969397395841121285828465511804242163591476710446840 : ℝ) : ℝ) * (115845228902412666881097791/100000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hp.2 (by norm_num)
  have hA4 : ((-3460689125375653578126466349512970736203907459037563985423386829141658049365238431383937684405767115721759869084374/3150059308934197712076447352676926475953856248956982295445646521030379075538550925259759039354650922170609516266561 : ℝ) : ℝ) * log 2 ≤ ((-3460689125375653578126466349512970736203907459037563985423386829141658049365238431383937684405767115721759869084374/3150059308934197712076447352676926475953856248956982295445646521030379075538550925259759039354650922170609516266561 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) :=
    mul_le_mul_of_nonpos_left b9_log_two_tight.1 (by norm_num)
  have hV : (73848205825892437677021712182984032688029546535566218697532254898211125857608617144762988390936770240143227112732540904216769323278129598136776540414584670669473330057320049/974965183546931760883297686854977378949504735423419244537517489247812006187821091481577577930041277539496802566764941187566250000000000000000000000000000000000000000000000000 : ℝ) ≤ log ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) * log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) -
      ((1982121440483345057723324836641508318107820201369819879691022340325707733975233309029140550898509549792456028013257/1384641454476570422890746089088758890529167581959113096899185283969397395841121285828465511804242163591476710446840 : ℝ) * log ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) + (-3460689125375653578126466349512970736203907459037563985423386829141658049365238431383937684405767115721759869084374/3150059308934197712076447352676926475953856248956982295445646521030379075538550925259759039354650922170609516266561 : ℝ) * log 2 + (-20600635951823007092362117109239413441751568044240386522544666545032380356304719436005559243777835857764409475524341900698435147/35098746607689543391798716726779185642182170475243092803350629612921232222761559293336792805481485991421884892403537882752385000 : ℝ)) := by
    have e : (73848205825892437677021712182984032688029546535566218697532254898211125857608617144762988390936770240143227112732540904216769323278129598136776540414584670669473330057320049/974965183546931760883297686854977378949504735423419244537517489247812006187821091481577577930041277539496802566764941187566250000000000000000000000000000000000000000000000000 : ℝ) = (115845228902412666881097789/100000000000000000000000000 : ℝ) * (4161180190916611890830497/12500000000000000000000000 : ℝ) - (((1982121440483345057723324836641508318107820201369819879691022340325707733975233309029140550898509549792456028013257/1384641454476570422890746089088758890529167581959113096899185283969397395841121285828465511804242163591476710446840 : ℝ) : ℝ) * (115845228902412666881097791/100000000000000000000000000 : ℝ) + ((-3460689125375653578126466349512970736203907459037563985423386829141658049365238431383937684405767115721759869084374/3150059308934197712076447352676926475953856248956982295445646521030379075538550925259759039354650922170609516266561 : ℝ) : ℝ) * (346573590279972654708616060729/500000000000000000000000000000 : ℝ) + ((-20600635951823007092362117109239413441751568044240386522544666545032380356304719436005559243777835857764409475524341900698435147/35098746607689543391798716726779185642182170475243092803350629612921232222761559293336792805481485991421884892403537882752385000 : ℝ) : ℝ)) := by norm_num
    rw [e]
    linarith [hprod, hA1, hA4]
  have hsig : (73848205825892437677021712182984032688029546535566218697532254898211125857608617144762988390936770240143227112732540904216769323278129598136776540414584670669473330057320049/974965183546931760883297686854977378949504735423419244537517489247812006187821091481577577930041277539496802566764941187566250000000000000000000000000000000000000000000000000 : ℝ) ≤ Wu04Integral.sigma 3 ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) := by linarith [hV, hlow]
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
  unfold Wu04Integral.sigma0
  refine le_trans ?_ (div_le_div_of_nonneg_right hsig hKpos.le)
  calc (9144495010572847821/100000000000000000000 : ℝ) ≤ (73848205825892437677021712182984032688029546535566218697532254898211125857608617144762988390936770240143227112732540904216769323278129598136776540414584670669473330057320049/974965183546931760883297686854977378949504735423419244537517489247812006187821091481577577930041277539496802566764941187566250000000000000000000000000000000000000000000000000 : ℝ) / (165661317/200000000 : ℝ) := by norm_num
    _ ≤ (73848205825892437677021712182984032688029546535566218697532254898211125857608617144762988390936770240143227112732540904216769323278129598136776540414584670669473330057320049/974965183546931760883297686854977378949504735423419244537517489247812006187821091481577577930041277539496802566764941187566250000000000000000000000000000000000000000000000000 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- Panel 39 of the `[1, 11/5]` quadrature: `∫ sigma0 t/(2t)` over `[217/100, 11/5]`. -/
private theorem b9_pan_39 : (156940394048333756457/250000000000000000000000 : ℝ) ≤ ∫ t in (217/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hA0 : (9144495010572847821/100000000000000000000 : ℝ) ≤ Wu04Integral.sigma0 (((217/100 : ℝ) + (11/5 : ℝ)) / 2) := b9_sig_39
  have hB0 : ((log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1)) / (1 - Wu04Integral.sigma 3 5 4)) ≤ (1261844862770250587/10000000000000000000 : ℝ) := by
    have hp := b9_lgs_39.2.1.2
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKl : (33132263/40000000 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have h1 : log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) ≤ (33289441527332895126643977/100000000000000000000000000 : ℝ) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) := div_le_div_of_nonneg_right hp (by norm_num)
    have h1' : log (((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 2) / 3) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (33289441527332895126643977/100000000000000000000000000 : ℝ) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) := div_le_div_of_nonneg_right h1 hKpos.le
    have h2 : (33289441527332895126643977/100000000000000000000000000 : ℝ) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) / (1 - Wu04Integral.sigma 3 5 4) ≤ (33289441527332895126643977/100000000000000000000000000 : ℝ) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKl
    have h3 : (33289441527332895126643977/100000000000000000000000000 : ℝ) / ((((217/100 : ℝ) + (11/5 : ℝ)) / 2) + 1) / (33132263/40000000 : ℝ) ≤ (1261844862770250587/10000000000000000000 : ℝ) := by norm_num
    linarith [h1', h2, h3]
  have hC0 : ∀ s ∈ Set.Icc (217/100 : ℝ) (11/5 : ℝ), 2 * (2507896580782439361/100000000000000000000 : ℝ) ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
    have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
    have hKle : 1 - Wu04Integral.sigma 3 5 4 ≤ 1 := by linarith [sigma_3_5_4_bounds_exact.1]
    have hb3 := b9_lgs_39.2.2.1
    have hX : (446704151547726422970176909/1050000000000000000000000000 : ℝ) ≤ (1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) := by linarith
    have hXpos : (0 : ℝ) < (1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) := by linarith
    have hxa : (0 : ℝ) < (446704151547726422970176909/1050000000000000000000000000 : ℝ) := by norm_num
    have hden : (0 : ℝ) < ((11/5 : ℝ) + 1) ^ 2 := by positivity
    have hval1 : 2 * (2507896580782439361/100000000000000000000 : ℝ) * (165661317/200000000 : ℝ) ≤ (446704151547726422970176909/1050000000000000000000000000 : ℝ) / ((11/5 : ℝ) + 1) ^ 2 := by norm_num
    have hmain : 2 * (2507896580782439361/100000000000000000000 : ℝ) ≤ ((1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) / ((11/5 : ℝ) + 1) ^ 2) / (1 - Wu04Integral.sigma 3 5 4) := by
      have g1 : 2 * (2507896580782439361/100000000000000000000 : ℝ) ≤ (446704151547726422970176909/1050000000000000000000000000 : ℝ) / ((11/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ))]
        linarith [hval1]
      have gX : (446704151547726422970176909/1050000000000000000000000000 : ℝ) / ((11/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) / ((11/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hX hden.le) (by norm_num)
      have hXD : (0 : ℝ) ≤ (1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) / ((11/5 : ℝ) + 1) ^ 2 :=
        div_nonneg hXpos.le hden.le
      have g4 : (1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) / ((11/5 : ℝ) + 1) ^ 2 / (165661317/200000000 : ℝ) ≤ (1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) - log (((11/5 : ℝ) + 2) / 3)) / ((11/5 : ℝ) + 1) ^ 2 / (1 - Wu04Integral.sigma 3 5 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < (165661317/200000000 : ℝ)) hKpos]
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (165661317/200000000 : ℝ) := by linarith [sigma_3_5_4_bounds_exact.1]
        exact mul_le_mul_of_nonneg_left hKhi hXD
      linarith [g1, gX, g4]
    exact sigma0_second_lower_sharp (a := (217/100 : ℝ)) (b := (11/5 : ℝ)) (C := (2507896580782439361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) hXpos hmain
  have hL0 : (11/5 : ℝ) - (217/100 : ℝ) ≤ (((217/100 : ℝ) + (11/5 : ℝ)) / 2) * log ((11/5 : ℝ) / (217/100 : ℝ)) := by
    have hl := b9_lgs_39.2.2.2.1
    nlinarith [hl]
  have h := sigma0_mid_panel (a := (217/100 : ℝ)) (b := (11/5 : ℝ)) (m := (((217/100 : ℝ) + (11/5 : ℝ)) / 2)) (A := (9144495010572847821/100000000000000000000 : ℝ)) (B := (1261844862770250587/10000000000000000000 : ℝ)) (C := (2507896580782439361/100000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA0 hB0 hC0 hL0
  have hlr := b9_lgs_39.2.2.2
  norm_num at h
  linarith [h, hlr.1, hlr.2]

set_option maxHeartbeats 4000000 in
/-- `∫ sigma0 t/(2t)` on `[1, 11/5]`, from the 40 midpoint panels. -/
private theorem b9_I_sigma :
    ((5597961931220961137453/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have e1 : (∫ t in (1 : ℝ)..(53/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(103/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (103/100 : ℝ)..(53/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e2 : (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(53/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (53/50 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e3 : (∫ t in (1 : ℝ)..(28/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (109/100 : ℝ)..(28/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e4 : (∫ t in (1 : ℝ)..(23/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(28/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (28/25 : ℝ)..(23/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e5 : (∫ t in (1 : ℝ)..(59/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(23/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (23/20 : ℝ)..(59/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e6 : (∫ t in (1 : ℝ)..(121/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(59/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (59/50 : ℝ)..(121/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e7 : (∫ t in (1 : ℝ)..(31/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(121/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (121/100 : ℝ)..(31/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e8 : (∫ t in (1 : ℝ)..(127/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(31/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (31/25 : ℝ)..(127/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e9 : (∫ t in (1 : ℝ)..(13/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(127/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (127/100 : ℝ)..(13/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e10 : (∫ t in (1 : ℝ)..(133/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(13/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (13/10 : ℝ)..(133/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e11 : (∫ t in (1 : ℝ)..(34/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(133/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (133/100 : ℝ)..(34/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e12 : (∫ t in (1 : ℝ)..(139/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(34/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (34/25 : ℝ)..(139/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e13 : (∫ t in (1 : ℝ)..(71/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(139/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (139/100 : ℝ)..(71/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e14 : (∫ t in (1 : ℝ)..(29/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(71/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (71/50 : ℝ)..(29/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e15 : (∫ t in (1 : ℝ)..(37/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(29/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (29/20 : ℝ)..(37/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e16 : (∫ t in (1 : ℝ)..(151/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(37/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (37/25 : ℝ)..(151/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e17 : (∫ t in (1 : ℝ)..(77/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(151/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (151/100 : ℝ)..(77/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e18 : (∫ t in (1 : ℝ)..(157/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(77/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (77/50 : ℝ)..(157/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e19 : (∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(157/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (157/100 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e20 : (∫ t in (1 : ℝ)..(163/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (8/5 : ℝ)..(163/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e21 : (∫ t in (1 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(163/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (163/100 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e22 : (∫ t in (1 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (83/50 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e23 : (∫ t in (1 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (169/100 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e24 : (∫ t in (1 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (43/25 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e25 : (∫ t in (1 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (7/4 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e26 : (∫ t in (1 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (89/50 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e27 : (∫ t in (1 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (181/100 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e28 : (∫ t in (1 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (46/25 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e29 : (∫ t in (1 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (187/100 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e30 : (∫ t in (1 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (19/10 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e31 : (∫ t in (1 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (193/100 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e32 : (∫ t in (1 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (49/25 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e33 : (∫ t in (1 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (199/100 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e34 : (∫ t in (1 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (101/50 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e35 : (∫ t in (1 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (41/20 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e36 : (∫ t in (1 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (52/25 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e37 : (∫ t in (1 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (211/100 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e38 : (∫ t in (1 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (107/50 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have e39 : (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (1 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (217/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))
      (sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num))).symm
  have a0 : (436247405734118921/1000000000000000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(103/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := b9_pan_0
  have a1 : ((3394388377875562523/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(53/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((3394388377875562523/1000000000000000000000000 : ℝ) : ℝ) ≤ ((436247405734118921/1000000000000000000000000 : ℝ) : ℝ) + (1479070486070721801/500000000000000000000000 : ℝ) := by norm_num
    rw [e1]
    linarith [a0, b9_pan_1, hprev]
  have a2 : ((11115678965699436453/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((11115678965699436453/1000000000000000000000000 : ℝ) : ℝ) ≤ ((3394388377875562523/1000000000000000000000000 : ℝ) : ℝ) + (772129058782387393/100000000000000000000000 : ℝ) := by norm_num
    rw [e2]
    linarith [a1, b9_pan_2, hprev]
  have a3 : ((511392376732078367/20000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(28/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((511392376732078367/20000000000000000000000 : ℝ) : ℝ) ≤ ((11115678965699436453/1000000000000000000000000 : ℝ) : ℝ) + (14453939870904481897/1000000000000000000000000 : ℝ) := by norm_num
    rw [e3]
    linarith [a2, b9_pan_3, hprev]
  have a4 : ((24243398876198195423/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(23/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((24243398876198195423/500000000000000000000000 : ℝ) : ℝ) ≤ ((511392376732078367/20000000000000000000000 : ℝ) : ℝ) + (1432323682237029531/62500000000000000000000 : ℝ) := by norm_num
    rw [e4]
    linarith [a3, b9_pan_4, hprev]
  have a5 : ((20346819125072545043/250000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(59/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((20346819125072545043/250000000000000000000000 : ℝ) : ℝ) ≤ ((24243398876198195423/500000000000000000000000 : ℝ) : ℝ) + (16450239373946894663/500000000000000000000000 : ℝ) := by norm_num
    rw [e5]
    linarith [a4, b9_pan_5, hprev]
  have a6 : ((12560519136344612399/100000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(121/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((12560519136344612399/100000000000000000000000 : ℝ) : ℝ) ≤ ((20346819125072545043/250000000000000000000000 : ℝ) : ℝ) + (22108957431577971909/500000000000000000000000 : ℝ) := by norm_num
    rw [e6]
    linarith [a5, b9_pan_6, hprev]
  have a7 : ((182310151730049183507/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(31/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((182310151730049183507/1000000000000000000000000 : ℝ) : ℝ) ≤ ((12560519136344612399/100000000000000000000000 : ℝ) : ℝ) + (56704960366603059517/1000000000000000000000000 : ℝ) := by norm_num
    rw [e7]
    linarith [a6, b9_pan_7, hprev]
  have a8 : ((252525903935321311521/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(127/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((252525903935321311521/1000000000000000000000000 : ℝ) : ℝ) ≤ ((182310151730049183507/1000000000000000000000000 : ℝ) : ℝ) + (35107876102636064007/500000000000000000000000 : ℝ) := by norm_num
    rw [e8]
    linarith [a7, b9_pan_8, hprev]
  have a9 : ((67429331212763506991/200000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(13/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((67429331212763506991/200000000000000000000000 : ℝ) : ℝ) ≤ ((252525903935321311521/1000000000000000000000000 : ℝ) : ℝ) + (42310376064248111717/500000000000000000000000 : ℝ) := by norm_num
    rw [e9]
    linarith [a8, b9_pan_9, hprev]
  have a10 : ((218475697236591507139/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(133/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((218475697236591507139/500000000000000000000000 : ℝ) : ℝ) ≤ ((67429331212763506991/200000000000000000000000 : ℝ) : ℝ) + (99804738409365479323/1000000000000000000000000 : ℝ) := by norm_num
    rw [e10]
    linarith [a9, b9_pan_10, hprev]
  have a11 : ((138154117583431122827/250000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(34/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((138154117583431122827/250000000000000000000000 : ℝ) : ℝ) ≤ ((218475697236591507139/500000000000000000000000 : ℝ) : ℝ) + (11566507586054147703/100000000000000000000000 : ℝ) := by norm_num
    rw [e11]
    linarith [a10, b9_pan_11, hprev]
  have a12 : ((342363345621776261809/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(139/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((342363345621776261809/500000000000000000000000 : ℝ) : ℝ) ≤ ((138154117583431122827/250000000000000000000000 : ℝ) : ℝ) + (13211022090982803231/100000000000000000000000 : ℝ) := by norm_num
    rw [e12]
    linarith [a11, b9_pan_12, hprev]
  have a13 : ((833785117194767150799/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(71/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((833785117194767150799/1000000000000000000000000 : ℝ) : ℝ) ≤ ((342363345621776261809/500000000000000000000000 : ℝ) : ℝ) + (149058425951214627181/1000000000000000000000000 : ℝ) := by norm_num
    rw [e13]
    linarith [a12, b9_pan_13, hprev]
  have a14 : ((1000221730423737654261/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(29/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1000221730423737654261/1000000000000000000000000 : ℝ) : ℝ) ≤ ((833785117194767150799/1000000000000000000000000 : ℝ) : ℝ) + (83218306614485251731/500000000000000000000000 : ℝ) := by norm_num
    rw [e14]
    linarith [a13, b9_pan_14, hprev]
  have a15 : ((148050140482339701173/125000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(37/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((148050140482339701173/125000000000000000000000 : ℝ) : ℝ) ≤ ((1000221730423737654261/1000000000000000000000000 : ℝ) : ℝ) + (184179393434979955123/1000000000000000000000000 : ℝ) := by norm_num
    rw [e15]
    linarith [a14, b9_pan_15, hprev]
  have a16 : ((693314666043425116987/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(151/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((693314666043425116987/500000000000000000000000 : ℝ) : ℝ) ≤ ((148050140482339701173/125000000000000000000000 : ℝ) : ℝ) + (20222820822813262459/100000000000000000000000 : ℝ) := by norm_num
    rw [e16]
    linarith [a15, b9_pan_16, hprev]
  have a17 : ((1607159911282492754403/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(77/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1607159911282492754403/1000000000000000000000000 : ℝ) : ℝ) ≤ ((693314666043425116987/500000000000000000000000 : ℝ) : ℝ) + (220530579195642520429/1000000000000000000000000 : ℝ) := by norm_num
    rw [e17]
    linarith [a16, b9_pan_17, hprev]
  have a18 : ((1846199359791071693707/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(157/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1846199359791071693707/1000000000000000000000000 : ℝ) : ℝ) ≤ ((1607159911282492754403/1000000000000000000000000 : ℝ) : ℝ) + (29879931063572367413/125000000000000000000000 : ℝ) := by norm_num
    rw [e18]
    linarith [a17, b9_pan_18, hprev]
  have a19 : ((2103911958578653483949/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(8/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((2103911958578653483949/1000000000000000000000000 : ℝ) : ℝ) ≤ ((1846199359791071693707/1000000000000000000000000 : ℝ) : ℝ) + (128856299393790895121/500000000000000000000000 : ℝ) := by norm_num
    rw [e19]
    linarith [a18, b9_pan_19, hprev]
  have a20 : ((1190212050077887411839/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(163/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1190212050077887411839/500000000000000000000000 : ℝ) : ℝ) ≤ ((2103911958578653483949/1000000000000000000000000 : ℝ) : ℝ) + (276512141577121339729/1000000000000000000000000 : ℝ) := by norm_num
    rw [e20]
    linarith [a19, b9_pan_20, hprev]
  have a21 : ((535165633110672147937/200000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(83/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((535165633110672147937/200000000000000000000000 : ℝ) : ℝ) ≤ ((1190212050077887411839/500000000000000000000000 : ℝ) : ℝ) + (295404065397585916007/1000000000000000000000000 : ℝ) := by norm_num
    rw [e21]
    linarith [a20, b9_pan_21, hprev]
  have a22 : ((1495093000606672839547/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(169/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1495093000606672839547/500000000000000000000000 : ℝ) : ℝ) ≤ ((535165633110672147937/200000000000000000000000 : ℝ) : ℝ) + (314357835659984939409/1000000000000000000000000 : ℝ) := by norm_num
    rw [e22]
    linarith [a21, b9_pan_22, hprev]
  have a23 : ((3323532041046650691331/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(43/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((3323532041046650691331/1000000000000000000000000 : ℝ) : ℝ) ≤ ((1495093000606672839547/500000000000000000000000 : ℝ) : ℝ) + (333346039833305012237/1000000000000000000000000 : ℝ) := by norm_num
    rw [e23]
    linarith [a22, b9_pan_23, hprev]
  have a24 : ((735175222646550854443/200000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(7/4 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((735175222646550854443/200000000000000000000000 : ℝ) : ℝ) ≤ ((3323532041046650691331/1000000000000000000000000 : ℝ) : ℝ) + (88086018046525895221/250000000000000000000000 : ℝ) := by norm_num
    rw [e24]
    linarith [a23, b9_pan_24, hprev]
  have a25 : ((4047205966444215998823/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(89/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((4047205966444215998823/1000000000000000000000000 : ℝ) : ℝ) ≤ ((735175222646550854443/200000000000000000000000 : ℝ) : ℝ) + (23208115825716357913/62500000000000000000000 : ℝ) := by norm_num
    rw [e25]
    linarith [a24, b9_pan_25, hprev]
  have a26 : ((1109372386489094495149/250000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(181/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1109372386489094495149/250000000000000000000000 : ℝ) : ℝ) ≤ ((4047205966444215998823/1000000000000000000000000 : ℝ) : ℝ) + (390283579512161981773/1000000000000000000000000 : ℝ) := by norm_num
    rw [e26]
    linarith [a25, b9_pan_26, hprev]
  have a27 : ((4846677046447107110709/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(46/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((4846677046447107110709/1000000000000000000000000 : ℝ) : ℝ) ≤ ((1109372386489094495149/250000000000000000000000 : ℝ) : ℝ) + (409187500490729130113/1000000000000000000000000 : ℝ) := by norm_num
    rw [e27]
    linarith [a26, b9_pan_27, hprev]
  have a28 : ((527470276512016063129/100000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(187/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((527470276512016063129/100000000000000000000000 : ℝ) : ℝ) ≤ ((4846677046447107110709/1000000000000000000000000 : ℝ) : ℝ) + (428025718673053520581/1000000000000000000000000 : ℝ) := by norm_num
    rw [e28]
    linarith [a27, b9_pan_28, hprev]
  have a29 : ((5721486776028286909301/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(19/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((5721486776028286909301/1000000000000000000000000 : ℝ) : ℝ) ≤ ((527470276512016063129/100000000000000000000000 : ℝ) : ℝ) + (446784010908126278011/1000000000000000000000000 : ℝ) := by norm_num
    rw [e29]
    linarith [a28, b9_pan_29, hprev]
  have a30 : ((618693644406933616833/100000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(193/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((618693644406933616833/100000000000000000000000 : ℝ) : ℝ) ≤ ((5721486776028286909301/1000000000000000000000000 : ℝ) : ℝ) + (465449668041049259029/1000000000000000000000000 : ℝ) := by norm_num
    rw [e30]
    linarith [a29, b9_pan_30, hprev]
  have a31 : ((6670947795030481482543/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(49/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((6670947795030481482543/1000000000000000000000000 : ℝ) : ℝ) ≤ ((618693644406933616833/100000000000000000000000 : ℝ) : ℝ) + (484011350961145314213/1000000000000000000000000 : ℝ) := by norm_num
    rw [e31]
    linarith [a30, b9_pan_31, hprev]
  have a32 : ((896675844527478099123/125000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(199/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((896675844527478099123/125000000000000000000000 : ℝ) : ℝ) ≤ ((6670947795030481482543/1000000000000000000000000 : ℝ) : ℝ) + (502458961189343310441/1000000000000000000000000 : ℝ) := by norm_num
    rw [e32]
    linarith [a31, b9_pan_32, hprev]
  have a33 : ((3847095140307632417259/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(101/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((3847095140307632417259/500000000000000000000000 : ℝ) : ℝ) ≤ ((896675844527478099123/125000000000000000000000 : ℝ) : ℝ) + (260391762197720020767/500000000000000000000000 : ℝ) := by norm_num
    rw [e33]
    linarith [a32, b9_pan_33, hprev]
  have a34 : ((8233167366046960244201/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(41/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((8233167366046960244201/1000000000000000000000000 : ℝ) : ℝ) ≤ ((3847095140307632417259/500000000000000000000000 : ℝ) : ℝ) + (538977085431695409683/1000000000000000000000000 : ℝ) := by norm_num
    rw [e34]
    linarith [a33, b9_pan_34, hprev]
  have a35 : ((439509998984297359327/50000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(52/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((439509998984297359327/50000000000000000000000 : ℝ) : ℝ) ≤ ((8233167366046960244201/1000000000000000000000000 : ℝ) : ℝ) + (557032613638986942339/1000000000000000000000000 : ℝ) := by norm_num
    rw [e35]
    linarith [a34, b9_pan_35, hprev]
  have a36 : ((9365143897015159332041/1000000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(211/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((9365143897015159332041/1000000000000000000000000 : ℝ) : ℝ) ≤ ((439509998984297359327/50000000000000000000000 : ℝ) : ℝ) + (574943917329212145501/1000000000000000000000000 : ℝ) := by norm_num
    rw [e36]
    linarith [a35, b9_pan_36, hprev]
  have a37 : ((1244731182936391027757/125000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(107/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((1244731182936391027757/125000000000000000000000 : ℝ) : ℝ) ≤ ((9365143897015159332041/1000000000000000000000000 : ℝ) : ℝ) + (118541113295193778003/200000000000000000000000 : ℝ) := by norm_num
    rw [e37]
    linarith [a36, b9_pan_37, hprev]
  have a38 : ((5284081143124293624539/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(217/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((5284081143124293624539/500000000000000000000000 : ℝ) : ℝ) ≤ ((1244731182936391027757/125000000000000000000000 : ℝ) : ℝ) + (305156411378729513511/500000000000000000000000 : ℝ) := by norm_num
    rw [e38]
    linarith [a37, b9_pan_38, hprev]
  have a39 : ((5597961931220961137453/500000000000000000000000 : ℝ) : ℝ) ≤ ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    have hprev : ((5597961931220961137453/500000000000000000000000 : ℝ) : ℝ) ≤ ((5284081143124293624539/500000000000000000000000 : ℝ) : ℝ) + (156940394048333756457/250000000000000000000000 : ℝ) := by norm_num
    rw [e39]
    linarith [a38, b9_pan_39, hprev]
  have hfin := a39
  norm_num at hfin ⊢
  exact hfin



/-! ### `entry_8_0`: the `[1, 11/5]` panel of row 9 (`Xi1 3 3`, the `sp = 3` row)

On `(1, 11/5)` the kernel `Xi1 3 3` has only two live windows: the base term with
`log (16/4) = log 4` and the `(t+1)^2` window (its indicator is `[3-2, 3] = [1,3]`, which covers
the panel), while the third window `[3 - 3/3 - 1, 3 - 2] = [1,1]` is a single point.  So
`Xi1 3 3 t = log 4 · sigma0 t/(2t) + log ((t+1)/2)/t` a.e., and the entry splits into the
`sigma0` quadrature `b9_I_sigma` and one logarithm integral. -/

/-- Two-sided bound for `log (13/10)`. -/
private theorem b9_log_13_10 :
    (13118213223374552601774799/50000000000000000000000000 : ℝ) ≤ log (13/10 : ℝ) ∧
      log (13/10 : ℝ) ≤ (26236426446749105203549599/100000000000000000000000000 : ℝ) := by
  have h := log_enclosure (y := (13/10 : ℝ)) (x := (3/23 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 17
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
/-- `∫_1^{11/5} log ((t+1)/2)/t`, from the `log (t+1)` series at the midpoint `8/5` with 20 terms
(remainder `5.6e-14`) and `log (11/5)`, `log 2` two-sided. -/
private theorem b9_J_lower :
    (1755310892/10000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11/5 : ℝ), log ((t + 1) / 2) / t := by
  have hc1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume 1 (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ continuousOn_id ?_
    · refine Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) ?_
      intro t ht
      have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
      exact ne_of_gt h1
    · intro t ht
      linarith [ht.1]
  have hc2 : IntervalIntegrable (fun t : ℝ => log 2 * (1 / t)) volume 1 (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.mul continuousOn_const ?_
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    linarith [ht.1]
  have hpt : ∀ t ∈ uIcc (1 : ℝ) (11/5),
      log ((t + 1) / 2) / t = log (t + 1) / t - log 2 * (1 / t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have h1 : (0 : ℝ) < t + 1 := by linarith
    have hgoal : log ((t + 1) / 2) / t - (log (t + 1) / t - log 2 * (1 / t)) = 0 := by
      rw [Real.log_div (ne_of_gt h1) (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp
      ring
    linarith [hgoal]
  have hlog1 : log ((11/5 : ℝ) / 1) = log (11/5) := by norm_num
  have hid : (∫ t in (1 : ℝ)..(11/5 : ℝ), log ((t + 1) / 2) / t) =
      (∫ t in (1 : ℝ)..(11/5 : ℝ), log (t + 1) / t) - log 2 * log (11/5) := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub hc1 hc2,
      intervalIntegral.integral_const_mul, integral_one_div_exp (by norm_num) (by norm_num), hlog1]
  rw [hid]
  have hxr : ∀ t ∈ uIcc (1 : ℝ) (11/5), |(8/5 - t) / (8/5 + 1)| ≤ 3/13 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(8/5 : ℝ) - t| ≤ 3/5 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (8/5 : ℝ) + 1 = 13/5 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8/5 + 1), hden]
    have h3 : |(8/5 : ℝ) - t| / (13/5) ≤ (3/5) / (13/5) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (3/5 : ℝ) / (13/5) = 3/13 := by norm_num
    linarith [h3, h4]
  have hint : (∫ t in (1 : ℝ)..(11/5), log (1 + t) * t⁻¹) =
      ∫ t in (1 : ℝ)..(11/5), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  have h := log_succ_integral_lower (a := 1) (b := 11/5) (c := 8/5) (r := 3/13)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 20
  simp only [Finset.sum_range_succ] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  rw [hint] at h
  have h2lo : (69314718055/10^11 : ℝ) ≤ log 2 := by linarith [log_two_bounds.1]
  have h2hi : log 2 ≤ (69314718056/10^11 : ℝ) := by linarith [log_two_bounds.2]
  have hLlo : (78845736036/10^11 : ℝ) ≤ log (11/5) := by linarith [log_2_2_bounds.1]
  have hLhi : log (11/5) ≤ (78845736037/10^11 : ℝ) := by linarith [log_2_2_bounds.2]
  have h13 : log (13/5 : ℝ) = log 2 + log (13/10) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h13lo : (69314718055/10^11 + 13118213223374552601774799/50000000000000000000000000 : ℝ) ≤
      log (13/5) := by
    rw [h13]
    linarith [h2lo, b9_log_13_10.1]
  have hprod : ((69314718055/10^11 + 13118213223374552601774799/50000000000000000000000000 : ℝ) *
      (78845736036/10^11)) ≤ log (13/5) * log (11/5) := by
    refine mul_le_mul h13lo hLlo (by norm_num) ?_
    linarith [h13lo]
  have h2L : log 2 * log (11/5) ≤ (69314718056/10^11 : ℝ) * (78845736037/10^11) := by
    refine mul_le_mul h2hi hLhi ?_ (by norm_num)
    linarith [h2lo]
  linarith [h, hprod, h2L, hLhi, hLlo]

/-- On `(1, 11/5)` the kernel `Xi1 3 3` is the base term plus the `(t+1)^2` window. -/
private theorem b9_xi1_3_3 {t : ℝ} (ht : t ∈ Set.uIoo (1 : ℝ) (11/5)) :
    Wu04Functional.Xi1 3 3 t = log 4 * (Wu04Integral.sigma0 t / (2 * t)) + log ((t + 1) / 2) / t := by
  have hmin : min (1 : ℝ) (11/5) = 1 := min_eq_left (by norm_num)
  have hmax : max (1 : ℝ) (11/5) = 11/5 := max_eq_right (by norm_num)
  rw [Set.uIoo, hmin, hmax] at ht
  have ht1 : (1 : ℝ) < t := ht.1
  have ht2 : t < 11/5 := ht.2
  have e1 : Wu04Functional.ind ((3 : ℝ) - 2) 3 t = 1 := by
    unfold Wu04Functional.ind
    exact if_pos ⟨by linarith, by linarith⟩
  have e2 : Wu04Functional.ind ((3 : ℝ) - 3/3 - 1) ((3 : ℝ) - 2) t = 0 := by
    unfold Wu04Functional.ind
    refine if_neg ?_
    rintro ⟨-, h2⟩
    norm_num at h2
    linarith
  unfold Wu04Functional.Xi1
  rw [e1, e2]
  norm_num
  have hsq : log (((t + 1) ^ 2) / 4 : ℝ) = 2 * log ((t + 1) / 2) := by
    rw [show ((t + 1) ^ 2) / 4 = ((t + 1) / 2) ^ 2 by ring]
    rw [Real.log_pow]
    push_cast
    ring
  rw [hsq]
  field_simp

/-- `integralMatrix 8 0` is the `Xi1 (3) (3)` quadrature on `[1, 11/5]`. -/
private theorem integralMatrix_8_0_eq :
    Wu04Table.integralMatrix 8 0 =
      ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 ((3 : ℝ)) ((3 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_8_0` of Wu's Section 7 matrix**, certified on the `[1, 11/5]` panel. -/
theorem c8_entry_8_0_leaf :
    (Wu04Table.candidateMatrixQ 8 0 : ℝ) ≤ Wu04Table.integralMatrix 8 0 := by
  have hc : (Wu04Table.candidateMatrixQ 8 0 : ℝ) = 1910519 / 10^7 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc, integralMatrix_8_0_eq]
  rw [intervalIntegral.integral_congr_uIoo (f := fun t => Wu04Functional.Xi1 3 3 t)
    (g := fun t => log 4 * (Wu04Integral.sigma0 t / (2 * t)) + log ((t + 1) / 2) / t)
    (fun t ht => b9_xi1_3_3 ht)]
  have h1 : IntervalIntegrable (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) volume 1 (11/5) :=
    sigma0_div_two_integrable_Icc (by norm_num) (by norm_num) (by norm_num)
  have h2 : IntervalIntegrable (fun t : ℝ => log ((t + 1) / 2) / t) volume 1 (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ continuousOn_id ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_id.add continuousOn_const |>.div_const 2
      · intro t ht
        have h3 : (0 : ℝ) < (t + 1) / 2 := by linarith [ht.1]
        exact ne_of_gt h3
    · intro t ht
      linarith [ht.1]
  have hsplit : (∫ t in (1 : ℝ)..(11/5 : ℝ),
        (log 4 * (Wu04Integral.sigma0 t / (2 * t)) + log ((t + 1) / 2) / t)) =
      log 4 * (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (1 : ℝ)..(11/5 : ℝ), log ((t + 1) / 2) / t) := by
    rw [intervalIntegral.integral_add (h1.const_mul (log 4)) h2,
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  have hI := b9_I_sigma
  have hJ := b9_J_lower
  have h4 : (1.3862943611 : ℝ) ≤ log 4 := log_four_bounds.1
  have hIpos : (0 : ℝ) ≤ ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
    linarith [hI]
  nlinarith [hI, hJ, h4, hIpos]

/-- Exact value of `∫ (t-m)^k / t`: the binomial expansion of `integral_sub_pow_div`, with the
sign of `(t-m)^k = (-1)^k (m-t)^k` carried out front. -/
private theorem integral_pow_sub_div {a b m : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    (∫ t in a..b, (t - m) ^ k / t) =
      (-1) ^ k * (m ^ k * log (b / a) + ∑ j ∈ Finset.range k,
        (-1) ^ (j + k) * m ^ j * (k.choose j : ℝ) *
          ((b ^ (k - j) - a ^ (k - j)) / ((k : ℝ) - j))) := by
  rw [← integral_sub_pow_div (a := a) (b := b) (c := m) (m := k) ha hab]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have h1 : ((-1 : ℝ) ^ k) * ((m - t) ^ k) = (t - m) ^ k := by
    rw [← mul_pow, show ((-1 : ℝ) * (m - t)) = t - m by ring]
  rw [← mul_div_assoc, h1]

/-! ### The `j = 0` panel of the `Xi1` rows

Rows 4-8 carry, on the middle piece of `[1, 11/5]`, the window `log ((t+1)/((s-1)(sp-1-t))): a
logarithm of a *decreasing* affine, with a minus sign in front of its integral.  The file's series
machinery only handles `log (t+1)`; here is the decreasing-argument version: expand `log (1 - u)`
with `u = (t - m)/(al - m)` by `Real.abs_log_sub_add_sum_range_le` around the midpoint `m` of the
piece, integrate the resulting polynomial against `1/(2t)` in closed form
(`integral_sub_pow_div`), and keep the alternating remainder. -/

/-- Pointwise upper bound for `log (al - t)` from the alternating series around `m`. -/
private theorem log_affine_le_series {al m r t : ℝ} (hD : 0 < al - m) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : |(t - m) / (al - m)| ≤ r) (n : ℕ) :
    log (al - t) ≤ log (al - m) -
      (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
      r ^ (n + 1) / (1 - r) := by
  have hx1 : |(t - m) / (al - m)| < 1 := lt_of_le_of_lt ht hr1
  have hS := Real.abs_log_sub_add_sum_range_le hx1 n
  have hb : |(t - m) / (al - m)| ^ (n + 1) / (1 - |(t - m) / (al - m)|) ≤
      r ^ (n + 1) / (1 - r) := by
    refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) ht _)
      (by linarith) (by linarith)
  have hle : log (1 - (t - m) / (al - m)) ≤
      -(∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
        r ^ (n + 1) / (1 - r) := by
    have h2 := (abs_le.mp (le_trans hS hb)).2
    linarith
  have h2 : (0 : ℝ) < 1 - (t - m) / (al - m) := by
    have h3 := (abs_lt.mp hx1).2
    linarith
  have harg : al - t = (al - m) * (1 - (t - m) / (al - m)) := by
    field_simp
    ring
  have hlog : log (al - t) = log (al - m) + log (1 - (t - m) / (al - m)) := by
    rw [harg, Real.log_mul (ne_of_gt hD) (ne_of_gt h2)]
  linarith

/-- `∫_a^b log (al - t)/(2t)` from above: the alternating series around `m`, integrated exactly. -/
private theorem integral_log_affine_upper {a b al m r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 < al - m) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : ∀ t ∈ Set.Icc a b, |(t - m) / (al - m)| ≤ r) (n : ℕ) :
    (∫ t in a..b, log (al - t) / (2 * t)) ≤
      (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * log (b / a)) -
        (1 / 2) * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
          (∫ t in a..b, (t - m) ^ (i + 1) / t) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hmem' : ∀ t ∈ Set.Icc a b, (0 : ℝ) < t := by
    intro t ht
    exact lt_of_lt_of_le ha ht.1
  have hxr' : ∀ t ∈ uIcc a b, |(t - m) / (al - m)| ≤ r := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hxr t ht
  have hpos : ∀ t ∈ Set.Icc a b, (0 : ℝ) < al - t := by
    intro t ht
    have h3 : (t - m) / (al - m) < 1 := (abs_lt.mp (lt_of_le_of_lt (hxr t ht) hr1)).2
    have h6 : t - m < al - m := (div_lt_one hD).mp h3
    linarith
  -- pointwise bound
  have hpt : ∀ t ∈ Set.Icc a b,
      log (al - t) / (2 * t) ≤
        (log (al - m) - (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
          r ^ (n + 1) / (1 - r)) / (2 * t) := by
    intro t ht
    have h2t : (0 : ℝ) < 2 * t := by linarith [hmem' t ht]
    exact div_le_div_of_nonneg_right (log_affine_le_series hD hr0 hr1 (hxr t ht) n) h2t.le
  have hcont1 : ContinuousOn (fun t : ℝ => log (al - t) / (2 * t)) (uIcc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine ContinuousOn.log (continuousOn_const.sub continuousOn_id) ?_
      intro t ht
      have h3 : (t - m) / (al - m) < 1 := (abs_lt.mp (lt_of_le_of_lt (hxr' t ht) hr1)).2
      have h6 : t - m < al - m := (div_lt_one hD).mp h3
      intro hcon
      linarith [hcon]
    · intro t ht
      have h2t : (0 : ℝ) < 2 * t := by linarith [hmem t ht]
      positivity
  have hcont2 : ContinuousOn (fun t : ℝ =>
      (log (al - m) - (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
        r ^ (n + 1) / (1 - r)) / (2 * t)) (uIcc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine ContinuousOn.add (ContinuousOn.sub continuousOn_const ?_) continuousOn_const
      refine continuousOn_finsetSum (Finset.range n) (fun i _ => ?_)
      exact (((continuousOn_id.sub continuousOn_const).div_const _).pow _).div_const _
    · intro t ht
      have h2t : (0 : ℝ) < 2 * t := by linarith [hmem t ht]
      positivity
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    hcont1.intervalIntegrable hcont2.intervalIntegrable hpt
  -- integrability of the pieces of the right-hand side
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht)))
  have hterm : ∀ i ∈ Finset.range n, IntervalIntegrable
      (fun t : ℝ => (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
        ((t - m) ^ (i + 1) / t)) volume a b := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ?_
    exact ((continuousOn_id.sub continuousOn_const).pow _).div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht))
  -- split the series against `1/t`
  have hsum_eq : ∀ t ∈ uIcc a b,
      (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) / t =
      ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
        ((t - m) ^ (i + 1) / t) := by
    intro t _
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow]
    field_simp
  have hcongr : ∀ t ∈ uIcc a b,
      (log (al - m) - (∑ i ∈ Finset.range n, ((t - m) / (al - m)) ^ (i + 1) / ((i : ℝ) + 1)) +
          r ^ (n + 1) / (1 - r)) / (2 * t) =
      (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * (1 / t)) -
        (1 / 2) * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
          ((t - m) ^ (i + 1) / t) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    rw [← hsum_eq t ht]
    field_simp
    ring
  have hA : IntervalIntegrable
      (fun t : ℝ => (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * (1 / t))) volume a b :=
    (hinv.const_mul (log (al - m) + r ^ (n + 1) / (1 - r))).const_mul (1 / 2)
  have hS : IntervalIntegrable (fun t : ℝ => (1 / 2) * ∑ i ∈ Finset.range n,
      (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) * ((t - m) ^ (i + 1) / t))
      volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.const_mul ?_ _
    refine continuousOn_finsetSum (Finset.range n) (fun i _ => ?_)
    exact continuousOn_const.mul
      (((continuousOn_id.sub continuousOn_const).pow _).div continuousOn_id
        (fun t ht => ne_of_gt (hmem t ht)))
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub hA hS] at hmono
  have e1 : (∫ t in a..b, (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * (1 / t))) =
      (1 / 2) * ((log (al - m) + r ^ (n + 1) / (1 - r)) * log (b / a)) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_one_div_exp ha hab]
  have e2 : (∫ t in a..b, (1 / 2) * ∑ i ∈ Finset.range n,
        (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) * ((t - m) ^ (i + 1) / t)) =
      (1 / 2) * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (al - m) ^ (i + 1))) *
        (∫ t in a..b, (t - m) ^ (i + 1) / t) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hterm]
    refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
    rw [intervalIntegral.integral_const_mul]
  rw [e1, e2] at hmono
  linarith [hmono]

set_option maxHeartbeats 2000000 in
/-- The middle-piece logarithm integral of the `Xi1` rows of column 0:
`∫_{391/325}^{79/50} log (129/50 - t)/(2t) ≤ 0.0239355694978` (12 series terms around
`m = 1809/1300`, ratio `|u| ≤ 49/309`). -/
private theorem c4_int_log_affine :
    (∫ t in (391/325 : ℝ)..(79/50 : ℝ), log ((129/50 : ℝ) - t) / (2 * t)) ≤
      (0.0239355694979 : ℝ) := by
  have hxr : ∀ t ∈ Set.Icc (391/325 : ℝ) (79/50),
      |(t - 1809/1300) / ((129/50 : ℝ) - 1809/1300)| ≤ 49/309 := by
    intro t ht
    have h1 : |t - (1809/1300 : ℝ)| ≤ 245/1300 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 129/50 - 1809/1300)]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 129/50 - 1809/1300) (by norm_num : (0 : ℝ) < 309)]
    nlinarith [h1]
  have h := integral_log_affine_upper (a := (391/325 : ℝ)) (b := (79/50 : ℝ)) (al := (129/50 : ℝ))
    (m := (1809/1300 : ℝ)) (r := (49/309 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [integral_pow_sub_div (a := (391/325 : ℝ)) (b := (79/50 : ℝ)) (by norm_num) (by norm_num)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  have h1 : (0.1726596458822177 : ℝ) ≤ log (309/260) ∧ log (309/260) ≤ (0.1726596458822178 : ℝ) := by
    have hh := log_enclosure (y := (309/260 : ℝ)) (x := (49/569 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 14
    constructor
    · refine le_trans ?_ hh.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hh.2 ?_
      norm_num [Finset.sum_range_succ]
  have h2 : (0.2725424693832471 : ℝ) ≤ log (1027/782) ∧ log (1027/782) ≤ (0.2725424693832472 : ℝ) := by
    have hh := log_enclosure (y := (1027/782 : ℝ)) (x := (245/1809 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 14
    constructor
    · refine le_trans ?_ hh.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hh.2 ?_
      norm_num [Finset.sum_range_succ]
  have hprod : log (309/260) * log (1027/782) ≤
      (0.1726596458822178 : ℝ) * (0.2725424693832472 : ℝ) :=
    mul_le_mul h1.2 h2.2 (le_trans (by norm_num) h2.1) (by norm_num)
  nlinarith [h, h1.2, h2.1, h2.2, hprod]


/-! ### Row 4 on the `[1, 11/5]` panel: `Xi1 (13/5) (179/50)`

Unlike the rows whose second window starts beyond `11/5`, row 4 has `sp - 2 = 79/50` strictly
inside the panel, so the panel splits at `s1 = 391/325` and at `s2 = 79/50` into

* `[1, s1]`: the `sigma0` term,
* `[s1, s2]`: `sigma0` term plus the descending window `log ((t+1)/((8/5)(129/50 - t)))`,
* `[s2, 11/5]`: `sigma0` term plus the `(t+1)^2` window.

The descending window is handled by the alternating-series upper bound `c4_int_log_affine` for
`∫ log (129/50 - t)/(2t)`. -/

/-- `log (500/129)`, the `sigma0` coefficient of row 4, from below (`x = 371/629`, 24 terms). -/
private theorem c4_log_c_lo : (1.3547956940601 : ℝ) ≤ log (500/129 : ℝ) := by
  have h := log_enclosure (y := (500/129 : ℝ)) (x := (371/629 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 24
  refine le_trans ?_ h.1
  norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (3109/1300)` (`x = 1809/4409`, 16 terms). -/
private theorem c4_log_3109 : (0.8719368666091 : ℝ) ≤ log (3109/1300 : ℝ) ∧
    log (3109/1300 : ℝ) ≤ (0.8719368666096 : ℝ) := by
  have h := log_enclosure (y := (3109/1300 : ℝ)) (x := (1809/4409 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (1027/782)` (`x = 245/1809`, 16 terms). -/
private theorem c4_log_1027 : (0.2725424693832471 : ℝ) ≤ log (1027/782 : ℝ) ∧
    log (1027/782 : ℝ) ≤ (0.2725424693832472 : ℝ) := by
  have h := log_enclosure (y := (1027/782 : ℝ)) (x := (245/1809 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (289/100)` (`x = 189/389`, 16 terms). -/
private theorem c4_log_289 : (1.0612565021208 : ℝ) ≤ log (289/100 : ℝ) ∧
    log (289/100 : ℝ) ≤ (1.0612565022391 : ℝ) := by
  have h := log_enclosure (y := (289/100 : ℝ)) (x := (189/389 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (110/79)` (`x = 31/189`, 16 terms). -/
private theorem c4_log_110 : (0.3310325133253947 : ℝ) ≤ log (110/79 : ℝ) ∧
    log (110/79 : ℝ) ≤ (0.3310325133253948 : ℝ) := by
  have h := log_enclosure (y := (110/79 : ℝ)) (x := (31/189 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (8/5)` from above (`x = 3/13`, 14 terms). -/
private theorem c4_log_85_hi : log (8/5 : ℝ) ≤ (0.4700036292457356 : ℝ) := by
  have h := log_enclosure (y := (8/5 : ℝ)) (x := (3/13 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 14
  refine le_trans h.2 ?_
  norm_num [Finset.sum_range_succ]

/-- `log (516/125)` from above (`x = 391/641`, 30 terms). -/
private theorem c4_log_4128_hi : log (516/125 : ℝ) ≤ (1.4177930281796 : ℝ) := by
  have h := log_enclosure (y := (516/125 : ℝ)) (x := (391/641 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 30
  refine le_trans h.2 ?_
  norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
/-- `L1 = ∫_{391/325}^{79/50} log (t+1)/t` from below: the `log (t+1)` series at the midpoint
`1809/1300` with 10 terms, ratio `245/3109`. -/
private theorem c4_L1_lower :
    (0.2363802324848 : ℝ) ≤ ∫ t in (391/325 : ℝ)..(79/50 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (391/325 : ℝ) (79/50),
      |(1809/1300 - t) / (1809/1300 + 1)| ≤ 245/3109 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(1809/1300 : ℝ) - t| ≤ 245/1300 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (1809/1300 : ℝ) + 1 = 3109/1300 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1809/1300 + 1), hden]
    have h3 : |(1809/1300 : ℝ) - t| / (3109/1300) ≤ (245/1300) / (3109/1300) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (245/1300 : ℝ) / (3109/1300) = 245/3109 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (391/325 : ℝ)) (b := (79/50 : ℝ))
    (c := (1809/1300 : ℝ)) (r := (245/3109 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (391/325 : ℝ)..(79/50 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (391/325 : ℝ)..(79/50 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc1 := c4_log_3109
  have hba := c4_log_1027
  have hprod : (0.8719368666091 : ℝ) * (0.2725424693832471 : ℝ) ≤
      log (3109/1300 : ℝ) * log (1027/782 : ℝ) :=
    mul_le_mul hc1.1 hba.1 (by norm_num) (le_trans (by norm_num) hc1.1)
  linarith [h, hprod, hba.1, hba.2]

set_option maxHeartbeats 2000000 in
/-- `L2 = ∫_{79/50}^{11/5} log (t+1)/t` from below: midpoint `189/100`, 12 terms,
ratio `22/289`. -/
private theorem c4_L2_lower :
    (0.348708690738 : ℝ) ≤ ∫ t in (79/50 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (79/50 : ℝ) (11/5),
      |(189/100 - t) / (189/100 + 1)| ≤ 31/289 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(189/100 : ℝ) - t| ≤ 31/100 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (189/100 : ℝ) + 1 = 289/100 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 189/100 + 1), hden]
    have h3 : |(189/100 : ℝ) - t| / (289/100) ≤ (31/100) / (289/100) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (31/100 : ℝ) / (289/100) = 31/289 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (79/50 : ℝ)) (b := (11/5 : ℝ))
    (c := (189/100 : ℝ)) (r := (31/289 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (79/50 : ℝ)..(11/5 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (79/50 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc2 := c4_log_289
  have hba := c4_log_110
  have hprod : (1.0612565021208 : ℝ) * (0.3310325133253947 : ℝ) ≤
      log (289/100 : ℝ) * log (110/79 : ℝ) :=
    mul_le_mul hc2.1 hba.1 (by norm_num) (le_trans (by norm_num) hc2.1)
  linarith [h, hprod, hba.1, hba.2]

/-- The descending window on `[391/325, 79/50]`, split into `log (t+1)`, `log (8/5)` and
`log (129/50 - t)`. -/
private theorem c4_J3_eq :
    (∫ t in (391/325 : ℝ)..(79/50 : ℝ), log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t)) =
      (1/2) * (∫ t in (391/325 : ℝ)..(79/50 : ℝ), log (t + 1) / t) -
        (1/2) * log (8/5) * log (1027/782) -
        (∫ t in (391/325 : ℝ)..(79/50 : ℝ), log (129/50 - t) / (2 * t)) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (391/325 : ℝ) (79/50 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (391/325 : ℝ) (79/50 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => log (129/50 - t) / (2 * t)) volume
      (391/325 : ℝ) (79/50 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · refine Real.continuousOn_log.comp (continuousOn_const.sub continuousOn_id) ?_
      intro t ht
      have h2 : (0 : ℝ) < 129/50 - t := by linarith [ht.2]
      exact ne_of_gt h2
    · intro t ht
      have h2 : (0 : ℝ) < t := by linarith [ht.1]
      positivity
  have hpt : ∀ t ∈ uIcc (391/325 : ℝ) (79/50),
      log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t) =
        (1/2) * (log (t + 1) / t) - (1/2) * log (8/5) * (1 / t) -
          log (129/50 - t) / (2 * t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have h1 : (0 : ℝ) < t + 1 := by linarith
    have h3 : (0 : ℝ) < 129/50 - t := by linarith [ht.2]
    have hden : ((8/5) * (129/50 - t) : ℝ) ≠ 0 := by positivity
    rw [Real.log_div (ne_of_gt h1) hden,
      Real.log_mul (by norm_num : (8/5 : ℝ) ≠ 0) (ne_of_gt h3)]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub
      ((hI1.const_mul (1/2)).sub (hI2.const_mul (1/2 * log (8/5)))) hI3]
  rw [intervalIntegral.integral_sub (hI1.const_mul (1/2)) (hI2.const_mul (1/2 * log (8/5)))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((79/50 : ℝ) / (391/325)) = (1027/782 : ℝ) by norm_num]

/-- The `(t+1)^2` window on `[79/50, 11/5]`, split into `log (t+1)` and `log (516/125)`. -/
private theorem c4_J2_eq :
    (∫ t in (79/50 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (516/125)) / (2 * t)) =
      (∫ t in (79/50 : ℝ)..(11/5 : ℝ), log (t + 1) / t) -
        (1/2) * log (516/125) * log (110/79) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (79/50 : ℝ) (11/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (79/50 : ℝ) (11/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (79/50 : ℝ) (11/5),
      log ((t + 1) ^ 2 / (516/125)) / (2 * t) =
        log (t + 1) / t - (1/2) * log (516/125) * (1 / t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have hnum : ((t + 1) ^ 2 : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hnum (by norm_num : (516/125 : ℝ) ≠ 0), Real.log_pow]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub hI1 (hI2.const_mul (1/2 * log (516/125)))]
  rw [intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((11/5 : ℝ) / (79/50)) = (110/79 : ℝ) by norm_num]

/-- On `(1, 11/5)` the row-4 kernel is the `sigma0` term plus its two windows. -/
private theorem c4_xi1_eq {t : ℝ} (ht : t ∈ Set.uIoo (1 : ℝ) (11/5)) :
    Wu04Functional.Xi1 (13/5) (179/50) t =
      log (500/129) * (Wu04Integral.sigma0 t / (2 * t)) +
        Wu04Functional.ind (79/50) 3 t * (log ((t + 1) ^ 2 / (516/125)) / (2 * t)) +
        Wu04Functional.ind (391/325) (79/50) t *
          (log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t)) := by
  rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
    max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)] at ht
  unfold Wu04Functional.Xi1
  have hA : ((13/5 : ℝ) - 1) * (179/50 - 1) = 516/125 := by norm_num
  have hB : (16 : ℝ) / (516/125) = 500/129 := by norm_num
  have hC : (179/50 : ℝ) - 2 = 79/50 := by norm_num
  have hD : (179/50 : ℝ) - 179/50/(13/5) - 1 = 391/325 := by norm_num
  have hE : (13/5 : ℝ) - 1 = 8/5 := by norm_num
  have hF : (179/50 : ℝ) - 1 = 129/50 := by norm_num
  rw [hA, hB, hC, hD, hE, hF]
  ring

/-- `integralMatrix 4 0` is the `Xi1 (13/5) (179/50)` quadrature on `[1, 11/5]`. -/
private theorem integralMatrix_4_0_eq :
    Wu04Table.integralMatrix 4 0 =
      ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_4_0` of Wu's Section 7 matrix**, certified on the `[1, 11/5]` panel. -/
theorem c4_entry_4_0_leaf :
    (Wu04Table.candidateMatrixQ 4 0 : ℝ) ≤ Wu04Table.integralMatrix 4 0 := by
  have hc : (Wu04Table.candidateMatrixQ 4 0 : ℝ) = 1594156 / 10^7 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc, integralMatrix_4_0_eq]
  -- the three smooth representatives
  have hS1 : ∀ t ∈ Set.uIoo (1 : ℝ) (391/325),
      log (500/129) * (Wu04Integral.sigma0 t / (2 * t)) =
        Wu04Functional.Xi1 (13/5) (179/50) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 391/325),
      max_eq_right (by norm_num : (1 : ℝ) ≤ 391/325)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨ht.1, by linarith [ht.2]⟩
    rw [c4_xi1_eq ht']
    have e1 : Wu04Functional.ind (79/50) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (391/325) (79/50) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    rw [e1, e2]
    ring
  have hS2 : ∀ t ∈ Set.uIoo (391/325 : ℝ) (79/50),
      (log (500/129) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t)) =
        Wu04Functional.Xi1 (13/5) (179/50) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (391/325 : ℝ) ≤ 79/50),
      max_eq_right (by norm_num : (391/325 : ℝ) ≤ 79/50)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [c4_xi1_eq ht']
    have e1 : Wu04Functional.ind (79/50) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (391/325) (79/50) t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [e1, e2]
    ring
  have hS3 : ∀ t ∈ Set.uIoo (79/50 : ℝ) (11/5),
      (log (500/129) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) ^ 2 / (516/125)) / (2 * t)) =
        Wu04Functional.Xi1 (13/5) (179/50) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (79/50 : ℝ) ≤ 11/5),
      max_eq_right (by norm_num : (79/50 : ℝ) ≤ 11/5)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨by linarith [ht.1], ht.2⟩
    rw [c4_xi1_eq ht']
    have e1 : Wu04Functional.ind (79/50) 3 t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, by linarith [ht.2]⟩
    have e2 : Wu04Functional.ind (391/325) (79/50) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨-, h2⟩; linarith [ht.1])
    rw [e1, e2]
    ring
  -- integrability of the kernel on each of the three pieces
  have hI1 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (13/5) (179/50) t) volume
      (1 : ℝ) (391/325) :=
    ((sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (391/325 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (500/129))).congr_uIoo hS1
  have hJ3int : IntervalIntegrable (fun t : ℝ => log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t))
      volume (391/325 : ℝ) (79/50) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · refine ContinuousOn.div (continuousOn_id.add continuousOn_const) ?_ ?_
        · exact continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
        · intro t ht
          have h4 : (0 : ℝ) < 129/50 - t := by linarith [ht.2]
          exact ne_of_gt (by positivity)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        have h6 : (0 : ℝ) < 129/50 - t := by linarith [ht.2]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hJ2int : IntervalIntegrable (fun t : ℝ => log ((t + 1) ^ 2 / (516/125)) / (2 * t))
      volume (79/50 : ℝ) (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_id.add continuousOn_const).pow 2 |>.div_const (516/125)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hI2 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (13/5) (179/50) t) volume
      (391/325 : ℝ) (79/50) :=
    (((sigma0_div_two_integrable_Icc (a := (391/325 : ℝ)) (b := (79/50 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (500/129))).add hJ3int).congr_uIoo hS2
  have hI3 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (13/5) (179/50) t) volume
      (79/50 : ℝ) (11/5) :=
    (((sigma0_div_two_integrable_Icc (a := (79/50 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (500/129))).add hJ2int).congr_uIoo hS3
  -- split the panel and replace each piece
  have hsplit : (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) =
      (∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) +
        (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) +
        (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hI12 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (13/5) (179/50) t) volume
        (1 : ℝ) (79/50) := hI1.trans hI2
    have h123 := intervalIntegral.integral_add_adjacent_intervals hI12 hI3
    linarith [h12, h123]
  have e1 : (∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) =
      log (500/129) * (∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (13/5) (179/50) t)
      (g := fun t : ℝ => log (500/129) * (Wu04Integral.sigma0 t / (2 * t)))
      (fun t ht => (hS1 t ht).symm)]
    rw [intervalIntegral.integral_const_mul]
  have e2 : (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) =
      log (500/129) * (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (391/325 : ℝ)..(79/50 : ℝ),
          log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (13/5) (179/50) t)
      (g := fun t : ℝ => log (500/129) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t))
      (fun t ht => (hS2 t ht).symm)]
    rw [intervalIntegral.integral_add
      ((sigma0_div_two_integrable_Icc (a := (391/325 : ℝ)) (b := (79/50 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)).const_mul (log (500/129))) hJ3int]
    rw [intervalIntegral.integral_const_mul]
  have e3 : (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t) =
      log (500/129) * (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (79/50 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (516/125)) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (13/5) (179/50) t)
      (g := fun t : ℝ => log (500/129) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) ^ 2 / (516/125)) / (2 * t))
      (fun t ht => (hS3 t ht).symm)]
    rw [intervalIntegral.integral_add
      ((sigma0_div_two_integrable_Icc (a := (79/50 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)).const_mul (log (500/129))) hJ2int]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit, e1, e2, e3]
  -- assemble the `sigma0` quadrature
  have hs12 := intervalIntegral.integral_add_adjacent_intervals
    (sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (391/325 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
    (sigma0_div_two_integrable_Icc (a := (391/325 : ℝ)) (b := (79/50 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
  have hs123 := intervalIntegral.integral_add_adjacent_intervals
    ((sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (391/325 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).trans
      (sigma0_div_two_integrable_Icc (a := (391/325 : ℝ)) (b := (79/50 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)))
    (sigma0_div_two_integrable_Icc (a := (79/50 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
  have hsig_all : log (500/129) * (∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
      log (500/129) * (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
      log (500/129) * (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      log (500/129) * (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hfac : log (500/129) *
          (∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (500/129) *
          (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (500/129) *
          (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
        log (500/129) *
          ((∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
            (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
            (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t))) := by
      ring
    have hsum : (∫ t in (1 : ℝ)..(391/325 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (391/325 : ℝ)..(79/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (79/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
        (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
      by linarith [hs12, hs123]
    rw [hfac, hsum]
  -- the three certified lower bounds
  have hsig := b9_I_sigma
  have hc := c4_log_c_lo
  have hmul : (1.3547956940601 : ℝ) * (5597961931220961137453/500000000000000000000000) ≤
      log (500/129 : ℝ) *
        (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    refine mul_le_mul hc hsig (by norm_num) ?_
    linarith [hc]
  have hJ3 : (0.0302065718776 : ℝ) ≤
      ∫ t in (391/325 : ℝ)..(79/50 : ℝ), log ((t + 1) / ((8/5) * (129/50 - t))) / (2 * t) := by
    rw [c4_J3_eq]
    have hL := c4_L1_lower
    have hU := c4_int_log_affine
    have h85 := c4_log_85_hi
    have hba := c4_log_1027
    have hprod : log (8/5 : ℝ) * log (1027/782 : ℝ) ≤
        (0.4700036292457356 : ℝ) * (0.2725424693832472 : ℝ) :=
      mul_le_mul h85 hba.2 (le_trans (by norm_num) hba.1) (by norm_num)
    linarith [hL, hU, hprod]
  have hJ2 : (0.1140408959912 : ℝ) ≤
      ∫ t in (79/50 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (516/125)) / (2 * t) := by
    rw [c4_J2_eq]
    have hL := c4_L2_lower
    have hP := c4_log_4128_hi
    have h110 := c4_log_110
    have hprod : log (516/125 : ℝ) * log (110/79 : ℝ) ≤
        (1.4177930281796 : ℝ) * (0.3310325133253948 : ℝ) :=
      mul_le_mul hP h110.2 (le_trans (by norm_num) h110.1) (by norm_num)
    linarith [hL, hprod]
  linarith [hmul, hJ3, hJ2, hsig_all]

/-! ### Row 6 of column 0: `Xi1 (14/5) (167/50)`

Same shape as row 4: `s = 14/5` and `sp = 167/50`, so `sp - 2 = 67/50` and
`sp - sp/s - 1 = 803/700` both lie inside `[1, 11/5]` and the panel splits three ways. -/

/-- `log (9/5)` from above (`x = 2/7`, 14 terms). -/
theorem c6_log_9_5_hi : log (9/5 : ℝ) ≤ (0.5877866649021194 : ℝ) := by
  have h := log_enclosure (y := (9/5 : ℝ)) (x := (2/7 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 14
  refine le_trans h.2 ?_
  norm_num [Finset.sum_range_succ]

/-- `log (117/50)` from above (`x = 67/167`, 22 terms). -/
theorem c6_log_117_50_hi : log (117/50 : ℝ) ≤ (0.8501509293696101 : ℝ) := by
  have h := log_enclosure (y := (117/50 : ℝ)) (x := (67/167 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 22
  refine le_trans h.2 ?_
  norm_num [Finset.sum_range_succ]

/-- `log (4000/1053)`, the `sigma0` coefficient of row 6, from below. -/
theorem c6_log_c_lo : (1.3346511279282 : ℝ) ≤ log (4000/1053 : ℝ) := by
  have h16 : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have hden : log ((9/5) * (117/50) : ℝ) = log (9/5) + log (117/50) :=
    Real.log_mul (by norm_num) (by norm_num)
  have harg : (4000/1053 : ℝ) = 16 / ((9/5) * (117/50)) := by norm_num
  rw [harg, Real.log_div (by norm_num) (by norm_num), h16, hden]
  have h9 := c6_log_9_5_hi
  have hQ := c6_log_117_50_hi
  have h2 := log_two_bounds.1
  linarith [h9, hQ, h2]

/-- Two-sided enclosure of `log (110/67)` (`x = 43/177`, 16 terms). -/
theorem c6_log_110_67 : (0.4957877464014501 : ℝ) ≤ log (110/67 : ℝ) ∧
    log (110/67 : ℝ) ≤ (0.4957877464014502 : ℝ) := by
  have h := log_enclosure (y := (110/67 : ℝ)) (x := (43/177 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (938/803)` (`x = 135/1741`, 16 terms). -/
theorem c6_log_938_803 : (0.155395235059463 : ℝ) ≤ log (938/803 : ℝ) ∧
    log (938/803 : ℝ) ≤ (0.1553952350594631 : ℝ) := by
  have h := log_enclosure (y := (938/803 : ℝ)) (x := (135/1741 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (3141/1400)` (`x = 1741/4541`, 16 terms). -/
theorem c6_log_3141 : (0.80806898393529 : ℝ) ≤ log (3141/1400 : ℝ) ∧
    log (3141/1400 : ℝ) ≤ (0.80806898393534 : ℝ) := by
  have h := log_enclosure (y := (3141/1400 : ℝ)) (x := (1741/4541 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (277/100)` (`x = 177/377`, 18 terms). -/
theorem c6_log_277 : (1.018847320199198 : ℝ) ≤ log (277/100 : ℝ) ∧
    log (277/100 : ℝ) ≤ (1.018847320201017 : ℝ) := by
  have h := log_enclosure (y := (277/100 : ℝ)) (x := (177/377 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 18
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (307/280)` (`x = 27/587`, 14 terms). -/
theorem c6_log_307_280 : (0.0920581444179475 : ℝ) ≤ log (307/280 : ℝ) ∧
    log (307/280 : ℝ) ≤ (0.092058144417948 : ℝ) := by
  have h := log_enclosure (y := (307/280 : ℝ)) (x := (27/587 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 14
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
/-- `L1 = ∫_{803/700}^{67/50} log (t+1)/t` from below: midpoint `1741/1400`, 12 terms,
ratio `15/349`. -/
theorem c6_L1_lower :
    (0.12534915114012 : ℝ) ≤ ∫ t in (803/700 : ℝ)..(67/50 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (803/700 : ℝ) (67/50),
      |(1741/1400 - t) / (1741/1400 + 1)| ≤ 15/349 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(1741/1400 : ℝ) - t| ≤ 27/280 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (1741/1400 : ℝ) + 1 = 3141/1400 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1741/1400 + 1), hden]
    have h3 : |(1741/1400 : ℝ) - t| / (3141/1400) ≤ (27/280) / (3141/1400) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (27/280 : ℝ) / (3141/1400) = 15/349 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (803/700 : ℝ)) (b := (67/50 : ℝ))
    (c := (1741/1400 : ℝ)) (r := (15/349 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (803/700 : ℝ)..(67/50 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (803/700 : ℝ)..(67/50 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc1 := c6_log_3141
  have hba := c6_log_938_803
  have hprod : (0.80806898393529 : ℝ) * (0.155395235059463 : ℝ) ≤
      log (3141/1400 : ℝ) * log (938/803 : ℝ) :=
    mul_le_mul hc1.1 hba.1 (by norm_num : (0 : ℝ) ≤ (0.155395235059463 : ℝ))
      (by linarith [hc1.1] : (0 : ℝ) ≤ log (3141/1400))
  linarith [h, hprod, hc1.1, hba.1, hba.2]

set_option maxHeartbeats 2000000 in
/-- `L2 = ∫_{67/50}^{11/5} log (t+1)/t` from below: midpoint `177/100`, 16 terms,
ratio `43/554`. -/
theorem c6_L2_lower :
    (0.4967287880154 : ℝ) ≤ ∫ t in (67/50 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (67/50 : ℝ) (11/5),
      |(177/100 - t) / (177/100 + 1)| ≤ 43/277 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(177/100 : ℝ) - t| ≤ 43/100 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (177/100 : ℝ) + 1 = 277/100 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 177/100 + 1), hden]
    have h3 : |(177/100 : ℝ) - t| / (277/100) ≤ (43/100) / (277/100) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (43/100 : ℝ) / (277/100) = 43/277 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (67/50 : ℝ)) (b := (11/5 : ℝ))
    (c := (177/100 : ℝ)) (r := (43/277 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 16
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (67/50 : ℝ)..(11/5 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (67/50 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc2 := c6_log_277
  have hba := c6_log_110_67
  have hprod : (1.018847320199198 : ℝ) * (0.4957877464014501 : ℝ) ≤
      log (277/100 : ℝ) * log (110/67 : ℝ) :=
    mul_le_mul hc2.1 hba.1 (by norm_num : (0 : ℝ) ≤ (0.4957877464014501 : ℝ))
      (by linarith [hc2.1] : (0 : ℝ) ≤ log (277/100))
  linarith [h, hprod, hc2.1, hba.1, hba.2]

set_option maxHeartbeats 2000000 in
/-- `∫_{803/700}^{67/50} log (117/50 - t)/(2t)` from above: alternating series around
`1741/1400`, ratio `27/307`, 16 terms. -/
theorem c6_int_log_affine :
    (∫ t in (803/700 : ℝ)..(67/50 : ℝ), log ((117/50 : ℝ) - t) / (2 * t)) ≤
      (0.00722932227751 : ℝ) := by
  have hxr : ∀ t ∈ Set.Icc (803/700 : ℝ) (67/50),
      |(t - 1741/1400) / ((117/50 : ℝ) - 1741/1400)| ≤ 27/307 := by
    intro t ht
    have h1 : |t - (1741/1400 : ℝ)| ≤ 27/280 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 117/50 - 1741/1400)]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 117/50 - 1741/1400)
      (by norm_num : (0 : ℝ) < 307)]
    nlinarith [h1]
  have h := integral_log_affine_upper (a := (803/700 : ℝ)) (b := (67/50 : ℝ))
    (al := (117/50 : ℝ)) (m := (1741/1400 : ℝ)) (r := (27/307 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 16
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [integral_pow_sub_div (a := (803/700 : ℝ)) (b := (67/50 : ℝ))
    (by norm_num) (by norm_num)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  have h1 := c6_log_307_280
  have h2 := c6_log_938_803
  have hprod : log (307/280) * log (938/803) ≤
      (0.092058144417948 : ℝ) * (0.1553952350594631 : ℝ) :=
    mul_le_mul h1.2 h2.2 (by linarith [h2.1] : (0 : ℝ) ≤ log (938/803))
      (by norm_num : (0 : ℝ) ≤ (0.092058144417948 : ℝ))
  nlinarith [h, h2.1, h2.2, hprod]

/-- The middle window of row 6, split into `log (t+1)`, `log (9/5)` and `log (117/50 - t)`. -/
theorem c6_J3_eq :
    (∫ t in (803/700 : ℝ)..(67/50 : ℝ),
        log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t)) =
      (1/2) * (∫ t in (803/700 : ℝ)..(67/50 : ℝ), log (t + 1) / t) -
        (1/2) * log (9/5) * log (938/803) -
        (∫ t in (803/700 : ℝ)..(67/50 : ℝ), log (117/50 - t) / (2 * t)) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (803/700 : ℝ) (67/50 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (803/700 : ℝ) (67/50 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => log (117/50 - t) / (2 * t)) volume
      (803/700 : ℝ) (67/50 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_const.sub continuousOn_id
      · intro t ht
        have h2 : (0 : ℝ) < 117/50 - t := by linarith [ht.2]
        exact ne_of_gt h2
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h2 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hpt : ∀ t ∈ uIcc (803/700 : ℝ) (67/50),
      log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t) =
        (1/2) * (log (t + 1) / t) - (1/2) * log (9/5) * (1 / t) -
          log (117/50 - t) / (2 * t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have h3 : (0 : ℝ) < 117/50 - t := by linarith [ht.2]
    have hden : ((9/5) * (117/50 - t) : ℝ) ≠ 0 := by positivity
    rw [Real.log_div (ne_of_gt h1) hden,
      Real.log_mul (by norm_num : (9/5 : ℝ) ≠ 0) (ne_of_gt h3)]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub
      ((hI1.const_mul (1/2)).sub (hI2.const_mul (1/2 * log (9/5)))) hI3]
  rw [intervalIntegral.integral_sub (hI1.const_mul (1/2)) (hI2.const_mul (1/2 * log (9/5)))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((67/50 : ℝ) / (803/700)) = (938/803 : ℝ) by norm_num]

/-- The upper window of row 6, split into `log (t+1)` and `log (1053/250)`. -/
theorem c6_J2_eq :
    (∫ t in (67/50 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (1053/250)) / (2 * t)) =
      (∫ t in (67/50 : ℝ)..(11/5 : ℝ), log (t + 1) / t) -
        (1/2) * log (1053/250) * log (110/67) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (67/50 : ℝ) (11/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (67/50 : ℝ) (11/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (67/50 : ℝ) (11/5),
      log ((t + 1) ^ 2 / (1053/250)) / (2 * t) =
        log (t + 1) / t - (1/2) * log (1053/250) * (1 / t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have hnum : ((t + 1) ^ 2 : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hnum (by norm_num : (1053/250 : ℝ) ≠ 0), Real.log_pow]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub hI1 (hI2.const_mul (1/2 * log (1053/250)))]
  rw [intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((11/5 : ℝ) / (67/50)) = (110/67 : ℝ) by norm_num]

/-- On `(1, 11/5)` the row-6 kernel is the `sigma0` term plus its two windows. -/
theorem c6_xi1_eq {t : ℝ} (ht : t ∈ Set.uIoo (1 : ℝ) (11/5)) :
    Wu04Functional.Xi1 (14/5) (167/50) t =
      log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)) +
        Wu04Functional.ind (67/50) 3 t * (log ((t + 1) ^ 2 / (1053/250)) / (2 * t)) +
        Wu04Functional.ind (803/700) (67/50) t *
          (log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t)) := by
  rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
    max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)] at ht
  unfold Wu04Functional.Xi1
  have hA : ((14/5 : ℝ) - 1) * (167/50 - 1) = 1053/250 := by norm_num
  have hB : (16 : ℝ) / (1053/250) = 4000/1053 := by norm_num
  have hC : (167/50 : ℝ) - 2 = 67/50 := by norm_num
  have hD : (167/50 : ℝ) - 167/50/(14/5) - 1 = 803/700 := by norm_num
  have hE : (14/5 : ℝ) - 1 = 9/5 := by norm_num
  have hF : (167/50 : ℝ) - 1 = 117/50 := by norm_num
  rw [hA, hB, hC, hD, hE, hF]
  ring

/-- `integralMatrix 6 0` is the `Xi1 (14/5) (167/50)` quadrature on `[1, 11/5]`. -/
theorem integralMatrix_6_0_eq :
    Wu04Table.integralMatrix 6 0 =
      ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_6_0` of Wu's Section 7 matrix**, certified on the `[1, 11/5]` panel. -/
theorem c6_entry_6_0_leaf :
    (Wu04Table.candidateMatrixQ 6 0 : ℝ) ≤ Wu04Table.integralMatrix 6 0 := by
  have hc : (Wu04Table.candidateMatrixQ 6 0 : ℝ) = 1649911 / 10^7 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc, integralMatrix_6_0_eq]
  have hS1 : ∀ t ∈ Set.uIoo (1 : ℝ) (803/700),
      log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)) =
        Wu04Functional.Xi1 (14/5) (167/50) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 803/700),
      max_eq_right (by norm_num : (1 : ℝ) ≤ 803/700)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨ht.1, by linarith [ht.2]⟩
    rw [c6_xi1_eq ht']
    have e1 : Wu04Functional.ind (67/50) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (803/700) (67/50) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    rw [e1, e2]
    ring
  have hS2 : ∀ t ∈ Set.uIoo (803/700 : ℝ) (67/50),
      (log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t)) =
        Wu04Functional.Xi1 (14/5) (167/50) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (803/700 : ℝ) ≤ 67/50),
      max_eq_right (by norm_num : (803/700 : ℝ) ≤ 67/50)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [c6_xi1_eq ht']
    have e1 : Wu04Functional.ind (67/50) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (803/700) (67/50) t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [e1, e2]
    ring
  have hS3 : ∀ t ∈ Set.uIoo (67/50 : ℝ) (11/5),
      (log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) ^ 2 / (1053/250)) / (2 * t)) =
        Wu04Functional.Xi1 (14/5) (167/50) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (67/50 : ℝ) ≤ 11/5),
      max_eq_right (by norm_num : (67/50 : ℝ) ≤ 11/5)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨by linarith [ht.1], ht.2⟩
    rw [c6_xi1_eq ht']
    have e1 : Wu04Functional.ind (67/50) 3 t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, by linarith [ht.2]⟩
    have e2 : Wu04Functional.ind (803/700) (67/50) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨-, h2⟩; linarith [ht.1])
    rw [e1, e2]
    ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (14/5) (167/50) t) volume
      (1 : ℝ) (803/700) :=
    ((sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (803/700 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (4000/1053))).congr_uIoo hS1
  have hJ3int : IntervalIntegrable (fun t : ℝ => log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t))
      volume (803/700 : ℝ) (67/50) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · refine ContinuousOn.div (continuousOn_id.add continuousOn_const) ?_ ?_
        · exact continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
        · intro t ht
          have h4 : (0 : ℝ) < 117/50 - t := by linarith [ht.2]
          exact ne_of_gt (by positivity)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        have h6 : (0 : ℝ) < 117/50 - t := by linarith [ht.2]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hJ2int : IntervalIntegrable (fun t : ℝ => log ((t + 1) ^ 2 / (1053/250)) / (2 * t))
      volume (67/50 : ℝ) (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_id.add continuousOn_const).pow 2 |>.div_const (1053/250)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hI2 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (14/5) (167/50) t) volume
      (803/700 : ℝ) (67/50) :=
    (((sigma0_div_two_integrable_Icc (a := (803/700 : ℝ)) (b := (67/50 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (4000/1053))).add hJ3int).congr_uIoo hS2
  have hI3 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (14/5) (167/50) t) volume
      (67/50 : ℝ) (11/5) :=
    (((sigma0_div_two_integrable_Icc (a := (67/50 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (4000/1053))).add hJ2int).congr_uIoo hS3
  have hsplit : (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) =
      (∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) +
        (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) +
        (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hI12 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (14/5) (167/50) t) volume
        (1 : ℝ) (67/50) := hI1.trans hI2
    have h123 := intervalIntegral.integral_add_adjacent_intervals hI12 hI3
    linarith [h12, h123]
  have e1 : (∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) =
      log (4000/1053) * (∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (14/5) (167/50) t)
      (g := fun t : ℝ => log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)))
      (fun t ht => (hS1 t ht).symm)]
    rw [intervalIntegral.integral_const_mul]
  have e2 : (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) =
      log (4000/1053) * (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (803/700 : ℝ)..(67/50 : ℝ),
          log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (14/5) (167/50) t)
      (g := fun t : ℝ => log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t))
      (fun t ht => (hS2 t ht).symm)]
    rw [intervalIntegral.integral_add
      ((sigma0_div_two_integrable_Icc (a := (803/700 : ℝ)) (b := (67/50 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)).const_mul (log (4000/1053))) hJ3int]
    rw [intervalIntegral.integral_const_mul]
  have e3 : (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t) =
      log (4000/1053) * (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (67/50 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (1053/250)) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (14/5) (167/50) t)
      (g := fun t : ℝ => log (4000/1053) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) ^ 2 / (1053/250)) / (2 * t))
      (fun t ht => (hS3 t ht).symm)]
    rw [intervalIntegral.integral_add
      ((sigma0_div_two_integrable_Icc (a := (67/50 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)).const_mul (log (4000/1053))) hJ2int]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit, e1, e2, e3]
  have hs12 := intervalIntegral.integral_add_adjacent_intervals
    (sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (803/700 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
    (sigma0_div_two_integrable_Icc (a := (803/700 : ℝ)) (b := (67/50 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
  have hs123 := intervalIntegral.integral_add_adjacent_intervals
    ((sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (803/700 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).trans
      (sigma0_div_two_integrable_Icc (a := (803/700 : ℝ)) (b := (67/50 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)))
    (sigma0_div_two_integrable_Icc (a := (67/50 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
  have hsig_all : log (4000/1053) * (∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
      log (4000/1053) * (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
      log (4000/1053) * (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      log (4000/1053) * (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hfac : log (4000/1053) *
          (∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (4000/1053) *
          (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (4000/1053) *
          (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
        log (4000/1053) *
          ((∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
            (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
            (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t))) := by
      ring
    have hsum : (∫ t in (1 : ℝ)..(803/700 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (803/700 : ℝ)..(67/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (67/50 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
        (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
      by linarith [hs12, hs123]
    rw [hfac, hsum]
  have hsig := b9_I_sigma
  have hc6 := c6_log_c_lo
  have hmul : (1.3346511279282 : ℝ) * (5597961931220961137453/500000000000000000000000) ≤
      log (4000/1053 : ℝ) *
        (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    refine mul_le_mul hc6 hsig (by norm_num) ?_
    linarith [hc6]
  have hJ3 : (0.0097756298139 : ℝ) ≤
      ∫ t in (803/700 : ℝ)..(67/50 : ℝ),
        log ((t + 1) / ((9/5) * (117/50 - t))) / (2 * t) := by
    rw [c6_J3_eq]
    have hL := c6_L1_lower
    have hU := c6_int_log_affine
    have h95 := c6_log_9_5_hi
    have hba := c6_log_938_803
    have hprod : log (9/5 : ℝ) * log (938/803 : ℝ) ≤
        (0.5877866649021194 : ℝ) * (0.1553952350594631 : ℝ) :=
      mul_le_mul h95 hba.2 (by linarith [hba.1] : (0 : ℝ) ≤ log (938/803)) (by norm_num)
    linarith [hL, hU, hprod]
  have hJ2 : (0.1402728683504 : ℝ) ≤
      ∫ t in (67/50 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (1053/250)) / (2 * t) := by
    rw [c6_J2_eq]
    have hL := c6_L2_lower
    have hP : log (1053/250 : ℝ) ≤ (1.43793759427174 : ℝ) := by
      have h1 := c6_log_9_5_hi
      have h2 := c6_log_117_50_hi
      have hm : log (1053/250 : ℝ) = log (9/5) + log (117/50) := by
        rw [← Real.log_mul (by norm_num : (9/5 : ℝ) ≠ 0) (by norm_num : (117/50 : ℝ) ≠ 0)]
        norm_num
      rw [hm]
      linarith [h1, h2]
    have h110 := c6_log_110_67
    have hprod : log (1053/250 : ℝ) * log (110/67 : ℝ) ≤
        (1.43793759427174 : ℝ) * (0.4957877464014502 : ℝ) :=
      mul_le_mul hP h110.2 (by linarith [h110.1] : (0 : ℝ) ≤ log (110/67)) (by norm_num)
    linarith [hL, hprod]
  linarith [hmul, hJ3, hJ2, hsig_all]

/-! ### Row 7 of column 0: `Xi1 (29/10) (319/100)`

`s = 29/10`, `sp = 319/100`, so `sp - 2 = 119/100` and `sp - sp/s - 1 = 109/100`: both windows live
on `[1, 11/5]` and the panel splits three ways. The candidate `1737478/10^7` leaves only `5.6e-8`
against the true entry and the forty-panel `sigma0` quadrature already spends `3.84e-8` of that, so
this certificate is tight: it clears the candidate by `4.3e-9`. -/

set_option maxHeartbeats 4000000 in
/-- Two-sided enclosure of `log (19/10)` (`x = 9/29`, 24 terms). -/
theorem c7_log_19_10 : (0.6418538861723947 : ℝ) ≤ log (19/10 : ℝ) ∧
    log (19/10 : ℝ) ≤ (0.6418538861723949 : ℝ) := by
  have h := log_enclosure (y := (19/10 : ℝ)) (x := (9/29 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 24
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 4000000 in
/-- Two-sided enclosure of `log (219/100)` (`x = 119/319`, 26 terms). -/
theorem c7_log_219_100 : (0.7839015438284094 : ℝ) ≤ log (219/100 : ℝ) ∧
    log (219/100 : ℝ) ≤ (0.7839015438284095 : ℝ) := by
  have h := log_enclosure (y := (219/100 : ℝ)) (x := (119/319 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 26
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (16000/4161)`, the `sigma0` coefficient of row 7, from below. -/
theorem c7_log_c_lo : (1.3468332921991 : ℝ) ≤ log (16000/4161 : ℝ) := by
  have h16 : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have hden : log ((19/10) * (219/100) : ℝ) = log (19/10) + log (219/100) :=
    Real.log_mul (by norm_num) (by norm_num)
  have harg : (16000/4161 : ℝ) = 16 / ((19/10) * (219/100)) := by norm_num
  rw [harg, Real.log_div (by norm_num) (by norm_num), h16, hden]
  have h19 := c7_log_19_10.2
  have h219 := c7_log_219_100.2
  have h2 := log_two_bounds.1
  linarith [h19, h219, h2]

set_option maxHeartbeats 4000000 in
/-- Two-sided enclosure of `log (107/50)` (`x = 57/107`, 30 terms). -/
theorem c7_log_107_50 : (0.760805829033 : ℝ) ≤ log (107/50 : ℝ) ∧
    log (107/50 : ℝ) ≤ (0.760805829034 : ℝ) := by
  have h := log_enclosure (y := (107/50 : ℝ)) (x := (57/157 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 30
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (119/109)` (`x = 5/114`, 16 terms). -/
theorem c7_log_119_109 : (0.0877756108823856 : ℝ) ≤ log (119/109 : ℝ) ∧
    log (119/109 : ℝ) ≤ (0.0877756108823857 : ℝ) := by
  have h := log_enclosure (y := (119/109 : ℝ)) (x := (5/114 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (539/200)` (`x = 339/739`, 26 terms). -/
theorem c7_log_539_200 : (0.9913982043609 : ℝ) ≤ log (539/200 : ℝ) ∧
    log (539/200 : ℝ) ≤ (0.991398204361 : ℝ) := by
  have h := log_enclosure (y := (539/200 : ℝ)) (x := (339/739 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 26
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (220/119)` (`x = 101/339`, 18 terms). -/
theorem c7_log_220_119 : (0.6145040532408321 : ℝ) ≤ log (220/119 : ℝ) ∧
    log (220/119 : ℝ) ≤ (0.6145040532408322 : ℝ) := by
  have h := log_enclosure (y := (220/119 : ℝ)) (x := (101/339 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 18
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (21/20)` (`x = 1/41`, 16 terms). -/
theorem c7_log_21_20 : (0.048790164169432 : ℝ) ≤ log (21/20 : ℝ) ∧
    log (21/20 : ℝ) ≤ (0.0487901641694321 : ℝ) := by
  have h := log_enclosure (y := (21/20 : ℝ)) (x := (1/41 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
/-- `L1 = ∫_{109/100}^{119/100} log (t+1)/t` from below: midpoint `57/50`, 8 terms, ratio `5/214`. -/
theorem c7_L1_lower :
    (0.06674220329 : ℝ) ≤ ∫ t in (109/100 : ℝ)..(119/100 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (109/100 : ℝ) (119/100),
      |(57/50 - t) / (57/50 + 1)| ≤ 5/214 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(57/50 : ℝ) - t| ≤ 1/20 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (57/50 : ℝ) + 1 = 107/50 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 57/50 + 1), hden]
    have h3 : |(57/50 : ℝ) - t| / (107/50) ≤ (1/20) / (107/50) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (1/20 : ℝ) / (107/50) = 5/214 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (109/100 : ℝ)) (b := (119/100 : ℝ))
    (c := (57/50 : ℝ)) (r := (5/214 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 8
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (109/100 : ℝ)..(119/100 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (109/100 : ℝ)..(119/100 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc1 := c7_log_107_50
  have hba := c7_log_119_109
  have hprod : (0.760805829033 : ℝ) * (0.0877756108823856 : ℝ) ≤
      log (107/50 : ℝ) * log (119/109 : ℝ) :=
    mul_le_mul hc1.1 hba.1 (by norm_num : (0 : ℝ) ≤ (0.0877756108823856 : ℝ))
      (by linarith [hc1.1] : (0 : ℝ) ≤ log (107/50))
  linarith [h, hprod, hc1.1, hba.1, hba.2]

set_option maxHeartbeats 2000000 in
/-- `L2 = ∫_{119/100}^{11/5} log (t+1)/t` from below: midpoint `339/200`, 18 terms, ratio `101/539`. -/
theorem c7_L2_lower :
    (0.5936887443 : ℝ) ≤ ∫ t in (119/100 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (119/100 : ℝ) (11/5),
      |(339/200 - t) / (339/200 + 1)| ≤ 101/539 := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : |(339/200 : ℝ) - t| ≤ 101/200 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hden : (339/200 : ℝ) + 1 = 539/200 := by norm_num
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 339/200 + 1), hden]
    have h3 : |(339/200 : ℝ) - t| / (539/200) ≤ (101/200) / (539/200) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h4 : (101/200 : ℝ) / (539/200) = 101/539 := by norm_num
    linarith [h3, h4]
  have h := log_succ_integral_lower (a := (119/100 : ℝ)) (b := (11/5 : ℝ))
    (c := (339/200 : ℝ)) (r := (101/539 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hxr 18
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  ring_nf at h
  have hint : (∫ t in (119/100 : ℝ)..(11/5 : ℝ), log (1 + t) * t⁻¹) =
      ∫ t in (119/100 : ℝ)..(11/5 : ℝ), log (t + 1) / t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (1 + t : ℝ) = t + 1 := by ring
    rw [h1]
    ring
  rw [hint] at h
  have hc2 := c7_log_539_200
  have hba := c7_log_220_119
  have hprod : (0.9913982043609 : ℝ) * (0.6145040532408321 : ℝ) ≤
      log (539/200 : ℝ) * log (220/119 : ℝ) :=
    mul_le_mul hc2.1 hba.1 (by norm_num : (0 : ℝ) ≤ (0.6145040532408321 : ℝ))
      (by linarith [hc2.1] : (0 : ℝ) ≤ log (539/200))
  linarith [h, hprod, hc2.1, hba.1, hba.2]

set_option maxHeartbeats 2000000 in
/-- `∫_{109/100}^{119/100} log (219/100 - t)/(2t)` from above: alternating series around `57/50`,
ratio `1/21`, 12 terms. -/
theorem c7_int_log_affine :
    (∫ t in (109/100 : ℝ)..(119/100 : ℝ), log ((219/100 : ℝ) - t) / (2 * t)) ≤
      (0.0021552705369 : ℝ) := by
  have hxr : ∀ t ∈ Set.Icc (109/100 : ℝ) (119/100),
      |(t - 57/50) / ((219/100 : ℝ) - 57/50)| ≤ 1/21 := by
    intro t ht
    have h1 : |t - (57/50 : ℝ)| ≤ 1/20 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 219/100 - 57/50)]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 219/100 - 57/50)
      (by norm_num : (0 : ℝ) < 21)]
    nlinarith [h1]
  have h := integral_log_affine_upper (a := (109/100 : ℝ)) (b := (119/100 : ℝ))
    (al := (219/100 : ℝ)) (m := (57/50 : ℝ)) (r := (1/21 : ℝ)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [integral_pow_sub_div (a := (109/100 : ℝ)) (b := (119/100 : ℝ))
    (by norm_num) (by norm_num)] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.choose] at h
  have h1 := c7_log_21_20
  have h2 := c7_log_119_109
  have hprod : log (21/20) * log (119/109) ≤
      (0.0487901641694321 : ℝ) * (0.0877756108823857 : ℝ) :=
    mul_le_mul h1.2 h2.2 (by linarith [h2.1] : (0 : ℝ) ≤ log (119/109))
      (by norm_num : (0 : ℝ) ≤ (0.0487901641694321 : ℝ))
  nlinarith [h, h2.1, h2.2, hprod]

/-- The middle window of row 7, split into `log (t+1)`, `log (19/10)` and `log (219/100 - t)`. -/
theorem c7_J3_eq :
    (∫ t in (109/100 : ℝ)..(119/100 : ℝ),
        log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t)) =
      (1/2) * (∫ t in (109/100 : ℝ)..(119/100 : ℝ), log (t + 1) / t) -
        (1/2) * log (19/10) * log (119/109) -
        (∫ t in (109/100 : ℝ)..(119/100 : ℝ), log (219/100 - t) / (2 * t)) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (109/100 : ℝ) (119/100 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (109/100 : ℝ) (119/100 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => log (219/100 - t) / (2 * t)) volume
      (109/100 : ℝ) (119/100 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact continuousOn_const.sub continuousOn_id
      · intro t ht
        have h2 : (0 : ℝ) < 219/100 - t := by linarith [ht.2]
        exact ne_of_gt h2
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h2 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hpt : ∀ t ∈ uIcc (109/100 : ℝ) (119/100),
      log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t) =
        (1/2) * (log (t + 1) / t) - (1/2) * log (19/10) * (1 / t) -
          log (219/100 - t) / (2 * t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have h3 : (0 : ℝ) < 219/100 - t := by linarith [ht.2]
    have hden : ((19/10) * (219/100 - t) : ℝ) ≠ 0 := by positivity
    rw [Real.log_div (ne_of_gt h1) hden,
      Real.log_mul (by norm_num : (19/10 : ℝ) ≠ 0) (ne_of_gt h3)]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub
      ((hI1.const_mul (1/2)).sub (hI2.const_mul (1/2 * log (19/10)))) hI3]
  rw [intervalIntegral.integral_sub (hI1.const_mul (1/2)) (hI2.const_mul (1/2 * log (19/10)))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((119/100 : ℝ) / (109/100)) = (119/109 : ℝ) by norm_num]

/-- The upper window of row 7, split into `log (t+1)` and `log (4161/1000)`. -/
theorem c7_J2_eq :
    (∫ t in (119/100 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (4161/1000)) / (2 * t)) =
      (∫ t in (119/100 : ℝ)..(11/5 : ℝ), log (t + 1) / t) -
        (1/2) * log (4161/1000) * log (220/119) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (119/100 : ℝ) (11/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (119/100 : ℝ) (11/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (119/100 : ℝ) (11/5),
      log ((t + 1) ^ 2 / (4161/1000)) / (2 * t) =
        log (t + 1) / t - (1/2) * log (4161/1000) * (1 / t) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : (0 : ℝ) < t + 1 := by linarith [ht.1]
    have hnum : ((t + 1) ^ 2 : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hnum (by norm_num : (4161/1000 : ℝ) ≠ 0), Real.log_pow]
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_sub hI1 (hI2.const_mul (1/2 * log (4161/1000)))]
  rw [intervalIntegral.integral_const_mul,
    integral_one_div_exp (by norm_num) (by norm_num)]
  rw [show ((11/5 : ℝ) / (119/100)) = (220/119 : ℝ) by norm_num]

/-- On `(1, 11/5)` the row-7 kernel is the `sigma0` term plus its two windows. -/
theorem c7_xi1_eq {t : ℝ} (ht : t ∈ Set.uIoo (1 : ℝ) (11/5)) :
    Wu04Functional.Xi1 (29/10) (319/100) t =
      log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)) +
        Wu04Functional.ind (119/100) 3 t * (log ((t + 1) ^ 2 / (4161/1000)) / (2 * t)) +
        Wu04Functional.ind (109/100) (119/100) t *
          (log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t)) := by
  rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
    max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)] at ht
  unfold Wu04Functional.Xi1
  have hA : ((29/10 : ℝ) - 1) * (319/100 - 1) = 4161/1000 := by norm_num
  have hB : (16 : ℝ) / (4161/1000) = 16000/4161 := by norm_num
  have hC : (319/100 : ℝ) - 2 = 119/100 := by norm_num
  have hD : (319/100 : ℝ) - 319/100/(29/10) - 1 = 109/100 := by norm_num
  have hE : (29/10 : ℝ) - 1 = 19/10 := by norm_num
  have hF : (319/100 : ℝ) - 1 = 219/100 := by norm_num
  rw [hA, hB, hC, hD, hE, hF]
  ring

/-- `integralMatrix 7 0` is the `Xi1 (29/10) (319/100)` quadrature on `[1, 11/5]`. -/
theorem integralMatrix_7_0_eq :
    Wu04Table.integralMatrix 7 0 =
      ∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_7_0` of Wu's Section 7 matrix**, certified on the `[1, 11/5]` panel. -/
theorem c7_entry_7_0_leaf :
    (Wu04Table.candidateMatrixQ 7 0 : ℝ) ≤ Wu04Table.integralMatrix 7 0 := by
  have hc : (Wu04Table.candidateMatrixQ 7 0 : ℝ) = 1737478 / 10^7 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc, integralMatrix_7_0_eq]
  have hS1 : ∀ t ∈ Set.uIoo (1 : ℝ) (109/100),
      log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)) =
        Wu04Functional.Xi1 (29/10) (319/100) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 109/100),
      max_eq_right (by norm_num : (1 : ℝ) ≤ 109/100)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨ht.1, by linarith [ht.2]⟩
    rw [c7_xi1_eq ht']
    have e1 : Wu04Functional.ind (119/100) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (109/100) (119/100) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    rw [e1, e2]
    ring
  have hS2 : ∀ t ∈ Set.uIoo (109/100 : ℝ) (119/100),
      (log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t)) =
        Wu04Functional.Xi1 (29/10) (319/100) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (109/100 : ℝ) ≤ 119/100),
      max_eq_right (by norm_num : (109/100 : ℝ) ≤ 119/100)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [c7_xi1_eq ht']
    have e1 : Wu04Functional.ind (119/100) 3 t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨h1, -⟩; linarith [ht.2])
    have e2 : Wu04Functional.ind (109/100) (119/100) t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [e1, e2]
    ring
  have hS3 : ∀ t ∈ Set.uIoo (119/100 : ℝ) (11/5),
      (log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)) +
          log ((t + 1) ^ 2 / (4161/1000)) / (2 * t)) =
        Wu04Functional.Xi1 (29/10) (319/100) t := by
    intro t ht
    rw [Set.uIoo, min_eq_left (by norm_num : (119/100 : ℝ) ≤ 11/5),
      max_eq_right (by norm_num : (119/100 : ℝ) ≤ 11/5)] at ht
    have ht' : t ∈ Set.uIoo (1 : ℝ) (11/5) := by
      rw [Set.uIoo, min_eq_left (by norm_num : (1 : ℝ) ≤ 11/5),
        max_eq_right (by norm_num : (1 : ℝ) ≤ 11/5)]
      exact ⟨by linarith [ht.1], ht.2⟩
    rw [c7_xi1_eq ht']
    have e1 : Wu04Functional.ind (119/100) 3 t = 1 := by
      unfold Wu04Functional.ind
      exact if_pos ⟨le_of_lt ht.1, by linarith [ht.2]⟩
    have e2 : Wu04Functional.ind (109/100) (119/100) t = 0 := by
      unfold Wu04Functional.ind
      exact if_neg (by rintro ⟨-, h2⟩; linarith [ht.1])
    rw [e1, e2]
    ring
  have hI1 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (29/10) (319/100) t) volume
      (1 : ℝ) (109/100) :=
    ((sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (109/100 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (16000/4161))).congr_uIoo hS1
  have hJ3int : IntervalIntegrable (fun t : ℝ => log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t))
      volume (109/100 : ℝ) (119/100) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · refine ContinuousOn.div (continuousOn_id.add continuousOn_const) ?_ ?_
        · exact continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
        · intro t ht
          have h4 : (0 : ℝ) < 219/100 - t := by linarith [ht.2]
          exact ne_of_gt (by positivity)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        have h6 : (0 : ℝ) < 219/100 - t := by linarith [ht.2]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hJ2int : IntervalIntegrable (fun t : ℝ => log ((t + 1) ^ 2 / (4161/1000)) / (2 * t))
      volume (119/100 : ℝ) (11/5) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    refine ContinuousOn.div ?_ ?_ ?_
    · refine Real.continuousOn_log.comp ?_ ?_
      · exact (continuousOn_id.add continuousOn_const).pow 2 |>.div_const (4161/1000)
      · intro t ht
        have h5 : (0 : ℝ) < t + 1 := by linarith [ht.1]
        exact ne_of_gt (by positivity)
    · exact continuousOn_const.mul continuousOn_id
    · intro t ht
      have h5 : (0 : ℝ) < t := by linarith [ht.1]
      exact ne_of_gt (by positivity)
  have hI2 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (29/10) (319/100) t) volume
      (109/100 : ℝ) (119/100) :=
    (((sigma0_div_two_integrable_Icc (a := (109/100 : ℝ)) (b := (119/100 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (16000/4161))).add hJ3int).congr_uIoo hS2
  have hI3 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (29/10) (319/100) t) volume
      (119/100 : ℝ) (11/5) :=
    (((sigma0_div_two_integrable_Icc (a := (119/100 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).const_mul (log (16000/4161))).add hJ2int).congr_uIoo hS3
  have hsplit : (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) =
      (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) +
        (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) +
        (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hI12 : IntervalIntegrable (fun t : ℝ => Wu04Functional.Xi1 (29/10) (319/100) t) volume
        (1 : ℝ) (119/100) := hI1.trans hI2
    have h123 := intervalIntegral.integral_add_adjacent_intervals hI12 hI3
    linarith [h12, h123]
  have e1 : (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) =
      log (16000/4161) * (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (29/10) (319/100) t)
      (g := fun t : ℝ => log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)))
      (fun t ht => (hS1 t ht).symm)]
    rw [intervalIntegral.integral_const_mul]
  have e2 : (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) =
      log (16000/4161) * (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (109/100 : ℝ)..(119/100 : ℝ),
          log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (29/10) (319/100) t)
      (g := fun t : ℝ => log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t))
      (fun t ht => (hS2 t ht).symm)]
    rw [intervalIntegral.integral_add
      ((sigma0_div_two_integrable_Icc (a := (109/100 : ℝ)) (b := (119/100 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)).const_mul (log (16000/4161))) hJ3int]
    rw [intervalIntegral.integral_const_mul]
  have e3 : (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) =
      log (16000/4161) * (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (119/100 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (4161/1000)) / (2 * t)) := by
    rw [intervalIntegral.integral_congr_uIoo (f := fun t : ℝ =>
        Wu04Functional.Xi1 (29/10) (319/100) t)
      (g := fun t : ℝ => log (16000/4161) * (Wu04Integral.sigma0 t / (2 * t)) +
        log ((t + 1) ^ 2 / (4161/1000)) / (2 * t))
      (fun t ht => (hS3 t ht).symm)]
    rw [intervalIntegral.integral_add
      ((sigma0_div_two_integrable_Icc (a := (119/100 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)).const_mul (log (16000/4161))) hJ2int]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit, e1, e2, e3]
  have hs12 := intervalIntegral.integral_add_adjacent_intervals
    (sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (109/100 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
    (sigma0_div_two_integrable_Icc (a := (109/100 : ℝ)) (b := (119/100 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
  have hs123 := intervalIntegral.integral_add_adjacent_intervals
    ((sigma0_div_two_integrable_Icc (a := (1 : ℝ)) (b := (109/100 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num)).trans
      (sigma0_div_two_integrable_Icc (a := (109/100 : ℝ)) (b := (119/100 : ℝ)) (by norm_num)
        (by norm_num) (by norm_num)))
    (sigma0_div_two_integrable_Icc (a := (119/100 : ℝ)) (b := (11/5 : ℝ)) (by norm_num)
      (by norm_num) (by norm_num))
  have hsig_all : log (16000/4161) * (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
      log (16000/4161) * (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
      log (16000/4161) * (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      log (16000/4161) * (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hfac : log (16000/4161) *
          (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (16000/4161) *
          (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        log (16000/4161) *
          (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
        log (16000/4161) *
          ((∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
            (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
            (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t))) := by
      ring
    have hsum : (∫ t in (1 : ℝ)..(109/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (109/100 : ℝ)..(119/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (119/100 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
        (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
      by linarith [hs12, hs123]
    rw [hfac, hsum]
  have hsig := b9_I_sigma
  have hc6 := c7_log_c_lo
  have hmul : (1.3468332921991 : ℝ) * (5597961931220961137453/500000000000000000000000) ≤
      log (16000/4161 : ℝ) *
        (∫ t in (1 : ℝ)..(11/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    refine mul_le_mul hc6 hsig (by norm_num) ?_
    linarith [hc6]
  have hJ3 : (0.0030462726 : ℝ) ≤
      ∫ t in (109/100 : ℝ)..(119/100 : ℝ),
        log ((t + 1) / ((19/10) * (219/100 - t))) / (2 * t) := by
    rw [c7_J3_eq]
    have hL := c7_L1_lower
    have hU := c7_int_log_affine
    have h95 := c7_log_19_10
    have hba := c7_log_119_109
    have hprod : log (19/10 : ℝ) * log (119/109 : ℝ) ≤
        (0.6418538861723949 : ℝ) * (0.0877756108823857 : ℝ) :=
      mul_le_mul h95.2 hba.2 (by linarith [hba.1] : (0 : ℝ) ≤ log (119/109)) (by norm_num)
    linarith [hL, hU, hprod]
  have hJ2 : (0.1556224989 : ℝ) ≤
      ∫ t in (119/100 : ℝ)..(11/5 : ℝ), log ((t + 1) ^ 2 / (4161/1000)) / (2 * t) := by
    rw [c7_J2_eq]
    have hL := c7_L2_lower
    have hP : log (4161/1000 : ℝ) ≤ (1.4257554300008044 : ℝ) := by
      have h1 := c7_log_19_10
      have h2 := c7_log_219_100
      have hm : log (4161/1000 : ℝ) = log (19/10) + log (219/100) := by
        rw [← Real.log_mul (by norm_num : (19/10 : ℝ) ≠ 0) (by norm_num : (219/100 : ℝ) ≠ 0)]
        norm_num
      rw [hm]
      linarith [h1, h2]
    have h110 := c7_log_220_119
    have hprod : log (4161/1000 : ℝ) * log (220/119 : ℝ) ≤
        (1.4257554300008044 : ℝ) * (0.6145040532408322 : ℝ) :=
      mul_le_mul hP h110.2 (by linarith [h110.1] : (0 : ℝ) ≤ log (220/119)) (by norm_num)
    linarith [hL, hprod]
  linarith [hmul, hJ3, hJ2, hsig_all]

end LeanLab.ChenDoubleSieve.Burst9MatrixCol0

#print axioms LeanLab.ChenDoubleSieve.Burst9MatrixCol0.c4_entry_4_0_leaf
#print axioms LeanLab.ChenDoubleSieve.Burst9MatrixCol0.c8_entry_8_0_leaf
#print axioms LeanLab.ChenDoubleSieve.Burst9MatrixCol0.c6_entry_6_0_leaf
#print axioms LeanLab.ChenDoubleSieve.Burst9MatrixCol0.c7_entry_7_0_leaf
