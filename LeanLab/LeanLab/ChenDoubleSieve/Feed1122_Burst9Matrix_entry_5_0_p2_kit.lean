import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Feed 1122, second split of `Burst9Matrix.entry_5_0`: the shared toolkit

Source: Wu 2004, arXiv 0705.1652, display 7.2, kernel Xi1 of display 3.21, page 14, and the
`sigma0` kernel of displays 3.21 and 3.22. This module is a verbatim copy of lines 27 to 1254, the toolkit before the panels, of
`LeanLab.ChenDoubleSieve.Burst9MatrixCol0`, with `private` dropped where a later module needs the
lemma and a new namespace. The copy exists because `Burst9MatrixCol0` as one module goes over the
8 GB build cap, so it cannot be imported here; the proofs are unchanged.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit
open Wu04Table
open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LeanLab.ChenDoubleSieve.Wu04Integral LeanLab.ChenDoubleSieve.Wu04Functional



/-- `∫ 1/x dx = log (b/a)` on a positive interval, from the fundamental theorem of calculus. -/
theorem integral_one_div_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
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
theorem sigma_diagonal_eq {t : ℝ} (ht : 1 < t) :
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
theorem hasDerivAt_sigma_diagonal {t : ℝ} (ht : 1 < t) :
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
theorem sigma0_hasDerivAt {t : ℝ} (ht : 1 < t) (_hD : 0 < 1 - Wu04Integral.sigma 3 5 4) :
    HasDerivAt Wu04Integral.sigma0
      ((log ((t + 2) / 3) / (t + 1)) / (1 - Wu04Integral.sigma 3 5 4)) t := by
  have h := (hasDerivAt_sigma_diagonal ht).div_const (1 - Wu04Integral.sigma 3 5 4)
  exact h

/-- Exact value of `∫ (c-t)^m / t`: expand the binomial and divide by `t`. -/
theorem integral_sub_pow_div {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (m : ℕ) :
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
theorem integral_log_mul_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j : ℕ) :
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
theorem log_succ_lower_pointwise {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b)
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
theorem integral_log_series_lower {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (n : ℕ)
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
theorem log_succ_integral_lower {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b)
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
theorem inv_series_exact {M s : ℝ} (hM : 0 < M) (hM1 : M + s ≠ 0) (n : ℕ) :
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
theorem inv_series_remainder {M s : ℝ} (hM : 0 < M) (hs : |s| < M) (n : ℕ) :
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
theorem integral_log_mul_sub_pow {a b m : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (k : ℕ) :
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
theorem sigma_eq_log_sub {a b c : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 < c) :
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
theorem integral_log_div_one_add_bounds {a b m : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
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
theorem sigma_lower_bound {a b c m : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 < c)
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
theorem sigma_upper_bound {a b c m : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 0 < c)
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
theorem log_enclosure {y x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
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

theorem log_2_2_bounds : (0.78845736036 : ℝ) ≤ log (11/5) ∧ log (11/5) ≤ (0.78845736037 : ℝ) := by
  have h := log_enclosure (y := 11/5) (x := (3/8 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

theorem log_three_bounds : (1.09861228866 : ℝ) ≤ log 3 ∧ log 3 ≤ (1.09861228867 : ℝ) := by
  have h := log_enclosure (y := 3) (x := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 21
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

theorem log_two_bounds : (0.69314718055 : ℝ) ≤ log 2 ∧ log 2 ≤ (0.69314718056 : ℝ) := by
  have h := log_enclosure (y := 2) (x := (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 14
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

theorem log_four_bounds : (1.3862943611 : ℝ) ≤ log 4 ∧ log 4 ≤ (1.3862943615 : ℝ) := by
  have h := log_enclosure (y := 4) (x := (3/5 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

theorem log_five_bounds : (1.6094379124 : ℝ) ≤ log 5 ∧ log 5 ≤ (1.6094379125 : ℝ) := by
  have h := log_enclosure (y := 5) (x := (2/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 30
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 1000000 in
/-- `sigma 3 5 4`, the normalising constant of `sigma0`, to `1e-8`. -/
theorem sigma_3_5_4_bounds_exact :
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
theorem hasDerivAt_sigma0' {t : ℝ} (ht : 1 < t) (hK : 0 < 1 - Wu04Integral.sigma 3 5 4) :
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
theorem inv_integrable_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))

/-- `log (t+1)/t` is interval integrable on `[a,b]` with `0 < a`. -/
theorem log_succ_div_integrable_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))
  exact Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) (fun t ht => by
    have := lt_of_lt_of_le ha ht.1
    exact ne_of_gt (by linarith : (0 : ℝ) < t + 1))

/-- Derivative of `C (s - a)^2`. -/
theorem hasDerivAt_const_mul_sq_sub {a C x : ℝ} :
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
theorem hasDerivAt_two_mul_const_sub {a C x : ℝ} :
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
theorem sigma0_one : Wu04Integral.sigma0 1 = 0 := by
  have h : Wu04Integral.sigma 3 3 2 = 0 := by
    unfold Wu04Integral.sigma
    rw [intervalIntegral.integral_same]
  unfold Wu04Integral.sigma0
  rw [show (1 : ℝ) + 2 = 3 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num, h]
  simp

/-- `|sigma0 t| ≤ 2 (t-1)` on `[1, 11/5]`: the squeeze that makes `sigma0` continuous at `1`. -/
theorem sigma0_abs_le_one {t : ℝ} (ht : t ∈ Set.Icc (1 : ℝ) (11/5)) :
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
theorem continuousWithinAt_sigma0_one :
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
theorem continuousOn_sigma0_Icc :
    ContinuousOn Wu04Integral.sigma0 (Set.Icc (1 : ℝ) (11/5)) := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h1 | h1
  · rw [← h1]
    exact continuousWithinAt_sigma0_one
  · exact ((sigma0_hasDerivAt h1 hK).continuousAt).continuousWithinAt

/-- `log ((t+2)/3) ≤ (t+1)/(t+2)` on `[1, 11/5]`: this is what makes `sigma0'` increasing there. -/
theorem log_shift_le1 {t : ℝ} (h1 : (1 : ℝ) ≤ t) (h2 : t ≤ 11/5) :
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
theorem sigma0_second_deriv_nonneg1 {t : ℝ} (h1 : (1 : ℝ) < t) (h2 : t < 11/5) :
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
theorem convexOn_sigma0_1 :
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
theorem sigma0_mid_taylor1 {a b m C t : ℝ} (ha : (1 : ℝ) ≤ a) (hb : b ≤ 11/5)
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
theorem integral_quad_shift_div {a b m X B C : ℝ} (ha : 0 < a) (hab : a ≤ b) :
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
theorem sigma0_mid_panel {a b m A B C : ℝ} (ha : (1 : ℝ) ≤ a) (hb : b ≤ 11/5)
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


/-- The `(b+1)`-endpoint lower bound for `sigma0''` on `[a,b]` implies the pointwise one. -/
theorem sigma0_second_lower {a b C : ℝ} (ha : (1 : ℝ) ≤ a) (hab : a ≤ b)
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
theorem sigma0_div_two_integrable_Icc {a b : ℝ} (ha : (1 : ℝ) ≤ a) (hb : b ≤ 11/5)
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
theorem b9_log_two_tight :
    ((346573590279972654708616060729/500000000000000000000000000000 : ℝ) : ℝ) ≤ log 2 ∧ log 2 ≤ ((693147180559945309417232121459/1000000000000000000000000000000 : ℝ) : ℝ) := by
  have h := log_enclosure (y := 2) (x := (1/3 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 40
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]


end LeanLab.ChenDoubleSieve.Feed1122_Burst9Matrix_entry_5_0_p2_kit
