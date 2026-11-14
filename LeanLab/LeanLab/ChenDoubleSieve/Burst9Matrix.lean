import LeanLab.ChenDoubleSieve.Table1Algebra

/-!
# Burst 9: the 81 entries of Wu's Section 7 matrix, one statement each

Source: Wu 2004, arXiv 0705.1652, displays 7.1 and 7.2, page 30: for the grid
`s₀ = 1, s_j = 2 + (j+1)/10`, the entries are `a_{i,j} = ∫_{s_{j−1}}^{s_j} Ξ(t; sᵢ) dt`, with
`Ξ₂` of display 3.22 for rows 1 to 4 and `Ξ₁` of display 3.21 for rows 5 to 9; Wu computed
them with Maple and printed the matrix `A` on page 31. `Wu04Table.IntegralMatrixBound` asks that
each rational candidate, the Maple value truncated to seven decimals, be a lower bound for the
true entry. `integral_matrix_bound_p3` proves that statement from the 81 single quadrature
statements below. Each is LEAF: every kernel contains the term `σ₀(t)`, itself an integral, and
the scipy recomputation leaves margins between 0 and 1.0e−7, see the note; no entry was
certified in Lean in this burst.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
namespace LeanLab.ChenDoubleSieve.Burst9Matrix
open Wu04Table

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open Wu04Table
open LeanLab.ChenDoubleSieve.Wu04Integral

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


/-! ## Workhorses for the certified integral bounds (this pass, 2026-11-14)

`entry_7_1` and its 44 Xi₁ siblings need only two kinds of piece: an integral of
`σ₀(t)/t` and an integral of `log ((t+1)^k/C)/(c·t)`.  Both are attacked by expanding the
logarithm in its power series and integrating the resulting monomials exactly.  The two
lemmas below are the exact integrations those expansions need. -/

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

private theorem log_2_3_bounds : (0.83290912293 : ℝ) ≤ log (23/10) ∧ log (23/10) ≤ (0.83290912294 : ℝ) := by
  have h := log_enclosure (y := 23/10) (x := (13/33 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_3_25_bounds : (1.17865499634 : ℝ) ≤ log (13/4) ∧ log (13/4) ≤ (1.17865499635 : ℝ) := by
  have h := log_enclosure (y := 13/4) (x := (9/17 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 23
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_4_161_bounds : (1.42575543000 : ℝ) ≤ log (4161/1000) ∧ log (4161/1000) ≤ (1.42575543001 : ℝ) := by
  have h := log_enclosure (y := 4161/1000) (x := (3161/5161 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 29
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_3_2_bounds : (1.16315080980 : ℝ) ≤ log (16/5) ∧ log (16/5) ≤ (1.16315080981 : ℝ) := by
  have h := log_enclosure (y := 16/5) (x := (11/21 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 22
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_4_2_bounds : (1.43508452528 : ℝ) ≤ log (21/5) ∧ log (21/5) ≤ (1.43508452529 : ℝ) := by
  have h := log_enclosure (y := 21/5) (x := (8/13 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 31
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
/-- `sigma 3 4.2 3.2`, the numerator of `sigma0 2.2`, to `2e-8`. -/
private theorem sigma_3_42_32_bounds :
    (0.077316960 : ℝ) ≤ Wu04Integral.sigma 3 4.2 3.2 ∧
      Wu04Integral.sigma 3 4.2 3.2 ≤ (0.077316980 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 4.2) (c := 3.2) (m := 2.6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 4.2) (c := 3.2) (m := 2.6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (4.2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((4.2 : ℝ) - 1) = 3.2 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 3.2) (m := 2.6) (by norm_num) (by norm_num),
    integral_log_mul_pow (a := 2) (b := 3.2) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.33647223661 : ℝ) ≤ log (21/5) - log 3 := by
    linarith [log_4_2_bounds.1, log_three_bounds.2]
  have hdiff_hi : log (21/5) - log 3 ≤ (0.33647223663 : ℝ) := by
    linarith [log_4_2_bounds.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (16/5) := by linarith [log_3_2_bounds.1]
  have hp : (0 : ℝ) ≤ (0.33647223661 : ℝ) := by norm_num
  have hlo : (0.39136795448 : ℝ) ≤ log (16/5) * (log (21/5) - log 3) := by
    have hm := mul_le_mul log_3_2_bounds.1 hdiff_lo hp hq
    have hc : (0.39136795448 : ℝ) ≤ (1.16315080980 : ℝ) * (0.33647223661 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi : log (16/5) * (log (21/5) - log 3) ≤ (0.39136795452 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (21/5) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_3_2_bounds.2 hdiff_hi h0 (by norm_num)
    have hc : (1.16315080981 : ℝ) * (0.33647223663 : ℝ) ≤ (0.39136795452 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo, log_3_2_bounds.1, log_3_2_bounds.2,
      log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi, log_3_2_bounds.1, log_3_2_bounds.2,
      log_two_bounds.1, log_two_bounds.2]

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

/-- Pointwise **upper** bound for `log (t+1)` from the logarithm's power series. -/
private theorem log_succ_upper_pointwise {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c + 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : ∀ t ∈ uIcc a b, |(c - t) / (c + 1)| ≤ r) (n : ℕ) :
    ∀ t ∈ uIcc a b, log (t + 1) ≤ log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) +
      r ^ (n + 1) / (1 - r) := by
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
  have := (abs_le.mp (le_trans hS hbound)).2
  linarith [hlog1mx]

/-- Upper bound for `∫ log (t+1)/t` from the logarithm series. -/
private theorem log_succ_integral_upper {a b c r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c + 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hxr : ∀ t ∈ uIcc a b, |(c - t) / (c + 1)| ≤ r) (n : ℕ) :
    (∫ t in a..b, log (t + 1) / t) ≤
      (log (c + 1) * log (b / a) + (r ^ (n + 1) / (1 - r)) * log (b / a)) -
        ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) * (1 / (c + 1) ^ (i + 1))) *
          (c ^ (i + 1) * log (b / a) + ∑ j ∈ Finset.range (i + 1),
            (-1) ^ (j + (i + 1)) * c ^ j * ((i + 1).choose j : ℝ) *
              ((b ^ (i + 1 - j) - a ^ (i + 1 - j)) / (((i : ℝ) + 1) - j))) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hpt := log_succ_upper_pointwise ha hab hc hr0 hr1 hxr n
  have hdiv : ∀ t ∈ Icc a b, log (t + 1) / t ≤ (log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) +
      r ^ (n + 1) / (1 - r)) / t := by
    intro t ht
    have htu : t ∈ uIcc a b := by
      rw [uIcc_of_le hab]
      exact ht
    exact div_le_div_of_nonneg_right (hpt t htu) (hmem t htu).le
  have hcont1 : ContinuousOn (fun t : ℝ => log (t + 1) / t) (uIcc a b) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (hmem t ht))
    have h1 : ContinuousOn (fun t : ℝ => t + 1) (uIcc a b) :=
      continuousOn_id.add continuousOn_const
    exact Real.continuousOn_log.comp h1 (fun t ht => by
      have := hmem t ht
      exact ne_of_gt (by linarith : (0:ℝ) < t + 1))
  have hcont2 : ContinuousOn (fun t : ℝ => (log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) +
      r ^ (n + 1) / (1 - r)) / t) (uIcc a b) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => ne_of_gt (hmem t ht))
    refine (continuousOn_const.sub ?_).add continuousOn_const
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact (((continuousOn_const.sub continuousOn_id).div_const (c + 1)).pow (i + 1)).div_const
      ((i : ℝ) + 1)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    hcont1.intervalIntegrable hcont2.intervalIntegrable hdiv
  have heq : (∫ t in a..b, (log (c + 1) -
      (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) +
      r ^ (n + 1) / (1 - r)) / t)
      = (∫ t in a..b, (log (c + 1) -
        (∑ i ∈ Finset.range n, ((c - t) / (c + 1)) ^ (i + 1) / ((i : ℝ) + 1)) -
        (-(r ^ (n + 1) / (1 - r)))) / t) := by
    congr 1
    funext t
    ring
  rw [heq] at hmono
  rw [integral_log_series_lower (c := c) ha hab n (-(r ^ (n + 1) / (1 - r)))] at hmono
  linarith [hmono]

/-- `log (33/10)` to `1e-11`, from the atanh series. -/
private theorem log_3_3_bounds : (1.19392246847 : ℝ) ≤ log (33/10) ∧ log (33/10) ≤ (1.19392246848 : ℝ) := by
  have h := log_enclosure (y := 33/10) (x := (23/43 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 26
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `log (43/10)` to `2e-11`, from the atanh series. -/
private theorem log_4_3_bounds : (1.45861502269 : ℝ) ≤ log (43/10) ∧ log (43/10) ≤ (1.45861502271 : ℝ) := by
  have h := log_enclosure (y := 43/10) (x := (33/53 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 30
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 1000000 in
/-- `sigma 3 4.3 3.3`, the numerator of `sigma0 2.3`, to `4e-8`. -/
private theorem sigma_3_43_33_bounds :
    (0.088032358 : ℝ) ≤ Wu04Integral.sigma 3 4.3 3.3 ∧
      Wu04Integral.sigma 3 4.3 3.3 ≤ (0.088032399 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 4.3) (c := 3.3) (m := 2.65)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 4.3) (c := 3.3) (m := 2.65)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (4.3 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, show ((4.3 : ℝ) - 1) = 3.3 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 3.3) (m := 2.65) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.36000273402 : ℝ) ≤ log (43/10) - log 3 := by
    linarith [log_4_3_bounds.1, log_three_bounds.2]
  have hdiff_hi : log (43/10) - log 3 ≤ (0.36000273405 : ℝ) := by
    linarith [log_4_3_bounds.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (33/10) := by linarith [log_3_3_bounds.1]
  have hp : (0 : ℝ) ≤ (0.36000273402 : ℝ) := by norm_num
  have hlo : (0.42981535285 : ℝ) ≤ log (33/10) * (log (43/10) - log 3) := by
    have hm := mul_le_mul log_3_3_bounds.1 hdiff_lo hp hq
    have hc : (0.42981535285 : ℝ) ≤ (1.19392246847 : ℝ) * (0.36000273402 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi : log (33/10) * (log (43/10) - log 3) ≤ (0.42981535290 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (43/10) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_3_3_bounds.2 hdiff_hi h0 (by norm_num)
    have hc : (1.19392246848 : ℝ) * (0.36000273405 : ℝ) ≤ (0.42981535290 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo, log_3_3_bounds.1, log_3_3_bounds.2,
      log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi, log_3_3_bounds.1, log_3_3_bounds.2,
      log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 2.2` to `3e-8`. -/
private theorem sigma0_two_two_bounds :
    (0.093343408 : ℝ) ≤ Wu04Integral.sigma0 2.2 ∧
      Wu04Integral.sigma0 2.2 ≤ (0.093343434 : ℝ) := by
  have hN := sigma_3_42_32_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0
  rw [show (2.2 : ℝ) + 2 = 4.2 by norm_num, show (2.2 : ℝ) + 1 = 3.2 by norm_num]
  constructor
  · calc (0.093343408 : ℝ) ≤ (0.077316960 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.077316960 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 4.2 3.2 / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN.1 hKpos.le
  · calc Wu04Integral.sigma 3 4.2 3.2 / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.077316980 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN.2 hKpos.le
      _ ≤ (0.077316980 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.093343434 : ℝ) := by norm_num

/-- `sigma0 2.3` to `6e-8`. -/
private theorem sigma0_two_three_bounds :
    (0.106279920 : ℝ) ≤ Wu04Integral.sigma0 2.3 ∧
      Wu04Integral.sigma0 2.3 ≤ (0.106279972 : ℝ) := by
  have hN := sigma_3_43_33_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0
  rw [show (2.3 : ℝ) + 2 = 4.3 by norm_num, show (2.3 : ℝ) + 1 = 3.3 by norm_num]
  constructor
  · calc (0.106279920 : ℝ) ≤ (0.088032358 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.088032358 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 4.3 3.3 / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN.1 hKpos.le
  · calc Wu04Integral.sigma 3 4.3 3.3 / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.088032399 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN.2 hKpos.le
      _ ≤ (0.088032399 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.106279972 : ℝ) := by norm_num

private theorem log_106_25 : (1.44456326924 : ℝ) ≤ log (106/25) ∧ log (106/25) ≤ (1.44456326926 : ℝ) := by
  have h := log_enclosure (y := 106/25) (x := (81/131 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_107_25 : (1.45395300959 : ℝ) ≤ log (107/25) ∧ log (107/25) ≤ (1.45395300961 : ℝ) := by
  have h := log_enclosure (y := 107/25) (x := (41/66 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_161_50 : (1.16938135955 : ℝ) ≤ log (161/50) ∧ log (161/50) ≤ (1.16938135957 : ℝ) := by
  have h := log_enclosure (y := 161/50) (x := (111/211 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_163_50 : (1.18172719537 : ℝ) ≤ log (163/50) ∧ log (163/50) ≤ (1.1817271954 : ℝ) := by
  have h := log_enclosure (y := 163/50) (x := (113/213 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_17_4 : (1.44691898293 : ℝ) ≤ log (17/4) ∧ log (17/4) ≤ (1.44691898295 : ℝ) := by
  have h := log_enclosure (y := 17/4) (x := (13/21 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_211_50 : (1.43983512804 : ℝ) ≤ log (211/50) ∧ log (211/50) ≤ (1.43983512806 : ℝ) := by
  have h := log_enclosure (y := 211/50) (x := (161/261 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_213_50 : (1.44926916028 : ℝ) ≤ log (213/50) ∧ log (213/50) ≤ (1.4492691603 : ℝ) := by
  have h := log_enclosure (y := 213/50) (x := (163/263 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_321_100 : (1.16627093714 : ℝ) ≤ log (321/100) ∧ log (321/100) ≤ (1.16627093716 : ℝ) := by
  have h := log_enclosure (y := 321/100) (x := (221/421 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_323_100 : (1.17248213723 : ℝ) ≤ log (323/100) ∧ log (323/100) ≤ (1.17248213725 : ℝ) := by
  have h := log_enclosure (y := 323/100) (x := (223/423 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_327_100 : (1.1847899849 : ℝ) ≤ log (327/100) ∧ log (327/100) ≤ (1.18478998493 : ℝ) := by
  have h := log_enclosure (y := 327/100) (x := (227/427 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_329_100 : (1.19088756477 : ℝ) ≤ log (329/100) ∧ log (329/100) ≤ (1.1908875648 : ℝ) := by
  have h := log_enclosure (y := 329/100) (x := (229/429 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_421_100 : (1.43746264769 : ℝ) ≤ log (421/100) ∧ log (421/100) ≤ (1.43746264771 : ℝ) := by
  have h := log_enclosure (y := 421/100) (x := (321/521 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_423_100 : (1.44220199305 : ℝ) ≤ log (423/100) ∧ log (423/100) ≤ (1.44220199307 : ℝ) := by
  have h := log_enclosure (y := 423/100) (x := (323/523 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_427_100 : (1.45161382724 : ℝ) ≤ log (427/100) ∧ log (427/100) ≤ (1.45161382726 : ℝ) := by
  have h := log_enclosure (y := 427/100) (x := (327/527 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_429_100 : (1.45628673293 : ℝ) ≤ log (429/100) ∧ log (429/100) ≤ (1.45628673296 : ℝ) := by
  have h := log_enclosure (y := 429/100) (x := (329/529 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 27
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_81_25 : (1.1755733298 : ℝ) ≤ log (81/25) ∧ log (81/25) ≤ (1.17557332982 : ℝ) := by
  have h := log_enclosure (y := 81/25) (x := (28/53 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

private theorem log_82_25 : (1.18784342239 : ℝ) ≤ log (82/25) ∧ log (82/25) ≤ (1.18784342242 : ℝ) := by
  have h := log_enclosure (y := 82/25) (x := (57/107 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 20
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `sigma0 11/5` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_11_5 :
    (0.093343408 : ℝ) ≤ Wu04Integral.sigma0 (11/5) ∧
      Wu04Integral.sigma0 (11/5) ≤ (0.093343434 : ℝ) := by
  have hN := sigma_3_42_32_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0
  have hsig : Wu04Integral.sigma 3 ((11/5 : ℝ) + 2) ((11/5 : ℝ) + 1) = Wu04Integral.sigma 3 (21/5) (16/5) := by
    norm_num
  rw [hsig]
  have hN' : (0.077316960 : ℝ) ≤ Wu04Integral.sigma 3 (21/5) (16/5) ∧
      Wu04Integral.sigma 3 (21/5) (16/5) ≤ (0.077316980 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.093343408 : ℝ) ≤ (0.077316960 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.077316960 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (21/5) (16/5) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (21/5) (16/5) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.077316980 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.077316980 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.093343434 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 421/100 321/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_421_100_321_100 :
    (0.0783705 : ℝ) ≤ Wu04Integral.sigma 3 (421/100) (321/100) ∧
      Wu04Integral.sigma 3 (421/100) (321/100) ≤ (0.07837053 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 421/100) (c := 321/100) (m := 521/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 421/100) (c := 321/100) (m := 521/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (421/100 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((421/100 : ℝ) - 1) = 321/100 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 321/100) (m := 521/200) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.33885035901 : ℝ) ≤ log (421/100) - log 3 := by
    linarith [log_421_100.1, log_three_bounds.2]
  have hdiff_hi : log (421/100) - log 3 ≤ (0.33885035905 : ℝ) := by
    linarith [log_421_100.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (321/100) := by linarith [log_321_100.1]
  have hp : (0 : ℝ) ≤ (0.33885035901 : ℝ) := by norm_num
  have hlo' : (1975956628764090713157/5000000000000000000000 : ℝ) ≤ log (321/100) * (log (421/100) - log 3) := by
    have hm := mul_le_mul log_321_100.1 hdiff_lo hp hq
    have hc : (1975956628764090713157/5000000000000000000000 : ℝ) ≤ (1.16627093714 : ℝ) * (0.33885035901 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (321/100) * (log (421/100) - log 3) ≤ (197595662903122993649/500000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (421/100) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_321_100.2 hdiff_hi h0 (by norm_num)
    have hc : (1.16627093716 : ℝ) * (0.33885035905 : ℝ) ≤ (197595662903122993649/500000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_321_100.1, log_321_100.2, log_421_100.1, log_421_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_321_100.1, log_321_100.2, log_421_100.1, log_421_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 221/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_221_100 :
    (0.094615328 : ℝ) ≤ Wu04Integral.sigma0 (221/100) ∧
      Wu04Integral.sigma0 (221/100) ≤ (0.094615367 : ℝ) := by
  have hN := sigma_panel_421_100_321_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (221/100 : ℝ) + 2 = 421/100 by norm_num, show (221/100 : ℝ) + 1 = 321/100 by norm_num]
  have hN' : (0.0783705 : ℝ) ≤ Wu04Integral.sigma 3 (421/100) (321/100) ∧
      Wu04Integral.sigma 3 (421/100) (321/100) ≤ (0.07837053 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.094615328 : ℝ) ≤ (0.0783705 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.0783705 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (421/100) (321/100) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (421/100) (321/100) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.07837053 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.07837053 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.094615367 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 211/50 161/50` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_211_50_161_50 :
    (0.07942816 : ℝ) ≤ Wu04Integral.sigma 3 (211/50) (161/50) ∧
      Wu04Integral.sigma 3 (211/50) (161/50) ≤ (0.07942819 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 211/50) (c := 161/50) (m := 261/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 211/50) (c := 161/50) (m := 261/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (211/50 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((211/50 : ℝ) - 1) = 161/50 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 161/50) (m := 261/100) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.34122283936 : ℝ) ≤ log (211/50) - log 3 := by
    linarith [log_211_50.1, log_three_bounds.2]
  have hdiff_hi : log (211/50) - log 3 ≤ (0.3412228394 : ℝ) := by
    linarith [log_211_50.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (161/50) := by linarith [log_161_50.1]
  have hp : (0 : ℝ) ≤ (0.34122283936 : ℝ) := by norm_num
  have hlo' : (24938726737519253243/62500000000000000000 : ℝ) ≤ log (161/50) * (log (211/50) - log 3) := by
    have hm := mul_le_mul log_161_50.1 hdiff_lo hp hq
    have hc : (24938726737519253243/62500000000000000000 : ℝ) ≤ (1.16938135955 : ℝ) * (0.34122283936 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (161/50) * (log (211/50) - log 3) ≤ (199509813926953881529/500000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (211/50) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_161_50.2 hdiff_hi h0 (by norm_num)
    have hc : (1.16938135957 : ℝ) * (0.3412228394 : ℝ) ≤ (199509813926953881529/500000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_161_50.1, log_161_50.2, log_211_50.1, log_211_50.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_161_50.1, log_161_50.2, log_211_50.1, log_211_50.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 111/50` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_111_50 :
    (0.095892223 : ℝ) ≤ Wu04Integral.sigma0 (111/50) ∧
      Wu04Integral.sigma0 (111/50) ≤ (0.095892261 : ℝ) := by
  have hN := sigma_panel_211_50_161_50
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (111/50 : ℝ) + 2 = 211/50 by norm_num, show (111/50 : ℝ) + 1 = 161/50 by norm_num]
  have hN' : (0.07942816 : ℝ) ≤ Wu04Integral.sigma 3 (211/50) (161/50) ∧
      Wu04Integral.sigma 3 (211/50) (161/50) ≤ (0.07942819 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.095892223 : ℝ) ≤ (0.07942816 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.07942816 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (211/50) (161/50) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (211/50) (161/50) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.07942819 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.07942819 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.095892261 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 423/100 323/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_423_100_323_100 :
    (0.08048988 : ℝ) ≤ Wu04Integral.sigma 3 (423/100) (323/100) ∧
      Wu04Integral.sigma 3 (423/100) (323/100) ≤ (0.08048991 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 423/100) (c := 323/100) (m := 523/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 423/100) (c := 323/100) (m := 523/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (423/100 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((423/100 : ℝ) - 1) = 323/100 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 323/100) (m := 523/200) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.34358970437 : ℝ) ≤ log (423/100) - log 3 := by
    linarith [log_423_100.1, log_three_bounds.2]
  have hdiff_hi : log (423/100) - log 3 ≤ (0.34358970441 : ℝ) := by
    linarith [log_423_100.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (323/100) := by linarith [log_323_100.1]
  have hp : (0 : ℝ) ≤ (0.34358970437 : ℝ) := by norm_num
  have hlo' : (4028527909099614706951/10000000000000000000000 : ℝ) ≤ log (323/100) * (log (423/100) - log 3) := by
    have hm := mul_le_mul log_323_100.1 hdiff_lo hp hq
    have hc : (4028527909099614706951/10000000000000000000000 : ℝ) ≤ (1.17248213723 : ℝ) * (0.34358970437 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (323/100) * (log (423/100) - log 3) ≤ (161141116385493020109/400000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (423/100) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_323_100.2 hdiff_hi h0 (by norm_num)
    have hc : (1.17248213725 : ℝ) * (0.34358970441 : ℝ) ≤ (161141116385493020109/400000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_323_100.1, log_323_100.2, log_423_100.1, log_423_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_323_100.1, log_323_100.2, log_423_100.1, log_423_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 223/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_223_100 :
    (0.097174019 : ℝ) ≤ Wu04Integral.sigma0 (223/100) ∧
      Wu04Integral.sigma0 (223/100) ≤ (0.097174057 : ℝ) := by
  have hN := sigma_panel_423_100_323_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (223/100 : ℝ) + 2 = 423/100 by norm_num, show (223/100 : ℝ) + 1 = 323/100 by norm_num]
  have hN' : (0.08048988 : ℝ) ≤ Wu04Integral.sigma 3 (423/100) (323/100) ∧
      Wu04Integral.sigma 3 (423/100) (323/100) ≤ (0.08048991 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.097174019 : ℝ) ≤ (0.08048988 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08048988 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (423/100) (323/100) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (423/100) (323/100) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.08048991 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.08048991 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.097174057 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 106/25 81/25` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_106_25_81_25 :
    (0.08155563 : ℝ) ≤ Wu04Integral.sigma 3 (106/25) (81/25) ∧
      Wu04Integral.sigma 3 (106/25) (81/25) ≤ (0.08155567 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 106/25) (c := 81/25) (m := 131/50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 106/25) (c := 81/25) (m := 131/50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (106/25 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((106/25 : ℝ) - 1) = 81/25 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 81/25) (m := 131/50) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.34595098056 : ℝ) ≤ log (106/25) - log 3 := by
    linarith [log_106_25.1, log_three_bounds.2]
  have hdiff_hi : log (106/25) - log 3 ≤ (0.3459509806 : ℝ) := by
    linarith [log_106_25.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (81/25) := by linarith [log_81_25.1]
  have hp : (0 : ℝ) ≤ (0.34595098056 : ℝ) := by norm_num
  have hlo' : (25418171635280891793/62500000000000000000 : ℝ) ≤ log (81/25) * (log (106/25) - log 3) := by
    have hm := mul_le_mul log_81_25.1 hdiff_lo hp hq
    have hc : (25418171635280891793/62500000000000000000 : ℝ) ≤ (1.1755733298 : ℝ) * (0.34595098056 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (81/25) * (log (106/25) - log 3) ≤ (101672686554609055373/250000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (106/25) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_81_25.2 hdiff_hi h0 (by norm_num)
    have hc : (1.17557332982 : ℝ) * (0.3459509806 : ℝ) ≤ (101672686554609055373/250000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_81_25.1, log_81_25.2, log_106_25.1, log_106_25.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_81_25.1, log_81_25.2, log_106_25.1, log_106_25.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 56/25` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_56_25 :
    (0.09846068 : ℝ) ≤ Wu04Integral.sigma0 (56/25) ∧
      Wu04Integral.sigma0 (56/25) ≤ (0.09846073 : ℝ) := by
  have hN := sigma_panel_106_25_81_25
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (56/25 : ℝ) + 2 = 106/25 by norm_num, show (56/25 : ℝ) + 1 = 81/25 by norm_num]
  have hN' : (0.08155563 : ℝ) ≤ Wu04Integral.sigma 3 (106/25) (81/25) ∧
      Wu04Integral.sigma 3 (106/25) (81/25) ≤ (0.08155567 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.09846068 : ℝ) ≤ (0.08155563 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08155563 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (106/25) (81/25) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (106/25) (81/25) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.08155567 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.08155567 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.09846073 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 17/4 13/4` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_17_4_13_4 :
    (0.08262537 : ℝ) ≤ Wu04Integral.sigma 3 (17/4) (13/4) ∧
      Wu04Integral.sigma 3 (17/4) (13/4) ≤ (0.0826254 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 17/4) (c := 13/4) (m := 21/8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 17/4) (c := 13/4) (m := 21/8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (17/4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((17/4 : ℝ) - 1) = 13/4 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 13/4) (m := 21/8) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.34830669425 : ℝ) ≤ log (17/4) - log 3 := by
    linarith [log_17_4.1, log_three_bounds.2]
  have hdiff_hi : log (17/4) - log 3 ≤ (0.34830669429 : ℝ) := by
    linarith [log_17_4.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (13/4) := by linarith [log_3_25_bounds.1]
  have hp : (0 : ℝ) ≤ (0.34830669425 : ℝ) := by norm_num
  have hlo' : (82106685087286249809/200000000000000000000 : ℝ) ≤ log (13/4) * (log (17/4) - log 3) := by
    have hm := mul_le_mul log_3_25_bounds.1 hdiff_lo hp hq
    have hc : (82106685087286249809/200000000000000000000 : ℝ) ≤ (1.17865499634 : ℝ) * (0.34830669425 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (13/4) * (log (17/4) - log 3) ≤ (821066850974121031683/2000000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (17/4) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_3_25_bounds.2 hdiff_hi h0 (by norm_num)
    have hc : (1.17865499635 : ℝ) * (0.34830669429 : ℝ) ≤ (821066850974121031683/2000000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_3_25_bounds.1, log_3_25_bounds.2, log_17_4.1, log_17_4.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_3_25_bounds.1, log_3_25_bounds.2, log_17_4.1, log_17_4.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 9/4` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_9_4 :
    (0.099752158 : ℝ) ≤ Wu04Integral.sigma0 (9/4) ∧
      Wu04Integral.sigma0 (9/4) ≤ (0.099752197 : ℝ) := by
  have hN := sigma_panel_17_4_13_4
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (9/4 : ℝ) + 2 = 17/4 by norm_num, show (9/4 : ℝ) + 1 = 13/4 by norm_num]
  have hN' : (0.08262537 : ℝ) ≤ Wu04Integral.sigma 3 (17/4) (13/4) ∧
      Wu04Integral.sigma 3 (17/4) (13/4) ≤ (0.0826254 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.099752158 : ℝ) ≤ (0.08262537 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08262537 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (17/4) (13/4) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (17/4) (13/4) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.0826254 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.0826254 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.099752197 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 213/50 163/50` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_213_50_163_50 :
    (0.08369904 : ℝ) ≤ Wu04Integral.sigma 3 (213/50) (163/50) ∧
      Wu04Integral.sigma 3 (213/50) (163/50) ≤ (0.08369908 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 213/50) (c := 163/50) (m := 263/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 213/50) (c := 163/50) (m := 263/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (213/50 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((213/50 : ℝ) - 1) = 163/50 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 163/50) (m := 263/100) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.3506568716 : ℝ) ≤ log (213/50) - log 3 := by
    linarith [log_213_50.1, log_three_bounds.2]
  have hdiff_hi : log (213/50) - log 3 ≤ (0.35065687164 : ℝ) := by
    linarith [log_213_50.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (163/50) := by linarith [log_163_50.1]
  have hp : (0 : ℝ) ≤ (0.3506568716 : ℝ) := by norm_num
  have hlo' : (103595190353271551123/250000000000000000000 : ℝ) ≤ log (163/50) * (log (213/50) - log 3) := by
    have hm := mul_le_mul log_163_50.1 hdiff_lo hp hq
    have hc : (103595190353271551123/250000000000000000000 : ℝ) ≤ (1.18172719537 : ℝ) * (0.3506568716 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (163/50) * (log (213/50) - log 3) ≤ (51797595183859374807/125000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (213/50) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_163_50.2 hdiff_hi h0 (by norm_num)
    have hc : (1.1817271954 : ℝ) * (0.35065687164 : ℝ) ≤ (51797595183859374807/125000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_163_50.1, log_163_50.2, log_213_50.1, log_213_50.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_163_50.1, log_163_50.2, log_213_50.1, log_213_50.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 113/50` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_113_50 :
    (0.101048381 : ℝ) ≤ Wu04Integral.sigma0 (113/50) ∧
      Wu04Integral.sigma0 (113/50) ≤ (0.101048432 : ℝ) := by
  have hN := sigma_panel_213_50_163_50
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (113/50 : ℝ) + 2 = 213/50 by norm_num, show (113/50 : ℝ) + 1 = 163/50 by norm_num]
  have hN' : (0.08369904 : ℝ) ≤ Wu04Integral.sigma 3 (213/50) (163/50) ∧
      Wu04Integral.sigma 3 (213/50) (163/50) ≤ (0.08369908 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.101048381 : ℝ) ≤ (0.08369904 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08369904 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (213/50) (163/50) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (213/50) (163/50) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.08369908 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.08369908 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.101048432 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 427/100 327/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_427_100_327_100 :
    (0.08477662 : ℝ) ≤ Wu04Integral.sigma 3 (427/100) (327/100) ∧
      Wu04Integral.sigma 3 (427/100) (327/100) ≤ (0.08477666 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 427/100) (c := 327/100) (m := 527/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 427/100) (c := 327/100) (m := 527/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (427/100 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((427/100 : ℝ) - 1) = 327/100 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 327/100) (m := 527/200) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.35300153857 : ℝ) ≤ log (427/100) - log 3 := by
    linarith [log_427_100.1, log_three_bounds.2]
  have hdiff_hi : log (427/100) - log 3 ≤ (0.3530015386 : ℝ) := by
    linarith [log_427_100.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (327/100) := by linarith [log_327_100.1]
  have hp : (0 : ℝ) ≤ (0.35300153857 : ℝ) := by norm_num
  have hlo' : (418232687552027067593/1000000000000000000000 : ℝ) ≤ log (327/100) * (log (427/100) - log 3) := by
    have hm := mul_le_mul log_327_100.1 hdiff_lo hp hq
    have hc : (418232687552027067593/1000000000000000000000 : ℝ) ≤ (1.1847899849 : ℝ) * (0.35300153857 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (327/100) * (log (427/100) - log 3) ≤ (209116343799080406649/500000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (427/100) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_327_100.2 hdiff_hi h0 (by norm_num)
    have hc : (1.18478998493 : ℝ) * (0.3530015386 : ℝ) ≤ (209116343799080406649/500000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_327_100.1, log_327_100.2, log_427_100.1, log_427_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_327_100.1, log_327_100.2, log_427_100.1, log_427_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 227/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_227_100 :
    (0.102349325 : ℝ) ≤ Wu04Integral.sigma0 (227/100) ∧
      Wu04Integral.sigma0 (227/100) ≤ (0.102349375 : ℝ) := by
  have hN := sigma_panel_427_100_327_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (227/100 : ℝ) + 2 = 427/100 by norm_num, show (227/100 : ℝ) + 1 = 327/100 by norm_num]
  have hN' : (0.08477662 : ℝ) ≤ Wu04Integral.sigma 3 (427/100) (327/100) ∧
      Wu04Integral.sigma 3 (427/100) (327/100) ≤ (0.08477666 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.102349325 : ℝ) ≤ (0.08477662 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08477662 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (427/100) (327/100) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (427/100) (327/100) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.08477666 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.08477666 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.102349375 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 107/25 82/25` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_107_25_82_25 :
    (0.08585806 : ℝ) ≤ Wu04Integral.sigma 3 (107/25) (82/25) ∧
      Wu04Integral.sigma 3 (107/25) (82/25) ≤ (0.0858581 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 107/25) (c := 82/25) (m := 66/25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 107/25) (c := 82/25) (m := 66/25)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (107/25 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((107/25 : ℝ) - 1) = 82/25 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 82/25) (m := 66/25) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.35534072091 : ℝ) ≤ log (107/25) - log 3 := by
    linarith [log_107_25.1, log_three_bounds.2]
  have hdiff_hi : log (107/25) - log 3 ≤ (0.35534072095 : ℝ) := by
    linarith [log_107_25.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (82/25) := by linarith [log_82_25.1]
  have hp : (0 : ℝ) ≤ (0.35534072091 : ℝ) := by norm_num
  have hlo' : (4220891380402642351749/10000000000000000000000 : ℝ) ≤ log (82/25) * (log (107/25) - log 3) := by
    have hm := mul_le_mul log_82_25.1 hdiff_lo hp hq
    have hc : (4220891380402642351749/10000000000000000000000 : ℝ) ≤ (1.18784342239 : ℝ) * (0.35534072091 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (82/25) * (log (107/25) - log 3) ≤ (422089138098438193699/1000000000000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (107/25) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_82_25.2 hdiff_hi h0 (by norm_num)
    have hc : (1.18784342242 : ℝ) * (0.35534072095 : ℝ) ≤ (422089138098438193699/1000000000000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_82_25.1, log_82_25.2, log_107_25.1, log_107_25.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_82_25.1, log_82_25.2, log_107_25.1, log_107_25.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 57/25` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_57_25 :
    (0.103654928 : ℝ) ≤ Wu04Integral.sigma0 (57/25) ∧
      Wu04Integral.sigma0 (57/25) ≤ (0.103654979 : ℝ) := by
  have hN := sigma_panel_107_25_82_25
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (57/25 : ℝ) + 2 = 107/25 by norm_num, show (57/25 : ℝ) + 1 = 82/25 by norm_num]
  have hN' : (0.08585806 : ℝ) ≤ Wu04Integral.sigma 3 (107/25) (82/25) ∧
      Wu04Integral.sigma 3 (107/25) (82/25) ≤ (0.0858581 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.103654928 : ℝ) ≤ (0.08585806 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08585806 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (107/25) (82/25) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (107/25) (82/25) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.0858581 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.0858581 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.103654979 : ℝ) := by norm_num

set_option maxHeartbeats 1000000 in
/-- `sigma 3 429/100 329/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma_panel_429_100_329_100 :
    (0.08694331 : ℝ) ≤ Wu04Integral.sigma 3 (429/100) (329/100) ∧
      Wu04Integral.sigma 3 (429/100) (329/100) ≤ (0.08694336 : ℝ) := by
  have hlow := sigma_lower_bound (a := 3) (b := 429/100) (c := 329/100) (m := 529/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  have hupp := sigma_upper_bound (a := 3) (b := 429/100) (c := 329/100) (m := 529/200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : (429/100 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show ((429/100 : ℝ) - 1) = 329/100 by norm_num] at hlow hupp
  simp only [integral_log_mul_sub_pow (a := 2) (b := 329/100) (m := 529/200) (by norm_num) (by norm_num)] at hlow hupp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow hupp
  norm_num [Nat.choose] at hlow hupp
  have hdiff_lo : (0.35767444425 : ℝ) ≤ log (429/100) - log 3 := by
    linarith [log_429_100.1, log_three_bounds.2]
  have hdiff_hi : log (429/100) - log 3 ≤ (0.3576744443 : ℝ) := by
    linarith [log_429_100.2, log_three_bounds.1]
  have hq : (0 : ℝ) ≤ log (329/100) := by linarith [log_329_100.1]
  have hp : (0 : ℝ) ≤ (0.35767444425 : ℝ) := by norm_num
  have hlo' : (42595004788976888463/100000000000000000000 : ℝ) ≤ log (329/100) * (log (429/100) - log 3) := by
    have hm := mul_le_mul log_329_100.1 hdiff_lo hp hq
    have hc : (42595004788976888463/100000000000000000000 : ℝ) ≤ (1.19088756476 : ℝ) * (0.35767444425 : ℝ) := by norm_num
    linarith [hm, hc]
  have hhi' : log (329/100) * (log (429/100) - log 3) ≤ (332773474971578313/781250000000000000 : ℝ) := by
    have h0 : (0 : ℝ) ≤ log (429/100) - log 3 := by linarith [hdiff_lo]
    have hm := mul_le_mul log_329_100.2 hdiff_hi h0 (by norm_num)
    have hc : (1.1908875648 : ℝ) * (0.3576744443 : ℝ) ≤ (332773474971578313/781250000000000000 : ℝ) := by norm_num
    linarith [hm, hc]
  constructor
  · linarith [hlow, hlo', log_329_100.1, log_329_100.2, log_429_100.1, log_429_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]
  · linarith [hupp, hhi', log_329_100.1, log_329_100.2, log_429_100.1, log_429_100.2, log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 229/100` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_229_100 :
    (0.104965131 : ℝ) ≤ Wu04Integral.sigma0 (229/100) ∧
      Wu04Integral.sigma0 (229/100) ≤ (0.104965194 : ℝ) := by
  have hN := sigma_panel_429_100_329_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0

  rw [show (229/100 : ℝ) + 2 = 429/100 by norm_num, show (229/100 : ℝ) + 1 = 329/100 by norm_num]
  have hN' : (0.08694331 : ℝ) ≤ Wu04Integral.sigma 3 (429/100) (329/100) ∧
      Wu04Integral.sigma 3 (429/100) (329/100) ≤ (0.08694336 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.104965131 : ℝ) ≤ (0.08694331 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.08694331 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (429/100) (329/100) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (429/100) (329/100) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.08694336 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.08694336 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.104965194 : ℝ) := by norm_num

/-- `sigma0 23/10` — a panel endpoint of the `entry_7_1` quadrature. -/
private theorem sigma0_panel_23_10 :
    (0.10627992 : ℝ) ≤ Wu04Integral.sigma0 (23/10) ∧
      Wu04Integral.sigma0 (23/10) ≤ (0.106279972 : ℝ) := by
  have hN := sigma_3_43_33_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hKlo : (0.828306575 : ℝ) ≤ 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hpos : (0 : ℝ) < (0.828306575 : ℝ) := by norm_num
  unfold Wu04Integral.sigma0
  have hsig : Wu04Integral.sigma 3 ((23/10 : ℝ) + 2) ((23/10 : ℝ) + 1) = Wu04Integral.sigma 3 (43/10) (33/10) := by
    norm_num
  rw [hsig]
  have hN' : (0.088032358 : ℝ) ≤ Wu04Integral.sigma 3 (43/10) (33/10) ∧
      Wu04Integral.sigma 3 (43/10) (33/10) ≤ (0.088032399 : ℝ) := by
    convert hN using 2 <;> norm_num
  constructor
  · calc (0.10627992 : ℝ) ≤ (0.088032358 : ℝ) / (0.828306585 : ℝ) := by norm_num
      _ ≤ (0.088032358 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
      _ ≤ Wu04Integral.sigma 3 (43/10) (33/10) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.1 hKpos.le
  · calc Wu04Integral.sigma 3 (43/10) (33/10) / (1 - Wu04Integral.sigma 3 5 4)
        ≤ (0.088032399 : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
          div_le_div_of_nonneg_right hN'.2 hKpos.le
      _ ≤ (0.088032399 : ℝ) / (0.828306575 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hpos hKlo
      _ ≤ (0.106279972 : ℝ) := by norm_num
/-- `∫ (A + B(t-a))/t = (A - Ba)·log(b/a) + B(b-a)`: the exact integral of an affine
function over `t`, which is what a tangent/chord panel sandwich reduces to. -/
private theorem integral_affine_div {a b A B : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (A + B * (t - a)) / t) = (A - B * a) * log (b / a) + B * (b - a) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hpt : ∀ t ∈ uIcc a b, (A + B * (t - a)) / t = (A - B * a) * (1 / t) + B := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    field_simp
    ring
  have hint1 : IntervalIntegrable (fun t : ℝ => (A - B * a) * (1 / t)) volume a b :=
    (ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht)))).const_mul _
  have hint2 : IntervalIntegrable (fun _ : ℝ => B) volume a b := intervalIntegrable_const
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hint1 hint2,
    intervalIntegral.integral_const_mul, integral_one_div_exp ha hab,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- `log ((t+2)/3) ≤ (t+1)/(t+2)` on `[11/5, 23/10]`: this is what makes `sigma0'`
increasing, i.e. `sigma0` convex. -/
private theorem log_shift_le {t : ℝ} (h1 : (11/5 : ℝ) ≤ t) (h2 : t ≤ 23/10) :
    log ((t + 2) / 3) ≤ (t + 1) / (t + 2) := by
  have hu : (0 : ℝ) < (t + 2) / 3 := by linarith
  have htp : (0 : ℝ) < t + 2 := by linarith
  have hlog : log ((t + 2) / 3) ≤ (t + 2) / 3 - 1 := Real.log_le_sub_one_of_pos hu
  have hstep : (t + 2) / 3 - 1 ≤ (t + 1) / (t + 2) := by
    have htp' : (0 : ℝ) < t + 2 := htp
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hsplit : (t + 2) / 3 - 1 = (t - 1) / 3 := by
      field_simp
      ring
    rw [hsplit]
    have hkey : (t - 1) * (t + 2) ≤ (t + 1) * 3 := by nlinarith
    rw [div_le_div_iff₀ h3 htp']
    exact hkey
  linarith

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

/-- `sigma0'' ≥ 0` on the interior of `[11/5, 23/10]`, i.e. `sigma0` is convex there. -/
private theorem sigma0_second_deriv_nonneg {t : ℝ} (h1 : (11/5 : ℝ) < t) (h2 : t < 23/10) :
    0 ≤ ((1 / (t + 2) * (t + 1) - log ((t + 2) / 3)) / (t + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hden : (0 : ℝ) < (t + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by positivity
  have hle := log_shift_le h1.le h2.le
  have hnum : 0 ≤ 1 / (t + 2) * (t + 1) - log ((t + 2) / 3) := by
    have h1' : 1 / (t + 2) * (t + 1) = (t + 1) / (t + 2) := by
      field_simp
    rw [h1']
    linarith
  refine div_nonneg ?_ hK.le
  refine div_nonneg hnum (by positivity)

/-- `sigma0` is convex on `[11/5, 23/10]`. -/
private theorem convexOn_sigma0 : ConvexOn ℝ (Set.Icc (11/5 : ℝ) (23/10)) Wu04Integral.sigma0 := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc (11/5 : ℝ) (23/10))
    (f := Wu04Integral.sigma0)
    (f' := fun s : ℝ => (log ((s + 2) / 3) / (s + 1)) / (1 - Wu04Integral.sigma 3 5 4))
    (f'' := fun s : ℝ => ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
      (1 - Wu04Integral.sigma 3 5 4))
    (convex_Icc _ _) ?_ ?_ ?_ ?_
  · -- continuity on the interval
    intro x hx
    exact (sigma0_hasDerivAt (by linarith [hx.1]) hK).continuousAt.continuousWithinAt
  · intro x hx
    have hx1 : (1 : ℝ) < x := by
      have : x ∈ Set.Ioo (11/5 : ℝ) (23/10) := by rwa [interior_Icc] at hx
      linarith [this.1]
    exact (sigma0_hasDerivAt hx1 hK).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (11/5 : ℝ) (23/10) := by rwa [interior_Icc] at hx
    exact (hasDerivAt_sigma0' (by linarith [hx'.1]) hK).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (11/5 : ℝ) (23/10) := by rwa [interior_Icc] at hx
    exact sigma0_second_deriv_nonneg hx'.1 hx'.2

/-- Tangent lower bound: `sigma0 t ≥ sigma0 a + sigma0' a · (t - a)` on `[11/5, 23/10]`. -/
private theorem sigma0_tangent_le {a t : ℝ} (ha : (11/5 : ℝ) ≤ a) (ht : t ≤ 23/10)
    (hat : a ≤ t) :
    Wu04Integral.sigma0 a +
        ((log ((a + 2) / 3) / (a + 1)) / (1 - Wu04Integral.sigma 3 5 4)) * (t - a)
      ≤ Wu04Integral.sigma0 t := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have ha1 : (1 : ℝ) < a := by linarith
  rcases eq_or_lt_of_le hat with rfl | hlt
  · simp
  · have haD : a ∈ Set.Icc (11/5 : ℝ) (23/10) := ⟨ha, by linarith⟩
    have htD : t ∈ Set.Icc (11/5 : ℝ) (23/10) := ⟨by linarith, ht⟩
    have hslope := convexOn_sigma0.le_slope_of_hasDerivAt haD htD hlt
      (sigma0_hasDerivAt ha1 hK)
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < t - a := by linarith
    rw [le_div_iff₀ hpos] at hslope
    linarith

/-- **One panel of the `entry_7_1` quadrature.** On `[a,b] ⊆ [11/5, 23/10]`, any affine
lower bound `A + B(t-a)` for `sigma0` (from convexity, with `A ≤ sigma0 a` and `B ≤ sigma0' a`)
integrates explicitly against `1/(2t)`. -/
private theorem sigma0_panel_lower {a b A B : ℝ} (ha : (11/5 : ℝ) ≤ a)
    (hb : b ≤ 23/10) (hab : a ≤ b)
    (hA : A ≤ Wu04Integral.sigma0 a)
    (hB : B ≤ (log ((a + 2) / 3) / (a + 1)) / (1 - Wu04Integral.sigma 3 5 4)) :
    (1 / 2) * ((A - B * a) * log (b / a) + B * (b - a)) ≤
      ∫ t in a..b, Wu04Integral.sigma0 t / (2 * t) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  -- pointwise: the tangent line at `a` is below `sigma0`
  have hpt : ∀ t ∈ Set.Icc a b, (A + B * (t - a)) / (2 * t) ≤
      Wu04Integral.sigma0 t / (2 * t) := by
    intro t ht
    have ht1 : a ≤ t := ht.1
    have htt : t ≤ 23/10 := le_trans ht.2 hb
    have htan := sigma0_tangent_le ha htt ht1
    have hstep : A + B * (t - a) ≤ Wu04Integral.sigma0 t := by
      have h1 : B * (t - a) ≤ ((log ((a + 2) / 3) / (a + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - a) :=
        mul_le_mul_of_nonneg_right hB (by linarith)
      linarith
    have h2t : (0 : ℝ) < 2 * t := by
      have := hmem t (by rw [uIcc_of_le hab]; exact ht)
      linarith
    exact div_le_div_of_nonneg_right hstep h2t.le
  have hcont1 : ContinuousOn (fun t : ℝ => (A + B * (t - a)) / (2 * t)) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · exact continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro t ht
      have := hmem t (by rw [uIcc_of_le hab]; exact ht)
      linarith
  have hcont2 : ContinuousOn (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · intro t ht
      have ht1 : (1 : ℝ) < t := by linarith [ht.1]
      exact (sigma0_hasDerivAt ht1 (by linarith [sigma_3_5_4_bounds_exact.2])).continuousAt.continuousWithinAt
    · intro t ht
      have := hmem t (by rw [uIcc_of_le hab]; exact ht)
      linarith
  have hcont1' : ContinuousOn (fun t : ℝ => (A + B * (t - a)) / (2 * t)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hcont1
  have hcont2' : ContinuousOn (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hcont2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    hcont1'.intervalIntegrable hcont2'.intervalIntegrable hpt
  have heq : (∫ t in a..b, (A + B * (t - a)) / (2 * t)) =
      (1 / 2) * (∫ t in a..b, (A + B * (t - a)) / t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    field_simp
  rw [heq, integral_affine_div (by linarith) hab] at hmono
  exact hmono

/-- Two-sided enclosure of `log (221/220)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_221_220 :
    (0.00453515516539 : ℝ) ≤ log (221/220) ∧ log (221/220) ≤ (0.0045351551654 : ℝ) := by
  have h := log_enclosure (y := 221/220) (x := (1/441 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (222/221)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_222_221 :
    (0.00451468035452 : ℝ) ≤ log (222/221) ∧ log (222/221) ≤ (0.00451468035453 : ℝ) := by
  have h := log_enclosure (y := 222/221) (x := (1/443 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (223/222)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_223_222 :
    (0.00449438958783 : ℝ) ≤ log (223/222) ∧ log (223/222) ≤ (0.00449438958784 : ℝ) := by
  have h := log_enclosure (y := 223/222) (x := (1/445 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (224/223)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_224_223 :
    (0.00447428039492 : ℝ) ≤ log (224/223) ∧ log (224/223) ≤ (0.00447428039493 : ℝ) := by
  have h := log_enclosure (y := 224/223) (x := (1/447 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (225/224)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_225_224 :
    (0.00445435034938 : ℝ) ≤ log (225/224) ∧ log (225/224) ≤ (0.00445435034939 : ℝ) := by
  have h := log_enclosure (y := 225/224) (x := (1/449 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (226/225)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_226_225 :
    (0.00443459706786 : ℝ) ≤ log (226/225) ∧ log (226/225) ≤ (0.00443459706787 : ℝ) := by
  have h := log_enclosure (y := 226/225) (x := (1/451 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (227/226)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_227_226 :
    (0.00441501820911 : ℝ) ≤ log (227/226) ∧ log (227/226) ≤ (0.00441501820912 : ℝ) := by
  have h := log_enclosure (y := 227/226) (x := (1/453 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (228/227)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_228_227 :
    (0.00439561147303 : ℝ) ≤ log (228/227) ∧ log (228/227) ≤ (0.00439561147304 : ℝ) := by
  have h := log_enclosure (y := 228/227) (x := (1/455 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (229/228)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_229_228 :
    (0.00437637459979 : ℝ) ≤ log (229/228) ∧ log (229/228) ≤ (0.0043763745998 : ℝ) := by
  have h := log_enclosure (y := 229/228) (x := (1/457 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (230/229)`, the log of one `entry_7_1` panel ratio. -/
private theorem log_230_229 :
    (0.00435730536895 : ℝ) ≤ log (230/229) ∧ log (230/229) ≤ (0.00435730536896 : ℝ) := by
  have h := log_enclosure (y := 230/229) (x := (1/459 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (23/22)`, the total log of the `entry_7_1` interval. -/
private theorem log_23_22 :
    (0.04445176257083 : ℝ) ≤ log (23/22) ∧ log (23/22) ≤ (0.04445176257084 : ℝ) := by
  have h := log_enclosure (y := 23/22) (x := (1/45 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 4
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Lower bound of `sigma0' ((11/5 : ℝ))`, the tangent slope of panel 0 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_11_5 :
    (0.1269428202 : ℝ) ≤
      (log (((11/5 : ℝ) + 2) / 3) / ((11/5 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_4_2_bounds
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.33647223661 : ℝ) ≤ log (21/5 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((11/5 : ℝ) + 2) / 3) = (21/5 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1269428202 : ℝ)
      ≤ (0.33647223661 : ℝ) / (((11/5 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (21/5 : ℝ) - log 3) / (((11/5 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (21/5 : ℝ) - log 3) / (((11/5 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((221/100 : ℝ))`, the tangent slope of panel 1 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_221_100 :
    (0.1274417726 : ℝ) ≤
      (log (((221/100 : ℝ) + 2) / 3) / ((221/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_421_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.33885035902 : ℝ) ≤ log (421/100 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((221/100 : ℝ) + 2) / 3) = (421/100 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1274417726 : ℝ)
      ≤ (0.33885035902 : ℝ) / (((221/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (421/100 : ℝ) - log 3) / (((221/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (421/100 : ℝ) - log 3) / (((221/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((111/50 : ℝ))`, the tangent slope of panel 2 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_111_50 :
    (0.1279355106 : ℝ) ≤
      (log (((111/50 : ℝ) + 2) / 3) / ((111/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_211_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.34122283937 : ℝ) ≤ log (211/50 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((111/50 : ℝ) + 2) / 3) = (211/50 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1279355106 : ℝ)
      ≤ (0.34122283937 : ℝ) / (((111/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (211/50 : ℝ) - log 3) / (((111/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (211/50 : ℝ) - log 3) / (((111/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((223/100 : ℝ))`, the tangent slope of panel 3 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_223_100 :
    (0.1284240924 : ℝ) ≤
      (log (((223/100 : ℝ) + 2) / 3) / ((223/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_423_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.34358970438 : ℝ) ≤ log (423/100 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((223/100 : ℝ) + 2) / 3) = (423/100 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1284240924 : ℝ)
      ≤ (0.34358970438 : ℝ) / (((223/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (423/100 : ℝ) - log 3) / (((223/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (423/100 : ℝ) - log 3) / (((223/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((56/25 : ℝ))`, the tangent slope of panel 4 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_56_25 :
    (0.1289075759 : ℝ) ≤
      (log (((56/25 : ℝ) + 2) / 3) / ((56/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_106_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.34595098057 : ℝ) ≤ log (106/25 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((56/25 : ℝ) + 2) / 3) = (106/25 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1289075759 : ℝ)
      ≤ (0.34595098057 : ℝ) / (((56/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (106/25 : ℝ) - log 3) / (((56/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (106/25 : ℝ) - log 3) / (((56/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((9/4 : ℝ))`, the tangent slope of panel 5 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_9_4 :
    (0.1293860177 : ℝ) ≤
      (log (((9/4 : ℝ) + 2) / 3) / ((9/4 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_17_4
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.34830669426 : ℝ) ≤ log (17/4 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((9/4 : ℝ) + 2) / 3) = (17/4 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1293860177 : ℝ)
      ≤ (0.34830669426 : ℝ) / (((9/4 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (17/4 : ℝ) - log 3) / (((9/4 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (17/4 : ℝ) - log 3) / (((9/4 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((113/50 : ℝ))`, the tangent slope of panel 6 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_113_50 :
    (0.1298594741 : ℝ) ≤
      (log (((113/50 : ℝ) + 2) / 3) / ((113/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_213_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.35065687161 : ℝ) ≤ log (213/50 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((113/50 : ℝ) + 2) / 3) = (213/50 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1298594741 : ℝ)
      ≤ (0.35065687161 : ℝ) / (((113/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (213/50 : ℝ) - log 3) / (((113/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (213/50 : ℝ) - log 3) / (((113/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((227/100 : ℝ))`, the tangent slope of panel 7 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_227_100 :
    (0.1303280002 : ℝ) ≤
      (log (((227/100 : ℝ) + 2) / 3) / ((227/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_427_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.35300153857 : ℝ) ≤ log (427/100 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((227/100 : ℝ) + 2) / 3) = (427/100 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1303280002 : ℝ)
      ≤ (0.35300153857 : ℝ) / (((227/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (427/100 : ℝ) - log 3) / (((227/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (427/100 : ℝ) - log 3) / (((227/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((57/25 : ℝ))`, the tangent slope of panel 8 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_57_25 :
    (0.1307916508 : ℝ) ≤
      (log (((57/25 : ℝ) + 2) / 3) / ((57/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_107_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.35534072092 : ℝ) ≤ log (107/25 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((57/25 : ℝ) + 2) / 3) = (107/25 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1307916508 : ℝ)
      ≤ (0.35534072092 : ℝ) / (((57/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (107/25 : ℝ) - log 3) / (((57/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (107/25 : ℝ) - log 3) / (((57/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((229/100 : ℝ))`, the tangent slope of panel 9 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_229_100 :
    (0.1312504796 : ℝ) ≤
      (log (((229/100 : ℝ) + 2) / 3) / ((229/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_429_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.35767444426 : ℝ) ≤ log (429/100 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((229/100 : ℝ) + 2) / 3) = (429/100 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1312504796 : ℝ)
      ≤ (0.35767444426 : ℝ) / (((229/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (429/100 : ℝ) - log 3) / (((229/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (429/100 : ℝ) - log 3) / (((229/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((23/10 : ℝ))`, the tangent slope of panel 10 of `entry_7_1`. -/
private theorem sigma0_deriv_lower_23_10 :
    (0.1317045397 : ℝ) ≤
      (log (((23/10 : ℝ) + 2) / 3) / ((23/10 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_4_3_bounds
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.36000273402 : ℝ) ≤ log (43/10 : ℝ) - log 3 := by linarith [hx.1, h3.2]
  rw [show (((23/10 : ℝ) + 2) / 3) = (43/10 : ℝ) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1317045397 : ℝ)
      ≤ (0.36000273402 : ℝ) / (((23/10 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log (43/10 : ℝ) - log 3) / (((23/10 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log (43/10 : ℝ) - log 3) / (((23/10 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Panel 0 of the `sigma0` quadrature for `entry_7_1`, on `[(11/5 : ℝ), (221/100 : ℝ)]`. -/
private theorem sigma0_panel_val_0 :
    (0.00021310159505 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(221/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (11/5 : ℝ)) (b := (221/100 : ℝ)) (A := (0.093343408 : ℝ))
    (B := (0.1269428202 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_11_5.1 sigma0_deriv_lower_11_5
  have hl := log_221_220
  rw [show ((221/100 : ℝ)) / ((11/5 : ℝ)) = (221/220 : ℝ) by norm_num] at hp
  have hX : ((0.093343408 : ℝ) - (0.1269428202 : ℝ) * (11/5 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.093343408 : ℝ) - (0.1269428202 : ℝ) * (11/5 : ℝ)) * log (221/220) ≥
      (((0.093343408 : ℝ) - (0.1269428202 : ℝ) * (11/5 : ℝ))) * (0.0045351551654 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 1 of the `sigma0` quadrature for `entry_7_1`, on `[(221/100 : ℝ), (111/50 : ℝ)]`. -/
private theorem sigma0_panel_val_1 :
    (0.00021501629612 : ℝ) ≤ ∫ t in (221/100 : ℝ)..(111/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (221/100 : ℝ)) (b := (111/50 : ℝ)) (A := (0.094615328 : ℝ))
    (B := (0.1274417726 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_221_100.1 sigma0_deriv_lower_221_100
  have hl := log_222_221
  rw [show ((111/50 : ℝ)) / ((221/100 : ℝ)) = (222/221 : ℝ) by norm_num] at hp
  have hX : ((0.094615328 : ℝ) - (0.1274417726 : ℝ) * (221/100 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.094615328 : ℝ) - (0.1274417726 : ℝ) * (221/100 : ℝ)) * log (222/221) ≥
      (((0.094615328 : ℝ) - (0.1274417726 : ℝ) * (221/100 : ℝ))) * (0.00451468035453 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 2 of the `sigma0` quadrature for `entry_7_1`, on `[(111/50 : ℝ), (223/100 : ℝ)]`. -/
private theorem sigma0_panel_val_2 :
    (0.0002169249076 : ℝ) ≤ ∫ t in (111/50 : ℝ)..(223/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (111/50 : ℝ)) (b := (223/100 : ℝ)) (A := (0.095892223 : ℝ))
    (B := (0.1279355106 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_111_50.1 sigma0_deriv_lower_111_50
  have hl := log_223_222
  rw [show ((223/100 : ℝ)) / ((111/50 : ℝ)) = (223/222 : ℝ) by norm_num] at hp
  have hX : ((0.095892223 : ℝ) - (0.1279355106 : ℝ) * (111/50 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.095892223 : ℝ) - (0.1279355106 : ℝ) * (111/50 : ℝ)) * log (223/222) ≥
      (((0.095892223 : ℝ) - (0.1279355106 : ℝ) * (111/50 : ℝ))) * (0.00449438958784 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 3 of the `sigma0` quadrature for `entry_7_1`, on `[(223/100 : ℝ), (56/25 : ℝ)]`. -/
private theorem sigma0_panel_val_3 :
    (0.00021882734632 : ℝ) ≤ ∫ t in (223/100 : ℝ)..(56/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (223/100 : ℝ)) (b := (56/25 : ℝ)) (A := (0.097174019 : ℝ))
    (B := (0.1284240924 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_223_100.1 sigma0_deriv_lower_223_100
  have hl := log_224_223
  rw [show ((56/25 : ℝ)) / ((223/100 : ℝ)) = (224/223 : ℝ) by norm_num] at hp
  have hX : ((0.097174019 : ℝ) - (0.1284240924 : ℝ) * (223/100 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.097174019 : ℝ) - (0.1284240924 : ℝ) * (223/100 : ℝ)) * log (224/223) ≥
      (((0.097174019 : ℝ) - (0.1284240924 : ℝ) * (223/100 : ℝ))) * (0.00447428039493 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 4 of the `sigma0` quadrature for `entry_7_1`, on `[(56/25 : ℝ), (9/4 : ℝ)]`. -/
private theorem sigma0_panel_val_4 :
    (0.00022072361524 : ℝ) ≤ ∫ t in (56/25 : ℝ)..(9/4 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (56/25 : ℝ)) (b := (9/4 : ℝ)) (A := (0.09846068 : ℝ))
    (B := (0.1289075759 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_56_25.1 sigma0_deriv_lower_56_25
  have hl := log_225_224
  rw [show ((9/4 : ℝ)) / ((56/25 : ℝ)) = (225/224 : ℝ) by norm_num] at hp
  have hX : ((0.09846068 : ℝ) - (0.1289075759 : ℝ) * (56/25 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.09846068 : ℝ) - (0.1289075759 : ℝ) * (56/25 : ℝ)) * log (225/224) ≥
      (((0.09846068 : ℝ) - (0.1289075759 : ℝ) * (56/25 : ℝ))) * (0.00445435034939 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 5 of the `sigma0` quadrature for `entry_7_1`, on `[(9/4 : ℝ), (113/50 : ℝ)]`. -/
private theorem sigma0_panel_val_5 :
    (0.00022261369063 : ℝ) ≤ ∫ t in (9/4 : ℝ)..(113/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (9/4 : ℝ)) (b := (113/50 : ℝ)) (A := (0.099752158 : ℝ))
    (B := (0.1293860177 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_9_4.1 sigma0_deriv_lower_9_4
  have hl := log_226_225
  rw [show ((113/50 : ℝ)) / ((9/4 : ℝ)) = (226/225 : ℝ) by norm_num] at hp
  have hX : ((0.099752158 : ℝ) - (0.1293860177 : ℝ) * (9/4 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.099752158 : ℝ) - (0.1293860177 : ℝ) * (9/4 : ℝ)) * log (226/225) ≥
      (((0.099752158 : ℝ) - (0.1293860177 : ℝ) * (9/4 : ℝ))) * (0.00443459706787 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 6 of the `sigma0` quadrature for `entry_7_1`, on `[(113/50 : ℝ), (227/100 : ℝ)]`. -/
private theorem sigma0_panel_val_6 :
    (0.00022449749621 : ℝ) ≤ ∫ t in (113/50 : ℝ)..(227/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (113/50 : ℝ)) (b := (227/100 : ℝ)) (A := (0.101048381 : ℝ))
    (B := (0.1298594741 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_113_50.1 sigma0_deriv_lower_113_50
  have hl := log_227_226
  rw [show ((227/100 : ℝ)) / ((113/50 : ℝ)) = (227/226 : ℝ) by norm_num] at hp
  have hX : ((0.101048381 : ℝ) - (0.1298594741 : ℝ) * (113/50 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.101048381 : ℝ) - (0.1298594741 : ℝ) * (113/50 : ℝ)) * log (227/226) ≥
      (((0.101048381 : ℝ) - (0.1298594741 : ℝ) * (113/50 : ℝ))) * (0.00441501820912 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 7 of the `sigma0` quadrature for `entry_7_1`, on `[(227/100 : ℝ), (57/25 : ℝ)]`. -/
private theorem sigma0_panel_val_7 :
    (0.00022637506252 : ℝ) ≤ ∫ t in (227/100 : ℝ)..(57/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (227/100 : ℝ)) (b := (57/25 : ℝ)) (A := (0.102349325 : ℝ))
    (B := (0.1303280002 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_227_100.1 sigma0_deriv_lower_227_100
  have hl := log_228_227
  rw [show ((57/25 : ℝ)) / ((227/100 : ℝ)) = (228/227 : ℝ) by norm_num] at hp
  have hX : ((0.102349325 : ℝ) - (0.1303280002 : ℝ) * (227/100 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.102349325 : ℝ) - (0.1303280002 : ℝ) * (227/100 : ℝ)) * log (228/227) ≥
      (((0.102349325 : ℝ) - (0.1303280002 : ℝ) * (227/100 : ℝ))) * (0.00439561147304 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 8 of the `sigma0` quadrature for `entry_7_1`, on `[(57/25 : ℝ), (229/100 : ℝ)]`. -/
private theorem sigma0_panel_val_8 :
    (0.00022824633641 : ℝ) ≤ ∫ t in (57/25 : ℝ)..(229/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (57/25 : ℝ)) (b := (229/100 : ℝ)) (A := (0.103654928 : ℝ))
    (B := (0.1307916508 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_57_25.1 sigma0_deriv_lower_57_25
  have hl := log_229_228
  rw [show ((229/100 : ℝ)) / ((57/25 : ℝ)) = (229/228 : ℝ) by norm_num] at hp
  have hX : ((0.103654928 : ℝ) - (0.1307916508 : ℝ) * (57/25 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.103654928 : ℝ) - (0.1307916508 : ℝ) * (57/25 : ℝ)) * log (229/228) ≥
      (((0.103654928 : ℝ) - (0.1307916508 : ℝ) * (57/25 : ℝ))) * (0.0043763745998 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- Panel 9 of the `sigma0` quadrature for `entry_7_1`, on `[(229/100 : ℝ), (23/10 : ℝ)]`. -/
private theorem sigma0_panel_val_9 :
    (0.00023011127217 : ℝ) ≤ ∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower (a := (229/100 : ℝ)) (b := (23/10 : ℝ)) (A := (0.104965131 : ℝ))
    (B := (0.1312504796 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_229_100.1 sigma0_deriv_lower_229_100
  have hl := log_230_229
  rw [show ((23/10 : ℝ)) / ((229/100 : ℝ)) = (230/229 : ℝ) by norm_num] at hp
  have hX : ((0.104965131 : ℝ) - (0.1312504796 : ℝ) * (229/100 : ℝ)) ≤ 0 := by norm_num
  have hmul : ((0.104965131 : ℝ) - (0.1312504796 : ℝ) * (229/100 : ℝ)) * log (230/229) ≥
      (((0.104965131 : ℝ) - (0.1312504796 : ℝ) * (229/100 : ℝ))) * (0.00435730536896 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  linarith [hp, hmul]

/-- `sigma0 t/(2t)` is interval integrable on any `[a,b]` with `1 < a`. -/
private theorem sigma0_div_two_integrable {a b : ℝ} (ha : (1 : ℝ) < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) volume a b := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
  · intro t ht
    exact (sigma0_hasDerivAt (by linarith [ht.1]) hK).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    linarith

/-- The ten-panel tangent sandwich for `∫ sigma0 t/(2t)` on `[11/5, 23/10]`. -/
private theorem sigma0_integral_lower :
    (0.00221643761827 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have s10 : (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (11/5 : ℝ)..(221/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (221/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s0 : (∫ t in (221/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (221/100 : ℝ)..(111/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (111/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s1 : (∫ t in (111/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (111/50 : ℝ)..(223/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (223/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s2 : (∫ t in (223/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (223/100 : ℝ)..(56/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (56/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s3 : (∫ t in (56/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (56/25 : ℝ)..(9/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (9/4 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s4 : (∫ t in (9/4 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (9/4 : ℝ)..(113/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (113/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s5 : (∫ t in (113/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (113/50 : ℝ)..(227/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (227/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s6 : (∫ t in (227/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (227/100 : ℝ)..(57/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (57/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s7 : (∫ t in (57/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (57/25 : ℝ)..(229/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s8 : (∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (23/10 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  rw [s10, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  linarith [sigma0_panel_val_0, sigma0_panel_val_1, sigma0_panel_val_2,
    sigma0_panel_val_3, sigma0_panel_val_4, sigma0_panel_val_5, sigma0_panel_val_6,
    sigma0_panel_val_7, sigma0_panel_val_8, sigma0_panel_val_9]

/-! ### The `entry_7_1` certificate: logarithmic integral, kernel identification, assembly -/

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

/-- Two-sided enclosure of `log (P)` for `P = (29/10 - 1)(319/100 - 1) = 4161/1000`. -/
private theorem log_P_7_1_bounds :
    (1.42575543000 : ℝ) ≤ log ((29/10 - 1) * (319/100 - 1)) ∧
      log ((29/10 - 1) * (319/100 - 1)) ≤ (1.42575543001 : ℝ) := by
  have hP := log_4_161_bounds
  rw [show (29/10 - 1) * (319/100 - 1) = (4161/1000 : ℝ) by norm_num]
  exact hP

/-- Lower bound of `log (16/((29/10-1)(319/100-1)))`, the weight of the `sigma0` term. -/
private theorem log_LP_7_1_lower :
    (1.34683329219 : ℝ) ≤ log (16 / ((29/10 - 1) * (319/100 - 1))) := by
  have h4 := log_four_bounds
  have hP := log_P_7_1_bounds
  rw [show (16 : ℝ) / ((29/10 - 1) * (319/100 - 1)) = 16 / (4161/1000) by norm_num,
    Real.log_div (by norm_num) (by norm_num),
    show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
  push_cast
  linarith [h4.1, hP.2]

/-- `∫_{11/5}^{23/10} log (t+1)/t` from the eight-term geometric expansion at `c = 9/4`. -/
private theorem log_succ_integral_7_1_lower :
    (0.05238647153843 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(23/10 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (11/5 : ℝ) (23/10 : ℝ), |((9/4 : ℝ) - t) / (9/4 + 1)| ≤ (1/65 : ℝ) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (11/5 : ℝ) ≤ 23/10)] at ht
    rw [abs_le]
    have hb : (0 : ℝ) < 9/4 + 1 := by norm_num
    constructor
    · rw [le_div_iff₀ hb]
      nlinarith [ht.1, ht.2]
    · rw [div_le_iff₀ hb]
      nlinarith [ht.1, ht.2]
  have h := log_succ_integral_lower (a := (11/5 : ℝ)) (b := (23/10 : ℝ)) (c := (9/4 : ℝ))
    (r := (1/65 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 8
  have hc := log_3_25_bounds
  have hl := log_23_22
  rw [show ((23/10 : ℝ) / (11/5)) = 23/22 by norm_num] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  norm_num at h
  have hmul : (1.17865499634 : ℝ) * (0.04445176257083 : ℝ) ≤ log (13/4) * log (23/22) := by
    have hm := mul_le_mul hc.1 hl.1 (by norm_num) (by linarith [hc.2])
    linarith [hm]
  linarith [h, hmul, hl.2]

/-- On `[11/5, 23/10]` the `entry_7_1` kernel `Xi1 (29/10) (319/100)` has both indicators
fixed, so it is the sum of the `sigma0` term and one plain logarithmic term. -/
private theorem Xi1_7_1_eq {t : ℝ} (h1 : (11/5 : ℝ) ≤ t) (h2 : t ≤ 23/10) :
    Wu04Functional.Xi1 (29/10) (319/100) t =
      Wu04Integral.sigma0 t / (2 * t) * log (16 / ((29/10 - 1) * (319/100 - 1))) +
        log ((t + 1) ^ 2 / ((29/10 - 1) * (319/100 - 1))) / (2 * t) := by
  have hI1 : (319/100 - 2 : ℝ) ≤ t ∧ t ≤ 3 := by constructor <;> linarith
  have hI2 : ¬ (319/100 - (319/100) / (29/10) - 1 ≤ t ∧ t ≤ (319/100 - 2)) := by
    intro hc
    linarith [hc.2]
  simp only [Wu04Functional.Xi1, Wu04Functional.ind, if_pos hI1]
  rw [if_neg hI2]
  ring

/-- The `entry_7_1` integral, split into the three elementary pieces. -/
private theorem Xi1_7_1_integral :
    (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t) =
      log (16 / ((29/10 - 1) * (319/100 - 1))) *
          (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), log (t + 1) / t) -
          (log ((29/10 - 1) * (319/100 - 1)) / 2) *
            (∫ t in (11/5 : ℝ)..(23/10 : ℝ), 1 / t) := by
  have hI1 := sigma0_div_two_integrable (a := (11/5 : ℝ)) (b := (23/10 : ℝ))
    (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (11/5 : ℝ) (23/10 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (11/5 : ℝ) (23/10 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hPpos : (0 : ℝ) < (29/10 - 1) * (319/100 - 1) := by norm_num
  -- pointwise rewriting
  have hpt : ∀ t ∈ uIcc (11/5 : ℝ) (23/10 : ℝ),
      Wu04Functional.Xi1 (29/10) (319/100) t =
        log (16 / ((29/10 - 1) * (319/100 - 1))) * (Wu04Integral.sigma0 t / (2 * t)) +
          (log (t + 1) / t - (log ((29/10 - 1) * (319/100 - 1)) / 2) * (1 / t)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (11/5 : ℝ) ≤ 23/10)] at ht
    rw [Xi1_7_1_eq ht.1 ht.2]
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    have ht1 : (0 : ℝ) < t + 1 := by linarith
    have h2 : log ((t + 1) ^ 2 / ((29/10 - 1) * (319/100 - 1))) =
        2 * log (t + 1) - log ((29/10 - 1) * (319/100 - 1)) := by
      rw [Real.log_div (by positivity) (ne_of_gt hPpos), Real.log_pow]
      push_cast
      ring
    rw [h2]
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_add (hI1.const_mul _) (hI2.sub (hI3.const_mul _))]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub hI2 (hI3.const_mul _)]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- `integralMatrix 7 1` is the `entry_7_1` quadrature. -/
private theorem integralMatrix_7_1_eq :
    Wu04Table.integralMatrix 7 1 =
      ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 (29/10) (319/100) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_7_1` of Wu's Section 7 matrix**, certified by the ten-panel tangent sandwich. -/
private theorem entry_7_1_certified : (236829 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 7 1 := by
  rw [integralMatrix_7_1_eq, Xi1_7_1_integral]
  have hA := sigma0_integral_lower
  have hB := log_succ_integral_7_1_lower
  have h1t := integral_one_div_exp (a := (11/5 : ℝ)) (b := (23/10 : ℝ)) (by norm_num) (by norm_num)
  have hLP := log_LP_7_1_lower
  have hP := log_P_7_1_bounds
  have h23 := log_23_22
  rw [h1t]
  have hmul : (1.34683329219 : ℝ) * (0.00221643761827 : ℝ) ≤
      log (16 / ((29/10 - 1) * (319/100 - 1))) *
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((29/10 - 1) * (319/100 - 1)) / 2) * log (23/22) ≤
      (1.42575543001 : ℝ) / 2 * (0.04445176257084 : ℝ) := by
    have h2 : log ((29/10 - 1) * (319/100 - 1)) / 2 ≤ (1.42575543001 : ℝ) / 2 := by
      linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- The `(7,1)` entry of the rational candidate matrix, at scale `10^7`. -/
private theorem candidate_7_1 :
    (Wu04Table.candidateMatrixQ 7 1 : ℝ) = 236829 / 10000000 := by
  norm_num [Wu04Table.candidateMatrixQ]

/-- `entry_7_1` in the shape the matrix file states it. -/
private theorem entry_7_1_leaf : (Wu04Table.candidateMatrixQ 7 1 : ℝ) ≤ Wu04Table.integralMatrix 7 1 := by
  rw [candidate_7_1]
  exact entry_7_1_certified

/-! ### The same certificate for the other `Xi1` rows on the `[11/5, 23/10]` panel -/

/-- On `[11/5, 23/10]` the `Xi1` kernel has both indicators fixed whenever `sp - 2 ≤ 11/5`
(the second window sits below the panel and the first covers it). -/
private theorem Xi1_general_eq {s sp t : ℝ} (hsp : sp - 2 < 11/5)
    (h1 : (11/5 : ℝ) ≤ t) (h2 : t ≤ 23/10) :
    Wu04Functional.Xi1 s sp t =
      Wu04Integral.sigma0 t / (2 * t) * log (16 / ((s - 1) * (sp - 1))) +
        log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) / (2 * t) := by
  have hI1 : sp - 2 ≤ t ∧ t ≤ 3 := ⟨le_trans hsp.le h1, by linarith⟩
  have hI2 : ¬ (sp - sp / s - 1 ≤ t ∧ t ≤ sp - 2) := by
    intro hc
    linarith [hc.2, hsp, h1]
  simp only [Wu04Functional.Xi1, Wu04Functional.ind, if_pos hI1]
  rw [if_neg hI2]
  ring

/-- The `Xi1` panel integral in its three elementary pieces, for any `s`, `sp` whose windows sit
below `[11/5, 23/10]`. -/
private theorem Xi1_general_integral {s sp : ℝ} (hsp : sp - 2 < 11/5)
    (hPpos : 0 < (s - 1) * (sp - 1)) :
    (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 s sp t) =
      log (16 / ((s - 1) * (sp - 1))) *
          (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), log (t + 1) / t) -
          (log ((s - 1) * (sp - 1)) / 2) *
            (∫ t in (11/5 : ℝ)..(23/10 : ℝ), 1 / t) := by
  have hI1 := sigma0_div_two_integrable (a := (11/5 : ℝ)) (b := (23/10 : ℝ))
    (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (11/5 : ℝ) (23/10 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (11/5 : ℝ) (23/10 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (11/5 : ℝ) (23/10 : ℝ),
      Wu04Functional.Xi1 s sp t =
        log (16 / ((s - 1) * (sp - 1))) * (Wu04Integral.sigma0 t / (2 * t)) +
          (log (t + 1) / t - (log ((s - 1) * (sp - 1)) / 2) * (1 / t)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (11/5 : ℝ) ≤ 23/10)] at ht
    rw [Xi1_general_eq hsp ht.1 ht.2]
    have hsq : ((t + 1) ^ 2 : ℝ) ≠ 0 := by
      have ht1 : (t + 1) ≠ 0 := by linarith [ht.1]
      positivity
    have h2 : log ((t + 1) ^ 2 / ((s - 1) * (sp - 1))) =
        2 * log (t + 1) - log ((s - 1) * (sp - 1)) := by
      rw [Real.log_div hsq (ne_of_gt hPpos), Real.log_pow]
      push_cast
      ring
    rw [h2]
    field_simp
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_add (hI1.const_mul _) (hI2.sub (hI3.const_mul _))]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub hI2 (hI3.const_mul _)]
  rw [intervalIntegral.integral_const_mul]
  ring


/-! ### Second-order refinement of the `sigma0` panel sandwich

The first-order tangent sandwich leaves `1.8e-8` on `∫ sigma0 t/(2t)`; adding the
second-order term `C (t-a)^2` with `2C ≤ sigma0''` on the panel removes it.
-/

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

/-- Second-order Taylor (tangent plus a quadratic correction) for `sigma0`, from convexity
of `s ↦ sigma0 s - C (s-a)^2` on the panel. -/
private theorem sigma0_taylor2_le {a C t : ℝ} (ha : (11/5 : ℝ) ≤ a) (ht : t ≤ 23/10)
    (hat : a ≤ t)
    (hC : ∀ s ∈ Set.Icc a t,
      2 * C ≤ ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4)) :
    Wu04Integral.sigma0 a +
        ((log ((a + 2) / 3) / (a + 1)) / (1 - Wu04Integral.sigma 3 5 4)) * (t - a)
        + C * (t - a) ^ 2 ≤ Wu04Integral.sigma0 t := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  rcases eq_or_lt_of_le hat with rfl | hlt
  · simp
  · have haD : a ∈ Set.Icc a t := ⟨le_rfl, hat⟩
    have htD : t ∈ Set.Icc a t := ⟨hat, le_rfl⟩
    have hconv : ConvexOn ℝ (Set.Icc a t) (fun s => Wu04Integral.sigma0 s - C * (s - a) ^ 2) := by
      refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc a t)
        (f := fun s : ℝ => Wu04Integral.sigma0 s - C * (s - a) ^ 2)
        (f' := fun s : ℝ => ((log ((s + 2) / 3) / (s + 1)) / (1 - Wu04Integral.sigma 3 5 4))
          - 2 * C * (s - a))
        (f'' := fun s : ℝ => ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
          (1 - Wu04Integral.sigma 3 5 4) - 2 * C)
        (convex_Icc _ _) ?_ ?_ ?_ ?_
      · intro x hx
        have hx1 : (1 : ℝ) < x := by linarith [hx.1, ha]
        exact ((sigma0_hasDerivAt hx1 hK).sub hasDerivAt_const_mul_sq_sub).continuousAt
          |>.continuousWithinAt
      · intro x hx
        have hx' : x ∈ Set.Ioo a t := by rwa [interior_Icc] at hx
        have hx1 : (1 : ℝ) < x := by linarith [hx'.1, ha]
        exact (sigma0_hasDerivAt hx1 hK).sub hasDerivAt_const_mul_sq_sub |>.hasDerivWithinAt
      · intro x hx
        have hx' : x ∈ Set.Ioo a t := by rwa [interior_Icc] at hx
        have hx1 : (1 : ℝ) < x := by linarith [hx'.1, ha]
        have hsub : HasDerivAt
            (fun s : ℝ => ((log ((s + 2) / 3) / (s + 1)) / (1 - Wu04Integral.sigma 3 5 4))
              - 2 * C * (s - a))
            (((1 / (x + 2) * (x + 1) - log ((x + 2) / 3)) / (x + 1) ^ 2) /
              (1 - Wu04Integral.sigma 3 5 4) - 2 * C) x :=
          (hasDerivAt_sigma0' hx1 hK).sub (hasDerivAt_two_mul_const_sub (a := a) (C := C) (x := x))
        exact hsub.hasDerivWithinAt
      · intro x hx
        have hx' : x ∈ Set.Ioo a t := by rwa [interior_Icc] at hx
        have hmem : x ∈ Set.Icc a t := ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
        have hcx := hC x hmem
        linarith
    have hga : HasDerivAt (fun s : ℝ => Wu04Integral.sigma0 s - C * (s - a) ^ 2)
        (((log ((a + 2) / 3) / (a + 1)) / (1 - Wu04Integral.sigma 3 5 4))) a := by
      have ha1 : (1 : ℝ) < a := by linarith
      have h := (sigma0_hasDerivAt ha1 hK).sub
        (hasDerivAt_const_mul_sq_sub (a := a) (C := C) (x := a))
      have hzero : 2 * C * (a - a) = 0 := by ring
      rw [hzero, sub_zero] at h
      exact h
    have hslope := hconv.le_slope_of_hasDerivAt haD htD hlt hga
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < t - a := by linarith
    rw [le_div_iff₀ hpos] at hslope
    linarith [hslope]

/-- Exact integral of the quadratic panel polynomial against `1/(2t)`. -/
private theorem integral_panel_poly2 {a b A B C : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (A + B * (t - a) + C * (t - a) ^ 2) / (2 * t)) =
      (1 / 2) * ((A - B * a) * log (b / a) + B * (b - a)) +
        (C / 2) * ((b ^ 2 - a ^ 2) / 2 - 2 * a * (b - a) + a ^ 2 * log (b / a)) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact lt_of_lt_of_le ha ht.1
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht)))
  have hid : IntervalIntegrable (fun t : ℝ => t) volume a b := continuousOn_id.intervalIntegrable
  have hpt : ∀ t ∈ uIcc a b, (A + B * (t - a) + C * (t - a) ^ 2) / (2 * t) =
      ((A - B * a + C * a ^ 2) / 2) * (1 / t) + (B / 2 - C * a) + (C / 2) * t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hmem t ht)
    field_simp
    ring
  have h1 : IntervalIntegrable
      (fun t : ℝ => ((A - B * a + C * a ^ 2) / 2) * (1 / t)) volume a b := hinv.const_mul _
  have h2 : IntervalIntegrable (fun _ : ℝ => (B / 2 - C * a)) volume a b :=
    intervalIntegrable_const
  have h3 : IntervalIntegrable (fun t : ℝ => (C / 2) * t) volume a b := hid.const_mul _
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_add (h1.add h2) h3]
  rw [intervalIntegral.integral_add h1 h2]
  rw [intervalIntegral.integral_const_mul, integral_one_div_exp ha hab]
  rw [intervalIntegral.integral_const]
  rw [intervalIntegral.integral_const_mul, integral_id]
  simp only [smul_eq_mul]
  ring

/-- **Second-order panel bound**: with `2C ≤ sigma0''` on `[a,b]`, the quadratic
`A + B(t-a) + C(t-a)^2` integrates to a lower bound of `∫ sigma0 t/(2t)`. -/
private theorem sigma0_panel_lower2 {a b A B C : ℝ} (ha : (11/5 : ℝ) ≤ a)
    (hb : b ≤ 23/10) (hab : a ≤ b)
    (hA : A ≤ Wu04Integral.sigma0 a)
    (hB : B ≤ (log ((a + 2) / 3) / (a + 1)) / (1 - Wu04Integral.sigma 3 5 4))
    (hC : ∀ s ∈ Set.Icc a b, 2 * C ≤
      ((1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) / (s + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4)) :
    (1 / 2) * ((A - B * a) * log (b / a) + B * (b - a)) +
        (C / 2) * ((b ^ 2 - a ^ 2) / 2 - 2 * a * (b - a) + a ^ 2 * log (b / a)) ≤
      ∫ t in a..b, Wu04Integral.sigma0 t / (2 * t) := by
  have hmem : ∀ t ∈ uIcc a b, (0 : ℝ) < t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hpt : ∀ t ∈ Set.Icc a b, (A + B * (t - a) + C * (t - a) ^ 2) / (2 * t) ≤
      Wu04Integral.sigma0 t / (2 * t) := by
    intro t ht
    have htt : t ≤ 23/10 := le_trans ht.2 hb
    have htan := sigma0_taylor2_le ha htt ht.1 (fun s hs => hC s ⟨hs.1, le_trans hs.2 ht.2⟩)
    have hstep : A + B * (t - a) + C * (t - a) ^ 2 ≤ Wu04Integral.sigma0 t := by
      have h1 : B * (t - a) ≤ ((log ((a + 2) / 3) / (a + 1)) /
          (1 - Wu04Integral.sigma 3 5 4)) * (t - a) :=
        mul_le_mul_of_nonneg_right hB (by linarith [ht.1])
      linarith [htan]
    have h2t : (0 : ℝ) < 2 * t := by
      have := hmem t (by rw [uIcc_of_le hab]; exact ht)
      linarith
    exact div_le_div_of_nonneg_right hstep h2t.le
  have hcont1 : ContinuousOn (fun t : ℝ => (A + B * (t - a) + C * (t - a) ^ 2) / (2 * t))
      (Set.Icc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · exact (continuousOn_const.add (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))).add
          (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
    · intro t ht
      have := hmem t (by rw [uIcc_of_le hab]; exact ht)
      linarith
  have hcont2 : ContinuousOn (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) (Set.Icc a b) := by
    refine ContinuousOn.div ?_ (continuousOn_const.mul continuousOn_id) ?_
    · intro t ht
      have ht1 : (1 : ℝ) < t := by linarith [ht.1]
      exact (sigma0_hasDerivAt ht1 (by linarith [sigma_3_5_4_bounds_exact.2])).continuousAt
        |>.continuousWithinAt
    · intro t ht
      have := hmem t (by rw [uIcc_of_le hab]; exact ht)
      linarith
  have hcont1' : ContinuousOn (fun t : ℝ => (A + B * (t - a) + C * (t - a) ^ 2) / (2 * t))
      (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hcont1
  have hcont2' : ContinuousOn (fun t : ℝ => Wu04Integral.sigma0 t / (2 * t)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact hcont2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    hcont1'.intervalIntegrable hcont2'.intervalIntegrable hpt
  rw [integral_panel_poly2 (by linarith) hab] at hmono
  exact hmono
/-- Second-order panel 0 of the `sigma0` quadrature, on `[(11/5 : ℝ), (221/100 : ℝ)]`. -/
private theorem sigma0_panel_val2_0 :
    (0.0002131034662297 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(221/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (11/5 : ℝ)) (b := (221/100 : ℝ)) (A := (0.093343408 : ℝ))
    (B := (0.1269428202 : ℝ)) (C := (0.02478363730366 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_11_5.1 sigma0_deriv_lower_11_5
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.43746264771 : ℝ) := by
        have hle : s + 2 ≤ (421/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_421_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.43746264771 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((11/5 : ℝ) + 2) * ((11/5 : ℝ) + 1) = ((11/5 : ℝ) + 1) / ((11/5 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.42305440285476190476 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (321/100 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (321/100 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (321/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02478363730366 : ℝ))) ≤ (0.42305440285476190476 : ℝ) / (((321/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.42305440285476190476 : ℝ) / (((321/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.42305440285476190476 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.42305440285476190476 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_221_220
  rw [show ((221/100 : ℝ)) / ((11/5 : ℝ)) = (221/220 : ℝ) by norm_num] at hp
  have hX : ((0.093343408 : ℝ) - (0.1269428202 : ℝ) * (11/5 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.093343408 : ℝ) - (0.1269428202 : ℝ) * (11/5 : ℝ)) * log (221/220) ≥
      (((0.093343408 : ℝ) - (0.1269428202 : ℝ) * (11/5 : ℝ))) * (0.0045351551654 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02478363730366 : ℝ) * (11/5 : ℝ) ^ 2) * log (221/220) ≥
      ((0.02478363730366 : ℝ) * (11/5 : ℝ) ^ 2) * (0.00453515516539 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 1 of the `sigma0` quadrature, on `[(221/100 : ℝ), (111/50 : ℝ)]`. -/
private theorem sigma0_panel_val2_1 :
    (0.0002150181394035 : ℝ) ≤ ∫ t in (221/100 : ℝ)..(111/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (221/100 : ℝ)) (b := (111/50 : ℝ)) (A := (0.094615328 : ℝ))
    (B := (0.1274417726 : ℝ)) (C := (0.02452474225659 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_221_100.1 sigma0_deriv_lower_221_100
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.43983512806 : ℝ) := by
        have hle : s + 2 ≤ (211/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_211_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.43983512806 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((221/100 : ℝ) + 2) * ((221/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((221/100 : ℝ) + 2) * ((221/100 : ℝ) + 1) = ((221/100 : ℝ) + 1) / ((221/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.42124746938859857482 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (161/50 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (161/50 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (161/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02452474225659 : ℝ))) ≤ (0.42124746938859857482 : ℝ) / (((161/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.42124746938859857482 : ℝ) / (((161/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.42124746938859857482 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.42124746938859857482 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_222_221
  rw [show ((111/50 : ℝ)) / ((221/100 : ℝ)) = (222/221 : ℝ) by norm_num] at hp
  have hX : ((0.094615328 : ℝ) - (0.1274417726 : ℝ) * (221/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.094615328 : ℝ) - (0.1274417726 : ℝ) * (221/100 : ℝ)) * log (222/221) ≥
      (((0.094615328 : ℝ) - (0.1274417726 : ℝ) * (221/100 : ℝ))) * (0.00451468035453 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02452474225659 : ℝ) * (221/100 : ℝ) ^ 2) * log (222/221) ≥
      ((0.02452474225659 : ℝ) * (221/100 : ℝ) ^ 2) * (0.00451468035452 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 2 of the `sigma0` quadrature, on `[(111/50 : ℝ), (223/100 : ℝ)]`. -/
private theorem sigma0_panel_val2_2 :
    (0.0002169267234481 : ℝ) ≤ ∫ t in (111/50 : ℝ)..(223/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (111/50 : ℝ)) (b := (223/100 : ℝ)) (A := (0.095892223 : ℝ))
    (B := (0.1279355106 : ℝ)) (C := (0.02426874309029 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_111_50.1 sigma0_deriv_lower_111_50
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.44220199307 : ℝ) := by
        have hle : s + 2 ≤ (423/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_423_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.44220199307 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((111/50 : ℝ) + 2) * ((111/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((111/50 : ℝ) + 2) * ((111/50 : ℝ) + 1) = ((111/50 : ℝ) + 1) / ((111/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.41944347094545023696 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (323/100 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (323/100 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (323/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02426874309029 : ℝ))) ≤ (0.41944347094545023696 : ℝ) / (((323/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.41944347094545023696 : ℝ) / (((323/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.41944347094545023696 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.41944347094545023696 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_223_222
  rw [show ((223/100 : ℝ)) / ((111/50 : ℝ)) = (223/222 : ℝ) by norm_num] at hp
  have hX : ((0.095892223 : ℝ) - (0.1279355106 : ℝ) * (111/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.095892223 : ℝ) - (0.1279355106 : ℝ) * (111/50 : ℝ)) * log (223/222) ≥
      (((0.095892223 : ℝ) - (0.1279355106 : ℝ) * (111/50 : ℝ))) * (0.00449438958784 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02426874309029 : ℝ) * (111/50 : ℝ) ^ 2) * log (223/222) ≥
      ((0.02426874309029 : ℝ) * (111/50 : ℝ) ^ 2) * (0.00449438958783 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 3 of the `sigma0` quadrature, on `[(223/100 : ℝ), (56/25 : ℝ)]`. -/
private theorem sigma0_panel_val2_3 :
    (0.0002188291351958 : ℝ) ≤ ∫ t in (223/100 : ℝ)..(56/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (223/100 : ℝ)) (b := (56/25 : ℝ)) (A := (0.097174019 : ℝ))
    (B := (0.1284240924 : ℝ)) (C := (0.0240156006256 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_223_100.1 sigma0_deriv_lower_223_100
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.44456326926 : ℝ) := by
        have hle : s + 2 ≤ (106/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_106_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.44456326926 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((223/100 : ℝ) + 2) * ((223/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((223/100 : ℝ) + 2) * ((223/100 : ℝ) + 1) = ((223/100 : ℝ) + 1) / ((223/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.4176424000146572104 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (81/25 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (81/25 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (81/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.0240156006256 : ℝ))) ≤ (0.4176424000146572104 : ℝ) / (((81/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.4176424000146572104 : ℝ) / (((81/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.4176424000146572104 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.4176424000146572104 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_224_223
  rw [show ((56/25 : ℝ)) / ((223/100 : ℝ)) = (224/223 : ℝ) by norm_num] at hp
  have hX : ((0.097174019 : ℝ) - (0.1284240924 : ℝ) * (223/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.097174019 : ℝ) - (0.1284240924 : ℝ) * (223/100 : ℝ)) * log (224/223) ≥
      (((0.097174019 : ℝ) - (0.1284240924 : ℝ) * (223/100 : ℝ))) * (0.00447428039493 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.0240156006256 : ℝ) * (223/100 : ℝ) ^ 2) * log (224/223) ≥
      ((0.0240156006256 : ℝ) * (223/100 : ℝ) ^ 2) * (0.00447428039492 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 4 of the `sigma0` quadrature, on `[(56/25 : ℝ), (9/4 : ℝ)]`. -/
private theorem sigma0_panel_val2_4 :
    (0.0002207253775908 : ℝ) ≤ ∫ t in (56/25 : ℝ)..(9/4 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (56/25 : ℝ)) (b := (9/4 : ℝ)) (A := (0.09846068 : ℝ))
    (B := (0.1289075759 : ℝ)) (C := (0.02376527631847 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_56_25.1 sigma0_deriv_lower_56_25
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.44691898295 : ℝ) := by
        have hle : s + 2 ≤ (17/4 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_17_4.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.44691898295 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((56/25 : ℝ) + 2) * ((56/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((56/25 : ℝ) + 2) * ((56/25 : ℝ) + 1) = ((56/25 : ℝ) + 1) / ((56/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.41584424910622641509 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (13/4 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (13/4 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (13/4 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02376527631847 : ℝ))) ≤ (0.41584424910622641509 : ℝ) / (((13/4 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.41584424910622641509 : ℝ) / (((13/4 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.41584424910622641509 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.41584424910622641509 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_225_224
  rw [show ((9/4 : ℝ)) / ((56/25 : ℝ)) = (225/224 : ℝ) by norm_num] at hp
  have hX : ((0.09846068 : ℝ) - (0.1289075759 : ℝ) * (56/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.09846068 : ℝ) - (0.1289075759 : ℝ) * (56/25 : ℝ)) * log (225/224) ≥
      (((0.09846068 : ℝ) - (0.1289075759 : ℝ) * (56/25 : ℝ))) * (0.00445435034939 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02376527631847 : ℝ) * (56/25 : ℝ) ^ 2) * log (225/224) ≥
      ((0.02376527631847 : ℝ) * (56/25 : ℝ) ^ 2) * (0.00445435034938 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 5 of the `sigma0` quadrature, on `[(9/4 : ℝ), (113/50 : ℝ)]`. -/
private theorem sigma0_panel_val2_5 :
    (0.0002226154269026 : ℝ) ≤ ∫ t in (9/4 : ℝ)..(113/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (9/4 : ℝ)) (b := (113/50 : ℝ)) (A := (0.099752158 : ℝ))
    (B := (0.1293860177 : ℝ)) (C := (0.02351773224571 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_9_4.1 sigma0_deriv_lower_9_4
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.4492691603 : ℝ) := by
        have hle : s + 2 ≤ (213/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_213_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.4492691603 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((9/4 : ℝ) + 2) * ((9/4 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((9/4 : ℝ) + 2) * ((9/4 : ℝ) + 1) = ((9/4 : ℝ) + 1) / ((9/4 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.41404901071294117647 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (163/50 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (163/50 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (163/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02351773224571 : ℝ))) ≤ (0.41404901071294117647 : ℝ) / (((163/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.41404901071294117647 : ℝ) / (((163/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.41404901071294117647 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.41404901071294117647 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_226_225
  rw [show ((113/50 : ℝ)) / ((9/4 : ℝ)) = (226/225 : ℝ) by norm_num] at hp
  have hX : ((0.099752158 : ℝ) - (0.1293860177 : ℝ) * (9/4 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.099752158 : ℝ) - (0.1293860177 : ℝ) * (9/4 : ℝ)) * log (226/225) ≥
      (((0.099752158 : ℝ) - (0.1293860177 : ℝ) * (9/4 : ℝ))) * (0.00443459706787 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02351773224571 : ℝ) * (9/4 : ℝ) ^ 2) * log (226/225) ≥
      ((0.02351773224571 : ℝ) * (9/4 : ℝ) ^ 2) * (0.00443459706786 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 6 of the `sigma0` quadrature, on `[(113/50 : ℝ), (227/100 : ℝ)]`. -/
private theorem sigma0_panel_val2_6 :
    (0.000224499206836 : ℝ) ≤ ∫ t in (113/50 : ℝ)..(227/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (113/50 : ℝ)) (b := (227/100 : ℝ)) (A := (0.101048381 : ℝ))
    (B := (0.1298594741 : ℝ)) (C := (0.02327293109622 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_113_50.1 sigma0_deriv_lower_113_50
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.45161382726 : ℝ) := by
        have hle : s + 2 ≤ (427/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_427_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.45161382726 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((113/50 : ℝ) + 2) * ((113/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((113/50 : ℝ) + 2) * ((113/50 : ℝ) + 1) = ((113/50 : ℝ) + 1) / ((113/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.41225667736244131455 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (327/100 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (327/100 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (327/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02327293109622 : ℝ))) ≤ (0.41225667736244131455 : ℝ) / (((327/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.41225667736244131455 : ℝ) / (((327/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.41225667736244131455 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.41225667736244131455 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_227_226
  rw [show ((227/100 : ℝ)) / ((113/50 : ℝ)) = (227/226 : ℝ) by norm_num] at hp
  have hX : ((0.101048381 : ℝ) - (0.1298594741 : ℝ) * (113/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.101048381 : ℝ) - (0.1298594741 : ℝ) * (113/50 : ℝ)) * log (227/226) ≥
      (((0.101048381 : ℝ) - (0.1298594741 : ℝ) * (113/50 : ℝ))) * (0.00441501820912 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02327293109622 : ℝ) * (113/50 : ℝ) ^ 2) * log (227/226) ≥
      ((0.02327293109622 : ℝ) * (113/50 : ℝ) ^ 2) * (0.00441501820911 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 7 of the `sigma0` quadrature, on `[(227/100 : ℝ), (57/25 : ℝ)]`. -/
private theorem sigma0_panel_val2_7 :
    (0.0002263767479193 : ℝ) ≤ ∫ t in (227/100 : ℝ)..(57/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (227/100 : ℝ)) (b := (57/25 : ℝ)) (A := (0.102349325 : ℝ))
    (B := (0.1303280002 : ℝ)) (C := (0.02303083615724 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_227_100.1 sigma0_deriv_lower_227_100
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.45395300961 : ℝ) := by
        have hle : s + 2 ≤ (107/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_107_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.45395300961 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((227/100 : ℝ) + 2) * ((227/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((227/100 : ℝ) + 2) * ((227/100 : ℝ) + 1) = ((227/100 : ℝ) + 1) / ((227/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.41046724157927400468 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (82/25 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (82/25 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (82/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02303083615724 : ℝ))) ≤ (0.41046724157927400468 : ℝ) / (((82/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.41046724157927400468 : ℝ) / (((82/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.41046724157927400468 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.41046724157927400468 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_228_227
  rw [show ((57/25 : ℝ)) / ((227/100 : ℝ)) = (228/227 : ℝ) by norm_num] at hp
  have hX : ((0.102349325 : ℝ) - (0.1303280002 : ℝ) * (227/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.102349325 : ℝ) - (0.1303280002 : ℝ) * (227/100 : ℝ)) * log (228/227) ≥
      (((0.102349325 : ℝ) - (0.1303280002 : ℝ) * (227/100 : ℝ))) * (0.00439561147304 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02303083615724 : ℝ) * (227/100 : ℝ) ^ 2) * log (228/227) ≥
      ((0.02303083615724 : ℝ) * (227/100 : ℝ) ^ 2) * (0.00439561147303 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 8 of the `sigma0` quadrature, on `[(57/25 : ℝ), (229/100 : ℝ)]`. -/
private theorem sigma0_panel_val2_8 :
    (0.0002282479969919 : ℝ) ≤ ∫ t in (57/25 : ℝ)..(229/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (57/25 : ℝ)) (b := (229/100 : ℝ)) (A := (0.103654928 : ℝ))
    (B := (0.1307916508 : ℝ)) (C := (0.02279141130324 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_57_25.1 sigma0_deriv_lower_57_25
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.45628673296 : ℝ) := by
        have hle : s + 2 ≤ (429/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_429_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.45628673296 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((57/25 : ℝ) + 2) * ((57/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((57/25 : ℝ) + 2) * ((57/25 : ℝ) + 1) = ((57/25 : ℝ) + 1) / ((57/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.40868069588691588785 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (329/100 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (329/100 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (329/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02279141130324 : ℝ))) ≤ (0.40868069588691588785 : ℝ) / (((329/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.40868069588691588785 : ℝ) / (((329/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.40868069588691588785 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.40868069588691588785 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_229_228
  rw [show ((229/100 : ℝ)) / ((57/25 : ℝ)) = (229/228 : ℝ) by norm_num] at hp
  have hX : ((0.103654928 : ℝ) - (0.1307916508 : ℝ) * (57/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.103654928 : ℝ) - (0.1307916508 : ℝ) * (57/25 : ℝ)) * log (229/228) ≥
      (((0.103654928 : ℝ) - (0.1307916508 : ℝ) * (57/25 : ℝ))) * (0.0043763745998 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02279141130324 : ℝ) * (57/25 : ℝ) ^ 2) * log (229/228) ≥
      ((0.02279141130324 : ℝ) * (57/25 : ℝ) ^ 2) * (0.00437637459979 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 9 of the `sigma0` quadrature, on `[(229/100 : ℝ), (23/10 : ℝ)]`. -/
private theorem sigma0_panel_val2_9 :
    (0.0002301129083436 : ℝ) ≤ ∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2 (a := (229/100 : ℝ)) (b := (23/10 : ℝ)) (A := (0.104965131 : ℝ))
    (B := (0.1312504796 : ℝ)) (C := (0.02255462098716 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    sigma0_panel_229_100.1 sigma0_deriv_lower_229_100
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.45861502271 : ℝ) := by
        have hle : s + 2 ≤ (43/10 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_4_3_bounds.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.45861502271 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((229/100 : ℝ) + 2) * ((229/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((229/100 : ℝ) + 2) * ((229/100 : ℝ) + 1) = ((229/100 : ℝ) + 1) / ((229/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.40689703284976689976 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          (33/10 : ℝ) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ (33/10 : ℝ) ^ 2 := by
          have h1 : s + 1 ≤ (33/10 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02255462098716 : ℝ))) ≤ (0.40689703284976689976 : ℝ) / (((33/10 : ℝ)) ^ 2 * (0.828306585 : ℝ)) := by norm_num
      have step1 : (0.40689703284976689976 : ℝ) / (((33/10 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.40689703284976689976 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.40689703284976689976 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_230_229
  rw [show ((23/10 : ℝ)) / ((229/100 : ℝ)) = (230/229 : ℝ) by norm_num] at hp
  have hX : ((0.104965131 : ℝ) - (0.1312504796 : ℝ) * (229/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.104965131 : ℝ) - (0.1312504796 : ℝ) * (229/100 : ℝ)) * log (230/229) ≥
      (((0.104965131 : ℝ) - (0.1312504796 : ℝ) * (229/100 : ℝ))) * (0.00435730536896 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02255462098716 : ℝ) * (229/100 : ℝ) ^ 2) * log (230/229) ≥
      ((0.02255462098716 : ℝ) * (229/100 : ℝ) ^ 2) * (0.00435730536895 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- The ten-panel **second-order** sandwich for `∫ sigma0 t/(2t)` on `[11/5, 23/10]`. -/
private theorem sigma0_integral_lower2 :
    (0.0022164551288613 : ℝ) ≤ ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have s10 : (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (11/5 : ℝ)..(221/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (221/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s0 : (∫ t in (221/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (221/100 : ℝ)..(111/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (111/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s1 : (∫ t in (111/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (111/50 : ℝ)..(223/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (223/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s2 : (∫ t in (223/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (223/100 : ℝ)..(56/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (56/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s3 : (∫ t in (56/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (56/25 : ℝ)..(9/4 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (9/4 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s4 : (∫ t in (9/4 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (9/4 : ℝ)..(113/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (113/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s5 : (∫ t in (113/50 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (113/50 : ℝ)..(227/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (227/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s6 : (∫ t in (227/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (227/100 : ℝ)..(57/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (57/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s7 : (∫ t in (57/25 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (57/25 : ℝ)..(229/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s8 : (∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (229/100 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (23/10 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  rw [s10, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  linarith [sigma0_panel_val2_0, sigma0_panel_val2_1, sigma0_panel_val2_2,
    sigma0_panel_val2_3, sigma0_panel_val2_4, sigma0_panel_val2_5, sigma0_panel_val2_6,
    sigma0_panel_val2_7, sigma0_panel_val2_8, sigma0_panel_val2_9]

/-! ### The remaining `Xi1` rows of the `[11/5, 23/10]` panel, with the second-order sandwich -/

/-- `integralMatrix 4 1` is the `Xi1 (13/5) (179/50)` quadrature on `[11/5, 23/10]`. -/
private theorem integralMatrix_4_1_eq :
    Wu04Table.integralMatrix 4 1 =
      ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 (13/5) (179/50) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- Two-sided enclosure of `log (516/125)`, the parameter `P` of row 4. -/
private theorem log_P_4_bounds :
    (1.41779302817926 : ℝ) ≤ log (516/125) ∧ log (516/125) ≤ (1.4177930281793 : ℝ) := by
  have h := log_enclosure (y := 516/125) (x := (391/641 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 32
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- **`entry_4_1` of Wu's Section 7 matrix**, certified by the second-order `sigma0` sandwich. -/
private theorem entry_4_1_certified :
    (238776 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 4 1 := by
  rw [integralMatrix_4_1_eq,
    Xi1_general_integral (s := 13/5) (sp := 179/50) (by norm_num) (by norm_num),
    show ((13/5 : ℝ) - 1) * (179/50 - 1) = 516/125 by norm_num]
  have hA := sigma0_integral_lower2
  have hB := log_succ_integral_7_1_lower
  have h1t := integral_one_div_exp (a := (11/5 : ℝ)) (b := (23/10 : ℝ))
    (by norm_num) (by norm_num)
  have hP := log_P_4_bounds
  have h23 := log_23_22
  have h4 := log_four_bounds
  rw [h1t]
  have hLP : (1.3547956940207 : ℝ) ≤ log (16 / (516/125)) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3547956940207 : ℝ) * (0.0022164551288613 : ℝ) ≤
      log (16 / (516/125)) *
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log (516/125) / 2) * log (23/22) ≤
      (1.4177930281793 : ℝ) / 2 * (0.04445176257084 : ℝ) := by
    have h2 : log (516/125) / 2 ≤ (1.4177930281793 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_4_1` in the shape the matrix file states it. -/
private theorem entry_4_1_leaf :
    (Wu04Table.candidateMatrixQ 4 1 : ℝ) ≤ Wu04Table.integralMatrix 4 1 := by
  have hc : (Wu04Table.candidateMatrixQ 4 1 : ℝ) = 238776 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_4_1_certified

/-- `integralMatrix 5 1` is the `Xi1 (27/10) (347/100)` quadrature on `[11/5, 23/10]`. -/
private theorem integralMatrix_5_1_eq :
    Wu04Table.integralMatrix 5 1 =
      ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 (27/10) (347/100) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- Two-sided enclosure of `log (4199/1000)`, the parameter `P` of row 5. -/
private theorem log_P_5_bounds :
    (1.43484640170205 : ℝ) ≤ log (4199/1000) ∧ log (4199/1000) ≤ (1.43484640170212 : ℝ) := by
  have h := log_enclosure (y := 4199/1000) (x := (3199/5199 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 32
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- **`entry_5_1` of Wu's Section 7 matrix**, certified by the second-order `sigma0` sandwich. -/
private theorem entry_5_1_certified :
    (234607 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 5 1 := by
  rw [integralMatrix_5_1_eq,
    Xi1_general_integral (s := 27/10) (sp := 347/100) (by norm_num) (by norm_num),
    show ((27/10 : ℝ) - 1) * (347/100 - 1) = 4199/1000 by norm_num]
  have hA := sigma0_integral_lower2
  have hB := log_succ_integral_7_1_lower
  have h1t := integral_one_div_exp (a := (11/5 : ℝ)) (b := (23/10 : ℝ))
    (by norm_num) (by norm_num)
  have hP := log_P_5_bounds
  have h23 := log_23_22
  have h4 := log_four_bounds
  rw [h1t]
  have hLP : (1.33774232049788 : ℝ) ≤ log (16 / (4199/1000)) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.33774232049788 : ℝ) * (0.0022164551288613 : ℝ) ≤
      log (16 / (4199/1000)) *
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log (4199/1000) / 2) * log (23/22) ≤
      (1.43484640170212 : ℝ) / 2 * (0.04445176257084 : ℝ) := by
    have h2 : log (4199/1000) / 2 ≤ (1.43484640170212 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_5_1` in the shape the matrix file states it. -/
private theorem entry_5_1_leaf :
    (Wu04Table.candidateMatrixQ 5 1 : ℝ) ≤ Wu04Table.integralMatrix 5 1 := by
  have hc : (Wu04Table.candidateMatrixQ 5 1 : ℝ) = 234607 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_5_1_certified

/-- `integralMatrix 6 1` is the `Xi1 (14/5) (167/50)` quadrature on `[11/5, 23/10]`. -/
private theorem integralMatrix_6_1_eq :
    Wu04Table.integralMatrix 6 1 =
      ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 (14/5) (167/50) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- Two-sided enclosure of `log (1053/250)`, the parameter `P` of row 6. -/
private theorem log_P_6_bounds :
    (1.43793759427172 : ℝ) ≤ log (1053/250) ∧ log (1053/250) ≤ (1.4379375942718 : ℝ) := by
  have h := log_enclosure (y := 1053/250) (x := (803/1303 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) 32
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- **`entry_6_1` of Wu's Section 7 matrix**, certified by the second-order `sigma0` sandwich. -/
private theorem entry_6_1_certified :
    (233852 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 6 1 := by
  rw [integralMatrix_6_1_eq,
    Xi1_general_integral (s := 14/5) (sp := 167/50) (by norm_num) (by norm_num),
    show ((14/5 : ℝ) - 1) * (167/50 - 1) = 1053/250 by norm_num]
  have hA := sigma0_integral_lower2
  have hB := log_succ_integral_7_1_lower
  have h1t := integral_one_div_exp (a := (11/5 : ℝ)) (b := (23/10 : ℝ))
    (by norm_num) (by norm_num)
  have hP := log_P_6_bounds
  have h23 := log_23_22
  have h4 := log_four_bounds
  rw [h1t]
  have hLP : (1.3346511279282 : ℝ) ≤ log (16 / (1053/250)) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3346511279282 : ℝ) * (0.0022164551288613 : ℝ) ≤
      log (16 / (1053/250)) *
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log (1053/250) / 2) * log (23/22) ≤
      (1.4379375942718 : ℝ) / 2 * (0.04445176257084 : ℝ) := by
    have h2 : log (1053/250) / 2 ≤ (1.4379375942718 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_6_1` in the shape the matrix file states it. -/
private theorem entry_6_1_leaf :
    (Wu04Table.candidateMatrixQ 6 1 : ℝ) ≤ Wu04Table.integralMatrix 6 1 := by
  have hc : (Wu04Table.candidateMatrixQ 6 1 : ℝ) = 233852 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_6_1_certified

/-- `integralMatrix 8 1` is the `Xi1 (3) (3)` quadrature on `[11/5, 23/10]`. -/
private theorem integralMatrix_8_1_eq :
    Wu04Table.integralMatrix 8 1 =
      ∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Functional.Xi1 (3) (3) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_8_1` of Wu's Section 7 matrix**, certified by the second-order `sigma0` sandwich. -/
private theorem entry_8_1_certified :
    (246475 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 8 1 := by
  rw [integralMatrix_8_1_eq,
    Xi1_general_integral (s := 3) (sp := 3) (by norm_num) (by norm_num),
    show ((3 : ℝ) - 1) * (3 - 1) = 4 by norm_num]
  have hA := sigma0_integral_lower2
  have hB := log_succ_integral_7_1_lower
  have h1t := integral_one_div_exp (a := (11/5 : ℝ)) (b := (23/10 : ℝ))
    (by norm_num) (by norm_num)
  have hP : (1.3862943611 : ℝ) ≤ log (4) ∧ log (4) ≤ (1.3862943615 : ℝ) := log_four_bounds
  have h23 := log_23_22
  have h4 := log_four_bounds
  rw [h1t]
  have hLP : (1.3862943607 : ℝ) ≤ log (16 / (4)) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3862943607 : ℝ) * (0.0022164551288613 : ℝ) ≤
      log (16 / (4)) *
        (∫ t in (11/5 : ℝ)..(23/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log (4) / 2) * log (23/22) ≤
      (1.3862943615 : ℝ) / 2 * (0.04445176257084 : ℝ) := by
    have h2 : log (4) / 2 ≤ (1.3862943615 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_8_1` in the shape the matrix file states it. -/
private theorem entry_8_1_leaf :
    (Wu04Table.candidateMatrixQ 8 1 : ℝ) ≤ Wu04Table.integralMatrix 8 1 := by
  have hc : (Wu04Table.candidateMatrixQ 8 1 : ℝ) = 246475 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_8_1_certified


/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,1} = ∫_{1}^{2.2} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 1551926/10⁷`.
scipy value 0.1551926574, margin 0.57e−7. -/
theorem entry_0_0 : (candidateMatrixQ 0 0 : ℝ) ≤ integralMatrix 0 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 261910/10⁷`.
scipy value 0.0261910681, margin 0.68e−7. -/
theorem entry_0_1 : (candidateMatrixQ 0 1 : ℝ) ≤ integralMatrix 0 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 266515/10⁷`.
scipy value 0.0266515083, margin 0.08e−7. -/
theorem entry_0_2 : (candidateMatrixQ 0 2 : ℝ) ≤ integralMatrix 0 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 269346/10⁷`.
scipy value 0.0269346906, margin 0.91e−7. -/
theorem entry_0_3 : (candidateMatrixQ 0 3 : ℝ) ≤ integralMatrix 0 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 271084/10⁷`.
scipy value 0.0271084782, margin 0.78e−7. -/
theorem entry_0_4 : (candidateMatrixQ 0 4 : ℝ) ≤ integralMatrix 0 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 274861/10⁷`.
scipy value 0.0274861583, margin 0.58e−7. -/
theorem entry_0_5 : (candidateMatrixQ 0 5 : ℝ) ≤ integralMatrix 0 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 278478/10⁷`.
scipy value 0.0278478963, margin 0.96e−7. -/
theorem entry_0_6 : (candidateMatrixQ 0 6 : ℝ) ≤ integralMatrix 0 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 281663/10⁷`.
scipy value 0.0281663353, margin 0.35e−7. -/
theorem entry_0_7 : (candidateMatrixQ 0 7 : ℝ) ≤ integralMatrix 0 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{1,9} = ∫_{2.9}^{3} Ξ₂(t; 2.2, 4.54, 3.53, 2.90, 2.44) dt ≥ 284464/10⁷`.
scipy value 0.0284464442, margin 0.44e−7. -/
theorem entry_0_8 : (candidateMatrixQ 0 8 : ℝ) ≤ integralMatrix 0 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,1} = ∫_{1}^{2.2} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 1537386/10⁷`.
scipy value 0.1537386795, margin 0.80e−7. -/
theorem entry_1_0 : (candidateMatrixQ 1 0 : ℝ) ≤ integralMatrix 1 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 255908/10⁷`.
scipy value 0.0255908608, margin 0.61e−7. -/
theorem entry_1_1 : (candidateMatrixQ 1 1 : ℝ) ≤ integralMatrix 1 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 260352/10⁷`.
scipy value 0.0260352023, margin 0.02e−7. -/
theorem entry_1_2 : (candidateMatrixQ 1 2 : ℝ) ≤ integralMatrix 1 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 262914/10⁷`.
scipy value 0.0262914366, margin 0.37e−7. -/
theorem entry_1_3 : (candidateMatrixQ 1 3 : ℝ) ≤ integralMatrix 1 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 265826/10⁷`.
scipy value 0.0265826524, margin 0.52e−7. -/
theorem entry_1_4 : (candidateMatrixQ 1 4 : ℝ) ≤ integralMatrix 1 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 270061/10⁷`.
scipy value 0.0270061132, margin 0.13e−7. -/
theorem entry_1_5 : (candidateMatrixQ 1 5 : ℝ) ≤ integralMatrix 1 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 273794/10⁷`.
scipy value 0.0273794440, margin 0.44e−7. -/
theorem entry_1_6 : (candidateMatrixQ 1 6 : ℝ) ≤ integralMatrix 1 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 277085/10⁷`.
scipy value 0.0277085524, margin 0.52e−7. -/
theorem entry_1_7 : (candidateMatrixQ 1 7 : ℝ) ≤ integralMatrix 1 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{2,9} = ∫_{2.9}^{3} Ξ₂(t; 2.3, 4.50, 3.54, 2.88, 2.43) dt ≥ 279985/10⁷`.
scipy value 0.0279985116, margin 0.12e−7. -/
theorem entry_1_8 : (candidateMatrixQ 1 8 : ℝ) ≤ integralMatrix 1 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,1} = ∫_{1}^{2.2} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 1525199/10⁷`.
scipy value 0.1525199200, margin 0.20e−7. -/
theorem entry_2_0 : (candidateMatrixQ 2 0 : ℝ) ≤ integralMatrix 2 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 250515/10⁷`.
scipy value 0.0250515037, margin 0.04e−7. -/
theorem entry_2_1 : (candidateMatrixQ 2 1 : ℝ) ≤ integralMatrix 2 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 254743/10⁷`.
scipy value 0.0254743353, margin 0.35e−7. -/
theorem entry_2_2 : (candidateMatrixQ 2 2 : ℝ) ≤ integralMatrix 2 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 257327/10⁷`.
scipy value 0.0257327789, margin 0.79e−7. -/
theorem entry_2_3 : (candidateMatrixQ 2 3 : ℝ) ≤ integralMatrix 2 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 261548/10⁷`.
scipy value 0.0261548552, margin 0.55e−7. -/
theorem entry_2_4 : (candidateMatrixQ 2 4 : ℝ) ≤ integralMatrix 2 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 265892/10⁷`.
scipy value 0.0265892899, margin 0.90e−7. -/
theorem entry_2_5 : (candidateMatrixQ 2 5 : ℝ) ≤ integralMatrix 2 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 269726/10⁷`.
scipy value 0.0269726868, margin 0.87e−7. -/
theorem entry_2_6 : (candidateMatrixQ 2 6 : ℝ) ≤ integralMatrix 2 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 273110/10⁷`.
scipy value 0.0273110594, margin 0.59e−7. -/
theorem entry_2_7 : (candidateMatrixQ 2 7 : ℝ) ≤ integralMatrix 2 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{3,9} = ∫_{2.9}^{3} Ξ₂(t; 2.4, 4.46, 3.57, 2.87, 2.40) dt ≥ 276095/10⁷`.
scipy value 0.0276095716, margin 0.72e−7. -/
theorem entry_2_8 : (candidateMatrixQ 2 8 : ℝ) ≤ integralMatrix 2 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,1} = ∫_{1}^{2.2} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 1549103/10⁷`.
scipy value 0.1549103474, margin 0.47e−7. -/
theorem entry_3_0 : (candidateMatrixQ 3 0 : ℝ) ≤ integralMatrix 3 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,2} = ∫_{2.2}^{2.3} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 239617/10⁷`.
scipy value 0.0239617849, margin 0.85e−7. -/
theorem entry_3_1 : (candidateMatrixQ 3 1 : ℝ) ≤ integralMatrix 3 1 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,3} = ∫_{2.3}^{2.4} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 246126/10⁷`.
scipy value 0.0246126132, margin 0.13e−7. -/
theorem entry_3_2 : (candidateMatrixQ 3 2 : ℝ) ≤ integralMatrix 3 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,4} = ∫_{2.4}^{2.5} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 251857/10⁷`.
scipy value 0.0251857826, margin 0.83e−7. -/
theorem entry_3_3 : (candidateMatrixQ 3 3 : ℝ) ≤ integralMatrix 3 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,5} = ∫_{2.5}^{2.6} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 256913/10⁷`.
scipy value 0.0256913054, margin 0.05e−7. -/
theorem entry_3_4 : (candidateMatrixQ 3 4 : ℝ) ≤ integralMatrix 3 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,6} = ∫_{2.6}^{2.7} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 261376/10⁷`.
scipy value 0.0261376312, margin 0.31e−7. -/
theorem entry_3_5 : (candidateMatrixQ 3 5 : ℝ) ≤ integralMatrix 3 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,7} = ∫_{2.7}^{2.8} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 265319/10⁷`.
scipy value 0.0265319355, margin 0.35e−7. -/
theorem entry_3_6 : (candidateMatrixQ 3 6 : ℝ) ≤ integralMatrix 3 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,8} = ∫_{2.8}^{2.9} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 268803/10⁷`.
scipy value 0.0268803466, margin 0.47e−7. -/
theorem entry_3_7 : (candidateMatrixQ 3 7 : ℝ) ≤ integralMatrix 3 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.1, kernel of display 3.22, page 15: `a_{4,9} = ∫_{2.9}^{3} Ξ₂(t; 2.5, 4.12, 3.56, 2.91, 2.50) dt ≥ 271881/10⁷`.
scipy value 0.0271881266, margin 0.27e−7. -/
theorem entry_3_8 : (candidateMatrixQ 3 8 : ℝ) ≤ integralMatrix 3 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,1} = ∫_{1}^{2.2} Ξ₁(t; 2.6, 3.58) dt ≥ 1594156/10⁷`.
scipy value 0.1594156990, margin 0.99e−7. -/
theorem entry_4_0 : (candidateMatrixQ 4 0 : ℝ) ≤ integralMatrix 4 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.6, 3.58) dt ≥ 238776/10⁷`.
scipy value 0.0238776167, margin 0.17e−7. -/
theorem entry_4_1 : (candidateMatrixQ 4 1 : ℝ) ≤ integralMatrix 4 1 := by
  exact entry_4_1_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.6, 3.58) dt ≥ 245310/10⁷`.
scipy value 0.0245310629, margin 0.63e−7. -/
theorem entry_4_2 : (candidateMatrixQ 4 2 : ℝ) ≤ integralMatrix 4 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.6, 3.58) dt ≥ 251066/10⁷`.
scipy value 0.0251066062, margin 0.06e−7. -/
theorem entry_4_3 : (candidateMatrixQ 4 3 : ℝ) ≤ integralMatrix 4 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.6, 3.58) dt ≥ 256142/10⁷`.
scipy value 0.0256142905, margin 0.91e−7. -/
theorem entry_4_4 : (candidateMatrixQ 4 4 : ℝ) ≤ integralMatrix 4 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.6, 3.58) dt ≥ 260625/10⁷`.
scipy value 0.0260625919, margin 0.92e−7. -/
theorem entry_4_5 : (candidateMatrixQ 4 5 : ℝ) ≤ integralMatrix 4 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.6, 3.58) dt ≥ 264587/10⁷`.
scipy value 0.0264587083, margin 0.08e−7. -/
theorem entry_4_6 : (candidateMatrixQ 4 6 : ℝ) ≤ integralMatrix 4 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.6, 3.58) dt ≥ 268087/10⁷`.
scipy value 0.0268087872, margin 0.87e−7. -/
theorem entry_4_7 : (candidateMatrixQ 4 7 : ℝ) ≤ integralMatrix 4 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,9} = ∫_{2.9}^{3} Ξ₁(t; 2.6, 3.58) dt ≥ 271181/10⁷`.
scipy value 0.0271181070, margin 0.07e−7. -/
theorem entry_4_8 : (candidateMatrixQ 4 8 : ℝ) ≤ integralMatrix 4 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,1} = ∫_{1}^{2.2} Ξ₁(t; 2.7, 3.47) dt ≥ 1602317/10⁷`.
scipy value 0.1602317488, margin 0.49e−7. -/
theorem entry_5_0 : (candidateMatrixQ 5 0 : ℝ) ≤ integralMatrix 5 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.7, 3.47) dt ≥ 234607/10⁷`.
scipy value 0.0234607924, margin 0.92e−7. -/
theorem entry_5_1 : (candidateMatrixQ 5 1 : ℝ) ≤ integralMatrix 5 1 := by
  exact entry_5_1_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.7, 3.47) dt ≥ 241272/10⁷`.
scipy value 0.0241272031, margin 0.03e−7. -/
theorem entry_5_2 : (candidateMatrixQ 5 2 : ℝ) ≤ integralMatrix 5 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.7, 3.47) dt ≥ 247145/10⁷`.
scipy value 0.0247145026, margin 0.03e−7. -/
theorem entry_5_3 : (candidateMatrixQ 5 3 : ℝ) ≤ integralMatrix 5 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.7, 3.47) dt ≥ 252328/10⁷`.
scipy value 0.0252328911, margin 0.91e−7. -/
theorem entry_5_4 : (candidateMatrixQ 5 4 : ℝ) ≤ integralMatrix 5 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.7, 3.47) dt ≥ 256909/10⁷`.
scipy value 0.0256909762, margin 0.76e−7. -/
theorem entry_5_5 : (candidateMatrixQ 5 5 : ℝ) ≤ integralMatrix 5 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.7, 3.47) dt ≥ 260960/10⁷`.
scipy value 0.0260960669, margin 0.67e−7. -/
theorem entry_5_6 : (candidateMatrixQ 5 6 : ℝ) ≤ integralMatrix 5 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.7, 3.47) dt ≥ 264544/10⁷`.
scipy value 0.0264544053, margin 0.05e−7. -/
theorem entry_5_7 : (candidateMatrixQ 5 7 : ℝ) ≤ integralMatrix 5 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,9} = ∫_{2.9}^{3} Ξ₁(t; 2.7, 3.47) dt ≥ 267713/10⁷`.
scipy value 0.0267713505, margin 0.50e−7. -/
theorem entry_5_8 : (candidateMatrixQ 5 8 : ℝ) ≤ integralMatrix 5 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,1} = ∫_{1}^{2.2} Ξ₁(t; 2.8, 3.34) dt ≥ 1649911/10⁷`.
scipy value 0.1649911916, margin 0.92e−7. -/
theorem entry_6_0 : (candidateMatrixQ 6 0 : ℝ) ≤ integralMatrix 6 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.8, 3.34) dt ≥ 233852/10⁷`.
scipy value 0.0233852365, margin 0.36e−7. -/
theorem entry_6_1 : (candidateMatrixQ 6 1 : ℝ) ≤ integralMatrix 6 1 := by
  exact entry_6_1_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.8, 3.34) dt ≥ 240539/10⁷`.
scipy value 0.0240539971, margin 0.97e−7. -/
theorem entry_6_2 : (candidateMatrixQ 6 2 : ℝ) ≤ integralMatrix 6 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.8, 3.34) dt ≥ 246434/10⁷`.
scipy value 0.0246434276, margin 0.28e−7. -/
theorem entry_6_3 : (candidateMatrixQ 6 3 : ℝ) ≤ integralMatrix 6 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.8, 3.34) dt ≥ 251637/10⁷`.
scipy value 0.0251637564, margin 0.56e−7. -/
theorem entry_6_4 : (candidateMatrixQ 6 4 : ℝ) ≤ integralMatrix 6 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.8, 3.34) dt ≥ 256236/10⁷`.
scipy value 0.0256236150, margin 0.15e−7. -/
theorem entry_6_5 : (candidateMatrixQ 6 5 : ℝ) ≤ integralMatrix 6 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.8, 3.34) dt ≥ 260303/10⁷`.
scipy value 0.0260303325, margin 0.32e−7. -/
theorem entry_6_6 : (candidateMatrixQ 6 6 : ℝ) ≤ integralMatrix 6 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.8, 3.34) dt ≥ 263901/10⁷`.
scipy value 0.0263901680, margin 0.68e−7. -/
theorem entry_6_7 : (candidateMatrixQ 6 7 : ℝ) ≤ integralMatrix 6 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,9} = ∫_{2.9}^{3} Ξ₁(t; 2.8, 3.34) dt ≥ 267084/10⁷`.
scipy value 0.0267084954, margin 0.95e−7. -/
theorem entry_6_8 : (candidateMatrixQ 6 8 : ℝ) ≤ integralMatrix 6 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,1} = ∫_{1}^{2.2} Ξ₁(t; 2.9, 3.19) dt ≥ 1737478/10⁷`.
scipy value 0.1737478561, margin 0.56e−7. -/
theorem entry_7_0 : (candidateMatrixQ 7 0 : ℝ) ≤ integralMatrix 7 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,2} = ∫_{2.2}^{2.3} Ξ₁(t; 2.9, 3.19) dt ≥ 236829/10⁷`.
scipy value 0.0236829970, margin 0.97e−7. -/
theorem entry_7_1 : (candidateMatrixQ 7 1 : ℝ) ≤ integralMatrix 7 1 := by
  exact entry_7_1_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,3} = ∫_{2.3}^{2.4} Ξ₁(t; 2.9, 3.19) dt ≥ 243424/10⁷`.
scipy value 0.0243424965, margin 0.96e−7. -/
theorem entry_7_2 : (candidateMatrixQ 7 2 : ℝ) ≤ integralMatrix 7 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.9, 3.19) dt ≥ 249235/10⁷`.
scipy value 0.0249235289, margin 0.29e−7. -/
theorem entry_7_3 : (candidateMatrixQ 7 3 : ℝ) ≤ integralMatrix 7 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.9, 3.19) dt ≥ 254362/10⁷`.
scipy value 0.0254362110, margin 0.11e−7. -/
theorem entry_7_4 : (candidateMatrixQ 7 4 : ℝ) ≤ integralMatrix 7 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.9, 3.19) dt ≥ 258890/10⁷`.
scipy value 0.0258890806, margin 0.81e−7. -/
theorem entry_7_5 : (candidateMatrixQ 7 5 : ℝ) ≤ integralMatrix 7 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,7} = ∫_{2.7}^{2.8} Ξ₁(t; 2.9, 3.19) dt ≥ 262893/10⁷`.
scipy value 0.0262893872, margin 0.87e−7. -/
theorem entry_7_6 : (candidateMatrixQ 7 6 : ℝ) ≤ integralMatrix 7 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,8} = ∫_{2.8}^{2.9} Ξ₁(t; 2.9, 3.19) dt ≥ 266433/10⁷`.
scipy value 0.0266433225, margin 0.23e−7. -/
theorem entry_7_7 : (candidateMatrixQ 7 7 : ℝ) ≤ integralMatrix 7 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,9} = ∫_{2.9}^{3} Ξ₁(t; 2.9, 3.19) dt ≥ 269562/10⁷`.
scipy value 0.0269562027, margin 0.03e−7. -/
theorem entry_7_8 : (candidateMatrixQ 7 8 : ℝ) ≤ integralMatrix 7 8 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,1} = ∫_{1}^{2.2} Ξ₁(t; 3.0, 3.00) dt ≥ 1910519/10⁷`.
scipy value 0.1910519781, margin 0.78e−7. -/
theorem entry_8_0 : (candidateMatrixQ 8 0 : ℝ) ≤ integralMatrix 8 0 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,2} = ∫_{2.2}^{2.3} Ξ₁(t; 3.0, 3.00) dt ≥ 246475/10⁷`.
scipy value 0.0246475178, margin 0.18e−7. -/
theorem entry_8_1 : (candidateMatrixQ 8 1 : ℝ) ≤ integralMatrix 8 1 := by
  exact entry_8_1_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,3} = ∫_{2.3}^{2.4} Ξ₁(t; 3.0, 3.00) dt ≥ 252770/10⁷`.
scipy value 0.0252770177, margin 0.18e−7. -/
theorem entry_8_2 : (candidateMatrixQ 8 2 : ℝ) ≤ integralMatrix 8 2 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,4} = ∫_{2.4}^{2.5} Ξ₁(t; 3.0, 3.00) dt ≥ 258308/10⁷`.
scipy value 0.0258308467, margin 0.47e−7. -/
theorem entry_8_3 : (candidateMatrixQ 8 3 : ℝ) ≤ integralMatrix 8 3 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,5} = ∫_{2.5}^{2.6} Ξ₁(t; 3.0, 3.00) dt ≥ 263187/10⁷`.
scipy value 0.0263187595, margin 0.60e−7. -/
theorem entry_8_4 : (candidateMatrixQ 8 4 : ℝ) ≤ integralMatrix 8 4 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,6} = ∫_{2.6}^{2.7} Ξ₁(t; 3.0, 3.00) dt ≥ 267489/10⁷`.
scipy value 0.0267489897, margin 0.90e−7. -/
theorem entry_8_5 : (candidateMatrixQ 8 5 : ℝ) ≤ integralMatrix 8 5 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,7} = ∫_{2.7}^{2.8} Ξ₁(t; 3.0, 3.00) dt ≥ 271285/10⁷`.
scipy value 0.0271285300, margin 0.30e−7. -/
theorem entry_8_6 : (candidateMatrixQ 8 6 : ℝ) ≤ integralMatrix 8 6 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,8} = ∫_{2.8}^{2.9} Ξ₁(t; 3.0, 3.00) dt ≥ 274633/10⁷`.
scipy value 0.0274633532, margin 0.53e−7. -/
theorem entry_8_7 : (candidateMatrixQ 8 7 : ℝ) ≤ integralMatrix 8 7 := by
  sorry

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,9} = ∫_{2.9}^{3} Ξ₁(t; 3.0, 3.00) dt ≥ 277585/10⁷`.
scipy value 0.0277585884, margin 0.88e−7. -/
theorem entry_8_8 : (candidateMatrixQ 8 8 : ℝ) ≤ integralMatrix 8 8 := by
  sorry

/-- **Displays 7.1 and 7.2 of Wu 2004, page 30**: the statement of the leaf
`Burst4Split.integral_matrix_bound`, proved from the 81 single entry statements.
CONDITIONAL ON the 81 LEAF entries. -/
theorem integral_matrix_bound_p3 : IntegralMatrixBound := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0
  · exact entry_0_1
  · exact entry_0_2
  · exact entry_0_3
  · exact entry_0_4
  · exact entry_0_5
  · exact entry_0_6
  · exact entry_0_7
  · exact entry_0_8
  · exact entry_1_0
  · exact entry_1_1
  · exact entry_1_2
  · exact entry_1_3
  · exact entry_1_4
  · exact entry_1_5
  · exact entry_1_6
  · exact entry_1_7
  · exact entry_1_8
  · exact entry_2_0
  · exact entry_2_1
  · exact entry_2_2
  · exact entry_2_3
  · exact entry_2_4
  · exact entry_2_5
  · exact entry_2_6
  · exact entry_2_7
  · exact entry_2_8
  · exact entry_3_0
  · exact entry_3_1
  · exact entry_3_2
  · exact entry_3_3
  · exact entry_3_4
  · exact entry_3_5
  · exact entry_3_6
  · exact entry_3_7
  · exact entry_3_8
  · exact entry_4_0
  · exact entry_4_1
  · exact entry_4_2
  · exact entry_4_3
  · exact entry_4_4
  · exact entry_4_5
  · exact entry_4_6
  · exact entry_4_7
  · exact entry_4_8
  · exact entry_5_0
  · exact entry_5_1
  · exact entry_5_2
  · exact entry_5_3
  · exact entry_5_4
  · exact entry_5_5
  · exact entry_5_6
  · exact entry_5_7
  · exact entry_5_8
  · exact entry_6_0
  · exact entry_6_1
  · exact entry_6_2
  · exact entry_6_3
  · exact entry_6_4
  · exact entry_6_5
  · exact entry_6_6
  · exact entry_6_7
  · exact entry_6_8
  · exact entry_7_0
  · exact entry_7_1
  · exact entry_7_2
  · exact entry_7_3
  · exact entry_7_4
  · exact entry_7_5
  · exact entry_7_6
  · exact entry_7_7
  · exact entry_7_8
  · exact entry_8_0
  · exact entry_8_1
  · exact entry_8_2
  · exact entry_8_3
  · exact entry_8_4
  · exact entry_8_5
  · exact entry_8_6
  · exact entry_8_7
  · exact entry_8_8

end LeanLab.ChenDoubleSieve.Burst9Matrix

