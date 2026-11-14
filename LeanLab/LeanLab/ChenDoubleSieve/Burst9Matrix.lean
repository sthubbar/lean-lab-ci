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

/-- `log ((t+2)/3) ≤ (t+1)/(t+2)` on `[11/5, 3]`: this is what makes `sigma0'`
increasing, i.e. `sigma0` convex. -/
private theorem log_shift_le3 {t : ℝ} (h1 : (11/5 : ℝ) ≤ t) (h2 : t ≤ 3) :
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

/-- `sigma0'' ≥ 0` on the interior of `[11/5, 3]`, i.e. `sigma0` is convex there. -/
private theorem sigma0_second_deriv_nonneg3 {t : ℝ} (h1 : (11/5 : ℝ) < t) (h2 : t < 3) :
    0 ≤ ((1 / (t + 2) * (t + 1) - log ((t + 2) / 3)) / (t + 1) ^ 2) /
        (1 - Wu04Integral.sigma 3 5 4) := by
  have ht1 : (0 : ℝ) < t + 1 := by linarith
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have hden : (0 : ℝ) < (t + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by positivity
  have hle := log_shift_le3 h1.le h2.le
  have hnum : 0 ≤ 1 / (t + 2) * (t + 1) - log ((t + 2) / 3) := by
    have h1' : 1 / (t + 2) * (t + 1) = (t + 1) / (t + 2) := by
      field_simp
    rw [h1']
    linarith
  refine div_nonneg ?_ hK.le
  refine div_nonneg hnum (by positivity)

/-- `sigma0` is convex on `[11/5, 3]`. -/
private theorem convexOn_sigma0_3 : ConvexOn ℝ (Set.Icc (11/5 : ℝ) (3)) Wu04Integral.sigma0 := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Icc (11/5 : ℝ) (3))
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
      have : x ∈ Set.Ioo (11/5 : ℝ) (3) := by rwa [interior_Icc] at hx
      linarith [this.1]
    exact (sigma0_hasDerivAt hx1 hK).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (11/5 : ℝ) (3) := by rwa [interior_Icc] at hx
    exact (hasDerivAt_sigma0' (by linarith [hx'.1]) hK).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (11/5 : ℝ) (3) := by rwa [interior_Icc] at hx
    exact sigma0_second_deriv_nonneg3 hx'.1 hx'.2

/-- Tangent lower bound: `sigma0 t ≥ sigma0 a + sigma0' a · (t - a)` on `[11/5, 3]`. -/
private theorem sigma0_tangent_le3 {a t : ℝ} (ha : (11/5 : ℝ) ≤ a) (ht : t ≤ 3)
    (hat : a ≤ t) :
    Wu04Integral.sigma0 a +
        ((log ((a + 2) / 3) / (a + 1)) / (1 - Wu04Integral.sigma 3 5 4)) * (t - a)
      ≤ Wu04Integral.sigma0 t := by
  have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
  have ha1 : (1 : ℝ) < a := by linarith
  rcases eq_or_lt_of_le hat with rfl | hlt
  · simp
  · have haD : a ∈ Set.Icc (11/5 : ℝ) (3) := ⟨ha, by linarith⟩
    have htD : t ∈ Set.Icc (11/5 : ℝ) (3) := ⟨by linarith, ht⟩
    have hslope := convexOn_sigma0_3.le_slope_of_hasDerivAt haD htD hlt
      (sigma0_hasDerivAt ha1 hK)
    rw [slope_def_field] at hslope
    have hpos : (0 : ℝ) < t - a := by linarith
    rw [le_div_iff₀ hpos] at hslope
    linarith

/-- **One panel of the `entry_7_1` quadrature.** On `[a,b] ⊆ [11/5, 3]`, any affine
lower bound `A + B(t-a)` for `sigma0` (from convexity, with `A ≤ sigma0 a` and `B ≤ sigma0' a`)
integrates explicitly against `1/(2t)`. -/
private theorem sigma0_panel_lower3 {a b A B : ℝ} (ha : (11/5 : ℝ) ≤ a)
    (hb : b ≤ 3) (hab : a ≤ b)
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
    have htt : t ≤ 3 := le_trans ht.2 hb
    have htan := sigma0_tangent_le3 ha htt ht1
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

/-- Second-order Taylor (tangent plus a quadratic correction) for `sigma0`, from convexity
of `s ↦ sigma0 s - C (s-a)^2` on the panel. -/
private theorem sigma0_taylor2_le3 {a C t : ℝ} (ha : (11/5 : ℝ) ≤ a) (ht : t ≤ 3)
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

/-- **Second-order panel bound**: with `2C ≤ sigma0''` on `[a,b]`, the quadratic
`A + B(t-a) + C(t-a)^2` integrates to a lower bound of `∫ sigma0 t/(2t)`. -/
private theorem sigma0_panel_lower2_c2 {a b A B C : ℝ} (ha : (11/5 : ℝ) ≤ a)
    (hb : b ≤ 3) (hab : a ≤ b)
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
    have htt : t ≤ 3 := le_trans ht.2 hb
    have htan := sigma0_taylor2_le3 ha htt ht.1 (fun s hs => hC s ⟨hs.1, le_trans hs.2 ht.2⟩)
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

/-- Two-sided enclosure of `log (431/100)`, from `log 43/10` and the ratio `431/430`. -/
private theorem log_431_100 :
    (1.460937904106 : ℝ) ≤ log ((431/100 : ℝ)) ∧ log ((431/100 : ℝ)) ≤ (1.460937904127 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (431/430 : ℝ))
    (x := (1/861 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0023228814161396 : ℝ) : ℝ) ≤ log (431/430) ∧
      log (431/430) ≤ ((0.0023228814161397 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((431/100 : ℝ)) = log ((43/10 : ℝ)) + log (431/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (431/430 : ℝ) = (431/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (108/25)`, from `log 43/10` and the ratio `216/215`. -/
private theorem log_108_25 :
    (1.463255402246 : ℝ) ≤ log ((108/25 : ℝ)) ∧ log ((108/25 : ℝ)) ≤ (1.463255402267 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (216/215 : ℝ))
    (x := (1/431 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0046403795565022 : ℝ) : ℝ) ≤ log (216/215) ∧
      log (216/215) ≤ ((0.0046403795565023 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((108/25 : ℝ)) = log ((43/10 : ℝ)) + log (216/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (216/215 : ℝ) = (108/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (433/100)`, from `log 43/10` and the ratio `433/430`. -/
private theorem log_433_100 :
    (1.465567542004 : ℝ) ≤ log ((433/100 : ℝ)) ∧ log ((433/100 : ℝ)) ≤ (1.465567542025 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (433/430 : ℝ))
    (x := (3/863 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0069525193148817 : ℝ) : ℝ) ≤ log (433/430) ∧
      log (433/430) ≤ ((0.0069525193148818 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((433/100 : ℝ)) = log ((43/10 : ℝ)) + log (433/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (433/430 : ℝ) = (433/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (217/50)`, from `log 43/10` and the ratio `217/215`. -/
private theorem log_217_50 :
    (1.467874348102 : ℝ) ≤ log ((217/50 : ℝ)) ∧ log ((217/50 : ℝ)) ≤ (1.467874348123 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (217/215 : ℝ))
    (x := (1/216 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0092593254127967 : ℝ) : ℝ) ≤ log (217/215) ∧
      log (217/215) ≤ ((0.0092593254127969 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((217/50 : ℝ)) = log ((43/10 : ℝ)) + log (217/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (217/215 : ℝ) = (217/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (87/20)`, from `log 43/10` and the ratio `87/86`. -/
private theorem log_87_20 :
    (1.470175845091 : ℝ) ≤ log ((87/20 : ℝ)) ∧ log ((87/20 : ℝ)) ≤ (1.470175845112 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (87/86 : ℝ))
    (x := (1/173 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0115608224010759 : ℝ) : ℝ) ≤ log (87/86) ∧
      log (87/86) ≤ ((0.0115608224010764 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((87/20 : ℝ)) = log ((43/10 : ℝ)) + log (87/86) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (87/86 : ℝ) = (87/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (109/25)`, from `log 43/10` and the ratio `218/215`. -/
private theorem log_109_25 :
    (1.472472057351 : ℝ) ≤ log ((109/25 : ℝ)) ∧ log ((109/25 : ℝ)) ≤ (1.472472057372 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (218/215 : ℝ))
    (x := (3/433 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0138570346614259 : ℝ) : ℝ) ≤ log (218/215) ∧
      log (218/215) ≤ ((0.0138570346614276 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((109/25 : ℝ)) = log ((43/10 : ℝ)) + log (218/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (218/215 : ℝ) = (109/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (437/100)`, from `log 43/10` and the ratio `437/430`. -/
private theorem log_437_100 :
    (1.474763009097 : ℝ) ≤ log ((437/100 : ℝ)) ∧ log ((437/100 : ℝ)) ≤ (1.474763009118 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (437/430 : ℝ))
    (x := (7/867 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0161479864079814 : ℝ) : ℝ) ≤ log (437/430) ∧
      log (437/430) ≤ ((0.0161479864079859 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((437/100 : ℝ)) = log ((43/10 : ℝ)) + log (437/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (437/430 : ℝ) = (437/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (219/50)`, from `log 43/10` and the ratio `219/215`. -/
private theorem log_219_50 :
    (1.477048724378 : ℝ) ≤ log ((219/50 : ℝ)) ∧ log ((219/50 : ℝ)) ≤ (1.477048724399 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (219/215 : ℝ))
    (x := (2/217 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0184337016888364 : ℝ) : ℝ) ≤ log (219/215) ∧
      log (219/215) ≤ ((0.0184337016888478 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((219/50 : ℝ)) = log ((43/10 : ℝ)) + log (219/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (219/215 : ℝ) = (219/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (439/100)`, from `log 43/10` and the ratio `439/430`. -/
private theorem log_439_100 :
    (1.479329227077 : ℝ) ≤ log ((439/100 : ℝ)) ∧ log ((439/100 : ℝ)) ≤ (1.479329227098 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (439/430 : ℝ))
    (x := (9/869 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0207142043875595 : ℝ) : ℝ) ≤ log (439/430) ∧
      log (439/430) ≤ ((0.0207142043875852 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((439/100 : ℝ)) = log ((43/10 : ℝ)) + log (439/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (439/430 : ℝ) = (439/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (331/100)`, from `log 33/10` and the ratio `331/330`. -/
private theorem log_331_100 :
    (1.196948189386 : ℝ) ≤ log ((331/100 : ℝ)) ∧ log ((331/100 : ℝ)) ≤ (1.196948189397 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (331/330 : ℝ))
    (x := (1/661 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0030257209165369 : ℝ) : ℝ) ≤ log (331/330) ∧
      log (331/330) ≤ ((0.003025720916537 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((331/100 : ℝ)) = log ((33/10 : ℝ)) + log (331/330) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (331/330 : ℝ) = (331/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (83/25)`, from `log 33/10` and the ratio `166/165`. -/
private theorem log_83_25 :
    (1.199964782925 : ℝ) ≤ log ((83/25 : ℝ)) ∧ log ((83/25 : ℝ)) ≤ (1.199964782936 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (166/165 : ℝ))
    (x := (1/331 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0060423144559626 : ℝ) : ℝ) ≤ log (166/165) ∧
      log (166/165) ≤ ((0.0060423144559627 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((83/25 : ℝ)) = log ((33/10 : ℝ)) + log (166/165) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (166/165 : ℝ) = (83/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (333/100)`, from `log 33/10` and the ratio `111/110`. -/
private theorem log_333_100 :
    (1.202972303989 : ℝ) ≤ log ((333/100 : ℝ)) ∧ log ((333/100 : ℝ)) ≤ (1.202972304 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (111/110 : ℝ))
    (x := (1/221 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0090498355199178 : ℝ) : ℝ) ≤ log (111/110) ∧
      log (111/110) ≤ ((0.009049835519918 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((333/100 : ℝ)) = log ((33/10 : ℝ)) + log (111/110) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (111/110 : ℝ) = (333/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (167/50)`, from `log 33/10` and the ratio `167/165`. -/
private theorem log_167_50 :
    (1.205970806986 : ℝ) ≤ log ((167/50 : ℝ)) ∧ log ((167/50 : ℝ)) ≤ (1.205970806997 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (167/165 : ℝ))
    (x := (1/166 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0120483385161744 : ℝ) : ℝ) ≤ log (167/165) ∧
      log (167/165) ≤ ((0.012048338516175 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((167/50 : ℝ)) = log ((33/10 : ℝ)) + log (167/165) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (167/165 : ℝ) = (167/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (67/20)`, from `log 33/10` and the ratio `67/66`. -/
private theorem log_67_20 :
    (1.208960345834 : ℝ) ≤ log ((67/20 : ℝ)) ∧ log ((67/20 : ℝ)) ≤ (1.208960345845 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (67/66 : ℝ))
    (x := (1/133 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0150378773645401 : ℝ) : ℝ) ≤ log (67/66) ∧
      log (67/66) ≤ ((0.0150378773645429 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((67/20 : ℝ)) = log ((33/10 : ℝ)) + log (67/66) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (67/66 : ℝ) = (67/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (84/25)`, from `log 33/10` and the ratio `56/55`. -/
private theorem log_84_25 :
    (1.211940973972 : ℝ) ≤ log ((84/25 : ℝ)) ∧ log ((84/25 : ℝ)) ≤ (1.211940973983 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (56/55 : ℝ))
    (x := (1/111 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0180185055026769 : ℝ) : ℝ) ≤ log (56/55) ∧
      log (56/55) ≤ ((0.0180185055026866 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((84/25 : ℝ)) = log ((33/10 : ℝ)) + log (56/55) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (56/55 : ℝ) = (84/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (337/100)`, from `log 33/10` and the ratio `337/330`. -/
private theorem log_337_100 :
    (1.214912744361 : ℝ) ≤ log ((337/100 : ℝ)) ∧ log ((337/100 : ℝ)) ≤ (1.214912744372 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (337/330 : ℝ))
    (x := (7/667 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0209902758918317 : ℝ) : ℝ) ≤ log (337/330) ∧
      log (337/330) ≤ ((0.0209902758918599 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((337/100 : ℝ)) = log ((33/10 : ℝ)) + log (337/330) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (337/330 : ℝ) = (337/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (169/50)`, from `log 33/10` and the ratio `169/165`. -/
private theorem log_169_50 :
    (1.217875709492 : ℝ) ≤ log ((169/50 : ℝ)) ∧ log ((169/50 : ℝ)) ≤ (1.217875709503 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (169/165 : ℝ))
    (x := (2/167 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0239532410224827 : ℝ) : ℝ) ≤ log (169/165) ∧
      log (169/165) ≤ ((0.0239532410225535 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((169/50 : ℝ)) = log ((33/10 : ℝ)) + log (169/165) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (169/165 : ℝ) = (169/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (339/100)`, from `log 33/10` and the ratio `113/110`. -/
private theorem log_339_100 :
    (1.220829921389 : ℝ) ≤ log ((339/100 : ℝ)) ∧ log ((339/100 : ℝ)) ≤ (1.220829921401 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (113/110 : ℝ))
    (x := (3/223 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0269074529199015 : ℝ) : ℝ) ≤ log (113/110) ∧
      log (113/110) ≤ ((0.0269074529200611 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((339/100 : ℝ)) = log ((33/10 : ℝ)) + log (113/110) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (113/110 : ℝ) = (339/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (22/5)`, from `log 43/10` and the ratio `44/43`. -/
private theorem log_22_5 :
    (1.481604540914 : ℝ) ≤ log ((22/5 : ℝ)) ∧ log ((22/5 : ℝ)) ≤ (1.481604540935 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (44/43 : ℝ))
    (x := (1/87 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0229895182246911 : ℝ) : ℝ) ≤ log (44/43) ∧
      log (44/43) ≤ ((0.0229895182247442 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((22/5 : ℝ)) = log ((43/10 : ℝ)) + log (44/43) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (44/43 : ℝ) = (22/5 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (24/23)` from the atanh series. -/
private theorem log_24_23 :
    (0.04255961441879 : ℝ) ≤ log ((24/23 : ℝ)) ∧ log ((24/23 : ℝ)) ≤ (0.0425596144188 : ℝ) := by
  have h := log_enclosure (y := (24/23 : ℝ))
    (x := (1/47 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 4
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (231/230)` from the atanh series. -/
private theorem log_231_230 :
    (0.00433840159859 : ℝ) ≤ log ((231/230 : ℝ)) ∧ log ((231/230 : ℝ)) ≤ (0.0043384015986 : ℝ) := by
  have h := log_enclosure (y := (231/230 : ℝ))
    (x := (1/461 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (232/231)` from the atanh series. -/
private theorem log_232_231 :
    (0.00431966114451 : ℝ) ≤ log ((232/231 : ℝ)) ∧ log ((232/231 : ℝ)) ≤ (0.00431966114452 : ℝ) := by
  have h := log_enclosure (y := (232/231 : ℝ))
    (x := (1/463 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (233/232)` from the atanh series. -/
private theorem log_233_232 :
    (0.00430108189939 : ℝ) ≤ log ((233/232 : ℝ)) ∧ log ((233/232 : ℝ)) ≤ (0.0043010818994 : ℝ) := by
  have h := log_enclosure (y := (233/232 : ℝ))
    (x := (1/465 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (234/233)` from the atanh series. -/
private theorem log_234_233 :
    (0.004282661792 : ℝ) ≤ log ((234/233 : ℝ)) ∧ log ((234/233 : ℝ)) ≤ (0.00428266179201 : ℝ) := by
  have h := log_enclosure (y := (234/233 : ℝ))
    (x := (1/467 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (235/234)` from the atanh series. -/
private theorem log_235_234 :
    (0.00426439878645 : ℝ) ≤ log ((235/234 : ℝ)) ∧ log ((235/234 : ℝ)) ≤ (0.00426439878646 : ℝ) := by
  have h := log_enclosure (y := (235/234 : ℝ))
    (x := (1/469 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (236/235)` from the atanh series. -/
private theorem log_236_235 :
    (0.00424629088145 : ℝ) ≤ log ((236/235 : ℝ)) ∧ log ((236/235 : ℝ)) ≤ (0.00424629088146 : ℝ) := by
  have h := log_enclosure (y := (236/235 : ℝ))
    (x := (1/471 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (237/236)` from the atanh series. -/
private theorem log_237_236 :
    (0.00422833610952 : ℝ) ≤ log ((237/236 : ℝ)) ∧ log ((237/236 : ℝ)) ≤ (0.00422833610953 : ℝ) := by
  have h := log_enclosure (y := (237/236 : ℝ))
    (x := (1/473 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (238/237)` from the atanh series. -/
private theorem log_238_237 :
    (0.00421053253634 : ℝ) ≤ log ((238/237 : ℝ)) ∧ log ((238/237 : ℝ)) ≤ (0.00421053253635 : ℝ) := by
  have h := log_enclosure (y := (238/237 : ℝ))
    (x := (1/475 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (239/238)` from the atanh series. -/
private theorem log_239_238 :
    (0.00419287826003 : ℝ) ≤ log ((239/238 : ℝ)) ∧ log ((239/238 : ℝ)) ≤ (0.00419287826004 : ℝ) := by
  have h := log_enclosure (y := (239/238 : ℝ))
    (x := (1/477 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (240/239)` from the atanh series. -/
private theorem log_240_239 :
    (0.00417537141048 : ℝ) ≤ log ((240/239 : ℝ)) ∧ log ((240/239 : ℝ)) ≤ (0.00417537141049 : ℝ) := by
  have h := log_enclosure (y := (240/239 : ℝ))
    (x := (1/479 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `sigma 3 (431/100) (331/100)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_431_100 :
    (0.089125145622 : ℝ) ≤ Wu04Integral.sigma 3 ((431/100 : ℝ)) ((331/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (431/100 : ℝ)) (c := (331/100 : ℝ)) (m := (531/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((431/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((431/100 : ℝ)) - 1) = (331/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (331/100 : ℝ)) (m := (531/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.362325615436 : ℝ) ≤ log ((431/100 : ℝ)) - log 3 := by
    linarith [log_431_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((331/100 : ℝ)) := by linarith [log_331_100.1]
  have hp : (0 : ℝ) ≤ (0.362325615436 : ℝ) := by norm_num
  have hlo' : (0.43368498936428833296 : ℝ) ≤ log ((331/100 : ℝ)) * (log ((431/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_331_100.1 hdiff_lo hp hq
    have hc : (0.43368498936428833296 : ℝ) ≤ (1.196948189386 : ℝ) * (0.362325615436 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_331_100.1, log_331_100.2, log_431_100.1, log_431_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((231/100 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_231_100 :
    (0.107599223809 : ℝ) ≤ Wu04Integral.sigma0 ((231/100 : ℝ)) := by
  have h := sigma_c2_431_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((231/100 : ℝ)) + 2 = (431/100 : ℝ) by norm_num, show ((231/100 : ℝ)) + 1 = (331/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.107599223809 : ℝ) : ℝ) ≤ ((0.089125145622 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.089125145622 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (108/25) (83/25)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_432_100 :
    (0.090221628803 : ℝ) ≤ Wu04Integral.sigma 3 ((108/25 : ℝ)) ((83/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (108/25 : ℝ)) (c := (83/25 : ℝ)) (m := (133/50 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((108/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((108/25 : ℝ)) - 1) = (83/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (83/25 : ℝ)) (m := (133/50 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.364643113576 : ℝ) ≤ log ((108/25 : ℝ)) - log 3 := by
    linarith [log_108_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((83/25 : ℝ)) := by linarith [log_83_25.1]
  have hp : (0 : ℝ) ≤ (0.364643113576 : ℝ) := by norm_num
  have hlo' : (0.43755889462732096048 : ℝ) ≤ log ((83/25 : ℝ)) * (log ((108/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_83_25.1 hdiff_lo hp hq
    have hc : (0.43755889462732096048 : ℝ) ≤ (1.199964782925 : ℝ) * (0.364643113576 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_83_25.1, log_83_25.2, log_108_25.1, log_108_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((58/25 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_232_100 :
    (0.108922988705 : ℝ) ≤ Wu04Integral.sigma0 ((58/25 : ℝ)) := by
  have h := sigma_c2_432_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((58/25 : ℝ)) + 2 = (108/25 : ℝ) by norm_num, show ((58/25 : ℝ)) + 1 = (83/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.108922988705 : ℝ) : ℝ) ≤ ((0.090221628803 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.090221628803 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (433/100) (333/100)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_433_100 :
    (0.091321776087 : ℝ) ≤ Wu04Integral.sigma 3 ((433/100 : ℝ)) ((333/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (433/100 : ℝ)) (c := (333/100 : ℝ)) (m := (533/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((433/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((433/100 : ℝ)) - 1) = (333/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (333/100 : ℝ)) (m := (533/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.366955253334 : ℝ) ≤ log ((433/100 : ℝ)) - log 3 := by
    linarith [log_433_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((333/100 : ℝ)) := by linarith [log_333_100.1]
  have hp : (0 : ℝ) ≤ (0.366955253334 : ℝ) := by norm_num
  have hlo' : (0.44143700656406915374 : ℝ) ≤ log ((333/100 : ℝ)) * (log ((433/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_333_100.1 hdiff_lo hp hq
    have hc : (0.44143700656406915374 : ℝ) ≤ (1.202972303989 : ℝ) * (0.366955253334 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_333_100.1, log_333_100.2, log_433_100.1, log_433_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((233/100 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_233_100 :
    (0.110251177209 : ℝ) ≤ Wu04Integral.sigma0 ((233/100 : ℝ)) := by
  have h := sigma_c2_433_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((233/100 : ℝ)) + 2 = (433/100 : ℝ) by norm_num, show ((233/100 : ℝ)) + 1 = (333/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.110251177209 : ℝ) : ℝ) ≤ ((0.091321776087 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.091321776087 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (217/50) (167/50)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_434_100 :
    (0.092425549467 : ℝ) ≤ Wu04Integral.sigma 3 ((217/50 : ℝ)) ((167/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (217/50 : ℝ)) (c := (167/50 : ℝ)) (m := (267/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((217/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((217/50 : ℝ)) - 1) = (167/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (167/50 : ℝ)) (m := (267/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.369262059432 : ℝ) ≤ log ((217/50 : ℝ)) - log 3 := by
    linarith [log_217_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((167/50 : ℝ)) := by linarith [log_167_50.1]
  have hp : (0 : ℝ) ≤ (0.369262059432 : ℝ) := by norm_num
  have hlo' : (0.44531926380252133279 : ℝ) ≤ log ((167/50 : ℝ)) * (log ((217/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_167_50.1 hdiff_lo hp hq
    have hc : (0.44531926380252133279 : ℝ) ≤ (1.205970806986 : ℝ) * (0.369262059432 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_167_50.1, log_167_50.2, log_217_50.1, log_217_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((117/50 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_234_100 :
    (0.111583743436 : ℝ) ≤ Wu04Integral.sigma0 ((117/50 : ℝ)) := by
  have h := sigma_c2_434_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((117/50 : ℝ)) + 2 = (217/50 : ℝ) by norm_num, show ((117/50 : ℝ)) + 1 = (167/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.111583743436 : ℝ) : ℝ) ≤ ((0.092425549467 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.092425549467 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (87/20) (67/20)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_435_100 :
    (0.093532911351 : ℝ) ≤ Wu04Integral.sigma 3 ((87/20 : ℝ)) ((67/20 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (87/20 : ℝ)) (c := (67/20 : ℝ)) (m := (107/40 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((87/20 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((87/20 : ℝ)) - 1) = (67/20 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (67/20 : ℝ)) (m := (107/40 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.371563556421 : ℝ) ≤ log ((87/20 : ℝ)) - log 3 := by
    linarith [log_87_20.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((67/20 : ℝ)) := by linarith [log_67_20.1]
  have hp : (0 : ℝ) ≤ (0.371563556421 : ℝ) := by norm_num
  have hlo' : (0.4492056056700431313 : ℝ) ≤ log ((67/20 : ℝ)) * (log ((87/20 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_67_20.1 hdiff_lo hp hq
    have hc : (0.4492056056700431313 : ℝ) ≤ (1.208960345834 : ℝ) * (0.371563556421 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_67_20.1, log_67_20.2, log_87_20.1, log_87_20.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((47/20 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_235_100 :
    (0.112920641999 : ℝ) ≤ Wu04Integral.sigma0 ((47/20 : ℝ)) := by
  have h := sigma_c2_435_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((47/20 : ℝ)) + 2 = (87/20 : ℝ) by norm_num, show ((47/20 : ℝ)) + 1 = (67/20 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.112920641999 : ℝ) : ℝ) ≤ ((0.093532911351 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.093532911351 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (109/25) (84/25)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_436_100 :
    (0.094643824551 : ℝ) ≤ Wu04Integral.sigma 3 ((109/25 : ℝ)) ((84/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (109/25 : ℝ)) (c := (84/25 : ℝ)) (m := (67/25 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((109/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((109/25 : ℝ)) - 1) = (84/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (84/25 : ℝ)) (m := (67/25 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.373859768681 : ℝ) ≤ log ((109/25 : ℝ)) - log 3 := by
    linarith [log_109_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((84/25 : ℝ)) := by linarith [log_84_25.1]
  have hp : (0 : ℝ) ≤ (0.373859768681 : ℝ) := by norm_num
  have hlo' : (0.45309597218419776177 : ℝ) ≤ log ((84/25 : ℝ)) * (log ((109/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_84_25.1 hdiff_lo hp hq
    have hc : (0.45309597218419776177 : ℝ) ≤ (1.211940973972 : ℝ) * (0.373859768681 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_84_25.1, log_84_25.2, log_109_25.1, log_109_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((59/25 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_236_100 :
    (0.114261828005 : ℝ) ≤ Wu04Integral.sigma0 ((59/25 : ℝ)) := by
  have h := sigma_c2_436_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((59/25 : ℝ)) + 2 = (109/25 : ℝ) by norm_num, show ((59/25 : ℝ)) + 1 = (84/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.114261828005 : ℝ) : ℝ) ≤ ((0.094643824551 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.094643824551 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (437/100) (337/100)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_437_100 :
    (0.095758252287 : ℝ) ≤ Wu04Integral.sigma 3 ((437/100 : ℝ)) ((337/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (437/100 : ℝ)) (c := (337/100 : ℝ)) (m := (537/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((437/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((437/100 : ℝ)) - 1) = (337/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (337/100 : ℝ)) (m := (537/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.376150720427 : ℝ) ≤ log ((437/100 : ℝ)) - log 3 := by
    linarith [log_437_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((337/100 : ℝ)) := by linarith [log_337_100.1]
  have hp : (0 : ℝ) ≤ (0.376150720427 : ℝ) := by norm_num
  have hlo' : (0.45699030404733383176 : ℝ) ≤ log ((337/100 : ℝ)) * (log ((437/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_337_100.1 hdiff_lo hp hq
    have hc : (0.45699030404733383176 : ℝ) ≤ (1.214912744361 : ℝ) * (0.376150720427 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_337_100.1, log_337_100.2, log_437_100.1, log_437_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((237/100 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_237_100 :
    (0.115607257048 : ℝ) ≤ Wu04Integral.sigma0 ((237/100 : ℝ)) := by
  have h := sigma_c2_437_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((237/100 : ℝ)) + 2 = (437/100 : ℝ) by norm_num, show ((237/100 : ℝ)) + 1 = (337/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.115607257048 : ℝ) : ℝ) ≤ ((0.095758252287 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.095758252287 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (219/50) (169/50)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_438_100 :
    (0.096876158178 : ℝ) ≤ Wu04Integral.sigma 3 ((219/50 : ℝ)) ((169/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (219/50 : ℝ)) (c := (169/50 : ℝ)) (m := (269/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((219/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((219/50 : ℝ)) - 1) = (169/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (169/50 : ℝ)) (m := (269/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.378436435708 : ℝ) ≤ log ((219/50 : ℝ)) - log 3 := by
    linarith [log_219_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((169/50 : ℝ)) := by linarith [log_169_50.1]
  have hp : (0 : ℝ) ≤ (0.378436435708 : ℝ) := by norm_num
  have hlo' : (0.46088854263550414334 : ℝ) ≤ log ((169/50 : ℝ)) * (log ((219/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_169_50.1 hdiff_lo hp hq
    have hc : (0.46088854263550414334 : ℝ) ≤ (1.217875709492 : ℝ) * (0.378436435708 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_169_50.1, log_169_50.2, log_219_50.1, log_219_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((119/50 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_238_100 :
    (0.116956885206 : ℝ) ≤ Wu04Integral.sigma0 ((119/50 : ℝ)) := by
  have h := sigma_c2_438_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((119/50 : ℝ)) + 2 = (219/50 : ℝ) by norm_num, show ((119/50 : ℝ)) + 1 = (169/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.116956885206 : ℝ) : ℝ) ≤ ((0.096876158178 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.096876158178 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (439/100) (339/100)` at the left end of a `[23/10, 12/5]` panel of `entry_i_2`. -/
private theorem sigma_c2_439_100 :
    (0.097997506232 : ℝ) ≤ Wu04Integral.sigma 3 ((439/100 : ℝ)) ((339/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (439/100 : ℝ)) (c := (339/100 : ℝ)) (m := (539/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((439/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((439/100 : ℝ)) - 1) = (339/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (339/100 : ℝ)) (m := (539/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.380716938407 : ℝ) ≤ log ((439/100 : ℝ)) - log 3 := by
    linarith [log_439_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((339/100 : ℝ)) := by linarith [log_339_100.1]
  have hp : (0 : ℝ) ≤ (0.380716938407 : ℝ) := by norm_num
  have hlo' : (0.46479062998687856488 : ℝ) ≤ log ((339/100 : ℝ)) * (log ((439/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_339_100.1 hdiff_lo hp hq
    have hc : (0.46479062998687856488 : ℝ) ≤ (1.220829921389 : ℝ) * (0.380716938407 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_339_100.1, log_339_100.2, log_439_100.1, log_439_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((239/100 : ℝ))` at a `[23/10, 12/5]` panel endpoint. -/
private theorem sigma0_c2_239_100 :
    (0.118310669028 : ℝ) ≤ Wu04Integral.sigma0 ((239/100 : ℝ)) := by
  have h := sigma_c2_439_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((239/100 : ℝ)) + 2 = (439/100 : ℝ) by norm_num, show ((239/100 : ℝ)) + 1 = (339/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.118310669028 : ℝ) : ℝ) ≤ ((0.097997506232 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.097997506232 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
/-- Lower bound of `sigma0' ((231/100 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_231_100 :
    (0.1321538837 : ℝ) ≤
      (log (((231/100 : ℝ) + 2) / 3) / ((231/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_431_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.362325615436 : ℝ) ≤ log ((431/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((231/100 : ℝ) + 2) / 3) = ((431/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1321538837 : ℝ)
      ≤ (0.362325615436 : ℝ) / (((231/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((431/100 : ℝ)) - log 3) / (((231/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((431/100 : ℝ)) - log 3) / (((231/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((58/25 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_232_100 :
    (0.1325985632 : ℝ) ≤
      (log (((58/25 : ℝ) + 2) / 3) / ((58/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_108_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.364643113576 : ℝ) ≤ log ((108/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((58/25 : ℝ) + 2) / 3) = ((108/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1325985632 : ℝ)
      ≤ (0.364643113576 : ℝ) / (((58/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((108/25 : ℝ)) - log 3) / (((58/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((108/25 : ℝ)) - log 3) / (((58/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((233/100 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_233_100 :
    (0.1330386293 : ℝ) ≤
      (log (((233/100 : ℝ) + 2) / 3) / ((233/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_433_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.366955253334 : ℝ) ≤ log ((433/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((233/100 : ℝ) + 2) / 3) = ((433/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1330386293 : ℝ)
      ≤ (0.366955253334 : ℝ) / (((233/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((433/100 : ℝ)) - log 3) / (((233/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((433/100 : ℝ)) - log 3) / (((233/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((117/50 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_234_100 :
    (0.1334741324 : ℝ) ≤
      (log (((117/50 : ℝ) + 2) / 3) / ((117/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_217_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.369262059432 : ℝ) ≤ log ((217/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((117/50 : ℝ) + 2) / 3) = ((217/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1334741324 : ℝ)
      ≤ (0.369262059432 : ℝ) / (((117/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((217/50 : ℝ)) - log 3) / (((117/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((217/50 : ℝ)) - log 3) / (((117/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((47/20 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_235_100 :
    (0.1339051221 : ℝ) ≤
      (log (((47/20 : ℝ) + 2) / 3) / ((47/20 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_87_20
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.371563556421 : ℝ) ≤ log ((87/20 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((47/20 : ℝ) + 2) / 3) = ((87/20 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1339051221 : ℝ)
      ≤ (0.371563556421 : ℝ) / (((47/20 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((87/20 : ℝ)) - log 3) / (((47/20 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((87/20 : ℝ)) - log 3) / (((47/20 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((59/25 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_236_100 :
    (0.1343316476 : ℝ) ≤
      (log (((59/25 : ℝ) + 2) / 3) / ((59/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_109_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.373859768681 : ℝ) ≤ log ((109/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((59/25 : ℝ) + 2) / 3) = ((109/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1343316476 : ℝ)
      ≤ (0.373859768681 : ℝ) / (((59/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((109/25 : ℝ)) - log 3) / (((59/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((109/25 : ℝ)) - log 3) / (((59/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((237/100 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_237_100 :
    (0.1347537572 : ℝ) ≤
      (log (((237/100 : ℝ) + 2) / 3) / ((237/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_437_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.376150720427 : ℝ) ≤ log ((437/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((237/100 : ℝ) + 2) / 3) = ((437/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1347537572 : ℝ)
      ≤ (0.376150720427 : ℝ) / (((237/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((437/100 : ℝ)) - log 3) / (((237/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((437/100 : ℝ)) - log 3) / (((237/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((119/50 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_238_100 :
    (0.1351714987 : ℝ) ≤
      (log (((119/50 : ℝ) + 2) / 3) / ((119/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_219_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.378436435708 : ℝ) ≤ log ((219/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((119/50 : ℝ) + 2) / 3) = ((219/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1351714987 : ℝ)
      ≤ (0.378436435708 : ℝ) / (((119/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((219/50 : ℝ)) - log 3) / (((119/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((219/50 : ℝ)) - log 3) / (((119/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((239/100 : ℝ))`, the tangent slope of a `[23/10, 12/5]` panel. -/
private theorem sigma0_deriv_lower_c2_239_100 :
    (0.1355849193 : ℝ) ≤
      (log (((239/100 : ℝ) + 2) / 3) / ((239/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_439_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.380716938407 : ℝ) ≤ log ((439/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((239/100 : ℝ) + 2) / 3) = ((439/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1355849193 : ℝ)
      ≤ (0.380716938407 : ℝ) / (((239/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((439/100 : ℝ)) - log 3) / (((239/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((439/100 : ℝ)) - log 3) / (((239/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Second-order panel 0 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_0 :
    (0.0002319715346656 : ℝ) ≤ ∫ t in (23/10 : ℝ)..(231/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (23/10 : ℝ)) (b := (231/100 : ℝ)) (A := (0.10627992 : ℝ))
    (B := (0.1317045397 : ℝ)) (C := (0.02232043022549 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_panel_23_10.1) (sigma0_deriv_lower_23_10)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.460937904127 : ℝ) := by
        have hle : s + 2 ≤ (431/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_431_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.460937904127 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((23/10 : ℝ) + 2) * ((23/10 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((23/10 : ℝ) + 2) * ((23/10 : ℝ) + 1) = ((23/10 : ℝ) + 1) / ((23/10 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.40511624499811627906 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((331/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((331/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (331/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02232043022549 : ℝ))) ≤ (0.40511624499811627906 : ℝ) / (((331/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.40511624499811627906 : ℝ) / (((331/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.40511624499811627906 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.40511624499811627906 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_231_230
  rw [show ((231/100 : ℝ)) / ((23/10 : ℝ)) = (231/230 : ℝ) by norm_num] at hp
  have hX : ((0.10627992 : ℝ) - (0.1317045397 : ℝ) * (23/10 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.10627992 : ℝ) - (0.1317045397 : ℝ) * (23/10 : ℝ)) * log (231/230) ≥
      (((0.10627992 : ℝ) - (0.1317045397 : ℝ) * (23/10 : ℝ))) * (0.0043384015986 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02232043022549 : ℝ) * (23/10 : ℝ) ^ 2) * log (231/230) ≥
      ((0.02232043022549 : ℝ) * (23/10 : ℝ) ^ 2) * (0.00433840159859 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 1 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_1 :
    (0.0002338238042097 : ℝ) ≤ ∫ t in (231/100 : ℝ)..(58/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (231/100 : ℝ)) (b := (58/25 : ℝ)) (A := (0.107599223809 : ℝ))
    (B := (0.1321538837 : ℝ)) (C := (0.02208880459209 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_231_100) (sigma0_deriv_lower_c2_231_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.463255402267 : ℝ) := by
        have hle : s + 2 ≤ (108/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_108_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.463255402267 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((231/100 : ℝ) + 2) * ((231/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((231/100 : ℝ) + 2) * ((231/100 : ℝ) + 1) = ((231/100 : ℝ) + 1) / ((231/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.40333832490808120649 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((83/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((83/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (83/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02208880459209 : ℝ))) ≤ (0.40333832490808120649 : ℝ) / (((83/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.40333832490808120649 : ℝ) / (((83/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.40333832490808120649 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.40333832490808120649 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_232_231
  rw [show ((58/25 : ℝ)) / ((231/100 : ℝ)) = (232/231 : ℝ) by norm_num] at hp
  have hX : ((0.107599223809 : ℝ) - (0.1321538837 : ℝ) * (231/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.107599223809 : ℝ) - (0.1321538837 : ℝ) * (231/100 : ℝ)) * log (232/231) ≥
      (((0.107599223809 : ℝ) - (0.1321538837 : ℝ) * (231/100 : ℝ))) * (0.00431966114452 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02208880459209 : ℝ) * (231/100 : ℝ) ^ 2) * log (232/231) ≥
      ((0.02208880459209 : ℝ) * (231/100 : ℝ) ^ 2) * (0.00431966114451 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 2 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_2 :
    (0.0002356696840195 : ℝ) ≤ ∫ t in (58/25 : ℝ)..(233/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (58/25 : ℝ)) (b := (233/100 : ℝ)) (A := (0.108922988705 : ℝ))
    (B := (0.1325985632 : ℝ)) (C := (0.02185971020523 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_232_100) (sigma0_deriv_lower_c2_232_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.465567542025 : ℝ) := by
        have hle : s + 2 ≤ (433/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_433_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.465567542025 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((58/25 : ℝ) + 2) * ((58/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((58/25 : ℝ) + 2) * ((58/25 : ℝ) + 1) = ((58/25 : ℝ) + 1) / ((58/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.40156326515351851851 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((333/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((333/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (333/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02185971020523 : ℝ))) ≤ (0.40156326515351851851 : ℝ) / (((333/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.40156326515351851851 : ℝ) / (((333/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.40156326515351851851 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.40156326515351851851 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_233_232
  rw [show ((233/100 : ℝ)) / ((58/25 : ℝ)) = (233/232 : ℝ) by norm_num] at hp
  have hX : ((0.108922988705 : ℝ) - (0.1325985632 : ℝ) * (58/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.108922988705 : ℝ) - (0.1325985632 : ℝ) * (58/25 : ℝ)) * log (233/232) ≥
      (((0.108922988705 : ℝ) - (0.1325985632 : ℝ) * (58/25 : ℝ))) * (0.0043010818994 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02185971020523 : ℝ) * (58/25 : ℝ) ^ 2) * log (233/232) ≥
      ((0.02185971020523 : ℝ) * (58/25 : ℝ) ^ 2) * (0.00430108189939 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 3 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_3 :
    (0.0002375091764799 : ℝ) ≤ ∫ t in (233/100 : ℝ)..(117/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (233/100 : ℝ)) (b := (117/50 : ℝ)) (A := (0.110251177209 : ℝ))
    (B := (0.1330386293 : ℝ)) (C := (0.02163311371816 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_233_100) (sigma0_deriv_lower_c2_233_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.467874348123 : ℝ) := by
        have hle : s + 2 ≤ (217/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_217_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.467874348123 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((233/100 : ℝ) + 2) * ((233/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((233/100 : ℝ) + 2) * ((233/100 : ℝ) + 1) = ((233/100 : ℝ) + 1) / ((233/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.39979105831990993071 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((167/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((167/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (167/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02163311371816 : ℝ))) ≤ (0.39979105831990993071 : ℝ) / (((167/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.39979105831990993071 : ℝ) / (((167/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.39979105831990993071 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.39979105831990993071 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_234_233
  rw [show ((117/50 : ℝ)) / ((233/100 : ℝ)) = (234/233 : ℝ) by norm_num] at hp
  have hX : ((0.110251177209 : ℝ) - (0.1330386293 : ℝ) * (233/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.110251177209 : ℝ) - (0.1330386293 : ℝ) * (233/100 : ℝ)) * log (234/233) ≥
      (((0.110251177209 : ℝ) - (0.1330386293 : ℝ) * (233/100 : ℝ))) * (0.00428266179201 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02163311371816 : ℝ) * (233/100 : ℝ) ^ 2) * log (234/233) ≥
      ((0.02163311371816 : ℝ) * (233/100 : ℝ) ^ 2) * (0.004282661792 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 4 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_4 :
    (0.0002393422660041 : ℝ) ≤ ∫ t in (117/50 : ℝ)..(47/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (117/50 : ℝ)) (b := (47/20 : ℝ)) (A := (0.111583743436 : ℝ))
    (B := (0.1334741324 : ℝ)) (C := (0.02140898230926 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_234_100) (sigma0_deriv_lower_c2_234_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.470175845112 : ℝ) := by
        have hle : s + 2 ≤ (87/20 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_87_20.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.470175845112 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((117/50 : ℝ) + 2) * ((117/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((117/50 : ℝ) + 2) * ((117/50 : ℝ) + 1) = ((117/50 : ℝ) + 1) / ((117/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.39802169700422119815 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((67/20 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((67/20 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (67/20 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02140898230926 : ℝ))) ≤ (0.39802169700422119815 : ℝ) / (((67/20 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.39802169700422119815 : ℝ) / (((67/20 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.39802169700422119815 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.39802169700422119815 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_235_234
  rw [show ((47/20 : ℝ)) / ((117/50 : ℝ)) = (235/234 : ℝ) by norm_num] at hp
  have hX : ((0.111583743436 : ℝ) - (0.1334741324 : ℝ) * (117/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.111583743436 : ℝ) - (0.1334741324 : ℝ) * (117/50 : ℝ)) * log (235/234) ≥
      (((0.111583743436 : ℝ) - (0.1334741324 : ℝ) * (117/50 : ℝ))) * (0.00426439878646 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02140898230926 : ℝ) * (117/50 : ℝ) ^ 2) * log (235/234) ≥
      ((0.02140898230926 : ℝ) * (117/50 : ℝ) ^ 2) * (0.00426439878645 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 5 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_5 :
    (0.0002411689383182 : ℝ) ≤ ∫ t in (47/20 : ℝ)..(59/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (47/20 : ℝ)) (b := (59/25 : ℝ)) (A := (0.112920641999 : ℝ))
    (B := (0.1339051221 : ℝ)) (C := (0.02118728367244 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_235_100) (sigma0_deriv_lower_c2_235_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.472472057372 : ℝ) := by
        have hle : s + 2 ≤ (109/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_109_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.472472057372 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((47/20 : ℝ) + 2) * ((47/20 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((47/20 : ℝ) + 2) * ((47/20 : ℝ) + 1) = ((47/20 : ℝ) + 1) / ((47/20 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.39625517381673563218 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((84/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((84/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (84/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02118728367244 : ℝ))) ≤ (0.39625517381673563218 : ℝ) / (((84/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.39625517381673563218 : ℝ) / (((84/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.39625517381673563218 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.39625517381673563218 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_236_235
  rw [show ((59/25 : ℝ)) / ((47/20 : ℝ)) = (236/235 : ℝ) by norm_num] at hp
  have hX : ((0.112920641999 : ℝ) - (0.1339051221 : ℝ) * (47/20 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.112920641999 : ℝ) - (0.1339051221 : ℝ) * (47/20 : ℝ)) * log (236/235) ≥
      (((0.112920641999 : ℝ) - (0.1339051221 : ℝ) * (47/20 : ℝ))) * (0.00424629088146 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02118728367244 : ℝ) * (47/20 : ℝ) ^ 2) * log (236/235) ≥
      ((0.02118728367244 : ℝ) * (47/20 : ℝ) ^ 2) * (0.00424629088145 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 6 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_6 :
    (0.0002429891804314 : ℝ) ≤ ∫ t in (59/25 : ℝ)..(237/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (59/25 : ℝ)) (b := (237/100 : ℝ)) (A := (0.114261828005 : ℝ))
    (B := (0.1343316476 : ℝ)) (C := (0.02096798600735 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_236_100) (sigma0_deriv_lower_c2_236_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.474763009118 : ℝ) := by
        have hle : s + 2 ≤ (437/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_437_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.474763009118 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((59/25 : ℝ) + 2) * ((59/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((59/25 : ℝ) + 2) * ((59/25 : ℝ) + 1) = ((59/25 : ℝ) + 1) / ((59/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.39449148137686238532 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((337/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((337/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (337/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02096798600735 : ℝ))) ≤ (0.39449148137686238532 : ℝ) / (((337/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.39449148137686238532 : ℝ) / (((337/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.39449148137686238532 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.39449148137686238532 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_237_236
  rw [show ((237/100 : ℝ)) / ((59/25 : ℝ)) = (237/236 : ℝ) by norm_num] at hp
  have hX : ((0.114261828005 : ℝ) - (0.1343316476 : ℝ) * (59/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.114261828005 : ℝ) - (0.1343316476 : ℝ) * (59/25 : ℝ)) * log (237/236) ≥
      (((0.114261828005 : ℝ) - (0.1343316476 : ℝ) * (59/25 : ℝ))) * (0.00422833610953 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02096798600735 : ℝ) * (59/25 : ℝ) ^ 2) * log (237/236) ≥
      ((0.02096798600735 : ℝ) * (59/25 : ℝ) ^ 2) * (0.00422833610952 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 7 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_7 :
    (0.0002448029805865 : ℝ) ≤ ∫ t in (237/100 : ℝ)..(119/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (237/100 : ℝ)) (b := (119/50 : ℝ)) (A := (0.115607257048 : ℝ))
    (B := (0.1347537572 : ℝ)) (C := (0.02075105801035 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_237_100) (sigma0_deriv_lower_c2_237_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.477048724399 : ℝ) := by
        have hle : s + 2 ≤ (219/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_219_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.477048724399 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((237/100 : ℝ) + 2) * ((237/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((237/100 : ℝ) + 2) * ((237/100 : ℝ) + 1) = ((237/100 : ℝ) + 1) / ((237/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.39273061231591990846 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((169/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((169/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (169/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02075105801035 : ℝ))) ≤ (0.39273061231591990846 : ℝ) / (((169/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.39273061231591990846 : ℝ) / (((169/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.39273061231591990846 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.39273061231591990846 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_238_237
  rw [show ((119/50 : ℝ)) / ((237/100 : ℝ)) = (238/237 : ℝ) by norm_num] at hp
  have hX : ((0.115607257048 : ℝ) - (0.1347537572 : ℝ) * (237/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.115607257048 : ℝ) - (0.1347537572 : ℝ) * (237/100 : ℝ)) * log (238/237) ≥
      (((0.115607257048 : ℝ) - (0.1347537572 : ℝ) * (237/100 : ℝ))) * (0.00421053253635 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02075105801035 : ℝ) * (237/100 : ℝ) ^ 2) * log (238/237) ≥
      ((0.02075105801035 : ℝ) * (237/100 : ℝ) ^ 2) * (0.00421053253634 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 8 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_8 :
    (0.0002466103282333 : ℝ) ≤ ∫ t in (119/50 : ℝ)..(239/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (119/50 : ℝ)) (b := (239/100 : ℝ)) (A := (0.116956885206 : ℝ))
    (B := (0.1351714987 : ℝ)) (C := (0.02053646886539 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_238_100) (sigma0_deriv_lower_c2_238_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.479329227098 : ℝ) := by
        have hle : s + 2 ≤ (439/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_439_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.479329227098 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((119/50 : ℝ) + 2) * ((119/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((119/50 : ℝ) + 2) * ((119/50 : ℝ) + 1) = ((119/50 : ℝ) + 1) / ((119/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.39097255927889497716 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((339/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((339/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (339/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02053646886539 : ℝ))) ≤ (0.39097255927889497716 : ℝ) / (((339/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.39097255927889497716 : ℝ) / (((339/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.39097255927889497716 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.39097255927889497716 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_239_238
  rw [show ((239/100 : ℝ)) / ((119/50 : ℝ)) = (239/238 : ℝ) by norm_num] at hp
  have hX : ((0.116956885206 : ℝ) - (0.1351714987 : ℝ) * (119/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.116956885206 : ℝ) - (0.1351714987 : ℝ) * (119/50 : ℝ)) * log (239/238) ≥
      (((0.116956885206 : ℝ) - (0.1351714987 : ℝ) * (119/50 : ℝ))) * (0.00419287826004 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02053646886539 : ℝ) * (119/50 : ℝ) ^ 2) * log (239/238) ≥
      ((0.02053646886539 : ℝ) * (119/50 : ℝ) ^ 2) * (0.00419287826003 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 9 of the `[23/10, 12/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c2_9 :
    (0.0002484112139744 : ℝ) ≤ ∫ t in (239/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (239/100 : ℝ)) (b := (12/5 : ℝ)) (A := (0.118310669028 : ℝ))
    (B := (0.1355849193 : ℝ)) (C := (0.02032418823516 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c2_239_100) (sigma0_deriv_lower_c2_239_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.481604540935 : ℝ) := by
        have hle : s + 2 ≤ (22/5 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_22_5.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.481604540935 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((239/100 : ℝ) + 2) * ((239/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((239/100 : ℝ) + 2) * ((239/100 : ℝ) + 1) = ((239/100 : ℝ) + 1) / ((239/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.38921731492317767653 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((17/5 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((17/5 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (17/5 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02032418823516 : ℝ))) ≤ (0.38921731492317767653 : ℝ) / (((17/5 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.38921731492317767653 : ℝ) / (((17/5 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.38921731492317767653 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.38921731492317767653 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_240_239
  rw [show ((12/5 : ℝ)) / ((239/100 : ℝ)) = (240/239 : ℝ) by norm_num] at hp
  have hX : ((0.118310669028 : ℝ) - (0.1355849193 : ℝ) * (239/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.118310669028 : ℝ) - (0.1355849193 : ℝ) * (239/100 : ℝ)) * log (240/239) ≥
      (((0.118310669028 : ℝ) - (0.1355849193 : ℝ) * (239/100 : ℝ))) * (0.00417537141049 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02032418823516 : ℝ) * (239/100 : ℝ) ^ 2) * log (240/239) ≥
      ((0.02032418823516 : ℝ) * (239/100 : ℝ) ^ 2) * (0.00417537141048 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- The ten-panel second-order sandwich for `∫ sigma0 t/(2t)` on `[23/10, 12/5]`. -/
private theorem sigma0_integral_lower2_c2 :
    (0.0024022991069226 : ℝ) ≤ ∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have s10 : (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (23/10 : ℝ)..(231/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (231/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s0 : (∫ t in (231/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (231/100 : ℝ)..(58/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (58/25 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s1 : (∫ t in (58/25 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (58/25 : ℝ)..(233/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (233/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s2 : (∫ t in (233/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (233/100 : ℝ)..(117/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (117/50 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s3 : (∫ t in (117/50 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (117/50 : ℝ)..(47/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (47/20 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s4 : (∫ t in (47/20 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (47/20 : ℝ)..(59/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (59/25 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s5 : (∫ t in (59/25 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (59/25 : ℝ)..(237/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (237/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s6 : (∫ t in (237/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (237/100 : ℝ)..(119/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (119/50 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s7 : (∫ t in (119/50 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (119/50 : ℝ)..(239/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (239/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s8 : (∫ t in (239/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (239/100 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (12/5 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  rw [s10, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  linarith [sigma0_panel_val2_c2_0, sigma0_panel_val2_c2_1, sigma0_panel_val2_c2_2, sigma0_panel_val2_c2_3, sigma0_panel_val2_c2_4, sigma0_panel_val2_c2_5, sigma0_panel_val2_c2_6, sigma0_panel_val2_c2_7, sigma0_panel_val2_c2_8, sigma0_panel_val2_c2_9]

/-- `∫ log (t+1)/t` on `[23/10, 12/5]` from the eight-term expansion at `c = 47/20`. -/
private theorem log_succ_integral_c2_lower :
    (0.0514467998874413 : ℝ) ≤ ∫ t in (23/10 : ℝ)..(12/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (23/10 : ℝ) (12/5 : ℝ),
      |((47/20 : ℝ) - t) / (47/20 + 1)| ≤ (1/67 : ℝ) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (23/10 : ℝ) ≤ 12/5)] at ht
    rw [abs_le]
    have hb : (0 : ℝ) < 47/20 + 1 := by norm_num
    constructor
    · rw [le_div_iff₀ hb]
      nlinarith [ht.1, ht.2]
    · rw [div_le_iff₀ hb]
      nlinarith [ht.1, ht.2]
  have h := log_succ_integral_lower (a := (23/10 : ℝ)) (b := (12/5 : ℝ)) (c := (47/20 : ℝ))
    (r := (1/67 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 8
  have hc := log_67_20
  have hl := log_24_23
  rw [show ((12/5 : ℝ) / (23/10)) = 24/23 by norm_num] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  norm_num at h
  have hmul : (1.208960345834 : ℝ) * (0.04255961441879 : ℝ) ≤ log (67/20) * log (24/23) := by
    have hm := mul_le_mul hc.1 hl.1 (by norm_num) (by linarith [hc.1])
    linarith [hm]
  linarith [h, hmul, hl.2]
/-- On `[23/10, 12/5]` the `Xi1` kernel has both indicators fixed whenever `sp - 2 ≤ 23/10`
(the second window sits below the panel and the first covers it). -/
private theorem Xi1_general_eq_c2 {s sp t : ℝ} (hsp : sp - 2 < 23/10)
    (h1 : (23/10 : ℝ) ≤ t) (h2 : t ≤ 12/5) :
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
below `[23/10, 12/5]`. -/
private theorem Xi1_general_integral_c2 {s sp : ℝ} (hsp : sp - 2 < 23/10)
    (hPpos : 0 < (s - 1) * (sp - 1)) :
    (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Functional.Xi1 s sp t) =
      log (16 / ((s - 1) * (sp - 1))) *
          (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (23/10 : ℝ)..(12/5 : ℝ), log (t + 1) / t) -
          (log ((s - 1) * (sp - 1)) / 2) *
            (∫ t in (23/10 : ℝ)..(12/5 : ℝ), 1 / t) := by
  have hI1 := sigma0_div_two_integrable (a := (23/10 : ℝ)) (b := (12/5 : ℝ))
    (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (23/10 : ℝ) (12/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (23/10 : ℝ) (12/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (23/10 : ℝ) (12/5 : ℝ),
      Wu04Functional.Xi1 s sp t =
        log (16 / ((s - 1) * (sp - 1))) * (Wu04Integral.sigma0 t / (2 * t)) +
          (log (t + 1) / t - (log ((s - 1) * (sp - 1)) / 2) * (1 / t)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (23/10 : ℝ) ≤ 12/5)] at ht
    rw [Xi1_general_eq_c2 hsp ht.1 ht.2]
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

/-- `integralMatrix 4 2` is the `Xi1 (13/5) (179/50)` quadrature on `[23/10, 12/5]`. -/
private theorem integralMatrix_4_2_eq :
    Wu04Table.integralMatrix 4 2 =
      ∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Functional.Xi1 ((13/5 : ℝ)) ((179/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_4_2` of Wu's Section 7 matrix**, certified on the `[23/10, 12/5]` panel. -/
private theorem entry_4_2_certified :
    (245310 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 4 2 := by
  rw [integralMatrix_4_2_eq,
    Xi1_general_integral_c2 (s := (13/5 : ℝ)) (sp := (179/50 : ℝ)) (by norm_num) (by norm_num),
    show (((13/5 : ℝ)) - 1) * ((179/50 : ℝ) - 1) = (516/125 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c2
  have hB := log_succ_integral_c2_lower
  have h1t := integral_one_div_exp (a := (23/10 : ℝ)) (b := (12/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_24_23
  have h4 := log_four_bounds
  have hP := log_P_4_bounds
  rw [h1t]
  have hLP : (1.3547956940207 : ℝ) ≤ log (16 / ((516/125 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3547956940207 : ℝ) * (0.0024022991069226 : ℝ) ≤
      log (16 / ((516/125 : ℝ))) * (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((516/125 : ℝ)) / 2) * log (24/23) ≤
      (1.4177930281793 : ℝ) / 2 * (0.0425596144188 : ℝ) := by
    have h2 : log ((516/125 : ℝ)) / 2 ≤ (1.4177930281793 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_4_2` in the shape the matrix file states it. -/
private theorem entry_4_2_leaf :
    (Wu04Table.candidateMatrixQ 4 2 : ℝ) ≤ Wu04Table.integralMatrix 4 2 := by
  have hc : (Wu04Table.candidateMatrixQ 4 2 : ℝ) = 245310 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_4_2_certified

/-- `integralMatrix 5 2` is the `Xi1 (27/10) (347/100)` quadrature on `[23/10, 12/5]`. -/
private theorem integralMatrix_5_2_eq :
    Wu04Table.integralMatrix 5 2 =
      ∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Functional.Xi1 ((27/10 : ℝ)) ((347/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_5_2` of Wu's Section 7 matrix**, certified on the `[23/10, 12/5]` panel. -/
private theorem entry_5_2_certified :
    (241272 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 5 2 := by
  rw [integralMatrix_5_2_eq,
    Xi1_general_integral_c2 (s := (27/10 : ℝ)) (sp := (347/100 : ℝ)) (by norm_num) (by norm_num),
    show (((27/10 : ℝ)) - 1) * ((347/100 : ℝ) - 1) = (4199/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c2
  have hB := log_succ_integral_c2_lower
  have h1t := integral_one_div_exp (a := (23/10 : ℝ)) (b := (12/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_24_23
  have h4 := log_four_bounds
  have hP := log_P_5_bounds
  rw [h1t]
  have hLP : (1.33774232049788 : ℝ) ≤ log (16 / ((4199/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.33774232049788 : ℝ) * (0.0024022991069226 : ℝ) ≤
      log (16 / ((4199/1000 : ℝ))) * (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4199/1000 : ℝ)) / 2) * log (24/23) ≤
      (1.43484640170212 : ℝ) / 2 * (0.0425596144188 : ℝ) := by
    have h2 : log ((4199/1000 : ℝ)) / 2 ≤ (1.43484640170212 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_5_2` in the shape the matrix file states it. -/
private theorem entry_5_2_leaf :
    (Wu04Table.candidateMatrixQ 5 2 : ℝ) ≤ Wu04Table.integralMatrix 5 2 := by
  have hc : (Wu04Table.candidateMatrixQ 5 2 : ℝ) = 241272 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_5_2_certified

/-- `integralMatrix 6 2` is the `Xi1 (14/5) (167/50)` quadrature on `[23/10, 12/5]`. -/
private theorem integralMatrix_6_2_eq :
    Wu04Table.integralMatrix 6 2 =
      ∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Functional.Xi1 ((14/5 : ℝ)) ((167/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_6_2` of Wu's Section 7 matrix**, certified on the `[23/10, 12/5]` panel. -/
private theorem entry_6_2_certified :
    (240539 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 6 2 := by
  rw [integralMatrix_6_2_eq,
    Xi1_general_integral_c2 (s := (14/5 : ℝ)) (sp := (167/50 : ℝ)) (by norm_num) (by norm_num),
    show (((14/5 : ℝ)) - 1) * ((167/50 : ℝ) - 1) = (1053/250 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c2
  have hB := log_succ_integral_c2_lower
  have h1t := integral_one_div_exp (a := (23/10 : ℝ)) (b := (12/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_24_23
  have h4 := log_four_bounds
  have hP := log_P_6_bounds
  rw [h1t]
  have hLP : (1.3346511279282 : ℝ) ≤ log (16 / ((1053/250 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3346511279282 : ℝ) * (0.0024022991069226 : ℝ) ≤
      log (16 / ((1053/250 : ℝ))) * (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((1053/250 : ℝ)) / 2) * log (24/23) ≤
      (1.4379375942718 : ℝ) / 2 * (0.0425596144188 : ℝ) := by
    have h2 : log ((1053/250 : ℝ)) / 2 ≤ (1.4379375942718 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_6_2` in the shape the matrix file states it. -/
private theorem entry_6_2_leaf :
    (Wu04Table.candidateMatrixQ 6 2 : ℝ) ≤ Wu04Table.integralMatrix 6 2 := by
  have hc : (Wu04Table.candidateMatrixQ 6 2 : ℝ) = 240539 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_6_2_certified

/-- `integralMatrix 7 2` is the `Xi1 (29/10) (319/100)` quadrature on `[23/10, 12/5]`. -/
private theorem integralMatrix_7_2_eq :
    Wu04Table.integralMatrix 7 2 =
      ∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Functional.Xi1 ((29/10 : ℝ)) ((319/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- Two-sided enclosure of `log (4161/1000)`, the `P` of row 7, in reduced form. -/
private theorem log_P_7_bounds :
    (1.42575543000 : ℝ) ≤ log (4161/1000) ∧ log (4161/1000) ≤ (1.42575543001 : ℝ) :=
  log_4_161_bounds

/-- **`entry_7_2` of Wu's Section 7 matrix**, certified on the `[23/10, 12/5]` panel. -/
private theorem entry_7_2_certified :
    (243424 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 7 2 := by
  rw [integralMatrix_7_2_eq,
    Xi1_general_integral_c2 (s := (29/10 : ℝ)) (sp := (319/100 : ℝ)) (by norm_num) (by norm_num),
    show (((29/10 : ℝ)) - 1) * ((319/100 : ℝ) - 1) = (4161/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c2
  have hB := log_succ_integral_c2_lower
  have h1t := integral_one_div_exp (a := (23/10 : ℝ)) (b := (12/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_24_23
  have h4 := log_four_bounds
  have hP := log_P_7_bounds
  rw [h1t]
  have hLP : (1.34683329219 : ℝ) ≤ log (16 / ((4161/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.34683329219 : ℝ) * (0.0024022991069226 : ℝ) ≤
      log (16 / ((4161/1000 : ℝ))) * (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4161/1000 : ℝ)) / 2) * log (24/23) ≤
      (1.42575543001 : ℝ) / 2 * (0.0425596144188 : ℝ) := by
    have h2 : log ((4161/1000 : ℝ)) / 2 ≤ (1.42575543001 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_7_2` in the shape the matrix file states it. -/
private theorem entry_7_2_leaf :
    (Wu04Table.candidateMatrixQ 7 2 : ℝ) ≤ Wu04Table.integralMatrix 7 2 := by
  have hc : (Wu04Table.candidateMatrixQ 7 2 : ℝ) = 243424 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_7_2_certified

/-- `integralMatrix 8 2` is the `Xi1 (3) (3)` quadrature on `[23/10, 12/5]`. -/
private theorem integralMatrix_8_2_eq :
    Wu04Table.integralMatrix 8 2 =
      ∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Functional.Xi1 ((3 : ℝ)) ((3 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_8_2` of Wu's Section 7 matrix**, certified on the `[23/10, 12/5]` panel. -/
private theorem entry_8_2_certified :
    (252770 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 8 2 := by
  rw [integralMatrix_8_2_eq,
    Xi1_general_integral_c2 (s := (3 : ℝ)) (sp := (3 : ℝ)) (by norm_num) (by norm_num),
    show (((3 : ℝ)) - 1) * ((3 : ℝ) - 1) = (4 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c2
  have hB := log_succ_integral_c2_lower
  have h1t := integral_one_div_exp (a := (23/10 : ℝ)) (b := (12/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_24_23
  have h4 := log_four_bounds
  have hP : (1.3862943611 : ℝ) ≤ log (4) ∧ log (4) ≤ (1.3862943615 : ℝ) := log_four_bounds
  rw [h1t]
  have hLP : (1.3862943607 : ℝ) ≤ log (16 / ((4 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3862943607 : ℝ) * (0.0024022991069226 : ℝ) ≤
      log (16 / ((4 : ℝ))) * (∫ t in (23/10 : ℝ)..(12/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4 : ℝ)) / 2) * log (24/23) ≤
      (1.3862943615 : ℝ) / 2 * (0.0425596144188 : ℝ) := by
    have h2 : log ((4 : ℝ)) / 2 ≤ (1.3862943615 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_8_2` in the shape the matrix file states it. -/
private theorem entry_8_2_leaf :
    (Wu04Table.candidateMatrixQ 8 2 : ℝ) ≤ Wu04Table.integralMatrix 8 2 := by
  have hc : (Wu04Table.candidateMatrixQ 8 2 : ℝ) = 252770 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_8_2_certified

/-- Two-sided enclosure of `log (441/100)`, from `log 43/10` and the ratio `441/430`. -/
private theorem log_441_100 :
    (1.483874689449 : ℝ) ≤ log ((441/100 : ℝ)) ∧ log ((441/100 : ℝ)) ≤ (1.48387468947 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (441/430 : ℝ))
    (x := (11/871 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0252596667592232 : ℝ) : ℝ) ≤ log (441/430) ∧
      log (441/430) ≤ ((0.0252596667593258 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((441/100 : ℝ)) = log ((43/10 : ℝ)) + log (441/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (441/430 : ℝ) = (441/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (221/50)`, from `log 43/10` and the ratio `221/215`. -/
private theorem log_221_50 :
    (1.48613969608 : ℝ) ≤ log ((221/50 : ℝ)) ∧ log ((221/50 : ℝ)) ≤ (1.486139696101 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (221/215 : ℝ))
    (x := (3/218 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0275246733900633 : ℝ) : ℝ) ≤ log (221/215) ∧
      log (221/215) ≤ ((0.0275246733902503 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((221/50 : ℝ)) = log ((43/10 : ℝ)) + log (221/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (221/215 : ℝ) = (221/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (443/100)`, from `log 43/10` and the ratio `443/430`. -/
private theorem log_443_100 :
    (1.488399584047 : ℝ) ≤ log ((443/100 : ℝ)) ∧ log ((443/100 : ℝ)) ≤ (1.488399584068 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (443/430 : ℝ))
    (x := (13/873 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0297845613574811 : ℝ) : ℝ) ≤ log (443/430) ∧
      log (443/430) ≤ ((0.029784561357806 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((443/100 : ℝ)) = log ((43/10 : ℝ)) + log (443/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (443/430 : ℝ) = (443/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (111/25)`, from `log 43/10` and the ratio `222/215`. -/
private theorem log_111_25 :
    (1.490654376434 : ℝ) ≤ log ((111/25 : ℝ)) ∧ log ((111/25 : ℝ)) ≤ (1.490654376456 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (222/215 : ℝ))
    (x := (7/437 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0320393537445393 : ℝ) : ℝ) ≤ log (222/215) ∧
      log (222/215) ≤ ((0.0320393537450807 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((111/25 : ℝ)) = log ((43/10 : ℝ)) + log (222/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (222/215 : ℝ) = (111/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (89/20)`, from `log 43/10` and the ratio `89/86`. -/
private theorem log_89_20 :
    (1.492904096168 : ℝ) ≤ log ((89/20 : ℝ)) ∧ log ((89/20 : ℝ)) ≤ (1.49290409619 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (89/86 : ℝ))
    (x := (3/175 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0342890734785077 : ℝ) : ℝ) ≤ log (89/86) ∧
      log (89/86) ≤ ((0.0342890734793783 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((89/20 : ℝ)) = log ((43/10 : ℝ)) + log (89/86) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (89/86 : ℝ) = (89/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (223/50)`, from `log 43/10` and the ratio `223/215`. -/
private theorem log_223_50 :
    (1.495148766022 : ℝ) ≤ log ((223/50 : ℝ)) ∧ log ((223/50 : ℝ)) ≤ (1.495148766044 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (223/215 : ℝ))
    (x := (4/219 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0365337433322621 : ℝ) : ℝ) ≤ log (223/215) ∧
      log (223/215) ≤ ((0.0365337433336189 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((223/50 : ℝ)) = log ((43/10 : ℝ)) + log (223/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (223/215 : ℝ) = (223/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (447/100)`, from `log 43/10` and the ratio `447/430`. -/
private theorem log_447_100 :
    (1.497388408615 : ℝ) ≤ log ((447/100 : ℝ)) ∧ log ((447/100 : ℝ)) ≤ (1.497388408638 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (447/430 : ℝ))
    (x := (17/877 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0387733859256668 : ℝ) : ℝ) ≤ log (447/430) ∧
      log (447/430) ≤ ((0.0387733859277244 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((447/100 : ℝ)) = log ((43/10 : ℝ)) + log (447/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (447/430 : ℝ) = (447/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (112/25)`, from `log 43/10` and the ratio `224/215`. -/
private theorem log_112_25 :
    (1.499623046416 : ℝ) ≤ log ((112/25 : ℝ)) ∧ log ((112/25 : ℝ)) ≤ (1.49962304644 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (224/215 : ℝ))
    (x := (9/439 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.041008023726942 : ℝ) : ℝ) ≤ log (224/215) ∧
      log (224/215) ≤ ((0.0410080237299876 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((112/25 : ℝ)) = log ((43/10 : ℝ)) + log (224/215) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (224/215 : ℝ) = (112/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (449/100)`, from `log 43/10` and the ratio `449/430`. -/
private theorem log_449_100 :
    (1.501852701744 : ℝ) ≤ log ((449/100 : ℝ)) ∧ log ((449/100 : ℝ)) ≤ (1.501852701769 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (449/430 : ℝ))
    (x := (19/879 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.043237679054016 : ℝ) : ℝ) ≤ log (449/430) ∧
      log (449/430) ≤ ((0.0432376790584276 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((449/100 : ℝ)) = log ((43/10 : ℝ)) + log (449/430) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (449/430 : ℝ) = (449/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (9/2)`, from `log 43/10` and the ratio `45/43`. -/
private theorem log_9_2 :
    (1.504077396765 : ℝ) ≤ log ((9/2 : ℝ)) ∧ log ((9/2 : ℝ)) ≤ (1.504077396793 : ℝ) := by
  have hA := log_4_3_bounds
  have hB := log_enclosure (y := (45/43 : ℝ))
    (x := (1/44 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.045462374075862 : ℝ) : ℝ) ≤ log (45/43) ∧
      log (45/43) ≤ ((0.0454623740821295 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((9/2 : ℝ)) = log ((43/10 : ℝ)) + log (45/43) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((43/10 : ℝ)) * (45/43 : ℝ) = (9/2 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (17/5)`, from `log 33/10` and the ratio `34/33`. -/
private theorem log_17_5 :
    (1.223775431619 : ℝ) ≤ log ((17/5 : ℝ)) ∧ log ((17/5 : ℝ)) ≤ (1.22377543163 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (34/33 : ℝ))
    (x := (1/67 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.029852963149634 : ℝ) : ℝ) ≤ log (34/33) ∧
      log (34/33) ≤ ((0.0298529631499641 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((17/5 : ℝ)) = log ((33/10 : ℝ)) + log (34/33) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (34/33 : ℝ) = (17/5 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (341/100)`, from `log 33/10` and the ratio `31/30`. -/
private theorem log_341_100 :
    (1.226712291292 : ℝ) ≤ log ((341/100 : ℝ)) ∧ log ((341/100 : ℝ)) ≤ (1.226712291304 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (31/30 : ℝ))
    (x := (1/61 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0327898228228999 : ℝ) : ℝ) ≤ log (31/30) ∧
      log (31/30) ≤ ((0.0327898228235365 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((341/100 : ℝ)) = log ((33/10 : ℝ)) + log (31/30) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (31/30 : ℝ) = (341/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (171/50)`, from `log 33/10` and the ratio `57/55`. -/
private theorem log_171_50 :
    (1.229640551071 : ℝ) ≤ log ((171/50 : ℝ)) ∧ log ((171/50 : ℝ)) ≤ (1.229640551084 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (57/55 : ℝ))
    (x := (1/56 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0357180826019137 : ℝ) : ℝ) ≤ log (57/55) ∧
      log (57/55) ≤ ((0.0357180826030722 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((171/50 : ℝ)) = log ((33/10 : ℝ)) + log (57/55) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (57/55 : ℝ) = (171/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (343/100)`, from `log 33/10` and the ratio `343/330`. -/
private theorem log_343_100 :
    (1.232560261175 : ℝ) ≤ log ((343/100 : ℝ)) ∧ log ((343/100 : ℝ)) ≤ (1.232560261188 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (343/330 : ℝ))
    (x := (13/673 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0386377927051272 : ℝ) : ℝ) ≤ log (343/330) ∧
      log (343/330) ≤ ((0.0386377927071349 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((343/100 : ℝ)) = log ((33/10 : ℝ)) + log (343/330) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (343/330 : ℝ) = (343/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (86/25)`, from `log 33/10` and the ratio `172/165`. -/
private theorem log_86_25 :
    (1.235471471382 : ℝ) ≤ log ((86/25 : ℝ)) ∧ log ((86/25 : ℝ)) ≤ (1.235471471396 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (172/165 : ℝ))
    (x := (7/337 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0415490029123956 : ℝ) : ℝ) ≤ log (172/165) ∧
      log (172/165) ≤ ((0.0415490029157337 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((86/25 : ℝ)) = log ((33/10 : ℝ)) + log (172/165) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (172/165 : ℝ) = (86/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (69/20)`, from `log 33/10` and the ratio `23/22`. -/
private theorem log_69_20 :
    (1.23837423104 : ℝ) ≤ log ((69/20 : ℝ)) ∧ log ((69/20 : ℝ)) ≤ (1.238374231056 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (23/22 : ℝ))
    (x := (1/45 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0444517625700689 : ℝ) : ℝ) ≤ log (23/22) ∧
      log (23/22) ≤ ((0.0444517625754239 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((69/20 : ℝ)) = log ((33/10 : ℝ)) + log (23/22) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (23/22 : ℝ) = (69/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (173/50)`, from `log 33/10` and the ratio `173/165`. -/
private theorem log_173_50 :
    (1.241268589066 : ℝ) ≤ log ((173/50 : ℝ)) ∧ log ((173/50 : ℝ)) ≤ (1.241268589085 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (173/165 : ℝ))
    (x := (4/169 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0473461205960089 : ℝ) : ℝ) ≤ log (173/165) ∧
      log (173/165) ≤ ((0.0473461206043359 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((173/50 : ℝ)) = log ((33/10 : ℝ)) + log (173/165) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (173/165 : ℝ) = (173/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (347/100)`, from `log 33/10` and the ratio `347/330`. -/
private theorem log_347_100 :
    (1.244154593954 : ℝ) ≤ log ((347/100 : ℝ)) ∧ log ((347/100 : ℝ)) ≤ (1.244154593978 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (347/330 : ℝ))
    (x := (17/677 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0502321254845337 : ℝ) : ℝ) ≤ log (347/330) ∧
      log (347/330) ≤ ((0.0502321254971325 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((347/100 : ℝ)) = log ((33/10 : ℝ)) + log (347/330) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (347/330 : ℝ) = (347/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (87/25)`, from `log 33/10` and the ratio `58/55`. -/
private theorem log_87_25 :
    (1.247032293781 : ℝ) ≤ log ((87/25 : ℝ)) ∧ log ((87/25 : ℝ)) ≤ (1.24703229381 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (58/55 : ℝ))
    (x := (3/113 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0531098253112909 : ℝ) : ℝ) ≤ log (58/55) ∧
      log (58/55) ≤ ((0.0531098253298963 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((87/25 : ℝ)) = log ((33/10 : ℝ)) + log (58/55) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (58/55 : ℝ) = (87/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (349/100)`, from `log 33/10` and the ratio `349/330`. -/
private theorem log_349_100 :
    (1.249901736208 : ℝ) ≤ log ((349/100 : ℝ)) ∧ log ((349/100 : ℝ)) ≤ (1.249901736245 : ℝ) := by
  have hA := log_3_3_bounds
  have hB := log_enclosure (y := (349/330 : ℝ))
    (x := (19/679 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0559792677380607 : ℝ) : ℝ) ≤ log (349/330) ∧
      log (349/330) ≤ ((0.0559792677649487 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((349/100 : ℝ)) = log ((33/10 : ℝ)) + log (349/330) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((33/10 : ℝ)) * (349/330 : ℝ) = (349/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (25/24)` from the atanh series. -/
private theorem log_25_24 :
    (0.04082199452025 : ℝ) ≤ log ((25/24 : ℝ)) ∧ log ((25/24 : ℝ)) ≤ (0.04082199452026 : ℝ) := by
  have h := log_enclosure (y := (25/24 : ℝ))
    (x := (1/49 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 4
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (241/240)` from the atanh series. -/
private theorem log_241_240 :
    (0.00415801014866 : ℝ) ≤ log ((241/240 : ℝ)) ∧ log ((241/240 : ℝ)) ≤ (0.00415801014867 : ℝ) := by
  have h := log_enclosure (y := (241/240 : ℝ))
    (x := (1/481 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (242/241)` from the atanh series. -/
private theorem log_242_241 :
    (0.00414079266603 : ℝ) ≤ log ((242/241 : ℝ)) ∧ log ((242/241 : ℝ)) ≤ (0.00414079266604 : ℝ) := by
  have h := log_enclosure (y := (242/241 : ℝ))
    (x := (1/483 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (243/242)` from the atanh series. -/
private theorem log_243_242 :
    (0.00412371718386 : ℝ) ≤ log ((243/242 : ℝ)) ∧ log ((243/242 : ℝ)) ≤ (0.00412371718387 : ℝ) := by
  have h := log_enclosure (y := (243/242 : ℝ))
    (x := (1/485 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (244/243)` from the atanh series. -/
private theorem log_244_243 :
    (0.00410678195265 : ℝ) ≤ log ((244/243 : ℝ)) ∧ log ((244/243 : ℝ)) ≤ (0.00410678195266 : ℝ) := by
  have h := log_enclosure (y := (244/243 : ℝ))
    (x := (1/487 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (245/244)` from the atanh series. -/
private theorem log_245_244 :
    (0.00408998525152 : ℝ) ≤ log ((245/244 : ℝ)) ∧ log ((245/244 : ℝ)) ≤ (0.00408998525153 : ℝ) := by
  have h := log_enclosure (y := (245/244 : ℝ))
    (x := (1/489 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (246/245)` from the atanh series. -/
private theorem log_246_245 :
    (0.00407332538763 : ℝ) ≤ log ((246/245 : ℝ)) ∧ log ((246/245 : ℝ)) ≤ (0.00407332538764 : ℝ) := by
  have h := log_enclosure (y := (246/245 : ℝ))
    (x := (1/491 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (247/246)` from the atanh series. -/
private theorem log_247_246 :
    (0.00405680069561 : ℝ) ≤ log ((247/246 : ℝ)) ∧ log ((247/246 : ℝ)) ≤ (0.00405680069562 : ℝ) := by
  have h := log_enclosure (y := (247/246 : ℝ))
    (x := (1/493 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (248/247)` from the atanh series. -/
private theorem log_248_247 :
    (0.004040409537 : ℝ) ≤ log ((248/247 : ℝ)) ∧ log ((248/247 : ℝ)) ≤ (0.00404040953701 : ℝ) := by
  have h := log_enclosure (y := (248/247 : ℝ))
    (x := (1/495 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (249/248)` from the atanh series. -/
private theorem log_249_248 :
    (0.00402415029972 : ℝ) ≤ log ((249/248 : ℝ)) ∧ log ((249/248 : ℝ)) ≤ (0.00402415029973 : ℝ) := by
  have h := log_enclosure (y := (249/248 : ℝ))
    (x := (1/497 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (250/249)` from the atanh series. -/
private theorem log_250_249 :
    (0.00400802139753 : ℝ) ≤ log ((250/249 : ℝ)) ∧ log ((250/249 : ℝ)) ≤ (0.00400802139754 : ℝ) := by
  have h := log_enclosure (y := (250/249 : ℝ))
    (x := (1/499 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `sigma 3 (22/5) (17/5)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_440_100 :
    (0.099122260851 : ℝ) ≤ Wu04Integral.sigma 3 ((22/5 : ℝ)) ((17/5 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (22/5 : ℝ)) (c := (17/5 : ℝ)) (m := (27/10 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((22/5 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((22/5 : ℝ)) - 1) = (17/5 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (17/5 : ℝ)) (m := (27/10 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.382992252244 : ℝ) ≤ log ((22/5 : ℝ)) - log 3 := by
    linarith [log_22_5.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((17/5 : ℝ)) := by linarith [log_17_5.1]
  have hp : (0 : ℝ) ≤ (0.382992252244 : ℝ) := by norm_num
  have hlo' : (0.4686965087966340213 : ℝ) ≤ log ((17/5 : ℝ)) * (log ((22/5 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_17_5.1 hdiff_lo hp hq
    have hc : (0.4686965087966340213 : ℝ) ≤ (1.223775431619 : ℝ) * (0.382992252244 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_17_5.1, log_17_5.2, log_22_5.1, log_22_5.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((12/5 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_240_100 :
    (0.119668565536 : ℝ) ≤ Wu04Integral.sigma0 ((12/5 : ℝ)) := by
  have h := sigma_c3_440_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((12/5 : ℝ)) + 2 = (22/5 : ℝ) by norm_num, show ((12/5 : ℝ)) + 1 = (17/5 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.119668565536 : ℝ) : ℝ) ≤ ((0.099122260851 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.099122260851 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (441/100) (341/100)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_441_100 :
    (0.100250386811 : ℝ) ≤ Wu04Integral.sigma 3 ((441/100 : ℝ)) ((341/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (441/100 : ℝ)) (c := (341/100 : ℝ)) (m := (541/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((441/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((441/100 : ℝ)) - 1) = (341/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (341/100 : ℝ)) (m := (541/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.385262400779 : ℝ) ≤ log ((441/100 : ℝ)) - log 3 := by
    linarith [log_441_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((341/100 : ℝ)) := by linarith [log_341_100.1]
  have hp : (0 : ℝ) ≤ (0.385262400779 : ℝ) := by norm_num
  have hlo' : (0.47260612240826389571 : ℝ) ≤ log ((341/100 : ℝ)) * (log ((441/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_341_100.1 hdiff_lo hp hq
    have hc : (0.47260612240826389571 : ℝ) ≤ (1.226712291292 : ℝ) * (0.385262400779 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_341_100.1, log_341_100.2, log_441_100.1, log_441_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((241/100 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_241_100 :
    (0.121030532204 : ℝ) ≤ Wu04Integral.sigma0 ((241/100 : ℝ)) := by
  have h := sigma_c3_441_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((241/100 : ℝ)) + 2 = (441/100 : ℝ) by norm_num, show ((241/100 : ℝ)) + 1 = (341/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.121030532204 : ℝ) : ℝ) ≤ ((0.100250386811 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.100250386811 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (221/50) (171/50)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_442_100 :
    (0.101381849274 : ℝ) ≤ Wu04Integral.sigma 3 ((221/50 : ℝ)) ((171/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (221/50 : ℝ)) (c := (171/50 : ℝ)) (m := (271/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((221/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((221/50 : ℝ)) - 1) = (171/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (171/50 : ℝ)) (m := (271/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.38752740741 : ℝ) ≤ log ((221/50 : ℝ)) - log 3 := by
    linarith [log_221_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((171/50 : ℝ)) := by linarith [log_171_50.1]
  have hp : (0 : ℝ) ≤ (0.38752740741 : ℝ) := by norm_num
  have hlo' : (0.47651941480274832883 : ℝ) ≤ log ((171/50 : ℝ)) * (log ((221/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_171_50.1 hdiff_lo hp hq
    have hc : (0.47651941480274832883 : ℝ) ≤ (1.229640551071 : ℝ) * (0.38752740741 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_171_50.1, log_171_50.2, log_221_50.1, log_221_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((121/50 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_242_100 :
    (0.122396526974 : ℝ) ≤ Wu04Integral.sigma0 ((121/50 : ℝ)) := by
  have h := sigma_c3_442_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((121/50 : ℝ)) + 2 = (221/50 : ℝ) by norm_num, show ((121/50 : ℝ)) + 1 = (171/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.122396526974 : ℝ) : ℝ) ≤ ((0.101381849274 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.101381849274 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (443/100) (343/100)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_443_100 :
    (0.10251661377 : ℝ) ≤ Wu04Integral.sigma 3 ((443/100 : ℝ)) ((343/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (443/100 : ℝ)) (c := (343/100 : ℝ)) (m := (543/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((443/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((443/100 : ℝ)) - 1) = (343/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (343/100 : ℝ)) (m := (543/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.389787295377 : ℝ) ≤ log ((443/100 : ℝ)) - log 3 := by
    linarith [log_443_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((343/100 : ℝ)) := by linarith [log_343_100.1]
  have hp : (0 : ℝ) ≤ (0.389787295377 : ℝ) := by norm_num
  have hlo' : (0.48043633059257199008 : ℝ) ≤ log ((343/100 : ℝ)) * (log ((443/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_343_100.1 hdiff_lo hp hq
    have hc : (0.48043633059257199008 : ℝ) ≤ (1.232560261175 : ℝ) * (0.389787295377 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_343_100.1, log_343_100.2, log_443_100.1, log_443_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((243/100 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_243_100 :
    (0.12376650823 : ℝ) ≤ Wu04Integral.sigma0 ((243/100 : ℝ)) := by
  have h := sigma_c3_443_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((243/100 : ℝ)) + 2 = (443/100 : ℝ) by norm_num, show ((243/100 : ℝ)) + 1 = (343/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.12376650823 : ℝ) : ℝ) ≤ ((0.10251661377 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.10251661377 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (111/25) (86/25)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_444_100 :
    (0.103654646201 : ℝ) ≤ Wu04Integral.sigma 3 ((111/25 : ℝ)) ((86/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (111/25 : ℝ)) (c := (86/25 : ℝ)) (m := (68/25 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((111/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((111/25 : ℝ)) - 1) = (86/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (86/25 : ℝ)) (m := (68/25 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.392042087764 : ℝ) ≤ log ((111/25 : ℝ)) - log 3 := by
    linarith [log_111_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((86/25 : ℝ)) := by linarith [log_86_25.1]
  have hp : (0 : ℝ) ≤ (0.392042087764 : ℝ) := by norm_num
  have hlo' : (0.48435681501346025836 : ℝ) ≤ log ((86/25 : ℝ)) * (log ((111/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_86_25.1 hdiff_lo hp hq
    have hc : (0.48435681501346025836 : ℝ) ≤ (1.235471471382 : ℝ) * (0.392042087764 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_86_25.1, log_86_25.2, log_111_25.1, log_111_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((61/25 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_244_100 :
    (0.125140434807 : ℝ) ≤ Wu04Integral.sigma0 ((61/25 : ℝ)) := by
  have h := sigma_c3_444_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((61/25 : ℝ)) + 2 = (111/25 : ℝ) by norm_num, show ((61/25 : ℝ)) + 1 = (86/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.125140434807 : ℝ) : ℝ) ≤ ((0.103654646201 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.103654646201 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (89/20) (69/20)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_445_100 :
    (0.104795912828 : ℝ) ≤ Wu04Integral.sigma 3 ((89/20 : ℝ)) ((69/20 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (89/20 : ℝ)) (c := (69/20 : ℝ)) (m := (109/40 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((89/20 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((89/20 : ℝ)) - 1) = (69/20 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (69/20 : ℝ)) (m := (109/40 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.394291807498 : ℝ) ≤ log ((89/20 : ℝ)) - log 3 := by
    linarith [log_89_20.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((69/20 : ℝ)) := by linarith [log_69_20.1]
  have hp : (0 : ℝ) ≤ (0.394291807498 : ℝ) := by norm_num
  have hlo' : (0.48828081391570745633 : ℝ) ≤ log ((69/20 : ℝ)) * (log ((89/20 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_69_20.1 hdiff_lo hp hq
    have hc : (0.48828081391570745633 : ℝ) ≤ (1.23837423104 : ℝ) * (0.394291807498 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_69_20.1, log_69_20.2, log_89_20.1, log_89_20.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((49/20 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_245_100 :
    (0.126518265972 : ℝ) ≤ Wu04Integral.sigma0 ((49/20 : ℝ)) := by
  have h := sigma_c3_445_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((49/20 : ℝ)) + 2 = (89/20 : ℝ) by norm_num, show ((49/20 : ℝ)) + 1 = (69/20 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.126518265972 : ℝ) : ℝ) ≤ ((0.104795912828 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.104795912828 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (223/50) (173/50)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_446_100 :
    (0.105940380275 : ℝ) ≤ Wu04Integral.sigma 3 ((223/50 : ℝ)) ((173/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (223/50 : ℝ)) (c := (173/50 : ℝ)) (m := (273/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((223/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((223/50 : ℝ)) - 1) = (173/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (173/50 : ℝ)) (m := (273/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.396536477352 : ℝ) ≤ log ((223/50 : ℝ)) - log 3 := by
    linarith [log_223_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((173/50 : ℝ)) := by linarith [log_173_50.1]
  have hp : (0 : ℝ) ≤ (0.396536477352 : ℝ) := by norm_num
  have hlo' : (0.49220827375591890383 : ℝ) ≤ log ((173/50 : ℝ)) * (log ((223/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_173_50.1 hdiff_lo hp hq
    have hc : (0.49220827375591890383 : ℝ) ≤ (1.241268589066 : ℝ) * (0.396536477352 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_173_50.1, log_173_50.2, log_223_50.1, log_223_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((123/50 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_246_100 :
    (0.127899961431 : ℝ) ≤ Wu04Integral.sigma0 ((123/50 : ℝ)) := by
  have h := sigma_c3_446_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((123/50 : ℝ)) + 2 = (223/50 : ℝ) by norm_num, show ((123/50 : ℝ)) + 1 = (173/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.127899961431 : ℝ) : ℝ) ≤ ((0.105940380275 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.105940380275 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (447/100) (347/100)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_447_100 :
    (0.107088015516 : ℝ) ≤ Wu04Integral.sigma 3 ((447/100 : ℝ)) ((347/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (447/100 : ℝ)) (c := (347/100 : ℝ)) (m := (547/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((447/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((447/100 : ℝ)) - 1) = (347/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (347/100 : ℝ)) (m := (547/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.398776119945 : ℝ) ≤ log ((447/100 : ℝ)) - log 3 := by
    linarith [log_447_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((347/100 : ℝ)) := by linarith [log_347_100.1]
  have hp : (0 : ℝ) ≤ (0.398776119945 : ℝ) := by norm_num
  have hlo' : (0.49613914158872307581 : ℝ) ≤ log ((347/100 : ℝ)) * (log ((447/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_347_100.1 hdiff_lo hp hq
    have hc : (0.49613914158872307581 : ℝ) ≤ (1.244154593954 : ℝ) * (0.398776119945 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_347_100.1, log_347_100.2, log_447_100.1, log_447_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((247/100 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_247_100 :
    (0.129285481312 : ℝ) ≤ Wu04Integral.sigma0 ((247/100 : ℝ)) := by
  have h := sigma_c3_447_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((247/100 : ℝ)) + 2 = (447/100 : ℝ) by norm_num, show ((247/100 : ℝ)) + 1 = (347/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.129285481312 : ℝ) : ℝ) ≤ ((0.107088015516 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.107088015516 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (112/25) (87/25)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_448_100 :
    (0.108238785879 : ℝ) ≤ Wu04Integral.sigma 3 ((112/25 : ℝ)) ((87/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (112/25 : ℝ)) (c := (87/25 : ℝ)) (m := (137/50 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((112/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((112/25 : ℝ)) - 1) = (87/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (87/25 : ℝ)) (m := (137/50 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.401010757746 : ℝ) ≤ log ((112/25 : ℝ)) - log 3 := by
    linarith [log_112_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((87/25 : ℝ)) := by linarith [log_87_25.1]
  have hp : (0 : ℝ) ≤ (0.401010757746 : ℝ) := by norm_num
  have hlo' : (0.50007336506285129337 : ℝ) ≤ log ((87/25 : ℝ)) * (log ((112/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_87_25.1 hdiff_lo hp hq
    have hc : (0.50007336506285129337 : ℝ) ≤ (1.247032293781 : ℝ) * (0.401010757746 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_87_25.1, log_87_25.2, log_112_25.1, log_112_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((62/25 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_248_100 :
    (0.130674786171 : ℝ) ≤ Wu04Integral.sigma0 ((62/25 : ℝ)) := by
  have h := sigma_c3_448_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((62/25 : ℝ)) + 2 = (112/25 : ℝ) by norm_num, show ((62/25 : ℝ)) + 1 = (87/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.130674786171 : ℝ) : ℝ) ≤ ((0.108238785879 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.108238785879 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (449/100) (349/100)` at the left end of a `[12/5, 5/2]` panel of `entry_i_2`. -/
private theorem sigma_c3_449_100 :
    (0.109392659035 : ℝ) ≤ Wu04Integral.sigma 3 ((449/100 : ℝ)) ((349/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (449/100 : ℝ)) (c := (349/100 : ℝ)) (m := (549/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((449/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((449/100 : ℝ)) - 1) = (349/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (349/100 : ℝ)) (m := (549/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.403240413074 : ℝ) ≤ log ((449/100 : ℝ)) - log 3 := by
    linarith [log_449_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((349/100 : ℝ)) := by linarith [log_349_100.1]
  have hp : (0 : ℝ) ≤ (0.403240413074 : ℝ) := by norm_num
  have hlo' : (0.50401089241042370238 : ℝ) ≤ log ((349/100 : ℝ)) * (log ((449/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_349_100.1 hdiff_lo hp hq
    have hc : (0.50401089241042370238 : ℝ) ≤ (1.249901736208 : ℝ) * (0.403240413074 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_349_100.1, log_349_100.2, log_449_100.1, log_449_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((249/100 : ℝ))` at a `[12/5, 5/2]` panel endpoint. -/
private theorem sigma0_c3_249_100 :
    (0.132067836977 : ℝ) ≤ Wu04Integral.sigma0 ((249/100 : ℝ)) := by
  have h := sigma_c3_449_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((249/100 : ℝ)) + 2 = (449/100 : ℝ) by norm_num, show ((249/100 : ℝ)) + 1 = (349/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.132067836977 : ℝ) : ℝ) ≤ ((0.109392659035 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.109392659035 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
/-- Lower bound of `sigma0' ((12/5 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_240_100 :
    (0.1359940656 : ℝ) ≤
      (log (((12/5 : ℝ) + 2) / 3) / ((12/5 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_22_5
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.382992252244 : ℝ) ≤ log ((22/5 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((12/5 : ℝ) + 2) / 3) = ((22/5 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1359940656 : ℝ)
      ≤ (0.382992252244 : ℝ) / (((12/5 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((22/5 : ℝ)) - log 3) / (((12/5 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((22/5 : ℝ)) - log 3) / (((12/5 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((241/100 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_241_100 :
    (0.1363989834 : ℝ) ≤
      (log (((241/100 : ℝ) + 2) / 3) / ((241/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_441_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.385262400779 : ℝ) ≤ log ((441/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((241/100 : ℝ) + 2) / 3) = ((441/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1363989834 : ℝ)
      ≤ (0.385262400779 : ℝ) / (((241/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((441/100 : ℝ)) - log 3) / (((241/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((441/100 : ℝ)) - log 3) / (((241/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((121/50 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_242_100 :
    (0.1367997182 : ℝ) ≤
      (log (((121/50 : ℝ) + 2) / 3) / ((121/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_221_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.38752740741 : ℝ) ≤ log ((221/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((121/50 : ℝ) + 2) / 3) = ((221/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1367997182 : ℝ)
      ≤ (0.38752740741 : ℝ) / (((121/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((221/50 : ℝ)) - log 3) / (((121/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((221/50 : ℝ)) - log 3) / (((121/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((243/100 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_243_100 :
    (0.1371963146 : ℝ) ≤
      (log (((243/100 : ℝ) + 2) / 3) / ((243/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_443_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.389787295377 : ℝ) ≤ log ((443/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((243/100 : ℝ) + 2) / 3) = ((443/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1371963146 : ℝ)
      ≤ (0.389787295377 : ℝ) / (((243/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((443/100 : ℝ)) - log 3) / (((243/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((443/100 : ℝ)) - log 3) / (((243/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((61/25 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_244_100 :
    (0.137588817 : ℝ) ≤
      (log (((61/25 : ℝ) + 2) / 3) / ((61/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_111_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.392042087764 : ℝ) ≤ log ((111/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((61/25 : ℝ) + 2) / 3) = ((111/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.137588817 : ℝ)
      ≤ (0.392042087764 : ℝ) / (((61/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((111/25 : ℝ)) - log 3) / (((61/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((111/25 : ℝ)) - log 3) / (((61/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((49/20 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_245_100 :
    (0.1379772689 : ℝ) ≤
      (log (((49/20 : ℝ) + 2) / 3) / ((49/20 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_89_20
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.394291807498 : ℝ) ≤ log ((89/20 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((49/20 : ℝ) + 2) / 3) = ((89/20 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1379772689 : ℝ)
      ≤ (0.394291807498 : ℝ) / (((49/20 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((89/20 : ℝ)) - log 3) / (((49/20 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((89/20 : ℝ)) - log 3) / (((49/20 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((123/50 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_246_100 :
    (0.1383617133 : ℝ) ≤
      (log (((123/50 : ℝ) + 2) / 3) / ((123/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_223_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.396536477352 : ℝ) ≤ log ((223/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((123/50 : ℝ) + 2) / 3) = ((223/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1383617133 : ℝ)
      ≤ (0.396536477352 : ℝ) / (((123/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((223/50 : ℝ)) - log 3) / (((123/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((223/50 : ℝ)) - log 3) / (((123/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((247/100 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_247_100 :
    (0.1387421929 : ℝ) ≤
      (log (((247/100 : ℝ) + 2) / 3) / ((247/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_447_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.398776119945 : ℝ) ≤ log ((447/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((247/100 : ℝ) + 2) / 3) = ((447/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1387421929 : ℝ)
      ≤ (0.398776119945 : ℝ) / (((247/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((447/100 : ℝ)) - log 3) / (((247/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((447/100 : ℝ)) - log 3) / (((247/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((62/25 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_248_100 :
    (0.1391187495 : ℝ) ≤
      (log (((62/25 : ℝ) + 2) / 3) / ((62/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_112_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.401010757746 : ℝ) ≤ log ((112/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((62/25 : ℝ) + 2) / 3) = ((112/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1391187495 : ℝ)
      ≤ (0.401010757746 : ℝ) / (((62/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((112/25 : ℝ)) - log 3) / (((62/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((112/25 : ℝ)) - log 3) / (((62/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((249/100 : ℝ))`, the tangent slope of a `[12/5, 5/2]` panel. -/
private theorem sigma0_deriv_lower_c3_249_100 :
    (0.1394914247 : ℝ) ≤
      (log (((249/100 : ℝ) + 2) / 3) / ((249/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_449_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.403240413074 : ℝ) ≤ log ((449/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((249/100 : ℝ) + 2) / 3) = ((449/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1394914247 : ℝ)
      ≤ (0.403240413074 : ℝ) / (((249/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((449/100 : ℝ)) - log 3) / (((249/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((449/100 : ℝ)) - log 3) / (((249/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Second-order panel 0 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_0 :
    (0.000250205629547 : ℝ) ≤ ∫ t in (12/5 : ℝ)..(241/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (12/5 : ℝ)) (b := (241/100 : ℝ)) (A := (0.119668565536 : ℝ))
    (B := (0.1359940656 : ℝ)) (C := (0.02011418625219 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_240_100) (sigma0_deriv_lower_c3_240_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.48387468947 : ℝ) := by
        have hle : s + 2 ≤ (441/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_441_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.48387468947 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((12/5 : ℝ) + 2) * ((12/5 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((12/5 : ℝ) + 2) * ((12/5 : ℝ) + 1) = ((12/5 : ℝ) + 1) / ((12/5 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.38746487191727272727 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((341/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((341/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (341/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.02011418625219 : ℝ))) ≤ (0.38746487191727272727 : ℝ) / (((341/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.38746487191727272727 : ℝ) / (((341/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.38746487191727272727 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.38746487191727272727 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_241_240
  rw [show ((241/100 : ℝ)) / ((12/5 : ℝ)) = (241/240 : ℝ) by norm_num] at hp
  have hX : ((0.119668565536 : ℝ) - (0.1359940656 : ℝ) * (12/5 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.119668565536 : ℝ) - (0.1359940656 : ℝ) * (12/5 : ℝ)) * log (241/240) ≥
      (((0.119668565536 : ℝ) - (0.1359940656 : ℝ) * (12/5 : ℝ))) * (0.00415801014867 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.02011418625219 : ℝ) * (12/5 : ℝ) ^ 2) * log (241/240) ≥
      ((0.02011418625219 : ℝ) * (12/5 : ℝ) ^ 2) * (0.00415801014866 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 1 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_1 :
    (0.0002519935677514 : ℝ) ≤ ∫ t in (241/100 : ℝ)..(121/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (241/100 : ℝ)) (b := (121/50 : ℝ)) (A := (0.121030532204 : ℝ))
    (B := (0.1363989834 : ℝ)) (C := (0.01990643351059 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_241_100) (sigma0_deriv_lower_c3_241_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.486139696101 : ℝ) := by
        have hle : s + 2 ≤ (221/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_221_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.486139696101 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((241/100 : ℝ) + 2) * ((241/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((241/100 : ℝ) + 2) * ((241/100 : ℝ) + 1) = ((241/100 : ℝ) + 1) / ((241/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.38571522294448752834 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((171/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((171/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (171/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01990643351059 : ℝ))) ≤ (0.38571522294448752834 : ℝ) / (((171/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.38571522294448752834 : ℝ) / (((171/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.38571522294448752834 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.38571522294448752834 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_242_241
  rw [show ((121/50 : ℝ)) / ((241/100 : ℝ)) = (242/241 : ℝ) by norm_num] at hp
  have hX : ((0.121030532204 : ℝ) - (0.1363989834 : ℝ) * (241/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.121030532204 : ℝ) - (0.1363989834 : ℝ) * (241/100 : ℝ)) * log (242/241) ≥
      (((0.121030532204 : ℝ) - (0.1363989834 : ℝ) * (241/100 : ℝ))) * (0.00414079266604 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01990643351059 : ℝ) * (241/100 : ℝ) ^ 2) * log (242/241) ≥
      ((0.01990643351059 : ℝ) * (241/100 : ℝ) ^ 2) * (0.00414079266603 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 2 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_2 :
    (0.0002537750224696 : ℝ) ≤ ∫ t in (121/50 : ℝ)..(243/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (121/50 : ℝ)) (b := (243/100 : ℝ)) (A := (0.122396526974 : ℝ))
    (B := (0.1367997182 : ℝ)) (C := (0.01970090105755 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_242_100) (sigma0_deriv_lower_c3_242_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.488399584068 : ℝ) := by
        have hle : s + 2 ≤ (443/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_443_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.488399584068 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((121/50 : ℝ) + 2) * ((121/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((121/50 : ℝ) + 2) * ((121/50 : ℝ) + 1) = ((121/50 : ℝ) + 1) / ((121/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.38396836070059728506 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((343/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((343/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (343/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01970090105755 : ℝ))) ≤ (0.38396836070059728506 : ℝ) / (((343/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.38396836070059728506 : ℝ) / (((343/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.38396836070059728506 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.38396836070059728506 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_243_242
  rw [show ((243/100 : ℝ)) / ((121/50 : ℝ)) = (243/242 : ℝ) by norm_num] at hp
  have hX : ((0.122396526974 : ℝ) - (0.1367997182 : ℝ) * (121/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.122396526974 : ℝ) - (0.1367997182 : ℝ) * (121/50 : ℝ)) * log (243/242) ≥
      (((0.122396526974 : ℝ) - (0.1367997182 : ℝ) * (121/50 : ℝ))) * (0.00412371718387 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01970090105755 : ℝ) * (121/50 : ℝ) ^ 2) * log (243/242) ≥
      ((0.01970090105755 : ℝ) * (121/50 : ℝ) ^ 2) * (0.00412371718386 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 3 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_3 :
    (0.000255549988582 : ℝ) ≤ ∫ t in (243/100 : ℝ)..(61/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (243/100 : ℝ)) (b := (61/25 : ℝ)) (A := (0.12376650823 : ℝ))
    (B := (0.1371963146 : ℝ)) (C := (0.01949756038506 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_243_100) (sigma0_deriv_lower_c3_243_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.490654376456 : ℝ) := by
        have hle : s + 2 ≤ (111/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_111_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.490654376456 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((243/100 : ℝ) + 2) * ((243/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((243/100 : ℝ) + 2) * ((243/100 : ℝ) + 1) = ((243/100 : ℝ) + 1) / ((243/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.38222427789248758465 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((86/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((86/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (86/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01949756038506 : ℝ))) ≤ (0.38222427789248758465 : ℝ) / (((86/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.38222427789248758465 : ℝ) / (((86/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.38222427789248758465 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.38222427789248758465 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_244_243
  rw [show ((61/25 : ℝ)) / ((243/100 : ℝ)) = (244/243 : ℝ) by norm_num] at hp
  have hX : ((0.12376650823 : ℝ) - (0.1371963146 : ℝ) * (243/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.12376650823 : ℝ) - (0.1371963146 : ℝ) * (243/100 : ℝ)) * log (244/243) ≥
      (((0.12376650823 : ℝ) - (0.1371963146 : ℝ) * (243/100 : ℝ))) * (0.00410678195266 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01949756038506 : ℝ) * (243/100 : ℝ) ^ 2) * log (244/243) ≥
      ((0.01949756038506 : ℝ) * (243/100 : ℝ) ^ 2) * (0.00410678195265 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 4 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_4 :
    (0.0002573184619731 : ℝ) ≤ ∫ t in (61/25 : ℝ)..(49/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (61/25 : ℝ)) (b := (49/20 : ℝ)) (A := (0.125140434807 : ℝ))
    (B := (0.137588817 : ℝ)) (C := (0.01929638342227 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_244_100) (sigma0_deriv_lower_c3_244_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.49290409619 : ℝ) := by
        have hle : s + 2 ≤ (89/20 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_89_20.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.49290409619 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((61/25 : ℝ) + 2) * ((61/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((61/25 : ℝ) + 2) * ((61/25 : ℝ) + 1) = ((61/25 : ℝ) + 1) / ((61/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.38048296724477477477 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((69/20 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((69/20 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (69/20 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01929638342227 : ℝ))) ≤ (0.38048296724477477477 : ℝ) / (((69/20 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.38048296724477477477 : ℝ) / (((69/20 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.38048296724477477477 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.38048296724477477477 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_245_244
  rw [show ((49/20 : ℝ)) / ((61/25 : ℝ)) = (245/244 : ℝ) by norm_num] at hp
  have hX : ((0.125140434807 : ℝ) - (0.137588817 : ℝ) * (61/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.125140434807 : ℝ) - (0.137588817 : ℝ) * (61/25 : ℝ)) * log (245/244) ≥
      (((0.125140434807 : ℝ) - (0.137588817 : ℝ) * (61/25 : ℝ))) * (0.00408998525153 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01929638342227 : ℝ) * (61/25 : ℝ) ^ 2) * log (245/244) ≥
      ((0.01929638342227 : ℝ) * (61/25 : ℝ) ^ 2) * (0.00408998525152 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 5 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_5 :
    (0.0002590804394652 : ℝ) ≤ ∫ t in (49/20 : ℝ)..(123/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (49/20 : ℝ)) (b := (123/50 : ℝ)) (A := (0.126518265972 : ℝ))
    (B := (0.1379772689 : ℝ)) (C := (0.01909734252726 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_245_100) (sigma0_deriv_lower_c3_245_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.495148766044 : ℝ) := by
        have hle : s + 2 ≤ (223/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_223_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.495148766044 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((49/20 : ℝ) + 2) * ((49/20 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((49/20 : ℝ) + 2) * ((49/20 : ℝ) + 1) = ((49/20 : ℝ) + 1) / ((49/20 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.37874442149240449438 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((173/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((173/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (173/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01909734252726 : ℝ))) ≤ (0.37874442149240449438 : ℝ) / (((173/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.37874442149240449438 : ℝ) / (((173/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.37874442149240449438 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.37874442149240449438 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_246_245
  rw [show ((123/50 : ℝ)) / ((49/20 : ℝ)) = (246/245 : ℝ) by norm_num] at hp
  have hX : ((0.126518265972 : ℝ) - (0.1379772689 : ℝ) * (49/20 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.126518265972 : ℝ) - (0.1379772689 : ℝ) * (49/20 : ℝ)) * log (246/245) ≥
      (((0.126518265972 : ℝ) - (0.1379772689 : ℝ) * (49/20 : ℝ))) * (0.00407332538764 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01909734252726 : ℝ) * (49/20 : ℝ) ^ 2) * log (246/245) ≥
      ((0.01909734252726 : ℝ) * (49/20 : ℝ) ^ 2) * (0.00407332538763 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 6 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_6 :
    (0.0002608359188175 : ℝ) ≤ ∫ t in (123/50 : ℝ)..(247/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (123/50 : ℝ)) (b := (247/100 : ℝ)) (A := (0.127899961431 : ℝ))
    (B := (0.1383617133 : ℝ)) (C := (0.01890041047957 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_246_100) (sigma0_deriv_lower_c3_246_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.497388408638 : ℝ) := by
        have hle : s + 2 ≤ (447/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_447_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.497388408638 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((123/50 : ℝ) + 2) * ((123/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((123/50 : ℝ) + 2) * ((123/50 : ℝ) + 1) = ((123/50 : ℝ) + 1) / ((123/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.37700863338522869955 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((347/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((347/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (347/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01890041047957 : ℝ))) ≤ (0.37700863338522869955 : ℝ) / (((347/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.37700863338522869955 : ℝ) / (((347/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.37700863338522869955 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.37700863338522869955 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_247_246
  rw [show ((247/100 : ℝ)) / ((123/50 : ℝ)) = (247/246 : ℝ) by norm_num] at hp
  have hX : ((0.127899961431 : ℝ) - (0.1383617133 : ℝ) * (123/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.127899961431 : ℝ) - (0.1383617133 : ℝ) * (123/50 : ℝ)) * log (247/246) ≥
      (((0.127899961431 : ℝ) - (0.1383617133 : ℝ) * (123/50 : ℝ))) * (0.00405680069562 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01890041047957 : ℝ) * (123/50 : ℝ) ^ 2) * log (247/246) ≥
      ((0.01890041047957 : ℝ) * (123/50 : ℝ) ^ 2) * (0.00405680069561 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 7 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_7 :
    (0.0002625848986752 : ℝ) ≤ ∫ t in (247/100 : ℝ)..(62/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (247/100 : ℝ)) (b := (62/25 : ℝ)) (A := (0.129285481312 : ℝ))
    (B := (0.1387421929 : ℝ)) (C := (0.01870556047266 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_247_100) (sigma0_deriv_lower_c3_247_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.49962304644 : ℝ) := by
        have hle : s + 2 ≤ (112/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_112_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.49962304644 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((247/100 : ℝ) + 2) * ((247/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((247/100 : ℝ) + 2) * ((247/100 : ℝ) + 1) = ((247/100 : ℝ) + 1) / ((247/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.37527559568756152125 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((87/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((87/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (87/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01870556047266 : ℝ))) ≤ (0.37527559568756152125 : ℝ) / (((87/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.37527559568756152125 : ℝ) / (((87/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.37527559568756152125 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.37527559568756152125 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_248_247
  rw [show ((62/25 : ℝ)) / ((247/100 : ℝ)) = (248/247 : ℝ) by norm_num] at hp
  have hX : ((0.129285481312 : ℝ) - (0.1387421929 : ℝ) * (247/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.129285481312 : ℝ) - (0.1387421929 : ℝ) * (247/100 : ℝ)) * log (248/247) ≥
      (((0.129285481312 : ℝ) - (0.1387421929 : ℝ) * (247/100 : ℝ))) * (0.00404040953701 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01870556047266 : ℝ) * (247/100 : ℝ) ^ 2) * log (248/247) ≥
      ((0.01870556047266 : ℝ) * (247/100 : ℝ) ^ 2) * (0.004040409537 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 8 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_8 :
    (0.0002643273785572 : ℝ) ≤ ∫ t in (62/25 : ℝ)..(249/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (62/25 : ℝ)) (b := (249/100 : ℝ)) (A := (0.130674786171 : ℝ))
    (B := (0.1391187495 : ℝ)) (C := (0.01851276610647 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_248_100) (sigma0_deriv_lower_c3_248_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.501852701769 : ℝ) := by
        have hle : s + 2 ≤ (449/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_449_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.501852701769 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((62/25 : ℝ) + 2) * ((62/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((62/25 : ℝ) + 2) * ((62/25 : ℝ) + 1) = ((62/25 : ℝ) + 1) / ((62/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.37354530117671428571 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((349/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((349/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (349/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01851276610647 : ℝ))) ≤ (0.37354530117671428571 : ℝ) / (((349/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.37354530117671428571 : ℝ) / (((349/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.37354530117671428571 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.37354530117671428571 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_249_248
  rw [show ((249/100 : ℝ)) / ((62/25 : ℝ)) = (249/248 : ℝ) by norm_num] at hp
  have hX : ((0.130674786171 : ℝ) - (0.1391187495 : ℝ) * (62/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.130674786171 : ℝ) - (0.1391187495 : ℝ) * (62/25 : ℝ)) * log (249/248) ≥
      (((0.130674786171 : ℝ) - (0.1391187495 : ℝ) * (62/25 : ℝ))) * (0.00402415029973 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01851276610647 : ℝ) * (62/25 : ℝ) ^ 2) * log (249/248) ≥
      ((0.01851276610647 : ℝ) * (62/25 : ℝ) ^ 2) * (0.00402415029972 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 9 of the `[12/5, 5/2]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c3_9 :
    (0.0002660633588161 : ℝ) ≤ ∫ t in (249/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (249/100 : ℝ)) (b := (5/2 : ℝ)) (A := (0.132067836977 : ℝ))
    (B := (0.1394914247 : ℝ)) (C := (0.01832200138036 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c3_249_100) (sigma0_deriv_lower_c3_249_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.504077396793 : ℝ) := by
        have hle : s + 2 ≤ (9/2 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_9_2.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.504077396793 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((249/100 : ℝ) + 2) * ((249/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((249/100 : ℝ) + 2) * ((249/100 : ℝ) + 1) = ((249/100 : ℝ) + 1) / ((249/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.37181774264651002227 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((7/2 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((7/2 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (7/2 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01832200138036 : ℝ))) ≤ (0.37181774264651002227 : ℝ) / (((7/2 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.37181774264651002227 : ℝ) / (((7/2 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.37181774264651002227 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.37181774264651002227 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_250_249
  rw [show ((5/2 : ℝ)) / ((249/100 : ℝ)) = (250/249 : ℝ) by norm_num] at hp
  have hX : ((0.132067836977 : ℝ) - (0.1394914247 : ℝ) * (249/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.132067836977 : ℝ) - (0.1394914247 : ℝ) * (249/100 : ℝ)) * log (250/249) ≥
      (((0.132067836977 : ℝ) - (0.1394914247 : ℝ) * (249/100 : ℝ))) * (0.00400802139754 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01832200138036 : ℝ) * (249/100 : ℝ) ^ 2) * log (250/249) ≥
      ((0.01832200138036 : ℝ) * (249/100 : ℝ) ^ 2) * (0.00400802139753 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- The ten-panel second-order sandwich for `∫ sigma0 t/(2t)` on `[12/5, 5/2]`. -/
private theorem sigma0_integral_lower2_c3 :
    (0.0025817346646543 : ℝ) ≤ ∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have s10 : (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (12/5 : ℝ)..(241/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (241/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s0 : (∫ t in (241/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (241/100 : ℝ)..(121/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (121/50 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s1 : (∫ t in (121/50 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (121/50 : ℝ)..(243/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (243/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s2 : (∫ t in (243/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (243/100 : ℝ)..(61/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (61/25 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s3 : (∫ t in (61/25 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (61/25 : ℝ)..(49/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (49/20 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s4 : (∫ t in (49/20 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (49/20 : ℝ)..(123/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (123/50 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s5 : (∫ t in (123/50 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (123/50 : ℝ)..(247/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (247/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s6 : (∫ t in (247/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (247/100 : ℝ)..(62/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (62/25 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s7 : (∫ t in (62/25 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (62/25 : ℝ)..(249/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (249/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s8 : (∫ t in (249/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (249/100 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (5/2 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  rw [s10, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  linarith [sigma0_panel_val2_c3_0, sigma0_panel_val2_c3_1, sigma0_panel_val2_c3_2, sigma0_panel_val2_c3_3, sigma0_panel_val2_c3_4, sigma0_panel_val2_c3_5, sigma0_panel_val2_c3_6, sigma0_panel_val2_c3_7, sigma0_panel_val2_c3_8, sigma0_panel_val2_c3_9]

/-- `∫ log (t+1)/t` on `[12/5, 5/2]` from the eight-term expansion at `c = 49/20`. -/
private theorem log_succ_integral_c3_lower :
    (0.0505474515201772 : ℝ) ≤ ∫ t in (12/5 : ℝ)..(5/2 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (12/5 : ℝ) (5/2 : ℝ),
      |((49/20 : ℝ) - t) / (49/20 + 1)| ≤ (1/69 : ℝ) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (12/5 : ℝ) ≤ 5/2)] at ht
    rw [abs_le]
    have hb : (0 : ℝ) < 49/20 + 1 := by norm_num
    constructor
    · rw [le_div_iff₀ hb]
      nlinarith [ht.1, ht.2]
    · rw [div_le_iff₀ hb]
      nlinarith [ht.1, ht.2]
  have h := log_succ_integral_lower (a := (12/5 : ℝ)) (b := (5/2 : ℝ)) (c := (49/20 : ℝ))
    (r := (1/69 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 8
  have hc := log_69_20
  have hl := log_25_24
  rw [show ((5/2 : ℝ) / (12/5)) = 25/24 by norm_num] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  norm_num at h
  have hmul : (1.23837423104 : ℝ) * (0.04082199452025 : ℝ) ≤ log (69/20) * log (25/24) := by
    have hm := mul_le_mul hc.1 hl.1 (by norm_num) (by linarith [hc.1])
    linarith [hm]
  linarith [h, hmul, hl.2]
/-- On `[12/5, 5/2]` the `Xi1` kernel has both indicators fixed whenever `sp - 2 ≤ 12/5`
(the second window sits below the panel and the first covers it). -/
private theorem Xi1_general_eq_c3 {s sp t : ℝ} (hsp : sp - 2 < 12/5)
    (h1 : (12/5 : ℝ) ≤ t) (h2 : t ≤ 5/2) :
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
below `[12/5, 5/2]`. -/
private theorem Xi1_general_integral_c3 {s sp : ℝ} (hsp : sp - 2 < 12/5)
    (hPpos : 0 < (s - 1) * (sp - 1)) :
    (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Functional.Xi1 s sp t) =
      log (16 / ((s - 1) * (sp - 1))) *
          (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (12/5 : ℝ)..(5/2 : ℝ), log (t + 1) / t) -
          (log ((s - 1) * (sp - 1)) / 2) *
            (∫ t in (12/5 : ℝ)..(5/2 : ℝ), 1 / t) := by
  have hI1 := sigma0_div_two_integrable (a := (12/5 : ℝ)) (b := (5/2 : ℝ))
    (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (12/5 : ℝ) (5/2 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (12/5 : ℝ) (5/2 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (12/5 : ℝ) (5/2 : ℝ),
      Wu04Functional.Xi1 s sp t =
        log (16 / ((s - 1) * (sp - 1))) * (Wu04Integral.sigma0 t / (2 * t)) +
          (log (t + 1) / t - (log ((s - 1) * (sp - 1)) / 2) * (1 / t)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (12/5 : ℝ) ≤ 5/2)] at ht
    rw [Xi1_general_eq_c3 hsp ht.1 ht.2]
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

/-- `integralMatrix 4 2` is the `Xi1 (13/5) (179/50)` quadrature on `[12/5, 5/2]`. -/
private theorem integralMatrix_4_3_eq :
    Wu04Table.integralMatrix 4 3 =
      ∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Functional.Xi1 ((13/5 : ℝ)) ((179/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_4_2` of Wu's Section 7 matrix**, certified on the `[12/5, 5/2]` panel. -/
private theorem entry_4_3_certified :
    (251066 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 4 3 := by
  rw [integralMatrix_4_3_eq,
    Xi1_general_integral_c3 (s := (13/5 : ℝ)) (sp := (179/50 : ℝ)) (by norm_num) (by norm_num),
    show (((13/5 : ℝ)) - 1) * ((179/50 : ℝ) - 1) = (516/125 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c3
  have hB := log_succ_integral_c3_lower
  have h1t := integral_one_div_exp (a := (12/5 : ℝ)) (b := (5/2 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_25_24
  have h4 := log_four_bounds
  have hP := log_P_4_bounds
  rw [h1t]
  have hLP : (1.3547956940207 : ℝ) ≤ log (16 / ((516/125 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3547956940207 : ℝ) * (0.0025817346646543 : ℝ) ≤
      log (16 / ((516/125 : ℝ))) * (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((516/125 : ℝ)) / 2) * log (25/24) ≤
      (1.4177930281793 : ℝ) / 2 * (0.04082199452026 : ℝ) := by
    have h2 : log ((516/125 : ℝ)) / 2 ≤ (1.4177930281793 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_4_2` in the shape the matrix file states it. -/
private theorem entry_4_3_leaf :
    (Wu04Table.candidateMatrixQ 4 3 : ℝ) ≤ Wu04Table.integralMatrix 4 3 := by
  have hc : (Wu04Table.candidateMatrixQ 4 3 : ℝ) = 251066 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_4_3_certified

/-- `integralMatrix 5 2` is the `Xi1 (27/10) (347/100)` quadrature on `[12/5, 5/2]`. -/
private theorem integralMatrix_5_3_eq :
    Wu04Table.integralMatrix 5 3 =
      ∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Functional.Xi1 ((27/10 : ℝ)) ((347/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_5_2` of Wu's Section 7 matrix**, certified on the `[12/5, 5/2]` panel. -/
private theorem entry_5_3_certified :
    (247145 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 5 3 := by
  rw [integralMatrix_5_3_eq,
    Xi1_general_integral_c3 (s := (27/10 : ℝ)) (sp := (347/100 : ℝ)) (by norm_num) (by norm_num),
    show (((27/10 : ℝ)) - 1) * ((347/100 : ℝ) - 1) = (4199/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c3
  have hB := log_succ_integral_c3_lower
  have h1t := integral_one_div_exp (a := (12/5 : ℝ)) (b := (5/2 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_25_24
  have h4 := log_four_bounds
  have hP := log_P_5_bounds
  rw [h1t]
  have hLP : (1.33774232049788 : ℝ) ≤ log (16 / ((4199/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.33774232049788 : ℝ) * (0.0025817346646543 : ℝ) ≤
      log (16 / ((4199/1000 : ℝ))) * (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4199/1000 : ℝ)) / 2) * log (25/24) ≤
      (1.43484640170212 : ℝ) / 2 * (0.04082199452026 : ℝ) := by
    have h2 : log ((4199/1000 : ℝ)) / 2 ≤ (1.43484640170212 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_5_2` in the shape the matrix file states it. -/
private theorem entry_5_3_leaf :
    (Wu04Table.candidateMatrixQ 5 3 : ℝ) ≤ Wu04Table.integralMatrix 5 3 := by
  have hc : (Wu04Table.candidateMatrixQ 5 3 : ℝ) = 247145 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_5_3_certified

/-- `integralMatrix 6 2` is the `Xi1 (14/5) (167/50)` quadrature on `[12/5, 5/2]`. -/
private theorem integralMatrix_6_3_eq :
    Wu04Table.integralMatrix 6 3 =
      ∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Functional.Xi1 ((14/5 : ℝ)) ((167/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_6_2` of Wu's Section 7 matrix**, certified on the `[12/5, 5/2]` panel. -/
private theorem entry_6_3_certified :
    (246434 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 6 3 := by
  rw [integralMatrix_6_3_eq,
    Xi1_general_integral_c3 (s := (14/5 : ℝ)) (sp := (167/50 : ℝ)) (by norm_num) (by norm_num),
    show (((14/5 : ℝ)) - 1) * ((167/50 : ℝ) - 1) = (1053/250 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c3
  have hB := log_succ_integral_c3_lower
  have h1t := integral_one_div_exp (a := (12/5 : ℝ)) (b := (5/2 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_25_24
  have h4 := log_four_bounds
  have hP := log_P_6_bounds
  rw [h1t]
  have hLP : (1.3346511279282 : ℝ) ≤ log (16 / ((1053/250 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3346511279282 : ℝ) * (0.0025817346646543 : ℝ) ≤
      log (16 / ((1053/250 : ℝ))) * (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((1053/250 : ℝ)) / 2) * log (25/24) ≤
      (1.4379375942718 : ℝ) / 2 * (0.04082199452026 : ℝ) := by
    have h2 : log ((1053/250 : ℝ)) / 2 ≤ (1.4379375942718 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_6_2` in the shape the matrix file states it. -/
private theorem entry_6_3_leaf :
    (Wu04Table.candidateMatrixQ 6 3 : ℝ) ≤ Wu04Table.integralMatrix 6 3 := by
  have hc : (Wu04Table.candidateMatrixQ 6 3 : ℝ) = 246434 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_6_3_certified

/-- `integralMatrix 7 2` is the `Xi1 (29/10) (319/100)` quadrature on `[12/5, 5/2]`. -/
private theorem integralMatrix_7_3_eq :
    Wu04Table.integralMatrix 7 3 =
      ∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Functional.Xi1 ((29/10 : ℝ)) ((319/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_7_2` of Wu's Section 7 matrix**, certified on the `[12/5, 5/2]` panel. -/
private theorem entry_7_3_certified :
    (249235 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 7 3 := by
  rw [integralMatrix_7_3_eq,
    Xi1_general_integral_c3 (s := (29/10 : ℝ)) (sp := (319/100 : ℝ)) (by norm_num) (by norm_num),
    show (((29/10 : ℝ)) - 1) * ((319/100 : ℝ) - 1) = (4161/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c3
  have hB := log_succ_integral_c3_lower
  have h1t := integral_one_div_exp (a := (12/5 : ℝ)) (b := (5/2 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_25_24
  have h4 := log_four_bounds
  have hP := log_P_7_bounds
  rw [h1t]
  have hLP : (1.34683329219 : ℝ) ≤ log (16 / ((4161/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.34683329219 : ℝ) * (0.0025817346646543 : ℝ) ≤
      log (16 / ((4161/1000 : ℝ))) * (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4161/1000 : ℝ)) / 2) * log (25/24) ≤
      (1.42575543001 : ℝ) / 2 * (0.04082199452026 : ℝ) := by
    have h2 : log ((4161/1000 : ℝ)) / 2 ≤ (1.42575543001 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_7_2` in the shape the matrix file states it. -/
private theorem entry_7_3_leaf :
    (Wu04Table.candidateMatrixQ 7 3 : ℝ) ≤ Wu04Table.integralMatrix 7 3 := by
  have hc : (Wu04Table.candidateMatrixQ 7 3 : ℝ) = 249235 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_7_3_certified

/-- `integralMatrix 8 2` is the `Xi1 (3) (3)` quadrature on `[12/5, 5/2]`. -/
private theorem integralMatrix_8_3_eq :
    Wu04Table.integralMatrix 8 3 =
      ∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Functional.Xi1 ((3 : ℝ)) ((3 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_8_2` of Wu's Section 7 matrix**, certified on the `[12/5, 5/2]` panel. -/
private theorem entry_8_3_certified :
    (258308 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 8 3 := by
  rw [integralMatrix_8_3_eq,
    Xi1_general_integral_c3 (s := (3 : ℝ)) (sp := (3 : ℝ)) (by norm_num) (by norm_num),
    show (((3 : ℝ)) - 1) * ((3 : ℝ) - 1) = (4 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c3
  have hB := log_succ_integral_c3_lower
  have h1t := integral_one_div_exp (a := (12/5 : ℝ)) (b := (5/2 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_25_24
  have h4 := log_four_bounds
  have hP : (1.3862943611 : ℝ) ≤ log (4) ∧ log (4) ≤ (1.3862943615 : ℝ) := log_four_bounds
  rw [h1t]
  have hLP : (1.3862943607 : ℝ) ≤ log (16 / ((4 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3862943607 : ℝ) * (0.0025817346646543 : ℝ) ≤
      log (16 / ((4 : ℝ))) * (∫ t in (12/5 : ℝ)..(5/2 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4 : ℝ)) / 2) * log (25/24) ≤
      (1.3862943615 : ℝ) / 2 * (0.04082199452026 : ℝ) := by
    have h2 : log ((4 : ℝ)) / 2 ≤ (1.3862943615 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_8_2` in the shape the matrix file states it. -/
private theorem entry_8_3_leaf :
    (Wu04Table.candidateMatrixQ 8 3 : ℝ) ≤ Wu04Table.integralMatrix 8 3 := by
  have hc : (Wu04Table.candidateMatrixQ 8 3 : ℝ) = 258308 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_8_3_certified

/-- Two-sided enclosure of `log (451/100)`, from `log 9/2` and the ratio `451/450`. -/
private theorem log_451_100 :
    (1.506297153503 : ℝ) ≤ log ((451/100 : ℝ)) ∧ log ((451/100 : ℝ)) ≤ (1.506297153532 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (451/450 : ℝ))
    (x := (1/901 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0022197567383129 : ℝ) : ℝ) ≤ log (451/450) ∧
      log (451/450) ≤ ((0.002219756738313 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((451/100 : ℝ)) = log ((9/2 : ℝ)) + log (451/450) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (451/450 : ℝ) = (451/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (113/25)`, from `log 9/2` and the ratio `226/225`. -/
private theorem log_113_25 :
    (1.508511993832 : ℝ) ≤ log ((113/25 : ℝ)) ∧ log ((113/25 : ℝ)) ≤ (1.508511993861 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (226/225 : ℝ))
    (x := (1/451 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0044345970678657 : ℝ) : ℝ) ≤ log (226/225) ∧
      log (226/225) ≤ ((0.0044345970678658 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((113/25 : ℝ)) = log ((9/2 : ℝ)) + log (226/225) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (226/225 : ℝ) = (113/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (453/100)`, from `log 9/2` and the ratio `151/150`. -/
private theorem log_453_100 :
    (1.510721939483 : ℝ) ≤ log ((453/100 : ℝ)) ∧ log ((453/100 : ℝ)) ≤ (1.510721939512 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (151/150 : ℝ))
    (x := (1/301 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0066445427186685 : ℝ) : ℝ) ≤ log (151/150) ∧
      log (151/150) ≤ ((0.0066445427186686 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((453/100 : ℝ)) = log ((9/2 : ℝ)) + log (151/150) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (151/150 : ℝ) = (453/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (227/50)`, from `log 9/2` and the ratio `227/225`. -/
private theorem log_227_50 :
    (1.512927012041 : ℝ) ≤ log ((227/50 : ℝ)) ∧ log ((227/50 : ℝ)) ≤ (1.51292701207 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (227/225 : ℝ))
    (x := (1/226 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0088496152769825 : ℝ) : ℝ) ≤ log (227/225) ∧
      log (227/225) ≤ ((0.0088496152769826 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((227/50 : ℝ)) = log ((9/2 : ℝ)) + log (227/225) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (227/225 : ℝ) = (227/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (91/20)`, from `log 9/2` and the ratio `91/90`. -/
private theorem log_91_20 :
    (1.515127232951 : ℝ) ≤ log ((91/20 : ℝ)) ∧ log ((91/20 : ℝ)) ≤ (1.51512723298 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (91/90 : ℝ))
    (x := (1/181 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0110498361865849 : ℝ) : ℝ) ≤ log (91/90) ∧
      log (91/90) ≤ ((0.0110498361865853 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((91/20 : ℝ)) = log ((9/2 : ℝ)) + log (91/90) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (91/90 : ℝ) = (91/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (114/25)`, from `log 9/2` and the ratio `76/75`. -/
private theorem log_114_25 :
    (1.517322623515 : ℝ) ≤ log ((114/25 : ℝ)) ∧ log ((114/25 : ℝ)) ≤ (1.517322623544 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (76/75 : ℝ))
    (x := (1/151 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0132452267500204 : ℝ) : ℝ) ≤ log (76/75) ∧
      log (76/75) ≤ ((0.0132452267500216 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((114/25 : ℝ)) = log ((9/2 : ℝ)) + log (76/75) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (76/75 : ℝ) = (114/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (457/100)`, from `log 9/2` and the ratio `457/450`. -/
private theorem log_457_100 :
    (1.519513204894 : ℝ) ≤ log ((457/100 : ℝ)) ∧ log ((457/100 : ℝ)) ≤ (1.519513204923 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (457/450 : ℝ))
    (x := (7/907 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0154358081298387 : ℝ) : ℝ) ≤ log (457/450) ∧
      log (457/450) ≤ ((0.0154358081298421 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((457/100 : ℝ)) = log ((9/2 : ℝ)) + log (457/450) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (457/450 : ℝ) = (457/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (229/50)`, from `log 9/2` and the ratio `229/225`. -/
private theorem log_229_50 :
    (1.521698998114 : ℝ) ≤ log ((229/50 : ℝ)) ∧ log ((229/50 : ℝ)) ≤ (1.521698998143 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (229/225 : ℝ))
    (x := (2/227 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0176216013498183 : ℝ) : ℝ) ≤ log (229/225) ∧
      log (229/225) ≤ ((0.0176216013498266 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((229/50 : ℝ)) = log ((9/2 : ℝ)) + log (229/225) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (229/225 : ℝ) = (229/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (459/100)`, from `log 9/2` and the ratio `51/50`. -/
private theorem log_459_100 :
    (1.523880024061 : ℝ) ≤ log ((459/100 : ℝ)) ∧ log ((459/100 : ℝ)) ≤ (1.52388002409 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (51/50 : ℝ))
    (x := (1/101 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.019802627296177 : ℝ) : ℝ) ≤ log (51/50) ∧
      log (51/50) ≤ ((0.0198026272961958 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((459/100 : ℝ)) = log ((9/2 : ℝ)) + log (51/50) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (51/50 : ℝ) = (459/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (23/5)`, from `log 9/2` and the ratio `46/45`. -/
private theorem log_23_5 :
    (1.526056303483 : ℝ) ≤ log ((23/5 : ℝ)) ∧ log ((23/5 : ℝ)) ≤ (1.526056303512 : ℝ) := by
  have hA := log_9_2
  have hB := log_enclosure (y := (46/45 : ℝ))
    (x := (1/91 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0219789067187697 : ℝ) : ℝ) ≤ log (46/45) ∧
      log (46/45) ≤ ((0.0219789067188085 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((23/5 : ℝ)) = log ((9/2 : ℝ)) + log (46/45) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((9/2 : ℝ)) * (46/45 : ℝ) = (23/5 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (7/2)`, from `log 17/5` and the ratio `35/34`. -/
private theorem log_7_2 :
    (1.252762968492 : ℝ) ≤ log ((7/2 : ℝ)) ∧ log ((7/2 : ℝ)) ≤ (1.252762968504 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (35/34 : ℝ))
    (x := (1/69 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0289875368732139 : ℝ) : ℝ) ≤ log (35/34) ∧
      log (35/34) ≤ ((0.0289875368734826 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((7/2 : ℝ)) = log ((17/5 : ℝ)) + log (35/34) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (35/34 : ℝ) = (7/2 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (351/100)`, from `log 17/5` and the ratio `351/340`. -/
private theorem log_351_100 :
    (1.255616037474 : ℝ) ≤ log ((351/100 : ℝ)) ∧ log ((351/100 : ℝ)) ≤ (1.255616037487 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (351/340 : ℝ))
    (x := (11/691 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0318406058555847 : ℝ) : ℝ) ≤ log (351/340) ∧
      log (351/340) ≤ ((0.031840605856103 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((351/100 : ℝ)) = log ((17/5 : ℝ)) + log (351/340) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (351/340 : ℝ) = (351/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (88/25)`, from `log 17/5` and the ratio `88/85`. -/
private theorem log_88_25 :
    (1.258460989606 : ℝ) ≤ log ((88/25 : ℝ)) ∧ log ((88/25 : ℝ)) ≤ (1.258460989619 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (88/85 : ℝ))
    (x := (3/173 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0346855579877552 : ℝ) : ℝ) ≤ log (88/85) ∧
      log (88/85) ≤ ((0.0346855579886987 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((88/25 : ℝ)) = log ((17/5 : ℝ)) + log (88/85) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (88/85 : ℝ) = (88/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (353/100)`, from `log 17/5` and the ratio `353/340`. -/
private theorem log_353_100 :
    (1.261297870941 : ℝ) ≤ log ((353/100 : ℝ)) ∧ log ((353/100 : ℝ)) ≤ (1.261297870955 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (353/340 : ℝ))
    (x := (13/693 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.037522439322856 : ℝ) : ℝ) ≤ log (353/340) ∧
      log (353/340) ≤ ((0.0375224393244916 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((353/100 : ℝ)) = log ((17/5 : ℝ)) + log (353/340) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (353/340 : ℝ) = (353/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (177/50)`, from `log 17/5` and the ratio `177/170`. -/
private theorem log_177_50 :
    (1.264126727142 : ℝ) ≤ log ((177/50 : ℝ)) ∧ log ((177/50 : ℝ)) ≤ (1.264126727156 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (177/170 : ℝ))
    (x := (7/347 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0403512955231788 : ℝ) : ℝ) ≤ log (177/170) ∧
      log (177/170) ≤ ((0.040351295525899 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((177/50 : ℝ)) = log ((17/5 : ℝ)) + log (177/170) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (177/170 : ℝ) = (177/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (71/20)`, from `log 17/5` and the ratio `71/68`. -/
private theorem log_71_20 :
    (1.266947603483 : ℝ) ≤ log ((71/20 : ℝ)) ∧ log ((71/20 : ℝ)) ≤ (1.266947603499 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (71/68 : ℝ))
    (x := (3/139 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0431721718645852 : ℝ) : ℝ) ≤ log (71/68) ∧
      log (71/68) ≤ ((0.0431721718689502 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((71/20 : ℝ)) = log ((17/5 : ℝ)) + log (71/68) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (71/68 : ℝ) = (71/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (89/25)`, from `log 17/5` and the ratio `89/85`. -/
private theorem log_89_25 :
    (1.269760544859 : ℝ) ≤ log ((89/25 : ℝ)) ∧ log ((89/25 : ℝ)) ≤ (1.269760544878 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (89/85 : ℝ))
    (x := (2/87 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0459851132408535 : ℝ) : ℝ) ≤ log (89/85) ∧
      log (89/85) ≤ ((0.0459851132476431 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((89/25 : ℝ)) = log ((17/5 : ℝ)) + log (89/85) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (89/85 : ℝ) = (89/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (357/100)`, from `log 17/5` and the ratio `21/20`. -/
private theorem log_357_100 :
    (1.272565595786 : ℝ) ≤ log ((357/100 : ℝ)) ∧ log ((357/100 : ℝ)) ≤ (1.272565595809 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (21/20 : ℝ))
    (x := (1/41 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0487901641679642 : ℝ) : ℝ) ≤ log (21/20) ∧
      log (21/20) ≤ ((0.0487901641782398 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((357/100 : ℝ)) = log ((17/5 : ℝ)) + log (21/20) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (21/20 : ℝ) = (357/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (179/50)`, from `log 17/5` and the ratio `179/170`. -/
private theorem log_179_50 :
    (1.275362800407 : ℝ) ≤ log ((179/50 : ℝ)) ∧ log ((179/50 : ℝ)) ≤ (1.275362800434 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (179/170 : ℝ))
    (x := (9/349 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0515873687883251 : ℝ) : ℝ) ≤ log (179/170) ∧
      log (179/170) ≤ ((0.051587368803504 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((179/50 : ℝ)) = log ((17/5 : ℝ)) + log (179/170) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (179/170 : ℝ) = (179/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (359/100)`, from `log 17/5` and the ratio `359/340`. -/
private theorem log_359_100 :
    (1.278152202493 : ℝ) ≤ log ((359/100 : ℝ)) ∧ log ((359/100 : ℝ)) ≤ (1.278152202527 : ℝ) := by
  have hA := log_17_5
  have hB := log_enclosure (y := (359/340 : ℝ))
    (x := (19/699 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0543767708749376 : ℝ) : ℝ) ≤ log (359/340) ∧
      log (359/340) ≤ ((0.0543767708968802 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((359/100 : ℝ)) = log ((17/5 : ℝ)) + log (359/340) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((17/5 : ℝ)) * (359/340 : ℝ) = (359/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (26/25)` from the atanh series. -/
private theorem log_26_25 :
    (0.03922071315328 : ℝ) ≤ log ((26/25 : ℝ)) ∧ log ((26/25 : ℝ)) ≤ (0.03922071315329 : ℝ) := by
  have h := log_enclosure (y := (26/25 : ℝ))
    (x := (1/51 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 4
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (251/250)` from the atanh series. -/
private theorem log_251_250 :
    (0.00399202126953 : ℝ) ≤ log ((251/250 : ℝ)) ∧ log ((251/250 : ℝ)) ≤ (0.00399202126954 : ℝ) := by
  have h := log_enclosure (y := (251/250 : ℝ))
    (x := (1/501 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (252/251)` from the atanh series. -/
private theorem log_252_251 :
    (0.00397614837963 : ℝ) ≤ log ((252/251 : ℝ)) ∧ log ((252/251 : ℝ)) ≤ (0.00397614837964 : ℝ) := by
  have h := log_enclosure (y := (252/251 : ℝ))
    (x := (1/503 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (253/252)` from the atanh series. -/
private theorem log_253_252 :
    (0.00396040121609 : ℝ) ≤ log ((253/252 : ℝ)) ∧ log ((253/252 : ℝ)) ≤ (0.0039604012161 : ℝ) := by
  have h := log_enclosure (y := (253/252 : ℝ))
    (x := (1/505 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (254/253)` from the atanh series. -/
private theorem log_254_253 :
    (0.00394477829101 : ℝ) ≤ log ((254/253 : ℝ)) ∧ log ((254/253 : ℝ)) ≤ (0.00394477829102 : ℝ) := by
  have h := log_enclosure (y := (254/253 : ℝ))
    (x := (1/507 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (255/254)` from the atanh series. -/
private theorem log_255_254 :
    (0.00392927813988 : ℝ) ≤ log ((255/254 : ℝ)) ∧ log ((255/254 : ℝ)) ≤ (0.00392927813989 : ℝ) := by
  have h := log_enclosure (y := (255/254 : ℝ))
    (x := (1/509 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (256/255)` from the atanh series. -/
private theorem log_256_255 :
    (0.00391389932113 : ℝ) ≤ log ((256/255 : ℝ)) ∧ log ((256/255 : ℝ)) ≤ (0.00391389932114 : ℝ) := by
  have h := log_enclosure (y := (256/255 : ℝ))
    (x := (1/511 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (257/256)` from the atanh series. -/
private theorem log_257_256 :
    (0.00389864041565 : ℝ) ≤ log ((257/256 : ℝ)) ∧ log ((257/256 : ℝ)) ≤ (0.00389864041566 : ℝ) := by
  have h := log_enclosure (y := (257/256 : ℝ))
    (x := (1/513 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (258/257)` from the atanh series. -/
private theorem log_258_257 :
    (0.00388350002639 : ℝ) ≤ log ((258/257 : ℝ)) ∧ log ((258/257 : ℝ)) ≤ (0.0038835000264 : ℝ) := by
  have h := log_enclosure (y := (258/257 : ℝ))
    (x := (1/515 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (259/258)` from the atanh series. -/
private theorem log_259_258 :
    (0.00386847677792 : ℝ) ≤ log ((259/258 : ℝ)) ∧ log ((259/258 : ℝ)) ≤ (0.00386847677793 : ℝ) := by
  have h := log_enclosure (y := (259/258 : ℝ))
    (x := (1/517 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (260/259)` from the atanh series. -/
private theorem log_260_259 :
    (0.00385356931598 : ℝ) ≤ log ((260/259 : ℝ)) ∧ log ((260/259 : ℝ)) ≤ (0.00385356931599 : ℝ) := by
  have h := log_enclosure (y := (260/259 : ℝ))
    (x := (1/519 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `sigma 3 (9/2) (7/2)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_450_100 :
    (0.11054960304 : ℝ) ≤ Wu04Integral.sigma 3 ((9/2 : ℝ)) ((7/2 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (9/2 : ℝ)) (c := (7/2 : ℝ)) (m := (11/4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((9/2 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((9/2 : ℝ)) - 1) = (7/2 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (7/2 : ℝ)) (m := (11/4 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.405465108095 : ℝ) ≤ log ((9/2 : ℝ)) - log 3 := by
    linarith [log_9_2.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((7/2 : ℝ)) := by linarith [log_7_2.1]
  have hp : (0 : ℝ) ≤ (0.405465108095 : ℝ) := by norm_num
  have hlo' : (0.50795167243702185914 : ℝ) ≤ log ((7/2 : ℝ)) * (log ((9/2 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_7_2.1 hdiff_lo hp hq
    have hc : (0.50795167243702185914 : ℝ) ≤ (1.252762968492 : ℝ) * (0.405465108095 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_7_2.1, log_7_2.2, log_9_2.1, log_9_2.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((5/2 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_250_100 :
    (0.133464595165 : ℝ) ≤ Wu04Integral.sigma0 ((5/2 : ℝ)) := by
  have h := sigma_c4_450_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((5/2 : ℝ)) + 2 = (9/2 : ℝ) by norm_num, show ((5/2 : ℝ)) + 1 = (7/2 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.133464595165 : ℝ) : ℝ) ≤ ((0.11054960304 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.11054960304 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (451/100) (351/100)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_451_100 :
    (0.111709586168 : ℝ) ≤ Wu04Integral.sigma 3 ((451/100 : ℝ)) ((351/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (451/100 : ℝ)) (c := (351/100 : ℝ)) (m := (551/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((451/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((451/100 : ℝ)) - 1) = (351/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (351/100 : ℝ)) (m := (551/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.407684864833 : ℝ) ≤ log ((451/100 : ℝ)) - log 3 := by
    linarith [log_451_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((351/100 : ℝ)) := by linarith [log_351_100.1]
  have hp : (0 : ℝ) ≤ (0.407684864833 : ℝ) := by norm_num
  have hlo' : (0.51189565451973475275 : ℝ) ≤ log ((351/100 : ℝ)) * (log ((451/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_351_100.1 hdiff_lo hp hq
    have hc : (0.51189565451973475275 : ℝ) ≤ (1.255616037474 : ℝ) * (0.407684864833 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_351_100.1, log_351_100.2, log_451_100.1, log_451_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((251/100 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_251_100 :
    (0.134865022433 : ℝ) ≤ Wu04Integral.sigma0 ((251/100 : ℝ)) := by
  have h := sigma_c4_451_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((251/100 : ℝ)) + 2 = (451/100 : ℝ) by norm_num, show ((251/100 : ℝ)) + 1 = (351/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.134865022433 : ℝ) : ℝ) ≤ ((0.111709586168 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.111709586168 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (113/25) (88/25)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_452_100 :
    (0.112872577132 : ℝ) ≤ Wu04Integral.sigma 3 ((113/25 : ℝ)) ((88/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (113/25 : ℝ)) (c := (88/25 : ℝ)) (m := (69/25 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((113/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((113/25 : ℝ)) - 1) = (88/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (88/25 : ℝ)) (m := (69/25 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.409899705162 : ℝ) ≤ log ((113/25 : ℝ)) - log 3 := by
    linarith [log_113_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((88/25 : ℝ)) := by linarith [log_88_25.1]
  have hp : (0 : ℝ) ≤ (0.409899705162 : ℝ) := by norm_num
  have hlo' : (0.51584278859737814654 : ℝ) ≤ log ((88/25 : ℝ)) * (log ((113/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_88_25.1 hdiff_lo hp hq
    have hc : (0.51584278859737814654 : ℝ) ≤ (1.258460989606 : ℝ) * (0.409899705162 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_88_25.1, log_88_25.2, log_113_25.1, log_113_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((63/25 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_252_100 :
    (0.136269081009 : ℝ) ≤ Wu04Integral.sigma0 ((63/25 : ℝ)) := by
  have h := sigma_c4_452_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((63/25 : ℝ)) + 2 = (113/25 : ℝ) by norm_num, show ((63/25 : ℝ)) + 1 = (88/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.136269081009 : ℝ) : ℝ) ≤ ((0.112872577132 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.112872577132 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (453/100) (353/100)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_453_100 :
    (0.114038544943 : ℝ) ≤ Wu04Integral.sigma 3 ((453/100 : ℝ)) ((353/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (453/100 : ℝ)) (c := (353/100 : ℝ)) (m := (553/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((453/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((453/100 : ℝ)) - 1) = (353/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (353/100 : ℝ)) (m := (553/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.412109650813 : ℝ) ≤ log ((453/100 : ℝ)) - log 3 := by
    linarith [log_453_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((353/100 : ℝ)) := by linarith [log_353_100.1]
  have hp : (0 : ℝ) ≤ (0.412109650813 : ℝ) := by norm_num
  have hlo' : (0.51979302516467584972 : ℝ) ≤ log ((353/100 : ℝ)) * (log ((453/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_353_100.1 hdiff_lo hp hq
    have hc : (0.51979302516467584972 : ℝ) ≤ (1.261297870941 : ℝ) * (0.412109650813 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_353_100.1, log_353_100.2, log_453_100.1, log_453_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((253/100 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_253_100 :
    (0.13767673348 : ℝ) ≤ Wu04Integral.sigma0 ((253/100 : ℝ)) := by
  have h := sigma_c4_453_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((253/100 : ℝ)) + 2 = (453/100 : ℝ) by norm_num, show ((253/100 : ℝ)) + 1 = (353/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.13767673348 : ℝ) : ℝ) ≤ ((0.114038544943 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.114038544943 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (227/50) (177/50)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_454_100 :
    (0.115207458932 : ℝ) ≤ Wu04Integral.sigma 3 ((227/50 : ℝ)) ((177/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (227/50 : ℝ)) (c := (177/50 : ℝ)) (m := (277/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((227/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((227/50 : ℝ)) - 1) = (177/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (177/50 : ℝ)) (m := (277/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.414314723371 : ℝ) ≤ log ((227/50 : ℝ)) - log 3 := by
    linarith [log_227_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((177/50 : ℝ)) := by linarith [log_177_50.1]
  have hp : (0 : ℝ) ≤ (0.414314723371 : ℝ) := by norm_num
  have hlo' : (0.52374631526172532743 : ℝ) ≤ log ((177/50 : ℝ)) * (log ((227/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_177_50.1 hdiff_lo hp hq
    have hc : (0.52374631526172532743 : ℝ) ≤ (1.264126727142 : ℝ) * (0.414314723371 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_177_50.1, log_177_50.2, log_227_50.1, log_227_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((127/50 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_254_100 :
    (0.13908794282 : ℝ) ≤ Wu04Integral.sigma0 ((127/50 : ℝ)) := by
  have h := sigma_c4_454_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((127/50 : ℝ)) + 2 = (227/50 : ℝ) by norm_num, show ((127/50 : ℝ)) + 1 = (177/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.13908794282 : ℝ) : ℝ) ≤ ((0.115207458932 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.115207458932 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (91/20) (71/20)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_455_100 :
    (0.116379288752 : ℝ) ≤ Wu04Integral.sigma 3 ((91/20 : ℝ)) ((71/20 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (91/20 : ℝ)) (c := (71/20 : ℝ)) (m := (111/40 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((91/20 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((91/20 : ℝ)) - 1) = (71/20 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (71/20 : ℝ)) (m := (111/40 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.416514944281 : ℝ) ≤ log ((91/20 : ℝ)) - log 3 := by
    linarith [log_91_20.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((71/20 : ℝ)) := by linarith [log_71_20.1]
  have hp : (0 : ℝ) ≤ (0.416514944281 : ℝ) := by norm_num
  have hlo' : (0.52770261047166822653 : ℝ) ≤ log ((71/20 : ℝ)) * (log ((91/20 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_71_20.1 hdiff_lo hp hq
    have hc : (0.52770261047166822653 : ℝ) ≤ (1.266947603483 : ℝ) * (0.416514944281 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_71_20.1, log_71_20.2, log_91_20.1, log_91_20.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((51/20 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_255_100 :
    (0.140502672391 : ℝ) ≤ Wu04Integral.sigma0 ((51/20 : ℝ)) := by
  have h := sigma_c4_455_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((51/20 : ℝ)) + 2 = (91/20 : ℝ) by norm_num, show ((51/20 : ℝ)) + 1 = (71/20 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.140502672391 : ℝ) : ℝ) ≤ ((0.116379288752 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.116379288752 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (114/25) (89/25)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_456_100 :
    (0.117554004371 : ℝ) ≤ Wu04Integral.sigma 3 ((114/25 : ℝ)) ((89/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (114/25 : ℝ)) (c := (89/25 : ℝ)) (m := (139/50 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((114/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((114/25 : ℝ)) - 1) = (89/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (89/25 : ℝ)) (m := (139/50 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.418710334845 : ℝ) ≤ log ((114/25 : ℝ)) - log 3 := by
    linarith [log_114_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((89/25 : ℝ)) := by linarith [log_89_25.1]
  have hp : (0 : ℝ) ≤ (0.418710334845 : ℝ) := by norm_num
  have hlo' : (0.53166186291088153331 : ℝ) ≤ log ((89/25 : ℝ)) * (log ((114/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_89_25.1 hdiff_lo hp hq
    have hc : (0.53166186291088153331 : ℝ) ≤ (1.269760544859 : ℝ) * (0.418710334845 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_89_25.1, log_89_25.2, log_114_25.1, log_114_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((64/25 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_256_100 :
    (0.141920885937 : ℝ) ≤ Wu04Integral.sigma0 ((64/25 : ℝ)) := by
  have h := sigma_c4_456_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((64/25 : ℝ)) + 2 = (114/25 : ℝ) by norm_num, show ((64/25 : ℝ)) + 1 = (89/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.141920885937 : ℝ) : ℝ) ≤ ((0.117554004371 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.117554004371 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (457/100) (357/100)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_457_100 :
    (0.118731576069 : ℝ) ≤ Wu04Integral.sigma 3 ((457/100 : ℝ)) ((357/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (457/100 : ℝ)) (c := (357/100 : ℝ)) (m := (557/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((457/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((457/100 : ℝ)) - 1) = (357/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (357/100 : ℝ)) (m := (557/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.420900916224 : ℝ) ≤ log ((457/100 : ℝ)) - log 3 := by
    linarith [log_457_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((357/100 : ℝ)) := by linarith [log_357_100.1]
  have hp : (0 : ℝ) ≤ (0.420900916224 : ℝ) := by norm_num
  have hlo' : (0.53562402522146783343 : ℝ) ≤ log ((357/100 : ℝ)) * (log ((457/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_357_100.1 hdiff_lo hp hq
    have hc : (0.53562402522146783343 : ℝ) ≤ (1.272565595786 : ℝ) * (0.420900916224 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_357_100.1, log_357_100.2, log_457_100.1, log_457_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((257/100 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_257_100 :
    (0.143342547577 : ℝ) ≤ Wu04Integral.sigma0 ((257/100 : ℝ)) := by
  have h := sigma_c4_457_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((257/100 : ℝ)) + 2 = (457/100 : ℝ) by norm_num, show ((257/100 : ℝ)) + 1 = (357/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.143342547577 : ℝ) : ℝ) ≤ ((0.118731576069 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.118731576069 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (229/50) (179/50)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_458_100 :
    (0.119911974436 : ℝ) ≤ Wu04Integral.sigma 3 ((229/50 : ℝ)) ((179/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (229/50 : ℝ)) (c := (179/50 : ℝ)) (m := (279/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((229/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((229/50 : ℝ)) - 1) = (179/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (179/50 : ℝ)) (m := (279/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.423086709444 : ℝ) ≤ log ((229/50 : ℝ)) - log 3 := by
    linarith [log_229_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((179/50 : ℝ)) := by linarith [log_179_50.1]
  have hp : (0 : ℝ) ≤ (0.423086709444 : ℝ) := by norm_num
  have hlo' : (0.53958905057148257394 : ℝ) ≤ log ((179/50 : ℝ)) * (log ((229/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_179_50.1 hdiff_lo hp hq
    have hc : (0.53958905057148257394 : ℝ) ≤ (1.275362800407 : ℝ) * (0.423086709444 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_179_50.1, log_179_50.2, log_229_50.1, log_229_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((129/50 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_258_100 :
    (0.144767621805 : ℝ) ≤ Wu04Integral.sigma0 ((129/50 : ℝ)) := by
  have h := sigma_c4_458_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((129/50 : ℝ)) + 2 = (229/50 : ℝ) by norm_num, show ((129/50 : ℝ)) + 1 = (179/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.144767621805 : ℝ) : ℝ) ≤ ((0.119911974436 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.119911974436 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (459/100) (359/100)` at the left end of a `[5/2, 13/5]` panel of `entry_i_2`. -/
private theorem sigma_c4_459_100 :
    (0.121095170363 : ℝ) ≤ Wu04Integral.sigma 3 ((459/100 : ℝ)) ((359/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (459/100 : ℝ)) (c := (359/100 : ℝ)) (m := (559/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((459/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((459/100 : ℝ)) - 1) = (359/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (359/100 : ℝ)) (m := (559/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.425267735391 : ℝ) ≤ log ((459/100 : ℝ)) - log 3 := by
    linarith [log_459_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((359/100 : ℝ)) := by linarith [log_359_100.1]
  have hp : (0 : ℝ) ≤ (0.425267735391 : ℝ) := by norm_num
  have hlo' : (0.54355689263921697452 : ℝ) ≤ log ((359/100 : ℝ)) * (log ((459/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_359_100.1 hdiff_lo hp hq
    have hc : (0.54355689263921697452 : ℝ) ≤ (1.278152202493 : ℝ) * (0.425267735391 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_359_100.1, log_359_100.2, log_459_100.1, log_459_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((259/100 : ℝ))` at a `[5/2, 13/5]` panel endpoint. -/
private theorem sigma0_c4_259_100 :
    (0.146196073478 : ℝ) ≤ Wu04Integral.sigma0 ((259/100 : ℝ)) := by
  have h := sigma_c4_459_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((259/100 : ℝ)) + 2 = (459/100 : ℝ) by norm_num, show ((259/100 : ℝ)) + 1 = (359/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.146196073478 : ℝ) : ℝ) ≤ ((0.121095170363 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.121095170363 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
/-- Lower bound of `sigma0' ((5/2 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_250_100 :
    (0.1398602592 : ℝ) ≤
      (log (((5/2 : ℝ) + 2) / 3) / ((5/2 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_9_2
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.405465108095 : ℝ) ≤ log ((9/2 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((5/2 : ℝ) + 2) / 3) = ((9/2 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1398602592 : ℝ)
      ≤ (0.405465108095 : ℝ) / (((5/2 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((9/2 : ℝ)) - log 3) / (((5/2 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((9/2 : ℝ)) - log 3) / (((5/2 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((251/100 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_251_100 :
    (0.1402252936 : ℝ) ≤
      (log (((251/100 : ℝ) + 2) / 3) / ((251/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_451_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.407684864833 : ℝ) ≤ log ((451/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((251/100 : ℝ) + 2) / 3) = ((451/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1402252936 : ℝ)
      ≤ (0.407684864833 : ℝ) / (((251/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((451/100 : ℝ)) - log 3) / (((251/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((451/100 : ℝ)) - log 3) / (((251/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((63/25 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_252_100 :
    (0.1405865678 : ℝ) ≤
      (log (((63/25 : ℝ) + 2) / 3) / ((63/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_113_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.409899705162 : ℝ) ≤ log ((113/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((63/25 : ℝ) + 2) / 3) = ((113/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1405865678 : ℝ)
      ≤ (0.409899705162 : ℝ) / (((63/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((113/25 : ℝ)) - log 3) / (((63/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((113/25 : ℝ)) - log 3) / (((63/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((253/100 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_253_100 :
    (0.140944121 : ℝ) ≤
      (log (((253/100 : ℝ) + 2) / 3) / ((253/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_453_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.412109650813 : ℝ) ≤ log ((453/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((253/100 : ℝ) + 2) / 3) = ((453/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.140944121 : ℝ)
      ≤ (0.412109650813 : ℝ) / (((253/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((453/100 : ℝ)) - log 3) / (((253/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((453/100 : ℝ)) - log 3) / (((253/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((127/50 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_254_100 :
    (0.1412979922 : ℝ) ≤
      (log (((127/50 : ℝ) + 2) / 3) / ((127/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_227_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.414314723371 : ℝ) ≤ log ((227/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((127/50 : ℝ) + 2) / 3) = ((227/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1412979922 : ℝ)
      ≤ (0.414314723371 : ℝ) / (((127/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((227/50 : ℝ)) - log 3) / (((127/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((227/50 : ℝ)) - log 3) / (((127/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((51/20 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_255_100 :
    (0.1416482199 : ℝ) ≤
      (log (((51/20 : ℝ) + 2) / 3) / ((51/20 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_91_20
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.416514944281 : ℝ) ≤ log ((91/20 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((51/20 : ℝ) + 2) / 3) = ((91/20 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1416482199 : ℝ)
      ≤ (0.416514944281 : ℝ) / (((51/20 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((91/20 : ℝ)) - log 3) / (((51/20 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((91/20 : ℝ)) - log 3) / (((51/20 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((64/25 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_256_100 :
    (0.1419948419 : ℝ) ≤
      (log (((64/25 : ℝ) + 2) / 3) / ((64/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_114_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.418710334845 : ℝ) ≤ log ((114/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((64/25 : ℝ) + 2) / 3) = ((114/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1419948419 : ℝ)
      ≤ (0.418710334845 : ℝ) / (((64/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((114/25 : ℝ)) - log 3) / (((64/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((114/25 : ℝ)) - log 3) / (((64/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((257/100 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_257_100 :
    (0.1423378957 : ℝ) ≤
      (log (((257/100 : ℝ) + 2) / 3) / ((257/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_457_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.420900916224 : ℝ) ≤ log ((457/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((257/100 : ℝ) + 2) / 3) = ((457/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1423378957 : ℝ)
      ≤ (0.420900916224 : ℝ) / (((257/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((457/100 : ℝ)) - log 3) / (((257/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((457/100 : ℝ)) - log 3) / (((257/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((129/50 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_258_100 :
    (0.1426774182 : ℝ) ≤
      (log (((129/50 : ℝ) + 2) / 3) / ((129/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_229_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.423086709444 : ℝ) ≤ log ((229/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((129/50 : ℝ) + 2) / 3) = ((229/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1426774182 : ℝ)
      ≤ (0.423086709444 : ℝ) / (((129/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((229/50 : ℝ)) - log 3) / (((129/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((229/50 : ℝ)) - log 3) / (((129/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((259/100 : ℝ))`, the tangent slope of a `[5/2, 13/5]` panel. -/
private theorem sigma0_deriv_lower_c4_259_100 :
    (0.1430134461 : ℝ) ≤
      (log (((259/100 : ℝ) + 2) / 3) / ((259/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_459_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.425267735391 : ℝ) ≤ log ((459/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((259/100 : ℝ) + 2) / 3) = ((459/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1430134461 : ℝ)
      ≤ (0.425267735391 : ℝ) / (((259/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((459/100 : ℝ)) - log 3) / (((259/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((459/100 : ℝ)) - log 3) / (((259/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Second-order panel 0 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_0 :
    (0.0002677928407195 : ℝ) ≤ ∫ t in (5/2 : ℝ)..(251/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (5/2 : ℝ)) (b := (251/100 : ℝ)) (A := (0.133464595165 : ℝ))
    (B := (0.1398602592 : ℝ)) (C := (0.01813324068597 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_250_100) (sigma0_deriv_lower_c4_250_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.506297153532 : ℝ) := by
        have hle : s + 2 ≤ (451/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_451_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.506297153532 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((5/2 : ℝ) + 2) * ((5/2 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((5/2 : ℝ) + 2) * ((5/2 : ℝ) + 1) = ((5/2 : ℝ) + 1) / ((5/2 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.37009291290577777777 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((351/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((351/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (351/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01813324068597 : ℝ))) ≤ (0.37009291290577777777 : ℝ) / (((351/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.37009291290577777777 : ℝ) / (((351/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.37009291290577777777 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.37009291290577777777 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_251_250
  rw [show ((251/100 : ℝ)) / ((5/2 : ℝ)) = (251/250 : ℝ) by norm_num] at hp
  have hX : ((0.133464595165 : ℝ) - (0.1398602592 : ℝ) * (5/2 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.133464595165 : ℝ) - (0.1398602592 : ℝ) * (5/2 : ℝ)) * log (251/250) ≥
      (((0.133464595165 : ℝ) - (0.1398602592 : ℝ) * (5/2 : ℝ))) * (0.00399202126954 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01813324068597 : ℝ) * (5/2 : ℝ) ^ 2) * log (251/250) ≥
      ((0.01813324068597 : ℝ) * (5/2 : ℝ) ^ 2) * (0.00399202126953 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 1 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_1 :
    (0.0002695158260376 : ℝ) ≤ ∫ t in (251/100 : ℝ)..(63/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (251/100 : ℝ)) (b := (63/25 : ℝ)) (A := (0.134865022433 : ℝ))
    (B := (0.1402252936 : ℝ)) (C := (0.01794645880021 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_251_100) (sigma0_deriv_lower_c4_251_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.508511993861 : ℝ) := by
        have hle : s + 2 ≤ (113/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_113_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.508511993861 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((251/100 : ℝ) + 2) * ((251/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((251/100 : ℝ) + 2) * ((251/100 : ℝ) + 1) = ((251/100 : ℝ) + 1) / ((251/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.36837080477682705099 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((88/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((88/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (88/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01794645880021 : ℝ))) ≤ (0.36837080477682705099 : ℝ) / (((88/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.36837080477682705099 : ℝ) / (((88/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.36837080477682705099 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.36837080477682705099 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_252_251
  rw [show ((63/25 : ℝ)) / ((251/100 : ℝ)) = (252/251 : ℝ) by norm_num] at hp
  have hX : ((0.134865022433 : ℝ) - (0.1402252936 : ℝ) * (251/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.134865022433 : ℝ) - (0.1402252936 : ℝ) * (251/100 : ℝ)) * log (252/251) ≥
      (((0.134865022433 : ℝ) - (0.1402252936 : ℝ) * (251/100 : ℝ))) * (0.00397614837964 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01794645880021 : ℝ) * (251/100 : ℝ) ^ 2) * log (252/251) ≥
      ((0.01794645880021 : ℝ) * (251/100 : ℝ) ^ 2) * (0.00397614837963 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 2 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_2 :
    (0.0002712323175541 : ℝ) ≤ ∫ t in (63/25 : ℝ)..(253/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (63/25 : ℝ)) (b := (253/100 : ℝ)) (A := (0.136269081009 : ℝ))
    (B := (0.1405865678 : ℝ)) (C := (0.01776163087844 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_252_100) (sigma0_deriv_lower_c4_252_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.510721939512 : ℝ) := by
        have hle : s + 2 ≤ (453/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_453_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.510721939512 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((63/25 : ℝ) + 2) * ((63/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((63/25 : ℝ) + 2) * ((63/25 : ℝ) + 1) = ((63/25 : ℝ) + 1) / ((63/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.36665141109490265486 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((353/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((353/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (353/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01776163087844 : ℝ))) ≤ (0.36665141109490265486 : ℝ) / (((353/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.36665141109490265486 : ℝ) / (((353/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.36665141109490265486 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.36665141109490265486 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_253_252
  rw [show ((253/100 : ℝ)) / ((63/25 : ℝ)) = (253/252 : ℝ) by norm_num] at hp
  have hX : ((0.136269081009 : ℝ) - (0.1405865678 : ℝ) * (63/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.136269081009 : ℝ) - (0.1405865678 : ℝ) * (63/25 : ℝ)) * log (253/252) ≥
      (((0.136269081009 : ℝ) - (0.1405865678 : ℝ) * (63/25 : ℝ))) * (0.0039604012161 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01776163087844 : ℝ) * (63/25 : ℝ) ^ 2) * log (253/252) ≥
      ((0.01776163087844 : ℝ) * (63/25 : ℝ) ^ 2) * (0.00396040121609 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 3 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_3 :
    (0.0002729423187109 : ℝ) ≤ ∫ t in (253/100 : ℝ)..(127/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (253/100 : ℝ)) (b := (127/50 : ℝ)) (A := (0.13767673348 : ℝ))
    (B := (0.140944121 : ℝ)) (C := (0.01757873244808 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_253_100) (sigma0_deriv_lower_c4_253_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.51292701207 : ℝ) := by
        have hle : s + 2 ≤ (227/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_227_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.51292701207 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((253/100 : ℝ) + 2) * ((253/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((253/100 : ℝ) + 2) * ((253/100 : ℝ) + 1) = ((253/100 : ℝ) + 1) / ((253/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.36493472471362030905 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((177/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((177/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (177/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01757873244808 : ℝ))) ≤ (0.36493472471362030905 : ℝ) / (((177/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.36493472471362030905 : ℝ) / (((177/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.36493472471362030905 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.36493472471362030905 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_254_253
  rw [show ((127/50 : ℝ)) / ((253/100 : ℝ)) = (254/253 : ℝ) by norm_num] at hp
  have hX : ((0.13767673348 : ℝ) - (0.140944121 : ℝ) * (253/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.13767673348 : ℝ) - (0.140944121 : ℝ) * (253/100 : ℝ)) * log (254/253) ≥
      (((0.13767673348 : ℝ) - (0.140944121 : ℝ) * (253/100 : ℝ))) * (0.00394477829102 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01757873244808 : ℝ) * (253/100 : ℝ) ^ 2) * log (254/253) ≥
      ((0.01757873244808 : ℝ) * (253/100 : ℝ) ^ 2) * (0.00394477829101 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 4 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_4 :
    (0.0002746458336541 : ℝ) ≤ ∫ t in (127/50 : ℝ)..(51/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (127/50 : ℝ)) (b := (51/20 : ℝ)) (A := (0.13908794282 : ℝ))
    (B := (0.1412979922 : ℝ)) (C := (0.01739773940185 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_254_100) (sigma0_deriv_lower_c4_254_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.51512723298 : ℝ) := by
        have hle : s + 2 ≤ (91/20 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_91_20.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.51512723298 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((127/50 : ℝ) + 2) * ((127/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((127/50 : ℝ) + 2) * ((127/50 : ℝ) + 1) = ((127/50 : ℝ) + 1) / ((127/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.36322073849938325991 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((71/20 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((71/20 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (71/20 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01739773940185 : ℝ))) ≤ (0.36322073849938325991 : ℝ) / (((71/20 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.36322073849938325991 : ℝ) / (((71/20 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.36322073849938325991 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.36322073849938325991 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_255_254
  rw [show ((51/20 : ℝ)) / ((127/50 : ℝ)) = (255/254 : ℝ) by norm_num] at hp
  have hX : ((0.13908794282 : ℝ) - (0.1412979922 : ℝ) * (127/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.13908794282 : ℝ) - (0.1412979922 : ℝ) * (127/50 : ℝ)) * log (255/254) ≥
      (((0.13908794282 : ℝ) - (0.1412979922 : ℝ) * (127/50 : ℝ))) * (0.00392927813989 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01739773940185 : ℝ) * (127/50 : ℝ) ^ 2) * log (255/254) ≥
      ((0.01739773940185 : ℝ) * (127/50 : ℝ) ^ 2) * (0.00392927813988 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 5 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_5 :
    (0.0002763428672184 : ℝ) ≤ ∫ t in (51/20 : ℝ)..(64/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (51/20 : ℝ)) (b := (64/25 : ℝ)) (A := (0.140502672391 : ℝ))
    (B := (0.1416482199 : ℝ)) (C := (0.01721862799154 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_255_100) (sigma0_deriv_lower_c4_255_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.517322623544 : ℝ) := by
        have hle : s + 2 ≤ (114/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_114_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.517322623544 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((51/20 : ℝ) + 2) * ((51/20 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((51/20 : ℝ) + 2) * ((51/20 : ℝ) + 1) = ((51/20 : ℝ) + 1) / ((51/20 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.36150944533578021978 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((89/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((89/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (89/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01721862799154 : ℝ))) ≤ (0.36150944533578021978 : ℝ) / (((89/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.36150944533578021978 : ℝ) / (((89/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.36150944533578021978 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.36150944533578021978 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_256_255
  rw [show ((64/25 : ℝ)) / ((51/20 : ℝ)) = (256/255 : ℝ) by norm_num] at hp
  have hX : ((0.140502672391 : ℝ) - (0.1416482199 : ℝ) * (51/20 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.140502672391 : ℝ) - (0.1416482199 : ℝ) * (51/20 : ℝ)) * log (256/255) ≥
      (((0.140502672391 : ℝ) - (0.1416482199 : ℝ) * (51/20 : ℝ))) * (0.00391389932114 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01721862799154 : ℝ) * (51/20 : ℝ) ^ 2) * log (256/255) ≥
      ((0.01721862799154 : ℝ) * (51/20 : ℝ) ^ 2) * (0.00391389932113 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 6 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_6 :
    (0.0002780334249023 : ℝ) ≤ ∫ t in (64/25 : ℝ)..(257/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (64/25 : ℝ)) (b := (257/100 : ℝ)) (A := (0.141920885937 : ℝ))
    (B := (0.1419948419 : ℝ)) (C := (0.01704137482177 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_256_100) (sigma0_deriv_lower_c4_256_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.519513204923 : ℝ) := by
        have hle : s + 2 ≤ (457/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_457_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.519513204923 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((64/25 : ℝ) + 2) * ((64/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((64/25 : ℝ) + 2) * ((64/25 : ℝ) + 1) = ((64/25 : ℝ) + 1) / ((64/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.35980083812296491228 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((357/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((357/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (357/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01704137482177 : ℝ))) ≤ (0.35980083812296491228 : ℝ) / (((357/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.35980083812296491228 : ℝ) / (((357/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.35980083812296491228 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.35980083812296491228 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_257_256
  rw [show ((257/100 : ℝ)) / ((64/25 : ℝ)) = (257/256 : ℝ) by norm_num] at hp
  have hX : ((0.141920885937 : ℝ) - (0.1419948419 : ℝ) * (64/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.141920885937 : ℝ) - (0.1419948419 : ℝ) * (64/25 : ℝ)) * log (257/256) ≥
      (((0.141920885937 : ℝ) - (0.1419948419 : ℝ) * (64/25 : ℝ))) * (0.00389864041566 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01704137482177 : ℝ) * (64/25 : ℝ) ^ 2) * log (257/256) ≥
      ((0.01704137482177 : ℝ) * (64/25 : ℝ) ^ 2) * (0.00389864041565 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 7 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_7 :
    (0.0002797175128431 : ℝ) ≤ ∫ t in (257/100 : ℝ)..(129/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (257/100 : ℝ)) (b := (129/50 : ℝ)) (A := (0.143342547577 : ℝ))
    (B := (0.1423378957 : ℝ)) (C := (0.01686595684361 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_257_100) (sigma0_deriv_lower_c4_257_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.521698998143 : ℝ) := by
        have hle : s + 2 ≤ (229/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_229_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.521698998143 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((257/100 : ℝ) + 2) * ((257/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((257/100 : ℝ) + 2) * ((257/100 : ℝ) + 1) = ((257/100 : ℝ) + 1) / ((257/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.35809490977301750547 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((179/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((179/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (179/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01686595684361 : ℝ))) ≤ (0.35809490977301750547 : ℝ) / (((179/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.35809490977301750547 : ℝ) / (((179/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.35809490977301750547 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.35809490977301750547 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_258_257
  rw [show ((129/50 : ℝ)) / ((257/100 : ℝ)) = (258/257 : ℝ) by norm_num] at hp
  have hX : ((0.143342547577 : ℝ) - (0.1423378957 : ℝ) * (257/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.143342547577 : ℝ) - (0.1423378957 : ℝ) * (257/100 : ℝ)) * log (258/257) ≥
      (((0.143342547577 : ℝ) - (0.1423378957 : ℝ) * (257/100 : ℝ))) * (0.0038835000264 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01686595684361 : ℝ) * (257/100 : ℝ) ^ 2) * log (258/257) ≥
      ((0.01686595684361 : ℝ) * (257/100 : ℝ) ^ 2) * (0.00388350002639 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 8 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_8 :
    (0.0002813951378028 : ℝ) ≤ ∫ t in (129/50 : ℝ)..(259/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (129/50 : ℝ)) (b := (259/100 : ℝ)) (A := (0.144767621805 : ℝ))
    (B := (0.1426774182 : ℝ)) (C := (0.01669235134887 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_258_100) (sigma0_deriv_lower_c4_258_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.52388002409 : ℝ) := by
        have hle : s + 2 ≤ (459/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_459_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.52388002409 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((129/50 : ℝ) + 2) * ((129/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((129/50 : ℝ) + 2) * ((129/50 : ℝ) + 1) = ((129/50 : ℝ) + 1) / ((129/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.3563916532162882096 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((359/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((359/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (359/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01669235134887 : ℝ))) ≤ (0.3563916532162882096 : ℝ) / (((359/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.3563916532162882096 : ℝ) / (((359/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.3563916532162882096 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.3563916532162882096 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_259_258
  rw [show ((259/100 : ℝ)) / ((129/50 : ℝ)) = (259/258 : ℝ) by norm_num] at hp
  have hX : ((0.144767621805 : ℝ) - (0.1426774182 : ℝ) * (129/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.144767621805 : ℝ) - (0.1426774182 : ℝ) * (129/50 : ℝ)) * log (259/258) ≥
      (((0.144767621805 : ℝ) - (0.1426774182 : ℝ) * (129/50 : ℝ))) * (0.00386847677793 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01669235134887 : ℝ) * (129/50 : ℝ) ^ 2) * log (259/258) ≥
      ((0.01669235134887 : ℝ) * (129/50 : ℝ) ^ 2) * (0.00386847677792 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 9 of the `[5/2, 13/5]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c4_9 :
    (0.0002830663071384 : ℝ) ≤ ∫ t in (259/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (259/100 : ℝ)) (b := (13/5 : ℝ)) (A := (0.146196073478 : ℝ))
    (B := (0.1430134461 : ℝ)) (C := (0.0165205359642 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c4_259_100) (sigma0_deriv_lower_c4_259_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.526056303512 : ℝ) := by
        have hle : s + 2 ≤ (23/5 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_23_5.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.526056303512 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((259/100 : ℝ) + 2) * ((259/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((259/100 : ℝ) + 2) * ((259/100 : ℝ) + 1) = ((259/100 : ℝ) + 1) / ((259/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.35469106140072331154 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((18/5 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((18/5 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (18/5 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.0165205359642 : ℝ))) ≤ (0.35469106140072331154 : ℝ) / (((18/5 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.35469106140072331154 : ℝ) / (((18/5 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.35469106140072331154 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.35469106140072331154 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_260_259
  rw [show ((13/5 : ℝ)) / ((259/100 : ℝ)) = (260/259 : ℝ) by norm_num] at hp
  have hX : ((0.146196073478 : ℝ) - (0.1430134461 : ℝ) * (259/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.146196073478 : ℝ) - (0.1430134461 : ℝ) * (259/100 : ℝ)) * log (260/259) ≥
      (((0.146196073478 : ℝ) - (0.1430134461 : ℝ) * (259/100 : ℝ))) * (0.00385356931599 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.0165205359642 : ℝ) * (259/100 : ℝ) ^ 2) * log (260/259) ≥
      ((0.0165205359642 : ℝ) * (259/100 : ℝ) ^ 2) * (0.00385356931598 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- The ten-panel second-order sandwich for `∫ sigma0 t/(2t)` on `[5/2, 13/5]`. -/
private theorem sigma0_integral_lower2_c4 :
    (0.0027546843865812 : ℝ) ≤ ∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have s10 : (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (5/2 : ℝ)..(251/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (251/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s0 : (∫ t in (251/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (251/100 : ℝ)..(63/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (63/25 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s1 : (∫ t in (63/25 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (63/25 : ℝ)..(253/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (253/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s2 : (∫ t in (253/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (253/100 : ℝ)..(127/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (127/50 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s3 : (∫ t in (127/50 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (127/50 : ℝ)..(51/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (51/20 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s4 : (∫ t in (51/20 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (51/20 : ℝ)..(64/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (64/25 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s5 : (∫ t in (64/25 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (64/25 : ℝ)..(257/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (257/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s6 : (∫ t in (257/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (257/100 : ℝ)..(129/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (129/50 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s7 : (∫ t in (129/50 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (129/50 : ℝ)..(259/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (259/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s8 : (∫ t in (259/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (259/100 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (13/5 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  rw [s10, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  linarith [sigma0_panel_val2_c4_0, sigma0_panel_val2_c4_1, sigma0_panel_val2_c4_2, sigma0_panel_val2_c4_3, sigma0_panel_val2_c4_4, sigma0_panel_val2_c4_5, sigma0_panel_val2_c4_6, sigma0_panel_val2_c4_7, sigma0_panel_val2_c4_8, sigma0_panel_val2_c4_9]

/-- `∫ log (t+1)/t` on `[5/2, 13/5]` from the eight-term expansion at `c = 51/20`. -/
private theorem log_succ_integral_c4_lower :
    (0.0496856806024402 : ℝ) ≤ ∫ t in (5/2 : ℝ)..(13/5 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (5/2 : ℝ) (13/5 : ℝ),
      |((51/20 : ℝ) - t) / (51/20 + 1)| ≤ (1/71 : ℝ) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (5/2 : ℝ) ≤ 13/5)] at ht
    rw [abs_le]
    have hb : (0 : ℝ) < 51/20 + 1 := by norm_num
    constructor
    · rw [le_div_iff₀ hb]
      nlinarith [ht.1, ht.2]
    · rw [div_le_iff₀ hb]
      nlinarith [ht.1, ht.2]
  have h := log_succ_integral_lower (a := (5/2 : ℝ)) (b := (13/5 : ℝ)) (c := (51/20 : ℝ))
    (r := (1/71 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 8
  have hc := log_71_20
  have hl := log_26_25
  rw [show ((13/5 : ℝ) / (5/2)) = 26/25 by norm_num] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  norm_num at h
  have hmul : (1.266947603483 : ℝ) * (0.03922071315328 : ℝ) ≤ log (71/20) * log (26/25) := by
    have hm := mul_le_mul hc.1 hl.1 (by norm_num) (by linarith [hc.1])
    linarith [hm]
  linarith [h, hmul, hl.2]
/-- On `[5/2, 13/5]` the `Xi1` kernel has both indicators fixed whenever `sp - 2 ≤ 5/2`
(the second window sits below the panel and the first covers it). -/
private theorem Xi1_general_eq_c4 {s sp t : ℝ} (hsp : sp - 2 < 5/2)
    (h1 : (5/2 : ℝ) ≤ t) (h2 : t ≤ 13/5) :
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
below `[5/2, 13/5]`. -/
private theorem Xi1_general_integral_c4 {s sp : ℝ} (hsp : sp - 2 < 5/2)
    (hPpos : 0 < (s - 1) * (sp - 1)) :
    (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Functional.Xi1 s sp t) =
      log (16 / ((s - 1) * (sp - 1))) *
          (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (5/2 : ℝ)..(13/5 : ℝ), log (t + 1) / t) -
          (log ((s - 1) * (sp - 1)) / 2) *
            (∫ t in (5/2 : ℝ)..(13/5 : ℝ), 1 / t) := by
  have hI1 := sigma0_div_two_integrable (a := (5/2 : ℝ)) (b := (13/5 : ℝ))
    (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (5/2 : ℝ) (13/5 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (5/2 : ℝ) (13/5 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (5/2 : ℝ) (13/5 : ℝ),
      Wu04Functional.Xi1 s sp t =
        log (16 / ((s - 1) * (sp - 1))) * (Wu04Integral.sigma0 t / (2 * t)) +
          (log (t + 1) / t - (log ((s - 1) * (sp - 1)) / 2) * (1 / t)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (5/2 : ℝ) ≤ 13/5)] at ht
    rw [Xi1_general_eq_c4 hsp ht.1 ht.2]
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

/-- `integralMatrix 4 2` is the `Xi1 (13/5) (179/50)` quadrature on `[5/2, 13/5]`. -/
private theorem integralMatrix_4_4_eq :
    Wu04Table.integralMatrix 4 4 =
      ∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Functional.Xi1 ((13/5 : ℝ)) ((179/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_4_2` of Wu's Section 7 matrix**, certified on the `[5/2, 13/5]` panel. -/
private theorem entry_4_4_certified :
    (256142 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 4 4 := by
  rw [integralMatrix_4_4_eq,
    Xi1_general_integral_c4 (s := (13/5 : ℝ)) (sp := (179/50 : ℝ)) (by norm_num) (by norm_num),
    show (((13/5 : ℝ)) - 1) * ((179/50 : ℝ) - 1) = (516/125 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c4
  have hB := log_succ_integral_c4_lower
  have h1t := integral_one_div_exp (a := (5/2 : ℝ)) (b := (13/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_26_25
  have h4 := log_four_bounds
  have hP := log_P_4_bounds
  rw [h1t]
  have hLP : (1.3547956940207 : ℝ) ≤ log (16 / ((516/125 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3547956940207 : ℝ) * (0.0027546843865812 : ℝ) ≤
      log (16 / ((516/125 : ℝ))) * (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((516/125 : ℝ)) / 2) * log (26/25) ≤
      (1.4177930281793 : ℝ) / 2 * (0.03922071315329 : ℝ) := by
    have h2 : log ((516/125 : ℝ)) / 2 ≤ (1.4177930281793 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_4_2` in the shape the matrix file states it. -/
private theorem entry_4_4_leaf :
    (Wu04Table.candidateMatrixQ 4 4 : ℝ) ≤ Wu04Table.integralMatrix 4 4 := by
  have hc : (Wu04Table.candidateMatrixQ 4 4 : ℝ) = 256142 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_4_4_certified

/-- `integralMatrix 5 2` is the `Xi1 (27/10) (347/100)` quadrature on `[5/2, 13/5]`. -/
private theorem integralMatrix_5_4_eq :
    Wu04Table.integralMatrix 5 4 =
      ∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Functional.Xi1 ((27/10 : ℝ)) ((347/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_5_2` of Wu's Section 7 matrix**, certified on the `[5/2, 13/5]` panel. -/
private theorem entry_5_4_certified :
    (252328 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 5 4 := by
  rw [integralMatrix_5_4_eq,
    Xi1_general_integral_c4 (s := (27/10 : ℝ)) (sp := (347/100 : ℝ)) (by norm_num) (by norm_num),
    show (((27/10 : ℝ)) - 1) * ((347/100 : ℝ) - 1) = (4199/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c4
  have hB := log_succ_integral_c4_lower
  have h1t := integral_one_div_exp (a := (5/2 : ℝ)) (b := (13/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_26_25
  have h4 := log_four_bounds
  have hP := log_P_5_bounds
  rw [h1t]
  have hLP : (1.33774232049788 : ℝ) ≤ log (16 / ((4199/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.33774232049788 : ℝ) * (0.0027546843865812 : ℝ) ≤
      log (16 / ((4199/1000 : ℝ))) * (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4199/1000 : ℝ)) / 2) * log (26/25) ≤
      (1.43484640170212 : ℝ) / 2 * (0.03922071315329 : ℝ) := by
    have h2 : log ((4199/1000 : ℝ)) / 2 ≤ (1.43484640170212 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_5_2` in the shape the matrix file states it. -/
private theorem entry_5_4_leaf :
    (Wu04Table.candidateMatrixQ 5 4 : ℝ) ≤ Wu04Table.integralMatrix 5 4 := by
  have hc : (Wu04Table.candidateMatrixQ 5 4 : ℝ) = 252328 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_5_4_certified

/-- `integralMatrix 6 2` is the `Xi1 (14/5) (167/50)` quadrature on `[5/2, 13/5]`. -/
private theorem integralMatrix_6_4_eq :
    Wu04Table.integralMatrix 6 4 =
      ∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Functional.Xi1 ((14/5 : ℝ)) ((167/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_6_2` of Wu's Section 7 matrix**, certified on the `[5/2, 13/5]` panel. -/
private theorem entry_6_4_certified :
    (251637 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 6 4 := by
  rw [integralMatrix_6_4_eq,
    Xi1_general_integral_c4 (s := (14/5 : ℝ)) (sp := (167/50 : ℝ)) (by norm_num) (by norm_num),
    show (((14/5 : ℝ)) - 1) * ((167/50 : ℝ) - 1) = (1053/250 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c4
  have hB := log_succ_integral_c4_lower
  have h1t := integral_one_div_exp (a := (5/2 : ℝ)) (b := (13/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_26_25
  have h4 := log_four_bounds
  have hP := log_P_6_bounds
  rw [h1t]
  have hLP : (1.3346511279282 : ℝ) ≤ log (16 / ((1053/250 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3346511279282 : ℝ) * (0.0027546843865812 : ℝ) ≤
      log (16 / ((1053/250 : ℝ))) * (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((1053/250 : ℝ)) / 2) * log (26/25) ≤
      (1.4379375942718 : ℝ) / 2 * (0.03922071315329 : ℝ) := by
    have h2 : log ((1053/250 : ℝ)) / 2 ≤ (1.4379375942718 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_6_2` in the shape the matrix file states it. -/
private theorem entry_6_4_leaf :
    (Wu04Table.candidateMatrixQ 6 4 : ℝ) ≤ Wu04Table.integralMatrix 6 4 := by
  have hc : (Wu04Table.candidateMatrixQ 6 4 : ℝ) = 251637 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_6_4_certified

/-- `integralMatrix 7 2` is the `Xi1 (29/10) (319/100)` quadrature on `[5/2, 13/5]`. -/
private theorem integralMatrix_7_4_eq :
    Wu04Table.integralMatrix 7 4 =
      ∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Functional.Xi1 ((29/10 : ℝ)) ((319/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_7_2` of Wu's Section 7 matrix**, certified on the `[5/2, 13/5]` panel. -/
private theorem entry_7_4_certified :
    (254362 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 7 4 := by
  rw [integralMatrix_7_4_eq,
    Xi1_general_integral_c4 (s := (29/10 : ℝ)) (sp := (319/100 : ℝ)) (by norm_num) (by norm_num),
    show (((29/10 : ℝ)) - 1) * ((319/100 : ℝ) - 1) = (4161/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c4
  have hB := log_succ_integral_c4_lower
  have h1t := integral_one_div_exp (a := (5/2 : ℝ)) (b := (13/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_26_25
  have h4 := log_four_bounds
  have hP := log_P_7_bounds
  rw [h1t]
  have hLP : (1.34683329219 : ℝ) ≤ log (16 / ((4161/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.34683329219 : ℝ) * (0.0027546843865812 : ℝ) ≤
      log (16 / ((4161/1000 : ℝ))) * (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4161/1000 : ℝ)) / 2) * log (26/25) ≤
      (1.42575543001 : ℝ) / 2 * (0.03922071315329 : ℝ) := by
    have h2 : log ((4161/1000 : ℝ)) / 2 ≤ (1.42575543001 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_7_2` in the shape the matrix file states it. -/
private theorem entry_7_4_leaf :
    (Wu04Table.candidateMatrixQ 7 4 : ℝ) ≤ Wu04Table.integralMatrix 7 4 := by
  have hc : (Wu04Table.candidateMatrixQ 7 4 : ℝ) = 254362 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_7_4_certified

/-- `integralMatrix 8 2` is the `Xi1 (3) (3)` quadrature on `[5/2, 13/5]`. -/
private theorem integralMatrix_8_4_eq :
    Wu04Table.integralMatrix 8 4 =
      ∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Functional.Xi1 ((3 : ℝ)) ((3 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_8_2` of Wu's Section 7 matrix**, certified on the `[5/2, 13/5]` panel. -/
private theorem entry_8_4_certified :
    (263187 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 8 4 := by
  rw [integralMatrix_8_4_eq,
    Xi1_general_integral_c4 (s := (3 : ℝ)) (sp := (3 : ℝ)) (by norm_num) (by norm_num),
    show (((3 : ℝ)) - 1) * ((3 : ℝ) - 1) = (4 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c4
  have hB := log_succ_integral_c4_lower
  have h1t := integral_one_div_exp (a := (5/2 : ℝ)) (b := (13/5 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_26_25
  have h4 := log_four_bounds
  have hP : (1.3862943611 : ℝ) ≤ log (4) ∧ log (4) ≤ (1.3862943615 : ℝ) := log_four_bounds
  rw [h1t]
  have hLP : (1.3862943607 : ℝ) ≤ log (16 / ((4 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3862943607 : ℝ) * (0.0027546843865812 : ℝ) ≤
      log (16 / ((4 : ℝ))) * (∫ t in (5/2 : ℝ)..(13/5 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4 : ℝ)) / 2) * log (26/25) ≤
      (1.3862943615 : ℝ) / 2 * (0.03922071315329 : ℝ) := by
    have h2 : log ((4 : ℝ)) / 2 ≤ (1.3862943615 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_8_2` in the shape the matrix file states it. -/
private theorem entry_8_4_leaf :
    (Wu04Table.candidateMatrixQ 8 4 : ℝ) ≤ Wu04Table.integralMatrix 8 4 := by
  have hc : (Wu04Table.candidateMatrixQ 8 4 : ℝ) = 263187 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_8_4_certified

/-- Two-sided enclosure of `log (461/100)`, from `log 23/5` and the ratio `461/460`. -/
private theorem log_461_100 :
    (1.528227856996 : ℝ) ≤ log ((461/100 : ℝ)) ∧ log ((461/100 : ℝ)) ≤ (1.528227857026 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (461/460 : ℝ))
    (x := (1/921 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0021715535135078 : ℝ) : ℝ) ≤ log (461/460) ∧
      log (461/460) ≤ ((0.0021715535135079 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((461/100 : ℝ)) = log ((23/5 : ℝ)) + log (461/460) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (461/460 : ℝ) = (461/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (231/50)`, from `log 23/5` and the ratio `231/230`. -/
private theorem log_231_50 :
    (1.530394705081 : ℝ) ≤ log ((231/50 : ℝ)) ∧ log ((231/50 : ℝ)) ≤ (1.530394705111 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (231/230 : ℝ))
    (x := (1/461 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0043384015985981 : ℝ) : ℝ) ≤ log (231/230) ∧
      log (231/230) ≤ ((0.0043384015985982 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((231/50 : ℝ)) = log ((23/5 : ℝ)) + log (231/230) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (231/230 : ℝ) = (231/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (463/100)`, from `log 23/5` and the ratio `463/460`. -/
private theorem log_463_100 :
    (1.532556868086 : ℝ) ≤ log ((463/100 : ℝ)) ∧ log ((463/100 : ℝ)) ≤ (1.532556868116 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (463/460 : ℝ))
    (x := (3/923 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0065005646030933 : ℝ) : ℝ) ≤ log (463/460) ∧
      log (463/460) ≤ ((0.0065005646030934 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((463/100 : ℝ)) = log ((23/5 : ℝ)) + log (463/460) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (463/460 : ℝ) = (463/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (116/25)`, from `log 23/5` and the ratio `116/115`. -/
private theorem log_116_25 :
    (1.534714366226 : ℝ) ≤ log ((116/25 : ℝ)) ∧ log ((116/25 : ℝ)) ≤ (1.534714366256 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (116/115 : ℝ))
    (x := (1/231 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0086580627431145 : ℝ) : ℝ) ≤ log (116/115) ∧
      log (116/115) ≤ ((0.0086580627431147 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((116/25 : ℝ)) = log ((23/5 : ℝ)) + log (116/115) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (116/115 : ℝ) = (116/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (93/20)`, from `log 23/5` and the ratio `93/92`. -/
private theorem log_93_20 :
    (1.536867219587 : ℝ) ≤ log ((93/20 : ℝ)) ∧ log ((93/20 : ℝ)) ≤ (1.536867219617 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (93/92 : ℝ))
    (x := (1/185 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0108109161042155 : ℝ) : ℝ) ≤ log (93/92) ∧
      log (93/92) ≤ ((0.0108109161042159 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((93/20 : ℝ)) = log ((23/5 : ℝ)) + log (93/92) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (93/92 : ℝ) = (93/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (233/50)`, from `log 23/5` and the ratio `233/230`. -/
private theorem log_233_50 :
    (1.539015448125 : ℝ) ≤ log ((233/50 : ℝ)) ∧ log ((233/50 : ℝ)) ≤ (1.539015448155 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (233/230 : ℝ))
    (x := (3/463 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.012959144642505 : ℝ) : ℝ) ≤ log (233/230) ∧
      log (233/230) ≤ ((0.0129591446425061 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((233/50 : ℝ)) = log ((23/5 : ℝ)) + log (233/230) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (233/230 : ℝ) = (233/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (467/100)`, from `log 23/5` and the ratio `467/460`. -/
private theorem log_467_100 :
    (1.541159071668 : ℝ) ≤ log ((467/100 : ℝ)) ∧ log ((467/100 : ℝ)) ≤ (1.541159071698 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (467/460 : ℝ))
    (x := (7/927 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0151027681857562 : ℝ) : ℝ) ≤ log (467/460) ∧
      log (467/460) ≤ ((0.0151027681857591 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((467/100 : ℝ)) = log ((23/5 : ℝ)) + log (467/460) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (467/460 : ℝ) = (467/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (117/25)`, from `log 23/5` and the ratio `117/115`. -/
private theorem log_117_25 :
    (1.543298109917 : ℝ) ≤ log ((117/25 : ℝ)) ∧ log ((117/25 : ℝ)) ≤ (1.543298109947 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (117/115 : ℝ))
    (x := (1/116 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.017241806434505 : ℝ) : ℝ) ≤ log (117/115) ∧
      log (117/115) ≤ ((0.0172418064345122 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((117/25 : ℝ)) = log ((23/5 : ℝ)) + log (117/115) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (117/115 : ℝ) = (117/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (469/100)`, from `log 23/5` and the ratio `469/460`. -/
private theorem log_469_100 :
    (1.545432582446 : ℝ) ≤ log ((469/100 : ℝ)) ∧ log ((469/100 : ℝ)) ≤ (1.545432582476 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (469/460 : ℝ))
    (x := (9/929 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0193762789631363 : ℝ) : ℝ) ≤ log (469/460) ∧
      log (469/460) ≤ ((0.0193762789631525 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((469/100 : ℝ)) = log ((23/5 : ℝ)) + log (469/460) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (469/460 : ℝ) = (469/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (47/10)`, from `log 23/5` and the ratio `47/46`. -/
private theorem log_47_10 :
    (1.547562508703 : ℝ) ≤ log ((47/10 : ℝ)) ∧ log ((47/10 : ℝ)) ≤ (1.547562508733 : ℝ) := by
  have hA := log_23_5
  have hB := log_enclosure (y := (47/46 : ℝ))
    (x := (1/93 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0215062052209588 : ℝ) : ℝ) ≤ log (47/46) ∧
      log (47/46) ≤ ((0.0215062052209921 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((47/10 : ℝ)) = log ((23/5 : ℝ)) + log (47/46) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((23/5 : ℝ)) * (47/46 : ℝ) = (47/10 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (18/5)`, from `log 7/2` and the ratio `36/35`. -/
private theorem log_18_5 :
    (1.280933845458 : ℝ) ≤ log ((18/5 : ℝ)) ∧ log ((18/5 : ℝ)) ≤ (1.280933845471 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (36/35 : ℝ))
    (x := (1/71 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0281708769666649 : ℝ) : ℝ) ≤ log (36/35) ∧
      log (36/35) ≤ ((0.0281708769668849 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((18/5 : ℝ)) = log ((7/2 : ℝ)) + log (36/35) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (36/35 : ℝ) = (18/5 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (361/100)`, from `log 7/2` and the ratio `361/350`. -/
private theorem log_361_100 :
    (1.283707772341 : ℝ) ≤ log ((361/100 : ℝ)) ∧ log ((361/100 : ℝ)) ≤ (1.283707772354 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (361/350 : ℝ))
    (x := (11/711 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0309448038493609 : ℝ) : ℝ) ≤ log (361/350) ∧
      log (361/350) ≤ ((0.0309448038497854 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((361/100 : ℝ)) = log ((7/2 : ℝ)) + log (361/350) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (361/350 : ℝ) = (361/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (181/50)`, from `log 7/2` and the ratio `181/175`. -/
private theorem log_181_50 :
    (1.286474025834 : ℝ) ≤ log ((181/50 : ℝ)) ∧ log ((181/50 : ℝ)) ≤ (1.286474025847 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (181/175 : ℝ))
    (x := (3/178 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0337110573422013 : ℝ) : ℝ) ≤ log (181/175) ∧
      log (181/175) ≤ ((0.0337110573429741 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((181/50 : ℝ)) = log ((7/2 : ℝ)) + log (181/175) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (181/175 : ℝ) = (181/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (363/100)`, from `log 7/2` and the ratio `363/350`. -/
private theorem log_363_100 :
    (1.289232648273 : ℝ) ≤ log ((363/100 : ℝ)) ∧ log ((363/100 : ℝ)) ≤ (1.289232648287 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (363/350 : ℝ))
    (x := (13/713 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0364696797811999 : ℝ) : ℝ) ≤ log (363/350) ∧
      log (363/350) ≤ ((0.0364696797825402 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((363/100 : ℝ)) = log ((7/2 : ℝ)) + log (363/350) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (363/350 : ℝ) = (363/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (91/25)`, from `log 7/2` and the ratio `26/25`. -/
private theorem log_91_25 :
    (1.291983681644 : ℝ) ≤ log ((91/25 : ℝ)) ∧ log ((91/25 : ℝ)) ≤ (1.29198368166 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (26/25 : ℝ))
    (x := (1/51 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0392207131529628 : ℝ) : ℝ) ≤ log (26/25) ∧
      log (26/25) ≤ ((0.0392207131551924 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((91/25 : ℝ)) = log ((7/2 : ℝ)) + log (26/25) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (26/25 : ℝ) = (91/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (73/20)`, from `log 7/2` and the ratio `73/70`. -/
private theorem log_73_20 :
    (1.29472716759 : ℝ) ≤ log ((73/20 : ℝ)) ∧ log ((73/20 : ℝ)) ≤ (1.294727167607 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (73/70 : ℝ))
    (x := (3/143 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0419641990985209 : ℝ) : ℝ) ≤ log (73/70) ∧
      log (73/70) ≤ ((0.0419641991020996 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((73/20 : ℝ)) = log ((7/2 : ℝ)) + log (73/70) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (73/70 : ℝ) = (73/20 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (183/50)`, from `log 7/2` and the ratio `183/175`. -/
private theorem log_183_50 :
    (1.297463147409 : ℝ) ≤ log ((183/50 : ℝ)) ∧ log ((183/50 : ℝ)) ≤ (1.297463147427 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (183/175 : ℝ))
    (x := (4/179 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0447001789171115 : ℝ) : ℝ) ≤ log (183/175) ∧
      log (183/175) ≤ ((0.0447001789226796 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((183/50 : ℝ)) = log ((7/2 : ℝ)) + log (183/175) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (183/175 : ℝ) = (183/50 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (367/100)`, from `log 7/2` and the ratio `367/350`. -/
private theorem log_367_100 :
    (1.300191662061 : ℝ) ≤ log ((367/100 : ℝ)) ∧ log ((367/100 : ℝ)) ≤ (1.300191662083 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (367/350 : ℝ))
    (x := (17/717 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0474286935699068 : ℝ) : ℝ) ≤ log (367/350) ∧
      log (367/350) ≤ ((0.0474286935783361 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((367/100 : ℝ)) = log ((7/2 : ℝ)) + log (367/350) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (367/350 : ℝ) = (367/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (92/25)`, from `log 7/2` and the ratio `184/175`. -/
private theorem log_92_25 :
    (1.302912752175 : ℝ) ≤ log ((92/25 : ℝ)) ∧ log ((92/25 : ℝ)) ≤ (1.302912752201 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (184/175 : ℝ))
    (x := (9/359 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0501497836836925 : ℝ) : ℝ) ≤ log (184/175) ∧
      log (184/175) ≤ ((0.0501497836961475 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((92/25 : ℝ)) = log ((7/2 : ℝ)) + log (184/175) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (184/175 : ℝ) = (92/25 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (369/100)`, from `log 7/2` and the ratio `369/350`. -/
private theorem log_369_100 :
    (1.305626458046 : ℝ) ≤ log ((369/100 : ℝ)) ∧ log ((369/100 : ℝ)) ≤ (1.305626458077 : ℝ) := by
  have hA := log_7_2
  have hB := log_enclosure (y := (369/350 : ℝ))
    (x := (19/719 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  have hB' : ((0.0528634895544954 : ℝ) : ℝ) ≤ log (369/350) ∧
      log (369/350) ≤ ((0.0528634895725052 : ℝ) : ℝ) := by
    constructor
    · refine le_trans ?_ hB.1
      norm_num [Finset.sum_range_succ]
    · refine le_trans hB.2 ?_
      norm_num [Finset.sum_range_succ]
  have hkey : log ((369/100 : ℝ)) = log ((7/2 : ℝ)) + log (369/350) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show ((7/2 : ℝ)) * (369/350 : ℝ) = (369/100 : ℝ) by norm_num]
  constructor
  · linarith [hA.1, hB'.1, hkey]
  · linarith [hA.2, hB'.2, hkey]

/-- Two-sided enclosure of `log (27/26)` from the atanh series. -/
private theorem log_27_26 :
    (0.03774032798284 : ℝ) ≤ log ((27/26 : ℝ)) ∧ log ((27/26 : ℝ)) ≤ (0.03774032798285 : ℝ) := by
  have h := log_enclosure (y := (27/26 : ℝ))
    (x := (1/53 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 4
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (261/260)` from the atanh series. -/
private theorem log_261_260 :
    (0.00383877630716 : ℝ) ≤ log ((261/260 : ℝ)) ∧ log ((261/260 : ℝ)) ≤ (0.00383877630717 : ℝ) := by
  have h := log_enclosure (y := (261/260 : ℝ))
    (x := (1/521 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (262/261)` from the atanh series. -/
private theorem log_262_261 :
    (0.0038240964384 : ℝ) ≤ log ((262/261 : ℝ)) ∧ log ((262/261 : ℝ)) ≤ (0.00382409643841 : ℝ) := by
  have h := log_enclosure (y := (262/261 : ℝ))
    (x := (1/523 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (263/262)` from the atanh series. -/
private theorem log_263_262 :
    (0.00380952841666 : ℝ) ≤ log ((263/262 : ℝ)) ∧ log ((263/262 : ℝ)) ≤ (0.00380952841667 : ℝ) := by
  have h := log_enclosure (y := (263/262 : ℝ))
    (x := (1/525 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (264/263)` from the atanh series. -/
private theorem log_264_263 :
    (0.00379507096855 : ℝ) ≤ log ((264/263 : ℝ)) ∧ log ((264/263 : ℝ)) ≤ (0.00379507096856 : ℝ) := by
  have h := log_enclosure (y := (264/263 : ℝ))
    (x := (1/527 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (265/264)` from the atanh series. -/
private theorem log_265_264 :
    (0.0037807228399 : ℝ) ≤ log ((265/264 : ℝ)) ∧ log ((265/264 : ℝ)) ≤ (0.00378072283991 : ℝ) := by
  have h := log_enclosure (y := (265/264 : ℝ))
    (x := (1/529 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (266/265)` from the atanh series. -/
private theorem log_266_265 :
    (0.00376648279547 : ℝ) ≤ log ((266/265 : ℝ)) ∧ log ((266/265 : ℝ)) ≤ (0.00376648279548 : ℝ) := by
  have h := log_enclosure (y := (266/265 : ℝ))
    (x := (1/531 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (267/266)` from the atanh series. -/
private theorem log_267_266 :
    (0.00375234961855 : ℝ) ≤ log ((267/266 : ℝ)) ∧ log ((267/266 : ℝ)) ≤ (0.00375234961856 : ℝ) := by
  have h := log_enclosure (y := (267/266 : ℝ))
    (x := (1/533 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (268/267)` from the atanh series. -/
private theorem log_268_267 :
    (0.0037383221106 : ℝ) ≤ log ((268/267 : ℝ)) ∧ log ((268/267 : ℝ)) ≤ (0.00373832211061 : ℝ) := by
  have h := log_enclosure (y := (268/267 : ℝ))
    (x := (1/535 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (269/268)` from the atanh series. -/
private theorem log_269_268 :
    (0.00372439909098 : ℝ) ≤ log ((269/268 : ℝ)) ∧ log ((269/268 : ℝ)) ≤ (0.00372439909099 : ℝ) := by
  have h := log_enclosure (y := (269/268 : ℝ))
    (x := (1/537 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- Two-sided enclosure of `log (270/269)` from the atanh series. -/
private theorem log_270_269 :
    (0.00371057939653 : ℝ) ≤ log ((270/269 : ℝ)) ∧ log ((270/269 : ℝ)) ≤ (0.00371057939654 : ℝ) := by
  have h := log_enclosure (y := (270/269 : ℝ))
    (x := (1/539 : ℝ)) (by norm_num) (by norm_num) (by norm_num) 3
  constructor
  · refine le_trans ?_ h.1
    norm_num [Finset.sum_range_succ]
  · refine le_trans h.2 ?_
    norm_num [Finset.sum_range_succ]

/-- `sigma 3 (23/5) (18/5)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_460_100 :
    (0.122281135081 : ℝ) ≤ Wu04Integral.sigma 3 ((23/5 : ℝ)) ((18/5 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (23/5 : ℝ)) (c := (18/5 : ℝ)) (m := (14/5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((23/5 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((23/5 : ℝ)) - 1) = (18/5 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (18/5 : ℝ)) (m := (14/5 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.427444014813 : ℝ) ≤ log ((23/5 : ℝ)) - log 3 := by
    linarith [log_23_5.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((18/5 : ℝ)) := by linarith [log_18_5.1]
  have hp : (0 : ℝ) ≤ (0.427444014813 : ℝ) := by norm_num
  have hlo' : (0.54752750561242240476 : ℝ) ≤ log ((18/5 : ℝ)) * (log ((23/5 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_18_5.1 hdiff_lo hp hq
    have hc : (0.54752750561242240476 : ℝ) ≤ (1.280933845458 : ℝ) * (0.427444014813 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_18_5.1, log_18_5.2, log_23_5.1, log_23_5.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((13/5 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_260_100 :
    (0.147627867863 : ℝ) ≤ Wu04Integral.sigma0 ((13/5 : ℝ)) := by
  have h := sigma_c5_460_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((13/5 : ℝ)) + 2 = (23/5 : ℝ) by norm_num, show ((13/5 : ℝ)) + 1 = (18/5 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.147627867863 : ℝ) : ℝ) ≤ ((0.122281135081 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.122281135081 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (461/100) (361/100)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_461_100 :
    (0.123469840017 : ℝ) ≤ Wu04Integral.sigma 3 ((461/100 : ℝ)) ((361/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (461/100 : ℝ)) (c := (361/100 : ℝ)) (m := (561/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((461/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((461/100 : ℝ)) - 1) = (361/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (361/100 : ℝ)) (m := (561/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.429615568326 : ℝ) ≤ log ((461/100 : ℝ)) - log 3 := by
    linarith [log_461_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((361/100 : ℝ)) := by linarith [log_361_100.1]
  have hp : (0 : ℝ) ≤ (0.429615568326 : ℝ) := by norm_num
  have hlo' : (0.55150084417878213847 : ℝ) ≤ log ((361/100 : ℝ)) * (log ((461/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_361_100.1 hdiff_lo hp hq
    have hc : (0.55150084417878213847 : ℝ) ≤ (1.283707772341 : ℝ) * (0.429615568326 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_361_100.1, log_361_100.2, log_461_100.1, log_461_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((261/100 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_261_100 :
    (0.149062970466 : ℝ) ≤ Wu04Integral.sigma0 ((261/100 : ℝ)) := by
  have h := sigma_c5_461_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((261/100 : ℝ)) + 2 = (461/100 : ℝ) by norm_num, show ((261/100 : ℝ)) + 1 = (361/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.149062970466 : ℝ) : ℝ) ≤ ((0.123469840017 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.123469840017 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (231/50) (181/50)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_462_100 :
    (0.12466125698 : ℝ) ≤ Wu04Integral.sigma 3 ((231/50 : ℝ)) ((181/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (231/50 : ℝ)) (c := (181/50 : ℝ)) (m := (281/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((231/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((231/50 : ℝ)) - 1) = (181/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (181/50 : ℝ)) (m := (281/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.431782416411 : ℝ) ≤ log ((231/50 : ℝ)) - log 3 := by
    linarith [log_231_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((181/50 : ℝ)) := by linarith [log_181_50.1]
  have hp : (0 : ℝ) ≤ (0.431782416411 : ℝ) := by norm_num
  have hlo' : (0.55547686352459175956 : ℝ) ≤ log ((181/50 : ℝ)) * (log ((231/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_181_50.1 hdiff_lo hp hq
    have hc : (0.55547686352459175956 : ℝ) ≤ (1.286474025834 : ℝ) * (0.431782416411 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_181_50.1, log_181_50.2, log_231_50.1, log_231_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((131/50 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_262_100 :
    (0.150501347251 : ℝ) ≤ Wu04Integral.sigma0 ((131/50 : ℝ)) := by
  have h := sigma_c5_462_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((131/50 : ℝ)) + 2 = (231/50 : ℝ) by norm_num, show ((131/50 : ℝ)) + 1 = (181/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.150501347251 : ℝ) : ℝ) ≤ ((0.12466125698 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.12466125698 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (463/100) (363/100)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_463_100 :
    (0.125855358044 : ℝ) ≤ Wu04Integral.sigma 3 ((463/100 : ℝ)) ((363/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (463/100 : ℝ)) (c := (363/100 : ℝ)) (m := (563/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((463/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((463/100 : ℝ)) - 1) = (363/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (363/100 : ℝ)) (m := (563/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.433944579416 : ℝ) ≤ log ((463/100 : ℝ)) - log 3 := by
    linarith [log_463_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((363/100 : ℝ)) := by linarith [log_363_100.1]
  have hp : (0 : ℝ) ≤ (0.433944579416 : ℝ) := by norm_num
  have hlo' : (0.55945551932420284374 : ℝ) ≤ log ((363/100 : ℝ)) * (log ((463/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_363_100.1 hdiff_lo hp hq
    have hc : (0.55945551932420284374 : ℝ) ≤ (1.289232648273 : ℝ) * (0.433944579416 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_363_100.1, log_363_100.2, log_463_100.1, log_463_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((263/100 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_263_100 :
    (0.151942964505 : ℝ) ≤ Wu04Integral.sigma0 ((263/100 : ℝ)) := by
  have h := sigma_c5_463_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((263/100 : ℝ)) + 2 = (463/100 : ℝ) by norm_num, show ((263/100 : ℝ)) + 1 = (363/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.151942964505 : ℝ) : ℝ) ≤ ((0.125855358044 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.125855358044 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (116/25) (91/25)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_464_100 :
    (0.127052115564 : ℝ) ≤ Wu04Integral.sigma 3 ((116/25 : ℝ)) ((91/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (116/25 : ℝ)) (c := (91/25 : ℝ)) (m := (141/50 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((116/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((116/25 : ℝ)) - 1) = (91/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (91/25 : ℝ)) (m := (141/50 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.436102077556 : ℝ) ≤ log ((116/25 : ℝ)) - log 3 := by
    linarith [log_116_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((91/25 : ℝ)) := by linarith [log_91_25.1]
  have hp : (0 : ℝ) ≤ (0.436102077556 : ℝ) := by norm_num
  have hlo' : (0.56343676773339810158 : ℝ) ≤ log ((91/25 : ℝ)) * (log ((116/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_91_25.1 hdiff_lo hp hq
    have hc : (0.56343676773339810158 : ℝ) ≤ (1.291983681644 : ℝ) * (0.436102077556 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_91_25.1, log_91_25.2, log_116_25.1, log_116_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((66/25 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_264_100 :
    (0.153387788851 : ℝ) ≤ Wu04Integral.sigma0 ((66/25 : ℝ)) := by
  have h := sigma_c5_464_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((66/25 : ℝ)) + 2 = (116/25 : ℝ) by norm_num, show ((66/25 : ℝ)) + 1 = (91/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.153387788851 : ℝ) : ℝ) ≤ ((0.127052115564 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.127052115564 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (93/20) (73/20)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_465_100 :
    (0.128251502182 : ℝ) ≤ Wu04Integral.sigma 3 ((93/20 : ℝ)) ((73/20 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (93/20 : ℝ)) (c := (73/20 : ℝ)) (m := (113/40 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((93/20 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((93/20 : ℝ)) - 1) = (73/20 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (73/20 : ℝ)) (m := (113/40 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.438254930917 : ℝ) ≤ log ((93/20 : ℝ)) - log 3 := by
    linarith [log_93_20.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((73/20 : ℝ)) := by linarith [log_73_20.1]
  have hp : (0 : ℝ) ≤ (0.438254930917 : ℝ) := by norm_num
  have hlo' : (0.56742056538851853138 : ℝ) ≤ log ((73/20 : ℝ)) * (log ((93/20 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_73_20.1 hdiff_lo hp hq
    have hc : (0.56742056538851853138 : ℝ) ≤ (1.29472716759 : ℝ) * (0.438254930917 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_73_20.1, log_73_20.2, log_93_20.1, log_93_20.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((53/20 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_265_100 :
    (0.154835787261 : ℝ) ≤ Wu04Integral.sigma0 ((53/20 : ℝ)) := by
  have h := sigma_c5_465_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((53/20 : ℝ)) + 2 = (93/20 : ℝ) by norm_num, show ((53/20 : ℝ)) + 1 = (73/20 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.154835787261 : ℝ) : ℝ) ≤ ((0.128251502182 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.128251502182 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (233/50) (183/50)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_466_100 :
    (0.129453490818 : ℝ) ≤ Wu04Integral.sigma 3 ((233/50 : ℝ)) ((183/50 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (233/50 : ℝ)) (c := (183/50 : ℝ)) (m := (283/100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((233/50 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((233/50 : ℝ)) - 1) = (183/50 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (183/50 : ℝ)) (m := (283/100 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.440403159455 : ℝ) ≤ log ((233/50 : ℝ)) - log 3 := by
    linarith [log_233_50.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((183/50 : ℝ)) := by linarith [log_183_50.1]
  have hp : (0 : ℝ) ≤ (0.440403159455 : ℝ) := by norm_num
  have hlo' : (0.5714068693953519971 : ℝ) ≤ log ((183/50 : ℝ)) * (log ((233/50 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_183_50.1 hdiff_lo hp hq
    have hc : (0.5714068693953519971 : ℝ) ≤ (1.297463147409 : ℝ) * (0.440403159455 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_183_50.1, log_183_50.2, log_233_50.1, log_233_50.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((133/50 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_266_100 :
    (0.156286927041 : ℝ) ≤ Wu04Integral.sigma0 ((133/50 : ℝ)) := by
  have h := sigma_c5_466_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((133/50 : ℝ)) + 2 = (233/50 : ℝ) by norm_num, show ((133/50 : ℝ)) + 1 = (183/50 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.156286927041 : ℝ) : ℝ) ≤ ((0.129453490818 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.129453490818 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (467/100) (367/100)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_467_100 :
    (0.130658054663 : ℝ) ≤ Wu04Integral.sigma 3 ((467/100 : ℝ)) ((367/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (467/100 : ℝ)) (c := (367/100 : ℝ)) (m := (567/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((467/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((467/100 : ℝ)) - 1) = (367/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (367/100 : ℝ)) (m := (567/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.442546782998 : ℝ) ≤ log ((467/100 : ℝ)) - log 3 := by
    linarith [log_467_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((367/100 : ℝ)) := by linarith [log_367_100.1]
  have hp : (0 : ℝ) ≤ (0.442546782998 : ℝ) := by norm_num
  have hlo' : (0.57539563732591831643 : ℝ) ≤ log ((367/100 : ℝ)) * (log ((467/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_367_100.1 hdiff_lo hp hq
    have hc : (0.57539563732591831643 : ℝ) ≤ (1.300191662061 : ℝ) * (0.442546782998 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_367_100.1, log_367_100.2, log_467_100.1, log_467_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((267/100 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_267_100 :
    (0.157741175826 : ℝ) ≤ Wu04Integral.sigma0 ((267/100 : ℝ)) := by
  have h := sigma_c5_467_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((267/100 : ℝ)) + 2 = (467/100 : ℝ) by norm_num, show ((267/100 : ℝ)) + 1 = (367/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.157741175826 : ℝ) : ℝ) ≤ ((0.130658054663 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.130658054663 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (117/25) (92/25)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_468_100 :
    (0.131865167186 : ℝ) ≤ Wu04Integral.sigma 3 ((117/25 : ℝ)) ((92/25 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (117/25 : ℝ)) (c := (92/25 : ℝ)) (m := (71/25 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((117/25 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((117/25 : ℝ)) - 1) = (92/25 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (92/25 : ℝ)) (m := (71/25 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.444685821247 : ℝ) ≤ log ((117/25 : ℝ)) - log 3 := by
    linarith [log_117_25.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((92/25 : ℝ)) := by linarith [log_92_25.1]
  have hp : (0 : ℝ) ≤ (0.444685821247 : ℝ) := by norm_num
  have hlo' : (0.57938682721412886046 : ℝ) ≤ log ((92/25 : ℝ)) * (log ((117/25 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_92_25.1 hdiff_lo hp hq
    have hc : (0.57938682721412886046 : ℝ) ≤ (1.302912752175 : ℝ) * (0.444685821247 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_92_25.1, log_92_25.2, log_117_25.1, log_117_25.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((67/25 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_268_100 :
    (0.159198501586 : ℝ) ≤ Wu04Integral.sigma0 ((67/25 : ℝ)) := by
  have h := sigma_c5_468_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((67/25 : ℝ)) + 2 = (117/25 : ℝ) by norm_num, show ((67/25 : ℝ)) + 1 = (92/25 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.159198501586 : ℝ) : ℝ) ≤ ((0.131865167186 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.131865167186 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi

/-- `sigma 3 (469/100) (369/100)` at the left end of a `[13/5, 27/10]` panel of `entry_i_2`. -/
private theorem sigma_c5_469_100 :
    (0.133074802122 : ℝ) ≤ Wu04Integral.sigma 3 ((469/100 : ℝ)) ((369/100 : ℝ)) := by
  have hlow := sigma_lower_bound (a := 3) (b := (469/100 : ℝ)) (c := (369/100 : ℝ)) (m := (569/200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 10
  rw [log_div (by norm_num : ((469/100 : ℝ) : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  simp only [show (3 : ℝ) - 1 = 2 by norm_num,
    show (((469/100 : ℝ)) - 1) = (369/100 : ℝ) by norm_num] at hlow
  simp only [integral_log_mul_sub_pow (a := 2) (b := (369/100 : ℝ)) (m := (569/200 : ℝ))
    (by norm_num) (by norm_num)] at hlow
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlow
  norm_num [Nat.choose] at hlow
  have hdiff_lo : (0.446820293776 : ℝ) ≤ log ((469/100 : ℝ)) - log 3 := by
    linarith [log_469_100.1, log_three_bounds.2]
  have hq : (0 : ℝ) ≤ log ((369/100 : ℝ)) := by linarith [log_369_100.1]
  have hp : (0 : ℝ) ≤ (0.446820293776 : ℝ) := by norm_num
  have hlo' : (0.58338039754583205892 : ℝ) ≤ log ((369/100 : ℝ)) * (log ((469/100 : ℝ)) - log 3) := by
    have hm := mul_le_mul log_369_100.1 hdiff_lo hp hq
    have hc : (0.58338039754583205892 : ℝ) ≤ (1.305626458046 : ℝ) * (0.446820293776 : ℝ) := by norm_num
    linarith [hm, hc]
  linarith [hlow, hlo', log_369_100.1, log_369_100.2, log_469_100.1, log_469_100.2,
    log_three_bounds.1, log_three_bounds.2, log_two_bounds.1, log_two_bounds.2]

/-- `sigma0 ((269/100 : ℝ))` at a `[13/5, 27/10]` panel endpoint. -/
private theorem sigma0_c5_269_100 :
    (0.16065887261 : ℝ) ≤ Wu04Integral.sigma0 ((269/100 : ℝ)) := by
  have h := sigma_c5_469_100
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  unfold Wu04Integral.sigma0
  rw [show ((269/100 : ℝ)) + 2 = (469/100 : ℝ) by norm_num, show ((269/100 : ℝ)) + 1 = (369/100 : ℝ) by norm_num]
  refine le_trans ?_ (div_le_div_of_nonneg_right h hKpos.le)
  calc ((0.16065887261 : ℝ) : ℝ) ≤ ((0.133074802122 : ℝ) : ℝ) / (0.828306585) := by norm_num
    _ ≤ ((0.133074802122 : ℝ) : ℝ) / (1 - Wu04Integral.sigma 3 5 4) :=
        div_le_div_of_nonneg_left (by norm_num) hKpos hKhi
/-- Lower bound of `sigma0' ((13/5 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_260_100 :
    (0.1433460154 : ℝ) ≤
      (log (((13/5 : ℝ) + 2) / 3) / ((13/5 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_23_5
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.427444014813 : ℝ) ≤ log ((23/5 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((13/5 : ℝ) + 2) / 3) = ((23/5 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1433460154 : ℝ)
      ≤ (0.427444014813 : ℝ) / (((13/5 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((23/5 : ℝ)) - log 3) / (((13/5 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((23/5 : ℝ)) - log 3) / (((13/5 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((261/100 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_261_100 :
    (0.1436751618 : ℝ) ≤
      (log (((261/100 : ℝ) + 2) / 3) / ((261/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_461_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.429615568326 : ℝ) ≤ log ((461/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((261/100 : ℝ) + 2) / 3) = ((461/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1436751618 : ℝ)
      ≤ (0.429615568326 : ℝ) / (((261/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((461/100 : ℝ)) - log 3) / (((261/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((461/100 : ℝ)) - log 3) / (((261/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((131/50 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_262_100 :
    (0.1440009203 : ℝ) ≤
      (log (((131/50 : ℝ) + 2) / 3) / ((131/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_231_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.431782416411 : ℝ) ≤ log ((231/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((131/50 : ℝ) + 2) / 3) = ((231/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1440009203 : ℝ)
      ≤ (0.431782416411 : ℝ) / (((131/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((231/50 : ℝ)) - log 3) / (((131/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((231/50 : ℝ)) - log 3) / (((131/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((263/100 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_263_100 :
    (0.1443233259 : ℝ) ≤
      (log (((263/100 : ℝ) + 2) / 3) / ((263/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_463_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.433944579416 : ℝ) ≤ log ((463/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((263/100 : ℝ) + 2) / 3) = ((463/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1443233259 : ℝ)
      ≤ (0.433944579416 : ℝ) / (((263/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((463/100 : ℝ)) - log 3) / (((263/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((463/100 : ℝ)) - log 3) / (((263/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((66/25 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_264_100 :
    (0.1446424128 : ℝ) ≤
      (log (((66/25 : ℝ) + 2) / 3) / ((66/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_116_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.436102077556 : ℝ) ≤ log ((116/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((66/25 : ℝ) + 2) / 3) = ((116/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1446424128 : ℝ)
      ≤ (0.436102077556 : ℝ) / (((66/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((116/25 : ℝ)) - log 3) / (((66/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((116/25 : ℝ)) - log 3) / (((66/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((53/20 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_265_100 :
    (0.144958215 : ℝ) ≤
      (log (((53/20 : ℝ) + 2) / 3) / ((53/20 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_93_20
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.438254930917 : ℝ) ≤ log ((93/20 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((53/20 : ℝ) + 2) / 3) = ((93/20 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.144958215 : ℝ)
      ≤ (0.438254930917 : ℝ) / (((53/20 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((93/20 : ℝ)) - log 3) / (((53/20 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((93/20 : ℝ)) - log 3) / (((53/20 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((133/50 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_266_100 :
    (0.145270766 : ℝ) ≤
      (log (((133/50 : ℝ) + 2) / 3) / ((133/50 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_233_50
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.440403159455 : ℝ) ≤ log ((233/50 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((133/50 : ℝ) + 2) / 3) = ((233/50 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.145270766 : ℝ)
      ≤ (0.440403159455 : ℝ) / (((133/50 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((233/50 : ℝ)) - log 3) / (((133/50 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((233/50 : ℝ)) - log 3) / (((133/50 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((267/100 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_267_100 :
    (0.1455800988 : ℝ) ≤
      (log (((267/100 : ℝ) + 2) / 3) / ((267/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_467_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.442546782998 : ℝ) ≤ log ((467/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((267/100 : ℝ) + 2) / 3) = ((467/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1455800988 : ℝ)
      ≤ (0.442546782998 : ℝ) / (((267/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((467/100 : ℝ)) - log 3) / (((267/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((467/100 : ℝ)) - log 3) / (((267/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((67/25 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_268_100 :
    (0.1458862461 : ℝ) ≤
      (log (((67/25 : ℝ) + 2) / 3) / ((67/25 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_117_25
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.444685821247 : ℝ) ≤ log ((117/25 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((67/25 : ℝ) + 2) / 3) = ((117/25 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1458862461 : ℝ)
      ≤ (0.444685821247 : ℝ) / (((67/25 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((117/25 : ℝ)) - log 3) / (((67/25 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((117/25 : ℝ)) - log 3) / (((67/25 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Lower bound of `sigma0' ((269/100 : ℝ))`, the tangent slope of a `[13/5, 27/10]` panel. -/
private theorem sigma0_deriv_lower_c5_269_100 :
    (0.1461892404 : ℝ) ≤
      (log (((269/100 : ℝ) + 2) / 3) / ((269/100 : ℝ) + 1)) / (1 - Wu04Integral.sigma 3 5 4) := by
  have hx := log_469_100
  have h3 := log_three_bounds
  have hK := sigma_3_5_4_bounds_exact
  have hKpos : (0 : ℝ) < 1 - Wu04Integral.sigma 3 5 4 := by linarith [hK.2]
  have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by linarith [hK.1]
  have hnum : (0.446820293776 : ℝ) ≤ log ((469/100 : ℝ)) - log 3 := by
    linarith [hx.1, h3.2]
  rw [show (((269/100 : ℝ) + 2) / 3) = ((469/100 : ℝ)) / 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), div_div]
  calc (0.1461892404 : ℝ)
      ≤ (0.446820293776 : ℝ) / (((269/100 : ℝ) + 1) * (0.828306585 : ℝ)) := by norm_num
    _ ≤ (log ((469/100 : ℝ)) - log 3) / (((269/100 : ℝ) + 1) * (0.828306585)) :=
        div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ (log ((469/100 : ℝ)) - log 3) / (((269/100 : ℝ) + 1) * (1 - Wu04Integral.sigma 3 5 4)) := by
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left hKhi (by norm_num)

/-- Second-order panel 0 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_0 :
    (0.0002847310288709 : ℝ) ≤ ∫ t in (13/5 : ℝ)..(261/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (13/5 : ℝ)) (b := (261/100 : ℝ)) (A := (0.147627867863 : ℝ))
    (B := (0.1433460154 : ℝ)) (C := (0.016350488645 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_260_100) (sigma0_deriv_lower_c5_260_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.528227857026 : ℝ) := by
        have hle : s + 2 ≤ (461/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_461_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.528227857026 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((13/5 : ℝ) + 2) * ((13/5 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((13/5 : ℝ) + 2) * ((13/5 : ℝ) + 1) = ((13/5 : ℝ) + 1) / ((13/5 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.35299312728617391304 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((361/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((361/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (361/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.016350488645 : ℝ))) ≤ (0.35299312728617391304 : ℝ) / (((361/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.35299312728617391304 : ℝ) / (((361/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.35299312728617391304 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.35299312728617391304 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_261_260
  rw [show ((261/100 : ℝ)) / ((13/5 : ℝ)) = (261/260 : ℝ) by norm_num] at hp
  have hX : ((0.147627867863 : ℝ) - (0.1433460154 : ℝ) * (13/5 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.147627867863 : ℝ) - (0.1433460154 : ℝ) * (13/5 : ℝ)) * log (261/260) ≥
      (((0.147627867863 : ℝ) - (0.1433460154 : ℝ) * (13/5 : ℝ))) * (0.00383877630717 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.016350488645 : ℝ) * (13/5 : ℝ) ^ 2) * log (261/260) ≥
      ((0.016350488645 : ℝ) * (13/5 : ℝ) ^ 2) * (0.00383877630716 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 1 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_1 :
    (0.0002863893113555 : ℝ) ≤ ∫ t in (261/100 : ℝ)..(131/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (261/100 : ℝ)) (b := (131/50 : ℝ)) (A := (0.149062970466 : ℝ))
    (B := (0.1436751618 : ℝ)) (C := (0.0161821876702 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_261_100) (sigma0_deriv_lower_c5_261_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.530394705111 : ℝ) := by
        have hle : s + 2 ≤ (231/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_231_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.530394705111 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((261/100 : ℝ) + 2) * ((261/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((261/100 : ℝ) + 2) * ((261/100 : ℝ) + 1) = ((261/100 : ℝ) + 1) / ((261/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.35129784385268763557 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((181/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((181/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (181/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.0161821876702 : ℝ))) ≤ (0.35129784385268763557 : ℝ) / (((181/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.35129784385268763557 : ℝ) / (((181/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.35129784385268763557 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.35129784385268763557 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_262_261
  rw [show ((131/50 : ℝ)) / ((261/100 : ℝ)) = (262/261 : ℝ) by norm_num] at hp
  have hX : ((0.149062970466 : ℝ) - (0.1436751618 : ℝ) * (261/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.149062970466 : ℝ) - (0.1436751618 : ℝ) * (261/100 : ℝ)) * log (262/261) ≥
      (((0.149062970466 : ℝ) - (0.1436751618 : ℝ) * (261/100 : ℝ))) * (0.00382409643841 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.0161821876702 : ℝ) * (261/100 : ℝ) ^ 2) * log (262/261) ≥
      ((0.0161821876702 : ℝ) * (261/100 : ℝ) ^ 2) * (0.0038240964384 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 2 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_2 :
    (0.0002880411636853 : ℝ) ≤ ∫ t in (131/50 : ℝ)..(263/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (131/50 : ℝ)) (b := (263/100 : ℝ)) (A := (0.150501347251 : ℝ))
    (B := (0.1440009203 : ℝ)) (C := (0.01601561163636 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_262_100) (sigma0_deriv_lower_c5_262_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.532556868116 : ℝ) := by
        have hle : s + 2 ≤ (463/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_463_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.532556868116 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((131/50 : ℝ) + 2) * ((131/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((131/50 : ℝ) + 2) * ((131/50 : ℝ) + 1) = ((131/50 : ℝ) + 1) / ((131/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.34960520409378354978 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((363/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((363/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (363/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01601561163636 : ℝ))) ≤ (0.34960520409378354978 : ℝ) / (((363/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.34960520409378354978 : ℝ) / (((363/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.34960520409378354978 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.34960520409378354978 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_263_262
  rw [show ((263/100 : ℝ)) / ((131/50 : ℝ)) = (263/262 : ℝ) by norm_num] at hp
  have hX : ((0.150501347251 : ℝ) - (0.1440009203 : ℝ) * (131/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.150501347251 : ℝ) - (0.1440009203 : ℝ) * (131/50 : ℝ)) * log (263/262) ≥
      (((0.150501347251 : ℝ) - (0.1440009203 : ℝ) * (131/50 : ℝ))) * (0.00380952841667 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01601561163636 : ℝ) * (131/50 : ℝ) ^ 2) * log (263/262) ≥
      ((0.01601561163636 : ℝ) * (131/50 : ℝ) ^ 2) * (0.00380952841666 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 3 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_3 :
    (0.0002896865954269 : ℝ) ≤ ∫ t in (263/100 : ℝ)..(66/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (263/100 : ℝ)) (b := (66/25 : ℝ)) (A := (0.151942964505 : ℝ))
    (B := (0.1443233259 : ℝ)) (C := (0.0158507394525 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_263_100) (sigma0_deriv_lower_c5_263_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.534714366256 : ℝ) := by
        have hle : s + 2 ≤ (116/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_116_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.534714366256 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((263/100 : ℝ) + 2) * ((263/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((263/100 : ℝ) + 2) * ((263/100 : ℝ) + 1) = ((263/100 : ℝ) + 1) / ((263/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.34791520102171058315 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((91/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((91/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (91/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.0158507394525 : ℝ))) ≤ (0.34791520102171058315 : ℝ) / (((91/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.34791520102171058315 : ℝ) / (((91/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.34791520102171058315 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.34791520102171058315 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_264_263
  rw [show ((66/25 : ℝ)) / ((263/100 : ℝ)) = (264/263 : ℝ) by norm_num] at hp
  have hX : ((0.151942964505 : ℝ) - (0.1443233259 : ℝ) * (263/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.151942964505 : ℝ) - (0.1443233259 : ℝ) * (263/100 : ℝ)) * log (264/263) ≥
      (((0.151942964505 : ℝ) - (0.1443233259 : ℝ) * (263/100 : ℝ))) * (0.00379507096856 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.0158507394525 : ℝ) * (263/100 : ℝ) ^ 2) * log (264/263) ≥
      ((0.0158507394525 : ℝ) * (263/100 : ℝ) ^ 2) * (0.00379507096855 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 4 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_4 :
    (0.000291325616632 : ℝ) ≤ ∫ t in (66/25 : ℝ)..(53/20 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (66/25 : ℝ)) (b := (53/20 : ℝ)) (A := (0.153387788851 : ℝ))
    (B := (0.1446424128 : ℝ)) (C := (0.01568755033457 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_264_100) (sigma0_deriv_lower_c5_264_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.536867219617 : ℝ) := by
        have hle : s + 2 ≤ (93/20 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_93_20.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.536867219617 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((66/25 : ℝ) + 2) * ((66/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((66/25 : ℝ) + 2) * ((66/25 : ℝ) + 1) = ((66/25 : ℝ) + 1) / ((66/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.34622782766368965517 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((73/20 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((73/20 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (73/20 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01568755033457 : ℝ))) ≤ (0.34622782766368965517 : ℝ) / (((73/20 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.34622782766368965517 : ℝ) / (((73/20 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.34622782766368965517 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.34622782766368965517 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_265_264
  rw [show ((53/20 : ℝ)) / ((66/25 : ℝ)) = (265/264 : ℝ) by norm_num] at hp
  have hX : ((0.153387788851 : ℝ) - (0.1446424128 : ℝ) * (66/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.153387788851 : ℝ) - (0.1446424128 : ℝ) * (66/25 : ℝ)) * log (265/264) ≥
      (((0.153387788851 : ℝ) - (0.1446424128 : ℝ) * (66/25 : ℝ))) * (0.00378072283991 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01568755033457 : ℝ) * (66/25 : ℝ) ^ 2) * log (265/264) ≥
      ((0.01568755033457 : ℝ) * (66/25 : ℝ) ^ 2) * (0.0037807228399 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 5 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_5 :
    (0.0002929582378545 : ℝ) ≤ ∫ t in (53/20 : ℝ)..(133/50 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (53/20 : ℝ)) (b := (133/50 : ℝ)) (A := (0.154835787261 : ℝ))
    (B := (0.144958215 : ℝ)) (C := (0.01552602380035 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_265_100) (sigma0_deriv_lower_c5_265_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.539015448155 : ℝ) := by
        have hle : s + 2 ≤ (233/50 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_233_50.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.539015448155 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((53/20 : ℝ) + 2) * ((53/20 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((53/20 : ℝ) + 2) * ((53/20 : ℝ) + 1) = ((53/20 : ℝ) + 1) / ((53/20 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.34454307706413978494 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((183/50 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((183/50 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (183/50 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01552602380035 : ℝ))) ≤ (0.34454307706413978494 : ℝ) / (((183/50 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.34454307706413978494 : ℝ) / (((183/50 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.34454307706413978494 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.34454307706413978494 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_266_265
  rw [show ((133/50 : ℝ)) / ((53/20 : ℝ)) = (266/265 : ℝ) by norm_num] at hp
  have hX : ((0.154835787261 : ℝ) - (0.144958215 : ℝ) * (53/20 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.154835787261 : ℝ) - (0.144958215 : ℝ) * (53/20 : ℝ)) * log (266/265) ≥
      (((0.154835787261 : ℝ) - (0.144958215 : ℝ) * (53/20 : ℝ))) * (0.00376648279548 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01552602380035 : ℝ) * (53/20 : ℝ) ^ 2) * log (266/265) ≥
      ((0.01552602380035 : ℝ) * (53/20 : ℝ) ^ 2) * (0.00376648279547 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 6 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_6 :
    (0.0002945844701122 : ℝ) ≤ ∫ t in (133/50 : ℝ)..(267/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (133/50 : ℝ)) (b := (267/100 : ℝ)) (A := (0.156286927041 : ℝ))
    (B := (0.145270766 : ℝ)) (C := (0.01536613966426 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_266_100) (sigma0_deriv_lower_c5_266_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.541159071698 : ℝ) := by
        have hle : s + 2 ≤ (467/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_467_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.541159071698 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((133/50 : ℝ) + 2) * ((133/50 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((133/50 : ℝ) + 2) * ((133/50 : ℝ) + 1) = ((133/50 : ℝ) + 1) / ((133/50 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.34286094228388841201 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((367/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((367/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (367/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01536613966426 : ℝ))) ≤ (0.34286094228388841201 : ℝ) / (((367/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.34286094228388841201 : ℝ) / (((367/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.34286094228388841201 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.34286094228388841201 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_267_266
  rw [show ((267/100 : ℝ)) / ((133/50 : ℝ)) = (267/266 : ℝ) by norm_num] at hp
  have hX : ((0.156286927041 : ℝ) - (0.145270766 : ℝ) * (133/50 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.156286927041 : ℝ) - (0.145270766 : ℝ) * (133/50 : ℝ)) * log (267/266) ≥
      (((0.156286927041 : ℝ) - (0.145270766 : ℝ) * (133/50 : ℝ))) * (0.00375234961856 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01536613966426 : ℝ) * (133/50 : ℝ) ^ 2) * log (267/266) ≥
      ((0.01536613966426 : ℝ) * (133/50 : ℝ) ^ 2) * (0.00375234961855 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 7 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_7 :
    (0.0002962043248699 : ℝ) ≤ ∫ t in (267/100 : ℝ)..(67/25 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (267/100 : ℝ)) (b := (67/25 : ℝ)) (A := (0.157741175826 : ℝ))
    (B := (0.1455800988 : ℝ)) (C := (0.01520787803237 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_267_100) (sigma0_deriv_lower_c5_267_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.543298109947 : ℝ) := by
        have hle : s + 2 ≤ (117/25 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_117_25.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.543298109947 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((267/100 : ℝ) + 2) * ((267/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((267/100 : ℝ) + 2) * ((267/100 : ℝ) + 1) = ((267/100 : ℝ) + 1) / ((267/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.34118141640036616702 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((92/25 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((92/25 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (92/25 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01520787803237 : ℝ))) ≤ (0.34118141640036616702 : ℝ) / (((92/25 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.34118141640036616702 : ℝ) / (((92/25 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.34118141640036616702 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.34118141640036616702 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_268_267
  rw [show ((67/25 : ℝ)) / ((267/100 : ℝ)) = (268/267 : ℝ) by norm_num] at hp
  have hX : ((0.157741175826 : ℝ) - (0.1455800988 : ℝ) * (267/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.157741175826 : ℝ) - (0.1455800988 : ℝ) * (267/100 : ℝ)) * log (268/267) ≥
      (((0.157741175826 : ℝ) - (0.1455800988 : ℝ) * (267/100 : ℝ))) * (0.00373832211061 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01520787803237 : ℝ) * (267/100 : ℝ) ^ 2) * log (268/267) ≥
      ((0.01520787803237 : ℝ) * (267/100 : ℝ) ^ 2) * (0.0037383221106 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 8 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_8 :
    (0.0002978178140401 : ℝ) ≤ ∫ t in (67/25 : ℝ)..(269/100 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (67/25 : ℝ)) (b := (269/100 : ℝ)) (A := (0.159198501586 : ℝ))
    (B := (0.1458862461 : ℝ)) (C := (0.0150512192975 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_268_100) (sigma0_deriv_lower_c5_268_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.545432582476 : ℝ) := by
        have hle : s + 2 ≤ (469/100 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_469_100.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.545432582476 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((67/25 : ℝ) + 2) * ((67/25 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((67/25 : ℝ) + 2) * ((67/25 : ℝ) + 1) = ((67/25 : ℝ) + 1) / ((67/25 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.33950449250878632478 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((369/100 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((369/100 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (369/100 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.0150512192975 : ℝ))) ≤ (0.33950449250878632478 : ℝ) / (((369/100 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.33950449250878632478 : ℝ) / (((369/100 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.33950449250878632478 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.33950449250878632478 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_269_268
  rw [show ((269/100 : ℝ)) / ((67/25 : ℝ)) = (269/268 : ℝ) by norm_num] at hp
  have hX : ((0.159198501586 : ℝ) - (0.1458862461 : ℝ) * (67/25 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.159198501586 : ℝ) - (0.1458862461 : ℝ) * (67/25 : ℝ)) * log (269/268) ≥
      (((0.159198501586 : ℝ) - (0.1458862461 : ℝ) * (67/25 : ℝ))) * (0.00372439909099 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.0150512192975 : ℝ) * (67/25 : ℝ) ^ 2) * log (269/268) ≥
      ((0.0150512192975 : ℝ) * (67/25 : ℝ) ^ 2) * (0.00372439909098 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- Second-order panel 9 of the `[13/5, 27/10]` `sigma0` quadrature. -/
private theorem sigma0_panel_val2_c5_9 :
    (0.000299424949951 : ℝ) ≤ ∫ t in (269/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have hp := sigma0_panel_lower2_c2 (a := (269/100 : ℝ)) (b := (27/10 : ℝ)) (A := (0.16065887261 : ℝ))
    (B := (0.1461892404 : ℝ)) (C := (0.01489614413443 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    (sigma0_c5_269_100) (sigma0_deriv_lower_c5_269_100)
    (fun s hs => by
      have hlog1 : log ((s + 2) / 3) = log (s + 2) - log 3 := by
        rw [Real.log_div (by linarith [hs.1]) (by norm_num)]
      have hlog2 : log (s + 2) ≤ (1.547562508733 : ℝ) := by
        have hle : s + 2 ≤ (47/10 : ℝ) := by linarith [hs.2]
        have h := Real.log_le_log (by linarith [hs.1]) hle
        linarith [h, log_47_10.2]
      have hlog3 : log (s + 2) - log 3 ≤ (1.547562508733 - 1.09861228866 : ℝ) := by
        linarith [hlog2, log_three_bounds.1]
      have hfrac : 1 / ((269/100 : ℝ) + 2) * ((269/100 : ℝ) + 1) ≤ 1 / (s + 2) * (s + 1) := by
        rw [show 1 / ((269/100 : ℝ) + 2) * ((269/100 : ℝ) + 1) = ((269/100 : ℝ) + 1) / ((269/100 : ℝ) + 2) by ring,
          show 1 / (s + 2) * (s + 1) = (s + 1) / (s + 2) by ring,
          div_le_div_iff₀ (by norm_num) (by linarith [hs.1])]
        nlinarith [hs.1]
      have hnum : (0.33783016372230916844 : ℝ) ≤ 1 / (s + 2) * (s + 1) - log ((s + 2) / 3) := by
        rw [hlog1]
        linarith [hfrac, hlog3]
      have hden : (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) ≤
          ((37/10 : ℝ)) ^ 2 * (0.828306585 : ℝ) := by
        have hKhi : 1 - Wu04Integral.sigma 3 5 4 ≤ (0.828306585 : ℝ) := by
          linarith [sigma_3_5_4_bounds_exact.1]
        have hsq : (s + 1) ^ 2 ≤ ((37/10 : ℝ)) ^ 2 := by
          have h1 : s + 1 ≤ (37/10 : ℝ) := by linarith [hs.2]
          nlinarith [hs.1]
        exact mul_le_mul hsq hKhi (by linarith [sigma_3_5_4_bounds_exact.2]) (by positivity)
      have hpos : (0 : ℝ) < (s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4) := by
        have hK : 0 < 1 - Wu04Integral.sigma 3 5 4 := by linarith [sigma_3_5_4_bounds_exact.2]
        have hs1 : (0 : ℝ) < s + 1 := by linarith [hs.1]
        positivity
      have step0 : (2 * ((0.01489614413443 : ℝ))) ≤ (0.33783016372230916844 : ℝ) / (((37/10 : ℝ)) ^ 2 * (0.828306585 : ℝ)) :=
        by norm_num
      have step1 : (0.33783016372230916844 : ℝ) / (((37/10 : ℝ)) ^ 2 * (0.828306585 : ℝ))
          ≤ (0.33783016372230916844 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden
      have step2 : (0.33783016372230916844 : ℝ) / ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4))
          ≤ (1 / (s + 2) * (s + 1) - log ((s + 2) / 3)) /
              ((s + 1) ^ 2 * (1 - Wu04Integral.sigma 3 5 4)) :=
        div_le_div_of_nonneg_right hnum hpos.le
      rw [div_div]
      exact step0.trans (step1.trans step2))
  have hl := log_270_269
  rw [show ((27/10 : ℝ)) / ((269/100 : ℝ)) = (270/269 : ℝ) by norm_num] at hp
  have hX : ((0.16065887261 : ℝ) - (0.1461892404 : ℝ) * (269/100 : ℝ)) ≤ 0 := by norm_num
  have hmul1 : ((0.16065887261 : ℝ) - (0.1461892404 : ℝ) * (269/100 : ℝ)) * log (270/269) ≥
      (((0.16065887261 : ℝ) - (0.1461892404 : ℝ) * (269/100 : ℝ))) * (0.00371057939654 : ℝ) :=
    mul_le_mul_of_nonpos_left hl.2 hX
  have hmul2 : ((0.01489614413443 : ℝ) * (269/100 : ℝ) ^ 2) * log (270/269) ≥
      ((0.01489614413443 : ℝ) * (269/100 : ℝ) ^ 2) * (0.00371057939653 : ℝ) :=
    mul_le_mul_of_nonneg_left hl.1 (by norm_num)
  linarith [hp, hmul1, hmul2]

/-- The ten-panel second-order sandwich for `∫ sigma0 t/(2t)` on `[13/5, 27/10]`. -/
private theorem sigma0_integral_lower2_c5 :
    (0.0029211635127983 : ℝ) ≤ ∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t) := by
  have s10 : (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (13/5 : ℝ)..(261/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (261/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s0 : (∫ t in (261/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (261/100 : ℝ)..(131/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (131/50 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s1 : (∫ t in (131/50 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (131/50 : ℝ)..(263/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (263/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s2 : (∫ t in (263/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (263/100 : ℝ)..(66/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (66/25 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s3 : (∫ t in (66/25 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (66/25 : ℝ)..(53/20 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (53/20 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s4 : (∫ t in (53/20 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (53/20 : ℝ)..(133/50 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (133/50 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s5 : (∫ t in (133/50 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (133/50 : ℝ)..(267/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (267/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s6 : (∫ t in (267/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (267/100 : ℝ)..(67/25 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (67/25 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s7 : (∫ t in (67/25 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (67/25 : ℝ)..(269/100 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (269/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  have s8 : (∫ t in (269/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) =
      (∫ t in (269/100 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) + (∫ t in (27/10 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sigma0_div_two_integrable (by norm_num) (by norm_num))
      (sigma0_div_two_integrable (by norm_num) (by norm_num))).symm
  rw [s10, s0, s1, s2, s3, s4, s5, s6, s7, s8]
  linarith [sigma0_panel_val2_c5_0, sigma0_panel_val2_c5_1, sigma0_panel_val2_c5_2, sigma0_panel_val2_c5_3, sigma0_panel_val2_c5_4, sigma0_panel_val2_c5_5, sigma0_panel_val2_c5_6, sigma0_panel_val2_c5_7, sigma0_panel_val2_c5_8, sigma0_panel_val2_c5_9]

/-- `∫ log (t+1)/t` on `[13/5, 27/10]` from the eight-term expansion at `c = 53/20`. -/
private theorem log_succ_integral_c5_lower :
    (0.048858995485099 : ℝ) ≤ ∫ t in (13/5 : ℝ)..(27/10 : ℝ), log (t + 1) / t := by
  have hxr : ∀ t ∈ uIcc (13/5 : ℝ) (27/10 : ℝ),
      |((53/20 : ℝ) - t) / (53/20 + 1)| ≤ (1/73 : ℝ) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (13/5 : ℝ) ≤ 27/10)] at ht
    rw [abs_le]
    have hb : (0 : ℝ) < 53/20 + 1 := by norm_num
    constructor
    · rw [le_div_iff₀ hb]
      nlinarith [ht.1, ht.2]
    · rw [div_le_iff₀ hb]
      nlinarith [ht.1, ht.2]
  have h := log_succ_integral_lower (a := (13/5 : ℝ)) (b := (27/10 : ℝ)) (c := (53/20 : ℝ))
    (r := (1/73 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hxr 8
  have hc := log_73_20
  have hl := log_27_26
  rw [show ((27/10 : ℝ) / (13/5)) = 27/26 by norm_num] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose] at h
  norm_num at h
  have hmul : (1.29472716759 : ℝ) * (0.03774032798284 : ℝ) ≤ log (73/20) * log (27/26) := by
    have hm := mul_le_mul hc.1 hl.1 (by norm_num) (by linarith [hc.1])
    linarith [hm]
  linarith [h, hmul, hl.2]
/-- On `[13/5, 27/10]` the `Xi1` kernel has both indicators fixed whenever `sp - 2 ≤ 13/5`
(the second window sits below the panel and the first covers it). -/
private theorem Xi1_general_eq_c5 {s sp t : ℝ} (hsp : sp - 2 < 13/5)
    (h1 : (13/5 : ℝ) ≤ t) (h2 : t ≤ 27/10) :
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
below `[13/5, 27/10]`. -/
private theorem Xi1_general_integral_c5 {s sp : ℝ} (hsp : sp - 2 < 13/5)
    (hPpos : 0 < (s - 1) * (sp - 1)) :
    (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Functional.Xi1 s sp t) =
      log (16 / ((s - 1) * (sp - 1))) *
          (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) +
        (∫ t in (13/5 : ℝ)..(27/10 : ℝ), log (t + 1) / t) -
          (log ((s - 1) * (sp - 1)) / 2) *
            (∫ t in (13/5 : ℝ)..(27/10 : ℝ), 1 / t) := by
  have hI1 := sigma0_div_two_integrable (a := (13/5 : ℝ)) (b := (27/10 : ℝ))
    (by norm_num) (by norm_num)
  have hI2 : IntervalIntegrable (fun t : ℝ => log (t + 1) / t) volume (13/5 : ℝ) (27/10 : ℝ) :=
    log_succ_div_integrable_exp (by norm_num) (by norm_num)
  have hI3 : IntervalIntegrable (fun t : ℝ => 1 / t) volume (13/5 : ℝ) (27/10 : ℝ) :=
    inv_integrable_exp (by norm_num) (by norm_num)
  have hpt : ∀ t ∈ uIcc (13/5 : ℝ) (27/10 : ℝ),
      Wu04Functional.Xi1 s sp t =
        log (16 / ((s - 1) * (sp - 1))) * (Wu04Integral.sigma0 t / (2 * t)) +
          (log (t + 1) / t - (log ((s - 1) * (sp - 1)) / 2) * (1 / t)) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (13/5 : ℝ) ≤ 27/10)] at ht
    rw [Xi1_general_eq_c5 hsp ht.1 ht.2]
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

/-- `integralMatrix 4 2` is the `Xi1 (13/5) (179/50)` quadrature on `[13/5, 27/10]`. -/
private theorem integralMatrix_4_5_eq :
    Wu04Table.integralMatrix 4 5 =
      ∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Functional.Xi1 ((13/5 : ℝ)) ((179/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_4_2` of Wu's Section 7 matrix**, certified on the `[13/5, 27/10]` panel. -/
private theorem entry_4_5_certified :
    (260625 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 4 5 := by
  rw [integralMatrix_4_5_eq,
    Xi1_general_integral_c5 (s := (13/5 : ℝ)) (sp := (179/50 : ℝ)) (by norm_num) (by norm_num),
    show (((13/5 : ℝ)) - 1) * ((179/50 : ℝ) - 1) = (516/125 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c5
  have hB := log_succ_integral_c5_lower
  have h1t := integral_one_div_exp (a := (13/5 : ℝ)) (b := (27/10 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_27_26
  have h4 := log_four_bounds
  have hP := log_P_4_bounds
  rw [h1t]
  have hLP : (1.3547956940207 : ℝ) ≤ log (16 / ((516/125 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3547956940207 : ℝ) * (0.0029211635127983 : ℝ) ≤
      log (16 / ((516/125 : ℝ))) * (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((516/125 : ℝ)) / 2) * log (27/26) ≤
      (1.4177930281793 : ℝ) / 2 * (0.03774032798285 : ℝ) := by
    have h2 : log ((516/125 : ℝ)) / 2 ≤ (1.4177930281793 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_4_2` in the shape the matrix file states it. -/
private theorem entry_4_5_leaf :
    (Wu04Table.candidateMatrixQ 4 5 : ℝ) ≤ Wu04Table.integralMatrix 4 5 := by
  have hc : (Wu04Table.candidateMatrixQ 4 5 : ℝ) = 260625 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_4_5_certified

/-- `integralMatrix 5 2` is the `Xi1 (27/10) (347/100)` quadrature on `[13/5, 27/10]`. -/
private theorem integralMatrix_5_5_eq :
    Wu04Table.integralMatrix 5 5 =
      ∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Functional.Xi1 ((27/10 : ℝ)) ((347/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_5_2` of Wu's Section 7 matrix**, certified on the `[13/5, 27/10]` panel. -/
private theorem entry_5_5_certified :
    (256909 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 5 5 := by
  rw [integralMatrix_5_5_eq,
    Xi1_general_integral_c5 (s := (27/10 : ℝ)) (sp := (347/100 : ℝ)) (by norm_num) (by norm_num),
    show (((27/10 : ℝ)) - 1) * ((347/100 : ℝ) - 1) = (4199/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c5
  have hB := log_succ_integral_c5_lower
  have h1t := integral_one_div_exp (a := (13/5 : ℝ)) (b := (27/10 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_27_26
  have h4 := log_four_bounds
  have hP := log_P_5_bounds
  rw [h1t]
  have hLP : (1.33774232049788 : ℝ) ≤ log (16 / ((4199/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.33774232049788 : ℝ) * (0.0029211635127983 : ℝ) ≤
      log (16 / ((4199/1000 : ℝ))) * (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4199/1000 : ℝ)) / 2) * log (27/26) ≤
      (1.43484640170212 : ℝ) / 2 * (0.03774032798285 : ℝ) := by
    have h2 : log ((4199/1000 : ℝ)) / 2 ≤ (1.43484640170212 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_5_2` in the shape the matrix file states it. -/
private theorem entry_5_5_leaf :
    (Wu04Table.candidateMatrixQ 5 5 : ℝ) ≤ Wu04Table.integralMatrix 5 5 := by
  have hc : (Wu04Table.candidateMatrixQ 5 5 : ℝ) = 256909 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_5_5_certified

/-- `integralMatrix 6 2` is the `Xi1 (14/5) (167/50)` quadrature on `[13/5, 27/10]`. -/
private theorem integralMatrix_6_5_eq :
    Wu04Table.integralMatrix 6 5 =
      ∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Functional.Xi1 ((14/5 : ℝ)) ((167/50 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_6_2` of Wu's Section 7 matrix**, certified on the `[13/5, 27/10]` panel. -/
private theorem entry_6_5_certified :
    (256236 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 6 5 := by
  rw [integralMatrix_6_5_eq,
    Xi1_general_integral_c5 (s := (14/5 : ℝ)) (sp := (167/50 : ℝ)) (by norm_num) (by norm_num),
    show (((14/5 : ℝ)) - 1) * ((167/50 : ℝ) - 1) = (1053/250 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c5
  have hB := log_succ_integral_c5_lower
  have h1t := integral_one_div_exp (a := (13/5 : ℝ)) (b := (27/10 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_27_26
  have h4 := log_four_bounds
  have hP := log_P_6_bounds
  rw [h1t]
  have hLP : (1.3346511279282 : ℝ) ≤ log (16 / ((1053/250 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3346511279282 : ℝ) * (0.0029211635127983 : ℝ) ≤
      log (16 / ((1053/250 : ℝ))) * (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((1053/250 : ℝ)) / 2) * log (27/26) ≤
      (1.4379375942718 : ℝ) / 2 * (0.03774032798285 : ℝ) := by
    have h2 : log ((1053/250 : ℝ)) / 2 ≤ (1.4379375942718 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_6_2` in the shape the matrix file states it. -/
private theorem entry_6_5_leaf :
    (Wu04Table.candidateMatrixQ 6 5 : ℝ) ≤ Wu04Table.integralMatrix 6 5 := by
  have hc : (Wu04Table.candidateMatrixQ 6 5 : ℝ) = 256236 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_6_5_certified

/-- `integralMatrix 7 2` is the `Xi1 (29/10) (319/100)` quadrature on `[13/5, 27/10]`. -/
private theorem integralMatrix_7_5_eq :
    Wu04Table.integralMatrix 7 5 =
      ∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Functional.Xi1 ((29/10 : ℝ)) ((319/100 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_7_2` of Wu's Section 7 matrix**, certified on the `[13/5, 27/10]` panel. -/
private theorem entry_7_5_certified :
    (258890 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 7 5 := by
  rw [integralMatrix_7_5_eq,
    Xi1_general_integral_c5 (s := (29/10 : ℝ)) (sp := (319/100 : ℝ)) (by norm_num) (by norm_num),
    show (((29/10 : ℝ)) - 1) * ((319/100 : ℝ) - 1) = (4161/1000 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c5
  have hB := log_succ_integral_c5_lower
  have h1t := integral_one_div_exp (a := (13/5 : ℝ)) (b := (27/10 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_27_26
  have h4 := log_four_bounds
  have hP := log_P_7_bounds
  rw [h1t]
  have hLP : (1.34683329219 : ℝ) ≤ log (16 / ((4161/1000 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.34683329219 : ℝ) * (0.0029211635127983 : ℝ) ≤
      log (16 / ((4161/1000 : ℝ))) * (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4161/1000 : ℝ)) / 2) * log (27/26) ≤
      (1.42575543001 : ℝ) / 2 * (0.03774032798285 : ℝ) := by
    have h2 : log ((4161/1000 : ℝ)) / 2 ≤ (1.42575543001 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_7_2` in the shape the matrix file states it. -/
private theorem entry_7_5_leaf :
    (Wu04Table.candidateMatrixQ 7 5 : ℝ) ≤ Wu04Table.integralMatrix 7 5 := by
  have hc : (Wu04Table.candidateMatrixQ 7 5 : ℝ) = 258890 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_7_5_certified

/-- `integralMatrix 8 2` is the `Xi1 (3) (3)` quadrature on `[13/5, 27/10]`. -/
private theorem integralMatrix_8_5_eq :
    Wu04Table.integralMatrix 8 5 =
      ∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Functional.Xi1 ((3 : ℝ)) ((3 : ℝ)) t := by
  simp only [Wu04Table.integralMatrix, Wu04Table.tableKernel, Wu04Functional.grid,
    Wu04Functional.tableSp]
  norm_num

/-- **`entry_8_2` of Wu's Section 7 matrix**, certified on the `[13/5, 27/10]` panel. -/
private theorem entry_8_5_certified :
    (267489 / 10000000 : ℝ) ≤ Wu04Table.integralMatrix 8 5 := by
  rw [integralMatrix_8_5_eq,
    Xi1_general_integral_c5 (s := (3 : ℝ)) (sp := (3 : ℝ)) (by norm_num) (by norm_num),
    show (((3 : ℝ)) - 1) * ((3 : ℝ) - 1) = (4 : ℝ) by norm_num]
  have hA := sigma0_integral_lower2_c5
  have hB := log_succ_integral_c5_lower
  have h1t := integral_one_div_exp (a := (13/5 : ℝ)) (b := (27/10 : ℝ))
    (by norm_num) (by norm_num)
  have h23 := log_27_26
  have h4 := log_four_bounds
  have hP : (1.3862943611 : ℝ) ≤ log (4) ∧ log (4) ≤ (1.3862943615 : ℝ) := log_four_bounds
  rw [h1t]
  have hLP : (1.3862943607 : ℝ) ≤ log (16 / ((4 : ℝ))) := by
    rw [Real.log_div (by norm_num) (by norm_num),
      show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [h4.1, hP.2]
  have hmul : (1.3862943607 : ℝ) * (0.0029211635127983 : ℝ) ≤
      log (16 / ((4 : ℝ))) * (∫ t in (13/5 : ℝ)..(27/10 : ℝ), Wu04Integral.sigma0 t / (2 * t)) := by
    have hm := mul_le_mul hLP hA (by norm_num) (by linarith [hLP])
    linarith [hm]
  have hlast : (log ((4 : ℝ)) / 2) * log (27/26) ≤
      (1.3862943615 : ℝ) / 2 * (0.03774032798285 : ℝ) := by
    have h2 : log ((4 : ℝ)) / 2 ≤ (1.3862943615 : ℝ) / 2 := by linarith [hP.2]
    exact mul_le_mul h2 h23.2 (by linarith [h23.1]) (by linarith [hP.1])
  linarith [hmul, hB, hlast]

/-- `entry_8_2` in the shape the matrix file states it. -/
private theorem entry_8_5_leaf :
    (Wu04Table.candidateMatrixQ 8 5 : ℝ) ≤ Wu04Table.integralMatrix 8 5 := by
  have hc : (Wu04Table.candidateMatrixQ 8 5 : ℝ) = 267489 / 10000000 := by
    norm_num [Wu04Table.candidateMatrixQ]
  rw [hc]
  exact entry_8_5_certified



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
  exact entry_4_2_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.6, 3.58) dt ≥ 251066/10⁷`.
scipy value 0.0251066062, margin 0.06e−7. -/
theorem entry_4_3 : (candidateMatrixQ 4 3 : ℝ) ≤ integralMatrix 4 3 := by
  exact entry_4_3_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.6, 3.58) dt ≥ 256142/10⁷`.
scipy value 0.0256142905, margin 0.91e−7. -/
theorem entry_4_4 : (candidateMatrixQ 4 4 : ℝ) ≤ integralMatrix 4 4 := by
  exact entry_4_4_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{5,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.6, 3.58) dt ≥ 260625/10⁷`.
scipy value 0.0260625919, margin 0.92e−7. -/
theorem entry_4_5 : (candidateMatrixQ 4 5 : ℝ) ≤ integralMatrix 4 5 := by
  exact entry_4_5_leaf

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
  exact entry_5_2_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.7, 3.47) dt ≥ 247145/10⁷`.
scipy value 0.0247145026, margin 0.03e−7. -/
theorem entry_5_3 : (candidateMatrixQ 5 3 : ℝ) ≤ integralMatrix 5 3 := by
  exact entry_5_3_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.7, 3.47) dt ≥ 252328/10⁷`.
scipy value 0.0252328911, margin 0.91e−7. -/
theorem entry_5_4 : (candidateMatrixQ 5 4 : ℝ) ≤ integralMatrix 5 4 := by
  exact entry_5_4_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{6,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.7, 3.47) dt ≥ 256909/10⁷`.
scipy value 0.0256909762, margin 0.76e−7. -/
theorem entry_5_5 : (candidateMatrixQ 5 5 : ℝ) ≤ integralMatrix 5 5 := by
  exact entry_5_5_leaf

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
  exact entry_6_2_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.8, 3.34) dt ≥ 246434/10⁷`.
scipy value 0.0246434276, margin 0.28e−7. -/
theorem entry_6_3 : (candidateMatrixQ 6 3 : ℝ) ≤ integralMatrix 6 3 := by
  exact entry_6_3_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.8, 3.34) dt ≥ 251637/10⁷`.
scipy value 0.0251637564, margin 0.56e−7. -/
theorem entry_6_4 : (candidateMatrixQ 6 4 : ℝ) ≤ integralMatrix 6 4 := by
  exact entry_6_4_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{7,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.8, 3.34) dt ≥ 256236/10⁷`.
scipy value 0.0256236150, margin 0.15e−7. -/
theorem entry_6_5 : (candidateMatrixQ 6 5 : ℝ) ≤ integralMatrix 6 5 := by
  exact entry_6_5_leaf

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
  exact entry_7_2_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,4} = ∫_{2.4}^{2.5} Ξ₁(t; 2.9, 3.19) dt ≥ 249235/10⁷`.
scipy value 0.0249235289, margin 0.29e−7. -/
theorem entry_7_3 : (candidateMatrixQ 7 3 : ℝ) ≤ integralMatrix 7 3 := by
  exact entry_7_3_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,5} = ∫_{2.5}^{2.6} Ξ₁(t; 2.9, 3.19) dt ≥ 254362/10⁷`.
scipy value 0.0254362110, margin 0.11e−7. -/
theorem entry_7_4 : (candidateMatrixQ 7 4 : ℝ) ≤ integralMatrix 7 4 := by
  exact entry_7_4_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{8,6} = ∫_{2.6}^{2.7} Ξ₁(t; 2.9, 3.19) dt ≥ 258890/10⁷`.
scipy value 0.0258890806, margin 0.81e−7. -/
theorem entry_7_5 : (candidateMatrixQ 7 5 : ℝ) ≤ integralMatrix 7 5 := by
  exact entry_7_5_leaf

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
  exact entry_8_2_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,4} = ∫_{2.4}^{2.5} Ξ₁(t; 3.0, 3.00) dt ≥ 258308/10⁷`.
scipy value 0.0258308467, margin 0.47e−7. -/
theorem entry_8_3 : (candidateMatrixQ 8 3 : ℝ) ≤ integralMatrix 8 3 := by
  exact entry_8_3_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,5} = ∫_{2.5}^{2.6} Ξ₁(t; 3.0, 3.00) dt ≥ 263187/10⁷`.
scipy value 0.0263187595, margin 0.60e−7. -/
theorem entry_8_4 : (candidateMatrixQ 8 4 : ℝ) ≤ integralMatrix 8 4 := by
  exact entry_8_4_leaf

/-- LEAF. Wu 2004 display 7.2, kernel of display 3.21, page 14: `a_{9,6} = ∫_{2.6}^{2.7} Ξ₁(t; 3.0, 3.00) dt ≥ 267489/10⁷`.
scipy value 0.0267489897, margin 0.90e−7. -/
theorem entry_8_5 : (candidateMatrixQ 8 5 : ℝ) ≤ integralMatrix 8 5 := by
  exact entry_8_5_leaf

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

