import LeanLab.RamareSaouter2003.Decomp419a

/-!
Backlund p. 350, displays 21 and 25, and p. 374.
The Gamma remainder separates into the actual periodic Bernoulli integral
and elementary logarithm and arctangent terms.
The Euler summation identity for the continuous Gamma argument was OPEN; it is
proved below (a private development: the digamma series from the Weierstrass
product, Euler--Maclaurin at arctan (a/(c+x)), dominated convergence and the
passage n to infinity). The integral bound and elementary losses are proved
independently.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp419c
open Real Complex MeasureTheory Set Filter Decomp359g Circle419
open scoped Topology

/-! ## Private development for `gamma_stieltjes_expansion`

Everything between this comment and the statement of `gamma_stieltjes_expansion`
is private helper material. The first block (`hasDerivAt_fract_sub_sq` through
`euler_maclaurin_range`) is the periodic-Bernoulli Euler--Maclaurin machinery of
an earlier pass on this unit; the second block (from `one_sub_pow_le_n_mul` to
`log_succ_le_sum_inv`) is the locally uniform Weierstrass limit for
`Complex.GammaSeq` and its digamma series from a later pass; the material from
`trapezoid_sum` on is new here. -/

/-- Backlund p. 350, display 21, the imaginary part of J at one quarter plus iT/2.
The source periodic polynomial is fract u squared minus fract u.
Taking the imaginary part of its reciprocal-square kernel gives this real integral. -/
noncomputable def stirlingImag (T : ℝ) : ℝ :=
  -(T / 2) * ∫ u in Set.Ioi (0 : ℝ),
    (Int.fract u - (Int.fract u) ^ 2) * (u + 1 / 4) /
      ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2
-- ============================================================
-- Carried over from pass 1 (results/RamareSaouter2003-Decomp419c-wip.lean)
-- ============================================================
private theorem hasDerivAt_fract_sub_sq (u : ℝ) (hu : Int.fract u ≠ 0) :
    HasDerivAt (fun v : ℝ => (Int.fract v - (Int.fract v) ^ 2) / 2)
      (1 / 2 - Int.fract u) u := by
  set n : ℤ := ⌊u⌋ with hn
  have hfr : Int.fract u = u - (n : ℝ) := by
    rw [show Int.fract u = u - (⌊u⌋ : ℝ) from rfl, ← hn]
  have hlow : (n : ℝ) < u := by
    rcases lt_or_eq_of_le (Int.floor_le u) with h | h
    · simpa [hn] using h
    · exfalso
      apply hu
      rw [hfr]
      have hnu : (n : ℝ) = u := by simpa [← hn] using h
      rw [hnu, sub_self]
  have hhigh : u < (n : ℝ) + 1 := by
    simpa [hn] using Int.lt_floor_add_one u
  have hmem : Set.Ioo (n : ℝ) ((n : ℝ) + 1) ∈ 𝓝 u := Ioo_mem_nhds hlow hhigh
  have hpt : ∀ v ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), Int.fract v = v - (n : ℝ) := by
    intro v hv
    rw [show Int.fract v = v - (⌊v⌋ : ℝ) from rfl]
    have hfl : ⌊v⌋ = n := Int.floor_eq_iff.mpr ⟨le_of_lt hv.1, hv.2⟩
    rw [hfl]
  have heq : (fun v : ℝ => (Int.fract v - (Int.fract v) ^ 2) / 2) =ᶠ[𝓝 u]
      fun v : ℝ => ((v - (n : ℝ)) - (v - (n : ℝ)) ^ 2) / 2 := by
    filter_upwards [hmem] with v hv
    rw [hpt v hv]
  have hid : HasDerivAt (fun v : ℝ => v - (n : ℝ)) (1 : ℝ) u := by
    simpa using (hasDerivAt_id (x := u)).sub_const (n : ℝ)
  have h2 : HasDerivAt (fun v : ℝ => (v - (n : ℝ)) ^ 2) (2 * (u - (n : ℝ))) u := by
    have hp := hid.pow 2
    have hfun : ((fun v : ℝ => v - (n : ℝ)) ^ 2) = fun v : ℝ => (v - (n : ℝ)) ^ 2 := by
      funext v
      simp
    rw [hfun] at hp
    simpa using hp
  have h1 : HasDerivAt (fun v : ℝ => (v - (n : ℝ)) - (v - (n : ℝ)) ^ 2)
      (1 - 2 * (u - (n : ℝ))) u := hid.sub h2
  have hd : HasDerivAt (fun v : ℝ => ((v - (n : ℝ)) - (v - (n : ℝ)) ^ 2) / 2)
      (1 / 2 - (u - (n : ℝ))) u := by
    have := HasDerivAt.div_const h1 2
    convert this using 1
    ring
  have hmain := hd.congr_of_eventuallyEq heq
  simpa only [hfr] using hmain

/-! ## Brick 2: Euler--Maclaurin on one unit interval, second order

Backlund p. 350 needs the exact Euler-summation remainder for
`log |Gamma(1/4 + iY)|`.  The heart of it is the per-unit-interval identity

  ∫ x in n..n+1, ({x} - {x}^2)/2 * f'' x
      = (f n + f (n+1))/2 - ∫ x in n..n+1, f x,

i.e. Euler--Maclaurin with the periodic Bernoulli polynomial as the exact
remainder kernel.  It is proved here for a `C^2` function on one interval.
No continuity of the fractal part is needed: on `[n, n+1]` the periodic
Bernoulli polynomial is the *polynomial* `((x-n) - (x-n)^2)/2`, which also
vanishes at both endpoints, so both integrations by parts have zero boundary
term. -/

/-- First integration by parts on one unit interval: the sawtooth weight
integrates `f'` to the trapezoid minus the integral. -/
private theorem integral_sawtooth_mul_deriv (f df : ℝ → ℝ) (n : ℕ)
    (hc : ContinuousOn f (Set.Icc (n : ℝ) ((n : ℝ) + 1)))
    (hd : ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt f (df x) x)
    (hi : IntervalIntegrable df volume (n : ℝ) ((n : ℝ) + 1)) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), (x - (n : ℝ) - 1 / 2) * df x) =
      (f (n : ℝ) + f ((n : ℝ) + 1)) / 2 - ∫ x in (n : ℝ)..((n : ℝ) + 1), f x := by
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hcI : ContinuousOn f (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    rwa [Set.uIcc_of_le hle]
  have hdI : ∀ x ∈ Set.Ioo (min (n : ℝ) ((n : ℝ) + 1)) (max (n : ℝ) ((n : ℝ) + 1)),
      HasDerivAt f (df x) x := by
    rw [min_eq_left hle, max_eq_right hle]
    exact hd
  have hcontu : ContinuousOn (fun x : ℝ => x - (n : ℝ) - 1 / 2)
      (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by fun_prop
  have hderu : ∀ x ∈ Set.Ioo (min (n : ℝ) ((n : ℝ) + 1)) (max (n : ℝ) ((n : ℝ) + 1)),
      HasDerivAt (fun y : ℝ => y - (n : ℝ) - 1 / 2) 1 x := by
    intro x _
    simpa using (hasDerivAt_id (x := x)).sub_const ((n : ℝ) + 1 / 2)
  have hmain := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcontu hcI
    hderu hdI intervalIntegrable_const hi
  simp only [one_mul] at hmain
  have hub : ((n : ℝ) + 1) - (n : ℝ) - 1 / 2 = 1 / 2 := by ring
  have hua : (n : ℝ) - (n : ℝ) - 1 / 2 = -(1 / 2) := by ring
  rw [hmain, hub, hua]
  ring

/-- Second integration by parts on one unit interval: the full second-order
Euler--Maclaurin identity with the periodic Bernoulli kernel. -/
private theorem euler_maclaurin_interval (f df d2f : ℝ → ℝ) (n : ℕ)
    (hc : ContinuousOn f (Set.Icc (n : ℝ) ((n : ℝ) + 1)))
    (hc' : ContinuousOn df (Set.Icc (n : ℝ) ((n : ℝ) + 1)))
    (hd : ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt f (df x) x)
    (hd2 : ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt df (d2f x) x)
    (hi : IntervalIntegrable df volume (n : ℝ) ((n : ℝ) + 1))
    (hi2 : IntervalIntegrable d2f volume (n : ℝ) ((n : ℝ) + 1)) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1),
        ((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2) / 2 * d2f x) =
      (f (n : ℝ) + f ((n : ℝ) + 1)) / 2 - ∫ x in (n : ℝ)..((n : ℝ) + 1), f x := by
  have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hc'I : ContinuousOn df (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
    rwa [Set.uIcc_of_le hle]
  have hd2I : ∀ x ∈ Set.Ioo (min (n : ℝ) ((n : ℝ) + 1)) (max (n : ℝ) ((n : ℝ) + 1)),
      HasDerivAt df (d2f x) x := by
    rw [min_eq_left hle, max_eq_right hle]
    exact hd2
  set P : ℝ → ℝ := fun x => ((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2) / 2 with hP
  have hub : P ((n : ℝ) + 1) = 0 := by simp only [hP]; ring
  have hua : P (n : ℝ) = 0 := by simp only [hP]; ring
  have hcontu : ContinuousOn (fun x : ℝ => ((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2) / 2)
      (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by fun_prop
  have hderu : ∀ x ∈ Set.Ioo (min (n : ℝ) ((n : ℝ) + 1)) (max (n : ℝ) ((n : ℝ) + 1)),
      HasDerivAt (fun y : ℝ => ((y - (n : ℝ)) - (y - (n : ℝ)) ^ 2) / 2)
        (1 / 2 - (x - (n : ℝ))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 x := by
      simpa using (hasDerivAt_id (x := x)).sub_const (n : ℝ)
    have h2 : HasDerivAt (fun y : ℝ => (y - (n : ℝ)) ^ 2) (2 * (x - (n : ℝ))) x := by
      have hp := h1.pow 2
      have hfun : ((fun y : ℝ => y - (n : ℝ)) ^ 2) = fun y : ℝ => (y - (n : ℝ)) ^ 2 := by
        funext y; simp
      rw [hfun] at hp
      simpa using hp
    have hid : HasDerivAt (fun y : ℝ => (y - (n : ℝ)) - (y - (n : ℝ)) ^ 2)
        (1 - 2 * (x - (n : ℝ))) x := h1.sub h2
    have := HasDerivAt.div_const hid 2
    convert this using 1
    ring
  have hcontu' : ContinuousOn (fun x : ℝ => 1 / 2 - (x - (n : ℝ)))
      (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hcontu hc'I
    hderu hd2I hcontu'.intervalIntegrable hi2
  change (∫ x in (n : ℝ)..((n : ℝ) + 1), P x * d2f x) =
    P ((n : ℝ) + 1) * df ((n : ℝ) + 1) - P (n : ℝ) * df (n : ℝ) -
      ∫ x in (n : ℝ)..((n : ℝ) + 1), (1 / 2 - (x - (n : ℝ))) * df x at hibp
  rw [hub, hua] at hibp
  simp only [hP, zero_mul, zero_sub, sub_zero] at hibp
  have hneg : (∫ x in (n : ℝ)..((n : ℝ) + 1), (1 / 2 - (x - (n : ℝ))) * df x) =
      -(∫ x in (n : ℝ)..((n : ℝ) + 1), (x - (n : ℝ) - 1 / 2) * df x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hneg] at hibp
  rw [hibp, integral_sawtooth_mul_deriv f df n hc hd hi]
  ring

/- Next brick: glue `euler_maclaurin_interval` over n = 0..N-1 with
`intervalIntegral.sum_integral_adjacent_intervals`, using `hasDerivAt_fract_sub_sq`
to move between the polynomial and the fractal form, to obtain
  ∫ x in 0..N, ({x} - {x}^2)/2 * f'' x = (sum over k) f k - ... -/

/-- Backlund p. 350: on a unit interval the periodic Bernoulli polynomial
`({x} - {x}^2)/2` coincides with the polynomial `((x-n) - (x-n)^2)/2`,
including at both endpoints. This is what turns the Euler--Maclaurin interval
identity of brick 2 into the kernel of `stirlingImag`. -/
private theorem fract_bernoulli_eq_poly {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    (Int.fract x - (Int.fract x) ^ 2) / 2 = ((x - (n : ℝ)) - (x - (n : ℝ)) ^ 2) / 2 := by
  rcases eq_or_lt_of_le hx.2 with htop | hlt
  · subst htop
    have hfr : Int.fract ((n : ℝ) + 1) = 0 := by
      rw [Int.fract_add_one, Int.fract_natCast]
    rw [hfr]
    ring
  · have hfl : ⌊x⌋ = (n : ℤ) := by
      apply Int.floor_eq_iff.mpr
      refine ⟨by simpa using hx.1, ?_⟩
      push_cast
      linarith
    have hfr : Int.fract x = x - (n : ℝ) := by
      rw [show Int.fract x = x - (⌊x⌋ : ℝ) from rfl, hfl]
      simp
    rw [hfr]


/-- Brick 3: Euler--Maclaurin over `[0, N]`, trapezoid form. Summing brick 2
over the unit intervals and gluing with
`intervalIntegral.sum_integral_adjacent_intervals` gives

  ∫ x in 0..N, ({x} - {x}^2)/2 * f'' x
      = ∑ n in range N, (f n + f (n+1))/2 - ∫ x in 0..N, f x.

This is the exact Euler-summation remainder Backlund p. 350 needs; with
`f = fun x => log ‖(x + 1/4 : ℂ) + Y * I‖` it is one step from the leaf's
kernel `(u + 1/4) / ((u + 1/4)^2 + Y^2)^2`. -/
private theorem euler_maclaurin_range (f df d2f : ℝ → ℝ) (N : ℕ)
    (hcf : ∀ n : ℕ, n < N → ContinuousOn f (Set.Icc (n : ℝ) ((n : ℝ) + 1)))
    (hcf' : ∀ n : ℕ, n < N → ContinuousOn df (Set.Icc (n : ℝ) ((n : ℝ) + 1)))
    (hd : ∀ n : ℕ, n < N → ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt f (df x) x)
    (hd2 : ∀ n : ℕ, n < N → ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt df (d2f x) x)
    (hi : ∀ n : ℕ, n < N → IntervalIntegrable df volume (n : ℝ) ((n : ℝ) + 1))
    (hi2 : ∀ n : ℕ, n < N → IntervalIntegrable d2f volume (n : ℝ) ((n : ℝ) + 1)) :
    (∫ x in (0 : ℝ)..(N : ℝ), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x) =
      (∑ n ∈ Finset.range N, (f (n : ℝ) + f ((n : ℝ) + 1)) / 2) -
        ∫ x in (0 : ℝ)..(N : ℝ), f x := by
  have hbound : ∀ u : ℝ, ‖(Int.fract u - (Int.fract u) ^ 2) / 2‖ ≤ 1 / 8 := by
    intro u
    have h0 := Int.fract_nonneg u
    have h1 := Int.fract_lt_one u
    have hnn : (0 : ℝ) ≤ Int.fract u - (Int.fract u) ^ 2 := by nlinarith [sq_nonneg (Int.fract u - 1 / 2), h0, h1]
    have hle : Int.fract u - (Int.fract u) ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (Int.fract u - 1 / 2), h0, h1]
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ (Int.fract u - (Int.fract u) ^ 2) / 2)]
    linarith
  have hFint : ∀ n : ℕ, n < N →
      IntervalIntegrable (fun x : ℝ => ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x)
        volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    have hle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    have hd2i : MeasureTheory.IntegrableOn d2f (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      exact hi2 n hn
    have hm : AEStronglyMeasurable (fun x : ℝ => (Int.fract x - (Int.fract x) ^ 2) / 2)
        (volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1))) :=
      ((measurable_fract.sub (measurable_fract.pow_const 2)).div_const 2).aestronglyMeasurable
    have hb : ∀ᵐ x ∂(volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1))),
        ‖(Int.fract x - (Int.fract x) ^ 2) / 2‖ ≤ 1 / 8 := ae_of_all _ hbound
    exact hd2i.bdd_mul hm hb
  have hstep : ∀ n ∈ Finset.range N,
      (∫ x in (n : ℝ)..((n : ℝ) + 1), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x) =
        (f (n : ℝ) + f ((n : ℝ) + 1)) / 2 - ∫ x in (n : ℝ)..((n : ℝ) + 1), f x := by
    intro n hn
    have hn' : n < N := Finset.mem_range.mp hn
    have hpoly := euler_maclaurin_interval f df d2f n (hcf n hn') (hcf' n hn')
      (hd n hn') (hd2 n hn') (hi n hn') (hi2 n hn')
    rw [← hpoly]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hx
    show (Int.fract x - Int.fract x ^ 2) / 2 * d2f x = (x - (n : ℝ) - (x - (n : ℝ)) ^ 2) / 2 * d2f x
    rw [fract_bernoulli_eq_poly hx]
  have hsumF : (∑ n ∈ Finset.range N,
      (∫ x in (n : ℝ)..((n : ℝ) + 1), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x)) =
      ∫ x in (0 : ℝ)..(N : ℝ), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) (f := fun x : ℝ => ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x)
      (μ := volume) (n := N) (fun k hk => by simpa [Nat.cast_add, Nat.cast_one] using hFint k hk)
    simpa using h
  have hcfint : ∀ k : ℕ, k < N → IntervalIntegrable f volume (k : ℝ) ((k : ℝ) + 1) := by
    intro k hk
    exact (hcf k hk).intervalIntegrable_of_Icc (by linarith)
  have hsumf : (∑ n ∈ Finset.range N, (∫ x in (n : ℝ)..((n : ℝ) + 1), f x)) =
      ∫ x in (0 : ℝ)..(N : ℝ), f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) (f := f) (μ := volume) (n := N)
      (fun k hk => by simpa [Nat.cast_add, Nat.cast_one] using hcfint k hk)
    simpa using h
  calc (∫ x in (0 : ℝ)..(N : ℝ), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x)
      = ∑ n ∈ Finset.range N,
          (∫ x in (n : ℝ)..((n : ℝ) + 1), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x) := hsumF.symm
    _ = ∑ n ∈ Finset.range N,
          ((f (n : ℝ) + f ((n : ℝ) + 1)) / 2 - ∫ x in (n : ℝ)..((n : ℝ) + 1), f x) :=
        Finset.sum_congr rfl hstep
    _ = (∑ n ∈ Finset.range N, (f (n : ℝ) + f ((n : ℝ) + 1)) / 2) -
          ∑ n ∈ Finset.range N, (∫ x in (n : ℝ)..((n : ℝ) + 1), f x) := by rw [Finset.sum_sub_distrib]
    _ = _ := by rw [hsumf]

-- ============================================================
-- Carried over from pass 4/5
--   (results/RamareSaouter2003-Decomp419c-wip-0820Z.lean, lines 35-705)
-- ============================================================
private theorem one_sub_pow_le_n_mul {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) :
    1 - b ^ n ≤ (n : ℝ) * (1 - b) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem0 : b ∈ Set.Icc (0 : ℝ) 1 := ⟨hb0, hb1⟩
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmono : MonotoneOn (fun t : ℝ => (1 - t ^ n) - (n : ℝ) * (1 - t)) (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · fun_prop
    · exact (by fun_prop : DifferentiableOn ℝ (fun t : ℝ => t ^ n) (interior (Set.Icc 0 1))).const_sub
        (1 : ℝ) |>.sub ((differentiableOn_const (c := (n : ℝ))).mul
          ((differentiableOn_const (c := (1 : ℝ))).sub differentiableOn_id))
    · intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
      have hderiv : deriv (fun t : ℝ => (1 - t ^ n) - (n : ℝ) * (1 - t)) x
          = (n : ℝ) - (n : ℝ) * x ^ (n - 1) := by
        have h1 : HasDerivAt (fun t : ℝ => t ^ n) ((n : ℝ) * x ^ (n - 1) * 1) x :=
          (hasDerivAt_id x).pow n
        have h2 : HasDerivAt (fun t : ℝ => 1 - t ^ n) (-((n : ℝ) * x ^ (n - 1) * 1)) x :=
          h1.const_sub 1
        have h3 : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have h4 : HasDerivAt (fun t : ℝ => (n : ℝ) * (1 - t)) ((n : ℝ) * (-1)) x :=
          h3.const_mul (n : ℝ)
        have h5 := h2.sub h4
        change deriv ((fun t : ℝ => 1 - t ^ n) - fun t : ℝ => (n : ℝ) * (1 - t)) x
          = (n : ℝ) - (n : ℝ) * x ^ (n - 1)
        rw [h5.deriv]
        ring
      rw [hderiv]
      have hle : x ^ (n - 1) ≤ 1 := pow_le_one₀ hx'.1 hx'.2
      nlinarith
  have h := hmono hmem0 hmem1 hb1
  simp only [one_pow] at h
  linarith

private theorem exp_le_two_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) : Real.exp x ≤ 2 := by
  have h1 : Real.exp x ≤ Real.exp (1 / 2) := Real.exp_le_exp_of_le hx
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have hlt : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    calc Real.exp (1 / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp_of_le hlt
      _ = 2 := Real.exp_log (by norm_num)
  exact h1.trans h2

/-- `1 - v^2 ≤ exp v * (1 - v)` on `[0, 1/2]`. -/
private theorem one_sub_sq_le_exp_mul {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 1 / 2) :
    1 - v ^ 2 ≤ Real.exp v * (1 - v) := by
  have hmono :
      MonotoneOn (fun t : ℝ => Real.exp t * (1 - t) - 1 + t ^ 2) (Set.Icc 0 (1 / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
    · fun_prop
    · intro x hx
      have he : DifferentiableWithinAt ℝ (fun t : ℝ => Real.exp t) (interior (Set.Icc 0 (1 / 2))) x :=
        Real.differentiableAt_exp.differentiableWithinAt
      have h1 : DifferentiableWithinAt ℝ (fun t : ℝ => 1 - t) (interior (Set.Icc 0 (1 / 2))) x := by
        fun_prop
      have h3 : DifferentiableWithinAt ℝ (fun t : ℝ => t ^ 2) (interior (Set.Icc 0 (1 / 2))) x := by
        fun_prop
      exact ((he.mul h1).sub_const 1).add h3
    · intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) (1 / 2) := interior_subset hx
      have hderiv : deriv (fun t : ℝ => Real.exp t * (1 - t) - 1 + t ^ 2) x
          = x * (2 - Real.exp x) := by
        have he : HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp x) x := Real.hasDerivAt_exp x
        have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1 : ℝ) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have h2 : HasDerivAt (fun t : ℝ => Real.exp t * (1 - t))
            (Real.exp x * (1 - x) + Real.exp x * (-1)) x := he.mul h1
        have h3 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x ^ (2 - 1) * 1) x :=
          (hasDerivAt_id x).pow 2
        have h4 := (h2.sub_const 1).add h3
        change deriv (((fun x : ℝ => Real.exp x * (1 - x) - 1) + fun t : ℝ => t ^ 2)) x
          = x * (2 - Real.exp x)
        rw [h4.deriv]
        ring
      rw [hderiv]
      have hexp : Real.exp x ≤ 2 := exp_le_two_of_le_half hx'.2
      have hnn : 0 ≤ 2 - Real.exp x := by linarith
      exact mul_nonneg hx'.1 hnn
  have h := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩)
    (Set.mem_Icc.mpr ⟨hv0, hv⟩) hv0
  beta_reduce at h
  simp only [Real.exp_zero, pow_two, mul_zero, add_zero] at h
  linarith

/-- The reverse half of the exponential comparison, with the harmless constant `2`. -/
private theorem exp_neg_sub_one_sub_div_pow_le {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    Real.exp (-x) - (1 - x / n) ^ n ≤ 2 * x ^ 2 * Real.exp (-x) / n := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set v : ℝ := x / n with hv
  have hx_eq : x = (n : ℝ) * v := by
    rw [hv]; field_simp
  have hv0 : 0 ≤ v := by
    rw [hv]; positivity
  have hv1 : v ≤ 1 := by
    rw [hv, div_le_one hnpos]; exact_mod_cast hxn
  have hpow : (1 - x / n) ^ n = (1 - v) ^ n := by rw [hv]
  have hexp : Real.exp (-x) = (Real.exp (-v)) ^ n := by
    rw [hx_eq, show -((n : ℝ) * v) = (n : ℝ) * (-v) by ring, Real.exp_nat_mul]
  have hb0 : 0 ≤ Real.exp v * (1 - v) := by
    have h : 0 ≤ 1 - v := by linarith
    positivity
  have hb1 : Real.exp v * (1 - v) ≤ 1 := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := 1) (t := v) (by
      have hc : ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [hc]; exact hv1)
    simp only [Nat.cast_one, div_one, pow_one] at h
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos v).le
    have h3 : Real.exp v * Real.exp (-v) = 1 := by
      rw [← Real.exp_add]; simp
    exact h2.trans_eq h3
  have hmul : Real.exp (-v) * Real.exp v = 1 := by
    rw [← Real.exp_add]; simp
  have hone : (Real.exp (-v)) ^ n * (Real.exp v) ^ n = 1 := by
    rw [← mul_pow, hmul, one_pow]
  have hkey : (Real.exp (-v)) ^ n - (1 - v) ^ n =
      (Real.exp (-v)) ^ n * (1 - (Real.exp v * (1 - v)) ^ n) := by
    rw [mul_pow, mul_sub, mul_one]
    have hassoc : (Real.exp (-v)) ^ n * ((Real.exp v) ^ n * (1 - v) ^ n) =
        ((Real.exp (-v)) ^ n * (Real.exp v) ^ n) * (1 - v) ^ n := by ring
    rw [hassoc, hone, one_mul]
  have hmain : Real.exp (-x) - (1 - x / n) ^ n =
      Real.exp (-x) * (1 - (Real.exp v * (1 - v)) ^ n) := by
    rw [hpow, hexp]
    exact hkey
  rw [hmain]
  have hstep : 1 - (Real.exp v * (1 - v)) ^ n ≤ 2 * (n : ℝ) * v ^ 2 := by
    rcases lt_or_ge (2 * (n : ℝ) * v ^ 2) 1 with hsmall | hbig
    · have hv2 : v ^ 2 < 1 / (2 * (n : ℝ)) := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
        nlinarith
      have hvhalf : v ≤ 1 / 2 := by
        have h4 : 1 / (2 * (n : ℝ)) ≤ 1 / 4 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          linarith
        have hv24 : v ^ 2 ≤ 1 / 4 := le_of_lt (lt_of_lt_of_le hv2 h4)
        nlinarith [sq_nonneg (v - 1 / 2)]
      have hb : 1 - v ^ 2 ≤ Real.exp v * (1 - v) := one_sub_sq_le_exp_mul hv0 hvhalf
      have h := one_sub_pow_le_n_mul hb0 hb1 n
      nlinarith
    · have hle1 : (Real.exp v * (1 - v)) ^ n ≤ 1 := pow_le_one₀ hb0 hb1
      have hnn : (0 : ℝ) ≤ (Real.exp v * (1 - v)) ^ n := pow_nonneg hb0 n
      have h1 : 1 - (Real.exp v * (1 - v)) ^ n ≤ 1 := by linarith
      exact h1.trans hbig
  have hx2 : x ^ 2 = (n : ℝ) ^ 2 * v ^ 2 := by rw [hx_eq]; ring
  have hrhs : 2 * x ^ 2 * Real.exp (-x) / n = Real.exp (-x) * (2 * (n : ℝ) * v ^ 2) := by
    rw [hx2]; field_simp
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left hstep (Real.exp_pos (-x)).le

/-! ### The closed form of `logDeriv (GammaSeq · n)` -/

private theorem hasDerivAt_GammaSeq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    HasDerivAt (fun w : ℂ => Complex.GammaSeq w n)
      (Complex.GammaSeq s n *
        ((Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹)) s := by
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  set P : ℂ → ℂ := fun w => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) with hPdef
  have hne : ∀ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 := by
    intro j hj
    have hre : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
    have hpos : 0 < (s + (j : ℂ)).re := by
      rw [hre]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    exact fun h => by rw [h] at hpos; exact lt_irrefl 0 hpos
  have hPne : P s ≠ 0 := by
    rw [hPdef, Finset.prod_ne_zero_iff]
    exact hne
  have hP : HasDerivAt P (P s * ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹) s := by
    have hsum : (∑ j ∈ Finset.range (n + 1),
        (∏ i ∈ (Finset.range (n + 1)).erase j, (s + (i : ℂ))) • (1 : ℂ))
        = P s * ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [smul_eq_mul, mul_one, hPdef]
      rw [← Finset.prod_erase_mul (Finset.range (n + 1)) (fun i => (s + (i : ℂ))) hj]
      rw [mul_assoc, mul_inv_cancel₀ (hne j hj), mul_one]
    have h := HasDerivAt.finsetProd (u := Finset.range (n + 1))
      (f := fun j : ℕ => fun w : ℂ => w + (j : ℂ)) (f' := fun j : ℕ => (1 : ℂ))
      (fun j hj => (hasDerivAt_id s).add_const (j : ℂ))
    rw [hsum] at h
    rw [hPdef] at h
    have hfun : (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)))
        = ∏ i ∈ Finset.range (n + 1), fun w : ℂ => w + (i : ℂ) := by
      funext w
      rw [Finset.prod_apply]
    rw [hfun] at h
    rw [hPdef, hfun]
    exact h
  have hbase : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w)
      ((n : ℂ) ^ s * Complex.log (n : ℂ) * 1) s :=
    HasDerivAt.const_cpow (hasDerivAt_id s) (Or.inl (Nat.cast_ne_zero.mpr hn))
  have hA : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w * (Nat.factorial n : ℂ))
      ((n : ℂ) ^ s * Complex.log (n : ℂ) * 1 * (Nat.factorial n : ℂ)) s :=
    hbase.mul_const _
  have hquot := hA.div hP hPne
  have hfun : (fun w : ℂ => Complex.GammaSeq w n) =
      ((fun w : ℂ => (n : ℂ) ^ w * (Nat.factorial n : ℂ)) / P) := by
    funext w
    simp only [hPdef, Pi.div_apply, Complex.GammaSeq]
  have hprod : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 := by
    simpa only [hPdef] using hPne
  have hval : (((n : ℂ) ^ s * Complex.log (n : ℂ) * 1 * (Nat.factorial n : ℂ)) * P s -
      ((n : ℂ) ^ s * (Nat.factorial n : ℂ)) *
        (P s * ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹)) / (P s) ^ 2 =
      Complex.GammaSeq s n *
        ((Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹) := by
    rw [hlog]
    simp only [hPdef, Complex.GammaSeq]
    field_simp
  rw [hfun, ← hval]
  exact hquot

/-- `GammaSeq · n` does not vanish on `Re s > 0`. -/
private theorem GammaSeq_ne_zero {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    Complex.GammaSeq s n ≠ 0 := by
  have hne : ∀ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 := by
    intro j hj
    have hre : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
    have hpos : 0 < (s + (j : ℂ)).re := by
      rw [hre]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    exact fun h => by rw [h] at hpos; exact lt_irrefl 0 hpos
  simp only [Complex.GammaSeq]
  refine div_ne_zero (mul_ne_zero ?_ ?_) (Finset.prod_ne_zero_iff.mpr hne)
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- The digamma-series summand: the logarithmic derivative of `GammaSeq · n`. -/
private theorem logDeriv_GammaSeq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w : ℂ => Complex.GammaSeq w n) s =
      (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
  have hG : Complex.GammaSeq s n ≠ 0 := GammaSeq_ne_zero hs hn
  rw [logDeriv_apply, (hasDerivAt_GammaSeq hs hn).deriv]
  field_simp

/-! ### The real weight, its integrability, and its vanishing tail -/

/-- On `Re s ∈ [σ, R]` the modulus weight `x^(Re s - 1)` is dominated by
`x^(σ-1) + x^(R-1)`, separately on `(0,1]` and `[1,∞)`. -/
private theorem rpow_re_sub_one_le {σ R : ℝ} {s : ℂ} (h1 : σ ≤ s.re) (h2 : s.re ≤ R) {x : ℝ}
    (hx : 0 < x) :
    x ^ (s.re - 1) ≤ x ^ (σ - 1) + x ^ (R - 1) := by
  have h0σ : (0 : ℝ) ≤ x ^ (σ - 1) := Real.rpow_nonneg hx.le _
  have h0R : (0 : ℝ) ≤ x ^ (R - 1) := Real.rpow_nonneg hx.le _
  rcases le_total (1:ℝ) x with hx1 | hx1
  · have hle : x ^ (s.re - 1) ≤ x ^ (R - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith
  · have hle : x ^ (s.re - 1) ≤ x ^ (σ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
    linarith

private theorem integrableOn_exp_mul_rpow_sub_one {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (p - 1)) (Set.Ioi (0 : ℝ)) :=
  Real.GammaIntegral_convergent hp

private theorem integrableOn_exp_mul_weight {σ R : ℝ} (hσ : 0 < σ) (hR : σ ≤ R) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * (x ^ (σ - 1) + x ^ (R - 1)))
      (Set.Ioi (0 : ℝ)) := by
  have hR0 : 0 < R := lt_of_lt_of_le hσ hR
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (σ - 1)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_rpow_sub_one hσ
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (R - 1)) (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_rpow_sub_one hR0
  have h := h1.add h2
  convert h using 1
  ext x
  simp only [Pi.add_apply, mul_add]

/-- The tail of an integrable function on `Ioi 0` vanishes. -/
private theorem tendsto_integral_Ioi_natCast_zero {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioi (n : ℝ), g x) atTop (𝓝 0) := by
  have hmain : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(n : ℝ), g x) atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), g x)) :=
    intervalIntegral_tendsto_integral_Ioi (μ := volume) (a := (0 : ℝ)) (f := g) hg
      tendsto_natCast_atTop_atTop
  have hfun : ∀ n : ℕ, (∫ x in Set.Ioi (n : ℝ), g x) =
      (∫ x in Set.Ioi (0 : ℝ), g x) - ∫ x in (0 : ℝ)..(n : ℝ), g x := by
    intro n
    have h := intervalIntegral.integral_Ioi_sub_Ioi (μ := volume) (f := g) (a := (0 : ℝ))
      (b := (n : ℝ)) hg (by positivity)
    linarith
  have hlim : Tendsto (fun n : ℕ => ((∫ x in Set.Ioi (0 : ℝ), g x) -
      ∫ x in (0 : ℝ)..(n : ℝ), g x)) atTop (𝓝 ((∫ x in Set.Ioi (0 : ℝ), g x) -
      (∫ x in Set.Ioi (0 : ℝ), g x))) :=
    tendsto_const_nhds.sub hmain
  simp only [sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards with n
  exact (hfun n).symm

/-! ### Toward `tendstoLocallyUniformlyOn_GammaSeq`: the uniform strip bound -/

/-- `x^2 * x^(p-1) = x^(p+1)` for `x > 0`. -/
private theorem sq_mul_rpow_sub_one {p x : ℝ} (hx : 0 < x) : x ^ 2 * x ^ (p - 1) = x ^ (p + 1) := by
  rw [← Real.rpow_natCast (x := x) (n := 2), ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

private theorem integrableOn_exp_mul_weight_sq {σ R : ℝ} (hσ : 0 < σ) (hR : σ ≤ R) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1)))
      (Set.Ioi (0 : ℝ)) := by
  have h := integrableOn_exp_mul_weight (σ := σ + 2) (R := R + 2) (by linarith) (by linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have e1 : x ^ (σ + 2 - 1) = x ^ 2 * x ^ (σ - 1) := by
    rw [show σ + 2 - 1 = (σ - 1) + 2 by ring, Real.rpow_add hx0,
      ← Real.rpow_natCast (x := x) (n := 2)]
    ring
  have e2 : x ^ (R + 2 - 1) = x ^ 2 * x ^ (R - 1) := by
    rw [show R + 2 - 1 = (R - 1) + 2 by ring, Real.rpow_add hx0,
      ← Real.rpow_natCast (x := x) (n := 2)]
    ring
  simp only []
  rw [e1, e2]
  ring

/-- The uniform-in-`s` bound on a vertical strip. -/
private theorem norm_GammaSeq_sub_Gamma_le {σ R : ℝ} (hσ : 0 < σ) (hR : σ ≤ R) {n : ℕ}
    (hn : 2 ≤ n) {s : ℂ} (h1 : σ ≤ s.re) (h2 : s.re ≤ R) :
    ‖Complex.GammaSeq s n - Complex.Gamma s‖ ≤
      (2 / (n : ℝ)) * (∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) +
        ∫ x in Set.Ioi (n : ℝ), Real.exp (-x) * (x ^ (σ - 1) + x ^ (R - 1)) := by
  have hsr : 0 < s.re := lt_of_lt_of_le hσ h1
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hle : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  set F : ℝ → ℂ := fun x => ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) with hF
  set G : ℝ → ℂ := fun x => ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) with hG
  have hFint : IntegrableOn F (Set.Ioi (0 : ℝ)) := by
    rw [hF]; exact Complex.GammaIntegral_convergent hsr
  have hFs : Complex.Gamma s = ∫ x in Set.Ioi (0 : ℝ), F x := by
    rw [hF]
    exact Complex.Gamma_eq_integral hsr
  have hGs : Complex.GammaSeq s n = ∫ x in (0 : ℝ)..(n : ℝ), G x := by
    rw [hG]; exact Complex.GammaSeq_eq_approx_Gamma_integral hsr hn0
  have hFI' : IntervalIntegrable F volume (0 : ℝ) (n : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact hFint.mono_set Set.Ioc_subset_Ioi_self
  have hFIn : IntegrableOn F (Set.Ioi (n : ℝ)) := hFint.mono_set (Set.Ioi_subset_Ioi hle)
  have hGI : IntervalIntegrable G volume (0 : ℝ) (n : ℝ) := by
    rw [hG]
    apply IntervalIntegrable.continuousOn_mul
    · exact intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    · fun_prop
  have hsplit : (∫ x in (0 : ℝ)..(n : ℝ), F x) + ∫ x in Set.Ioi (n : ℝ), F x
      = ∫ x in Set.Ioi (0 : ℝ), F x :=
    intervalIntegral.integral_interval_add_Ioi hFint hFIn
  have hd : Complex.GammaSeq s n - Complex.Gamma s =
      (∫ x in (0 : ℝ)..(n : ℝ), (G x - F x)) - ∫ x in Set.Ioi (n : ℝ), F x := by
    rw [hGs, hFs, intervalIntegral.integral_sub hGI hFI', ← hsplit]
    ring
  rw [hd]
  have hmaj : ∀ x ∈ Set.Ioo (0 : ℝ) (n : ℝ),
      ‖G x - F x‖ ≤ 2 / (n : ℝ) * (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
    intro x hx
    obtain ⟨hx0, hxn⟩ := hx
    have hxn' : x ≤ (n : ℝ) := le_of_lt hxn
    have hGF : G x - F x = ↑((1 - x / n) ^ n - Real.exp (-x)) * (x : ℂ) ^ (s - 1) := by
      rw [hG, hF]; push_cast; ring
    rw [hGF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real,
        Real.norm_eq_abs]
    have hnonpos : (1 - x / n) ^ n - Real.exp (-x) ≤ 0 := by
      have := Real.one_sub_div_pow_le_exp_neg (n := n) (t := x) hxn'
      linarith
    rw [abs_of_nonpos hnonpos, neg_sub]
    have hkey := exp_neg_sub_one_sub_div_pow_le hn hx0.le hxn'
    have hrw : x ^ (s.re - 1) ≤ x ^ (σ - 1) + x ^ (R - 1) := rpow_re_sub_one_le h1 h2 hx0
    have h1' : (0 : ℝ) ≤ x ^ (s.re - 1) := Real.rpow_nonneg hx0.le _
    calc (Real.exp (-x) - (1 - x / n) ^ n) * x ^ (s.re - 1)
        ≤ (2 * x ^ 2 * Real.exp (-x) / n) * (x ^ (σ - 1) + x ^ (R - 1)) :=
          mul_le_mul hkey hrw h1' (by positivity)
      _ = 2 / (n : ℝ) * (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
          field_simp
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
    have stepA : (∫ x in (0 : ℝ)..(n : ℝ), ‖G x - F x‖) ≤ 2 / (n : ℝ) *
        ∫ x in (0 : ℝ)..(n : ℝ),
          (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
      have hInt : IntervalIntegrable (fun x : ℝ =>
          2 / (n : ℝ) * (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))))
          volume (0 : ℝ) (n : ℝ) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact ((integrableOn_exp_mul_weight_sq (σ := σ) (R := R) hσ hR).mono_set
          Set.Ioc_subset_Ioi_self).const_mul _
      have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hle ((hGI.sub hFI').norm)
        hInt hmaj
      rwa [intervalIntegral.integral_const_mul] at hmono
    have stepB : (∫ x in (0 : ℝ)..(n : ℝ),
          (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))))
        ≤ ∫ x in Set.Ioi (0 : ℝ),
          (Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1))) := by
      rw [intervalIntegral.integral_of_le hle]
      refine setIntegral_mono_set (f := fun x : ℝ =>
        Real.exp (-x) * x ^ 2 * (x ^ (σ - 1) + x ^ (R - 1)))
        (integrableOn_exp_mul_weight_sq (σ := σ) (R := R) hσ hR) ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 < x := hx
        have hw : (0 : ℝ) ≤ x ^ (σ - 1) + x ^ (R - 1) := by
          have a := Real.rpow_nonneg hx0.le (σ - 1)
          have b := Real.rpow_nonneg hx0.le (R - 1)
          linarith
        exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg x)) hw
      · exact ae_of_all _ (fun x hx => Set.Ioc_subset_Ioi_self hx)
    exact stepA.trans (mul_le_mul_of_nonneg_left stepB (by positivity))
  · refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (f := fun x => ‖F x‖)
      (g := fun x => Real.exp (-x) * (x ^ (σ - 1) + x ^ (R - 1)))
      (hFIn.norm) ((integrableOn_exp_mul_weight hσ hR).mono_set (Set.Ioi_subset_Ioi hle))
      measurableSet_Ioi ?_
    intro x hx
    have hx0 : 0 < x := lt_trans hnpos hx
    rw [hF, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (rpow_re_sub_one_le h1 h2 hx0) (Real.exp_pos _).le

/-- `GammaSeq · n` converges to `Gamma` locally uniformly on `Re s > 0`.  This is the
Mathlib-missing locally uniform strengthening of `Complex.GammaSeq_tendsto_Gamma`. -/
private theorem GammaSeq_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) => Complex.GammaSeq s n) Complex.Gamma
      atTop {z : ℂ | 0 < z.re} := by
  intro u hu x hx
  rw [Metric.mem_uniformity_dist] at hu
  obtain ⟨ε, hε, hεu⟩ := hu
  have hx0 : 0 < x.re := hx
  have hσ : 0 < x.re / 2 := by linarith
  have hσR : x.re / 2 ≤ x.re + 1 := by linarith
  set C : ℝ := ∫ y in Set.Ioi (0 : ℝ),
    Real.exp (-y) * y ^ 2 * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1)) with hCdef
  have htend1 : Tendsto (fun n : ℕ => 2 / (n : ℝ) * C) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
    have h2 : Tendsto (fun n : ℕ => 2 / (n : ℝ) * C) atTop (𝓝 (0 * C)) := h.mul_const C
    simpa using h2
  have htend2 : Tendsto (fun n : ℕ => ∫ y in Set.Ioi (n : ℝ),
      Real.exp (-y) * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1))) atTop (𝓝 0) :=
    tendsto_integral_Ioi_natCast_zero (integrableOn_exp_mul_weight hσ hσR)
  have htendB : Tendsto (fun n : ℕ => 2 / (n : ℝ) * C + ∫ y in Set.Ioi (n : ℝ),
      Real.exp (-y) * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1))) atTop (𝓝 (0 + 0)) :=
    htend1.add htend2
  rw [add_zero] at htendB
  have hev : ∀ᶠ n : ℕ in atTop, 2 / (n : ℝ) * C + ∫ y in Set.Ioi (n : ℝ),
      Real.exp (-y) * (y ^ (x.re / 2 - 1) + y ^ (x.re + 1 - 1)) < ε :=
    htendB.eventually (isOpen_Iio.mem_nhds hε)
  have hopen : IsOpen {y : ℂ | x.re / 2 < y.re ∧ y.re < x.re + 1} := by
    have h : {y : ℂ | x.re / 2 < y.re ∧ y.re < x.re + 1} =
        Complex.re ⁻¹' Set.Ioo (x.re / 2) (x.re + 1) := by
      ext y
      simp [Set.mem_Ioo]
    rw [h]
    exact isOpen_Ioo.preimage Complex.continuous_re
  refine ⟨{y : ℂ | x.re / 2 < y.re ∧ y.re < x.re + 1}, ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds ⟨by linarith, by linarith⟩)
  · filter_upwards [hev, eventually_ge_atTop 2] with n hnB hn2
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    refine hεu ?_
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (norm_GammaSeq_sub_Gamma_le hσ hσR hn2 (s := y) hy1.le hy2.le) hnB


/-- The digamma series: `ψ(z) = lim_n (log n - Σ_{j≤n} 1/(z+j))` on `Re z > 0`,
from the locally uniform convergence of the Weierstrass product. -/
private theorem digamma_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), (z + (j : ℂ))⁻¹)
      atTop (𝓝 (Complex.digamma z)) := by
  have hs : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (fun w : ℂ => Complex.GammaSeq w n) {w : ℂ | 0 < w.re} := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro w hw
    exact (hasDerivAt_GammaSeq (n := n) hw (Nat.one_le_iff_ne_zero.mp hn)).differentiableAt.differentiableWithinAt
  have hg : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have h := Complex.logDeriv_tendsto hs (show z ∈ {w : ℂ | 0 < w.re} from hz)
    GammaSeq_tendstoLocallyUniformlyOn hf hg
  rw [Complex.digamma_def]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact logDeriv_GammaSeq hz (Nat.one_le_iff_ne_zero.mp hn)



/-- `∫_0^a c/(c²+y²) dy = arctan (a/c)` for `c > 0`. -/
private theorem integral_quadratic_inv {c a : ℝ} (hc : 0 < c) :
    ∫ y in (0 : ℝ)..a, c / (c ^ 2 + y ^ 2) = Real.arctan (a / c) := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.arctan (y / c)) (c / (c ^ 2 + y ^ 2)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => y / c) (1 / c) y := by
      simpa using (hasDerivAt_id y).div_const c
    have h2 := h1.arctan
    convert h2 using 1
    field_simp
  have hne : ∀ y : ℝ, c ^ 2 + y ^ 2 ≠ 0 := fun y => by positivity
  have hcont : Continuous fun y : ℝ => c / (c ^ 2 + y ^ 2) :=
    Continuous.div continuous_const (by fun_prop) hne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    (hcont.intervalIntegrable _ _)]
  simp

/-- The real part of the `n`-th digamma-series term at `c + iy`. -/
private theorem re_series_GammaSeq (c y : ℝ) (n : ℕ) :
    (((Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1),
        (((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I)⁻¹)).re
      = Real.log n - ∑ j ∈ Finset.range (n + 1),
          (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2) := by
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ((((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I)⁻¹).re
        = (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2) := by
    intro j hj
    rw [Complex.inv_re, Complex.normSq_apply]
    have h1 : (((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I).re = c + (j : ℝ) := by simp
    have h2 : (((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I).im = y := by simp
    rw [h1, h2]
    congr 1
    push_cast
    ring
  have hsum : (∑ j ∈ Finset.range (n + 1),
      (((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I)⁻¹).re
      = ∑ j ∈ Finset.range (n + 1),
        ((((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I)⁻¹).re := by
    rw [← Complex.reCLM_apply, map_sum Complex.reCLM]
    simp only [Complex.reCLM_apply]
  rw [Complex.sub_re, Complex.ofReal_re, hsum]
  congr 1
  exact Finset.sum_congr rfl hterm

/-- `∫_0^a (log n - Σ_j (c+j)/((c+j)²+y²)) dy = a log n - Σ_j arctan (a/(c+j))`. -/
private theorem integral_re_series_GammaSeq {c a : ℝ} (hc : 0 < c) (n : ℕ) :
    (∫ y in (0 : ℝ)..a, (Real.log n - ∑ j ∈ Finset.range (n + 1),
        (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2)))
      = a * Real.log n - ∑ j ∈ Finset.range (n + 1), Real.arctan (a / (c + (j : ℝ))) := by
  have hbase : ∀ j ∈ Finset.range (n + 1),
      IntervalIntegrable (fun y : ℝ => (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2))
        volume (0 : ℝ) a := by
    intro j hj
    have hne : ∀ y : ℝ, (c + (j : ℝ)) ^ 2 + y ^ 2 ≠ 0 := fun y => by positivity
    exact (Continuous.div continuous_const (by fun_prop) hne).intervalIntegrable _ _
  have hsumint : IntervalIntegrable (∑ j ∈ Finset.range (n + 1),
      fun y : ℝ => (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2)) volume (0 : ℝ) a :=
    IntervalIntegrable.sum (Finset.range (n + 1)) hbase
  have hconst : (∫ _y in (0 : ℝ)..a, Real.log n) = a * Real.log n := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  trans (∫ y in (0 : ℝ)..a, (Real.log n - (∑ j ∈ Finset.range (n + 1),
      fun y : ℝ => (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2)) y))
  · apply intervalIntegral.integral_congr
    intro y _
    simp
  rw [intervalIntegral.integral_sub intervalIntegrable_const hsumint, hconst]
  simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finset_sum hbase]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hpos : 0 < c + (j : ℝ) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  exact integral_quadratic_inv hpos


/-- The harmonic bound `Σ_{j<n} 1/(j+1) ≤ 1 + log n`, from `1/(n+1) ≤ log((n+1)/n)`. -/
private theorem sum_inv_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hstep : (1 : ℝ) / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
      have hx : (0 : ℝ) < ((n : ℝ) + 1) / n := by positivity
      have h := Real.one_sub_inv_le_log_of_pos hx
      rw [inv_div] at h
      rw [Real.log_div (by positivity) (ne_of_gt hnpos)] at h
      have h1 : 1 - n / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      rw [h1] at h
      linarith
    push_cast
    linarith

/-- `Σ_{j<n} 1/(j+1)² ≤ 2 - 1/n` for `n ≥ 1`, from `1/(n+1)² ≤ 1/n - 1/(n+1)`. -/
private theorem sum_inv_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_range_succ]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hstep : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      have h1 : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) = 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      rw [← h1]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    push_cast
    linarith

/-- `Σ_{j<n} 1/(j+1)³ ≤ 2`. -/
private theorem sum_inv_cube_le_two (n : ℕ) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) ^ 3 ≤ 2 := by
  have hle : ∀ j ∈ Finset.range n,
      (1 : ℝ) / ((j : ℝ) + 1) ^ 3 ≤ (1 : ℝ) / ((j : ℝ) + 1) ^ 2 := by
    intro j hj
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    nlinarith [sq_nonneg ((j : ℝ) + 1), hj1]
  refine (Finset.sum_le_sum hle).trans ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    have := sum_inv_sq_le n hn
    linarith

/-- `Σ_{j≤n} 1/(c+j)³ ≤ 1/c³ + 2` for `c > 0`. -/
private theorem sum_inv_add_c_cube_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (1 : ℝ) / ((c + (j : ℝ)) ^ 3) ≤ 1 / c ^ 3 + 2 := by
  rw [Finset.sum_range_succ']
  have hzero : (1 : ℝ) / ((c + ((0 : ℕ) : ℝ)) ^ 3) = 1 / c ^ 3 := by norm_num
  rw [hzero]
  have hle : ∀ j ∈ Finset.range n,
      (1 : ℝ) / ((c + (((j + 1 : ℕ)) : ℝ)) ^ 3) ≤ (1 : ℝ) / ((j : ℝ) + 1) ^ 3 := by
    intro j hj
    have hcast : ((c + (((j + 1 : ℕ)) : ℝ))) = c + ((j : ℝ) + 1) := by push_cast; ring
    rw [hcast]
    have hbase : ((j : ℝ) + 1) ≤ c + ((j : ℝ) + 1) := by linarith
    have h0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ h0 hbase 3)
  refine (add_le_add_left (Finset.sum_le_sum hle) _).trans ?_
  have := sum_inv_cube_le_two n
  linarith


/-- The companion harmonic bound `log (n+1) ≤ Σ_{j<n} 1/(j+1)`, from
`log (1 + 1/(n+1)) ≤ 1/(n+1)`; both directions are needed for the dominator. -/
private theorem log_succ_le_sum_inv (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
      have hx : (0 : ℝ) < ((n : ℝ) + 2) / ((n : ℝ) + 1) := by positivity
      have h := Real.log_le_sub_one_of_pos hx
      rw [Real.log_div (by positivity) (by positivity)] at h
      have h1 : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      linarith
    push_cast
    have h2 : ((n : ℝ) + 1 + 1) = ((n : ℝ) + 2) := by ring
    rw [h2]
    linarith

/-! ## New work: the remaining steps of the chain

`results/RamareSaouter2003-Decomp419c-derivation-0820Z.md` reduces the leaf to

  `∫_0^a Re ψ(c+iy) dy = lim_n [a log n - Σ_{j≤n} arctan (a/(c+j))]`

(dominated convergence, using the digamma series already compiled above),
Euler--Maclaurin at `f x = arctan (a/(c+x))` (whose second derivative is the
kernel of `stirlingImag`), the passage `n → ∞`, and endgame arithmetic.
-/

/-! ### The trapezoid sum of a unit-step range -/

private theorem trapezoid_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f n + f (n + 1)) / 2) =
      (∑ j ∈ Finset.range (N + 1), f j) - (f 0 + f N) / 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

private theorem trapezoid_sum_real (f : ℝ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (f (n : ℝ) + f ((n : ℝ) + 1)) / 2) =
      (∑ j ∈ Finset.range (N + 1), f (j : ℝ)) - (f 0 + f (N : ℝ)) / 2 := by
  simpa [Nat.cast_add, Nat.cast_one] using trapezoid_sum (fun n : ℕ => f (n : ℝ)) N

/-! ### The three derivatives -/

private theorem hasDerivAt_J {a : ℝ} (ha : 0 < a) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (fun v : ℝ => v * Real.arctan (a / v) + (a / 2) * Real.log (v ^ 2 + a ^ 2))
      (Real.arctan (a / w)) w := by
  have hQ : 0 < w ^ 2 + a ^ 2 := by positivity
  have hw' : w ≠ 0 := ne_of_gt hw
  have hne : w ^ 2 + a ^ 2 ≠ 0 := ne_of_gt hQ
  have hinv : HasDerivAt (fun v : ℝ => a / v) (-a / w ^ 2) w := by
    have h1 : HasDerivAt (fun v : ℝ => v⁻¹) (-(w ^ 2)⁻¹) w := hasDerivAt_inv hw'
    have h2 : HasDerivAt (fun v : ℝ => a * v⁻¹) (a * (-(w ^ 2)⁻¹)) w := h1.const_mul a
    have hval : -a / w ^ 2 = a * (-(w ^ 2)⁻¹) := by ring
    rw [show (fun v : ℝ => a / v) = fun v : ℝ => a * v⁻¹ from by
      funext v; rw [div_eq_mul_inv], hval]
    exact h2
  have harct : HasDerivAt (fun v : ℝ => Real.arctan (a / v)) (-a / (w ^ 2 + a ^ 2)) w := by
    have h := hinv.arctan
    have hval : -a / (w ^ 2 + a ^ 2) = 1 / (1 + (a / w) ^ 2) * (-a / w ^ 2) := by
      field_simp
      try ring
    rw [hval]
    exact h
  have hlog : HasDerivAt (fun v : ℝ => Real.log (v ^ 2 + a ^ 2)) (2 * w / (w ^ 2 + a ^ 2)) w := by
    have h3 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    exact (h3.add_const (a ^ 2)).log hne
  have h1 : HasDerivAt (fun v : ℝ => v * Real.arctan (a / v))
      (Real.arctan (a / w) + w * (-a / (w ^ 2 + a ^ 2))) w := by
    have h := (hasDerivAt_id w).mul harct
    have hval : Real.arctan (a / w) + w * (-a / (w ^ 2 + a ^ 2))
        = 1 * Real.arctan (a / w) + id w * (-a / (w ^ 2 + a ^ 2)) := by
      simp
    rw [show (fun v : ℝ => v * Real.arctan (a / v)) = id * fun v : ℝ => Real.arctan (a / v) from by
      funext v; rfl, hval]
    exact h
  have h2 : HasDerivAt (fun v : ℝ => (a / 2) * Real.log (v ^ 2 + a ^ 2))
      ((a / 2) * (2 * w / (w ^ 2 + a ^ 2))) w := hlog.const_mul (a / 2)
  have h := h1.add h2
  have hval : Real.arctan (a / w)
      = Real.arctan (a / w) + w * (-a / (w ^ 2 + a ^ 2)) + (a / 2) * (2 * w / (w ^ 2 + a ^ 2)) := by
    field_simp
    ring
  rw [hval]
  exact h

private theorem hasDerivAt_f {c a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < c + x) :
    HasDerivAt (fun v : ℝ => Real.arctan (a / (c + v))) (-a / ((c + x) ^ 2 + a ^ 2)) x := by
  have hQ : 0 < (c + x) ^ 2 + a ^ 2 := by positivity
  have hx' : c + x ≠ 0 := ne_of_gt hx
  have hQne : (c + x) ^ 2 + a ^ 2 ≠ 0 := ne_of_gt hQ
  have hlin : HasDerivAt (fun v : ℝ => c + v) (1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_add c
  have hinv : HasDerivAt (fun v : ℝ => a / (c + v)) (-a / (c + x) ^ 2) x := by
    have h2 : HasDerivAt (fun v : ℝ => a * (c + v)⁻¹) (a * (-1 / (c + x) ^ 2)) x :=
      (hlin.inv hx').const_mul a
    have hval : -a / (c + x) ^ 2 = a * (-1 / (c + x) ^ 2) := by ring
    rw [show (fun v : ℝ => a / (c + v)) = fun v : ℝ => a * (c + v)⁻¹ from by
      funext v; rw [div_eq_mul_inv], hval]
    exact h2
  have h := hinv.arctan
  have hval : -a / ((c + x) ^ 2 + a ^ 2) = 1 / (1 + (a / (c + x)) ^ 2) * (-a / (c + x) ^ 2) := by
    field_simp
    try ring
  rw [hval]
  exact h

private theorem hasDerivAt_Jcomp {c a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 < c + x) :
    HasDerivAt
      (fun v : ℝ => (c + v) * Real.arctan (a / (c + v)) + (a / 2) * Real.log ((c + v) ^ 2 + a ^ 2))
      (Real.arctan (a / (c + x))) x := by
  have hQ : 0 < (c + x) ^ 2 + a ^ 2 := by positivity
  have hx' : c + x ≠ 0 := ne_of_gt hx
  have hQne : (c + x) ^ 2 + a ^ 2 ≠ 0 := ne_of_gt hQ
  have hlin : HasDerivAt (fun v : ℝ => c + v) (1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_add c
  have harct : HasDerivAt (fun v : ℝ => Real.arctan (a / (c + v)))
      (-a / ((c + x) ^ 2 + a ^ 2)) x := hasDerivAt_f ha hx
  have h1 : HasDerivAt (fun v : ℝ => (c + v) * Real.arctan (a / (c + v)))
      (Real.arctan (a / (c + x)) + (c + x) * (-a / ((c + x) ^ 2 + a ^ 2))) x := by
    have h := hlin.mul harct
    have hval : Real.arctan (a / (c + x)) + (c + x) * (-a / ((c + x) ^ 2 + a ^ 2))
        = 1 * Real.arctan (a / (c + x)) + (c + x) * (-a / ((c + x) ^ 2 + a ^ 2)) := by
      ring
    rw [show (fun v : ℝ => (c + v) * Real.arctan (a / (c + v)))
        = (fun v : ℝ => c + v) * fun v : ℝ => Real.arctan (a / (c + v)) from by
      funext v; rfl, hval]
    exact h
  have hsq : HasDerivAt (fun v : ℝ => (c + v) ^ 2) (2 * (c + x)) x := by
    have h := hlin.pow 2
    have hval : 2 * (c + x) = 2 * (c + x) ^ (2 - 1) * 1 := by ring
    rw [hval]
    exact h
  have hbase : HasDerivAt (fun v : ℝ => (c + v) ^ 2 + a ^ 2) (2 * (c + x)) x := hsq.add_const (a ^ 2)
  have hlog : HasDerivAt (fun v : ℝ => (a / 2) * Real.log ((c + v) ^ 2 + a ^ 2))
      ((a / 2) * (2 * (c + x) / ((c + x) ^ 2 + a ^ 2))) x :=
    (hbase.log hQne).const_mul (a / 2)
  have h := h1.add hlog
  have hval : Real.arctan (a / (c + x))
      = Real.arctan (a / (c + x)) + (c + x) * (-a / ((c + x) ^ 2 + a ^ 2))
        + (a / 2) * (2 * (c + x) / ((c + x) ^ 2 + a ^ 2)) := by
    field_simp
    ring
  rw [hval]
  exact h

private theorem hasDerivAt_df {c a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun v : ℝ => -a / ((c + v) ^ 2 + a ^ 2))
      (2 * a * (c + x) / ((c + x) ^ 2 + a ^ 2) ^ 2) x := by
  have hQ : 0 < (c + x) ^ 2 + a ^ 2 := by positivity
  have hQne : (c + x) ^ 2 + a ^ 2 ≠ 0 := ne_of_gt hQ
  have hlin : HasDerivAt (fun v : ℝ => c + v) (1 : ℝ) x := by
    simpa using (hasDerivAt_id x).const_add c
  have hsq : HasDerivAt (fun v : ℝ => (c + v) ^ 2) (2 * (c + x)) x := by
    have h := hlin.pow 2
    have hval : 2 * (c + x) = 2 * (c + x) ^ (2 - 1) * 1 := by ring
    rw [hval]
    exact h
  have hbase : HasDerivAt (fun v : ℝ => (c + v) ^ 2 + a ^ 2) (2 * (c + x)) x := hsq.add_const (a ^ 2)
  have h2 : HasDerivAt (fun v : ℝ => -a * ((c + v) ^ 2 + a ^ 2)⁻¹)
      (-a * (-(2 * (c + x)) / ((c + x) ^ 2 + a ^ 2) ^ 2)) x :=
    (hbase.inv hQne).const_mul (-a)
  have hval : -a * (-(2 * (c + x)) / ((c + x) ^ 2 + a ^ 2) ^ 2)
      = 2 * a * (c + x) / ((c + x) ^ 2 + a ^ 2) ^ 2 := by ring
  have hfun : (fun v : ℝ => -a / ((c + v) ^ 2 + a ^ 2))
      = fun v : ℝ => -a * ((c + v) ^ 2 + a ^ 2)⁻¹ := by
    funext v; rw [div_eq_mul_inv]
  rw [hfun, ← hval]
  exact h2

/-! ### Euler--Maclaurin specialised at `f x = arctan (a / (c + x))` -/

private theorem euler_maclaurin_K {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (N : ℕ) :
    a * (∫ u in (0 : ℝ)..(N : ℝ),
        (Int.fract u - (Int.fract u) ^ 2) * ((u + c) / ((u + c) ^ 2 + a ^ 2) ^ 2))
      = (∑ j ∈ Finset.range (N + 1), Real.arctan (a / (c + (j : ℝ))))
        - (Real.arctan (a / c) + Real.arctan (a / (c + (N : ℝ)))) / 2
        - ∫ x in (0 : ℝ)..(N : ℝ), Real.arctan (a / (c + x)) := by
  set f : ℝ → ℝ := fun x => Real.arctan (a / (c + x)) with hf
  set df : ℝ → ℝ := fun x => -a / ((c + x) ^ 2 + a ^ 2) with hdf
  set d2f : ℝ → ℝ := fun x => 2 * a * (c + x) / ((c + x) ^ 2 + a ^ 2) ^ 2 with hd2f
  have hpos : ∀ n : ℕ, ∀ x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1), 0 < c + x := by
    intro n x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg n) hx.1
    linarith
  have hcf : ∀ n : ℕ, n < N → ContinuousOn f (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro n hn
    have hc' : ContinuousOn (fun x : ℝ => a / (c + x)) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id)
        (fun x hx => ne_of_gt (hpos n x hx))
    exact Real.continuous_arctan.comp_continuousOn hc'
  have hcf' : ∀ n : ℕ, n < N → ContinuousOn df (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro n hn
    exact continuousOn_const.div (by fun_prop) (fun x _ => by positivity)
  have hd : ∀ n : ℕ, n < N → ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt f (df x) x := by
    intro n hn x hx
    exact hasDerivAt_f ha (hpos n x (Set.Ioo_subset_Icc_self hx))
  have hd2 : ∀ n : ℕ, n < N → ∀ x ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), HasDerivAt df (d2f x) x := by
    intro n hn x hx
    exact hasDerivAt_df ha x
  have hi : ∀ n : ℕ, n < N → IntervalIntegrable df volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    exact (hcf' n hn).intervalIntegrable_of_Icc (by linarith)
  have hi2 : ∀ n : ℕ, n < N → IntervalIntegrable d2f volume (n : ℝ) ((n : ℝ) + 1) := by
    intro n hn
    have hnum : ContinuousOn (fun x : ℝ => 2 * a * (c + x)) (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
      fun_prop
    have hden : ContinuousOn (fun x : ℝ => ((c + x) ^ 2 + a ^ 2) ^ 2)
        (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by fun_prop
    exact (hnum.div hden (fun x _ => by positivity)).intervalIntegrable_of_Icc (by linarith)
  have hEM := euler_maclaurin_range f df d2f N hcf hcf' hd hd2 hi hi2
  have hlhs : (∫ x in (0 : ℝ)..(N : ℝ), ((Int.fract x - (Int.fract x) ^ 2) / 2) * d2f x)
      = a * ∫ u in (0 : ℝ)..(N : ℝ),
          (Int.fract u - (Int.fract u) ^ 2) * ((u + c) / ((u + c) ^ 2 + a ^ 2) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hd2f]
    field_simp
    ring
  rw [hlhs, trapezoid_sum_real f N] at hEM
  simpa only [hf, Nat.cast_zero, add_zero] using hEM

/-! ### `∫_0^N arctan (a/(c+x)) dx` in closed form -/

private theorem integral_arctan_shift {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), Real.arctan (a / (c + x)))
      = (c + (N : ℝ)) * Real.arctan (a / (c + (N : ℝ)))
          + (a / 2) * Real.log ((c + (N : ℝ)) ^ 2 + a ^ 2)
        - (c * Real.arctan (a / c) + (a / 2) * Real.log (c ^ 2 + a ^ 2)) := by
  have hinter : IntervalIntegrable (fun x : ℝ => Real.arctan (a / (c + x))) volume (0 : ℝ) (N : ℝ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by positivity : (0 : ℝ) ≤ (N : ℝ))
    apply Real.continuous_arctan.comp_continuousOn
    exact continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun x hx => by
        have hx0 : (0 : ℝ) ≤ x := hx.1
        have hpos : 0 < c + x := by linarith
        exact ne_of_gt hpos)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (c + x) * Real.arctan (a / (c + x))
      + (a / 2) * Real.log ((c + x) ^ 2 + a ^ 2))
    (f' := fun x : ℝ => Real.arctan (a / (c + x))) ?_ hinter]
  · simp
  · intro x hx
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ))] at hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hcx : 0 < c + x := by linarith
    exact hasDerivAt_Jcomp ha hcx

/-! ### The dominator for the limit passage -/

/-- `Re` of the `n`-th digamma-series term, split as `(log n - Σ 1/(c+j)) + Σ y²/((c+j)Q_j)`,
is bounded by `(1/c + 1) + (1/c³ + 2) y²` uniformly in `n ≥ 1`. -/
private theorem abs_re_series_le {c y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    |Real.log n - ∑ j ∈ Finset.range (n + 1), (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2)| ≤
      (1 / c + 1) + (1 / c ^ 3 + 2) * y ^ 2 := by
  set T : ℝ := ∑ j ∈ Finset.range (n + 1), (1 : ℝ) / (c + (j : ℝ)) with hT
  set B : ℝ := ∑ j ∈ Finset.range (n + 1),
    (1 : ℝ) / ((c + (j : ℝ)) * ((c + (j : ℝ)) ^ 2 + y ^ 2)) with hB
  have hcj : ∀ j : ℕ, 0 < c + (j : ℝ) := fun j => by positivity
  have hsum : (∑ j ∈ Finset.range (n + 1), (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2))
      = T - y ^ 2 * B := by
    have hpt : ∀ j ∈ Finset.range (n + 1),
        (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2) =
          (1 : ℝ) / (c + (j : ℝ)) - y ^ 2 * ((1 : ℝ) / ((c + (j : ℝ)) * ((c + (j : ℝ)) ^ 2 + y ^ 2))) := by
      intro j hj
      have h1 : 0 < c + (j : ℝ) := hcj j
      have h2 : 0 < (c + (j : ℝ)) ^ 2 + y ^ 2 := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hB0 : 0 ≤ B := by
    rw [hB]
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hBle : B ≤ 1 / c ^ 3 + 2 := by
    rw [hB]
    refine (Finset.sum_le_sum ?_).trans (sum_inv_add_c_cube_le hc n)
    intro j hj
    have h1 : 0 < (c + (j : ℝ)) ^ 3 := by positivity
    have h2 : (c + (j : ℝ)) ^ 3 ≤ (c + (j : ℝ)) * ((c + (j : ℝ)) ^ 2 + y ^ 2) := by
      have h3 : (c + (j : ℝ)) ^ 3 = (c + (j : ℝ)) * (c + (j : ℝ)) ^ 2 := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg y)) (le_of_lt (hcj j))
    exact div_le_div_of_nonneg_left (by norm_num) h1 h2
  have hT1 : Real.log n ≤ T := by
    have h1 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log ((n : ℝ) + 1) ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) :=
      log_succ_le_sum_inv n
    have h3 : (∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / (c + (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have h4 : 0 < (j : ℝ) + 1 := by positivity
      have h5 : (j : ℝ) + 1 ≤ c + (j : ℝ) + 1 := by linarith
      have h6 : (c + (j : ℝ)) ≤ (j : ℝ) + 1 := by linarith
      exact div_le_div_of_nonneg_left (by norm_num) (hcj j) h6
    have h7 : (∑ j ∈ Finset.range n, (1 : ℝ) / (c + (j : ℝ))) ≤ T := by
      rw [hT, Finset.sum_range_succ]
      have h8 : 0 ≤ (1 : ℝ) / (c + (n : ℝ)) := by positivity
      linarith
    linarith
  have hT2 : T ≤ 1 / c + (1 + Real.log n) := by
    have h0 : (1 : ℝ) / (c + ((0 : ℕ) : ℝ)) = 1 / c := by norm_num
    have hsplit : T = 1 / c + ∑ j ∈ Finset.range n, (1 : ℝ) / (c + ((j + 1 : ℕ) : ℝ)) := by
      rw [hT, Finset.sum_range_succ', h0]
      ring
    have h3 : (∑ j ∈ Finset.range n, (1 : ℝ) / (c + ((j + 1 : ℕ) : ℝ)))
        ≤ ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hcast : ((c + ((j + 1 : ℕ) : ℝ))) = c + ((j : ℝ) + 1) := by push_cast; ring
      have h4 : 0 < (j : ℝ) + 1 := by positivity
      rw [hcast]
      exact div_le_div_of_nonneg_left (by norm_num) h4 (by linarith)
    have h5 := sum_inv_le_one_add_log n hn
    rw [hsplit]
    linarith
  have h1 : |Real.log n - T| ≤ 1 / c + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h2 : |y ^ 2 * B| ≤ (1 / c ^ 3 + 2) * y ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hBle (sq_nonneg y)
  rw [hsum]
  calc |Real.log n - (T - y ^ 2 * B)|
      = |(Real.log n - T) + y ^ 2 * B| := by ring_nf
    _ ≤ |Real.log n - T| + |y ^ 2 * B| := abs_add_le _ _
    _ ≤ (1 / c + 1) + (1 / c ^ 3 + 2) * y ^ 2 := by linarith [h1, h2]

/-- The real part of the `n`-th digamma-series term in the shape matching `digamma_tendsto`. -/
private theorem re_series_GammaSeq' (c y : ℝ) (n : ℕ) :
    (((Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1),
        (((c : ℂ) + (y : ℂ) * Complex.I) + (j : ℂ))⁻¹)).re
      = Real.log n - ∑ j ∈ Finset.range (n + 1),
          (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2) := by
  have hsum : (∑ j ∈ Finset.range (n + 1), (((c : ℂ) + (y : ℂ) * Complex.I) + (j : ℂ))⁻¹)
      = ∑ j ∈ Finset.range (n + 1), (((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show ((c : ℂ) + (y : ℂ) * Complex.I) + (j : ℂ) = ((c : ℂ) + (j : ℂ)) + (y : ℂ) * Complex.I
      from by ring]
  rw [hsum]
  exact re_series_GammaSeq c y n

/-! ### The dominated-convergence limit passage -/

/-- `∫_0^a Re ψ(c+iy) dy` is the limit of the explicit `n`-th digamma-series integrals. -/
private theorem tendsto_integral_re_series {c a : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∫ y in (0 : ℝ)..a,
        (Real.log n - ∑ j ∈ Finset.range (n + 1),
          (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2)))
      atTop (𝓝 (∫ y in (0 : ℝ)..a,
        (Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re)) := by
  set F : ℕ → ℝ → ℝ := fun n y => Real.log n - ∑ j ∈ Finset.range (n + 1),
    (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2) with hF
  set g : ℝ → ℝ := fun y => (1 / c + 1) + (1 / c ^ 3 + 2) * y ^ 2 with hg
  have hμ : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) a)) := by
    have h1 : IntegrableOn g (Set.Icc (0 : ℝ) a) :=
      (by rw [hg]; fun_prop : ContinuousOn g (Set.Icc (0 : ℝ) a)).integrableOn_compact
        isCompact_Icc
    exact h1.mono_set Set.Ioc_subset_Icc_self
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (F n) (volume.restrict (Set.Ioc (0 : ℝ) a)) := by
    filter_upwards with n
    have hcont : Continuous (fun y : ℝ => ∑ j ∈ Finset.range (n + 1),
        (c + (j : ℝ)) / ((c + (j : ℝ)) ^ 2 + y ^ 2)) := by
      apply continuous_finsetSum
      intro j hj
      exact continuous_const.div (by fun_prop) (fun y => by positivity)
    have : Continuous (F n) := by
      rw [hF]
      exact continuous_const.sub hcont
    exact this.aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop,
      ∀ᵐ y ∂(volume.restrict (Set.Ioc (0 : ℝ) a)), ‖F n y‖ ≤ g y := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have h := abs_re_series_le (y := y) hc hc1 n hn
    simpa only [hF, hg, Real.norm_eq_abs] using h
  have hlim : ∀ᵐ y ∂(volume.restrict (Set.Ioc (0 : ℝ) a)),
      Tendsto (fun n : ℕ => F n y) atTop
        (𝓝 ((Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re)) := by
    apply Filter.Eventually.of_forall
    intro y
    have hzc : 0 < (((c : ℂ) + (y : ℂ) * Complex.I)).re := by
      have h : (((c : ℂ) + (y : ℂ) * Complex.I)).re = c := by simp
      rw [h]
      exact hc
    have hbase := digamma_tendsto (z := ((c : ℂ) + (y : ℂ) * Complex.I)) hzc
    have hre := (Complex.continuous_re.tendsto _).comp hbase
    simpa only [Function.comp_def, hF, re_series_GammaSeq' c y] using hre
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0 : ℝ) a)) (l := atTop) g hmeas hbound hμ hlim
  have hconv : (fun n : ℕ => ∫ y, F n y ∂(volume.restrict (Set.Ioc (0 : ℝ) a)))
      = fun n : ℕ => ∫ y in (0 : ℝ)..a, F n y := by
    funext n
    rw [intervalIntegral.integral_of_le ha.le]
  have hconv2 : (∫ y, (fun y : ℝ => (Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re) y
      ∂(volume.restrict (Set.Ioc (0 : ℝ) a)))
      = ∫ y in (0 : ℝ)..a, (Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re := by
    rw [intervalIntegral.integral_of_le ha.le]
  rw [hconv, hconv2] at hmain
  simpa only [hF] using hmain

/-! ### The limits needed for `n → ∞` -/

private theorem tendsto_arctan_div {c a : ℝ} (_ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.arctan (a / (c + (N : ℝ)))) atTop (𝓝 0) := by
  have hden : Tendsto (fun N : ℕ => (N : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + c)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
  have hdiv : Tendsto (fun N : ℕ => a / ((N : ℝ) + c)) atTop (𝓝 0) := by
    have h := hinv.const_mul a
    simpa [div_eq_mul_inv] using h
  have hdiv' : Tendsto (fun N : ℕ => a / (c + (N : ℝ))) atTop (𝓝 0) := by
    simp_rw [add_comm c]
    exact hdiv
  have harct : Tendsto Real.arctan (𝓝 0) (𝓝 0) := by
    have h := Real.continuous_arctan.tendsto 0
    simpa using h
  exact harct.comp hdiv'

private theorem tendsto_shift_mul_arctan {c a : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun N : ℕ => (c + (N : ℝ)) * Real.arctan (a / (c + (N : ℝ)))) atTop (𝓝 a) := by
  have hden : Tendsto (fun N : ℕ => (N : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + c)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
  have hdiv : Tendsto (fun N : ℕ => a / (c + (N : ℝ))) atTop (𝓝 0) := by
    have h := hinv.const_mul a
    have h' : Tendsto (fun N : ℕ => a / ((N : ℝ) + c)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using h
    simp_rw [add_comm c]
    exact h'
  have hne : ∀ᶠ N : ℕ in atTop, a / (c + (N : ℝ)) ≠ 0 := by
    filter_upwards with N
    have hpos : 0 < a / (c + (N : ℝ)) := by
      apply div_pos ha
      positivity
    exact ne_of_gt hpos
  have hdiv' : Tendsto (fun N : ℕ => a / (c + (N : ℝ))) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdiv, hne⟩
  have hslope : Tendsto (fun t : ℝ => Real.arctan t / t) (𝓝[≠] 0) (𝓝 1) := by
    have h := (Real.hasDerivAt_arctan 0).tendsto_slope_zero
    simpa [div_eq_inv_mul, Real.arctan_zero] using h
  have hcomp : Tendsto (fun N : ℕ => Real.arctan (a / (c + (N : ℝ))) / (a / (c + (N : ℝ))))
      atTop (𝓝 1) := hslope.comp hdiv'
  have hconst := hcomp.const_mul a
  have hconst' : Tendsto (fun N : ℕ => a * (Real.arctan (a / (c + (N : ℝ))) / (a / (c + (N : ℝ)))))
      atTop (𝓝 a) := by simpa using hconst
  refine hconst'.congr' ?_
  filter_upwards [hne] with N hN
  field_simp
  try ring

private theorem tendsto_log_shift {c a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => a * Real.log (N : ℝ) - (a / 2) * Real.log ((c + (N : ℝ)) ^ 2 + a ^ 2))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hinv2 : Tendsto (fun N : ℕ => ((N : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have h1 : Tendsto (fun N : ℕ => (2 * c) / (N : ℝ)) atTop (𝓝 0) := by
    have h := hinv.const_mul (2 * c)
    simpa [div_eq_mul_inv] using h
  have h2 : Tendsto (fun N : ℕ => (c ^ 2 + a ^ 2) / ((N : ℝ) ^ 2)) atTop (𝓝 0) := by
    have h := hinv2.const_mul (c ^ 2 + a ^ 2)
    simpa [div_eq_mul_inv] using h
  have hu : Tendsto (fun N : ℕ => 1 + (2 * c) / (N : ℝ) + (c ^ 2 + a ^ 2) / ((N : ℝ) ^ 2))
      atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hone.add h1).add h2
    simpa using h
  have hu' : Tendsto (fun N : ℕ => ((c + (N : ℝ)) ^ 2 + a ^ 2) / ((N : ℝ) ^ 2)) atTop (𝓝 1) := by
    refine hu.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    field_simp
    ring
  have hlog : Tendsto (fun N : ℕ => Real.log (((c + (N : ℝ)) ^ 2 + a ^ 2) / ((N : ℝ) ^ 2)))
      atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hu'
    simpa [Function.comp_def] using h
  have hfinal := hlog.const_mul (-(a / 2))
  have hfinal' : Tendsto (fun N : ℕ =>
      -(a / 2) * Real.log (((c + (N : ℝ)) ^ 2 + a ^ 2) / ((N : ℝ) ^ 2))) atTop (𝓝 0) := by
    simpa using hfinal
  refine hfinal'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have harg : (0 : ℝ) < ((c + (N : ℝ)) ^ 2 + a ^ 2) / (N : ℝ) ^ 2 := by positivity
  have hmul : ((c + (N : ℝ)) ^ 2 + a ^ 2)
      = (N : ℝ) ^ 2 * (((c + (N : ℝ)) ^ 2 + a ^ 2) / (N : ℝ) ^ 2) := by
    field_simp
  have hlogpow : Real.log ((N : ℝ) ^ 2) = 2 * Real.log (N : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hsplit : Real.log ((c + (N : ℝ)) ^ 2 + a ^ 2)
      = 2 * Real.log (N : ℝ) + Real.log (((c + (N : ℝ)) ^ 2 + a ^ 2) / (N : ℝ) ^ 2) := by
    conv_lhs => rw [hmul]
    rw [Real.log_mul (ne_of_gt hsq) (ne_of_gt harg), hlogpow]
  rw [hsplit]
  ring

private theorem tendsto_combined {c a : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun N : ℕ => a * Real.log (N : ℝ)
        - (c + (N : ℝ)) * Real.arctan (a / (c + (N : ℝ)))
        - (a / 2) * Real.log ((c + (N : ℝ)) ^ 2 + a ^ 2)) atTop (𝓝 (-a)) := by
  have h1 := tendsto_log_shift (c := c) ha
  have h2 := tendsto_shift_mul_arctan (c := c) ha hc
  have h := h1.sub h2
  have hh : Tendsto (fun N : ℕ => a * Real.log (N : ℝ)
      - (c + (N : ℝ)) * Real.arctan (a / (c + (N : ℝ)))
      - (a / 2) * Real.log ((c + (N : ℝ)) ^ 2 + a ^ 2)) atTop (𝓝 (0 - a)) := by
    refine h.congr' ?_
    filter_upwards with N
    ring
  simpa using hh

/-- Integrability of the positive reciprocal-square kernel `u ↦ (u+c)/(((u+c)^2+a^2)^2)`
on `(0,∞)`, by the fundamental theorem of calculus (the same construction as
`kernel_integral`, kept general in `c` and `a` so that it can be used above that
declaration). -/
private theorem integrableOn_kernel {c a : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IntegrableOn (fun u : ℝ => (u + c) / ((u + c) ^ 2 + a ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) := by
  let F : ℝ → ℝ := fun u => -1 / (2 * ((u + c) ^ 2 + a ^ 2))
  let K : ℝ → ℝ := fun u => (u + c) / ((u + c) ^ 2 + a ^ 2) ^ 2
  have hd (u : ℝ) : 0 < (u + c) ^ 2 + a ^ 2 := by positivity
  have hderiv (u : ℝ) (_ : u ∈ Set.Ici (0 : ℝ)) : HasDerivAt F (K u) u := by
    have hq : HasDerivAt (fun v : ℝ => 2 * ((v + c) ^ 2 + a ^ 2)) (4 * (u + c)) u := by
      convert ((((hasDerivAt_id u).add_const c).pow 2).add_const (a ^ 2)).const_mul 2 using 1
      · ext v; dsimp; try ring
      · dsimp; try ring
    have hh := (hq.inv (by positivity : 2 * ((u + c) ^ 2 + a ^ 2) ≠ 0)).neg
    convert hh using 1
    · ext v; dsimp [F]; ring
    · dsimp [K]; field_simp; try ring
  have hn (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) : 0 ≤ K u := by
    have hu0 : 0 < u := hu
    dsimp [K]
    positivity
  have htop : Tendsto (fun u : ℝ => 2 * ((u + c) ^ 2 + a ^ 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact tendsto_atTop_add_const_right _ (a ^ 2)
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_atTop_add_const_right _ c tendsto_id))
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F, Pi.neg_apply, Pi.inv_apply, neg_div, one_div, neg_zero] using
      htop.inv_tendsto_atTop.neg
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv hn hlim

/-- The kernel integral converges along unit intervals. -/
private theorem tendsto_interval_integral_HK (T : ℝ) (hT : 0 < T) :
    Tendsto (fun N : ℕ => ∫ u in (0 : ℝ)..(N : ℝ),
        (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
      atTop (𝓝 (∫ u in Set.Ioi (0 : ℝ),
        (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))) := by
  have hKi := integrableOn_kernel (c := (1 : ℝ) / 4) (a := T / 2) (by linarith) (by norm_num)
  have hHbound : ∀ u : ℝ, 0 ≤ Int.fract u - (Int.fract u) ^ 2 ∧
      Int.fract u - (Int.fract u) ^ 2 ≤ (1 / 4 : ℝ) := by
    intro u
    have h0 := Int.fract_nonneg u
    have h1 := Int.fract_lt_one u
    constructor <;> nlinarith [sq_nonneg (Int.fract u - 1 / 2)]
  have hHi : IntegrableOn (fun u : ℝ => (Int.fract u - (Int.fract u) ^ 2) *
      ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2)) (Set.Ioi (0 : ℝ)) := by
    apply Integrable.bdd_mul (c := 1 / 4) hKi
    · exact (measurable_fract.sub (measurable_fract.pow_const 2)).aestronglyMeasurable
    · exact ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hHbound u).1]
        exact (hHbound u).2)
  have hb : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmain := intervalIntegral_tendsto_integral_Ioi (μ := volume) (0 : ℝ) hHi hb
  simpa using hmain

/-! ### The closed form of the Gamma remainder integral -/

private theorem integral_digamma_closed (T : ℝ) (hT : 0 < T) :
    (∫ y in (0 : ℝ)..(T / 2), (Complex.digamma ((1 / 4 : ℂ) + (y : ℂ) * Complex.I)).re)
      = -(T / 2) * (∫ u in Set.Ioi (0 : ℝ),
            (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
        + ((1 : ℝ) / 4 - 1 / 2) * Real.arctan ((T / 2) / (1 / 4))
        + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) - T / 2 := by
  have ha : 0 < T / 2 := by linarith
  have hc : (0 : ℝ) < 1 / 4 := by norm_num
  have hc1 : (1 : ℝ) / 4 ≤ 1 := by norm_num
  -- (1) the `n`-th digamma-series integral, in the closed form supplied by Euler--Maclaurin
  have hEq : ∀ N : ℕ, (∫ y in (0 : ℝ)..(T / 2),
        (Real.log N - ∑ j ∈ Finset.range (N + 1),
          ((1 : ℝ) / 4 + (j : ℝ)) / (((1 : ℝ) / 4 + (j : ℝ)) ^ 2 + y ^ 2)))
      = (T / 2 * Real.log (N : ℝ)
          - ((1 : ℝ) / 4 + (N : ℝ)) * Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))
          - (T / 4) * Real.log (((1 : ℝ) / 4 + (N : ℝ)) ^ 2 + (T / 2) ^ 2))
        - (T / 2) * (∫ u in (0 : ℝ)..(N : ℝ),
            (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
        - (Real.arctan ((T / 2) / (1 / 4)) + Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))) / 2
        + ((1 : ℝ) / 4 * Real.arctan ((T / 2) / (1 / 4))
            + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) := by
    intro N
    have hA := integral_re_series_GammaSeq (c := (1 : ℝ) / 4) (a := T / 2) hc N
    have hB := euler_maclaurin_K (c := (1 : ℝ) / 4) (a := T / 2) hc ha N
    have hC := integral_arctan_shift (c := (1 : ℝ) / 4) (a := T / 2) hc ha N
    rw [hA, hB, hC]
    ring
  -- (2) the limit of the digamma-series integrals
  have h1 := tendsto_integral_re_series (c := (1 : ℝ) / 4) (a := T / 2) hc hc1 ha
  have hseq2 : Tendsto (fun N : ℕ =>
      (T / 2 * Real.log (N : ℝ)
          - ((1 : ℝ) / 4 + (N : ℝ)) * Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))
          - (T / 4) * Real.log (((1 : ℝ) / 4 + (N : ℝ)) ^ 2 + (T / 2) ^ 2))
        - (T / 2) * (∫ u in (0 : ℝ)..(N : ℝ),
            (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
        - (Real.arctan ((T / 2) / (1 / 4)) + Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))) / 2
        + ((1 : ℝ) / 4 * Real.arctan ((T / 2) / (1 / 4))
            + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2))) atTop
      (𝓝 (∫ y in (0 : ℝ)..(T / 2),
        (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re)) :=
    h1.congr' (Filter.Eventually.of_forall (fun N => (hEq N)))
  -- (3) the limit of the Euler--Maclaurin side
  have hp1 : Tendsto (fun N : ℕ => T / 2 * Real.log (N : ℝ)
      - ((1 : ℝ) / 4 + (N : ℝ)) * Real.arctan ((T / 2) / (1 / 4 + (N : ℝ)))
      - (T / 4) * Real.log (((1 : ℝ) / 4 + (N : ℝ)) ^ 2 + (T / 2) ^ 2)) atTop (𝓝 (-(T / 2))) := by
    have h := tendsto_combined (c := (1 : ℝ) / 4) (a := T / 2) ha hc
    simpa [show (T / 2) / 2 = T / 4 by ring] using h
  have hp2 : Tendsto (fun N : ℕ => Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))) atTop (𝓝 0) :=
    tendsto_arctan_div (c := (1 : ℝ) / 4) (a := T / 2) ha
  have hp3 : Tendsto (fun N : ℕ => (T / 2) * (∫ u in (0 : ℝ)..(N : ℝ),
        (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2)))
      atTop (𝓝 ((T / 2) * (∫ u in Set.Ioi (0 : ℝ),
        (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2)))) :=
    (tendsto_interval_integral_HK T hT).const_mul (T / 2)
  have hc1' : Tendsto (fun N : ℕ =>
      (Real.arctan ((T / 2) / (1 / 4)) + Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))) / 2) atTop
      (𝓝 ((Real.arctan ((T / 2) / (1 / 4)) + 0) / 2)) := by
    have h := hp2.const_add (Real.arctan ((T / 2) / (1 / 4)))
    have h2 := h.div_const 2
    simpa [add_comm] using h2
  have hconstT : Tendsto (fun _ : ℕ => ((1 : ℝ) / 4 * Real.arctan ((T / 2) / (1 / 4))
      + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2))) atTop
      (𝓝 ((1 : ℝ) / 4 * Real.arctan ((T / 2) / (1 / 4))
        + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2))) := tendsto_const_nhds
  have hseq1 : Tendsto (fun N : ℕ =>
      (T / 2 * Real.log (N : ℝ)
          - ((1 : ℝ) / 4 + (N : ℝ)) * Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))
          - (T / 4) * Real.log (((1 : ℝ) / 4 + (N : ℝ)) ^ 2 + (T / 2) ^ 2))
        - (T / 2) * (∫ u in (0 : ℝ)..(N : ℝ),
            (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
        - (Real.arctan ((T / 2) / (1 / 4)) + Real.arctan ((T / 2) / ((1 : ℝ) / 4 + (N : ℝ)))) / 2
        + ((1 : ℝ) / 4 * Real.arctan ((T / 2) / (1 / 4))
            + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2))) atTop
      (𝓝 (-(T / 2) - (T / 2) * (∫ u in Set.Ioi (0 : ℝ),
            (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
        - (Real.arctan ((T / 2) / (1 / 4)) + 0) / 2
        + ((1 : ℝ) / 4 * Real.arctan ((T / 2) / (1 / 4))
            + (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)))) :=
    ((hp1.sub hp3).sub hc1').add hconstT
  have hlim := tendsto_nhds_unique hseq2 hseq1
  have hstep : (∫ y in (0 : ℝ)..(T / 2),
        (Complex.digamma ((1 / 4 : ℂ) + (y : ℂ) * Complex.I)).re)
      = ∫ y in (0 : ℝ)..(T / 2),
          (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re := by
    apply intervalIntegral.integral_congr
    intro y _
    norm_num
  rw [hstep, hlim]
  ring
/-- LEAF. Backlund p. 350, display 25 from displays 20 and 21.
The continuously normalized Gamma argument is linked to its actual
periodic Bernoulli integral. This leaf is an identity, not a remainder bound. -/
theorem gamma_stieltjes_expansion (T : ℝ) (hT : 1400 ≤ T) :
    gammaRemainder T = stirlingImag T +
      T / 4 * Real.log (1 + 1 / (4 * T ^ 2)) +
        (1 / 4) * Real.arctan (1 / (2 * T)) := by
  have hTpos : 0 < T := by linarith
  have hmain := integral_digamma_closed T hTpos
  have hdig : (∫ y in (0 : ℝ)..(T / 2),
      (deriv Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * Complex.I) /
        Complex.Gamma ((1 / 4 : ℂ) + (y : ℂ) * Complex.I)).re)
      = ∫ y in (0 : ℝ)..(T / 2),
          (Complex.digamma ((1 / 4 : ℂ) + (y : ℂ) * Complex.I)).re := by
    apply intervalIntegral.integral_congr
    intro y _
    simp only [Complex.digamma_def, logDeriv_apply]
  have hJK : (∫ u in Set.Ioi (0 : ℝ),
        (Int.fract u - (Int.fract u) ^ 2) * ((u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2))
      = ∫ u in Set.Ioi (0 : ℝ),
          (Int.fract u - (Int.fract u) ^ 2) * (u + 1 / 4) /
            ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  have hlogid : (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)
      - (T / 2) * Real.log (T / 2) = (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) := by
    have hT2 : (0 : ℝ) < T / 2 := by linarith
    have hsq : (0 : ℝ) < (T / 2) ^ 2 := by positivity
    have hpos2 : (0 : ℝ) < 1 + 1 / (4 * T ^ 2) := by positivity
    have fact : (1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2 = (T / 2) ^ 2 * (1 + 1 / (4 * T ^ 2)) := by
      field_simp
      ring
    have e1 : Real.log ((T / 2) ^ 2) = 2 * Real.log (T / 2) := by
      rw [Real.log_pow]
      push_cast
      ring
    have key : Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) - 2 * Real.log (T / 2)
        = Real.log (1 + 1 / (4 * T ^ 2)) := by
      rw [fact, Real.log_mul (ne_of_gt hsq) (ne_of_gt hpos2), e1]
      ring
    calc (T / 4) * Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) - (T / 2) * Real.log (T / 2)
        = (T / 4) * (Real.log ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) - 2 * Real.log (T / 2)) := by
          ring
      _ = (T / 4) * Real.log (1 + 1 / (4 * T ^ 2)) := by rw [key]
  have harctid : ((1 : ℝ) / 4 - 1 / 2) * Real.arctan (2 * T) + Real.pi / 8
      = (1 / 4) * Real.arctan (1 / (2 * T)) := by
    have h2T : 0 < 2 * T := by linarith
    have hinv : Real.arctan (1 / (2 * T)) = Real.pi / 2 - Real.arctan (2 * T) := by
      have h := Real.arctan_inv_of_pos h2T
      have h1 : (2 * T)⁻¹ = 1 / (2 * T) := by rw [one_div]
      rw [h1] at h
      exact h
    rw [hinv]
    ring
  unfold gammaRemainder stirlingImag
  rw [hdig, hmain, hJK, show (T / 2) / (1 / 4) = 2 * T by ring]
  linear_combination hlogid + harctid
/-- LEAF. Backlund p. 350, display 21, the real positive reciprocal-square kernel.
Its primitive is minus one over twice the quadratic denominator. -/
theorem kernel_integral (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun u : ℝ => (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2)
      (Set.Ioi 0) volume ∧
    (∫ u in Set.Ioi (0 : ℝ), (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2) =
      1 / (2 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) := by
  let F : ℝ → ℝ := fun u => -1 / (2 * ((u + 1 / 4) ^ 2 + (T / 2) ^ 2))
  let K : ℝ → ℝ := fun u => (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2
  have hd (u : ℝ) : 0 < (u + 1 / 4) ^ 2 + (T / 2) ^ 2 := by positivity
  have hderiv (u : ℝ) (_ : u ∈ Set.Ici (0 : ℝ)) : HasDerivAt F (K u) u := by
    have hq : HasDerivAt (fun v : ℝ => 2 * ((v + 1 / 4) ^ 2 + (T / 2) ^ 2))
        (4 * (u + 1 / 4)) u := by
      convert ((((hasDerivAt_id u).add_const (1 / 4)).pow 2).add_const ((T / 2) ^ 2)).const_mul 2 using 1
      · ext v; dsimp <;> ring
      · dsimp <;> ring
    have hh := (hq.inv (by positivity : 2 * ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ≠ 0)).neg
    convert hh using 1
    · ext v; dsimp [F]; ring
    · dsimp [K]; field_simp; ring
  have hn (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) : 0 ≤ K u := by
    have hu0 : 0 < u := hu
    dsimp [K]
    positivity
  have htop : Tendsto (fun u : ℝ => 2 * ((u + 1 / 4) ^ 2 + (T / 2) ^ 2)) atTop atTop := by
    apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact tendsto_atTop_add_const_right _ ((T / 2) ^ 2)
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_atTop_add_const_right _ (1 / 4 : ℝ) tendsto_id))
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa only [F, Pi.neg_apply, Pi.inv_apply, neg_div, one_div, neg_zero] using htop.inv_tendsto_atTop.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hn hlim, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hn hlim
  change (∫ u in Set.Ioi (0 : ℝ), K u) = _
  rw [h]
  dsimp [F]
  ring

/-- LEAF. Backlund p. 374, the imaginary Stieltjes remainder estimate.
The periodic Bernoulli factor is between zero and one quarter.
An explicit positive kernel majorant supplies the displayed one over 3T bound. -/
theorem stirlingImag_bound (T : ℝ) (hT : 0 < T) : |stirlingImag T| ≤ 1 / (3 * T) := by
  let K : ℝ → ℝ := fun u => (u + 1 / 4) / ((u + 1 / 4) ^ 2 + (T / 2) ^ 2) ^ 2
  let H : ℝ → ℝ := fun u => Int.fract u - (Int.fract u) ^ 2
  have hH (u : ℝ) : 0 ≤ H u ∧ H u ≤ (1 / 4 : ℝ) := by
    have h0 := Int.fract_nonneg u
    have h1 := Int.fract_lt_one u
    dsimp [H]
    constructor <;> nlinarith [sq_nonneg (Int.fract u - 1 / 2)]
  obtain ⟨hKi, hKeq⟩ := kernel_integral T hT
  have hKn (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) : 0 ≤ K u := by
    have hu0 : 0 < u := hu
    dsimp [K]
    positivity
  have hHi : IntegrableOn (fun u => H u * K u) (Set.Ioi 0) volume := by
    apply Integrable.bdd_mul (c := 1 / 4) hKi
    · exact (measurable_fract.sub (measurable_fract.pow_const 2)).aestronglyMeasurable
    · exact ae_of_all _ (fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hH u).1]; exact (hH u).2)
  have hIn : 0 ≤ ∫ u in Set.Ioi (0 : ℝ), H u * K u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (hH u).1 (hKn u hu)
  have hIle : (∫ u in Set.Ioi (0 : ℝ), H u * K u) ≤
      (1 / 4) * (1 / (2 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2))) := by
    rw [← hKeq, ← integral_const_mul]
    apply integral_mono_ae hHi (hKi.const_mul (1 / 4))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_le_mul_of_nonneg_right (hH u).2 (hKn u hu)
  have hform : stirlingImag T = -(T / 2) * ∫ u in Set.Ioi (0 : ℝ), H u * K u := by
    unfold stirlingImag
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [H, K]
    ring
  rw [hform, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < T / 2), abs_of_nonneg hIn]
  apply (mul_le_mul_of_nonneg_left hIle (by positivity : 0 ≤ T / 2)).trans
  have hd : 0 < 2 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) := by positivity
  calc
    _ = T / (16 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) := by field_simp; ring
    _ ≤ 1 / (3 * T) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 16 * ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)) (by positivity : 0 < 3 * T)]
      nlinarith [sq_nonneg T]

/-- LEAF. Backlund p. 374, the explicit logarithmic loss in display 25. -/
theorem logarithmic_loss (T : ℝ) (hT : 0 < T) :
    |T / 4 * Real.log (1 + 1 / (4 * T ^ 2))| ≤ 1 / (16 * T) := by
  have hl : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) := Real.log_nonneg (by
    have hx : (0 : ℝ) ≤ 1 / (4 * T ^ 2) := by positivity
    linarith)
  have hu := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (4 * T ^ 2))
  rw [abs_of_nonneg (mul_nonneg (by positivity) hl)]
  calc
    _ ≤ T / 4 * (1 / (4 * T ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by field_simp; ring

/-- LEAF. Backlund p. 374, the explicit arctangent loss in display 25. -/
theorem arctangent_loss (T : ℝ) (hT : 0 < T) :
    |(1 / 4 : ℝ) * Real.arctan (1 / (2 * T))| ≤ 1 / (8 * T) := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  calc
    _ ≤ (1 / 4 : ℝ) * |1 / (2 * T)| := mul_le_mul_of_nonneg_left Real.abs_arctan_le_abs (by norm_num)
    _ = _ := by rw [abs_of_pos (by positivity : 0 < 1 / (2 * T))]; ring

/-- Backlund p. 374, exactly the original gamma_remainder_bound target.
CONDITIONAL ON the Euler summation identity gamma_stieltjes_expansion only. -/
theorem gamma_remainder_bound (T : ℝ) (hT : 1400 ≤ T) :
    |gammaRemainder T| ≤ 25 / (48 * T) := by
  have ht : 0 < T := by linarith
  rw [gamma_stieltjes_expansion T hT]
  calc
    _ ≤ |stirlingImag T| + |T / 4 * Real.log (1 + 1 / (4 * T ^ 2))| +
        |(1 / 4 : ℝ) * Real.arctan (1 / (2 * T))| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 / (3 * T) + 1 / (16 * T) + 1 / (8 * T) := by
      gcongr
      · exact stirlingImag_bound T ht
      · exact logarithmic_loss T ht
      · exact arctangent_loss T ht
    _ = _ := by ring

/-- Rosser p. 224, exactly the original circle_gamma_bound statement.
CONDITIONAL ON the two zeta envelope leaves in Decomp419a and the single
Euler summation identity in this file. The gamma integral bound is proved. -/
theorem circle_gamma_bound (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * Complex.I))‖) /
        (2 * π * Real.log (4 * 1.32 / 3) * N) +
      1 / 2 + 4 / (π * T) + |gammaRemainder T| / π ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ /
            (2 * Real.log (4 * 1.32 / 3)) := by
  have ht : 1400 ≤ T := hA.trans hT
  have hq : 0 < Real.log (4 * 1.32 / 3) := Real.log_pos (by norm_num)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < 2 * π * Real.log (4 * 1.32 / 3) := by positivity
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le
    (powered_log_integrable T ht N) ((logEnvelope_integrable T).const_mul (N : ℝ))
    (fun φ hφ => by
      obtain ⟨hp, hm⟩ := Decomp419a.zeta_circle_bound T φ ht hφ
      exact log_average_pow_le _ _ N _ (logEnvelope_nonneg T φ ht) hp hm)
  rw [intervalIntegral.integral_const_mul] at hi
  have hdiv := div_le_div_of_nonneg_right hi (mul_pos hden hNR).le
  have hcancel : ((N : ℝ) * ∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
      (2 * π * Real.log (4 * 1.32 / 3) * N) =
      (∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
        (2 * π * Real.log (4 * 1.32 / 3)) := by field_simp
  rw [hcancel] at hdiv
  have hc := center_euler_lower (5 / 4) T (by norm_num)
  norm_num only [show (2 : ℝ) * (5 / 4) = 5 / 2 by norm_num,
    Complex.ofReal_div, Complex.ofReal_ofNat] at hc
  have hcz : 0 < ‖riemannZeta (5 / 2) / riemannZeta (5 / 4)‖ := by
    apply norm_pos_iff.mpr
    exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hcz hc) (by positivity : 0 ≤ 2 * Real.log (4 * 1.32 / 3))
  have hg := div_le_div_of_nonneg_right (gamma_remainder_bound T ht) Real.pi_pos.le
  have hid : 4 / (π * T) + (25 / (48 * T)) / π = 217 / (48 * π * T) := by ring
  have hb := Decomp419a.envelope_budget T ht
  rw [← hid] at hb
  linarith


end LeanLab.RamareSaouter2003.Decomp419c

#print axioms LeanLab.RamareSaouter2003.Decomp419c.gamma_stieltjes_expansion
#print axioms LeanLab.RamareSaouter2003.Decomp419c.kernel_integral
#print axioms LeanLab.RamareSaouter2003.Decomp419c.stirlingImag_bound
#print axioms LeanLab.RamareSaouter2003.Decomp419c.logarithmic_loss
#print axioms LeanLab.RamareSaouter2003.Decomp419c.arctangent_loss
#print axioms LeanLab.RamareSaouter2003.Decomp419c.gamma_remainder_bound

#print axioms LeanLab.RamareSaouter2003.Decomp419c.circle_gamma_bound
