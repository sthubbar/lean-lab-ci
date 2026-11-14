import LeanLab.HelfgottMajor.SPLIT_very_low_zero_count
import LeanLab.PNTPort.StrongPNT.ResidueCalcOnRectangles
import LeanLab.PNTPort.ZetaZeros.LogDerivZero

/-!
# Split of `strip_count_at_one_le_explicit` (`HelfgottMajor/SPLIT_very_low_zero_count`)

The target bounds the multiplicity count of the zeros of a primitive character in the
critical strip with `|im| ≤ 1` by

`(1 / π) * log (q / (2 π e)) + 0.5 * log q + 17.7`.

The cut follows the argument principle on a box.  Every strip zero with `|im| ≤ 1` lies in
the box `[-1/4, 5/4] x [-3/2, 3/2]`, so the count is at most the multiplicity count of the
zeros of a function `g` in that box, where `g` is `L χ` for a nontrivial `χ` and the
pole-removed trivial `L`-function otherwise.  The residue form of the rectangle theorem then
turns that count into the rectangle integral of `g'/g`, the integral is at most the
periphery `9/2` times the supremum of `‖g'/g‖` on the border, and the arithmetic of
`9/(2 π) ≤ 0.819` closes the bound.  Two steps stay open:

* `border_zero_free` — the border of the box carries no zero of `g`;
* `border_norm_logDeriv_le` — the explicit bound `‖g'/g‖ ≤ 0.5 log q + 11.7` on that border.

Everything else (the residue identity, the integral estimate, the count-to-box bridge, the
finiteness of the zeros in the box and the final arithmetic) is proved here.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.SplitStripCount

open Real MeasureTheory Set Filter
open scoped Topology
open LeanLab.HelfgottArcs Decomp269a Decomp269b
open scoped Interval
open LeanLab.PNTPort.ZetaZeros (tendsto_mul_logDeriv)

/-! ### The residue step of the argument principle -/

/-- At a zero of an analytic function the logarithmic derivative has a simple pole. -/
theorem ord_logDeriv_zero {f : ℂ → ℂ} {u : ℂ} (hf : AnalyticAt ℂ f u)
    (htop : analyticOrderAt f u ≠ ⊤) (h : f u = 0) :
    meromorphicOrderAt (logDeriv f) u = -1 := by
  have hm : analyticOrderAt f u = ((analyticOrderNatAt f u : ℕ) : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt htop).symm
  have hpos : analyticOrderNatAt f u ≠ 0 := by
    intro hc
    exact (hf.analyticOrderAt_ne_zero.mpr h) (by rw [hm, hc]; simp)
  have h1 : meromorphicOrderAt f u ≠ 0 := by
    rw [hf.meromorphicOrderAt_eq, hm]
    simp only [ENat.map_natCast]
    intro hc
    exact hpos (by exact_mod_cast hc)
  have h2 : meromorphicOrderAt f u ≠ ⊤ := by
    rw [hf.meromorphicOrderAt_eq, hm]; simp
  exact meromorphicOrderAt_logDeriv_eq_neg_one hf.meromorphicAt h1 h2

/-- Away from the zeros of an analytic function the logarithmic derivative is analytic
(hence has nonnegative order). -/
theorem ord_logDeriv_nonneg {f : ℂ → ℂ} {u : ℂ} (hf : AnalyticAt ℂ f u) (h : f u ≠ 0) :
    0 ≤ meromorphicOrderAt (logDeriv f) u := by
  have haz : analyticOrderAt f u = 0 := hf.analyticOrderAt_eq_zero.mpr h
  refine meromorphicOrderAt_logDeriv_nonneg hf.meromorphicAt ?_
  rw [hf.meromorphicOrderAt_eq, haz]; simp

/-- The residue of `f'/f` at a point of analyticity of `f` is the multiplicity. -/
theorem residue_logDeriv_eq {f : ℂ → ℂ} {u : ℂ} (hf : AnalyticAt ℂ f u)
    (htop : analyticOrderAt f u ≠ ⊤) :
    residue (logDeriv f) u = (analyticOrderNatAt f u : ℂ) := by
  refine residue_eq_of_tendsto ?_
  have h := tendsto_mul_logDeriv hf (Nat.cast_analyticOrderNatAt htop).symm
  simpa [logDeriv] using h

/-- **Argument principle on a rectangle, residue form.** -/
theorem rect_logDeriv_eq_sum_mult {f : ℂ → ℂ} {z w : ℂ} (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im)
    (hf : ∀ u ∈ Complex.Rectangle z w, AnalyticAt ℂ f u)
    (hntop : ∀ u ∈ Complex.Rectangle z w, analyticOrderAt f u ≠ ⊤)
    (hb : ∀ u ∈ RectangleBorder z w, f u ≠ 0)
    (hfin : (Complex.Rectangle z w ∩ {u | f u = 0}).Finite) :
    RectangleIntegral' (logDeriv f) z w
      = ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℂ) := by
  classical
  have hbz : RectangleBorder z w ⊆ Complex.Rectangle z w := rectangleBorder_subset_rectangle z w
  have hzeros : (Complex.Rectangle z w ∩ {u | meromorphicOrderAt (logDeriv f) u < 0})
      = (Complex.Rectangle z w ∩ {u | f u = 0}) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨huR, hlt⟩
      refine ⟨huR, ?_⟩
      by_contra hne
      exact absurd hlt (not_lt.mpr (ord_logDeriv_nonneg (hf u huR) hne))
    · rintro ⟨huR, h0⟩
      refine ⟨huR, ?_⟩
      rw [ord_logDeriv_zero (hf u huR) (hntop u huR) h0]
      decide
  have hmero : MeromorphicOn (logDeriv f) (Complex.Rectangle z w) :=
    fun u hu => (hf u hu).meromorphicAt.logDeriv
  have hdisj : Disjoint (RectangleBorder z w) {u | meromorphicOrderAt (logDeriv f) u < 0} := by
    rw [Set.disjoint_left]
    intro u hub hlt
    have h0 := ord_logDeriv_nonneg (hf u (hbz hub)) (hb u hub)
    exact absurd hlt (not_lt.mpr h0)
  have hsimple : HasSimplePolesOn (logDeriv f) (Complex.Rectangle z w) := by
    intro u hu
    by_cases h : f u = 0
    · rw [ord_logDeriv_zero (hf u hu) (hntop u hu) h]
      exact le_rfl
    · exact le_trans (by decide) (ord_logDeriv_nonneg (hf u hu) h)
  have hpol : (Complex.Rectangle z w ∩ {u | meromorphicOrderAt (logDeriv f) u < 0}).Finite := by
    rw [hzeros]; exact hfin
  rw [RectangleIntegral'_eq_sumResiduesIn hzw hzw' hmero hdisj hpol hsimple, hzeros,
    sumResiduesIn, tsum_subtype, tsum_eq_sum (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Set.indicator_of_mem (hfin.mem_toFinset.mp hx),
      residue_logDeriv_eq (hf x (hfin.mem_toFinset.mp hx).1) (hntop x (hfin.mem_toFinset.mp hx).1)]
  · intro x hx
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hx (hfin.mem_toFinset.mpr hmem)

/-! ### The border estimate for the rectangle integral -/

theorem mem_uIcc_of_mem_uIoc {a b x : ℝ} (hx : x ∈ Ι a b) : x ∈ [[a, b]] := by
  simp only [Set.uIcc, Set.uIoc] at *
  exact ⟨le_of_lt hx.1, hx.2⟩

theorem norm_HIntegral_le {f : ℂ → ℂ} {x₁ x₂ y M : ℝ}
    (h : ∀ x ∈ Ι x₁ x₂, ‖f (x + y * Complex.I)‖ ≤ M) :
    ‖HIntegral f x₁ x₂ y‖ ≤ M * |x₂ - x₁| :=
  intervalIntegral.norm_integral_le_of_norm_le_const h

theorem norm_VIntegral_le {f : ℂ → ℂ} {x y₁ y₂ M : ℝ}
    (h : ∀ y ∈ Ι y₁ y₂, ‖f (x + y * Complex.I)‖ ≤ M) :
    ‖VIntegral f x y₁ y₂‖ ≤ M * |y₂ - y₁| := by
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const h
  have h2 : ‖VIntegral f x y₁ y₂‖ = ‖∫ y in y₁..y₂, f (x + y * Complex.I)‖ := by
    simp [VIntegral]
  rw [h2]
  exact h1

theorem norm_rectangleIntegral_le {f : ℂ → ℂ} {z w : ℂ} (hzw : z.re ≤ w.re)
    (hzw' : z.im ≤ w.im) {M : ℝ} (h : ∀ u ∈ RectangleBorder z w, ‖f u‖ ≤ M) :
    ‖RectangleIntegral f z w‖ ≤ 2 * M * ((w.re - z.re) + (w.im - z.im)) := by
  have hb1 : ∀ x ∈ Ι z.re w.re, ‖f (x + z.im * Complex.I)‖ ≤ M := fun x hx =>
    h _ (mapsTo_rectangleBorder_left_im z w (mem_uIcc_of_mem_uIoc hx))
  have hb2 : ∀ x ∈ Ι z.re w.re, ‖f (x + w.im * Complex.I)‖ ≤ M := fun x hx =>
    h _ (mapsTo_rectangleBorder_right_im z w (mem_uIcc_of_mem_uIoc hx))
  have hl : ∀ y ∈ Ι z.im w.im, ‖f (z.re + (y : ℂ) * Complex.I)‖ ≤ M := fun y hy =>
    h _ (mapsTo_rectangleBorder_left_re z w (mem_uIcc_of_mem_uIoc hy))
  have hr : ∀ y ∈ Ι z.im w.im, ‖f (w.re + (y : ℂ) * Complex.I)‖ ≤ M := fun y hy =>
    h _ (mapsTo_rectangleBorder_right_re z w (mem_uIcc_of_mem_uIoc hy))
  have h1 : ‖HIntegral f z.re w.re z.im‖ ≤ M * (w.re - z.re) := by
    have := norm_HIntegral_le (x₁ := z.re) (x₂ := w.re) (y := z.im) hb1
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w.re - z.re)] at this
  have h2 : ‖HIntegral f z.re w.re w.im‖ ≤ M * (w.re - z.re) := by
    have := norm_HIntegral_le (x₁ := z.re) (x₂ := w.re) (y := w.im) hb2
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w.re - z.re)] at this
  have h3 : ‖VIntegral f w.re z.im w.im‖ ≤ M * (w.im - z.im) := by
    have := norm_VIntegral_le (x := w.re) (y₁ := z.im) (y₂ := w.im) hr
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w.im - z.im)] at this
  have h4 : ‖VIntegral f z.re z.im w.im‖ ≤ M * (w.im - z.im) := by
    have := norm_VIntegral_le (x := z.re) (y₁ := z.im) (y₂ := w.im) hl
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w.im - z.im)] at this
  have h5 : ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
      VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im‖ ≤
      M * (w.re - z.re) + M * (w.re - z.re) + M * (w.im - z.im) + M * (w.im - z.im) := by
    have e1 : ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
        VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im‖ ≤
        ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
          VIntegral f w.re z.im w.im‖ + ‖VIntegral f z.re z.im w.im‖ :=
      norm_sub_le _ _
    have e2 : ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
        VIntegral f w.re z.im w.im‖ ≤
        ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im‖ +
          ‖VIntegral f w.re z.im w.im‖ := norm_add_le _ _
    have e3 : ‖HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im‖ ≤
        ‖HIntegral f z.re w.re z.im‖ + ‖HIntegral f z.re w.re w.im‖ := norm_sub_le _ _
    linarith
  rw [RectangleIntegral]
  nlinarith [h5]

theorem norm_rectangleIntegral'_le {f : ℂ → ℂ} {z w : ℂ} (hzw : z.re ≤ w.re)
    (hzw' : z.im ≤ w.im) {M : ℝ} (h : ∀ u ∈ RectangleBorder z w, ‖f u‖ ≤ M) :
    ‖RectangleIntegral' f z w‖ ≤ M * ((w.re - z.re) + (w.im - z.im)) / Real.pi := by
  have hmain := norm_rectangleIntegral_le hzw hzw' h
  have hc : ‖(1 / (2 * (Real.pi : ℂ) * Complex.I))‖ = 1 / (2 * Real.pi) := by
    have h2 : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [norm_div, h2, norm_one]
  rw [RectangleIntegral', norm_smul, hc]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hstep : (1 / (2 * Real.pi)) * ‖RectangleIntegral f z w‖ ≤
      (1 / (2 * Real.pi)) * (2 * M * ((w.re - z.re) + (w.im - z.im))) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  have heq : (1 / (2 * Real.pi)) * (2 * M * ((w.re - z.re) + (w.im - z.im))) =
      M * ((w.re - z.re) + (w.im - z.im)) / Real.pi := by
    field_simp
  linarith [hstep, heq]

/-- The norm of a sum of cast multiplicities is the real sum. -/
private lemma norm_sum_natCast (s : Finset ℂ) (m : ℂ → ℕ) :
    ‖∑ ρ ∈ s, (m ρ : ℂ)‖ = ∑ ρ ∈ s, (m ρ : ℝ) := by
  have h1 : (∑ ρ ∈ s, (m ρ : ℂ)) = ∑ ρ ∈ s, (((m ρ : ℝ)) : ℂ) :=
    Finset.sum_congr rfl fun ρ _ => (Complex.ofReal_natCast (m ρ)).symm
  rw [h1, ← Complex.ofReal_sum s (fun ρ => (m ρ : ℝ)),
    Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]

/-- **The count is bounded by the periphery times the boundary supremum of `‖f'/f‖`.** -/
theorem sum_mult_le_of_logDeriv_bound {f : ℂ → ℂ} {z w : ℂ} (hzw : z.re ≤ w.re)
    (hzw' : z.im ≤ w.im) {M : ℝ}
    (hf : ∀ u ∈ Complex.Rectangle z w, AnalyticAt ℂ f u)
    (hntop : ∀ u ∈ Complex.Rectangle z w, analyticOrderAt f u ≠ ⊤)
    (hb : ∀ u ∈ RectangleBorder z w, f u ≠ 0)
    (hM : ∀ u ∈ RectangleBorder z w, ‖logDeriv f u‖ ≤ M)
    (hfin : (Complex.Rectangle z w ∩ {u | f u = 0}).Finite) :
    ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt f ρ : ℝ) ≤
      M * ((w.re - z.re) + (w.im - z.im)) / Real.pi := by
  classical
  have hnorm := norm_rectangleIntegral'_le hzw hzw' (f := logDeriv f) hM
  rw [rect_logDeriv_eq_sum_mult hzw hzw' hf hntop hb hfin] at hnorm
  rw [norm_sum_natCast] at hnorm
  exact hnorm

/-! ### The count-to-box bridge -/

/-- At a point where two functions agree on a neighbourhood, their multiplicities agree. -/
private lemma analyticOrderNatAt_congr' {f g : ℂ → ℂ} {u : ℂ} (h : f =ᶠ[nhds u] g) :
    analyticOrderNatAt f u = analyticOrderNatAt g u := by
  have h' : analyticOrderAt f u = analyticOrderAt g u := analyticOrderAt_congr h
  simp [analyticOrderNatAt, h']

/-- Every strip zero of absolute imaginary part at most one lies in the box
`[-1/4, 5/4] x [-3/2, 3/2]`. -/
theorem mem_box_of_mem_strip_one {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : |ρ.im| ≤ 1) :
    ρ ∈ Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ) := by
  rw [mem_Rect (by norm_num) (by norm_num)]
  obtain ⟨him1, him2⟩ := abs_le.mp him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The count-to-box-sum bridge.**  The multiplicity count of the strip zeros of `L χ` with
`|im| ≤ 1` is at most the multiplicity count of the zeros of `g` in the box, provided `g`
vanishes at every strip zero of `L χ` and has there the multiplicity of `L χ`. -/
theorem strip_count_le_box_zero_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (g : ℂ → ℂ)
    (hgzero : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 → g ρ = 0)
    (hgmult : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 →
      analyticOrderNatAt g ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (hfin : (Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ)
      ∩ {u : ℂ | g u = 0}).Finite) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ≤
    ∑ ρ ∈ hfin.toFinset, (analyticOrderNatAt g ρ : ℝ) := by
  classical
  have hSfin : ({ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1}).Finite := LeanLab.HelfgottMajor.ZeroCount1623.stripZeros_finite χ 1
  haveI : Fintype {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      |ρ.im| ≤ 1} := hSfin.fintype
  have hsub : (Finset.univ.image
      (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1} => ρ.val)) ⊆ hfin.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨ρ, -, rfl⟩ := hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨mem_box_of_mem_strip_one ρ.2.2.1 ρ.2.2.2.1 ρ.2.2.2.2,
      hgzero ρ.val ρ.2.1 ρ.2.2.2.1⟩
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ))
      = ∑ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
          |ρ.im| ≤ 1}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) :=
        tsum_fintype _
    _ = ∑ x ∈ Finset.univ.image
          (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
            |ρ.im| ≤ 1} => ρ.val),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) x : ℝ) := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact Subtype.ext hxy
    _ = ∑ x ∈ Finset.univ.image
          (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
            |ρ.im| ≤ 1} => ρ.val), (analyticOrderNatAt g x : ℝ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_image] at hx
        obtain ⟨ρ, -, rfl⟩ := hx
        rw [hgmult ρ.val ρ.2.1 ρ.2.2.2.1]
    _ ≤ ∑ x ∈ hfin.toFinset, (analyticOrderNatAt g x : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.cast_nonneg _)

/-- **The target from a border bound.**  With `g` as in `strip_count_le_box_zero_sum`, a
bound `‖g'/g‖ ≤ M` on the border of the box, analyticity in the box, a zero-free border and
the arithmetic inequality for `M` together give the height-one count. -/
theorem strip_count_at_one_le_explicit_of_border_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (g : ℂ → ℂ) {M : ℝ}
    (hgzero : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 → g ρ = 0)
    (hgmult : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 →
      analyticOrderNatAt g ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    (han : ∀ u ∈ Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      AnalyticAt ℂ g u)
    (hntop : ∀ u ∈ Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      analyticOrderAt g u ≠ ⊤)
    (hb : ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      g u ≠ 0)
    (hM : ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      ‖logDeriv g u‖ ≤ M)
    (hfin : (Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ)
      ∩ {u : ℂ | g u = 0}).Finite)
    (hMle : M * (((5 : ℝ) / 4 - (-1 / 4)) + (3 / 2 - (-3 / 2))) / Real.pi ≤
      (1 / Real.pi) * Real.log (q / (2 * Real.pi * Real.exp 1)) + 0.5 * Real.log q + 17.7) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
        |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ≤
    (1 / Real.pi) * Real.log (q / (2 * Real.pi * Real.exp 1)) + 0.5 * Real.log q + 17.7 := by
  refine (strip_count_le_box_zero_sum χ g hgzero hgmult hfin).trans ?_
  refine (sum_mult_le_of_logDeriv_bound (z := (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ))
    (w := (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ)) (by norm_num) (by norm_num) (M := M)
    han hntop hb hM hfin).trans hMle

/-! ### The arithmetic of the explicit height-one budget -/

/-- The box `[-1/4, 5/4] x [-3/2, 3/2]` has periphery `9/2`, so a border bound
`0.5 log q + 11.7` produces at most `0.819 log q + 16.79`, which is inside the explicit
budget `(1 / π) log (q / (2 π e)) + 0.5 log q + 17.7`. -/
theorem box_arith_explicit {q : ℕ} [NeZero q] :
    (0.5 * Real.log (q : ℝ) + 11.7) *
        (((5 : ℝ) / 4 - (-1 / 4)) + (3 / 2 - (-3 / 2))) / Real.pi ≤
      (1 / Real.pi) * Real.log ((q : ℝ) / (2 * Real.pi * Real.exp 1)) +
        0.5 * Real.log (q : ℝ) + 17.7 := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.one_le
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi1 : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi2 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hlogpi : Real.log Real.pi ≤ 1.1459 := by
    have hsplit : Real.log Real.pi = Real.log 3 + Real.log (Real.pi / 3) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      ring_nf
    have hthird : (0 : ℝ) < Real.pi / 3 := by linarith
    have hlow : Real.log (Real.pi / 3) ≤ Real.pi / 3 - 1 := Real.log_le_sub_one_of_pos hthird
    have h3 : Real.pi / 3 ≤ 1.0472 := by linarith
    rw [hsplit]
    linarith [Real.log_three_lt_d9]
  have hLle : Real.log (2 * Real.pi * Real.exp 1) ≤ 2.84 := by
    rw [Real.log_mul (by positivity) (Real.exp_pos 1).ne',
      Real.log_mul (by norm_num) hpi0.ne', Real.log_exp]
    linarith [Real.log_two_lt_d9]
  have hsplit : Real.log ((q : ℝ) / (2 * Real.pi * Real.exp 1)) =
      Real.log (q : ℝ) - Real.log (2 * Real.pi * Real.exp 1) :=
    Real.log_div hq0.ne' (by positivity)
  rw [hsplit]
  have hper : (((5 : ℝ) / 4 - (-1 / 4)) + (3 / 2 - (-3 / 2))) = 9 / 2 := by norm_num
  rw [hper]
  have hcoef1 : (1 : ℝ) / Real.pi ≤ 1 / 3.1415 := one_div_le_one_div_of_le (by norm_num) hpi1.le
  have hcoef2 : (1 : ℝ) / 3.1416 ≤ 1 / Real.pi :=
    one_div_le_one_div_of_le hpi0 hpi2.le
  have hcalc : (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) / Real.pi
      = (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) * (1 / Real.pi) := by ring
  rw [hcalc]
  have h9 : (0 : ℝ) ≤ (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) := by nlinarith
  have hLHS : (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) * (1 / Real.pi) ≤
      (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) * (1 / 3.1415) :=
    mul_le_mul_of_nonneg_left hcoef1 h9
  by_cases hbig : 2.84 ≤ Real.log (q : ℝ)
  · have hfac : (0 : ℝ) ≤ Real.log (q : ℝ) - 2.84 := by linarith
    have hR : (1 / 3.1416) * (Real.log (q : ℝ) - 2.84) ≤
        (1 / Real.pi) * (Real.log (q : ℝ) - Real.log (2 * Real.pi * Real.exp 1)) := by
      have ha : (1 / 3.1416) * (Real.log (q : ℝ) - 2.84) ≤
          (1 / Real.pi) * (Real.log (q : ℝ) - 2.84) :=
        mul_le_mul_of_nonneg_right hcoef2 hfac
      have hb : (1 / Real.pi) * (Real.log (q : ℝ) - 2.84) ≤
          (1 / Real.pi) * (Real.log (q : ℝ) - Real.log (2 * Real.pi * Real.exp 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hmain : (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) * (1 / 3.1415) ≤
        (1 / 3.1416) * (Real.log (q : ℝ) - 2.84) + 0.5 * Real.log (q : ℝ) + 17.7 := by
      nlinarith [hlogq]
    linarith
  · have hfac : Real.log (q : ℝ) - 2.84 ≤ 0 := by linarith
    have hR : (1 / 3.1415) * (Real.log (q : ℝ) - 2.84) ≤
        (1 / Real.pi) * (Real.log (q : ℝ) - Real.log (2 * Real.pi * Real.exp 1)) := by
      have ha : (1 / 3.1415) * (Real.log (q : ℝ) - 2.84) ≤
          (1 / Real.pi) * (Real.log (q : ℝ) - 2.84) :=
        mul_le_mul_of_nonpos_right hcoef1 hfac
      have hb : (1 / Real.pi) * (Real.log (q : ℝ) - 2.84) ≤
          (1 / Real.pi) * (Real.log (q : ℝ) - Real.log (2 * Real.pi * Real.exp 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hmain : (0.5 * Real.log (q : ℝ) + 11.7) * (9 / 2) * (1 / 3.1415) ≤
        (1 / 3.1415) * (Real.log (q : ℝ) - 2.84) + 0.5 * Real.log (q : ℝ) + 17.7 := by
      nlinarith [hlogq]
    linarith

/-! ### Two elementary facts about an entire function -/

/-- The zero set of an entire function that is not identically zero is finite inside any
axis-parallel rectangle. -/
theorem rect_zeros_finite {g : ℂ → ℂ} {z w : ℂ} (gd : Differentiable ℂ g)
    (hex : ∃ v, g v ≠ 0) :
    (Complex.Rectangle z w ∩ {u : ℂ | g u = 0}).Finite := by
  have hKc : IsCompact (Complex.Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  have hcod : g ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete (f := g)
      (gd.differentiableOn.analyticOnNhd isOpen_univ) hex.choose_spec
  rw [Set.preimage_compl] at hcod
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  exact (hKc.inter_right hclosed).finite (hdisc.mono Set.inter_subset_right)

/-- An entire function that is not identically zero has finite order of vanishing at every
point: an infinite order at one point would force the function to vanish everywhere. -/
theorem analyticOrderAt_ne_top_of_entire {g : ℂ → ℂ} (gd : Differentiable ℂ g)
    (hex : ∃ v, g v ≠ 0) (u : ℂ) : analyticOrderAt g u ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h0 : AnalyticOnNhd ℂ g Set.univ := gd.differentiableOn.analyticOnNhd isOpen_univ
  have hz : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := analyticOnNhd_const
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq h0 hz isPreconnected_univ
    (Set.mem_univ u) htop
  exact hex.choose_spec (heq (Set.mem_univ hex.choose))

/-! ### The two open steps -/

/-- LEAF. Border bound step.  On the border of the box `[-1/4, 5/4] x [-3/2, 3/2]` the
logarithmic derivative of the `L`-function of a primitive character is bounded by
`0.5 log q + 11.7`; for the principal character the pole-removed function
`s ↦ (s - 1) L(s, χ)` is used, which is what the piecewise choice below does.  This is the
count-free analytic input: it is a pointwise estimate on a fixed contour, not a statement
about the zeros. -/
theorem border_norm_logDeriv_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      ‖logDeriv (fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
        else DirichletCharacter.LFunction χ s) u‖ ≤ 0.5 * log q + 11.7 := by
  sorry

/-- LEAF. Zero-free border step.  The border of the box `[-1/4, 5/4] x [-3/2, 3/2]` carries
no zero of the `L`-function of a primitive character (with the pole removed in the principal
case), so that the logarithmic derivative in the previous leaf is the logarithmic derivative
of a function that does not vanish on the contour. -/
theorem border_zero_free (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      (if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q u
        else DirichletCharacter.LFunction χ u) ≠ 0 := by
  sorry

/-! ### The assembly -/

/-- The height-one multiplicity count of the strip zeros of a primitive character, from the
two open steps above and the rectangle argument principle. -/
theorem strip_count_at_one_le_explicit_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ 1},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) ≤
    (1 / π) * log (q / (2 * π * exp 1)) + 0.5 * log q + 17.7 := by
  classical
  set g : ℂ → ℂ := fun s => if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ q s
    else DirichletCharacter.LFunction χ s with hg
  have hg1 : χ = 1 → g = DirichletCharacter.LFunctionTrivChar₁ q := by
    intro h; rw [hg]; funext s; rw [if_pos h]
  have hg2 : χ ≠ 1 → g = DirichletCharacter.LFunction χ := by
    intro h; rw [hg]; funext s; rw [if_neg h]
  have hgd : Differentiable ℂ g := by
    by_cases h : χ = 1
    · rw [hg1 h]; exact DirichletCharacter.differentiable_LFunctionTrivChar₁ q
    · rw [hg2 h]; exact DirichletCharacter.differentiable_LFunction h
  have hb : ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ)
      (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ), g u ≠ 0 := by
    intro u hu
    have hu' := border_zero_free q χ hχ u hu
    simpa only [hg] using hu'
  have hcorner : (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) ∈
      RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ) := by
    simp [RectangleBorder, Complex.mem_reProdIm]
  have hex : ∃ v, g v ≠ 0 := ⟨_, hb _ hcorner⟩
  have hfin : (Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ)
      ∩ {u : ℂ | g u = 0}).Finite := rect_zeros_finite hgd hex
  have hntop : ∀ u ∈ Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      analyticOrderAt g u ≠ ⊤ := fun u _ => analyticOrderAt_ne_top_of_entire hgd hex u
  have han : ∀ u ∈ Complex.Rectangle (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ) (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ),
      AnalyticAt ℂ g u := by
    intro u _
    by_cases h : χ = 1
    · rw [hg1 h]; exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).analyticAt u
    · rw [hg2 h]; exact (DirichletCharacter.differentiable_LFunction h).analyticAt u
  have hgzero : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 → g ρ = 0 := by
    intro ρ hL hlt
    by_cases h : χ = 1
    · have hρ1 : ρ ≠ 1 := by
        rintro rfl
        rw [Complex.one_re] at hlt
        exact absurd hlt (by norm_num)
      have hL1 : DirichletCharacter.LFunctionTrivChar q ρ = 0 := by
        have h' : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ = 0 := by
          rw [← h]; exact hL
        exact h'
      rw [hg1 h]
      simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ1, hL1, mul_zero]
    · rw [hg2 h]; exact hL
  have hgmult : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 →
      analyticOrderNatAt g ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
    intro ρ hL hlt
    by_cases h : χ = 1
    · have hρ1 : ρ ≠ 1 := by
        rintro rfl
        rw [Complex.one_re] at hlt
        exact absurd hlt (by norm_num)
      rw [hg1 h]
      have hEq : DirichletCharacter.LFunctionTrivChar₁ q
          =ᶠ[nhds ρ] fun s => (s - 1) * DirichletCharacter.LFunction χ s := by
        filter_upwards [compl_singleton_mem_nhds hρ1] with z hz
        simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz]
        rw [h]
      rw [analyticOrderNatAt_congr' hEq]
      have h1 : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := by fun_prop
      have h2 : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
        rw [Complex.analyticAt_iff_eventually_differentiableAt]
        filter_upwards [compl_singleton_mem_nhds hρ1] with z hz
        exact DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)
      have hord : analyticOrderAt (fun s : ℂ => (s - 1) * DirichletCharacter.LFunction χ s) ρ
          = analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
        have hmul := analyticOrderAt_mul (z₀ := ρ) h1 h2
        rw [analyticOrderAt_id_sub_const_of_ne (c := 1) hρ1, zero_add] at hmul
        exact hmul
      have := congrArg ENat.toNat hord
      simpa [analyticOrderNatAt] using this
    · rw [hg2 h]
  have hM : ∀ u ∈ RectangleBorder (⟨(-1/4 : ℝ), (-3/2 : ℝ)⟩ : ℂ)
      (⟨(5/4 : ℝ), (3/2 : ℝ)⟩ : ℂ), ‖logDeriv g u‖ ≤ 0.5 * log q + 11.7 := by
    intro u hu
    have hu' := border_norm_logDeriv_le q χ hχ u hu
    simpa only [hg] using hu'
  refine strip_count_at_one_le_explicit_of_border_bound (M := 0.5 * log q + 11.7)
    χ g hgzero hgmult han hntop hb hM hfin ?_
  simpa using box_arith_explicit (q := q)

end LeanLab.HelfgottMajor.SplitStripCount
