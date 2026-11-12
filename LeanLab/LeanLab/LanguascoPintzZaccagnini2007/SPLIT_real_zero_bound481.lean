import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

/-!
Split of `real_zero_bound481` of `Decomp481b`, the real zero lower bound of preprint page 5.

The target asserts one positive constant `a` such that every real zero `1 - δ` of every real
character of modulus `r` satisfies `a * r ^ (-(1 / 2)) ≤ δ`.

The statement has two independent axes and the file cuts along both.

The size of `δ`. The lower bound is an assertion about zeros close to one only: once `1 / 2 ≤ δ`,
the conclusion follows from `a ≤ 1 / 4` together with `r ^ (-(1 / 2)) ≤ 1`, valid for `1 ≤ r`.
That step is elementary and is carried out in the assembly below, not left as a leaf.

The character. A character of modulus one is the trivial character, whose L function is the
Riemann zeta function, so the zeros near one there are a statement about zeta alone: that is
`leaf_real_zero_modulus_one481`. A real primitive character of modulus at least two is the
quadratic case, and the lower bound for it is `leaf_real_zero_primitive_large481`. An
imprimitive real character is the remaining case: the Euler factors at the ramified primes
remove zeros rather than add them, so a zero of the imprimitive L function need not come from
any primitive one, and the lower bound must be stated for that class on its own, which is
`leaf_real_zero_imprimitive481`.

Every leaf is the target with one case restriction and with `δ < 1 / 2`, so every leaf is
strictly weaker than the target and none of them restates it. The three case conditions `r ≤ 1`,
`2 ≤ r` with a primitive character, and a non-primitive character are exhaustive under the
target's `1 ≤ r`. `real_zero_bound481_split` below combines the three constants and the large
`δ` step into the target statement with no `sorry`, and it does not use `real_zero_bound481`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

noncomputable section

/-! Auxiliary lemmas for the modulus one leaf: the alternating ("eta") series
`∑ k, ((2k+1)^(-s) - (2k+2)^(-s))` converges for `0 < re s`, is termwise a positive
real for real `s ∈ (0,1)`, and equals `(1 - 2^(1-s)) * ζ s` there, so `ζ σ ≠ 0` for
real `σ ∈ (0,1)`. -/

namespace RZB481

open Complex Filter
open scoped Topology

/-- A nonnegative real base: the complex power is the coercion of the real power. -/
private theorem ofReal_rpow_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) :=
  Complex.ofReal_cpow hx y

/-- `((n : ℝ) : ℂ) ^ (-(σ : ℂ))` is the coercion of the real power. -/
private theorem nat_cpow_neg_eq {n : ℕ} {σ : ℝ} :
    (((n : ℂ)) ^ (-(σ : ℂ))) = ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) := by
  have hcoe : (((-σ : ℝ)) : ℂ) = -(σ : ℂ) := by push_cast; ring
  rw [← hcoe, ← Complex.ofReal_natCast n,
    ← ofReal_rpow_cpow (x := (n : ℝ)) (by positivity) (-σ)]

/-- Mean value bound for `t ↦ t ^ (-s)` between two positive reals. -/
private theorem norm_cpow_neg_sub_le {s : ℂ} (hs : -1 ≤ s.re) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  have hbound : ∀ x ∈ Set.Ico a b, ‖(-s) * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    have hnorm : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp
    have hmono : x ^ (-s.re - 1) ≤ a ^ (-s.re - 1) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.mpr ha)
        (Set.mem_Ioi.mpr hx0) hx.1
    rw [norm_mul, hnorm, norm_neg]
    gcongr
  have hmain : ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * a ^ (-s.re - 1) * (b - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => (t : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
      (C := ‖s‖ * a ^ (-s.re - 1))
      (fun x hx =>
        (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha hx.1)) (neg_ne_zero.mpr hs0)
          ).hasDerivWithinAt)
      hbound b (Set.right_mem_Icc.mpr hab)
  simpa only [norm_sub_rev] using hmain

/-- `t ↦ ((2k+1)^(-t) - (2k+2)^(-t))` is complex differentiable. -/
private theorem differentiableAt_pair_term (k : ℕ) (w : ℂ) :
    DifferentiableAt ℂ
      (fun t : ℂ => ((2 * k + 1 : ℕ) : ℂ) ^ (-t) - ((2 * k + 2 : ℕ) : ℂ) ^ (-t)) w := by
  have h1 : ((2 * k + 1 : ℕ) : ℂ) ≠ 0 := by
    have : (2 * k + 1 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have h2 : ((2 * k + 2 : ℕ) : ℂ) ≠ 0 := by
    have : (2 * k + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  exact ((differentiableAt_id.neg).const_cpow (Or.inl h1)).sub
    ((differentiableAt_id.neg).const_cpow (Or.inl h2))

/-- The alternating series is summable in the half plane `0 < re s`. -/
private theorem summable_pair_series {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ =>
      (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s))) := by
  have hmaj : Summable (fun k : ℕ => ‖s‖ * (((k : ℝ) + 1) ^ (-s.re - 1))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine Summable.mul_left ‖s‖ ?_
    exact hshift.congr (fun n => by norm_num)
  refine Summable.of_norm_bounded hmaj (fun k => ?_)
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
    have h : 2 * k + 1 ≤ 2 * k + 2 := by omega
    exact_mod_cast h
  have hb := norm_cpow_neg_sub_le (s := s) (by linarith) ha hab
  have hdiff1 : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by
    have h : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 2 : ℕ) : ℝ) := by
      have h' : (2 * k + 1 : ℕ) + 1 = 2 * k + 2 := by omega
      rw [← h']
      push_cast
      ring
    linarith
  rw [hdiff1, mul_one] at hb
  have hmono : ((2 * k + 1 : ℕ) : ℝ) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re - 1) := by
    refine Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · have h : (k : ℝ) + 1 ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      exact h
  exact hb.trans (by gcongr)

/-- The alternating series is complex differentiable in the half plane `0 < re s`. -/
private theorem differentiableAt_pair_series (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∑' k : ℕ,
        (((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w))) s := by
  have hr0 : 0 < s.re / 2 := by positivity
  have hmaj : Summable (fun k : ℕ => (‖s‖ + s.re / 2) * (((k : ℝ) + 1) ^ (-s.re / 2 - 1))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re / 2 - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-s.re / 2 - 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine Summable.mul_left (‖s‖ + s.re / 2) ?_
    exact hshift.congr (fun n => by norm_num)
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun t : ℂ => ((2 * k + 1 : ℕ) : ℂ) ^ (-t) - ((2 * k + 2 : ℕ) : ℂ) ^ (-t))
      (Metric.ball s (s.re / 2)) :=
    fun k x _ => (differentiableAt_pair_term k x).differentiableWithinAt
  have hle : ∀ (k : ℕ) (w : ℂ), w ∈ Metric.ball s (s.re / 2) →
      ‖((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w)‖
        ≤ (‖s‖ + s.re / 2) * (((k : ℝ) + 1) ^ (-s.re / 2 - 1)) := by
    intro k w hw
    have h2 : ‖w - s‖ < s.re / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hw
    have hwr : s.re / 2 < w.re := by
      have h1 : |(w - s).re| ≤ ‖w - s‖ := Complex.abs_re_le_norm _
      have h3 : w.re - s.re = (w - s).re := by simp
      have h4 : -(w.re - s.re) ≤ ‖w - s‖ := by
        rw [h3]
        exact (neg_le_abs _).trans h1
      linarith
    have hnorm : ‖w‖ ≤ ‖s‖ + s.re / 2 := by
      calc ‖w‖ = ‖s + (w - s)‖ := by rw [add_sub_cancel]
        _ ≤ ‖s‖ + ‖w - s‖ := norm_add_le _ _
        _ ≤ ‖s‖ + s.re / 2 := by linarith
    have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
      have h : 2 * k + 1 ≤ 2 * k + 2 := by omega
      exact_mod_cast h
    have hb := norm_cpow_neg_sub_le (s := w) (by linarith) ha hab
    have hdiff1 : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by
      have h : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 2 : ℕ) : ℝ) := by
        have h' : (2 * k + 1 : ℕ) + 1 = 2 * k + 2 := by omega
        rw [← h']
        push_cast
        ring
      linarith
    have hstep1 : ((2 * k + 1 : ℕ) : ℝ) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-w.re - 1) := by
      refine Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) ?_ ?_ ?_
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · have h : (k : ℝ) + 1 ≤ ((2 * k + 1 : ℕ) : ℝ) := by
          push_cast
          linarith [Nat.cast_nonneg (α := ℝ) k]
        exact h
    have hstep2 : ((k : ℝ) + 1) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re / 2 - 1) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hdiff1, mul_one] at hb
    refine hb.trans ?_
    exact mul_le_mul hnorm (hstep1.trans hstep2) (by positivity) (by positivity)
  have hall := differentiableOn_tsum_of_summable_norm
    (F := fun k : ℕ => fun t : ℂ =>
      ((2 * k + 1 : ℕ) : ℂ) ^ (-t) - ((2 * k + 2 : ℕ) : ℂ) ^ (-t))
    (U := Metric.ball s (s.re / 2)) hmaj hdiff Metric.isOpen_ball hle
  exact hall.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))

/-- `∑' n, n ^ (-s) = ζ s` in the half plane of absolute convergence. -/
private theorem tsum_nat_cpow_neg_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (n : ℂ) ^ (-s)) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr (fun n => ?_)
  rw [Complex.cpow_neg, one_div]

/-- The series `∑' n, n ^ (-s)` is summable for `1 < re s`. -/
private theorem summable_nat_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
  have hsne : -s ≠ 0 := by
    intro h
    have h0 : s = 0 := by linear_combination -h
    have hre : s.re = 0 := by rw [h0]; simp
    rw [hre] at hs
    linarith
  refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s.re))
    (Real.summable_nat_rpow.mpr (by linarith)) (fun n => ?_)
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp [Complex.zero_cpow, hsne, Real.zero_rpow (by linarith : -s.re ≠ 0)]
  · rw [← Complex.ofReal_natCast n,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero h)]
    simp

/-- The alternating ("eta") series equals `(1 - 2^(1-s)) * ζ s` for `1 < re s`. -/
private theorem pair_series_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hsne : -s ≠ 0 := by
    intro h
    have h0 : s = 0 := by linear_combination -h
    have hre : s.re = 0 := by rw [h0]; simp
    rw [hre] at hs
    linarith
  have hsum := summable_nat_cpow_neg (s := s) hs
  have hodd : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) :=
    hsum.comp_injective (i := fun k : ℕ => 2 * k + 1) (by
      intro a b hab
      simp only at hab
      omega)
  have heven : Summable (fun k : ℕ => ((2 * k : ℕ) : ℂ) ^ (-s)) :=
    hsum.comp_injective (i := fun k : ℕ => 2 * k) (by
      intro a b hab
      simp only at hab
      omega)
  have hshift : Summable (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) :=
    hsum.comp_injective (i := fun k : ℕ => 2 * k + 2) (by
      intro a b hab
      simp only at hab
      omega)
  have hz : ((0 : ℕ) : ℂ) ^ (-s) = 0 := by
    simp [Complex.zero_cpow, hsne]
  have hstep : (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s))
        - (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s)) := by
    rw [(hodd.hasSum.sub hshift.hasSum).tsum_eq]
    congr 1
    rw [heven.tsum_eq_zero_add, hz, zero_add]
    exact tsum_congr (fun k => by simp only [Nat.mul_succ])
  have hzetz : (∑' n : ℕ, (n : ℂ) ^ (-s)) = riemannZeta s :=
    tsum_nat_cpow_neg_eq_riemannZeta hs
  have hsplit : (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s))
      + (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) = riemannZeta s := by
    have hcomb := HasSum.even_add_odd (f := fun n : ℕ => (n : ℂ) ^ (-s))
      heven.hasSum hodd.hasSum
    rw [← hcomb.tsum_eq]
    exact hzetz
  have heven_eq : (∑' k : ℕ, ((2 * k : ℕ) : ℂ) ^ (-s))
      = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [← hzetz, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    have h := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := (k : ℝ)) (by norm_num)
      (Nat.cast_nonneg k) (-s)
    rw [show ((2 * k : ℕ) : ℂ) = (((2 : ℝ)) : ℂ) * (((k : ℝ)) : ℂ) by push_cast; ring,
      show (2 : ℂ) = (((2 : ℝ)) : ℂ) by norm_num,
      show ((k : ℕ) : ℂ) = (((k : ℝ)) : ℂ) from (Complex.ofReal_natCast k).symm]
    exact h
  have hpow : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    have h2 : (2 : ℂ) ^ (1 - s) = (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add (y := (1 : ℂ)) (z := -s) (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1
    rw [h2, Complex.cpow_one]
  have hA : (∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s))
      = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h := hsplit
    rw [heven_eq] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  rw [hstep, hA, heven_eq]
  rw [hpow.symm]
  ring

/-- The alternating series equals `(1 - 2^(1-s)) * ζ s` on the half plane `0 < re s`. -/
private theorem pair_series_eq_of_pos_re {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hpc : IsPreconnected {w : ℂ | 0 < w.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hG : AnalyticOnNhd ℂ
      (fun w : ℂ => (w - 1) * (∑' k : ℕ,
          (((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w)))
        - (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta₁ w) {w : ℂ | 0 < w.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hU
    exact DifferentiableOn.sub
      (DifferentiableOn.mul (fun w _ => (differentiableAt_id.sub
        (differentiableAt_const (c := (1 : ℂ)))).differentiableWithinAt)
        (fun w hw => (differentiableAt_pair_series w hw).differentiableWithinAt))
      (DifferentiableOn.mul (fun w _ =>
        ((differentiableAt_const (c := (1 : ℂ))).sub
          (((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).const_cpow
            (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))).differentiableWithinAt)
        differentiable_riemannZeta₁.differentiableOn)
  have hz0 : (fun w : ℂ => (w - 1) * (∑' k : ℕ,
          (((2 * k + 1 : ℕ) : ℂ) ^ (-w) - ((2 * k + 2 : ℕ) : ℂ) ^ (-w)))
        - (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta₁ w) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have haux : Continuous fun _ : ℂ => (1 : ℝ) := continuous_const
    have hset : {w : ℂ | 1 < w.re} = {w : ℂ | (fun _ : ℂ => (1 : ℝ)) w < w.re} := rfl
    have hopen : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) := by
      rw [hset]
      exact (isOpen_lt haux continuous_re).mem_nhds (by simp)
    filter_upwards [hopen] with w hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hw
      simp at hw
    rw [pair_series_eq_of_one_lt_re hw, riemannZeta_eq_inv_sub_mul hw1]
    simp only [Pi.zero_apply]
    field_simp
    ring
  have hres := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hG hpc
    (z₀ := (2 : ℂ)) (by simp) hz0 hs
  beta_reduce at hres
  simp only [Pi.zero_apply] at hres
  rw [riemannZeta_eq_inv_sub_mul hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hmul : (s - 1) * (∑' k : ℕ,
        (((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)))
      = (s - 1) * ((1 - (2 : ℂ) ^ (1 - s)) * ((s - 1)⁻¹ * riemannZeta₁ s)) := by
    have h := hres
    field_simp at h ⊢
    linear_combination h
  exact mul_left_cancel₀ hs1' hmul

/-- For real `σ > 0` each term of the alternating series is a positive real. -/
private theorem pair_term_pos {σ : ℝ} (h0 : 0 < σ) (k : ℕ) :
    ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) < ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) := by
  refine Real.rpow_lt_rpow_of_neg (by positivity : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ)) ?_
    (by linarith : -σ < 0)
  have h : 2 * k + 1 < 2 * k + 2 := by omega
  exact_mod_cast h

/-- The real alternating series is summable for `σ > 0`. -/
private theorem summable_pair_series_real {σ : ℝ} (h0 : 0 < σ) :
    Summable (fun k : ℕ =>
      (((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ))) := by
  have hmaj : Summable (fun k : ℕ => σ * (((k : ℝ) + 1) ^ (-σ - 1))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-σ - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-σ - 1)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine Summable.mul_left σ ?_
    exact hshift.congr (fun n => by norm_num)
  refine Summable.of_norm_bounded hmaj (fun k => ?_)
  have hab : ((2 * k + 1 : ℕ) : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
    have h : 2 * k + 1 ≤ 2 * k + 2 := by omega
    exact_mod_cast h
  have hcomplex := norm_cpow_neg_sub_le (s := (σ : ℂ))
    (by rw [Complex.ofReal_re]; linarith)
    (a := ((2 * k + 1 : ℕ) : ℝ)) (b := ((2 * k + 2 : ℕ) : ℝ)) (by positivity) hab
  have hkey : ‖(((2 * k + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - (((2 * k + 2 : ℕ) : ℂ) ^ (-(σ : ℂ))))‖
      = ((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ) := by
    rw [nat_cpow_neg_eq (n := 2 * k + 1) (σ := σ),
      nat_cpow_neg_eq (n := 2 * k + 2) (σ := σ), ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr (pair_term_pos h0 k))]
  simp only [Complex.ofReal_natCast] at hcomplex
  rw [hkey, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0,
    Complex.ofReal_re] at hcomplex
  have hdiff1 : ((2 * k + 2 : ℕ) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) = 1 := by
    have h : ((2 * k + 1 : ℕ) : ℝ) + 1 = ((2 * k + 2 : ℕ) : ℝ) := by
      have h' : (2 * k + 1 : ℕ) + 1 = 2 * k + 2 := by omega
      rw [← h']
      push_cast
      ring
    linarith
  rw [hdiff1, mul_one] at hcomplex
  have hmono : ((2 * k + 1 : ℕ) : ℝ) ^ (-σ - 1) ≤ ((k : ℝ) + 1) ^ (-σ - 1) := by
    refine Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) ?_ ?_ ?_
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · have h : (k : ℝ) + 1 ≤ ((2 * k + 1 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      exact h
  rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (pair_term_pos h0 k))]
  exact hcomplex.trans (mul_le_mul_of_nonneg_left hmono h0.le)

/-- The alternating series is positive at real arguments in `(0,1)`. -/
private theorem pair_series_pos_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (_h1 : σ < 1) :
    0 < (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ))) :=
  Summable.tsum_pos (summable_pair_series_real h0)
    (fun k => le_of_lt (sub_pos.mpr (pair_term_pos h0 k))) 0
    (sub_pos.mpr (pair_term_pos h0 0))

/-- At a real argument, the complex alternating series is the coercion of the real one. -/
private theorem pair_series_ofReal {σ : ℝ} :
    (∑' k : ℕ, (((2 * k + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((2 * k + 2 : ℕ) : ℂ) ^ (-(σ : ℂ))))
      = ((∑' k : ℕ,
          (((2 * k + 1 : ℕ) : ℝ) ^ (-σ) - ((2 * k + 2 : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun k => ?_)
  rw [nat_cpow_neg_eq (n := 2 * k + 1) (σ := σ), nat_cpow_neg_eq (n := 2 * k + 2) (σ := σ),
    ← Complex.ofReal_sub]

/-- **The Riemann zeta function has no real zero in `(0,1)`.** -/
private theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  have hcast := pair_series_ofReal (σ := σ)
  have hpos := pair_series_pos_of_mem_Ioo h0 h1
  have hne : (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) ≠ 0 := by
    have hgt : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith)
    have hbase : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    have hval : (2 : ℂ) ^ (1 - (σ : ℂ)) = (((2 : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
      have h2 : (1 : ℂ) - ((σ : ℂ)) = (((1 : ℝ) - σ : ℝ) : ℂ) := by push_cast; ring
      rw [hbase, h2, ← ofReal_rpow_cpow (x := (2 : ℝ)) (by norm_num) (1 - σ)]
    intro h
    rw [hval, sub_eq_zero] at h
    have hh : ((2 : ℝ) ^ (1 - σ) : ℝ) = 1 := by exact_mod_cast h.symm
    linarith
  have hid := pair_series_eq_of_pos_re (s := (σ : ℂ)) (by simpa using h0) (by
    intro h
    have hre : (σ : ℂ).re = 1 := by rw [h]; simp
    rw [show (σ : ℂ).re = σ from rfl] at hre
    linarith)
  have hEne : (∑' k : ℕ,
      (((2 * k + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((2 * k + 2 : ℕ) : ℂ) ^ (-(σ : ℂ)))) ≠ 0 := by
    rw [hcast]
    intro h
    exact (ne_of_gt hpos) (Complex.ofReal_eq_zero.mp h)
  intro hzero
  have hprod : (1 - (2 : ℂ) ^ (1 - (σ : ℂ))) * riemannZeta (σ : ℂ) ≠ 0 := by
    rw [← hid]
    exact hEne
  exact hprod (by rw [hzero, mul_zero])

end RZB481

/-- LEAF. The modulus one case of the real zero lower bound. For the trivial character, whose
L function is the Riemann zeta function, a zero at `1 - δ` with `0 < δ < 1 / 2` costs at least a
fixed positive multiple of `1 ^ (-(1 / 2))`, uniformly in the character of modulus one. -/
theorem leaf_real_zero_modulus_one481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → r ≤ 1 → ∀ χ : DirichletCharacter ℂ r,
      (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  refine ⟨1, one_pos, ?_⟩
  intro r hr hr1 χ _ δ hδ hδ2 hzero
  have hr1' : r = 1 := le_antisymm hr1 hr
  subst hr1'
  have hL : Lfun481 χ (1 - (δ : ℂ)) = riemannZeta (1 - (δ : ℂ)) := by
    simp [Lfun481]
  rw [hL] at hzero
  have hne := RZB481.riemannZeta_ne_zero_of_mem_Ioo (σ := 1 - δ) (by linarith) (by linarith)
  rw [show (((1 : ℝ) - δ : ℝ) : ℂ) = 1 - (δ : ℂ) by push_cast; ring] at hne
  exact absurd hzero hne

/-- LEAF. The quadratic case of the real zero lower bound. For a real primitive character of
modulus at least two, a zero at `1 - δ` with `0 < δ < 1 / 2` costs at least a fixed positive
multiple of `r ^ (-(1 / 2))`. The constant is uniform over the modulus and the character. -/
theorem leaf_real_zero_primitive_large481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → 2 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  sorry

/-- LEAF. The imprimitive case of the real zero lower bound. For a real character that is not
primitive, a zero of its L function at `1 - δ` with `0 < δ < 1 / 2` costs at least a fixed
positive multiple of `r ^ (-(1 / 2))`. No restriction to zeros induced from a primitive
character is made here, since the Euler factors at the ramified primes do not remove them all. -/
theorem leaf_real_zero_imprimitive481 :
    ∃ a : ℝ, 0 < a ∧ ∀ r : ℕ, 1 ≤ r → ∀ χ : DirichletCharacter ℂ r,
      ¬ χ.IsPrimitive → (∀ b, (χ b).im = 0) → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        Lfun481 χ (1 - (δ : ℂ)) = 0 → a * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ δ := by
  sorry

/-- The real zero lower bound from its three cases and the elementary step for large `δ`. -/
theorem real_zero_bound481_split : RealZeroStatement481 := by
  classical
  obtain ⟨a₁, ha₁pos, ha₁⟩ := leaf_real_zero_modulus_one481
  obtain ⟨a₂, ha₂pos, ha₂⟩ := leaf_real_zero_primitive_large481
  obtain ⟨a₃, ha₃pos, ha₃⟩ := leaf_real_zero_imprimitive481
  refine ⟨min (1 / 4) (min a₁ (min a₂ a₃)), ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min ha₁pos (lt_min ha₂pos ha₃pos))
  · intro r hr χ hreal δ hδ hzero
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
    have hrpow : (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
    have hpowpos : (0 : ℝ) ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hrpos _)
    have hA1 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ a₁ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hA2 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ a₂ :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hA3 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ a₃ :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hA0 : min (1 / 4) (min a₁ (min a₂ a₃)) ≤ 1 / 4 := min_le_left _ _
    by_cases hbig : (1 / 2 : ℝ) ≤ δ
    · have hmul : min (1 / 4) (min a₁ (min a₂ a₃)) * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / 4 := by
        have hstep : min (1 / 4) (min a₁ (min a₂ a₃)) * (r : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (1 / 4) * 1 :=
          mul_le_mul hA0 hrpow hpowpos (by norm_num)
        linarith
      linarith
    · have hsmall : δ < 1 / 2 := lt_of_not_ge hbig
      by_cases hrle : r ≤ 1
      · have h1 := ha₁ r hr hrle χ hreal δ hδ hsmall hzero
        exact le_trans (mul_le_mul_of_nonneg_right hA1 hpowpos) h1
      · have hr2 : 2 ≤ r := by omega
        by_cases hprim : χ.IsPrimitive
        · have h2 := ha₂ r hr hr2 χ hprim hreal δ hδ hsmall hzero
          exact le_trans (mul_le_mul_of_nonneg_right hA2 hpowpos) h2
        · have h3 := ha₃ r hr χ hprim hreal δ hδ hsmall hzero
          exact le_trans (mul_le_mul_of_nonneg_right hA3 hpowpos) h3

end

end LeanLab.LPZ2007
