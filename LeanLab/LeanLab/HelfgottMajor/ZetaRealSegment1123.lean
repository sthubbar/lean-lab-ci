import LeanLab.HelfgottMajor.ZetaFirstZero1123
import Mathlib

/-!
# Zeta has no zero on the real segment from 0 to 1, burst-20261122, session S116

Piece of the quarter LEAF `ZetaFirstZero1123.zeta_first_zero_quadrant`, book Part I page 86.
The classical argument: for Re s above 0 the alternating series
sum over k of (2k+1)^(-s) - (2k+2)^(-s) converges locally uniformly, so it is analytic there,
it equals (1 - 2 * 2^(-s)) zeta of s for Re s above 1, hence on the star shaped domain
Re s above 0 minus the ray [1, infinity) by the identity theorem, and at a real s in (0, 1)
every term is a positive real. So zeta of s is not 0 there.
The quarter LEAF is then reduced to the open quarter with Im s above 0.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZetaRealSegment1123
open Complex Set Filter Topology
open scoped ComplexConjugate

/-- One difference of the alternating series, bounded by the mean value theorem:
for x at least 1 and Re s above 0, the norm of x^(-s) - (x+1)^(-s) is at most
the norm of s times x^(-Re s - 1). -/
theorem cpow_neg_sub_le {s : ℂ} {x : ℝ} (hx : 1 ≤ x) (hs : 0 < s.re) :
    ‖((x + 1 : ℝ) : ℂ) ^ (-s) - ((x : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  have hx0 : 0 < x := by linarith
  have hd : ∀ y ∈ Icc x (x + 1), HasDerivWithinAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (-s))
      (-s * ((y : ℝ) : ℂ) ^ (-s - 1)) (Icc x (x + 1)) y := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hslit : ((y : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hy0
    exact ((Complex.hasStrictDerivAt_cpow_const (c := -s) hslit).hasDerivAt.comp_ofReal
      ).hasDerivWithinAt
  have hb : ∀ y ∈ Ico x (x + 1), ‖-s * ((y : ℝ) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos hx0 hy.1 (by linarith)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (x + 1)
    ⟨by linarith, le_rfl⟩
  simpa using this

/-- The k-th term of the alternating series, as `(2k+1)^(-s) - (2k+2)^(-s)` in the shape
`f (2k) - f (2k+1)` with `f n = (n+1)^(-s)`. -/
lemma term_eq (s : ℂ) (k : ℕ) :
    (((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s) =
      -((((2 * k + 1 : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((2 * k + 1 : ℝ) : ℝ) : ℂ) ^ (-s)) := by
  push_cast
  ring_nf

/-- Bound on the k-th term, summable in k for Re s above 0. -/
theorem term_norm_le {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖(((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ * ((k : ℝ) + 1) ^ (-s.re - 1) := by
  rw [term_eq, norm_neg]
  have h1 : (1 : ℝ) ≤ 2 * k + 1 := by have := k.cast_nonneg (α := ℝ); linarith
  refine (cpow_neg_sub_le h1 hs).trans ?_
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  have := k.cast_nonneg (α := ℝ); linarith

lemma summable_shift_rpow {p : ℝ} (hp : p < -1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa using h

/-- The alternating series is differentiable on the half plane Re s above 0. -/
theorem differentiableOn_eta :
    DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s)))
      {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  set δ := s.re / 2 with hδ
  set R := ‖s‖ + 1 with hR
  let U : Set ℂ := {w | δ < w.re} ∩ {w | ‖w‖ < R}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := ⟨show δ < s.re by rw [hδ]; linarith, show ‖s‖ < R by rw [hR]; linarith⟩
  have hdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_shift_rpow (p := -δ - 1) (by linarith)).mul_left R) ?_ hU ?_
    · intro k w _
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub
      · exact (differentiableAt_id.neg).const_cpow (Or.inl (Nat.cast_add_one_ne_zero _))
      · exact (differentiableAt_id.neg).const_cpow (Or.inl (Nat.cast_add_one_ne_zero _))
    · intro k w hw
      have hw1 : δ < w.re := hw.1
      have hw2 : ‖w‖ < R := hw.2
      refine (term_norm_le (by linarith) k).trans ?_
      have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := k.cast_nonneg (α := ℝ); linarith
      have hpow : ((k : ℝ) + 1) ^ (-w.re - 1) ≤ ((k : ℝ) + 1) ^ (-δ - 1) :=
        Real.rpow_le_rpow_of_exponent_le hk (by linarith)
      exact mul_le_mul hw2.le hpow (by positivity) (by linarith [norm_nonneg s])
  exact (hdiff.differentiableAt (hU.mem_nhds hsU)).differentiableWithinAt

/-- For Re s above 1 the alternating series is (1 - 2 * 2^(-s)) zeta of s. -/
theorem eta_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, ((((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))) =
      (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (-s) with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ = ((n : ℝ) + 1) ^ (-s.re) := by
    intro n
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hf]; dsimp only; rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
  have hsum : Summable f := by
    refine Summable.of_norm ?_
    simp_rw [hnorm]
    exact summable_shift_rpow (by linarith)
  have he : Summable (fun k => f (2 * k)) :=
    hsum.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable (fun k => f (2 * k + 1)) :=
    hsum.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hz : riemannZeta s = ∑' n, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    congr 1; ext n
    rw [hf]; dsimp only; rw [cpow_neg, one_div]
  have hodd : (∑' k, f (2 * k + 1)) = (2 : ℂ) ^ (-s) * ∑' n, f n := by
    rw [← tsum_mul_left]
    congr 1; ext k
    rw [hf]; dsimp only
    have h2 : ((((2 * k + 1 : ℕ) : ℂ)) + 1) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h2, mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast
    ring_nf
  have hsplit := tsum_even_add_odd he ho
  have hterm : (∑' k : ℕ, ((((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))) =
      (∑' k, f (2 * k)) - ∑' k, f (2 * k + 1) := by
    rw [← he.tsum_sub ho]
  rw [hterm, hz]
  have : (∑' k, f (2 * k)) = (∑' n, f n) - ∑' k, f (2 * k + 1) := by
    rw [← hsplit]; ring
  rw [this, hodd]
  ring

/-- The domain Re s above 0 minus the ray from 1 to the right. -/
lemma starConvex_dom :
    StarConvex ℝ (1 / 2 : ℂ) ({s : ℂ | 0 < s.re} \ {s : ℂ | 1 ≤ s.re ∧ s.im = 0}) := by
  intro y hy a b ha hb hab
  obtain ⟨hy1, hy2⟩ := hy
  have hy1' : 0 < y.re := hy1
  simp only [Set.mem_ofPred_eq, not_and] at hy2
  refine ⟨?_, ?_⟩
  · show 0 < (a • (1 / 2 : ℂ) + b • y).re
    simp only [Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]
    norm_num
    rcases eq_or_lt_of_le hb with h | h
    · rw [← h]; simp; linarith
    · nlinarith
  · simp only [Set.mem_ofPred_eq, not_and]
    intro h1 h2
    simp only [Complex.add_im, Complex.real_smul, Complex.im_ofReal_mul, Complex.add_re,
      Complex.re_ofReal_mul] at h1 h2
    norm_num at h1 h2
    rcases eq_or_lt_of_le hb with h | h
    · rw [← h] at h1; simp at h1; linarith
    · have hyim : y.im = 0 := by
        rcases h2 with h' | h'
        · linarith
        · exact h'
      by_cases hr : 1 ≤ y.re
      · exact absurd hyim (hy2 hr)
      · push Not at hr
        nlinarith

/-- Zeta has no zero at a real point of the open interval from 0 to 1. PROVED, no input. -/
theorem zeta_ne_zero_of_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : riemannZeta σ ≠ 0 := by
  set D : Set ℂ := {s : ℂ | 0 < s.re} \ {s : ℂ | 1 ≤ s.re ∧ s.im = 0} with hD
  have hDo : IsOpen D := by
    refine (isOpen_lt continuous_const Complex.continuous_re).sdiff ?_
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_eq Complex.continuous_im continuous_const)
  have hDc : IsPreconnected D :=
    (starConvex_dom.isPathConnected (by simp; norm_num)).isConnected.isPreconnected
  have h1D : ∀ s ∈ D, s ≠ 1 := by
    intro s hs h; apply hs.2; rw [h]; simp
  have hG : AnalyticOnNhd ℂ (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) D := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hDo
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · apply DifferentiableAt.sub (differentiableAt_const _)
      exact (differentiableAt_id.neg.const_cpow (Or.inl two_ne_zero)).const_mul _
    · exact differentiableAt_riemannZeta (h1D s hs)
  have hE : AnalyticOnNhd ℂ (fun s : ℂ => ∑' k : ℕ,
      ((((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))) D :=
    (differentiableOn_eta.mono sdiff_subset).analyticOnNhd hDo
  have hz0 : (2 + I : ℂ) ∈ D := by
    refine ⟨by simp, ?_⟩
    simp
  have heq : EqOn (fun s : ℂ => ∑' k : ℕ,
      ((((2 * k : ℕ) : ℂ) + 1) ^ (-s) - (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s)))
      (fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * riemannZeta s) D := by
    refine hE.eqOn_of_preconnected_of_eventuallyEq hG hDc hz0 ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 + I : ℂ).re by simp)] with z hz
    exact eta_eq_of_one_lt hz
  have hσD : (σ : ℂ) ∈ D := by
    refine ⟨by simpa using h0, ?_⟩
    simp only [Set.mem_ofPred_eq, ofReal_re, not_and]
    intro h; linarith
  intro hz
  have hval := heq hσD
  simp only [hz, mul_zero] at hval
  -- every term is a positive real
  have hterm : ∀ k : ℕ, (((2 * k : ℕ) : ℂ) + 1) ^ (-(σ : ℂ)) -
      (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-(σ : ℂ)) =
      (((2 * k + 1 : ℝ) ^ (-σ) - (2 * k + 2 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro k
    have ha : (((2 * k : ℕ) : ℂ) + 1) = (((2 * k + 1 : ℝ)) : ℂ) := by push_cast; ring
    have hb : (((2 * k + 1 : ℕ) : ℂ) + 1) = (((2 * k + 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [ha, hb, ← ofReal_neg, ← ofReal_cpow (by positivity), ← ofReal_cpow (by positivity)]
    push_cast
    ring
  have hpos : ∀ k : ℕ, 0 < (2 * k + 1 : ℝ) ^ (-σ) - (2 * k + 2 : ℝ) ^ (-σ) := by
    intro k
    have : (2 * k + 2 : ℝ) ^ (-σ) < (2 * k + 1 : ℝ) ^ (-σ) :=
      Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
    linarith
  have hsr : Summable (fun k : ℕ => (2 * k + 1 : ℝ) ^ (-σ) - (2 * k + 2 : ℝ) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun k => (hpos k).le) (fun k => ?_)
      ((summable_shift_rpow (p := -σ - 1) (by linarith)).mul_left ‖(σ : ℂ)‖)
    have h := term_norm_le (s := (σ : ℂ)) (by simpa using h0) k
    rw [hterm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos k)] at h
    simpa using h
  simp_rw [hterm] at hval
  rw [← ofReal_tsum] at hval
  have := hsr.tsum_pos (fun k => (hpos k).le) 0 (hpos 0)
  have h0' := ofReal_eq_zero.mp hval
  linarith

/-- LEAF: book Part I, section 3.7.3.3, page 86, the first non-trivial zero of zeta has
imaginary part 14.13472..., cited to Gra03 and Edw74 section 6.1, on the OPEN quarter
1/2 at most Re s below 1 and Im s above 0. With `zeta_ne_zero_of_real` and the two symmetries
of `ZetaFirstZero1123` it gives the whole leaf `BookZeroSplit1122.zeta_first_zero`.
Stated with the weaker constant 14.13. Class MEDIUM: a finite certified computation of zeta
on a rectangle of height 14.13. -/
theorem zeta_first_zero_open_quadrant {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 ≤ ρ.re)
    (h1 : ρ.re < 1) (him : 0 < ρ.im) : (14.13 : ℝ) < ρ.im := by
  sorry

/-- The quarter LEAF of `ZetaFirstZero1123`, PROVED from the open quarter LEAF and the real
segment `zeta_ne_zero_of_real`. CONDITIONAL ON `zeta_first_zero_open_quadrant`. -/
theorem zeta_first_zero_quadrant_split {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 ≤ ρ.re)
    (h1 : ρ.re < 1) (him : 0 ≤ ρ.im) : (14.13 : ℝ) < ρ.im := by
  rcases eq_or_lt_of_le him with h | h
  · exfalso
    have hρ : ρ = (ρ.re : ℂ) := by
      apply Complex.ext <;> simp [← h]
    rw [hρ] at hz
    exact zeta_ne_zero_of_real (by linarith) h1 hz
  · exact zeta_first_zero_open_quadrant hz h0 h1 h

example : type_of% @zeta_first_zero_quadrant_split =
    type_of% @ZetaFirstZero1123.zeta_first_zero_quadrant := rfl

/-- Exactly the statement of `BookZeroSplit1122.zeta_first_zero`, PROVED from
`zeta_first_zero_open_quadrant` by the real segment and the proved symmetries
`ZetaFirstZero1123.zeta_zero_conj` and `ZetaFirstZero1123.zeta_zero_one_sub`.
CONDITIONAL ON `zeta_first_zero_open_quadrant` alone. -/
theorem zeta_first_zero_honest {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : (14.13 : ℝ) < |ρ.im| := by
  have right : ∀ {w : ℂ}, riemannZeta w = 0 → 1 / 2 ≤ w.re → w.re < 1 → (14.13 : ℝ) < |w.im| := by
    intro w hw hw0 hw1
    rcases le_or_gt 0 w.im with h | h
    · rw [abs_of_nonneg h]
      exact zeta_first_zero_quadrant_split hw hw0 hw1 h
    · have hc := zeta_first_zero_quadrant_split (ZetaFirstZero1123.zeta_zero_conj hw)
        (by rwa [conj_re]) (by rwa [conj_re]) (by rw [conj_im]; linarith)
      rw [conj_im] at hc
      rw [abs_of_neg h]
      exact hc
  rcases le_or_gt (1 / 2) ρ.re with h | h
  · exact right hz h h1
  · have hr := right (ZetaFirstZero1123.zeta_zero_one_sub hz h0 h1)
      (by rw [sub_re, one_re]; linarith) (by rw [sub_re, one_re]; linarith)
    rw [sub_im, one_im, zero_sub, abs_neg] at hr
    exact hr

example : type_of% @zeta_first_zero_honest = type_of% @BookZeroSplit1122.zeta_first_zero := rfl

end LeanLab.HelfgottMajor.ZetaRealSegment1123
