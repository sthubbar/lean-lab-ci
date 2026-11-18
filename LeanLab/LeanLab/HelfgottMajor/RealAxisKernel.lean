import LeanLab.HelfgottMajor.StripBound123

/-!
# A kernel criterion for the nonvanishing of `L(σ, χ)` on the positive real axis

What is proved: for a non principal Dirichlet character `χ` modulo `q` and a complex number `c`,
if the real part of `c * P(x)`, with `P(x) = ∑_{a < q} χ(a) x^a`, is nonnegative on the open unit
interval and positive at one point of it, then `L(σ, χ) ≠ 0` for every real `σ > 0`.

Method: the Mellin transform representation
`Γ(σ) L(σ, χ) = ∫_0^∞ t^(σ-1) (∑_{n ≥ 1} χ(n) e^(-nt)) dt` together with
`∑_{n ≥ 1} χ(n) x^n = P(x) / (1 - x^q)`. Here it is run through the partial summation formula
`LFunction_eq_tsum` of `StripBound123`, valid on `Re s > 0`, so that every exchange of sum and
integral is absolutely convergent.

This is standard mathematics; see Davenport, Multiplicative Number Theory, chapters 1 and 9, or
Washington, Introduction to Cyclotomic Fields, chapter 4. Nothing here is new.

AI wrote this Lean code. The binary Goldbach conjecture is open; this file does not touch it.
-/

namespace LeanLab.HelfgottMajor.RealAxisKernel

open MeasureTheory Set Filter Topology
open LeanLab.HelfgottMajor.StripBound123

/-- The differences `(n+1)^(-σ) - (n+2)^(-σ)` are nonnegative for `σ > 0`. -/
private lemma rpow_diff_nonneg {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ) := by
  apply sub_nonneg.2
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)

/-- The telescoping series of `(n+1)^(-σ) - (n+2)^(-σ)` is summable for `σ > 0`. -/
private lemma summable_rpow_diff {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ)) := by
  refine summable_of_sum_range_le (c := 1) (rpow_diff_nonneg hσ) (fun N => ?_)
  have h := Finset.sum_range_sub' (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ (-σ)) N
  have e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) ^ (-σ) - ((i + 2 : ℕ) : ℝ) ^ (-σ)) =
      ((0 + 1 : ℕ) : ℝ) ^ (-σ) - ((N + 1 : ℕ) : ℝ) ^ (-σ) := h
  rw [e]
  have h2 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ (-σ) := by positivity
  simp only [zero_add, Nat.cast_one, Real.one_rpow]
  linarith

/-- Real Mellin transform core. If `a` is a bounded real sequence and, for every `t > 0`, the
series of `a n (e^(-(n+1)t) - e^(-(n+2)t))` has sum `G t`, with `G` continuous and nonnegative on
`(0, ∞)` and positive at one point, then the series of `a n ((n+1)^(-σ) - (n+2)^(-σ))` has a
positive sum, for every `σ > 0`. -/
private lemma mellin_pos {a : ℕ → ℝ} {M : ℝ} (ha : ∀ n, |a n| ≤ M) {σ : ℝ} (hσ : 0 < σ)
    {G : ℝ → ℝ}
    (hG : ∀ t : ℝ, 0 < t → HasSum
      (fun n : ℕ => a n * (Real.exp (-t) ^ (n + 1) - Real.exp (-t) ^ (n + 2))) (G t))
    (hGc : ContinuousOn G (Ioi 0)) (hG0 : ∀ t : ℝ, 0 < t → 0 ≤ G t)
    (hGp : ∃ t : ℝ, 0 < t ∧ 0 < G t) :
    0 < ∑' n : ℕ, a n * (((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ)) := by
  have hΓ := Real.Gamma_pos_of_pos hσ
  -- the basic integrals
  have hI : ∀ m : ℕ, 0 < m →
      IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-t) ^ m) (Ioi 0) := by
    intro m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := (m : ℝ))
      (by linarith) one_pos hm'
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hV : ∀ m : ℕ, 0 < m →
      ∫ t in Ioi 0, t ^ (σ - 1) * Real.exp (-t) ^ m = ((m : ℕ) : ℝ) ^ (-σ) * Real.Gamma σ := by
    intro m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hm'
    rw [one_div, Real.inv_rpow hm'.le, ← Real.rpow_neg hm'.le] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hw : ∀ (n : ℕ) (t : ℝ), 0 < t →
      0 ≤ t ^ (σ - 1) * Real.exp (-t) ^ (n + 1) - t ^ (σ - 1) * Real.exp (-t) ^ (n + 2) := by
    intro n t ht
    rw [← mul_sub]
    refine mul_nonneg (Real.rpow_nonneg ht.le _) (sub_nonneg.2 ?_)
    exact pow_le_pow_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by linarith))
      (by omega)
  have hFint : ∀ n : ℕ, Integrable (fun t : ℝ => a n * (t ^ (σ - 1) * Real.exp (-t) ^ (n + 1) -
      t ^ (σ - 1) * Real.exp (-t) ^ (n + 2))) (volume.restrict (Ioi 0)) := fun n =>
    ((hI (n + 1) (by omega)).sub (hI (n + 2) (by omega))).const_mul (a n)
  have hval : ∀ (b : ℝ) (n : ℕ), ∫ t in Ioi 0, b * (t ^ (σ - 1) * Real.exp (-t) ^ (n + 1) -
      t ^ (σ - 1) * Real.exp (-t) ^ (n + 2)) =
      b * (Real.Gamma σ * (((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ))) := by
    intro b n
    rw [integral_const_mul, integral_sub (hI (n + 1) (by omega)) (hI (n + 2) (by omega)),
      hV (n + 1) (by omega), hV (n + 2) (by omega)]
    ring
  have hnorm : ∀ n : ℕ, ∫ t in Ioi 0, ‖a n * (t ^ (σ - 1) * Real.exp (-t) ^ (n + 1) -
      t ^ (σ - 1) * Real.exp (-t) ^ (n + 2))‖ ≤
      M * (Real.Gamma σ * (((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ))) := by
    intro n
    rw [← hval M n]
    refine setIntegral_mono_on (hFint n).norm
      (((hI (n + 1) (by omega)).sub (hI (n + 2) (by omega))).const_mul M) measurableSet_Ioi
      (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n t ht)]
    exact mul_le_mul_of_nonneg_right (ha n) (hw n t ht)
  have hsum : Summable (fun n : ℕ => ∫ t in Ioi 0, ‖a n * (t ^ (σ - 1) * Real.exp (-t) ^ (n + 1) -
      t ^ (σ - 1) * Real.exp (-t) ^ (n + 2))‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) hnorm
      (((summable_rpow_diff hσ).mul_left (Real.Gamma σ)).mul_left M)
  have hex := integral_tsum_of_summable_integral_norm hFint hsum
  have hEq : ∫ t in Ioi 0, ∑' n : ℕ, a n * (t ^ (σ - 1) * Real.exp (-t) ^ (n + 1) -
      t ^ (σ - 1) * Real.exp (-t) ^ (n + 2)) = ∫ t in Ioi 0, t ^ (σ - 1) * G t := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have h := ((hG t ht).mul_left (t ^ (σ - 1))).tsum_eq
    rw [← h]
    congr 1
    funext n
    ring
  have hS : Real.Gamma σ * ∑' n : ℕ, a n * (((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ)) =
      ∫ t in Ioi 0, t ^ (σ - 1) * G t := by
    rw [← hEq, ← hex, ← tsum_mul_left]
    congr 1
    funext n
    rw [hval (a n) n]
    ring
  -- the bound on G
  have hbound : ∀ t : ℝ, 0 < t → |G t| ≤ M * Real.exp (-t) := by
    intro t ht
    have hx0 : 0 < Real.exp (-t) := Real.exp_pos _
    have hx1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hne : 1 - Real.exp (-t) ≠ 0 := by linarith
    have hg : HasSum (fun n : ℕ => M * (Real.exp (-t) ^ (n + 1) - Real.exp (-t) ^ (n + 2)))
        (M * Real.exp (-t)) := by
      have h := (hasSum_geometric_of_lt_one hx0.le hx1).mul_left
        (M * Real.exp (-t) * (1 - Real.exp (-t)))
      rw [mul_assoc (M * Real.exp (-t)), mul_inv_cancel₀ hne, mul_one] at h
      convert h using 1
      funext n
      ring
    have h := tsum_of_norm_bounded hg
      (f := fun n : ℕ => a n * (Real.exp (-t) ^ (n + 1) - Real.exp (-t) ^ (n + 2))) (fun n => by
        have hwn : 0 ≤ Real.exp (-t) ^ (n + 1) - Real.exp (-t) ^ (n + 2) :=
          sub_nonneg.2 (pow_le_pow_of_le_one hx0.le hx1.le (by omega))
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwn]
        exact mul_le_mul_of_nonneg_right (ha n) hwn)
    rw [(hG t ht).tsum_eq, Real.norm_eq_abs] at h
    exact h
  have hKc : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * G t) (Ioi 0) :=
    (continuousOn_id.rpow_const (fun t ht => Or.inl (show (0 : ℝ) < t from ht).ne')).mul hGc
  have hKint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * G t) (Ioi 0) := by
    have hdom : IntegrableOn (fun t : ℝ => M * (t ^ (σ - 1) * Real.exp (-t) ^ 1)) (Ioi 0) :=
      (hI 1 one_pos).const_mul M
    refine Integrable.mono' hdom (hKc.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have h1 := hbound t ht
    have h2 : 0 ≤ t ^ (σ - 1) := Real.rpow_nonneg (le_of_lt ht) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, pow_one]
    calc t ^ (σ - 1) * |G t| ≤ t ^ (σ - 1) * (M * Real.exp (-t)) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = M * (t ^ (σ - 1) * Real.exp (-t)) := by ring
  obtain ⟨t0, ht0, hGt0⟩ := hGp
  have hpos : 0 < ∫ t in Ioi 0, t ^ (σ - 1) * G t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ hKint]
    · have hat : ContinuousAt (fun t : ℝ => t ^ (σ - 1) * G t) t0 :=
        hKc.continuousAt (Ioi_mem_nhds ht0)
      have hev : ∀ᶠ t in 𝓝 t0, 0 < t ^ (σ - 1) * G t :=
        Filter.Tendsto.eventually hat
          (lt_mem_nhds (mul_pos (Real.rpow_pos_of_pos ht0 _) hGt0))
      have hmem : (Function.support (fun t : ℝ => t ^ (σ - 1) * G t) ∩ Ioi 0) ∈ 𝓝 t0 := by
        filter_upwards [hev, Ioi_mem_nhds ht0] with t h1 h2
        exact ⟨Function.mem_support.2 h1.ne', h2⟩
      exact Measure.measure_pos_of_mem_nhds volume hmem
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (hG0 t ht))
  rw [← hS] at hpos
  exact (mul_pos_iff_of_pos_left hΓ).1 hpos

section character
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
/-- Finite summation by parts for the power weights `z^(n+1) - z^(n+2)`. -/
private lemma abel_pow (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
        (z ^ (n + 1) - z ^ (n + 2)) =
      ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) * z ^ (n + 1) -
        (∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q)) * z ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, partialSum_succ χ N]
    ring

/-- A non principal character has modulus different from 1 and vanishes at 0. -/
private lemma chi_zero (hχ : χ ≠ 1) : χ (0 : ZMod q) = 0 := by
  have hq1 : q ≠ 1 := by
    intro h
    subst h
    exact hχ (Subsingleton.elim _ _)
  have : Fact (1 < q) := ⟨by have := NeZero.ne q; omega⟩
  exact MulChar.map_zero χ

/-- The generating function of the partial sums, in partial summation form: for `0 < x < 1`,
the series of `A(n+1) (x^(n+1) - x^(n+2))`, with `A` the partial sums of `χ`, has sum
`P(x) / (1 - x^q)`, `P(x) = ∑_{a < q} χ(a) x^a`. This is `∑_{n ≥ 1} χ(n) x^n` after summation by
parts. -/
private lemma hasSum_kernel (hχ : χ ≠ 1) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
        ((x : ℂ) ^ (n + 1) - (x : ℂ) ^ (n + 2)))
      ((∑ a ∈ Finset.range q, χ (a : ZMod q) * (x : ℂ) ^ a) / (1 - (x : ℂ) ^ q)) := by
  have hz : ‖(x : ℂ)‖ = x := Complex.norm_of_nonneg hx0.le
  have hsum : Summable (fun n : ℕ => (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      ((x : ℂ) ^ (n + 1) - (x : ℂ) ^ (n + 2))) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => (q : ℝ) * (x * ‖1 - (x : ℂ)‖) * x ^ n)
      ((summable_geometric_of_lt_one hx0.le hx1).mul_left _) (fun n => ?_)
    have e : (x : ℂ) ^ (n + 1) - (x : ℂ) ^ (n + 2) = (x : ℂ) * (1 - (x : ℂ)) * (x : ℂ) ^ n := by
      ring
    rw [e, norm_mul, norm_mul, norm_mul, norm_pow, hz, mul_assoc]
    exact (mul_le_mul_of_nonneg_right (norm_partialSum_le_modulus χ hχ _)
      (by positivity)).trans_eq (by ring)
  have hshift : ∀ n : ℕ, (∑ m ∈ Finset.Icc 1 (n + q + 1), χ (m : ZMod q)) *
      ((x : ℂ) ^ (n + q + 1) - (x : ℂ) ^ (n + q + 2)) =
      (x : ℂ) ^ q * ((∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      ((x : ℂ) ^ (n + 1) - (x : ℂ) ^ (n + 2))) := by
    intro n
    rw [show n + q + 1 = n + 1 + q by ring, partialSum_add_period χ hχ (n + 1)]
    ring
  have hsplit := hsum.sum_add_tsum_nat_add q
  rw [tsum_congr hshift, tsum_mul_left] at hsplit
  have hAq : ∑ m ∈ Finset.Icc 1 q, χ (m : ZMod q) = 0 := by
    have h := partialSum_add_period χ hχ 0
    simpa using h
  have hfin : ∑ n ∈ Finset.range q, (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      ((x : ℂ) ^ (n + 1) - (x : ℂ) ^ (n + 2)) =
      ∑ a ∈ Finset.range q, χ (a : ZMod q) * (x : ℂ) ^ a := by
    rw [abel_pow χ (x : ℂ) q, hAq, zero_mul, sub_zero]
    have h1 := Finset.sum_range_succ' (fun a : ℕ => χ (a : ZMod q) * (x : ℂ) ^ a) q
    have h2 := Finset.sum_range_succ (fun a : ℕ => χ (a : ZMod q) * (x : ℂ) ^ a) q
    rw [h2] at h1
    simp only [Nat.cast_zero, ZMod.natCast_self, chi_zero χ hχ, zero_mul, add_zero] at h1
    exact h1.symm
  rw [hfin] at hsplit
  have hne : (1 : ℂ) - (x : ℂ) ^ q ≠ 0 := by
    intro h
    have h' : (x : ℂ) ^ q = 1 := by linear_combination -h
    have h'' : x ^ q = 1 := by exact_mod_cast h'
    have := pow_lt_one₀ hx0.le hx1 (NeZero.ne q)
    linarith
  have hval : ∑' n : ℕ, (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      ((x : ℂ) ^ (n + 1) - (x : ℂ) ^ (n + 2)) =
      (∑ a ∈ Finset.range q, χ (a : ZMod q) * (x : ℂ) ^ a) / (1 - (x : ℂ) ^ q) := by
    rw [eq_div_iff hne]
    linear_combination (-1 : ℂ) * hsplit
  rw [← hval]
  exact hsum.hasSum

end character

/-- Kernel criterion. Let `χ` be a non principal character modulo `q` and `c` a complex number.
If the real part of `c * ∑_{a < q} χ(a) x^a` is nonnegative on the open unit interval and is
positive at one point of it, then `L(σ, χ) ≠ 0` for every real `σ > 0`. -/
theorem LFunction_ofReal_ne_zero_of_kernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (c : ℂ)
    (hnn : ∀ x : ℝ, 0 < x → x < 1 →
      0 ≤ (c * ∑ a ∈ Finset.range q, χ (a : ZMod q) * (x : ℂ) ^ a).re)
    (hpos : ∃ x : ℝ, 0 < x ∧ x < 1 ∧
      0 < (c * ∑ a ∈ Finset.range q, χ (a : ZMod q) * (x : ℂ) ^ a).re)
    {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  obtain ⟨x0, hx0, hx1, hxp⟩ := hpos
  have hAb : ∀ n : ℕ, ‖c * ∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)‖ ≤ ‖c‖ * q := fun n => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_partialSum_le_modulus χ hχ _) (norm_nonneg _)
  have ha : ∀ n : ℕ, |(c * ∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)).re| ≤ ‖c‖ * q :=
    fun n => (Complex.abs_re_le_norm _).trans (hAb n)
  have hpow : ∀ t : ℝ, 0 < t → Real.exp (-t) ^ q < 1 := fun t ht =>
    pow_lt_one₀ (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith)) (NeZero.ne q)
  have hG : ∀ t : ℝ, 0 < t → HasSum
      (fun n : ℕ => (c * ∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)).re *
        (Real.exp (-t) ^ (n + 1) - Real.exp (-t) ^ (n + 2)))
      ((fun t : ℝ => (c * ∑ a ∈ Finset.range q, χ (a : ZMod q) *
        ((Real.exp (-t) : ℝ) : ℂ) ^ a).re / (1 - Real.exp (-t) ^ q)) t) := by
    intro t ht
    have h := ((Complex.hasSum_iff _ _).1 ((hasSum_kernel χ hχ (Real.exp_pos (-t))
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left c)).1
    convert h using 1
    · funext n
      rw [show ((Real.exp (-t) : ℝ) : ℂ) ^ (n + 1) - ((Real.exp (-t) : ℝ) : ℂ) ^ (n + 2) =
        ((Real.exp (-t) ^ (n + 1) - Real.exp (-t) ^ (n + 2) : ℝ) : ℂ) by push_cast; ring,
        ← mul_assoc, Complex.re_mul_ofReal]
    · dsimp only
      rw [show (1 : ℂ) - ((Real.exp (-t) : ℝ) : ℂ) ^ q = ((1 - Real.exp (-t) ^ q : ℝ) : ℂ) by
        push_cast; ring, ← mul_div_assoc, Complex.div_ofReal_re]
  have hGc : ContinuousOn (fun t : ℝ => (c * ∑ a ∈ Finset.range q, χ (a : ZMod q) *
      ((Real.exp (-t) : ℝ) : ℂ) ^ a).re / (1 - Real.exp (-t) ^ q)) (Ioi 0) := by
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) (fun t ht => ?_)
    have := hpow t ht
    linarith
  have hG0 : ∀ t : ℝ, 0 < t → 0 ≤ (fun t : ℝ => (c * ∑ a ∈ Finset.range q, χ (a : ZMod q) *
      ((Real.exp (-t) : ℝ) : ℂ) ^ a).re / (1 - Real.exp (-t) ^ q)) t := by
    intro t ht
    have := hpow t ht
    exact div_nonneg (hnn _ (Real.exp_pos _) (Real.exp_lt_one_iff.2 (by linarith))) (by linarith)
  have hGp : ∃ t : ℝ, 0 < t ∧ 0 < (fun t : ℝ => (c * ∑ a ∈ Finset.range q, χ (a : ZMod q) *
      ((Real.exp (-t) : ℝ) : ℂ) ^ a).re / (1 - Real.exp (-t) ^ q)) t := by
    refine ⟨-Real.log x0, neg_pos.2 (Real.log_neg hx0 hx1), ?_⟩
    simp only [neg_neg, Real.exp_log hx0]
    have := pow_lt_one₀ hx0.le hx1 (NeZero.ne q)
    exact div_pos hxp (by linarith)
  have key := mellin_pos ha hσ hG hGc hG0 hGp
  intro hL
  rw [LFunction_eq_tsum χ hχ (by simpa using hσ)] at hL
  have hcp : ∀ k : ℕ, ((k : ℕ) : ℂ) ^ (-(σ : ℂ)) = ((((k : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := fun k => by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg k), Complex.ofReal_neg, Complex.ofReal_natCast]
  have hterm : ∀ n : ℕ, (c * ((∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      (((n + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(σ : ℂ))))).re =
      (c * ∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)).re *
        (((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ)) := by
    intro n
    rw [hcp, hcp, ← Complex.ofReal_sub, ← mul_assoc, Complex.re_mul_ofReal]
  have hsumC : Summable (fun n : ℕ => c * ((∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      (((n + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(σ : ℂ))))) := by
    refine Summable.of_norm_bounded ((summable_rpow_diff hσ).mul_left (‖c‖ * q)) (fun n => ?_)
    rw [hcp, hcp, ← Complex.ofReal_sub, ← mul_assoc, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (rpow_diff_nonneg hσ n)]
    exact mul_le_mul_of_nonneg_right (hAb n) (rpow_diff_nonneg hσ n)
  have h0 : (c * ∑' n : ℕ, (∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)) *
      (((n + 1 : ℕ) : ℂ) ^ (-(σ : ℂ)) - ((n + 2 : ℕ) : ℂ) ^ (-(σ : ℂ)))).re =
      ∑' n : ℕ, (c * ∑ m ∈ Finset.Icc 1 (n + 1), χ (m : ZMod q)).re *
        (((n + 1 : ℕ) : ℝ) ^ (-σ) - ((n + 2 : ℕ) : ℝ) ^ (-σ)) := by
    rw [← tsum_mul_left, Complex.re_tsum hsumC]
    exact tsum_congr hterm
  rw [hL, mul_zero, Complex.zero_re] at h0
  linarith

end LeanLab.HelfgottMajor.RealAxisKernel

#print axioms LeanLab.HelfgottMajor.RealAxisKernel.LFunction_ofReal_ne_zero_of_kernel
