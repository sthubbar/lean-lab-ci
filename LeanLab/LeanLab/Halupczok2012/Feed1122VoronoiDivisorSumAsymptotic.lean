import LeanLab.RieselVaughan1983.Lemma1Large
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import LeanLab.Halupczok2012.Feed1122SawtoothSumBound
import LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

/-!
Split of `voronoi_divisor_sum_asymptotic` from Decomp532a.
Halupczok journal page 337, the Voronoi formula cited below display 2.2.
The classical proof is the Dirichlet hyperbola method followed by the
Voronoi, van der Corput bound for the sawtooth sum over divisors up to the square root.
Leaves: the exact hyperbola identity, the elementary harmonic sum reduction,
and the sawtooth exponential sum bound.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic

open Finset Filter Topology

/-- Dirichlet hyperbola identity, formerly a leaf, the first step of the classical proof of the
Voronoi formula cited on Halupczok page 337. For every real x at least one,
the divisor summatory function equals twice the sum of floor x over m for m up to
the square root of x, minus the square of the floor of the square root.
Now carried by the integer leaf nat_hyperbola_identity in Feed1122HyperbolaIdentity. -/
theorem hyperbola_identity :
    ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) =
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 :=
  Feed1122HyperbolaIdentity.hyperbola_identity_of_leaves

/-! Helpers for the harmonic sum reduction: the second order Euler Maclaurin asymptotic
H_s = log s + gamma + 1/(2s) + O(1/s^2), proved by telescoping with the series of
log(1 + 1/n) in powers of 1/(2n+1). -/

lemma log_one_add_inv_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1)) - 1 / (n : ℝ) ^ 3 ≤ Real.log (1 + (n : ℝ)⁻¹) ∧
    Real.log (1 + (n : ℝ)⁻¹) ≤ 1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have hs := Real.hasSum_log_one_add_inv hpos
  set y : ℝ := 1 / (2 * (n : ℝ) + 1) with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy3 : y ≤ 1 / 3 := by
    rw [hy, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hy1 : y ^ 2 < 1 := by nlinarith
  have hgeo : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy1).mul_left (2 * y)
  have hval : 2 * y * (1 - y ^ 2)⁻¹ = 1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1)) := by
    have hq : 1 - y ^ 2 = 4 * (n : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) ^ 2 := by
      rw [hy]; field_simp; ring
    rw [hq, inv_div, hy]; field_simp; ring
  constructor
  · have h0 := le_hasSum hs 0 (fun j _ => by positivity)
    have e0 : (2 : ℝ) * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * y ^ (2 * 0 + 1) = 2 * y := by norm_num
    rw [e0] at h0
    have e : 1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1)) - 2 * y =
        1 / (2 * (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) := by
      rw [hy]; field_simp; ring
    have h3 : 1 / (2 * (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) ≤ 1 / (n : ℝ) ^ 3 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [pow_pos hpos 3, pow_pos hpos 2, hpos]
    linarith
  · have hle := hasSum_le (fun k => ?_) hs hgeo
    · linarith
    · have e : y ^ (2 * k + 1) = y * (y ^ 2) ^ k := by rw [← pow_mul, pow_succ]; ring
      rw [e]
      have h1 : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
      have h2 : 0 ≤ y * (y ^ 2) ^ k := by positivity
      nlinarith

lemma inv_sq_diff (n : ℝ) (hn : 1 ≤ n) : 1 / (2 * n ^ 3) ≤ 1 / n ^ 2 - 1 / (n + 1) ^ 2 := by
  have hp : 0 < n := by linarith
  have e : 1 / n ^ 2 - 1 / (n + 1) ^ 2 = (2 * n + 1) / (n ^ 2 * (n + 1) ^ 2) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_pos hp 2, pow_pos hp 3, pow_pos hp 4]

lemma a_diff (n : ℕ) (hn : 1 ≤ n) :
    ((harmonic n : ℝ) - Real.log n - 1 / (2 * (n : ℝ))) -
      ((harmonic (n + 1) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) - 1 / (2 * ((n + 1 : ℕ) : ℝ))) =
      Real.log (1 + (n : ℝ)⁻¹) - (1 / (2 * (n : ℝ)) + 1 / (2 * ((n : ℝ) + 1))) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : Real.log ((n : ℝ) + 1) = Real.log n + Real.log (1 + (n : ℝ)⁻¹) := by
    rw [← Real.log_mul hpos.ne' (by positivity)]
    congr 1; field_simp
  rw [harmonic_succ]; push_cast
  rw [hl]
  field_simp; ring

lemma harmonic_asymp (s : ℕ) (hs : 1 ≤ s) :
    |(harmonic s : ℝ) - Real.log s - 1 / (2 * (s : ℝ)) - Real.eulerMascheroniConstant| ≤
      2 / (s : ℝ) ^ 2 := by
  set A : ℕ → ℝ := fun m => (harmonic m : ℝ) - Real.log m - 1 / (2 * (m : ℝ)) with hA
  have hstep : ∀ k : ℕ, -1 / ((k : ℝ) + 1) ^ 3 ≤ A (k + 1) - A (k + 1 + 1) ∧
      A (k + 1) - A (k + 1 + 1) ≤ 0 := by
    intro k
    have hd := a_diff (k + 1) (by omega)
    have hb := log_one_add_inv_bounds (k + 1) (by omega)
    simp only [hA]
    push_cast at hd hb ⊢
    rw [hd]
    constructor
    · have : -1 / ((k : ℝ) + 1) ^ 3 = -(1 / ((k : ℝ) + 1) ^ 3) := by ring
      rw [this]; linarith [hb.1]
    · linarith [hb.2]
  have hz : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun k : ℕ => (harmonic (k + 1) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) atTop
      (𝓝 Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun k : ℕ => A (k + 1)) atTop (𝓝 Real.eulerMascheroniConstant) := by
    have := h1.sub (hz.const_mul (1 / 2))
    rw [mul_zero, sub_zero] at this
    refine this.congr (fun k => ?_)
    have e : (1 : ℝ) / (2 * ((k : ℝ) + 1)) = 1 / 2 * (1 / ((k : ℝ) + 1)) := by
      rw [one_div_mul_one_div]
    simp only [hA]; push_cast; rw [e]
  have hsq : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
    have := (hz.pow 2).const_mul 2
    simpa using this
  have hU : Monotone (fun k : ℕ => A (k + 1) - 2 * (1 / ((k : ℝ) + 1)) ^ 2) := by
    refine monotone_nat_of_le_succ (fun k => ?_)
    have h := (hstep k).2
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    have hi := inv_sq_diff ((k : ℝ) + 1) hk
    have hp : 0 ≤ 1 / (2 * ((k : ℝ) + 1) ^ 3) := by positivity
    push_cast
    have e1 : (1 / ((k : ℝ) + 1)) ^ 2 = 1 / ((k : ℝ) + 1) ^ 2 := by rw [div_pow, one_pow]
    have e2 : (1 / ((k : ℝ) + 1 + 1)) ^ 2 = 1 / ((k : ℝ) + 1 + 1) ^ 2 := by rw [div_pow, one_pow]
    rw [e1, e2]
    linarith
  have hV : Antitone (fun k : ℕ => A (k + 1) + 2 * (1 / ((k : ℝ) + 1)) ^ 2) := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    have h := (hstep k).1
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [k.cast_nonneg (α := ℝ)]
    have hi := inv_sq_diff ((k : ℝ) + 1) hk
    push_cast
    have e1 : (1 / ((k : ℝ) + 1)) ^ 2 = 1 / ((k : ℝ) + 1) ^ 2 := by rw [div_pow, one_pow]
    have e2 : (1 / ((k : ℝ) + 1 + 1)) ^ 2 = 1 / ((k : ℝ) + 1 + 1) ^ 2 := by rw [div_pow, one_pow]
    have e3 : -1 / ((k : ℝ) + 1) ^ 3 = - (2 * (1 / (2 * ((k : ℝ) + 1) ^ 3))) := by
      field_simp
    rw [e1, e2]
    rw [e3] at h
    linarith
  have hUl : Tendsto (fun k : ℕ => A (k + 1) - 2 * (1 / ((k : ℝ) + 1)) ^ 2) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa using hlim.sub hsq
  have hVl : Tendsto (fun k : ℕ => A (k + 1) + 2 * (1 / ((k : ℝ) + 1)) ^ 2) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa using hlim.add hsq
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hu := hU.ge_of_tendsto hUl k
  have hv := hV.le_of_tendsto hVl k
  have e : 2 * (1 / ((k : ℝ) + 1)) ^ 2 = 2 / (((k + 1 : ℕ) : ℝ)) ^ 2 := by
    push_cast; rw [div_pow, one_pow]; ring
  rw [e] at hu hv
  rw [abs_le]
  constructor <;> simp only [hA] at hu hv <;> linarith

/-- Formerly LEAF, now proved: harmonic sum reduction in the classical proof of the Voronoi formula cited on
Halupczok page 337. Writing floor of x over m as x over m minus one half minus the
sawtooth, and using the harmonic sum up to the square root with Euler's constant,
the hyperbola expression differs from the main term plus minus twice the sawtooth sum by
a bounded amount, here stated with the weaker bound C x to one third log x.
Class MEDIUM: elementary real analysis with the Euler Mascheroni asymptotic. -/
theorem harmonic_reduction :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |(2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  refine ⟨28, max 16 (Real.exp 1), by norm_num, fun x hx => ?_⟩
  have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  set s : ℕ := ⌊Real.sqrt x⌋₊ with hs_def
  have hsq0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs4 : 4 ≤ s := by
    apply Nat.le_floor
    rw [Real.le_sqrt (by norm_num) hx0.le]; push_cast; linarith
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs4
  have hs0 : (0 : ℝ) < s := by linarith
  have hsle : (s : ℝ) ≤ Real.sqrt x := Nat.floor_le hsq0
  have hslt : Real.sqrt x < (s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsx : (s : ℝ) ^ 2 ≤ x := by
    have := pow_le_pow_left₀ hs0.le hsle 2
    rwa [Real.sq_sqrt hx0.le] at this
  have hxs : x < ((s : ℝ) + 1) ^ 2 := by
    have := pow_lt_pow_left₀ hslt hsq0 (by norm_num : (2 : ℕ) ≠ 0)
    rwa [Real.sq_sqrt hx0.le] at this
  -- the harmonic sum
  set H : ℝ := ∑ m ∈ Icc 1 s, ((m : ℕ) : ℝ)⁻¹ with hH_def
  have hsum : 2 * ∑ m ∈ Icc 1 s, (⌊x / m⌋₊ : ℝ) + 2 * ∑ m ∈ Icc 1 s, (Int.fract (x / m) - 1 / 2)
      = 2 * x * H - s := by
    rw [← mul_add, ← sum_add_distrib]
    have hterm : ∀ m ∈ Icc 1 s, (⌊x / m⌋₊ : ℝ) + (Int.fract (x / m) - 1 / 2) =
        x * ((m : ℕ) : ℝ)⁻¹ - 1 / 2 := by
      intro m _
      rw [natCast_floor_eq_intCast_floor (by positivity), ← Int.self_sub_fract]; ring
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  have hH : (harmonic s : ℝ) = H := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hr := harmonic_asymp s (by omega)
  rw [hH] at hr
  set r : ℝ := H - Real.log s - 1 / (2 * (s : ℝ)) - Real.eulerMascheroniConstant with hr_def
  -- the logarithm
  set L : ℝ := Real.log (x / (s : ℝ) ^ 2) with hL_def
  have hq : 0 < x / (s : ℝ) ^ 2 := by positivity
  have hlogx : Real.log x = 2 * Real.log s + L := by
    rw [hL_def, Real.log_div hx0.ne' (by positivity), Real.log_pow]; push_cast; ring
  set u : ℝ := x / s - s with hu_def
  have hxu : x = (s : ℝ) ^ 2 + s * u := by
    have : (s : ℝ) * (x / s) = x := mul_div_cancel₀ x hs0.ne'
    rw [hu_def, mul_sub, this]; ring
  have hu0 : 0 ≤ u := by nlinarith
  have hu3 : u < 3 := by nlinarith
  have hLup : L ≤ u / s := by
    have h1 := Real.log_le_sub_one_of_pos hq
    have h2 : x / (s : ℝ) ^ 2 - 1 = u / s := by rw [hxu]; field_simp; ring
    linarith
  have hLlo : 1 - (s : ℝ) ^ 2 / x ≤ L := by
    have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hq)
    rw [Real.log_inv, inv_div] at h1
    linarith
  have hxL1 : x * L ≤ s * u + u ^ 2 := by
    have := mul_le_mul_of_nonneg_left hLup hx0.le
    have e : x * (u / s) = s * u + u ^ 2 := by rw [hxu]; field_simp; try ring
    linarith
  have hxL2 : s * u ≤ x * L := by
    have := mul_le_mul_of_nonneg_left hLlo hx0.le
    have e : x * (1 - (s : ℝ) ^ 2 / x) = s * u := by
      have : x * (1 - (s : ℝ) ^ 2 / x) = x - (s : ℝ) ^ 2 := by field_simp
      rw [this, hxu]; ring
    linarith
  have hr2 : |2 * x * r| ≤ 7 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * x)]
    have h1 : 2 * x * |r| ≤ 2 * x * (2 / (s : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    have h2 : 2 * x * (2 / (s : ℝ) ^ 2) = 4 + 4 * (u / s) := by rw [hxu]; field_simp; ring
    have h3 : u / s ≤ 3 / 4 := by
      rw [div_le_iff₀ hs0]; nlinarith
    linarith
  have hE : (2 * ∑ m ∈ Icc 1 s, (⌊x / m⌋₊ : ℝ) - (s : ℝ) ^ 2) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 s, (Int.fract (x / m) - 1 / 2) =
      (x - (s : ℝ) ^ 2 - x * L) + (x / s - s) + 2 * x * r := by
    have key : (2 * ∑ m ∈ Icc 1 s, (⌊x / m⌋₊ : ℝ) - (s : ℝ) ^ 2) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 s, (Int.fract (x / m) - 1 / 2) =
        2 * x * H - s - (s : ℝ) ^ 2 -
          (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) := by
      linarith [hsum]
    have hHr : H = Real.log s + 1 / (2 * (s : ℝ)) + Real.eulerMascheroniConstant + r := by
      rw [hr_def]; ring
    rw [key, hlogx, hHr]
    field_simp
    ring
  have hbound : |(2 * ∑ m ∈ Icc 1 s, (⌊x / m⌋₊ : ℝ) - (s : ℝ) ^ 2) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 s, (Int.fract (x / m) - 1 / 2)| ≤ 19 := by
    rw [hE]
    obtain ⟨a1, a2⟩ := abs_le.mp hr2
    have hxs2 : x - (s : ℝ) ^ 2 = s * u := by rw [hxu]; ring
    have hu2 : u ^ 2 ≤ 9 := by nlinarith
    rw [hxs2, abs_le]; constructor <;> linarith
  have hlog1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hpow1 : 1 ≤ x ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hprod : 1 ≤ x ^ (1 / 3 : ℝ) * Real.log x := one_le_mul_of_one_le_of_one_le hpow1 hlog1
  calc _ ≤ (19 : ℝ) := hbound
    _ ≤ 28 * (x ^ (1 / 3 : ℝ) * Real.log x) := by linarith
    _ = 28 * x ^ (1 / 3 : ℝ) * Real.log x := by ring


/-- Voronoi sawtooth bound, formerly a leaf, the analytic step of the classical proof of the
Voronoi formula cited on Halupczok page 337. The sum over m up to the square root of x
of the sawtooth Int.fract of x over m minus one half is O of x to one third times log x,
proved by the van der Corput second derivative test on dyadic blocks.
Analytic content: a genuine exponential sum estimate.
Now carried by the smaller HARD leaf tail_sawtooth_bound in Feed1122SawtoothSumBound. -/
theorem sawtooth_sum_bound :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
        C * x ^ (1 / 3 : ℝ) * Real.log x :=
  Feed1122SawtoothSumBound.sawtooth_sum_bound_of_leaves

/-- The hyperbola identity and the harmonic reduction give the divisor sum
minus the main term plus twice the sawtooth sum, at size x to one third log x. -/
theorem divisor_sum_sawtooth_form :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ x : ℝ, X0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  obtain ⟨C, X0, hC, h⟩ := harmonic_reduction
  refine ⟨C, max X0 1, hC, fun x hx => ?_⟩
  rw [hyperbola_identity x ((le_max_right _ _).trans hx)]
  exact h x ((le_max_left _ _).trans hx)

/-- Halupczok journal page 337, the printed Voronoi formula below display 2.2,
assembled from the three leaves. Statement identical to the parent declaration. -/
theorem voronoi_divisor_sum_asymptotic_of_leaves :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
          C * x ^ (1 / 3 : ℝ) * Real.log x := by
  obtain ⟨CA, XA, hCA, hA⟩ := divisor_sum_sawtooth_form
  obtain ⟨CB, XB, hCB, hB⟩ := sawtooth_sum_bound
  refine ⟨CA + 2 * CB, max (max XA XB) 2, by positivity, le_max_right _ _, fun x hx => ?_⟩
  have hA' := hA x ((le_max_left _ _).trans ((le_max_left _ _).trans hx))
  have hB' := hB x ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  obtain ⟨a1, a2⟩ := abs_le.mp hA'
  obtain ⟨b1, b2⟩ := abs_le.mp hB'
  have he : (CA + 2 * CB) * x ^ (1 / 3 : ℝ) * Real.log x =
      CA * x ^ (1 / 3 : ℝ) * Real.log x + 2 * (CB * x ^ (1 / 3 : ℝ) * Real.log x) := by ring
  rw [he]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Elementary algebra for the harmonic reduction before the Voronoi formula.
A two sided harmonic remainder of size 1 over 8r squared leaves a bounded error.
Source target: Halupczok journal page 337, the formula below display 2.2. -/
theorem harmonic_reduction_algebra (x s r H γ : ℝ) (hr : 1 ≤ r) (hrs : r ≤ s) (hsr : s ≤ r + 1)
    (hsx : s ^ 2 = x)
    (hHl : Real.log r + 1 / (2 * r) - 1 / (8 * r ^ 2) + γ ≤ H)
    (hHu : H ≤ Real.log r + 1 / (2 * r) + γ) :
    |2 * x * H - r - r ^ 2 - (x * Real.log x + (2 * γ - 1) * x)| ≤ 8 := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < s := by linarith
  have hx0 : 0 < x := by nlinarith
  have hlx : Real.log x = 2 * Real.log s := by
    rw [← hsx, Real.log_pow]
    norm_num
  have hlogu : Real.log s - Real.log r ≤ (s - r) / r := by
    rw [← Real.log_div hs0.ne' hr0.ne']
    have ht := Real.log_le_sub_one_of_pos (div_pos hs0 hr0)
    convert ht using 1 <;> field_simp
  have hlogl : (s - r) / s ≤ Real.log s - Real.log r := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hr0 hs0)
    rw [Real.log_div hr0.ne' hs0.ne'] at ht
    have he : r / s - 1 = -(s - r) / s := by field_simp; ring
    rw [he, neg_div] at ht
    linarith
  have hbaseu : x - r ^ 2 - 2 * x * (Real.log s - Real.log r) ≤ 0 := by
    have ht := mul_le_mul_of_nonneg_left hlogl (by positivity : 0 ≤ 2 * x)
    have he : 2 * x * ((s - r) / s) = 2 * s * (s - r) := by
      rw [← hsx]
      field_simp
    rw [he] at ht
    nlinarith [sq_nonneg (s - r)]
  have hbasel : -5 ≤ x - r ^ 2 - 2 * x * (Real.log s - Real.log r) := by
    have ht := mul_le_mul_of_nonneg_left hlogu (by positivity : 0 ≤ 2 * x)
    have he : x - r ^ 2 - 2 * x * ((s - r) / r) =
        -((s - r) ^ 2 * (2 * s + r) / r) := by
      rw [← hsx]; field_simp; ring
    have hd : (s - r) ^ 2 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hd (by linarith : 0 ≤ 2 * s + r)
    have hb : (s - r) ^ 2 * (2 * s + r) / r ≤ 5 := by
      apply (div_le_iff₀ hr0).mpr
      nlinarith
    linarith
  have hmidl : 0 ≤ x / r - r := by
    have : r ^ 2 ≤ x := by nlinarith
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hr0).mpr
    nlinarith
  have hmidu : x / r - r ≤ 3 := by
    have he : x / r - r = (s - r) * (s + r) / r := by
      rw [← hsx]; field_simp; ring
    rw [he]
    apply (div_le_iff₀ hr0).mpr
    have hm := mul_le_mul_of_nonneg_right (show s - r ≤ 1 by linarith)
      (by linarith : 0 ≤ s + r)
    nlinarith
  have hρu : H - Real.log r - γ - 1 / (2 * r) ≤ 0 := by linarith
  have hρl : -(1 / (8 * r ^ 2)) ≤ H - Real.log r - γ - 1 / (2 * r) := by linarith
  have hcorru := mul_le_mul_of_nonneg_left hρu (by positivity : 0 ≤ 2 * x)
  have hcorrl := mul_le_mul_of_nonneg_left hρl (by positivity : 0 ≤ 2 * x)
  have hc : 2 * x * (1 / (8 * r ^ 2)) ≤ 1 := by
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 8 * r ^ 2)]
    nlinarith
  have he : 2 * x * H - r - r ^ 2 - (x * Real.log x + (2 * γ - 1) * x) =
      2 * x * (H - Real.log r - γ - 1 / (2 * r)) +
        (x / r - r) + (x - r ^ 2 - 2 * x * (Real.log s - Real.log r)) := by
    rw [hlx]
    field_simp
    ring
  rw [he]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Combining the floor and sawtooth sums leaves the harmonic sum exactly.
Source target: the same elementary reduction before the cited Voronoi formula. -/
theorem floor_sawtooth_sum (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ m ∈ Icc 1 n, (⌊x / m⌋₊ : ℝ)) +
      ∑ m ∈ Icc 1 n, (Int.fract (x / m) - 1 / 2) =
        x * (harmonic n : ℝ) - (n : ℝ) / 2 := by
  rw [← sum_add_distrib]
  trans ∑ m ∈ Icc 1 n, (x * (m : ℝ)⁻¹ - 1 / 2)
  · apply sum_congr rfl
    intro m hm
    have hf := Int.floor_add_fract (x / m)
    rw [← natCast_floor_eq_intCast_floor (div_nonneg hx (Nat.cast_nonneg m))] at hf
    simp only [div_eq_mul_inv] at hf ⊢
    linarith
  · have hh : ∑ m ∈ Icc 1 n, (m : ℝ)⁻¹ = (harmonic n : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [sum_sub_distrib, ← mul_sum, hh]
    simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
      mul_one_div]

/-- The elementary harmonic residual is uniformly bounded before applying
any sawtooth cancellation. Source target: Halupczok page 337 below display 2.2. -/
theorem harmonic_reduction_bounded (x : ℝ) (hx : 4 ≤ x) :
    |(2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2) -
      (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
      2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (Int.fract (x / m) - 1 / 2)| ≤ 8 := by
  have hx0 : 0 < x := by linarith
  let n := ⌊Real.sqrt x⌋₊
  have hs1 : (1 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le (show (1 : ℝ) ^ 2 ≤ x by linarith)
  have hn : 1 ≤ n := Nat.le_floor (by simpa only [Nat.cast_one] using hs1)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hns : (n : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hsn : Real.sqrt x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one (Real.sqrt x)).le
  obtain ⟨hHl, hHu⟩ := LeanLab.RieselVaughan1983.harm_bounds n hn
  have hb := harmonic_reduction_algebra x (Real.sqrt x) n (harmonic n)
    Real.eulerMascheroniConstant hnR hns hsn (Real.sq_sqrt hx0.le) hHl hHu
  have he := floor_sawtooth_sum x hx0.le n
  change |(2 * ∑ m ∈ Icc 1 n, (⌊x / m⌋₊ : ℝ) - (n : ℝ) ^ 2) -
      (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 n, (Int.fract (x / m) - 1 / 2)| ≤ _
  have hid : (2 * ∑ m ∈ Icc 1 n, (⌊x / m⌋₊ : ℝ) - (n : ℝ) ^ 2) -
      (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) +
        2 * ∑ m ∈ Icc 1 n, (Int.fract (x / m) - 1 / 2) =
      2 * x * (harmonic n : ℝ) - (n : ℝ) - (n : ℝ) ^ 2 -
        (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x) := by
    linarith
  rw [hid]
  exact hb


/-- The elementary Dirichlet error bound obtained before the missing Voronoi
cancellation: five times sqrt x for x at least four.
This is weaker than the cube root logarithmic error cited on Halupczok page 337. -/
theorem divisor_sum_square_root_error (x : ℝ) (hx : 4 ≤ x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) -
      (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
        5 * Real.sqrt x := by
  let n := ⌊Real.sqrt x⌋₊
  let D : ℝ := ∑ m ∈ Icc 1 ⌊x⌋₊, (m.divisors.card : ℝ)
  let M := x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x
  let T := ∑ m ∈ Icc 1 n, (Int.fract (x / m) - 1 / 2)
  have hb : |D - M + 2 * T| ≤ 8 := by
    have hh := harmonic_reduction_bounded x hx
    rw [← hyperbola_identity x (by linarith)] at hh
    exact hh
  have hs : |T| ≤ (n : ℝ) / 2 := by
    calc
      _ ≤ ∑ m ∈ Icc 1 n, |Int.fract (x / m) - 1 / 2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Icc 1 n, (1 / 2 : ℝ) := sum_le_sum fun m _ =>
        Feed1122SawtoothSumBound.abs_sawtooth_le _
      _ = (n : ℝ) / 2 := by
        simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel,
          mul_one_div]
  have ht : |D - M| ≤ |D - M + 2 * T| + 2 * |T| := by
    calc
      _ = |(D - M + 2 * T) - 2 * T| := by congr 1; ring
      _ ≤ |D - M + 2 * T| + |2 * T| := abs_sub _ _
      _ = _ := by rw [abs_mul]; norm_num
  have hn : (n : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hx2 : (2 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le (show (2 : ℝ) ^ 2 ≤ x by linarith)
  change |D - M| ≤ 5 * Real.sqrt x
  linarith


end LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic

#print axioms LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic.harmonic_reduction
#print axioms LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic.divisor_sum_sawtooth_form
#print axioms LeanLab.Halupczok2012.Feed1122VoronoiDivisorSumAsymptotic.voronoi_divisor_sum_asymptotic_of_leaves
