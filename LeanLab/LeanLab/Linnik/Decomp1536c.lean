/-
Unit U-1536, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0026: J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I,
Acta Arith. 109.2 (2003), 169-194.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

File c, Section 7, p. 185, Corollary 1, in the form the proof of Theorem 1 needs, with `d = 3/4`
in place of the printed `d = 0.7163435444776661`, and its use in Section 10, pp. 190-193.

Why `d = 3/4` is enough: in (10.5) the paper uses Corollary 1 as `|G| ≤ (1-η)L` outside `E`,
`1 - η = 0.716344`; the bound then enters (10.2) and (10.15) through `(1-η)^4` and `(1-η)^6`,
and (10.15) has room: with `3/4` the product in (10.14) is below `0.88 < 1`, `k7_with_34`.
Certifying the printed `d` would need the inf in (7.1) to about 15 digits, since the printed `d`
is that inf at `c = (log 2)/2`; numerics/u1536_cert.py finds the margin there below `10⁻⁵`.

This is the lab's weakening of Corollary 1, faithful to the method of Sections 4 to 7, not the
printed constant.

Assemblies, CONDITIONAL ON the leaves of files a, b, c: `devSet_34`, `cor1_34`, `cor1_N`.
Proved outright: `k7_with_34`, `paper_d_lt`.
-/

/- CODEX task199 completed the three original leaves and their corollary assemblies.
The historical CONDITIONAL labels below are superseded by the build and axiom evidence in
build/codex-task199.log. The certified Corollary 1 threshold remains three fourths.
AI wrote the Lean changes. Goldbach is open. -/
import Mathlib
import LeanLab.Linnik.Decomp1536b

namespace LeanLab.Linnik.Decomp1536c

open Real MeasureTheory Finset
open LeanLab.Linnik.Decomp1536a (Gpow Spow EL devSet devSet_le)
open LeanLab.Linnik.Decomp1536b (EL_one_le)

/-- The paper's `G(α) = Σ_{m=1}^{L} e(2^m α)`, Section 8, p. 186; it equals `G_L(2α)`. -/
noncomputable def Gpaper (L : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ range L, Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ (m + 1) * α))

/-- LEAF. Unit U-1536. Numerical input for `λ = 1`, `d = 3/4`:
`1.454 · e^{-3/4} ≤ 0.98/√2`, that is `ψ(1) - 3/4 < -(log 2)/2` with room, (7.1), p. 184.
Equivalent to `2 · 1.454² ≤ 0.98² e^{3/2}`, `4.2283 ≤ 4.3042`. -/
theorem ratio_num : (1454 / 1000 : ℝ) * Real.exp (-(3 / 4)) ≤ (98 / 100) / Real.sqrt 2 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hs : Real.sqrt 2 ≤ (1415 / 1000 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity : 0 < Real.sqrt 2)]
  nlinarith


/-- LEAF. Unit U-1536. A polynomial times a geometric factor is bounded:
for every `B` there is `C` with `11 (1 + L) 0.98^L L^B ≤ C` for all `L`. -/
theorem poly_geom (B : ℕ) :
    ∃ C : ℝ, ∀ L : ℕ, 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L * (L : ℝ) ^ B ≤ C := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one B (r := (98 / 100 : ℝ)) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (B + 1) (r := (98 / 100 : ℝ)) (by norm_num)
  have hs : Summable (fun L : ℕ => 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L * (L : ℝ) ^ B) := by
    convert (h0.add h1).mul_left 11 using 1
    ext L
    rw [pow_succ]
    ring
  exact ⟨_, fun L => hs.le_tsum L (fun _ _ => by positivity)⟩


/-- LEAF. Unit U-1536. Change of variable between the paper's `G(α) = G_L(2α)` of Section 8, p. 186,
and `G_L` of Section 4, p. 172: `α ↦ 2α` is two to one on `[0,1]` onto `[0,2]` and `G_L` has period
1, so the two large deviation sets have the same measure. -/
theorem measure_transfer (L : ℕ) (d : ℝ) :
    volume {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ d * L < ‖Gpaper L α‖} = volume (devSet L d) := by
  have hpaper (x : ℝ) : Gpaper L x = Gpow L (2 * x) := by
    unfold Gpaper Gpow
    apply sum_congr rfl
    intro m hm
    congr 1
    push_cast
    ring
  have hperiod : Function.Periodic (Gpow L) 1 := by
    intro x
    unfold Gpow
    apply sum_congr rfl
    intro m hm
    have he : 2 * (π : ℂ) * Complex.I * ((2 : ℂ) ^ m * ((x + 1 : ℝ) : ℂ)) =
        2 * π * Complex.I * ((2 : ℂ) ^ m * x) + (2 ^ m : ℕ) * (2 * π * Complex.I) := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp_rw [hpaper]
  let s : Set ℝ := {x | d * L < ‖Gpow L x‖}
  have hc : Continuous (Gpow L) := by unfold Gpow; fun_prop
  have hm : MeasurableSet s := isOpen_lt continuous_const hc.norm |>.measurableSet
  let f : ℝ → ℝ := s.indicator (fun _ => 1)
  have hp : Function.Periodic f 1 := by
    intro x
    simp only [f, Set.indicator, s, Set.mem_ofPred_eq, hperiod x]
  have hi : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    have hi0 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
    exact ⟨hi0.1.indicator hm, hi0.2.indicator hm⟩
  have hdouble : (∫ x in (0 : ℝ)..2, f x) = 2 * ∫ x in (0 : ℝ)..1, f x := by
    have h := hp.intervalIntegral_add_zsmul_eq (2 : ℤ) 0 hi
    simpa using h
  have hchange : (∫ x in (0 : ℝ)..1, f (2 * x)) = ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [mul_zero, mul_one]
    rw [hdouble]
    simp
  have hm2 : MeasurableSet {x : ℝ | d * L < ‖Gpow L (2 * x)‖} := by
    exact (isOpen_lt continuous_const (hc.comp (continuous_const.mul continuous_id)).norm).measurableSet
  have hf2 : (fun x => f (2 * x)) = {x : ℝ | d * L < ‖Gpow L (2 * x)‖}.indicator (fun _ => (1 : ℝ)) := by
    ext x
    simp [f, s, Set.indicator]
  rw [hf2, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc, setIntegral_indicator hm2, setIntegral_const,
    intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator hm, setIntegral_const] at hchange
  simp only [smul_eq_mul, mul_one] at hchange
  have ha : volume (Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | d * L < ‖Gpow L (2 * x)‖}) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_left)
  have hb : volume (Set.Icc (0 : ℝ) 1 ∩ s) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_left)
  exact (measureReal_eq_measureReal_iff ha hb).mp hchange


/-! ### Assemblies -/

/-- `|{x ∈ [0,1] : |G_L(x)| > 3L/4}| ≤ 11 (1 + L) 0.98^L / (√2)^L`.
CONDITIONAL ON the leaves of files a and b and on `ratio_num`. -/
theorem devSet_34 (L : ℕ) :
    volume (devSet L (3 / 4)) ≤
      ENNReal.ofReal (11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L / Real.sqrt 2 ^ L) := by
  refine (devSet_le L (3 / 4) zero_le_one).trans (ENNReal.ofReal_le_ofReal ?_)
  have hE := EL_one_le L
  have hr := ratio_num
  have hs : 0 < Real.sqrt 2 := by positivity
  have hexp : Real.exp (-(1 * (3 / 4) * (L : ℝ))) = Real.exp (-(3 / 4)) ^ L := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hpos : 0 ≤ Real.exp (-(3 / 4 : ℝ)) := (Real.exp_pos _).le
  have key : Real.exp (-(3 / 4 : ℝ)) ^ L * EL L 1 ≤ ((98 / 100) / Real.sqrt 2) ^ L := by
    calc Real.exp (-(3 / 4 : ℝ)) ^ L * EL L 1
        ≤ Real.exp (-(3 / 4 : ℝ)) ^ L * (1454 / 1000 : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left hE (pow_nonneg hpos _)
      _ = ((1454 / 1000 : ℝ) * Real.exp (-(3 / 4))) ^ L := by rw [mul_pow]; ring
      _ ≤ ((98 / 100) / Real.sqrt 2) ^ L :=
          pow_le_pow_left₀ (by positivity) hr L
  have h11 : (0 : ℝ) ≤ 11 * (1 + 1 * (L : ℝ)) := by positivity
  calc 11 * (1 + 1 * (L : ℝ)) * Real.exp (-(1 * (3 / 4) * (L : ℝ))) * EL L 1
      = 11 * (1 + 1 * (L : ℝ)) * (Real.exp (-(3 / 4 : ℝ)) ^ L * EL L 1) := by
        rw [hexp]; ring
    _ ≤ 11 * (1 + 1 * (L : ℝ)) * ((98 / 100) / Real.sqrt 2) ^ L :=
        mul_le_mul_of_nonneg_left key h11
    _ = 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L / Real.sqrt 2 ^ L := by
        rw [div_pow]; ring

/-- Corollary 1 of p. 185 with `d = 3/4`, in terms of `L`: for every `B` there is `C` with
`|{x ∈ [0,1] : |G_L(x)| > 3L/4}| ≤ C / ((√2)^L L^B)` for `L ≥ 1`.
CONDITIONAL ON the leaves of files a, b and c. -/
theorem cor1_34 (B : ℕ) : ∃ C : ℝ, ∀ L : ℕ, 1 ≤ L →
    volume (devSet L (3 / 4)) ≤ ENNReal.ofReal (C / (Real.sqrt 2 ^ L * (L : ℝ) ^ B)) := by
  obtain ⟨C, hC⟩ := poly_geom B
  refine ⟨C, fun L hL => (devSet_34 L).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hLpos : (0 : ℝ) < (L : ℝ) ^ B := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hs : (0 : ℝ) < Real.sqrt 2 ^ L := by positivity
  rw [le_div_iff₀ (mul_pos hs hLpos)]
  have := hC L
  calc 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L / Real.sqrt 2 ^ L * (Real.sqrt 2 ^ L * (L : ℝ) ^ B)
      = 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L * (L : ℝ) ^ B := by
        field_simp
    _ ≤ C := this

/-- Corollary 1 of p. 185 with `d = 3/4`, in the paper's form: with `L = [log₂ N]` and the paper's
`G(α) = Σ_{m=1}^{L} e(2^m α)`, for every `B` there is `C` with
`|{α ∈ [0,1] : |G(α)| > 3L/4}| ≤ C N^{-1/2} L^{-B}` for `N ≥ 2`.
CONDITIONAL ON the leaves of files a, b and c. -/
theorem cor1_N (B : ℕ) : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    volume {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
        ‖Gpaper (Nat.log 2 N) α‖} ≤
      ENNReal.ofReal (C / (Real.sqrt N * ((Nat.log 2 N : ℕ) : ℝ) ^ B)) := by
  obtain ⟨C, hC⟩ := cor1_34 B
  refine ⟨Real.sqrt 2 * |C|, fun N hN => ?_⟩
  set L := Nat.log 2 N with hLdef
  have hL : 1 ≤ L := Nat.log_pos (by norm_num) hN
  rw [measure_transfer]
  refine (hC L hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hNlt : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNlt' : (N : ℝ) ≤ 2 ^ (L + 1) := by exact_mod_cast hNlt.le
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqN : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt 2 ^ L := by
    calc Real.sqrt N ≤ Real.sqrt (2 ^ (L + 1)) := Real.sqrt_le_sqrt hNlt'
      _ = Real.sqrt 2 ^ (L + 1) := by
          rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
            Real.mul_self_sqrt (by norm_num)]
      _ = Real.sqrt 2 * Real.sqrt 2 ^ L := by ring
  have hNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  have hLB : (0 : ℝ) < (L : ℝ) ^ B := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hsL : (0 : ℝ) < Real.sqrt 2 ^ L := by positivity
  calc C / (Real.sqrt 2 ^ L * (L : ℝ) ^ B) ≤ |C| / (Real.sqrt 2 ^ L * (L : ℝ) ^ B) :=
        div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    _ = Real.sqrt 2 * |C| / (Real.sqrt 2 * Real.sqrt 2 ^ L * (L : ℝ) ^ B) := by
        field_simp
    _ ≤ Real.sqrt 2 * |C| / (Real.sqrt N * (L : ℝ) ^ B) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hsqN hLB.le

/-- The printed constant of Corollary 1 is below `3/4`, and so is `1 - η` of Lemma 13, p. 190.
Proved. -/
theorem paper_d_lt : (0.7163435444776661 : ℝ) < 3 / 4 ∧ (1 - 0.283656 : ℝ) < 3 / 4 := by
  constructor <;> norm_num

/-- (10.2) and (10.15), pp. 191-193, with `d = 3/4` in place of `1 - η`: for `0 ≤ A(3) < 0.0136`,
`0 ≤ A(4) < 0.004`, `0 ≤ C₂' < 3.9095`, the product in (10.14) with `K = 7`, `i = 4`, `j = 3`, is
`(A(4) + C₂' d^6)(A(3) + C₂' d^4) < 0.88 < 1`.  Proved; no leaf. -/
theorem k7_with_34 {A3 A4 C : ℝ} (h3 : 0 ≤ A3) (h3' : A3 < 0.0136) (h4 : 0 ≤ A4)
    (h4' : A4 < 0.004) (hC : 0 ≤ C) (hC' : C < 3.9095) :
    (A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4) < 0.88 ∧
      Real.sqrt ((A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4)) < 1 := by
  have e1 : A4 + C * (3 / 4 : ℝ) ^ 6 < 0.6999 := by norm_num at *; nlinarith
  have e2 : A3 + C * (3 / 4 : ℝ) ^ 4 < 1.2506 := by norm_num at *; nlinarith
  have p1 : 0 ≤ A4 + C * (3 / 4 : ℝ) ^ 6 := by positivity
  have p2 : 0 ≤ A3 + C * (3 / 4 : ℝ) ^ 4 := by positivity
  have hprod : (A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4) < 0.88 := by
    calc (A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4)
        ≤ 0.6999 * (A3 + C * (3 / 4 : ℝ) ^ 4) := mul_le_mul_of_nonneg_right e1.le p2
      _ < 0.6999 * 1.2506 := by linarith
      _ < 0.88 := by norm_num
  refine ⟨hprod, ?_⟩
  rw [Real.sqrt_lt' one_pos]
  linarith


open Filter Set
open scoped Topology
open LeanLab.Linnik.Decomp1536a (EL_rate_exists norm_moment_exp_of_EL_rate continuous_SL)

/-- The strict large deviation rate bound of Section 7 p.184 before display 7.1.
The exponential moment rate is supplied by the proved Theorem 2a. -/
theorem large_deviation_rate {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ psi : ℝ,
      Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ)) atTop (𝓝 psi) ∧
      ∀ d c : ℝ, psi - lam * d < -c →
        ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
          volume (devSet L d) < ENNReal.ofReal (Real.exp (-c * L)) := by
  obtain ⟨psi, hpsi⟩ := EL_rate_exists lam
  refine ⟨psi, hpsi, fun d c hd => ?_⟩
  obtain ⟨err, herr, hform⟩ := norm_moment_exp_of_EL_rate hlam hpsi
  have hev : ∀ᶠ L : ℕ in atTop, err L < -c - psi + lam * d :=
    herr.eventually (gt_mem_nhds (by linarith))
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp hev
  refine ⟨max 1 L0, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL1
  refine (LeanLab.Linnik.Decomp1536a.markov hlam).trans_lt ?_
  rw [hform L hL1]
  apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mpr
  rw [← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  have he := mul_lt_mul_of_pos_right (hL0 L (le_trans (le_max_right _ _) hL)) hLp
  nlinarith


/-- The sufficient large deviation criterion of Section 7 p.184 display 7.1.
The rate exists by Theorem 2a and the inequality is strict as in the paper. -/
theorem large_deviation_criterion {lam : ℝ} (hlam : 0 < lam) :
    ∃ psi : ℝ,
      Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ)) atTop (𝓝 psi) ∧
      ∀ c d : ℝ, 0 < c → (psi + c) / lam < d →
        ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
          volume (devSet L d) < ENNReal.ofReal (Real.exp (-c * L)) := by
  obtain ⟨psi, hpsi, hdev⟩ := large_deviation_rate hlam.le
  refine ⟨psi, hpsi, fun c d _hc hd => ?_⟩
  apply hdev d c
  have h := (div_lt_iff₀ hlam).mp hd
  nlinarith


/-- The finite logarithmic moment is convex, as used in Section 7 p.185. -/
theorem log_EL_convex (L : ℕ) : ConvexOn ℝ Set.univ (fun lam : ℝ => Real.log (EL L lam)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hdom : ProbabilityTheory.integrableExpSet (Spow L) μ = Set.univ := by
    ext t
    simp only [Set.mem_univ, iff_true]
    change Integrable (fun x => Real.exp (t * Spow L x)) μ
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_SL L))).integrableOn_Icc
  have ha (t : ℝ) : AnalyticAt ℝ (ProbabilityTheory.cgf (Spow L) μ) t :=
    ProbabilityTheory.analyticAt_cgf (by rw [hdom, interior_univ]; trivial)
  have hd : Differentiable ℝ (ProbabilityTheory.cgf (Spow L) μ) := fun t => (ha t).differentiableAt
  have hdd : Differentiable ℝ (deriv (ProbabilityTheory.cgf (Spow L) μ)) :=
    fun t => (ha t).deriv.differentiableAt
  have he : (fun lam : ℝ => Real.log (EL L lam)) = ProbabilityTheory.cgf (Spow L) μ := by
    ext lam
    change Real.log (∫ x in (0 : ℝ)..1, Real.exp (lam * Spow L x)) =
      Real.log (∫ x in Set.Icc (0 : ℝ) 1, Real.exp (lam * Spow L x))
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rw [he]
  apply convexOn_of_deriv2_nonneg' convex_univ hd.differentiableOn hdd.differentiableOn
  intro t ht
  rw [← iteratedDeriv_eq_iterate]
  rw [ProbabilityTheory.iteratedDeriv_two_cgf_eq_integral (by rw [hdom, interior_univ]; trivial)]
  apply div_nonneg
  · apply integral_nonneg
    intro x
    positivity
  · exact ProbabilityTheory.mgf_nonneg


/-- Convexity passes to the common logarithmic rate, Section 7 p.185. -/
theorem rate_convex (psi : ℝ → ℝ)
    (hpsi : ∀ lam : ℝ, Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ))
      atTop (𝓝 (psi lam))) : ConvexOn ℝ Set.univ psi := by
  refine ⟨convex_univ, fun x hx y hy a b ha hb hab => ?_⟩
  change psi (a * x + b * y) ≤ a * psi x + b * psi y
  apply le_of_tendsto_of_tendsto (hpsi _) (((hpsi x).const_mul a).add ((hpsi y).const_mul b))
  filter_upwards [] with L
  have h := (log_EL_convex L).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  calc Real.log (EL L (a * x + b * y)) / (L : ℝ)
      ≤ (a * Real.log (EL L x) + b * Real.log (EL L y)) / (L : ℝ) :=
        div_le_div_of_nonneg_right h (Nat.cast_nonneg L)
    _ = a * (Real.log (EL L x) / (L : ℝ)) + b * (Real.log (EL L y) / (L : ℝ)) := by ring


/-- One convex moment rate function and the criterion of Section 7 pp.184 and 185. -/
theorem convex_large_deviation_criterion :
    ∃ psi : ℝ → ℝ, ConvexOn ℝ Set.univ psi ∧
      (∀ lam : ℝ, Tendsto (fun L : ℕ => Real.log (EL L lam) / (L : ℝ)) atTop (𝓝 (psi lam))) ∧
      ∀ lam c d : ℝ, 0 < lam → 0 < c → (psi lam + c) / lam < d →
        ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L →
          volume (devSet L d) < ENNReal.ofReal (Real.exp (-c * L)) := by
  choose psi hpsi using EL_rate_exists
  refine ⟨psi, rate_convex psi hpsi, hpsi, fun lam c d hlam _hc hd => ?_⟩
  obtain ⟨theta, htheta, hdev⟩ := large_deviation_rate hlam.le
  have heq : psi lam = theta := tendsto_nhds_unique (hpsi lam) htheta
  apply hdev d c
  rw [← heq]
  have h := (div_lt_iff₀ hlam).mp hd
  nlinarith


/-- The sublevel sets of the quotient used in Section 7 p.185 are intervals. -/
theorem ratio_quasiconvex {psi : ℝ → ℝ} (hpsi : ConvexOn ℝ Set.univ psi) (c : ℝ) :
    QuasiconvexOn ℝ (Set.Ioi 0) (fun lam : ℝ => (psi lam + c) / lam) := by
  intro r x hx y hy a b ha hb hab
  have hz : 0 < a * x + b * y := by
    simpa only [smul_eq_mul, Set.mem_Ioi] using (convex_Ioi (0 : ℝ)) hx.1 hy.1 ha hb hab
  refine ⟨hz, ?_⟩
  simp only [smul_eq_mul]
  apply (div_le_iff₀ hz).mpr
  have hx' := (div_le_iff₀ hx.1).mp hx.2
  have hy' := (div_le_iff₀ hy.1).mp hy.2
  have h := hpsi.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at h
  calc psi (a * x + b * y) + c
      = psi (a * x + b * y) + (a + b) * c := by rw [hab, one_mul]
    _ ≤ a * psi x + b * psi y + (a + b) * c := by linarith
    _ = a * (psi x + c) + b * (psi y + c) := by ring
    _ ≤ a * (r * x) + b * (r * y) := add_le_add
      (mul_le_mul_of_nonneg_left hx' ha) (mul_le_mul_of_nonneg_left hy' hb)
    _ = r * (a * x + b * y) := by ring


/-- The minimum bracket justified by convexity in Section 7 p.185. -/
theorem ratio_minimum_bracket {psi : ℝ → ℝ} (hpsi : ConvexOn ℝ Set.univ psi)
    (c : ℝ) {l1 l2 l3 : ℝ} (hl1 : 0 < l1) (h12 : l1 < l2) (h23 : l2 < l3)
    (hleft : (psi l2 + c) / l2 < (psi l1 + c) / l1)
    (hright : (psi l2 + c) / l2 < (psi l3 + c) / l3) :
    ∃ lam ∈ Set.Icc l1 l3, ∀ t : ℝ, 0 < t →
      (psi lam + c) / lam ≤ (psi t + c) / t := by
  let f : ℝ → ℝ := fun t => (psi t + c) / t
  have hq : QuasiconvexOn ℝ (Set.Ioi 0) f := ratio_quasiconvex hpsi c
  have hcont : Continuous psi := by
    simpa only [interior_univ, continuousOn_univ] using hpsi.continuousOn_interior
  have hf : ContinuousOn f (Set.Icc l1 l3) := by
    apply (hcont.continuousOn.add continuousOn_const).div continuousOn_id
    intro t ht
    exact (lt_of_lt_of_le hl1 ht.1).ne'
  obtain ⟨lam, hlam, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨l2, h12.le, h23.le⟩ hf
  refine ⟨lam, hlam, fun t ht => ?_⟩
  have h2 : 0 < l2 := hl1.trans h12
  have hm2 : f lam ≤ f l2 := hmin ⟨h12.le, h23.le⟩
  have hbetween {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hxz : x ≤ z) (hzy : z ≤ y) :
      f z ≤ max (f x) (f y) :=
    ((hq (max (f x) (f y))).ordConnected.out ⟨hx, le_max_left _ _⟩
      ⟨hy, le_max_right _ _⟩ ⟨hxz, hzy⟩).2
  by_cases htl : l1 ≤ t
  · by_cases htu : t ≤ l3
    · exact hmin ⟨htl, htu⟩
    · have h := hbetween h2 ht h23.le (le_of_not_ge htu)
      have hb : f l2 ≤ f t := by
        by_contra hn
        have he : max (f l2) (f t) = f l2 := max_eq_left (le_of_not_ge hn)
        rw [he] at h
        exact (not_le_of_gt hright) h
      exact hm2.trans hb
  · have h := hbetween ht h2 (le_of_not_ge htl) h12.le
    have hb : f l2 ≤ f t := by
      by_contra hn
      have he : max (f t) (f l2) = f l2 := max_eq_right (le_of_not_ge hn)
      rw [he] at h
      exact (not_le_of_gt hleft) h
    exact hm2.trans hb


/-- Corollary 1 on p.185 with the certified threshold three fourths, stated with a
measurable exceptional set and a positive constant. -/
theorem cor1_exceptional_set (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∃ E : Set ℝ,
      MeasurableSet E ∧ E ⊆ Set.Icc (0 : ℝ) 1 ∧
      volume E ≤ ENNReal.ofReal (C / (Real.sqrt N * (Nat.log 2 N : ℝ) ^ B)) ∧
      ∀ α ∈ Set.Icc (0 : ℝ) 1, α ∉ E →
        ‖Gpaper (Nat.log 2 N) α‖ ≤ (3 / 4 : ℝ) * (Nat.log 2 N : ℝ) := by
  have hG (L : ℕ) : Continuous (Gpaper L) := by unfold Gpaper; fun_prop
  obtain ⟨C, hC⟩ := cor1_N B
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun N hN => ?_⟩
  refine ⟨{x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℝ) < ‖Gpaper (Nat.log 2 N) x‖},
    measurableSet_Icc.inter ((isOpen_lt continuous_const (hG _).norm).measurableSet),
    fun x hx => hx.1, ?_, ?_⟩
  · exact (hC N hN).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
  · intro x hx hnot
    exact le_of_not_gt fun hlt => hnot ⟨hx, hlt⟩


/-- The weighted exceptional measure tends to zero. This is the auxiliary consequence of
Corollary 1 on p.185 used before display 10.6 on p.191, with the certified threshold three fourths. -/
theorem cor1_N_weighted_small (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      Real.sqrt N * (Nat.log 2 N : ℝ) ^ B * volume.real {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
          ‖Gpaper (Nat.log 2 N) α‖} ≤ ε := by
  let E : ℕ → Set ℝ := fun N => {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
          ‖Gpaper (Nat.log 2 N) α‖}
  change ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    Real.sqrt N * (Nat.log 2 N : ℝ) ^ B * volume.real (E N) ≤ ε
  obtain ⟨C, hC⟩ := cor1_N (B + 1)
  let D := max C 1
  refine ⟨max 2 (2 ^ ⌈D / ε⌉₊), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hL1 : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) hN2
  have hL : (0 : ℝ) < Nat.log 2 N := by exact_mod_cast hL1
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  have hden : (0 : ℝ) < Real.sqrt N * (Nat.log 2 N : ℝ) ^ (B + 1) := by positivity
  have hvol : volume.real (E N) ≤ D / (Real.sqrt N * (Nat.log 2 N : ℝ) ^ (B + 1)) := by
    apply ENNReal.toReal_le_of_le_ofReal (by dsimp [D]; positivity)
    exact (hC N hN2).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) hden.le))
  have hlog : ⌈D / ε⌉₊ ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num) (le_trans (le_max_right _ _) hN)
  have hCeps : D ≤ ε * (Nat.log 2 N : ℝ) := by
    have hceil : D / ε ≤ (⌈D / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hlog' : (⌈D / ε⌉₊ : ℝ) ≤ Nat.log 2 N := by exact_mod_cast hlog
    exact (div_le_iff₀ hε).mp (hceil.trans hlog') |>.trans_eq (mul_comm _ _)
  apply (mul_le_mul_iff_left₀ hL).mp
  calc (Real.sqrt N * (Nat.log 2 N : ℝ) ^ B * volume.real (E N)) * (Nat.log 2 N : ℝ)
      = volume.real (E N) * (Real.sqrt N * (Nat.log 2 N : ℝ) ^ (B + 1)) := by
        rw [pow_succ]; ring
    _ ≤ D := (le_div_iff₀ hden).mp hvol
    _ ≤ ε * (Nat.log 2 N : ℝ) := hCeps


/-- The little o estimate before display 10.6 on p.191. Taking B equal six gives the
power used in that display. The exceptional set uses the certified threshold three fourths. -/
theorem cor1_N_little_o (B : ℕ) :
    (fun N : ℕ => volume.real {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
          ‖Gpaper (Nat.log 2 N) α‖}) =o[atTop]
      (fun N : ℕ => 1 / (Real.sqrt N * (Nat.log 2 N : ℝ) ^ B)) := by
  let E : ℕ → Set ℝ := fun N => {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
          ‖Gpaper (Nat.log 2 N) α‖}
  change (fun N : ℕ => volume.real (E N)) =o[atTop]
    (fun N : ℕ => 1 / (Real.sqrt N * (Nat.log 2 N : ℝ) ^ B))
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨N0, hN0⟩ := cor1_N_weighted_small B hε
  filter_upwards [eventually_ge_atTop (max 2 N0)] with N hN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hL1 : 1 ≤ Nat.log 2 N := Nat.log_pos (by norm_num) hN2
  have hL : (0 : ℝ) < Nat.log 2 N := by exact_mod_cast hL1
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  have hden : (0 : ℝ) < Real.sqrt N * (Nat.log 2 N : ℝ) ^ B := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (Real.sqrt N * (Nat.log 2 N : ℝ) ^ B))]
  rw [mul_one_div, le_div_iff₀ hden]
  convert hN0 N (le_trans (le_max_right _ _) hN) using 1
  ring


/-- The final scalar absorption in display 10.6 on p.191. The factor N to power three halves
is written as N times sqrt N. The preceding GRH bound for the prime sum is a separate input. -/
theorem exceptional_error_small {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      C * volume.real {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
          ‖Gpaper (Nat.log 2 N) α‖} * (N : ℝ) * Real.sqrt N *
          (Nat.log 2 N : ℝ) ^ 4 * (Nat.log 2 N : ℝ) ^ (2 * k) ≤
        ε * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by
  let E : ℕ → Set ℝ := fun N => {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
          ‖Gpaper (Nat.log 2 N) α‖}
  change ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    C * volume.real (E N) * (N : ℝ) * Real.sqrt N * (Nat.log 2 N : ℝ) ^ 4 *
      (Nat.log 2 N : ℝ) ^ (2 * k) ≤ ε * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)
  obtain ⟨N0, hN0⟩ := cor1_N_weighted_small 6 (ε := ε / (C + 1)) (by positivity)
  refine ⟨N0, fun N hN => ?_⟩
  have hn := hN0 N hN
  have hp : 0 ≤ Real.sqrt N * (Nat.log 2 N : ℝ) ^ 6 * volume.real (E N) := by positivity
  have hbound : C * (Real.sqrt N * (Nat.log 2 N : ℝ) ^ 6 * volume.real (E N)) ≤ ε := by
    calc _ ≤ (C + 1) * (Real.sqrt N * (Nat.log 2 N : ℝ) ^ 6 * volume.real (E N)) := by nlinarith
      _ ≤ (C + 1) * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = ε := by field_simp
  have he : 2 * k = (2 * k - 2) + 2 := by omega
  calc _ = (C * (Real.sqrt N * (Nat.log 2 N : ℝ) ^ 6 * volume.real (E N))) *
      ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
        conv_lhs => rw [he, pow_add]
        ring
    _ ≤ ε * ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := by ring


/-- The shifted sum identity between Section 4 p.172 and Section 8 p.186. -/
theorem Gpaper_eq_Gpow (L : ℕ) (α : ℝ) : Gpaper L α = Gpow L (2 * α) := by
  unfold Gpaper Gpow
  apply sum_congr rfl
  intro m hm
  congr 1
  push_cast
  ring


/-- The trivial bound for the paper sum used in p.191 display 10.6. -/
theorem norm_Gpaper_le (L : ℕ) (α : ℝ) : ‖Gpaper L α‖ ≤ L := by
  rw [Gpaper_eq_Gpow]
  exact LeanLab.Linnik.Decomp1536a.norm_GL_le L (2 * α)


/-- The exceptional minor arc integral of p.191 display 10.6.
CONDITIONAL ON the supplied squared pointwise bound from p.171 display 2.10.
The measurable sets A represent minor arcs on the chosen unit interval. No prime sum estimate is asserted here. -/
theorem exceptional_integral_small {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (k : ℕ) (hk : 1 ≤ k) (S : ℕ → ℝ → ℂ) (hcont : ∀ N, Continuous (S N))
    (A : ℕ → Set ℝ) (hA : ∀ N, MeasurableSet (A N))
    (hS : ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N → ∀ α ∈ A N,
      ‖S N α‖ ^ 2 ≤ C * (N : ℝ) * Real.sqrt N * (Nat.log 2 N : ℝ) ^ 4) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∫ α in A N ∩ {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧
          (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) < ‖Gpaper (Nat.log 2 N) x‖},
        ‖S N α * Gpaper (Nat.log 2 N) α ^ k‖ ^ 2) ≤
          ε * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by
  obtain ⟨N1, hS⟩ := hS
  obtain ⟨N0, hsmall⟩ := exceptional_error_small hC hε k hk
  refine ⟨max N0 N1, fun N hN => ?_⟩
  let E : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) 1 ∧
    (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) < ‖Gpaper (Nat.log 2 N) x‖}
  let f : ℝ → ℝ := fun α => ‖S N α * Gpaper (Nat.log 2 N) α ^ k‖ ^ 2
  let M : ℝ := C * (N : ℝ) * Real.sqrt N * (Nat.log 2 N : ℝ) ^ 4 *
    (Nat.log 2 N : ℝ) ^ (2 * k)
  change (∫ α in A N ∩ E, f α) ≤ ε * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2)
  have hg : Continuous (Gpaper (Nat.log 2 N)) := by unfold Gpaper; fun_prop
  have hsN := hcont N
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hE : MeasurableSet E := measurableSet_Icc.inter
    ((isOpen_lt continuous_const hg.norm).measurableSet)
  have hEfin : volume E ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono fun x hx => hx.1)
  have hfin : volume (A N ∩ E) ≠ ⊤ :=
    ne_top_of_le_ne_top hEfin (measure_mono Set.inter_subset_right)
  have hi : IntegrableOn f (A N ∩ E) :=
    hf.integrableOn_Icc.mono_set (fun x hx => hx.2.1)
  have hconst : IntegrableOn (fun _ : ℝ => M) (A N ∩ E) := integrableOn_const hfin
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpt (α : ℝ) (hα : α ∈ A N ∩ E) : f α ≤ M := by
    calc f α = ‖S N α‖ ^ 2 * ‖Gpaper (Nat.log 2 N) α‖ ^ (2 * k) := by
          dsimp [f]
          simp only [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm]
      _ ≤ (C * (N : ℝ) * Real.sqrt N * (Nat.log 2 N : ℝ) ^ 4) *
          (Nat.log 2 N : ℝ) ^ (2 * k) :=
        mul_le_mul (hS N (le_trans (le_max_right _ _) hN) α hα.1)
          (pow_le_pow_left₀ (norm_nonneg _) (norm_Gpaper_le _ _) _) (by positivity) (by positivity)
      _ = M := rfl
  calc (∫ α in A N ∩ E, f α) ≤ ∫ _ in A N ∩ E, M :=
        setIntegral_mono_on hi hconst ((hA N).inter hE) hpt
    _ = volume.real (A N ∩ E) * M := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ volume.real E * M :=
      mul_le_mul_of_nonneg_right (measureReal_mono Set.inter_subset_right hEfin) hM
    _ = C * volume.real E * (N : ℝ) * Real.sqrt N * (Nat.log 2 N : ℝ) ^ 4 *
        (Nat.log 2 N : ℝ) ^ (2 * k) := by dsimp [M]; ring
    _ ≤ ε * N * (Nat.log 2 N : ℝ) ^ (2 * k - 2) :=
      hsmall N (le_trans (le_max_left _ _) hN)

end LeanLab.Linnik.Decomp1536c
