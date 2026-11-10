/-
Split of `lemma74` into smaller leaves.

The target is the smoothed explicit formula for `∑ Λ(n) χ(n) Ψ(n)` for a primitive
character, with the pole term at `s = 1` subtracted and the zeros of the Dirichlet
L-function of `χ` added back, up to an error `C * S ^ (-A)` depending only on `A` and
on the seminorm bounds `M` of the kernel `Ψ`, whose support starts at `S`.

The split follows the proof's shape.  One leaf is the elementary kernel estimate: the
Mellin transform of a kernel supported in `Ioi S` decays like `S ^ σ` times
`(1 + |t|) ^ (-k)`.  One leaf is the contour shift on a rectangle, an identity: the
arithmetic side equals the boundary integral of the logarithmic derivative against the
Mellin transform, with the zeros inside the rectangle counted with multiplicity.  Two
leaves bound the two kinds of boundary pieces, the shifted vertical line and the two
horizontal pieces.  One leaf bounds what the truncation at height `T` and at the
abscissa `-B` leaves out of the zero sum.

The error bounds are stated with `C * S ^ (-B)` for a freely chosen `B`, because the
assembly then takes `B = A + 2` and uses `S ^ (-(A + 2)) ≤ S ^ (-A)` for `S ≥ 1`.  The
assembly uses the identity, the two boundary bounds and the zero tail bound; the kernel
estimate is the input those two boundary bounds need.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

open scoped ComplexConjugate

/-! ## Elementary Mellin estimates -/

/-- Absolute Mellin bound on a negative real line, derived from page 27. -/
theorem mellinR_negative_bound469 (Ψ : ℝ → ℝ) (S C : ℝ) (hS : 0 < S)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (hb : ∀ x, |Ψ x| ≤ C)
    (s : ℂ) (hs : s.re < 0) :
    ‖mellinR Ψ s‖ ≤ C * (-(S ^ s.re) / s.re) := by
  have heq : mellinR Ψ s = ∫ x in Set.Ioi S, (Ψ x : ℂ) * (x : ℂ) ^ (s - 1) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Set.Ioi_subset_Ioi hS.le)
    intro x hx
    have hz : Ψ x = 0 := by
      by_contra hn
      exact hx.2 (hsupp (subset_tsupport Ψ hn))
    simp [hz]
  rw [heq]
  calc
    _ ≤ ∫ x in Set.Ioi S, C * x ^ (s.re - 1) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 1 < -1) hS).const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos (hS.trans hx)]
      simpa using mul_le_mul_of_nonneg_right (hb x)
        (Real.rpow_nonneg (le_of_lt (hS.trans hx)) (s.re - 1))
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hS]
      simp

/-- The zeroth derivative case of the sealed Mellin leaf on page 27. -/
theorem mellinR_decay_zero469 (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ)
    (hS : 1 ≤ S) (hsupp : tsupport Ψ ⊆ Set.Ioi S)
    (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
    (σ t : ℝ) (hσ : σ ≤ -1) :
    ‖mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M 0 * S ^ σ := by
  have hM : 0 ≤ M 0 := le_trans (abs_nonneg _) (hb 0 0)
  have h := mellinR_negative_bound469 Ψ S (M 0) (by linarith) hsupp
    (by simpa using hb 0) ((σ : ℂ) + (t : ℂ) * Complex.I) (by simp; linarith)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hM
  have hp := Real.rpow_nonneg (by linarith : 0 ≤ S) σ
  apply (div_le_iff_of_neg (by linarith : σ < 0)).2
  nlinarith

/-- Mellin dilation identity from Mathlib, used to audit page 27. -/
theorem mellinR_dilation469 (Ψ : ℝ → ℝ) (s : ℂ) (a : ℝ) (ha : 0 < a) :
    mellinR (fun x => Ψ (a * x)) s = (a : ℂ) ^ (-s) * mellinR Ψ s := by
  simpa [mellinR, mellin, smul_eq_mul, mul_comm] using
    mellin_comp_mul_left (fun x => (Ψ x : ℂ)) s ha

/-- A positive negative-second Mellin transform contradicts the proposed first derivative scaling. Derived audit of page 27. -/
theorem mellinR_dilation_obstruction469 (Ψ : ℝ → ℝ) (N : ℕ → ℝ)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi (1 : ℝ))
    (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ N k)
    (hd : 0 < ‖mellinR Ψ (-2)‖) :
    ∃ (M : ℕ → ℝ) (S : ℝ) (Φ : ℝ → ℝ),
      1 ≤ S ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ Set.Ioi S ∧ (∀ k x, |iteratedDeriv k Φ x| ≤ M k) ∧
      ((2 : ℝ) ^ (1 : ℕ) * M 1) * S ^ (-2 : ℝ) / (1 + |(0 : ℝ)|) ^ (1 : ℕ) <
        ‖mellinR Φ (((-2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ := by
  have hN : 0 ≤ N 1 := le_trans (abs_nonneg _) (hb 1 0)
  let d := ‖mellinR Ψ (-2)‖
  let a := min 1 (d / (4 * (N 1 + 1)))
  have ha : 0 < a := lt_min zero_lt_one (div_pos hd (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have had : a ≤ d / (4 * (N 1 + 1)) := min_le_right _ _
  have hsmall : 2 * a * N 1 < d := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * (N 1 + 1))).mp had
    nlinarith
  refine ⟨fun k => a ^ k * N k, 1 / a, fun x => Ψ (a * x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ ha).2 (by simpa using ha1)
  · exact hsm.comp (contDiff_const.mul contDiff_id)
  · exact hcs.comp_homeomorph (Homeomorph.mulLeft₀ a ha.ne')
  · intro x hx
    have hm : a * x ∈ tsupport Ψ :=
      tsupport_comp_subset_preimage Ψ (continuous_const.mul continuous_id) hx
    exact (div_lt_iff₀ ha).2 (by simpa [mul_comm] using hsupp hm)
  · intro k x
    rw [iteratedDeriv_comp_const_mul (hsm.of_le (by exact_mod_cast le_top)) a]
    dsimp
    rw [abs_mul, abs_of_nonneg (pow_nonneg ha.le k)]
    exact mul_le_mul_of_nonneg_left (hb k (a * x)) (pow_nonneg ha.le k)
  · have heq : mellinR (fun x => Ψ (a * x)) (-2) =
        (a : ℂ) ^ (2 : ℕ) * mellinR Ψ (-2) := by
      simpa [mellinR, mellin, smul_eq_mul, mul_comm] using
        mellin_comp_mul_left (fun x => (Ψ x : ℂ)) (-2) ha
    simp only [pow_one, abs_zero, add_zero, div_one, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_zero, zero_mul, add_zero]
    rw [heq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    have hp : (1 / a) ^ (-2 : ℝ) = a ^ (2 : ℕ) := by
      rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg_natCast,
        zpow_neg, zpow_natCast]
      simp
    rw [hp]
    change 2 * (a * N 1) * a ^ 2 < a ^ 2 * d
    nlinarith [sq_pos_of_pos ha]

/-- A smooth compactly supported kernel above one has positive negative-second Mellin norm. Nonvacuity for the page 27 audit. -/
theorem mellinR_positive_witness469 : ∃ (Ψ : ℝ → ℝ) (N : ℕ → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
    tsupport Ψ ⊆ Set.Ioi (1 : ℝ) ∧ (∀ k x, |iteratedDeriv k Ψ x| ≤ N k) ∧
    0 < ‖mellinR Ψ (-2)‖ := by
  let b : ContDiffBump (3 : ℝ) :=
    { rIn := 1, rOut := 3 / 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  have hbsupp : tsupport (b : ℝ → ℝ) ⊆ Set.Ioi (1 : ℝ) := by
    intro x hx
    rw [b.tsupport_eq] at hx
    have hdist : |x - 3| ≤ 3 / 2 := by simpa [Real.dist_eq] using hx
    have := (abs_le.mp hdist).1
    change 1 < x
    linarith
  have hbpos : 0 < ∫ x : ℝ, (b x : ℝ) := by
    apply b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      b.hasCompactSupport b.nonneg' (x := 3)
    rw [b.one_of_mem_closedBall]
    · norm_num
    · simp [b]
  let Ψ : ℝ → ℝ := fun x => x ^ 3 * b x
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ :=
    (contDiff_id.pow 3).mul b.contDiff
  have hcs : HasCompactSupport Ψ := b.hasCompactSupport.mul_left
  have hh := hcs.exists_bound_iteratedFDeriv hsm
  choose N hN using hh
  refine ⟨Ψ, N, hsm, hcs, ?_, ?_, ?_⟩
  · exact tsupport_mul_subset_right.trans hbsupp
  · intro k x
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      (hN k).2 k le_rfl x
  · have heq : mellinR Ψ (-2) = (↑(∫ x : ℝ, (b x : ℝ)) : ℂ) := by
      unfold mellinR
      calc
        _ = ∫ x in Set.Ioi (0 : ℝ), (b x : ℂ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          dsimp only [Ψ]
          have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
          rw [show (-2 : ℂ) - 1 = ((-3 : ℤ) : ℂ) by norm_num,
            Complex.cpow_intCast, zpow_neg, zpow_ofNat, Complex.ofReal_mul, Complex.ofReal_pow]
          field_simp
        _ = _ := by
          rw [integral_complex_ofReal]
          congr 1
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have hx' : x ≤ 0 := le_of_not_gt hx
          apply b.zero_of_le_dist
          simp only [Real.dist_eq]
          change 3 / 2 ≤ |x - 3|
          rw [abs_of_nonpos (by linarith : x - 3 ≤ 0)]
          linarith
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
    exact hbpos

/-- The sealed first derivative estimate fails for an admissible smooth compact kernel.
This is a statement audit of the proposed split, not a claim about equation 7.12 on page 27. -/
theorem leaf_mellin_decay74_counterexample469 :
    ∃ (M : ℕ → ℝ) (S : ℝ) (Φ : ℝ → ℝ),
      1 ≤ S ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ Set.Ioi S ∧ (∀ k x, |iteratedDeriv k Φ x| ≤ M k) ∧
      ((2 : ℝ) ^ (1 : ℕ) * M 1) * S ^ (-2 : ℝ) / (1 + |(0 : ℝ)|) ^ (1 : ℕ) <
        ‖mellinR Φ (((-2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)‖ := by
  obtain ⟨Ψ, N, hsm, hcs, hsupp, hb, hd⟩ := mellinR_positive_witness469
  exact mellinR_dilation_obstruction469 Ψ N hsm hcs hsupp hb hd

/-- One Mellin integration by parts on a positive finite interval. Derived from page 27. -/
theorem mellin_interval_parts469 (Ψ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hsm : ContDiff ℝ 1 Ψ) (s : ℂ) :
    s * (∫ x in a..b, (Ψ x : ℂ) * (x : ℂ) ^ (s - 1)) =
      (Ψ b : ℂ) * (b : ℂ) ^ s - (Ψ a : ℂ) * (a : ℂ) ^ s -
        ∫ x in a..b, (↑(deriv Ψ x) : ℂ) * (x : ℂ) ^ s := by
  have hpow : ContinuousOn (fun x : ℝ => (x : ℂ) ^ s) (Set.uIcc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply Complex.continuousAt_ofReal_cpow_const
    right
    have hx' : a ≤ x := (Set.uIcc_of_le hab ▸ hx).1
    exact ne_of_gt (ha.trans_le hx')
  have hpow' : ContinuousOn (fun x : ℝ => s * (x : ℂ) ^ (s - 1)) (Set.uIcc a b) := by
    apply continuousOn_const.mul
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply Complex.continuousAt_ofReal_cpow_const
    right
    have hx' : a ≤ x := (Set.uIcc_of_le hab ▸ hx).1
    exact ne_of_gt (ha.trans_le hx')
  have hh := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x => (Ψ x : ℂ)) (v := fun x : ℝ => (x : ℂ) ^ s)
    (u' := fun x => (↑(deriv Ψ x) : ℂ)) (v' := fun x : ℝ => s * (x : ℂ) ^ (s - 1))
    ((Complex.continuous_ofReal.comp hsm.continuous).continuousOn) hpow
    (fun x hx => (hsm.differentiable (by norm_num)).differentiableAt.hasDerivAt.ofReal_comp)
    (fun x hx => by
      by_cases hs : s = 0
      · subst s
        simpa using hasDerivAt_const x (1 : ℂ)
      · exact hasDerivAt_ofReal_cpow_const
          (ne_of_gt (lt_of_lt_of_le ha (by simpa [min_eq_left hab] using hx.1.le))) hs)
    ((Complex.continuous_ofReal.comp (hsm.continuous_deriv (by norm_num))).intervalIntegrable a b)
    hpow'.intervalIntegrable
  convert hh using 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  ring
/-- Repeated Mellin integration by parts on a positive interval with vanishing endpoint jets. Derived from page 27. -/
theorem mellin_interval_iterated_parts469 (Ψ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (s : ℂ) (k : ℕ)
    (hz : ∀ j < k, iteratedDeriv j Ψ a = 0 ∧ iteratedDeriv j Ψ b = 0) :
    (∏ j ∈ Finset.range k, (s + (j : ℂ))) *
        (∫ x in a..b, (Ψ x : ℂ) * (x : ℂ) ^ (s - 1)) =
      (-1 : ℂ) ^ k * ∫ x in a..b,
        (↑(iteratedDeriv k Ψ x) : ℂ) * (x : ℂ) ^ (s + (k : ℂ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsmk : ContDiff ℝ 1 (iteratedDeriv k Ψ) := by
      apply (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp _).2
      exact hsm.of_le (by exact_mod_cast le_top)
    have hk := mellin_interval_parts469 (iteratedDeriv k Ψ) a b ha hab hsmk (s + k)
    have hz' := hz k (Nat.lt_succ_self k)
    simp only [hz'.1, hz'.2, Complex.ofReal_zero, zero_mul, sub_self, zero_sub] at hk
    have hi := ih (fun j hj => hz j (Nat.lt_succ_of_lt hj))
    rw [Finset.prod_range_succ]
    calc
      _ = (s + k) * ((∏ j ∈ Finset.range k, (s + (j : ℂ))) *
          (∫ x in a..b, (Ψ x : ℂ) * (x : ℂ) ^ (s - 1))) := by ring
      _ = (-1 : ℂ) ^ k * ((s + k) * (∫ x in a..b,
          (↑(iteratedDeriv k Ψ x) : ℂ) * (x : ℂ) ^ (s + k - 1))) := by rw [hi]; ring
      _ = (-1 : ℂ) ^ k * (-(∫ x in a..b,
          (↑(deriv (iteratedDeriv k Ψ) x) : ℂ) * (x : ℂ) ^ (s + k))) := by rw [hk]
      _ = _ := by
        rw [pow_succ]
        simp only [iteratedDeriv_succ, Nat.cast_add, Nat.cast_one]
        rw [show s + ((k : ℂ) + 1) - 1 = s + k by ring]
        ring

/-- Restrict the Mellin integral to a positive interval containing the support. Derived from page 27. -/
theorem mellinR_finite_interval469 (Ψ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hsupp : tsupport Ψ ⊆ Set.Ioc a b) (s : ℂ) :
    mellinR Ψ s = ∫ x in a..b, (Ψ x : ℂ) * (x : ℂ) ^ (s - 1) := by
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
  · intro x hx
    exact ha.trans hx.1
  · intro x hx
    have hz : Ψ x = 0 := by
      by_contra hn
      exact hx.2 (hsupp (subset_tsupport Ψ hn))
    simp [hz]
/-- Repeated integration by parts for the full Mellin transform shifts its argument by the derivative order. Derived from page 27. -/
theorem mellinR_iterated_parts469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S) (s : ℂ) (k : ℕ) :
    (∏ j ∈ Finset.range k, (s + (j : ℂ))) * mellinR Ψ s =
      (-1 : ℂ) ^ k * mellinR (iteratedDeriv k Ψ) (s + (k : ℂ)) := by
  obtain ⟨u, hu⟩ := hcs.isCompact.bddAbove
  let R := max (S + 1) (u + 1)
  have hSR : S ≤ R := by dsimp [R]; linarith [le_max_left (S + 1) (u + 1)]
  have hR : u < R := by dsimp [R]; linarith [le_max_right (S + 1) (u + 1)]
  have hd : ∀ j, tsupport (iteratedDeriv j Ψ) ⊆ tsupport Ψ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih
  have hi : ∀ j, tsupport (iteratedDeriv j Ψ) ⊆ Set.Ioc S R := by
    intro j x hx
    exact ⟨hsupp (hd j hx), (hu (hd j hx)).trans hR.le⟩
  have hz : ∀ j < k, iteratedDeriv j Ψ S = 0 ∧ iteratedDeriv j Ψ R = 0 := by
    intro j hj
    constructor
    · by_contra hn
      exact lt_irrefl S (hsupp (hd j (subset_tsupport _ hn)))
    · by_contra hn
      exact (not_le_of_gt hR) (hu (hd j (subset_tsupport _ hn)))
  rw [mellinR_finite_interval469 Ψ S R hS hSR (by simpa using hi 0),
    mellinR_finite_interval469 (iteratedDeriv k Ψ) S R hS hSR (hi k)]
  exact mellin_interval_iterated_parts469 Ψ S R hS hSR hsm s k hz

/-- Valid repeated integration by parts decay with the shifted support exponent.
Derived calculus for page 27. The sealed leaf is preserved separately. -/
theorem mellinR_decay_shifted469 (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ) (hS : 1 ≤ S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
    (k : ℕ) (σ t : ℝ) (hσ : σ + (k : ℝ) ≤ -1) :
    ‖mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((2 : ℝ) ^ k * M k) * S ^ (σ + (k : ℝ)) / (1 + |t|) ^ k := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let P : ℂ := ∏ j ∈ Finset.range k, (z + (j : ℂ))
  have hM : 0 ≤ M k := le_trans (abs_nonneg _) (hb k 0)
  have hS0 : 0 < S := by linarith
  have hsuppk : tsupport (iteratedDeriv k Ψ) ⊆ Set.Ioi S := by
    have hd : ∀ j, tsupport (iteratedDeriv j Ψ) ⊆ tsupport Ψ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
    exact (hd k).trans hsupp
  have hparts := mellinR_iterated_parts469 Ψ S hS0 hsm hcs hsupp z k
  have heq : ‖P‖ * ‖mellinR Ψ z‖ = ‖mellinR (iteratedDeriv k Ψ) (z + (k : ℂ))‖ := by
    rw [← norm_mul]
    change ‖(∏ j ∈ Finset.range k, (z + (j : ℂ))) * mellinR Ψ z‖ = _
    rw [hparts, norm_mul, norm_pow]
    simp
  have hneg := mellinR_negative_bound469 (iteratedDeriv k Ψ) S (M k) hS0 hsuppk
    (hb k) (z + (k : ℂ)) (by dsimp [z]; simp; linarith)
  have hzr : (z + (k : ℂ)).re = σ + (k : ℝ) := by simp [z]
  rw [hzr] at hneg
  have hquot : -(S ^ (σ + (k : ℝ))) / (σ + (k : ℝ)) ≤ S ^ (σ + (k : ℝ)) := by
    have hp := Real.rpow_nonneg hS0.le (σ + (k : ℝ))
    apply (div_le_iff_of_neg (by linarith : σ + (k : ℝ) < 0)).2
    nlinarith
  have hbound : ‖P‖ * ‖mellinR Ψ z‖ ≤ M k * S ^ (σ + (k : ℝ)) :=
    heq.le.trans (hneg.trans (mul_le_mul_of_nonneg_left hquot hM))
  let q : ℝ := (1 + |t|) / 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hlower : q ^ k ≤ ‖P‖ := by
    have hh : (∏ j ∈ Finset.range k, q) ≤ ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact hq.le
      · intro j hj
        have hj' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
        have hre := Complex.abs_re_le_norm (z + (j : ℂ))
        have him := Complex.abs_im_le_norm (z + (j : ℂ))
        have hreal : (z + (j : ℂ)).re = σ + (j : ℝ) := by simp [z]
        have himag : (z + (j : ℂ)).im = t := by simp [z]
        rw [hreal, abs_of_nonpos (by linarith)] at hre
        rw [himag] at him
        dsimp [q]
        linarith
    simpa [P, norm_prod] using hh
  have hb' : q ^ k * ‖mellinR Ψ z‖ ≤ M k * S ^ (σ + (k : ℝ)) :=
    (mul_le_mul_of_nonneg_right hlower (norm_nonneg _)).trans hbound
  have hden : 0 < (1 + |t|) ^ k := by positivity
  apply (le_div_iff₀ hden).2
  have hqp : q ^ k = (1 + |t|) ^ k / 2 ^ k := by dsimp [q]; rw [div_pow]
  rw [hqp] at hb'
  have hh := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).mp
    (show (‖mellinR Ψ z‖ * (1 + |t|) ^ k) / 2 ^ k ≤ M k * S ^ (σ + (k : ℝ)) by
      convert hb' using 1
      ring)
  change ‖mellinR Ψ z‖ * (1 + |t|) ^ k ≤ _
  nlinarith

/-- A real kernel has conjugate symmetric Mellin transform. Derived calculus for page 27. -/
theorem mellinR_conj469 (Ψ : ℝ → ℝ) (s : ℂ) : mellinR Ψ (conj s) = conj (mellinR Ψ s) := by
  unfold mellinR
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have ha : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  have h := Complex.cpow_conj (x : ℂ) (s - 1) ha
  simpa using h

/-- Conjugate symmetry passes to the total logarithmic derivative. Derived audit for page 27. -/
theorem logDeriv_conj469 (f : ℂ → ℂ) (hf : ∀ z, f (conj z) = conj (f z)) (s : ℂ) :
    logDeriv f (conj s) = conj (logDeriv f s) := by
  have heq : conj ∘ f ∘ conj = f := by
    funext z
    simp [Function.comp_def, hf]
  have hd : deriv f (conj s) = conj (deriv f s) := by
    have hh := congrFun (deriv_conj_conj (f := f)) (conj s)
    rw [heq] at hh
    simpa using hh
  simp [logDeriv, hd, hf]

/-- The plus pairing in the proposed horizontal contour has zero real part for a conjugate symmetric integrand. Derived audit for page 27. -/
theorem conjugate_horizontal_re469 (F : ℂ → ℂ) (hF : ∀ z, F (conj z) = conj (F z)) (B T : ℝ) :
    ((1 / (2 * Real.pi * Complex.I)) *
      (∫ σ in (-B)..(2 : ℝ),
        F ((σ : ℂ) + (T : ℂ) * Complex.I) + F ((σ : ℂ) - (T : ℂ) * Complex.I))).re = 0 := by
  let Z : ℂ := ∫ σ in (-B)..(2 : ℝ),
    F ((σ : ℂ) + (T : ℂ) * Complex.I) + F ((σ : ℂ) - (T : ℂ) * Complex.I)
  have hconj : conj Z = Z := by
    dsimp [Z]
    simp only [intervalIntegral, map_sub, ← integral_conj]
    congr 1 <;> apply setIntegral_congr_fun measurableSet_Ioc <;> intro x hx <;> dsimp only
    all_goals
      have hp : conj ((x : ℂ) + (T : ℂ) * Complex.I) = (x : ℂ) - (T : ℂ) * Complex.I := by simp [sub_eq_add_neg]
      have hm : conj ((x : ℂ) - (T : ℂ) * Complex.I) = (x : ℂ) + (T : ℂ) * Complex.I := by simp [sub_eq_add_neg]
      rw [map_add, ← hF, ← hF, hp, hm]
      exact add_comm _ _
  have hi : Z.im = 0 := by
    have hh := congrArg Complex.im hconj
    simp only [Complex.conj_im] at hh
    linarith
  change ((1 / (2 * Real.pi * Complex.I)) * Z).re = 0
  simp [Complex.mul_re, hi]

/-- At conductor one the proposed horizontal plus pairing has zero real part. Derived audit for page 27. -/
theorem horizontal_modOne_re469 (χ : DirichletCharacter ℂ 1) (Ψ : ℝ → ℝ) (B T : ℝ) :
    ((1 / (2 * Real.pi * Complex.I)) *
      (∫ σ in (-B)..(2 : ℝ),
        ((-(logDeriv (DirichletCharacter.LFunction χ)))
          ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) +
        (-(logDeriv (DirichletCharacter.LFunction χ)))
          ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))).re = 0 := by
  rw [DirichletCharacter.LFunction_modOne_eq]
  apply conjugate_horizontal_re469 (fun z => -(logDeriv riemannZeta z) * mellinR Ψ z)
  intro z
  rw [logDeriv_conj469 _ riemannZeta_conj, mellinR_conj469]
  simp

/-- Opposite orientations give a real horizontal contribution for a conjugate symmetric integrand. Derived audit for page 27. -/
theorem conjugate_horizontal_difference_im469 (F : ℂ → ℂ) (hF : ∀ z, F (conj z) = conj (F z)) (B T : ℝ) :
    ((1 / (2 * Real.pi * Complex.I)) *
      (∫ σ in (-B)..(2 : ℝ),
        F ((σ : ℂ) + (T : ℂ) * Complex.I) - F ((σ : ℂ) - (T : ℂ) * Complex.I))).im = 0 := by
  let Z : ℂ := ∫ σ in (-B)..(2 : ℝ),
    F ((σ : ℂ) + (T : ℂ) * Complex.I) - F ((σ : ℂ) - (T : ℂ) * Complex.I)
  have hconj : conj Z = -Z := by
    have heq : (fun x : ℝ => conj (F ((x : ℂ) + (T : ℂ) * Complex.I) -
        F ((x : ℂ) - (T : ℂ) * Complex.I))) =
        (fun x : ℝ => -(F ((x : ℂ) + (T : ℂ) * Complex.I) -
        F ((x : ℂ) - (T : ℂ) * Complex.I))) := by
      funext x
      have hp : conj ((x : ℂ) + (T : ℂ) * Complex.I) = (x : ℂ) - (T : ℂ) * Complex.I := by simp [sub_eq_add_neg]
      have hm : conj ((x : ℂ) - (T : ℂ) * Complex.I) = (x : ℂ) + (T : ℂ) * Complex.I := by simp
      rw [map_sub, ← hF, ← hF, hp, hm]
      ring
    calc
      conj Z = ∫ x in (-B)..(2 : ℝ), conj (F ((x : ℂ) + (T : ℂ) * Complex.I) -
          F ((x : ℂ) - (T : ℂ) * Complex.I)) := by
        simp only [Z, intervalIntegral]
        rw [integral_conj, integral_conj, map_sub]
      _ = ∫ x in (-B)..(2 : ℝ), -(F ((x : ℂ) + (T : ℂ) * Complex.I) -
          F ((x : ℂ) - (T : ℂ) * Complex.I)) := by rw [heq]
      _ = -Z := intervalIntegral.integral_neg
  have hr : Z.re = 0 := by
    have hh := congrArg Complex.re hconj
    simp only [Complex.conj_re, Complex.neg_re] at hh
    linarith
  change ((1 / (2 * Real.pi * Complex.I)) * Z).im = 0
  simp [Complex.mul_im, hr]

/-- Compact support away from zero makes every Mellin integral integrable. Derived from page 27. -/
theorem mellinR_integrable469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hc : Continuous Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S) (s : ℂ) :
    IntegrableOn (fun x : ℝ => (Ψ x : ℂ) * (x : ℂ) ^ (s - 1)) (Set.Ioi (0 : ℝ)) := by
  let f : ℝ → ℂ := fun x => (Ψ x : ℂ) * (x : ℂ) ^ (s - 1)
  have hcont : ContinuousOn f (tsupport Ψ) := by
    apply (Complex.continuous_ofReal.comp hc).continuousOn.mul
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply Complex.continuousAt_ofReal_cpow_const
    right
    exact ne_of_gt (hS.trans (hsupp hx))
  have hsub : Function.support f ⊆ tsupport Ψ := by
    intro x hx
    apply subset_tsupport Ψ
    intro hz
    apply hx
    simp [f, hz]
  have hi : IntegrableOn f (tsupport Ψ) := hcont.integrableOn_compact hcs
  exact ((integrableOn_iff_integrable_of_support_subset hsub).mp hi).integrableOn
open Asymptotics in
/-- The Mellin transform of a continuous compact kernel away from zero is entire. Derived from page 27. -/
theorem mellinR_differentiable469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hc : Continuous Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S) :
    Differentiable ℂ (mellinR Ψ) := by
  have htop : ∀ᶠ x in atTop, Ψ x = 0 := by
    obtain ⟨u, hu⟩ := hcs.isCompact.bddAbove
    filter_upwards [eventually_gt_atTop u] with x hx
    by_contra hn
    exact (not_le_of_gt hx) (hu (subset_tsupport Ψ hn))
  have hbot : ∀ᶠ x in 𝓝[>] (0 : ℝ), Ψ x = 0 := by
    filter_upwards [(eventually_lt_nhds hS).filter_mono nhdsWithin_le_nhds] with x hx
    by_contra hn
    exact (not_lt_of_gt hx) (hsupp (subset_tsupport Ψ hn))
  intro s
  have htop' : (fun x => (Ψ x : ℂ)) =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1))) := by
    apply IsBigO.of_bound 0
    filter_upwards [htop] with x hx
    simp [hx]
  have hbot' : (fun x => (Ψ x : ℂ)) =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(s.re - 1))) := by
    apply IsBigO.of_bound 0
    filter_upwards [hbot] with x hx
    simp [hx]
  have heq : mellin (Complex.ofReal ∘ Ψ) = mellinR Ψ := by
    funext z
    simp only [mellin, mellinR, Function.comp_def, smul_eq_mul, mul_comm]
  rw [← heq]
  exact mellin_differentiableAt_of_isBigO_rpow
      ((Complex.continuous_ofReal.comp hc).continuousOn.locallyIntegrableOn measurableSet_Ioi)
      htop' (by linarith : s.re < s.re + 1) hbot' (by linarith : s.re - 1 < s.re)

/-- Compact support makes the arithmetic kernel sum finite for arbitrary coefficients. Derived from equation 7.12 on page 27. -/
theorem summable_arithmetic_kernel469 (Ψ : ℝ → ℝ) (hcs : HasCompactSupport Ψ) (a : ℕ → ℂ) :
    Summable (fun n : ℕ => a n * (Ψ n : ℂ)) := by
  obtain ⟨u, hu⟩ := hcs.isCompact.bddAbove
  apply summable_of_ne_finset_zero (s := Finset.range (⌈u⌉₊ + 1))
  intro n hn
  have hnu : (u : ℝ) < n := by
    have hn' : ⌈u⌉₊ < n := by simpa using hn
    exact (Nat.le_ceil u).trans_lt (by exact_mod_cast hn')
  have hz : Ψ n = 0 := by
    by_contra hne
    exact (not_le_of_gt hnu) (hu (subset_tsupport Ψ hne))
  simp [hz]

/-- Exact negation of the proposed Mellin leaf, established without using its admission.
This audits the sealed split statement beside page 27, not equation 7.12. -/
theorem not_leaf_mellin_decay74_statement469 :
    ¬ (∀ (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ) (_hS : 1 ≤ S)
      (_hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (_hcs : HasCompactSupport Ψ)
      (_hsupp : tsupport Ψ ⊆ Set.Ioi S) (_hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
      (k : ℕ) (σ t : ℝ) (_hσ : σ + (k : ℝ) ≤ -1),
      ‖mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ((2 : ℝ) ^ k * M k) * S ^ σ / (1 + |t|) ^ k) := by
  intro h
  obtain ⟨M, S, Ψ, hS, hsm, hcs, hsupp, hb, hlt⟩ := leaf_mellin_decay74_counterexample469
  have hh := h M S Ψ hS hsm hcs hsupp hb 1 (-2) 0 (by norm_num)
  exact (not_lt_of_ge hh) hlt

/-- Every fixed vertical line has arbitrary power Mellin decay for a smooth compact kernel. Derived from page 27. -/
theorem mellinR_vertical_decay469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (σ : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / (1 + |t|) ^ k := by
  have hnorm (f : ℝ → ℝ) (s w : ℂ) (h : s.re = w.re) :
      (∫ x in Set.Ioi (0 : ℝ), ‖(f x : ℂ) * (x : ℂ) ^ (s - 1)‖) =
        ∫ x in Set.Ioi (0 : ℝ), ‖(f x : ℂ) * (x : ℂ) ^ (w - 1)‖ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [h]
  let K0 : ℝ := ∫ x in Set.Ioi (0 : ℝ), ‖(Ψ x : ℂ) * (x : ℂ) ^ ((σ : ℂ) - 1)‖
  let Kk : ℝ := ∫ x in Set.Ioi (0 : ℝ),
    ‖(↑(iteratedDeriv k Ψ x) : ℂ) * (x : ℂ) ^ (((σ + (k : ℝ) : ℝ) : ℂ) - 1)‖
  have hK0 : 0 ≤ K0 := integral_nonneg (fun x => norm_nonneg _)
  have hKk : 0 ≤ Kk := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨2 ^ k * (K0 + Kk), by positivity, ?_⟩
  intro t
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have h0 : ‖mellinR Ψ z‖ ≤ K0 := by
    apply (norm_integral_le_integral_norm _).trans_eq
    exact hnorm Ψ z (σ : ℂ) (by simp [z])
  have hk : ‖mellinR (iteratedDeriv k Ψ) (z + k)‖ ≤ Kk := by
    apply (norm_integral_le_integral_norm _).trans_eq
    exact hnorm (iteratedDeriv k Ψ) (z + k) ((σ + (k : ℝ) : ℝ) : ℂ) (by simp [z])
  have heq := congrArg norm (mellinR_iterated_parts469 Ψ S hS hsm hcs hsupp z k)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at heq
  have hden : 0 < (1 + |t|) ^ k := by positivity
  apply (le_div_iff₀ hden).2
  change ‖mellinR Ψ z‖ * (1 + |t|) ^ k ≤ 2 ^ k * (K0 + Kk)
  by_cases ht : |t| ≤ 1
  · have hp : (1 + |t|) ^ k ≤ (2 : ℝ) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc
      _ ≤ K0 * 2 ^ k := mul_le_mul h0 hp (by positivity) hK0
      _ ≤ _ := by nlinarith
  · have ht' : 1 ≤ |t| := (lt_of_not_ge ht).le
    have hprod : |t| ^ k ≤ ‖∏ j ∈ Finset.range k, (z + (j : ℂ))‖ := by
      have hh : (∏ j ∈ Finset.range k, |t|) ≤ ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact abs_nonneg _
        · intro j hj
          simpa [z] using Complex.abs_im_le_norm (z + (j : ℂ))
      simpa [norm_prod] using hh
    have hb : |t| ^ k * ‖mellinR Ψ z‖ ≤ Kk := by
      calc
        _ ≤ ‖∏ j ∈ Finset.range k, (z + (j : ℂ))‖ * ‖mellinR Ψ z‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ = ‖mellinR (iteratedDeriv k Ψ) (z + k)‖ := heq
        _ ≤ Kk := hk
    have hp : (1 + |t|) ^ k ≤ (2 : ℝ) ^ k * |t| ^ k := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc
      _ ≤ ‖mellinR Ψ z‖ * (2 ^ k * |t| ^ k) :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = 2 ^ k * (|t| ^ k * ‖mellinR Ψ z‖) := by ring
      _ ≤ 2 ^ k * Kk := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK0) (by positivity)

/-- Every fixed vertical line of the Mellin transform is integrable. Derived convergence for page 27. -/
theorem mellinR_vertical_integrable469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (σ : ℝ) :
    Complex.VerticalIntegrable (mellinR Ψ) σ := by
  obtain ⟨C, hC, hb⟩ := mellinR_vertical_decay469 Ψ S hS hsm hcs hsupp σ 2
  have hbase : Integrable (fun t : ℝ => ((1 + |t|) ^ (2 : ℕ))⁻¹) := by
    convert (integrable_one_add_norm (E := ℝ) (r := 2) (μ := volume) (by norm_num)) using 1
    funext t
    rw [Real.norm_eq_abs, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  have hg : Integrable (fun t : ℝ => C / (1 + |t|) ^ (2 : ℕ)) := by
    simpa only [div_eq_mul_inv] using hbase.const_mul C
  apply hg.mono'
  · have hc := (mellinR_differentiable469 Ψ S hS hsm.continuous hcs hsupp).continuous
    apply Continuous.aestronglyMeasurable
    apply hc.comp
    fun_prop
  · exact Filter.Eventually.of_forall hb

/-- Mellin inversion holds on every real abscissa for the smooth compact kernels in page 27. -/
theorem mellinR_inversion469(Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (σ x : ℝ) (hx : 0 < x) :
    mellinInv σ (mellinR Ψ) x = (Ψ x : ℂ) := by
  have heq : mellin (Complex.ofReal ∘ Ψ) = mellinR Ψ := by
    funext z
    simp only [mellin, mellinR, Function.comp_def, smul_eq_mul, mul_comm]
  have hf : MellinConvergent (Complex.ofReal ∘ Ψ) (σ : ℂ) := by
    simpa [MellinConvergent, Function.comp_def, smul_eq_mul, mul_comm] using
      mellinR_integrable469 Ψ S hS hsm.continuous hcs hsupp (σ : ℂ)
  have hv : Complex.VerticalIntegrable (mellin (Complex.ofReal ∘ Ψ)) σ := by
    rw [heq]
    exact mellinR_vertical_integrable469 Ψ S hS hsm hcs hsupp σ
  rw [← heq]
  exact mellinInv_mellin_eq σ (Complex.ofReal ∘ Ψ) hx hf hv
    (Complex.continuous_ofReal.comp hsm.continuous).continuousAt

/-- CONDITIONAL ON zero sum summability. The omitted zero sum is exactly the complementary zero sum. Derived bookkeeping for page 27. -/
theorem zero_tail_eq_complement469 (B T : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (Ψ : ℝ → ℝ)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0} =>
      (mult χ ρ : ℂ) * mellinR Ψ ρ)) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T},
        (mult χ ρ : ℂ) * mellinR Ψ ρ) =
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ ¬ (-B < ρ.re ∧ |ρ.im| ≤ T)},
        (mult χ ρ : ℂ) * mellinR Ψ ρ := by
  let Z := {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}
  let W : Set Z := {ρ | -B < (ρ : ℂ).re ∧ |(ρ : ℂ).im| ≤ T}
  have hh := hs.tsum_subtype_add_tsum_subtype_compl W
  have hw : (∑' ρ : W, (mult χ (ρ : Z) : ℂ) * mellinR Ψ (ρ : Z)) =
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T},
        (mult χ ρ : ℂ) * mellinR Ψ ρ := by
    exact (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun ρ : ℂ => DirichletCharacter.LFunction χ ρ = 0)
      (fun ρ : ℂ => -B < ρ.re ∧ |ρ.im| ≤ T)).tsum_eq
      (fun ρ => (mult χ ρ : ℂ) * mellinR Ψ ρ)
  have hc : (∑' ρ : ↥(Wᶜ : Set Z), (mult χ (ρ : Z) : ℂ) * mellinR Ψ (ρ : Z)) =
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ ¬ (-B < ρ.re ∧ |ρ.im| ≤ T)},
        (mult χ ρ : ℂ) * mellinR Ψ ρ := by
    exact (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun ρ : ℂ => DirichletCharacter.LFunction χ ρ = 0)
      (fun ρ : ℂ => ¬ (-B < ρ.re ∧ |ρ.im| ≤ T))).tsum_eq
      (fun ρ => (mult χ ρ : ℂ) * mellinR Ψ ρ)
  rw [hw, hc] at hh
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hh.symm)

/-- The entire Mellin transform has a correctly oriented zero boundary integral on every rectangle. Derived calculus for page 27. -/
theorem mellinR_rectangle469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hc : Continuous Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S) (B T : ℝ) :
    (∫ σ in (-B)..(2 : ℝ), mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)) -
      (∫ σ in (-B)..(2 : ℝ), mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ t in (-T)..T, mellinR Ψ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I * (∫ t in (-T)..T, mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  have hd := mellinR_differentiable469 Ψ S hS hc hcs hsupp
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (mellinR Ψ)
    (((-B : ℝ) : ℂ) - (T : ℂ) * Complex.I) ((2 : ℂ) + (T : ℂ) * Complex.I)
    hd.differentiableOn
  simpa [Complex.smul_re, smul_eq_mul, sub_eq_add_neg] using hh

/-- Mathlib Dirichlet series formula for the negative logarithmic derivative on the right half plane. Normalized for page 27. -/
theorem logDeriv_dirichlet_series469 (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, (vonMangoldt n : ℂ) * χ n / (n : ℂ) ^ s) =
      -(logDeriv (DirichletCharacter.LFunction χ) s) := by
  have hh := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    ← DirichletCharacter.LFunction_eq_LSeries χ hs] at hh
  simp only [logDeriv, Pi.div_apply]
  rw [← neg_div]
  rw [← hh]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · simp [LSeries.term, hn, mul_comm]

/-- Mellin inversion and justified interchange with a summable Dirichlet series. Derived right line step for page 27. -/
theorem mellinR_dirichlet_inversion469 (Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (a : ℕ → ℂ) (ha : a 0 = 0)
    (σ : ℝ) (hseries : LSeriesSummable a (σ : ℂ)) :
    (∑' n : ℕ, a n * (Ψ n : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, LSeries a ((σ : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  let z : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * Complex.I
  let F : ℕ → ℝ → ℂ := fun n t => LSeries.term a (z t) n * mellinR Ψ (z t)
  have hM : Integrable (fun t : ℝ => mellinR Ψ (z t)) :=
    mellinR_vertical_integrable469 Ψ S hS hsm hcs hsupp σ
  have hcM : Continuous (fun t : ℝ => mellinR Ψ (z t)) := by
    apply (mellinR_differentiable469 Ψ S hS hsm.continuous hcs hsupp).continuous.comp
    fun_prop
  have hnorm (n : ℕ) (t : ℝ) :
      ‖F n t‖ = ‖LSeries.term a (σ : ℂ) n‖ * ‖mellinR Ψ (z t)‖ := by
    simp [F, LSeries.norm_term_eq, z]
  have hFc (n : ℕ) : Continuous (F n) := by
    by_cases hn : n = 0
    · subst n
      simpa [F] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp only [F, LSeries.term_def₀ ha]
      apply Continuous.mul _ hcM
      apply continuous_const.mul
      apply Continuous.const_cpow _ (Or.inl hn0)
      fun_prop
  have hFi (n : ℕ) : Integrable (F n) := by
    apply (hM.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono' (hFc n).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => (hnorm n t).le)
  have hFnorm (n : ℕ) : (∫ t : ℝ, ‖F n t‖) =
      ‖LSeries.term a (σ : ℂ) n‖ * ∫ t : ℝ, ‖mellinR Ψ (z t)‖ := by
    simp_rw [hnorm n]
    exact integral_const_mul _ _
  have hFs : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    simp_rw [hFnorm]
    exact hseries.norm.mul_right _
  have hswap := integral_tsum_of_summable_integral_norm hFi hFs
  have hinv (n : ℕ) : a n * (Ψ n : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F n t := by
    by_cases hn : n = 0
    · subst n
      simp [ha, F]
    · have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hh := mellinR_inversion469 Ψ S hS hsm hcs hsupp σ (n : ℝ) hnp
      simp only [mellinInv, Complex.real_smul, smul_eq_mul] at hh
      rw [← hh]
      have hF : F n = fun t : ℝ => a n * ((n : ℂ) ^ (-(z t)) * mellinR Ψ (z t)) := by
        funext t
        dsimp only [F]
        rw [LSeries.term_def₀ ha]
        ring
      rw [hF, integral_const_mul]
      dsimp [z]
      ring
  calc
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F n t := tsum_congr hinv
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, F n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, F n t := by rw [hswap]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      exact tsum_mul_right

/-- The arithmetic sum is the full right vertical integral of the negative logarithmic derivative against the Mellin kernel. Derived from page 27. -/
theorem arithmetic_right_line469(Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, -(logDeriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (t : ℂ) * Complex.I)) *
          mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  let a : ℕ → ℂ := fun n => (vonMangoldt n : ℂ) * χ n
  have ha : a 0 = 0 := by simp [a]
  have hs : LSeriesSummable a (σ : ℂ) := by
    convert DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := (σ : ℂ)) (by simpa using hσ) using 1
    funext n
    simp [a, mul_comm]
  have hh := mellinR_dirichlet_inversion469 Ψ S hS hsm hcs hsupp a ha σ hs
  have hlog (t : ℝ) : LSeries a ((σ : ℂ) + (t : ℂ) * Complex.I) =
      -(logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hz : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp at hre
      linarith
    unfold LSeries
    simp_rw [LSeries.term_of_ne_zero' hz]
    exact logDeriv_dirichlet_series469 r χ _ (by simpa using hσ)
  simp_rw [hlog] at hh
  exact hh

/-- The logarithmic residue of an analytic function of finite order is its analytic multiplicity. Derived local residue for page 27. -/
theorem analytic_logDeriv_residue469 (f : ℂ → ℂ) (ρ : ℂ) (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    Tendsto (fun z => (z - ρ) * logDeriv f z) (𝓝[≠] ρ)
      (𝓝 (analyticOrderNatAt f ρ : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hfin
  simp only [smul_eq_mul] at hfg
  have hlog := logDeriv_congr_nhds hfg
  have hgd : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z := by
    filter_upwards [hg.eventually_analyticAt] with z hz
    exact hz.differentiableAt
  have hgn : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hcont : ContinuousAt (logDeriv g) ρ := by
    exact hg.deriv.continuousAt.div hg.continuousAt hg0
  have hmul : Tendsto (fun z => (z - ρ) * logDeriv g z) (𝓝[≠] ρ) (𝓝 (0 : ℂ)) := by
    have hzlim : Tendsto (fun z : ℂ => z - ρ) (𝓝 ρ) (𝓝 (0 : ℂ)) := by
      simpa using (tendsto_id.sub_const ρ : Tendsto (fun z : ℂ => z - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)))
    simpa using (hzlim.mul hcont.tendsto).mono_left nhdsWithin_le_nhds
  have heq : (fun z => (z - ρ) * logDeriv f z) =ᶠ[𝓝[≠] ρ]
      (fun z => (analyticOrderNatAt f ρ : ℂ) + (z - ρ) * logDeriv g z) := by
    filter_upwards [hlog.filter_mono nhdsWithin_le_nhds,
      hgd.filter_mono nhdsWithin_le_nhds, hgn.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hdz hgz hzne
    have hsub : z - ρ ≠ 0 := sub_ne_zero.mpr hzne
    rw [hz, logDeriv_fun_mul (f := fun z : ℂ => (z - ρ) ^ analyticOrderNatAt f ρ) (g := g) z (pow_ne_zero _ hsub) hgz (by fun_prop) hdz,
      logDeriv_fun_pow (by fun_prop)]
    have hlin : logDeriv (fun w : ℂ => w - ρ) z = 1 / (z - ρ) := by
      simp [logDeriv_apply]
    rw [hlin]
    field_simp
  have ht : Tendsto (fun z => (analyticOrderNatAt f ρ : ℂ) + (z - ρ) * logDeriv g z)
      (𝓝[≠] ρ) (𝓝 (analyticOrderNatAt f ρ : ℂ)) := by
    simpa using (tendsto_const_nhds (x := (analyticOrderNatAt f ρ : ℂ))).add hmul
  exact ht.congr' heq.symm

/-- Every Dirichlet L function away from one has logarithmic residue equal to the sealed analytic multiplicity. Derived from page 27. -/
theorem LFunction_logDeriv_residue469 (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (ρ : ℂ) (hρ : ρ ≠ 1) :
    Tendsto (fun z => (z - ρ) * logDeriv (DirichletCharacter.LFunction χ) z) (𝓝[≠] ρ)
      (𝓝 (mult χ ρ : ℂ)) := by
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (by simpa using hz))).differentiableWithinAt
  have hnonzero : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 := by
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
  have horder : analyticOrderAt (DirichletCharacter.LFunction χ) (2 : ℂ) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hnonzero)]
    simp
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    hL.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (by norm_num) (by simpa using hρ) horder
  exact analytic_logDeriv_residue469 _ ρ (hL ρ (by simpa using hρ)) hfinite

/-- The weighted negative logarithmic derivative has local residue minus the multiplicity times the Mellin transform. Derived local zero term for page 27. -/
theorem weighted_zero_residue469(Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hc : Continuous Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S)
    (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (ρ : ℂ) (hρ : ρ ≠ 1) :
    Tendsto (fun z => (z - ρ) * (-(logDeriv (DirichletCharacter.LFunction χ) z) * mellinR Ψ z))
      (𝓝[≠] ρ) (𝓝 (-(mult χ ρ : ℂ) * mellinR Ψ ρ)) := by
  have hr := (LFunction_logDeriv_residue469 r χ ρ hρ).neg
  have hm : Tendsto (mellinR Ψ) (𝓝[≠] ρ) (𝓝 (mellinR Ψ ρ)) :=
    (mellinR_differentiable469 Ψ S hS hc hcs hsupp).continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  convert hr.mul hm using 1
  funext z
  ring

/-- The negative logarithmic derivative of zeta has residue one at its pole. Derived principal term for page 27. -/
theorem riemannZeta_logDeriv_pole469 : Tendsto (fun z : ℂ => (z - 1) * (-logDeriv riemannZeta z)) (𝓝[≠] 1) (𝓝 1) := by
  let g := DirichletCharacter.LFunctionTrivChar₁ 1
  have hg : Differentiable ℂ g := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  have hg0 : g 1 ≠ 0 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
  have hcont : ContinuousAt (logDeriv g) 1 :=
    ((hg.contDiff : ContDiff ℂ 1 g).continuous_deriv le_rfl).continuousAt.div hg.continuous.continuousAt hg0
  have hgn : ∀ᶠ z in 𝓝[≠] (1 : ℂ), g z ≠ 0 :=
    (hg.continuous.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
  have hgval (z : ℂ) (hz : z ≠ 1) : g z = (z - 1) * riemannZeta z := by
    simp [g, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz,
      DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  have hgder (z : ℂ) (hz : z ≠ 1) : deriv g z = (z - 1) * deriv riemannZeta z + riemannZeta z := by
    simpa [g, DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq] using
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hz
  have heq : (fun z : ℂ => (z - 1) * (-logDeriv riemannZeta z)) =ᶠ[𝓝[≠] 1]
      (fun z : ℂ => 1 - (z - 1) * logDeriv g z) := by
    filter_upwards [hgn, self_mem_nhdsWithin] with z hgz hz
    have hz0 : riemannZeta z ≠ 0 := by
      intro he
      apply hgz
      simp [hgval z hz, he]
    rw [logDeriv_apply, logDeriv_apply, hgder z hz, hgval z hz]
    field_simp [hz0, sub_ne_zero.mpr hz]
    ring
  have hzlim : Tendsto (fun z : ℂ => z - 1) (𝓝[≠] 1) (𝓝 (0 : ℂ)) := by
    simpa using (tendsto_id.sub_const (1 : ℂ) : Tendsto (fun z : ℂ => z - 1) (𝓝 1) (𝓝 (1 - 1))).mono_left nhdsWithin_le_nhds
  have hmul := hzlim.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  have ht : Tendsto (fun z : ℂ => 1 - (z - 1) * logDeriv g z) (𝓝[≠] 1) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub hmul
  exact ht.congr' heq.symm

/-- The principal pole contributes the kernel integral. Derived pole term for equation 7.12 on page 27. -/
theorem weighted_pole_residue469(Ψ : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hc : Continuous Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S) :
    Tendsto (fun z : ℂ => (z - 1) * (-logDeriv riemannZeta z * mellinR Ψ z))
      (𝓝[≠] 1) (𝓝 (∫ x in Set.Ioi (0 : ℝ), (Ψ x : ℂ))) := by
  have hm : Tendsto (mellinR Ψ) (𝓝[≠] (1 : ℂ)) (𝓝 (mellinR Ψ 1)) :=
    (mellinR_differentiable469 Ψ S hS hc hcs hsupp).continuous.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have ht := riemannZeta_logDeriv_pole469.mul hm
  convert ht using 1
  · funext z
    ring
  · simp [mellinR]

/-! ## The kernel estimate -/

/-- LEAF. Mellin decay of the kernel, from the support hypothesis and integration by parts.

Step: if every `k`-th derivative of `Ψ` is bounded by `M k` and the support of `Ψ`
lies in `Ioi S` with `S ≥ 1`, then on the half plane `re s + k ≤ -1` the Mellin
transform obeys a bound by `M k * S ^ (re s)` with `k` powers of `(1 + |Im s|)^-1`.
This is repeated integration by parts, with the boundary terms killed by the
support condition; no arithmetic enters.  It is the input the two boundary leaves
need, and the only place the seminorm bounds are spent. -/
theorem leaf_mellin_decay74 (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ) (hS : 1 ≤ S)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) (hcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ Set.Ioi S) (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
    (k : ℕ) (σ t : ℝ) (hσ : σ + (k : ℝ) ≤ -1) :
    ‖mellinR Ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ((2 : ℝ) ^ k * M k) * S ^ σ / (1 + |t|) ^ k := by
  -- BLOCKED FALSE. The checked in-file theorem not_leaf_mellin_decay74_statement469 is a counterexample.
  sorry

/-! ## The contour shift -/

/-- LEAF. The explicit formula on a rectangle, as an identity.

Step: for `0 < B`, `1 ≤ S`, a primitive `χ` and a smooth compactly supported `Ψ`
supported in `Ioi S`, the arithmetic side — the logarithmic sum, minus the residue
of the pole at `s = 1` when `χ` is the principal character, plus the zeros of the
L-function with `-B < re ρ` and `|Im ρ| ≤ T` counted with multiplicity — equals the
boundary of the rectangle with corners `-B` and `2` and heights `±T`: the shifted
vertical line plus the two horizontal pieces.  The identity is exact; every error
term of the target sits in the three quantities the next leaves bound. -/
theorem leaf_contour_shift74 (B T : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (M : ℕ → ℝ) (S : ℝ) (Ψ : ℝ → ℝ) (hB : 0 < B) (hT : 0 < T)
    (hS : 1 ≤ S) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
      (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S)
      (hb : ∀ k x, |iteratedDeriv k Ψ x| ≤ M k)
    (hχ : χ.IsPrimitive) :
    ∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ) =
    (1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
      (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I))) := by
  -- BLOCKED OUT OF REACH. Mathlib has no meromorphic rectangle residue theorem with zero and pole residues.
  sorry

/-! ## The two boundary bounds -/

/-- LEAF. The shifted vertical line contributes at most a constant times `S ^ (-B)`.

Step: on the line `re s = -B` the logarithmic derivative of the L-function grows
only logarithmically in `|Im s|`, while the kernel's Mellin transform decays like
`S ^ (-B) * (1 + |Im s|) ^ (-2)` by the kernel leaf; the integral over the line is
therefore bounded by a constant, uniform in the character and in the kernel, times
`S ^ (-B)`.  This is the vertical part of the rectangle, which is where the size of
the shifted contour is paid for. -/
theorem leaf_vertical_remainder74 (M : ℕ → ℝ) (B T : ℝ) (hB : 0 < B) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
        ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S →
        (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
        ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C * S ^ (-B) := by
  -- BLOCKED OUT OF REACH. Mathlib has no conductor-uniform logarithmic derivative bound on this line.
  sorry

/-- LEAF. The two horizontal pieces contribute at most a constant times `S ^ (-B)`.

Step: on the segments `Im s = ±T` and `-B ≤ re s ≤ 2` the Mellin transform is
bounded by `S ^ (-B)` times a constant depending on the seminorm bounds, and the
logarithmic derivative is bounded there as well, so the two segments together
contribute a constant times `S ^ (-B)`, uniformly in the character and in the
kernel.  This is the price of the truncation at height `T` that makes the zero sum
finite. -/
theorem leaf_horizontal_remainder74 (M : ℕ → ℝ) (B T : ℝ) (hB : 0 < B) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
        ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S →
        (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
        ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ ≤ C * S ^ (-B) := by
  -- BLOCKED OUT OF REACH. The horizontal Mellin scale is not S to the power minus B.
  sorry

/-! ## What the truncation leaves out -/

/-- LEAF. The zeros outside the truncated window contribute at most a constant times `S ^ (-B)`.

Step: the difference between the sum over all zeros of the L-function and the sum
over those with `-B < re ρ` and `|Im ρ| ≤ T` is a sum of `mult χ ρ * mellinR Ψ ρ`
over the zeros above height `T` and over the zeros with `re ρ ≤ -B`, with
multiplicity.  Each term is a Mellin transform at a zero, so the kernel decay makes
the whole tail bounded by a constant times `S ^ (-B)`, uniformly in the character
and in the kernel.  This is the difference the assembly adds back after the
truncated identity. -/
theorem leaf_zero_tail74 (M : ℕ → ℝ) (B T : ℝ) (hB : 0 < B) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
        ∀ (S : ℝ) (Ψ : ℝ → ℝ), 1 ≤ S → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Set.Ioi S →
        (∀ k x, |iteratedDeriv k Ψ x| ≤ M k) →
        ‖(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ)‖ ≤ C * S ^ (-B) := by
  -- BLOCKED OUT OF REACH. Summability and a high zero counting estimate are absent from Mathlib.
  sorry

/-! ## The assembly -/

/-- The assembly: the exact sealed statement of `lemma74`, proved from the leaves above
through the truncated identity, two triangle inequalities and the monotonicity of
`S ↦ S ^ (-·)` on `S ≥ 1`, and nothing left open. -/
theorem lemma74_split : Lemma74 := by
  intro A hA M
  let B : ℝ := A + 2
  let T : ℝ := 1
  have hBval : B = A + 2 := rfl
  have hTval : T = 1 := rfl
  have hB : 0 < B := by rw [hBval]; linarith
  have hT : 0 < T := by rw [hTval]; norm_num
  obtain ⟨Cv, hCv, hv⟩ := leaf_vertical_remainder74 M B T hB hT
  obtain ⟨Ch, hCh, hh⟩ := leaf_horizontal_remainder74 M B T hB hT
  obtain ⟨Ct, hCt, ht⟩ := leaf_zero_tail74 M B T hB hT
  refine ⟨Cv + Ch + Ct, ?_⟩
  intro r hrinst χ hχ S Ψ hS hsm hcs hsupp hb
  haveI : NeZero r := hrinst
  have hid := leaf_contour_shift74 B T r χ M S Ψ hB hT hS hsm hcs hsupp hb hχ
  have hvt := hv r χ hχ S Ψ hS hsm hcs hsupp hb
  have hhr := hh r χ hχ S Ψ hS hsm hcs hsupp hb
  have htl := ht r χ hχ S Ψ hS hsm hcs hsupp hb
  have hEq : (∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ)) = ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))) + (((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))) := by
    rw [← hid]
    abel
  have a2 : ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ := norm_add_le (a := ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) (b := ((1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))))
  have a1 : ‖((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))) + (((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ)))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ :=
    norm_add_le (a := ((1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) + (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I))))) (b := (((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))))
  have h1 : ‖(∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ := by
    rw [hEq]
    exact le_trans a1 (add_le_add a2 (le_refl (‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖)))
  have h2 : ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ ≤
      Cv * S ^ (-B) + Ch * S ^ (-B) + Ct * S ^ (-B) :=
    add_le_add (add_le_add hvt hhr) htl
  have h3 : Cv * S ^ (-B) + Ch * S ^ (-B) + Ct * S ^ (-B) =
      (Cv + Ch + Ct) * S ^ (-B) := by ring
  have hp : S ^ (-B) ≤ S ^ (-A) := by
    have hle : (-B : ℝ) ≤ -A := by rw [hBval]; linarith
    exact Real.rpow_le_rpow_of_exponent_le hS hle
  have h4 : (Cv + Ch + Ct) * S ^ (-B) ≤ (Cv + Ch + Ct) * S ^ (-A) :=
    mul_le_mul_of_nonneg_left hp (by linarith)
  calc ‖(∑' n : ℕ, (vonMangoldt n : ℂ) * χ n * (Ψ n : ℂ) -
      (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) +
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ ≤ ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T, (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) * mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ + ‖(1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ), (( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) + ( -(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) * mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))‖ + ‖((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0}, (mult χ ρ : ℂ) * mellinR Ψ ρ) -
            (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T}, (mult χ ρ : ℂ) * mellinR Ψ ρ))‖ := h1
    _ ≤ Cv * S ^ (-B) + Ch * S ^ (-B) + Ct * S ^ (-B) := h2
    _ = (Cv + Ch + Ct) * S ^ (-B) := h3
    _ ≤ (Cv + Ch + Ct) * S ^ (-A) := h4

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_negative_bound469
#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_decay_zero469
#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_dilation469
#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_dilation_obstruction469
#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_positive_witness469
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_mellin_decay74_counterexample469

#print axioms LeanLab.BhowmikGrimmelt2026.mellin_interval_parts469
#print axioms LeanLab.BhowmikGrimmelt2026.mellin_interval_iterated_parts469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_finite_interval469
#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_iterated_parts469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_decay_shifted469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_conj469
#print axioms LeanLab.BhowmikGrimmelt2026.logDeriv_conj469
#print axioms LeanLab.BhowmikGrimmelt2026.conjugate_horizontal_re469

#print axioms LeanLab.BhowmikGrimmelt2026.horizontal_modOne_re469

#print axioms LeanLab.BhowmikGrimmelt2026.conjugate_horizontal_difference_im469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_integrable469
#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_differentiable469
#print axioms LeanLab.BhowmikGrimmelt2026.summable_arithmetic_kernel469

#print axioms LeanLab.BhowmikGrimmelt2026.not_leaf_mellin_decay74_statement469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_vertical_decay469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_vertical_integrable469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_inversion469

#print axioms LeanLab.BhowmikGrimmelt2026.zero_tail_eq_complement469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_rectangle469

#print axioms LeanLab.BhowmikGrimmelt2026.logDeriv_dirichlet_series469

#print axioms LeanLab.BhowmikGrimmelt2026.mellinR_dirichlet_inversion469

#print axioms LeanLab.BhowmikGrimmelt2026.arithmetic_right_line469

#print axioms LeanLab.BhowmikGrimmelt2026.analytic_logDeriv_residue469

#print axioms LeanLab.BhowmikGrimmelt2026.LFunction_logDeriv_residue469

#print axioms LeanLab.BhowmikGrimmelt2026.weighted_zero_residue469

#print axioms LeanLab.BhowmikGrimmelt2026.riemannZeta_logDeriv_pole469

#print axioms LeanLab.BhowmikGrimmelt2026.weighted_pole_residue469
