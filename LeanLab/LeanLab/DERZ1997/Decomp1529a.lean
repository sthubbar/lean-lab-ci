/-
Unit U-1529, run 20261025T2003Z-426, DECOMPOSE of the GRH inputs of P0011,
Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, 99-104.

File a: zeros of the Riemann zeta function and of Dirichlet L-functions.
* `zetaZeros T`, the non-trivial zeros `ρ` (open strip `0 < Re ρ < 1`) with `|Im ρ| ≤ T`;
  `zetaZerosPos T` those with `0 < Im ρ ≤ T`; `zetaMult ρ`, the order of the zero.
* `LZeros χ T`, `LMult χ ρ`, the same for `DirichletCharacter.LFunction χ`.
Leaves: finiteness, the zero-free range below height 14, the explicit Riemann-von Mangoldt
formula in Rosser's form (Rosser 1941, Theorem 19), the count in unit windows, the sum of
`1/|ρ|` up to height T, and the analogues for `L(s, χ)` (McCurley 1984, Theorem 2.1).
Multiplicities are carried by `analyticOrderNatAt`, so no simplicity of zeros is assumed.
Sums over zeros run over `hfin.toFinset` for a finiteness proof `hfin`, which leaf
`zetaZeros_finite` (resp. `LZeros_finite`) supplies.

Source when the original is not at hand: Davenport, Multiplicative Number Theory, 3rd ed.,
chapters 15-17 and 19.
AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PNTPort.DirichletZF.SiegelSigns
import LeanLab.Routes.Decomp1551c
import LeanLab.PNTPort.ZetaZeros.Sym
import LeanLab.DERZ1997.Statements

namespace LeanLab.DERZ1997.Decomp1529a
open Complex Filter Topology MeasureTheory Set

/-- Non-trivial zeros of `ζ` with `|Im ρ| ≤ T`. -/
def zetaZeros (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Non-trivial zeros of `ζ` with `0 < Im ρ ≤ T`. -/
def zetaZerosPos (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Non-trivial zeros of `ζ` with `T < Im ρ ≤ T + 1`. -/
def zetaZerosWindow (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < ρ.im ∧ ρ.im ≤ T + 1}

/-- Multiplicity of a zero of `ζ`. -/
noncomputable def zetaMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- Zeros of `L(s, χ)` in the open strip with `|Im ρ| ≤ T`. -/
def LZeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

/-- Multiplicity of a zero of `L(s, χ)`. -/
noncomputable def LMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- Reciprocal-square integral used for finite partial summation.
Helfgott arXiv:1305.2897v4 page 38, partial summation behind equation 4.26. -/
theorem reciprocal_integral193 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / t ^ 2) = 1 / a - 1 / b := by
  have hn (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ≠ 0 := by
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun t : ℝ => -(1 / t)) (1 / t ^ 2) t := by
    convert ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) (hn t ht)).neg using 1
    · ext y; simp
    · simp only [zero_mul, zero_sub, mul_one, neg_div, neg_neg, id_eq]
  have hi : IntervalIntegrable (fun t : ℝ => 1 / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero _ (hn t ht)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  linarith

/-- Finite weighted partial summation for real ordinates, including integrability.
Helfgott arXiv:1305.2897v4 page 38, the partial summation step. -/
theorem reciprocal_sum_partial193 {ι : Type*} (s : Finset ι) (x w : ι → ℝ)
    {a T : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ T) :
    IntervalIntegrable (fun t => (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2) volume a T ∧
    (∑ i ∈ s, w i / x i) = (∑ i ∈ s, w i) / T +
      ∫ t in a..T, (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2 := by
  classical
  let f : ℝ → ℝ := fun t => 1 / t ^ 2
  have hi : IntervalIntegrable f volume a T := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [Set.uIcc_of_le haT] at ht
    exact pow_ne_zero _ (show t ≠ 0 by linarith [ht.1])
  have hint (i : ι) : IntervalIntegrable ((Ioi (x i)).indicator (fun t => w i * f t)) volume a T :=
    ⟨(hi.1.const_mul _).indicator measurableSet_Ioi,
      (hi.2.const_mul _).indicator measurableSet_Ioi⟩
  have hpoint (t : ℝ) : (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2 =
      ∑ i ∈ s, (Ioi (x i)).indicator (fun t => w i * f t) t := by
    rw [Finset.sum_div, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i < t <;> simp [Set.indicator, h, f, div_eq_mul_inv]
  constructor
  · have he : (fun t => (∑ i ∈ s.filter (fun i => x i < t), w i) / t ^ 2) =
        fun t => ∑ i ∈ s, (Ioi (x i)).indicator (fun t => w i * f t) t := funext hpoint
    rw [he]
    convert IntervalIntegrable.sum s (fun i _ => hint i) using 1
    ext t; simp only [Finset.sum_apply]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  have hterm (i : ι) (his : i ∈ s) :
      (∫ t in a..T, (Ioi (x i)).indicator (fun t => w i * f t) t) =
        w i / x i - w i / T := by
    rw [intervalIntegral.integral_of_le haT,
      MeasureTheory.integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi,
      sup_eq_right.mpr (hx i his).1,
      ← intervalIntegral.integral_of_le (hx i his).2,
      intervalIntegral.integral_const_mul]
    rw [show (∫ t in x i..T, f t) = 1 / x i - 1 / T from
      reciprocal_integral193 (ha.trans_le (hx i his).1) (hx i his).2]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_div]
  ring

/-- The rounded Rosser upper budget exceeds one at every allowed height.
This is a limitation of using that bound alone for the height-14 zero-free claim.
Davenport chapter 15 page 98, the rounded budget in rvm_upper. -/
theorem rosser_budget_gt_one193 {T : ℝ} (hT : Real.exp 1 ≤ T) :
    1 < T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
      + 0.14 * Real.log T + 0.45 * Real.log (Real.log T) + 1.6 := by
  have ht0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht0).mpr hT
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog
  have hu : 0 < T / (2 * Real.pi) := by positivity
  have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hu) hu.le
  have he : T / (2 * Real.pi) * (T / (2 * Real.pi))⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  nlinarith

/-! ### Zeta zeros -/

/-- LEAF. For every real `T` there are only finitely many non-trivial zeros of `ζ` with
`|Im ρ| ≤ T`: `ζ` is analytic off `s = 1`, has a pole at 1, does not vanish on `Re s = 1`, and
by the functional equation does not vanish on `Re s = 0`, so zeros cannot accumulate in the
closed rectangle. Davenport ch. 15, p. 97, and Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
Unit U-1529. -/
theorem zetaZeros_finite (T : ℝ) : (zetaZeros T).Finite := by
  have hf := (IsCompact.reProdIm (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
    (isCompact_Icc : IsCompact (Set.Icc (-T) T))).inter_riemannZetaZeros_finite
  apply hf.subset
  intro z hz
  refine ⟨?_, hz.1⟩
  exact ⟨⟨hz.2.1.le, hz.2.2.1.le⟩, (abs_le.mp hz.2.2.2)⟩


/-- LEAF. Non-trivial zeros are symmetric under complex conjugation, since
`ζ(conj s) = conj ζ(s)`. Davenport ch. 8, p. 61. Unit U-1529. -/
theorem conj_mem_zetaZeros {T : ℝ} {ρ : ℂ} (h : ρ ∈ zetaZeros T) :
    starRingEnd ℂ ρ ∈ zetaZeros T := by
  dsimp [zetaZeros] at *
  rcases h with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [riemannZeta_conj, h1, map_zero]
  · exact h2
  · exact h3
  · exact (abs_neg ρ.im).symm ▸ h4

/-- LEAF. Every non-trivial zero has multiplicity at least 1: `ζ` is analytic at `ρ ≠ 1`,
vanishes there, and is not identically zero near `ρ`. Davenport ch. 15. Unit U-1529. -/
theorem one_le_zetaMult {T : ℝ} {ρ : ℂ} (h : ρ ∈ zetaZeros T) : 1 ≤ zetaMult ρ := by
  dsimp [zetaMult, zetaZeros, analyticOrderNatAt] at *
  have h1 : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro h_eq
    have h2 := analyticOrderAt_eq_zero.mp h_eq
    cases h2 with
    | inl hna =>
      have ha : AnalyticAt ℂ riemannZeta ρ := by
        have h_nhd : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := by
          exact DifferentiableOn.analyticOnNhd differentiableOn_riemannZeta isOpen_compl_singleton
        apply h_nhd
        intro h_eq_1
        rw [Set.mem_singleton_iff] at h_eq_1
        rcases h with ⟨-, h2, h3, -⟩
        rw [h_eq_1] at h3
        norm_num at h3
      exact hna ha
    | inr hne =>
      exact hne h.1
  have h_not_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h_top
    have h_ev : riemannZeta =ᶠ[nhds ρ] 0 := analyticOrderAt_eq_top.mp h_top
    have h2 : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := by
      exact DifferentiableOn.analyticOnNhd differentiableOn_riemannZeta isOpen_compl_singleton
    have h3 : AnalyticOnNhd ℂ (fun (_ : ℂ) => (0 : ℂ)) ({1}ᶜ : Set ℂ) := analyticOnNhd_const
    have h4 : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) (1 : ℂ)).isPreconnected
    have h5 : ρ ∈ ({1}ᶜ : Set ℂ) := by
      intro h_eq
      rw [Set.mem_singleton_iff] at h_eq
      rcases h with ⟨-, h_re2, h_re3, -⟩
      rw [h_eq] at h_re3
      norm_num at h_re3
    have h6 : ∃ᶠ (z : ℂ) in nhdsWithin ρ {ρ}ᶜ, riemannZeta z = (0 : ℂ) := by
      apply Filter.Frequently.mono (Filter.Eventually.frequently (eventually_nhdsWithin_of_eventually_nhds h_ev))
      intro x hx
      exact hx
    have h7 := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq h2 h3 h4 h5 h6
    have h8 : riemannZeta 2 = 0 := by
      have h2_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
        intro h_eq
        rw [Set.mem_singleton_iff] at h_eq
        norm_num at h_eq
      exact h7 h2_mem
    have h9 : riemannZeta 2 ≠ 0 := by
      rw [riemannZeta_two]
      norm_num
    exact h9 h8
  change 1 ≤ (analyticOrderAt riemannZeta ρ).toNat
  generalize h_order : analyticOrderAt riemannZeta ρ = ord
  cases ord with
  | top => exact False.elim (h_not_top h_order)
  | coe n =>
    rw [ENat.toNat_natCast]
    have h4 : (n : ℕ∞) ≠ 0 := by
      rw [← h_order]
      exact h1
    exact Nat.pos_of_ne_zero (WithTop.coe_ne_zero.mp h4)

/-- LEAF. Rosser 1941 Theorem 19 as quoted in Kadiri and Lumley 2014,
page 6 equation 2.32 and page 11 Theorem 3.2 part d. The count uses strict height.
https://arxiv.org/abs/1407.7902. The original published analytic input remains open. -/
theorem rosser_strict193 {T : ℝ} (hT : Real.exp 1 ≤ T) (hfin : (zetaZerosPos T).Finite) :
    |(∑ ρ ∈ hfin.toFinset.filter (fun ρ => ρ.im < T), (zetaMult ρ : ℝ)) -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  sorry
/-- LEAF. Riemann-von Mangoldt, explicit upper bound: for `T ≥ e` the number `N(T)` of zeros
with `0 < γ ≤ T`, counted with multiplicity, is at most
`(T/2π) log(T/2π) - T/2π + 7/8 + 0.14 log T + 0.45 log log T + 1.6`.
Rosser 1941, Ann. of Math. 42, Theorem 19, `|N(T) - F(T)| < 0.137 log T + 0.443 log log T
+ 1.588` for `T ≥ 2`; Davenport ch. 15, p. 98. Unit U-1529. -/
theorem rvm_upper {T : ℝ} (hT : Real.exp 1 ≤ T) (hfin : (zetaZerosPos T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤
      T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
        + 0.14 * Real.log T + 0.45 * Real.log (Real.log T) + 1.6 := by
  classical
  have ht0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht0).mpr hT
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog
  let U : ℝ → ℝ := fun t => t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) -
    t / (2 * Real.pi) + 7/8 + 0.137 * Real.log t + 0.443 * Real.log (Real.log t) + 1.588
  have hcont : ContinuousAt U T := by
    have hn : T / (2 * Real.pi) ≠ 0 := div_ne_zero ht0.ne' (by positivity)
    have hl : Real.log T ≠ 0 := by linarith
    dsimp [U]
    fun_prop
  have hp (t : ℝ) : (zetaZerosPos t).Finite := by
    apply (zetaZeros_finite t).subset
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩
  have hbound : ∀ᶠ t in 𝓝[>] T, (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤ U t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htt : T < t := ht
    have hc := (abs_le.mp (rosser_strict193 (hT.trans htt.le) (hp t))).2
    have hs : (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤
        ∑ ρ ∈ (hp t).toFinset.filter (fun ρ => ρ.im < t), (zetaMult ρ : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => Nat.cast_nonneg _)
      intro ρ hρ
      have hz := hfin.mem_toFinset.mp hρ
      exact Finset.mem_filter.mpr ⟨(hp t).mem_toFinset.mpr
        ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.trans htt.le⟩,
        hz.2.2.2.2.trans_lt htt⟩
    dsimp [U]
    linarith
  have hc : (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤ U T :=
    ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hbound
  dsimp [U] at hc
  nlinarith

/-- LEAF. Riemann-von Mangoldt, explicit lower bound: for `T ≥ e`,
`N(T) ≥ (T/2π) log(T/2π) - T/2π + 7/8 - 0.14 log T - 0.45 log log T - 1.6`, zeros counted with
multiplicity. Rosser 1941, Ann. of Math. 42, Theorem 19; Davenport ch. 15, p. 98.
Unit U-1529. -/
theorem rvm_lower {T : ℝ} (hT : Real.exp 1 ≤ T) (hfin : (zetaZerosPos T).Finite) :
    T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
        - 0.14 * Real.log T - 0.45 * Real.log (Real.log T) - 1.6 ≤
      ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) := by
  classical
  have ht0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlog : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht0).mpr hT
  have hll : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlog
  have hc := (abs_le.mp (rosser_strict193 hT hfin)).1
  have hs : (∑ ρ ∈ hfin.toFinset.filter (fun ρ => ρ.im < T), (zetaMult ρ : ℝ)) ≤
      ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ρ _ _ => Nat.cast_nonneg _)
  nlinarith

/-- LEAF. Zeros in a unit window: for `T ≥ e`, the zeros with `T < γ ≤ T + 1`, counted with
multiplicity, number at most `2 log T + 5`. Follows from `rvm_upper` at `T + 1` and
`rvm_lower` at `T`; Davenport ch. 15, p. 98, corollary (b). Unit U-1529. -/
theorem window_count {T : ℝ} (hT : Real.exp 1 ≤ T) (hfin : (zetaZerosWindow T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤ 2 * Real.log T + 5 := by
  classical
  have ht2 : 2 ≤ T := by have := Real.exp_one_gt_d9; linarith
  have ht0 : 0 < T := by linarith
  have hu0 : 0 < T + 1 := by linarith
  have hp (S : ℝ) : (zetaZerosPos S).Finite := by
    apply (zetaZeros_finite S).subset
    intro z hz
    refine ⟨hz.1, hz.2.1, hz.2.2.1, ?_⟩
    rw [abs_of_pos hz.2.2.2.1]
    exact hz.2.2.2.2
  let A := (hp T).toFinset
  let B := hfin.toFinset
  let C := (hp (T + 1)).toFinset
  have hC : C = A ∪ B := by
    ext z
    simp only [A, B, C, Finset.mem_union, Set.Finite.mem_toFinset]
    constructor
    · intro hz
      by_cases hle : z.im ≤ T
      · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hle⟩
      · exact Or.inr ⟨hz.1, hz.2.1, hz.2.2.1, lt_of_not_ge hle, hz.2.2.2.2⟩
    · rintro (hz | hz)
      · exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, by linarith [hz.2.2.2.2]⟩
      · exact ⟨hz.1, hz.2.1, hz.2.2.1, by linarith [hz.2.2.2.1], hz.2.2.2.2⟩
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z ha hb
    have ha := (Set.Finite.mem_toFinset (hp T)).mp ha
    have hb := (Set.Finite.mem_toFinset hfin).mp hb
    linarith [ha.2.2.2.2, hb.2.2.2.1]
  let k : ℝ := 2 * Real.pi
  let M : ℝ → ℝ := fun s => s / k * Real.log (s / k) - s / k + 7 / 8
  let E : ℝ → ℝ := fun s => 0.14 * Real.log s + 0.45 * Real.log (Real.log s) + 1.6
  have hu : (∑ z ∈ C, (zetaMult z : ℝ)) ≤ M (T + 1) + E (T + 1) := by
    have h := rvm_upper (T := T + 1) (by linarith) (hp (T + 1))
    dsimp [C, M, E, k]
    linarith
  have hl : M T - E T ≤ ∑ z ∈ A, (zetaMult z : ℝ) := by
    have h := rvm_lower hT (hp T)
    dsimp [A, M, E, k]
    linarith
  have hsum : (∑ z ∈ B, (zetaMult z : ℝ)) ≤ M (T + 1) - M T + E (T + 1) + E T := by
    rw [hC, Finset.sum_union hdis] at hu
    linarith
  have hk2 : 2 ≤ k := by dsimp [k]; linarith [Real.pi_gt_three]
  have hk0 : 0 < k := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hlogT : 1 ≤ Real.log T := (Real.le_log_iff_exp_le ht0).mpr hT
  have hlogmono : Real.log T ≤ Real.log (T + 1) := Real.log_le_log ht0 (by linarith)
  have hmul : T * (Real.log (T + 1) - Real.log T) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hu0 ht0)
    rw [Real.log_div hu0.ne' ht0.ne'] at h
    have hh := mul_le_mul_of_nonneg_left h ht0.le
    have he : T * ((T + 1) / T - 1) = 1 := by field_simp; ring
    rwa [he] at hh
  have hlogadd : Real.log (T + 1) ≤ Real.log T + 1 / 2 := by nlinarith
  have hmain : M (T + 1) - M T ≤ (1 / 2) * Real.log (T + 1) := by
    have he : M (T + 1) - M T =
        (Real.log (T + 1) - Real.log k + T * (Real.log (T + 1) - Real.log T) - 1) / k := by
      dsimp [M]
      rw [Real.log_div hu0.ne' hk0.ne', Real.log_div ht0.ne' hk0.ne']
      ring
    rw [he, div_le_iff₀ hk0]
    nlinarith [mul_nonneg (show 0 ≤ k - 2 by linarith) (show 0 ≤ Real.log (T + 1) by linarith)]
  have hllT : Real.log (Real.log T) ≤ Real.log (T + 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log T by linarith)
    linarith
  have hllU : Real.log (Real.log (T + 1)) ≤ Real.log (T + 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log (T + 1) by linarith)
    linarith
  have heT : E T ≤ 0.59 * Real.log (T + 1) + 1.6 := by dsimp [E]; linarith
  have heU : E (T + 1) ≤ 0.59 * Real.log (T + 1) + 1.6 := by dsimp [E]; linarith
  change (∑ z ∈ B, (zetaMult z : ℝ)) ≤ _
  nlinarith

/-- Reflection pairs the two ordinate signs with multiplicity when real zeros are absent.
Davenport chapter 15 page 97, from the functional equation. -/
theorem zeta_count_both193 {T : ℝ} (hf : (zetaZeros T).Finite) (hp : (zetaZerosPos T).Finite)
    (hreal : ∀ ρ ∈ zetaZeros T, ρ.im ≠ 0) :
    (∑ ρ ∈ hf.toFinset, (zetaMult ρ : ℝ)) =
      2 * ∑ ρ ∈ hp.toFinset, (zetaMult ρ : ℝ) := by
  classical
  let s := hf.toFinset
  let p := s.filter (fun ρ => 0 < ρ.im)
  let n := s.filter (fun ρ => ¬0 < ρ.im)
  have he : p = hp.toFinset := by
    ext ρ
    simp only [p, s, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hρ, him⟩
      exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, him, (le_abs_self ρ.im).trans hρ.2.2.2⟩
    · intro hρ
      exact ⟨⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩,
        hρ.2.2.2.1⟩
  have hmap {ρ : ℂ} (hρ : ρ ∈ zetaZeros T) : 1 - ρ ∈ zetaZeros T := by
    refine ⟨LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero hρ.2.1 hρ.2.2.1 hρ.1, ?_, ?_, ?_⟩
    · simp only [sub_re, one_re]; linarith [hρ.2.2.1]
    · simp only [sub_re, one_re]; linarith [hρ.2.1]
    · simpa only [sub_im, one_im, zero_sub, abs_neg] using hρ.2.2.2
  have hnp : (∑ ρ ∈ n, (zetaMult ρ : ℝ)) = ∑ ρ ∈ p, (zetaMult ρ : ℝ) := by
    apply Finset.sum_bij (fun ρ _ => 1 - ρ)
    · intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hs, him⟩
      have hz := hf.mem_toFinset.mp hs
      refine Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr (hmap hz), ?_⟩
      simp only [sub_im, one_im, zero_sub]
      have hn := hreal ρ hz
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt him) hn)
    · intro a ha b hb h
      exact sub_right_inj.mp h
    · intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hs, him⟩
      have hz := hf.mem_toFinset.mp hs
      refine ⟨1 - ρ, Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr (hmap hz), ?_⟩, ?_⟩
      · simp only [sub_im, one_im, zero_sub]
        linarith
      · ring
    · intro ρ hρ
      have hz := hf.mem_toFinset.mp (Finset.mem_filter.mp hρ).1
      exact_mod_cast (LeanLab.PNTPort.ZetaZeros.ord_one_sub hz.2.1 hz.2.2.1).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun ρ => 0 < ρ.im) (fun ρ => (zetaMult ρ : ℝ))
  change (∑ ρ ∈ p, (zetaMult ρ : ℝ)) + (∑ ρ ∈ n, (zetaMult ρ : ℝ)) = _ at hsplit
  rw [hnp, he] at hsplit
  linarith

/-- Elementary envelope for twice the positive zeta count.
Davenport chapter 15 page 98 and the rounded Rosser upper bound. CONDITIONAL ON rvm_upper. -/
theorem zeta_count_envelope193 {t : ℝ} (ht : 14 ≤ t) (hp : (zetaZerosPos t).Finite) :
    2 * (∑ ρ ∈ hp.toFinset, (zetaMult ρ : ℝ)) ≤
      t / 3 * Real.log t - t / 2 + 6 / 5 * Real.log t + 5 := by
  have ht0 : 0 < t := by linarith
  have hk0 : 0 < 2 * Real.pi := by positivity
  have het : Real.exp 1 ≤ t := by have := Real.exp_one_lt_d9; linarith
  have hlogt : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr het
  have hlogk : 1 ≤ Real.log (2 * Real.pi) := by
    apply (Real.le_log_iff_exp_le hk0).mpr
    have := Real.exp_one_lt_d9
    linarith [Real.pi_gt_three]
  have hll : Real.log (Real.log t) ≤ Real.log t := by
    have hh := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log t)
    linarith
  have hc := rvm_upper het hp
  rw [Real.log_div ht0.ne' hk0.ne'] at hc
  have hpos : t / Real.pi * Real.log t ≤ t / 3 * Real.log t := by
    gcongr
    linarith [Real.pi_gt_three]
  have hneg : t / 2 ≤ t / Real.pi * (Real.log (2 * Real.pi) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]
    have hh := mul_le_mul_of_nonneg_left hlogk ht0.le
    nlinarith [Real.pi_lt_four]
  have he : 2 * (t / (2 * Real.pi) * (Real.log t - Real.log (2 * Real.pi)) -
      t / (2 * Real.pi) + 7/8 + 0.14 * Real.log t +
      0.45 * Real.log (Real.log t) + 1.6) =
      t / Real.pi * Real.log t - t / Real.pi * (Real.log (2 * Real.pi) + 1) +
      0.28 * Real.log t + 0.9 * Real.log (Real.log t) + 4.95 := by ring
  nlinarith

/-- The rounded Rosser budget at height four is below two.
This supplies the doublet exclusion in the small-height partial zero-free proof. -/
theorem rosser_upper_four_lt_two193 : (4 : ℝ) / (2 * Real.pi) * Real.log (4 / (2 * Real.pi)) - 4 / (2 * Real.pi) + 7 / 8
      + 0.14 * Real.log 4 + 0.45 * Real.log (Real.log 4) + 1.6 < 2 := by
  let u : ℝ := 4 / (2 * Real.pi)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hul : (5/8 : ℝ) ≤ u := by
    dsimp [u]
    rw [le_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_d2]
  have hlog4 : Real.log 4 ≤ 7/5 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hlogpos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hll : Real.log (Real.log 4) ≤ Real.log 4 - 1 := Real.log_le_sub_one_of_pos hlogpos
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hu0) hu0.le
  have hquad := mul_nonneg (sub_nonneg.mpr hul) (sub_nonneg.mpr hu1)
  change u * Real.log u - u + 7/8 + 0.14 * Real.log 4 + 0.45 * Real.log (Real.log 4) + 1.6 < 2
  nlinarith

/-- The existing positive critical-line certificate also covers negative ordinates.
Reuses Routes.Decomp1551c.zeta_half_ne_zero and Mathlib conjugation.
This supplies the critical-line part of P0011 page 101 zero sums without assuming RH. -/
theorem zeta_critical_height_fourteen193 {ρ : ℂ} (hhalf : ρ.re = 1/2) (hheight : |ρ.im| ≤ 14) : riemannZeta ρ ≠ 0 := by
  rcases le_total 0 ρ.im with hi | hi
  · have he : ρ = (1/2 : ℂ) + (ρ.im : ℂ) * I := by
      apply Complex.ext <;> simp [hhalf]
    rw [he]
    exact LeanLab.Routes.Decomp1551c.zeta_half_ne_zero ρ.im hi ((le_abs_self _).trans hheight)
  · have he : starRingEnd ℂ ρ = (1/2 : ℂ) + ((-ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hhalf]
    intro hz
    apply LeanLab.Routes.Decomp1551c.zeta_half_ne_zero (-ρ.im) (neg_nonneg.mpr hi)
      ((neg_le_abs _).trans hheight)
    rw [← he, riemannZeta_conj, hz, map_zero]

example : riemannZeta ((1/2 : ℂ) - I) ≠ 0 := by
  apply zeta_critical_height_fourteen193 <;> norm_num

/-- No nonreal strip zero at height at most four, from Rosser and the certified critical line.
Davenport chapter 15, supporting P0011 page 101. CONDITIONAL ON rvm_upper.
The critical-line calculation is the existing proved Routes.Decomp1551c certificate. -/
theorem zeta_small_nonreal193 {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) (hfour : |ρ.im| ≤ 4) :
    riemannZeta ρ ≠ 0 := by
  have hbudget := rosser_upper_four_lt_two193
  classical
  have hpos : ∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
      0 < z.im → z.im ≤ 4 → False := by
    intro z hz hz0 hz1 hzi hzi4
    have hhalf : z.re ≠ 1/2 := by
      intro hh
      have he : z = (1/2 : ℂ) + (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hh]
      apply LeanLab.Routes.Decomp1551c.zeta_half_ne_zero z.im hzi.le (by linarith)
      rw [← he]
      exact hz
    let τ : ℂ := 1 - starRingEnd ℂ z
    have hτ : τ ∈ zetaZerosPos 4 := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · dsimp [τ]
        exact LeanLab.PNTPort.ZetaZeros.zeta_one_sub_eq_zero hz0 hz1
          (by rw [riemannZeta_conj, hz, map_zero])
      · dsimp [τ]; linarith
      · dsimp [τ]; linarith
      · simpa [τ] using hzi
      · simpa [τ] using hzi4
    have hneq : z ≠ τ := by
      intro hh
      apply hhalf
      have hr := congrArg Complex.re hh
      dsimp [τ] at hr
      linarith
    have hzpos : z ∈ zetaZerosPos 4 := ⟨hz, hz0, hz1, hzi, hzi4⟩
    have hp : (zetaZerosPos 4).Finite := by
      apply (zetaZeros_finite 4).subset
      intro u hu
      exact ⟨hu.1, hu.2.1, hu.2.2.1, by rw [abs_of_pos hu.2.2.2.1]; exact hu.2.2.2.2⟩
    have hzfull (u : ℂ) (hu : u ∈ zetaZerosPos 4) : u ∈ zetaZeros 4 :=
      ⟨hu.1, hu.2.1, hu.2.2.1, by rw [abs_of_pos hu.2.2.2.1]; exact hu.2.2.2.2⟩
    have hwz : (1 : ℝ) ≤ zetaMult z := by exact_mod_cast one_le_zetaMult (hzfull z hzpos)
    have hwτ : (1 : ℝ) ≤ zetaMult τ := by exact_mod_cast one_le_zetaMult (hzfull τ hτ)
    have hpair : ({z, τ} : Finset ℂ) ⊆ hp.toFinset := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hp.mem_toFinset.mpr hzpos
      · exact hp.mem_toFinset.mpr hτ
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hpair
      (fun u _ _ => (Nat.cast_nonneg (zetaMult u) : (0 : ℝ) ≤ zetaMult u))
    rw [Finset.sum_pair hneq] at hs
    have hc := rvm_upper (T := 4) (by have := Real.exp_one_lt_d9; linarith) hp
    linarith
  intro hz
  rcases lt_or_gt_of_ne him with hn | hp
  · apply hpos (starRingEnd ℂ ρ)
    · rw [riemannZeta_conj, hz, map_zero]
    · exact h0
    · exact h1
    · simp only [conj_im]; linarith
    · simp only [conj_im]
      have hh := (neg_le_abs ρ.im).trans hfour
      exact hh
  · exact hpos ρ hz h0 h1 hp ((le_abs_self _).trans hfour)

/-- The strip zero set through height four is empty.
The nonreal case uses the rounded Rosser bound; the real axis uses the existing zeta sign proof.
Davenport chapter 15, supporting P0011 page 101. CONDITIONAL ON rvm_upper. -/
theorem zetaZeros_four_eq_empty193 :
    zetaZeros 4 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  by_cases him : ρ.im = 0
  · have he : (ρ.re : ℂ) = ρ := by
      apply Complex.ext <;> simp [him]
    have hn := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg hρ.2.1 hρ.2.2.1).2
    rw [he, hρ.1] at hn
    norm_num at hn
  · exact zeta_small_nonreal193 hρ.2.1 hρ.2.2.1 him hρ.2.2.2 hρ.1

/-- LEAF. `ζ` has no non-trivial zero with `|Im ρ| < 14`; the lowest ordinate is
`14.1347...`. Proof route: the explicit Riemann-von Mangoldt bound with Rosser's constants,
or a certified zero count by the argument principle. Rosser 1941, Ann. of Math. 42, Theorem 19
and Table; Davenport ch. 15. Unit U-1529. -/
theorem zetaZeros_eq_empty {T : ℝ} (hT : T < 14) : zetaZeros T = ∅ := by
  by_cases hfour : T ≤ 4
  · have hsub : zetaZeros T ⊆ zetaZeros 4 := by
      intro ρ hρ
      exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans hfour⟩
    apply Set.eq_empty_of_subset_empty
    rwa [zetaZeros_four_eq_empty193] at hsub
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    by_cases hlow : |ρ.im| ≤ 4
    · have hzfour : ρ ∈ zetaZeros 4 := ⟨hρ.1, hρ.2.1, hρ.2.2.1, hlow⟩
      rw [zetaZeros_four_eq_empty193] at hzfour
      exact hzfour
    · by_cases hhalf : ρ.re = 1/2
      · exact zeta_critical_height_fourteen193 hhalf (hρ.2.2.2.trans hT.le) hρ.1
      · have hband : 4 < |ρ.im| ∧ |ρ.im| < 14 ∧ ρ.re ≠ 1/2 :=
          ⟨lt_of_not_ge hlow, lt_of_le_of_lt hρ.2.2.2 hT, hhalf⟩
        /- LEAF. Remaining case only: an off-critical-line strip zero with
        4 < absolute ordinate < 14. Heights through four and the entire critical line
        through fourteen are handled by proved helpers above.
        Rosser 1941 Theorem 19 and table, or a certified argument-principle count.
        Davenport, Multiplicative Number Theory, chapter 15; P0011 page 101 support. -/
        sorry

/-- LEAF. Sum over zeros: for `T ≥ 15`, `∑_{|γ| ≤ T} m_ρ / |ρ| ≤ 0.2 log² T`. The true size is
`(1/2π) log²(T/2π) + O(1)`; partial summation `∑_{0<γ≤T} 1/γ = N(T)/T + ∫ N(t)/t² dt` with
`rvm_upper` gives at most `0.076 log² T` on the positive side for `15 ≤ T ≤ 10^30` (checked
numerically in this unit) and `(1/4π + o(1)) log² T` beyond, and `|ρ| ≥ |γ|`.
Davenport ch. 17, p. 108; Rosser 1941 Theorem 19. Unit U-1529. -/
theorem zero_recip_sum {T : ℝ} (hT : 15 ≤ T) (hfin : (zetaZeros T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) ≤ 0.2 * Real.log T ^ 2 := by
  classical
  have hT0 : 0 < T := by linarith
  let s := hfin.toFinset
  let w : ℂ → ℝ := fun ρ => zetaMult ρ
  let x : ℂ → ℝ := fun ρ => |ρ.im|
  let B : ℝ → ℝ := fun t => t / 3 * Real.log t - t / 2 + 6 / 5 * Real.log t + 5
  have hw (ρ : ℂ) : 0 ≤ w ρ := Nat.cast_nonneg _
  have h14 {u : ℝ} {ρ : ℂ} (hρ : ρ ∈ zetaZeros u) : 14 ≤ |ρ.im| := by
    by_contra hh
    have hz : ρ ∈ zetaZeros |ρ.im| := ⟨hρ.1, hρ.2.1, hρ.2.2.1, le_rfl⟩
    rw [zetaZeros_eq_empty (lt_of_not_ge hh)] at hz
    exact hz
  have hp (t : ℝ) : (zetaZerosPos t).Finite := by
    apply (zetaZeros_finite t).subset
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩
  have hc (t : ℝ) (ht : 14 ≤ t) :
      (∑ ρ ∈ (zetaZeros_finite t).toFinset, w ρ) ≤ B t := by
    have he := zeta_count_both193 (zetaZeros_finite t) (hp t)
      (fun ρ hρ hzero => by have hh := h14 hρ; rw [hzero, abs_zero] at hh; linarith)
    change (∑ ρ ∈ (zetaZeros_finite t).toFinset, (zetaMult ρ : ℝ)) ≤ _
    rw [he]
    exact zeta_count_envelope193 ht (hp t)
  have hcut (t : ℝ) (ht : 14 ≤ t) :
      (∑ ρ ∈ s.filter (fun ρ => x ρ < t), w ρ) ≤ B t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => hw ρ)) (hc t ht)
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρ, hxt⟩
    have hρ := hfin.mem_toFinset.mp hρ
    exact (zetaZeros_finite t).mem_toFinset.mpr ⟨hρ.1, hρ.2.1, hρ.2.2.1, hxt.le⟩
  have hx (ρ : ℂ) (hρ : ρ ∈ s) : 14 ≤ x ρ ∧ x ρ ≤ T :=
    ⟨h14 (hfin.mem_toFinset.mp hρ), (hfin.mem_toFinset.mp hρ).2.2.2⟩
  obtain ⟨hint, hpartial⟩ := reciprocal_sum_partial193 s x w (by norm_num : (0 : ℝ) < 14)
    (by linarith : (14 : ℝ) ≤ T) hx
  have hboundary : (∑ ρ ∈ s, w ρ) ≤ B T := hc T (by linarith)
  have hnorm : (∑ ρ ∈ s, w ρ / ‖ρ‖) ≤ ∑ ρ ∈ s, w ρ / x ρ := by
    apply Finset.sum_le_sum
    intro ρ hρ
    exact div_le_div_of_nonneg_left (hw ρ) (by have := (hx ρ hρ).1; dsimp [x] at *; linarith)
      (Complex.abs_im_le_norm ρ)
  have hn (t : ℝ) (ht : t ∈ Set.uIcc (14 : ℝ) T) : t ≠ 0 := by
    rw [Set.uIcc_of_le (by linarith : (14 : ℝ) ≤ T)] at ht
    linarith [ht.1]
  have hcont : ContinuousOn (fun t => B t / t^2) (Set.uIcc (14 : ℝ) T) := by
    have hl : ContinuousOn Real.log (Set.uIcc (14 : ℝ) T) :=
      continuousOn_id.log (fun t ht => hn t ht)
    apply ContinuousOn.div
    · exact (((((continuousOn_id.div_const 3).mul hl).sub (continuousOn_id.div_const 2)).add
        (continuousOn_const.mul hl)).add continuousOn_const)
    · exact continuousOn_id.pow 2
    · intro t ht; exact pow_ne_zero 2 (hn t ht)
  let F : ℝ → ℝ := fun t => Real.log t ^ 2 / 6 - Real.log t / 2 -
    (6/5 * (Real.log t + 1) + 5) / t
  have hIntegral : (∫ t in (14 : ℝ)..T, B t / t^2) = F T - F 14 := by
    have hd (t : ℝ) (ht : t ∈ Set.uIcc (14 : ℝ) T) : HasDerivAt F (B t/t^2) t := by
      have hl := Real.hasDerivAt_log (hn t ht)
      convert (((hl.pow 2).div_const 6).sub (hl.div_const 2)).sub
        ((((hl.add_const 1).const_mul (6/5)).add_const 5).div (hasDerivAt_id t) (hn t ht)) using 1
      · ext y; simp [F]
      · dsimp only [B, id_eq]
        field_simp [hn t ht]
        <;> ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hIntle := intervalIntegral.integral_mono_on (by linarith : (14 : ℝ) ≤ T)
    hint hcont.intervalIntegrable
    (fun t ht => div_le_div_of_nonneg_right (hcut t ht.1) (sq_nonneg t))
  rw [hIntegral] at hIntle
  have hdiv := div_le_div_of_nonneg_right hboundary hT0.le
  have htotal : (∑ ρ ∈ s, w ρ / ‖ρ‖) ≤ B T / T + F T - F 14 := by linarith
  have he : B T / T + F T - F 14 = Real.log T^2/6 - Real.log T/6 -
      6/(5*T) - 1/2 - F 14 := by
    dsimp [B, F]
    field_simp
    <;> ring
  rw [he] at htotal
  have hbase : -1/2 - F 14 ≤ (1/2 : ℝ) := by
    dsimp [F]
    nlinarith [sq_nonneg (Real.log 14 - 123/70)]
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    apply (Real.le_log_iff_exp_le (by norm_num)).mpr
    have := Real.exp_one_lt_d9
    linarith
  have hlog12 : (7/3 : ℝ) ≤ Real.log 12 := by
    have he : Real.log 12 = Real.log 3 + 2 * Real.log 2 := by
      rw [show (12 : ℝ) = 3 * 2^2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    rw [he]
    linarith [Real.log_two_gt_d9]
  have hL : (7/3 : ℝ) ≤ Real.log T := hlog12.trans (Real.log_le_log (by norm_num) (by linarith))
  have hnfrac : 0 ≤ 6/(5*T) := by positivity
  change (∑ ρ ∈ s, w ρ / ‖ρ‖) ≤ _
  nlinarith [sq_nonneg (Real.log T - 7/3)]

/-! ### Zeros of Dirichlet L-functions -/

/-- LEAF. For each Dirichlet character `χ` and real `T`, `L(s, χ)` has only finitely many zeros
in the open strip with `|Im ρ| ≤ T`: it is entire for `χ ≠ 1`, has only the pole at 1 for the
trivial character, and is not identically zero, so zeros are isolated and cannot accumulate at
the pole. Davenport ch. 16 and 19; Mathlib `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.
Unit U-1529. -/
theorem LZeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (LZeros χ T).Finite := by
  have hb : ∀ z ∈ LZeros χ T, ‖z‖ ≤ |T| + 2 := by
    intro z hz
    have ht : |z.im| ≤ |T| := hz.2.2.2.trans (le_abs_self T)
    have hr : |z.re| ≤ 1 := by rw [abs_of_pos hz.2.1]; exact hz.2.2.1.le
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have finite_zeros : ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∃ z, f z ≠ 0) → {z : ℂ | ‖z‖ ≤ |T| + 2 ∧ f z = 0}.Finite := by
    intro f hf ⟨w, hw⟩
    have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
    have hd : f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ := by
      simpa [Filter.codiscrete] using ha.preimage_zero_mem_codiscreteWithin hw (Set.mem_univ w)
        isConnected_univ
    have hclosed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hf.continuous
    have hdiscrete : IsDiscrete (f ⁻¹' {0}) := by
      simpa using (mem_codiscrete'.mp hd).2
    have hcompact := (isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_right hclosed
    have hfinite := hcompact.finite (hdiscrete.mono Set.inter_subset_right)
    convert hfinite using 1
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  by_cases hχ : χ = 1
  · subst χ
    have hf := finite_zeros (DirichletCharacter.LFunctionTrivChar₁ q)
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
      ⟨1, DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q⟩
    apply hf.subset
    intro z hz
    refine ⟨hb z hz, ?_⟩
    have hz1 : z ≠ 1 := by intro h; simpa [h] using hz.2.2.1
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz1]
    exact mul_eq_zero_of_right _ hz.1
  · have hf := finite_zeros (DirichletCharacter.LFunction χ)
      (DirichletCharacter.differentiable_LFunction hχ)
      ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)⟩
    apply hf.subset
    intro z hz
    exact ⟨hb z hz, hz.1⟩

/-- Changing level preserves positive-half-plane zeros and their orders away from the pole.
P0011 page 101, supporting zero sums; Mathlib LFunction_changeLevel, Euler factors. -/
theorem changeLevel_zero_data193 {m n : ℕ} [NeZero m] [NeZero n] (hmn : m ∣ n)
    (χ : DirichletCharacter ℂ m) {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    (DirichletCharacter.LFunction (DirichletCharacter.changeLevel hmn χ) ρ = 0 ↔
      DirichletCharacter.LFunction χ ρ = 0) ∧
    LMult (DirichletCharacter.changeLevel hmn χ) ρ = LMult χ ρ := by
  let P : ℂ → ℂ := fun s => ∏ p ∈ n.primeFactors, (1 - χ p * (p : ℂ)^(-s))
  have hP : P ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp' : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : ‖(p : ℂ)^(-ρ)‖ < 1 := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp' (by simpa using hρ)
    have hn : ‖χ p * (p : ℂ)^(-ρ)‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one p)) hpow
    intro hh
    have he : χ p * (p : ℂ)^(-ρ) = 1 := (sub_eq_zero.mp hh).symm
    rw [he, norm_one] at hn
    exact lt_irrefl _ hn
  have hPD : Differentiable ℂ P := by
    intro s
    dsimp [P]
    apply DifferentiableAt.fun_finsetProd
    intro p hp
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    · intro s hs
      exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
    · exact isOpen_compl_singleton.mem_nhds hρ1
  have he : DirichletCharacter.LFunction (DirichletCharacter.changeLevel hmn χ) =ᶠ[𝓝 ρ]
      (DirichletCharacter.LFunction χ * P) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hρ1] with s hs
    exact DirichletCharacter.LFunction_changeLevel hmn χ (Or.inr hs)
  constructor
  · rw [DirichletCharacter.LFunction_changeLevel hmn χ (Or.inr hρ1), mul_eq_zero]
    exact or_iff_left hP
  · dsimp [LMult, analyticOrderNatAt]
    rw [analyticOrderAt_congr he, analyticOrderAt_mul hL (hPD.analyticAt ρ),
      analyticOrderAt_eq_zero.mpr (Or.inr hP), add_zero]

/-- LEAF. Helfgott, Major arcs for Goldbach's problem, arXiv:1305.2897v4,
page 37 equation 4.25 and page 38 equation 4.26. Primitive characters only.
The error is 0.5 log qT plus 17.7. The proof cites Rosser 1941 and McCurley 1984 Theorem 2.1. -/
theorem primitive_zero_count193 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T) (hfin : (LZeros χ T).Finite) :
    |(∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) -
      T / Real.pi * Real.log (q * T / (2 * Real.pi * Real.exp 1))| ≤
        0.5 * Real.log (q * T) + 17.7 := by
  sorry

/-- LEAF. Zero count for `L(s, χ)`: for `T ≥ 1`, the zeros in the open strip with `|γ| ≤ T`,
counted with multiplicity, number at most `(T/π) log(qT) + 2 log(q(T + 2)) + 20`.
For primitive `χ` mod `q ≥ 3` McCurley 1984, Math. Comp. 43, Theorem 2.1, gives
`N(T, χ) ≤ (T/π) log(qT/2πe) + 0.9185 log(qT) + 5.512`; an imprimitive character has the
strip zeros of its primitive inducing character of modulus `q* ∣ q`; the trivial character has
those of `ζ`, two copies of `rvm_upper`. Davenport ch. 16, p. 101. Unit U-1529. -/
theorem LZeros_count {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (LZeros χ T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) ≤
      T / Real.pi * Real.log (q * T) + 2 * Real.log (q * (T + 2)) + 20 := by
  classical
  let c := χ.conductor
  have hc0 : 0 < c := Nat.pos_of_ne_zero χ.conductor_ne_zero
  haveI : NeZero c := ⟨hc0.ne'⟩
  let χ₀ := χ.primitiveCharacter
  have hχ : DirichletCharacter.changeLevel χ.conductor_dvd_level χ₀ = χ :=
    χ.changeLevel_primitiveCharacter
  have hsum : (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ)) ≤
      ∑ ρ ∈ (LZeros_finite χ₀ T).toFinset, (LMult χ₀ ρ : ℝ) := by
    have he (ρ : ℂ) (hρ : ρ ∈ hfin.toFinset) : LMult χ ρ = LMult χ₀ ρ := by
      have hz := hfin.mem_toFinset.mp hρ
      have hz1 : ρ ≠ 1 := by intro hh; have hh' := hz.2.2.1; simpa [hh] using hh'
      simpa only [hχ] using (changeLevel_zero_data193 χ.conductor_dvd_level χ₀ hz.2.1 hz1).2
    rw [Finset.sum_congr rfl (fun ρ hρ => congrArg (fun k : ℕ => (k : ℝ)) (he ρ hρ))]
    apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => Nat.cast_nonneg _)
    intro ρ hρ
    have hz := hfin.mem_toFinset.mp hρ
    have hz1 : ρ ≠ 1 := by intro hh; have hh' := hz.2.2.1; simpa [hh] using hh'
    have hh := (changeLevel_zero_data193 χ.conductor_dvd_level χ₀ hz.2.1 hz1).1
    rw [hχ] at hh
    exact (LZeros_finite χ₀ T).mem_toFinset.mpr ⟨hh.mp hz.1, hz.2⟩
  have hprim := (abs_le.mp (primitive_zero_count193 χ₀ χ.primitiveCharacter_isPrimitive hT
    (LZeros_finite χ₀ T))).2
  have hcleq : (c : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hcr0 : (0 : ℝ) < c := by exact_mod_cast hc0
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have ht0 : 0 < T := by linarith
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc0
  have hC : 0 ≤ Real.log (c * T) := Real.log_nonneg (by nlinarith [mul_le_mul_of_nonneg_left hT hcr0.le])
  have hlogc : Real.log (c * T) ≤ Real.log (q * T) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right hcleq ht0.le)
  have hlogT : Real.log (q * T) ≤ Real.log (q * (T + 2)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hden : 0 ≤ Real.log (2 * Real.pi * Real.exp 1) := Real.log_nonneg (by
    have hh := Real.add_one_le_exp (1 : ℝ)
    nlinarith [Real.pi_gt_three])
  rw [Real.log_div (by positivity : (c : ℝ) * T ≠ 0) (by positivity : 2 * Real.pi * Real.exp 1 ≠ 0)] at hprim
  have hmain : T / Real.pi * (Real.log (c * T) - Real.log (2 * Real.pi * Real.exp 1)) ≤
      T / Real.pi * Real.log (q * T) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- LEAF. Sum of `1/|ρ|` over zeros of `L(s, χ)` on the critical line: if every zero of
`L(s, χ)` in the strip with `|γ| ≤ T` has real part `1/2`, then for `T ≥ 1`
`∑ m_ρ/|ρ| ≤ log(qT) log T + 10 log(qT) + 100`. Zeros with `|γ| ≤ 1` have `|ρ| ≥ 1/2` and
number at most `LZeros_count` at 1; the rest by partial summation against `LZeros_count`,
`∫_1^T (1/πt) log(qt) dt = (log q log T + log² T/2)/π`. Davenport ch. 19, p. 117-118.
Unit U-1529. -/
theorem LZeros_recip_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} (hT : 1 ≤ T)
    (hfin : (LZeros χ T).Finite) (hline : ∀ ρ ∈ LZeros χ T, ρ.re = 1 / 2) :
    (∑ ρ ∈ hfin.toFinset, (LMult χ ρ : ℝ) / ‖ρ‖) ≤
      Real.log (q * T) * Real.log T + 10 * Real.log (q * T) + 100 := by
  classical
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) < q := by linarith
  have hT0 : 0 < T := by linarith
  let A := Real.log (q : ℝ)
  let s := hfin.toFinset
  let w : ℂ → ℝ := fun ρ => LMult χ ρ
  let x : ℂ → ℝ := fun ρ => max 1 |ρ.im|
  let B : ℝ → ℝ := fun t => t / 2 * (A + Real.log t) + 2 * A + 2 * t + 24
  have hA : 0 ≤ A := Real.log_nonneg hq
  have hL : 0 ≤ Real.log T := Real.log_nonneg hT
  have hc (t : ℝ) (ht : 1 ≤ t) :
      (∑ ρ ∈ (LZeros_finite χ t).toFinset, w ρ) ≤ B t := by
    have ht0 : 0 < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    have hc := LZeros_count χ ht (LZeros_finite χ t)
    rw [Real.log_mul hq0.ne' ht0.ne', Real.log_mul hq0.ne' (by linarith : t + 2 ≠ 0)] at hc
    have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < t + 2)
    have hp : t / Real.pi ≤ t / 2 := by
      apply div_le_div_of_nonneg_left ht0.le (by norm_num)
      linarith [Real.pi_gt_three]
    have hm := mul_le_mul_of_nonneg_right hp (add_nonneg hA hlog)
    dsimp [B, A, w] at *
    linarith
  have hw (ρ : ℂ) : 0 ≤ w ρ := Nat.cast_nonneg _
  have hcut (t : ℝ) (ht : 1 ≤ t) :
      (∑ ρ ∈ s.filter (fun ρ => x ρ < t), w ρ) ≤ B t := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => hw ρ)) (hc t ht)
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρ, hxt⟩
    have hρ := hfin.mem_toFinset.mp hρ
    apply (LZeros_finite χ t).mem_toFinset.mpr
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, (le_max_right 1 |ρ.im|).trans hxt.le⟩
  have hx (ρ : ℂ) (hρ : ρ ∈ s) : 1 ≤ x ρ ∧ x ρ ≤ T := by
    have hρ := hfin.mem_toFinset.mp hρ
    exact ⟨le_max_left _ _, max_le hT hρ.2.2.2⟩
  obtain ⟨hint, hpartial⟩ := reciprocal_sum_partial193 s x w one_pos hT hx
  have hboundary : (∑ ρ ∈ s, w ρ) ≤ B T := hc T hT
  have hlow : (∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 1), w ρ) ≤ B 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun ρ _ _ => hw ρ)) (hc 1 le_rfl)
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρ, him⟩
    have hρ := hfin.mem_toFinset.mp hρ
    exact (LZeros_finite χ 1).mem_toFinset.mpr ⟨hρ.1, hρ.2.1, hρ.2.2.1, him⟩
  have hnorm : (∑ ρ ∈ s, w ρ / ‖ρ‖) ≤ (∑ ρ ∈ s, w ρ / x ρ) +
      ∑ ρ ∈ s.filter (fun ρ => |ρ.im| ≤ 1), w ρ := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hlineρ := hline ρ (hfin.mem_toFinset.mp hρ)
    have hn : (1/2 : ℝ) ≤ ‖ρ‖ := by
      have hh := Complex.abs_re_le_norm ρ
      rw [hlineρ] at hh
      norm_num at hh ⊢
      exact hh
    by_cases him : |ρ.im| ≤ 1
    · simp only [if_pos him]
      have he : x ρ = 1 := max_eq_left him
      rw [he, div_one]
      have hh : w ρ / ‖ρ‖ ≤ w ρ / (1/2) :=
        div_le_div_of_nonneg_left (hw ρ) (by norm_num) hn
      linarith
    · simp only [if_neg him, add_zero]
      have he : x ρ = |ρ.im| := max_eq_right (le_of_not_ge him)
      rw [he]
      exact div_le_div_of_nonneg_left (hw ρ) (by linarith [lt_of_not_ge him]) (Complex.abs_im_le_norm ρ)
  have hn (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) T) : t ≠ 0 := by
    rw [Set.uIcc_of_le hT] at ht
    linarith [ht.1]
  have hcont : ContinuousOn (fun t => B t / t^2) (Set.uIcc (1 : ℝ) T) := by
    have hc : ContinuousOn Real.log (Set.uIcc (1 : ℝ) T) :=
      continuousOn_id.log (fun t ht => hn t ht)
    apply ContinuousOn.div
    · exact (((((continuousOn_id.div_const 2).mul (continuousOn_const.add hc)).add
        continuousOn_const).add (continuousOn_const.mul continuousOn_id)).add continuousOn_const)
    · exact continuousOn_id.pow 2
    · intro t ht; exact pow_ne_zero 2 (hn t ht)
  have hIntegral : (∫ t in (1 : ℝ)..T, B t / t^2) =
      (A + Real.log T)^2 / 4 + 2 * Real.log T - (2*A+24)/T -
      (A^2/4 - (2*A+24)) := by
    let F : ℝ → ℝ := fun t => (A + Real.log t)^2 / 4 + 2 * Real.log t - (2*A+24)/t
    have hd (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) T) : HasDerivAt F (B t/t^2) t := by
      have hl := Real.hasDerivAt_log (hn t ht)
      convert (((hl.const_add A).pow 2).div_const 4 |>.add (hl.const_mul 2)).sub
        ((hasDerivAt_const t (2*A+24)).div (hasDerivAt_id t) (hn t ht)) using 1
      · ext y; simp [F]
      · dsimp only [B, id_eq]
        field_simp [hn t ht]
        <;> ring
    simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hIntle := intervalIntegral.integral_mono_on hT hint hcont.intervalIntegrable
    (fun t ht => div_le_div_of_nonneg_right (hcut t ht.1) (sq_nonneg t))
  have hdiv := div_le_div_of_nonneg_right hboundary hT0.le
  have htotal : (∑ ρ ∈ s, w ρ / ‖ρ‖) ≤ B 1 + B T / T +
      (A + Real.log T)^2 / 4 + 2 * Real.log T - (2*A+24)/T -
      (A^2/4 - (2*A+24)) := by
    rw [hIntegral] at hIntle
    linarith
  have he : B 1 + B T / T + (A + Real.log T)^2 / 4 + 2 * Real.log T -
      (2*A+24)/T - (A^2/4 - (2*A+24)) =
      5 * A + 52 + 5/2 * Real.log T + A * Real.log T / 2 + Real.log T^2 / 4 := by
    dsimp [B]
    simp only [Real.log_one, add_zero, one_div, div_one]
    field_simp
    <;> ring
  rw [he] at htotal
  have hlogqt : Real.log (q * T) = A + Real.log T := Real.log_mul hq0.ne' hT0.ne'
  rw [hlogqt]
  change (∑ ρ ∈ s, w ρ / ‖ρ‖) ≤ _
  nlinarith [mul_nonneg hA hL, sq_nonneg (Real.log T)]

/-! ### Links and vacuity -/

/-- Under P0011's `GRH`, every zero in `zetaZeros T` lies on the critical line. Proved. -/
theorem re_eq_half_of_GRH (hG : GRH) {T : ℝ} {ρ : ℂ} (h : ρ ∈ zetaZeros T) :
    ρ.re = 1 / 2 :=
  zeta_strip_of_GRH hG ρ h.1 h.2.1 h.2.2.1

/-- Under P0011's `GRH`, every zero in `LZeros χ T` lies on the critical line, so
`LZeros_recip_sum` applies to every `χ`. Proved. -/
theorem L_re_eq_half_of_GRH (hG : GRH) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {T : ℝ} : ∀ ρ ∈ LZeros χ T, ρ.re = 1 / 2 :=
  fun ρ h => hG q χ ρ h.1 h.2.1 h.2.2.1

/-- Vacuity: the hypotheses `T ≥ e`, `T ≥ 15`, `T ≥ 1` of the leaves hold at `T = 15`. -/
example : Real.exp 1 ≤ (15 : ℝ) ∧ (15 : ℝ) ≤ 15 ∧ (1 : ℝ) ≤ 15 := by
  refine ⟨?_, le_rfl, by norm_num⟩
  have := Real.exp_one_lt_d9
  linarith


/-! ### CODEX task193, concrete instances
The conditional height inputs remain named. AI wrote the Lean code. Goldbach is open. -/

example : (∫ t : ℝ in (1 : ℝ)..2, 1 / t^2) = 1/2 := by
  convert reciprocal_integral193 (a := 1) (b := 2) (by norm_num) (by norm_num) using 1 <;> norm_num

example : IntervalIntegrable (fun t : ℝ =>
    (∑ i ∈ ({1, 2} : Finset ℕ).filter (fun i : ℕ => (i : ℝ) < t), (1 : ℝ)) / t^2) volume 1 2 := by
  apply (reciprocal_sum_partial193 ({1, 2} : Finset ℕ) (fun i => (i : ℝ)) (fun _ => 1)
    one_pos (by norm_num) ?_).1
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> norm_num

example : zetaZeros (-1) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  have hh := hρ.2.2.2
  linarith [abs_nonneg ρ.im]

example : ∃ hf : (zetaZeros (-1)).Finite, ∃ hp : (zetaZerosPos (-1)).Finite,
    ∀ ρ ∈ zetaZeros (-1), ρ.im ≠ 0 := by
  have hp : (zetaZerosPos (-1)).Finite := by
    apply (zetaZeros_finite (-1)).subset
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩
  refine ⟨zetaZeros_finite (-1), hp, ?_⟩
  intro ρ hρ hzero
  have hh := hρ.2.2.2
  rw [hzero, abs_zero] at hh
  linarith

example : Real.exp 1 ≤ (3 : ℝ) ∧ (zetaZerosPos 3).Finite := by
  refine ⟨by linarith [Real.exp_one_lt_d9], ?_⟩
  apply (zetaZeros_finite 3).subset
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩

example : (14 : ℝ) ≤ 14 ∧ (zetaZerosPos 14).Finite := by
  refine ⟨le_rfl, ?_⟩
  apply (zetaZeros_finite 14).subset
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by rw [abs_of_pos hρ.2.2.2.1]; exact hρ.2.2.2.2⟩

example : (15 : ℝ) ≤ 15 ∧ (zetaZeros 15).Finite := ⟨le_rfl, zetaZeros_finite 15⟩

example : (1 : DirichletCharacter ℂ 1).IsPrimitive ∧ (1 : ℝ) ≤ 1 ∧
    (LZeros (1 : DirichletCharacter ℂ 1) 1).Finite :=
  ⟨DirichletCharacter.isPrimitive_one_level_one, le_rfl, LZeros_finite _ _⟩

/-- This line instance remains conditional on the cited height-fourteen leaf. -/
example : ∀ ρ ∈ LZeros (1 : DirichletCharacter ℂ 1) 1, ρ.re = 1/2 := by
  intro ρ hρ
  have hz : riemannZeta ρ = 0 := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using hρ.1
  have hh : ρ ∈ zetaZeros 1 := ⟨hz, hρ.2⟩
  rw [zetaZeros_eq_empty (by norm_num : (1 : ℝ) < 14)] at hh
  exact False.elim hh

example : LMult (DirichletCharacter.changeLevel (by decide : 1 ∣ 4)
      (1 : DirichletCharacter ℂ 1)) ((1/2 : ℂ) + I) =
    LMult (1 : DirichletCharacter ℂ 1) ((1/2 : ℂ) + I) := by
  apply (changeLevel_zero_data193 (by decide : 1 ∣ 4) (1 : DirichletCharacter ℂ 1)
    (by norm_num) ?_).2
  intro h
  have hh := congrArg Complex.re h
  norm_num at hh

example : 0 < ((1/2 : ℂ) + I).re ∧ ((1/2 : ℂ) + I).re < 1 ∧
    ((1/2 : ℂ) + I).im ≠ 0 ∧ |((1/2 : ℂ) + I).im| ≤ 4 := by norm_num

end LeanLab.DERZ1997.Decomp1529a
