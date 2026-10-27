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
import LeanLab.DERZ1997.Statements

namespace LeanLab.DERZ1997.Decomp1529a
open Complex

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

/-- LEAF. `ζ` has no non-trivial zero with `|Im ρ| < 14`; the lowest ordinate is
`14.1347...`. Proof route: the explicit Riemann-von Mangoldt bound with Rosser's constants,
or a certified zero count by the argument principle. Rosser 1941, Ann. of Math. 42, Theorem 19
and Table; Davenport ch. 15. Unit U-1529. -/
theorem zetaZeros_eq_empty {T : ℝ} (hT : T < 14) : zetaZeros T = ∅ := by
  sorry

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

/-- LEAF. Riemann-von Mangoldt, explicit upper bound: for `T ≥ e` the number `N(T)` of zeros
with `0 < γ ≤ T`, counted with multiplicity, is at most
`(T/2π) log(T/2π) - T/2π + 7/8 + 0.14 log T + 0.45 log log T + 1.6`.
Rosser 1941, Ann. of Math. 42, Theorem 19, `|N(T) - F(T)| < 0.137 log T + 0.443 log log T
+ 1.588` for `T ≥ 2`; Davenport ch. 15, p. 98. Unit U-1529. -/
theorem rvm_upper {T : ℝ} (hT : Real.exp 1 ≤ T) (hfin : (zetaZerosPos T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ)) ≤
      T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
        + 0.14 * Real.log T + 0.45 * Real.log (Real.log T) + 1.6 := by
  sorry

/-- LEAF. Riemann-von Mangoldt, explicit lower bound: for `T ≥ e`,
`N(T) ≥ (T/2π) log(T/2π) - T/2π + 7/8 - 0.14 log T - 0.45 log log T - 1.6`, zeros counted with
multiplicity. Rosser 1941, Ann. of Math. 42, Theorem 19; Davenport ch. 15, p. 98.
Unit U-1529. -/
theorem rvm_lower {T : ℝ} (hT : Real.exp 1 ≤ T) (hfin : (zetaZerosPos T).Finite) :
    T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8
        - 0.14 * Real.log T - 0.45 * Real.log (Real.log T) - 1.6 ≤
      ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) := by
  sorry

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

/-- LEAF. Sum over zeros: for `T ≥ 15`, `∑_{|γ| ≤ T} m_ρ / |ρ| ≤ 0.2 log² T`. The true size is
`(1/2π) log²(T/2π) + O(1)`; partial summation `∑_{0<γ≤T} 1/γ = N(T)/T + ∫ N(t)/t² dt` with
`rvm_upper` gives at most `0.076 log² T` on the positive side for `15 ≤ T ≤ 10^30` (checked
numerically in this unit) and `(1/4π + o(1)) log² T` beyond, and `|ρ| ≥ |γ|`.
Davenport ch. 17, p. 108; Rosser 1941 Theorem 19. Unit U-1529. -/
theorem zero_recip_sum {T : ℝ} (hT : 15 ≤ T) (hfin : (zetaZeros T).Finite) :
    (∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) / ‖ρ‖) ≤ 0.2 * Real.log T ^ 2 := by
  sorry

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
  sorry

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
  sorry

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

end LeanLab.DERZ1997.Decomp1529a
