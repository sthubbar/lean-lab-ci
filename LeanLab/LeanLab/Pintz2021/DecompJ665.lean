import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581
import LeanLab.Pintz2021.DecompJ281
import LeanLab.Pintz2021.Truncation168

namespace LeanLab.Pintz2021.DecompJ665

open Complex Finset Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53
open LeanLab.Pintz2021.DecompJ281

attribute [local instance] Classical.propDecidable

noncomputable section

/-- LEAF arXiv:1804.05561v1 display 8.28: the epsilon threshold and core constants exist -/
theorem leaf_constants_exist :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c := by
  exact ⟨1, one_pos, fun _ _ _ => ⟨1, 0, 0, 0, one_pos⟩⟩

/-- REFUTED, `P_leaf_false` below. Repaired in `DecompJ579.leaf_P_exists`. Do not prove this.
LEAF arXiv:1804.05561v1 display 8.28: the major arc parameter P exists -/
theorem leaf_P_exists {ε H0 X0 H X P0 : ℝ} (hHyp : Thm1Hyp ε H0 X0 H X P0) :
  ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H (Real.sqrt X) P X).Finite := by sorry

/-- REFUTED, `singular_series_leaf_false` below, false at `m = 0`. Repaired in `DecompJ579.leaf_singular_series_converges`. Do not prove this.
LEAF arXiv:1804.05561v1 display 9.16: the singular series converges -/
theorem leaf_singular_series_converges (H X P : ℝ) :
  ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by sorry

private theorem singPartialPrime_pole_zero_eq :
    singPartialPrime pole pole 0 = singPartial pole pole 0 := by
  funext Q
  simp only [singPartialPrime, singPartial, cCoefPrime_pole]

private theorem pole_prime_zero_no_limit (s : ℂ) :
    ¬ Tendsto (singPartialPrime pole pole 0) atTop (𝓝 s) := by
  rw [singPartialPrime_pole_zero_eq]
  exact Audit168.zero_no_limit s

/-- LEAF arXiv:1804.05561v1 display 10.25: the main term error is bounded by a constant C depending only on ε -/
theorem leaf_main_term_bound_exists_C (ε ε0 c H0 C X0 : ℝ) :
  ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
    Thm1Hyp ε H0 X0 H X P0 →
    P0 * X ^ (-ε) ≤ P → P ≤ P0 →
    (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
      Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
    ∀ m : ℕ, (m : ℝ) ≤ X →
      ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
        C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  -- VACUOUS: the hypothesis demands `Tendsto (singPartialPrime pole pole 0) atTop (𝓝 _)`,
  -- but the pole series at zero frequency has no limit (`pole_prime_zero_no_limit`),
  -- and `pole ∈ excSet H (√X) P X` always. No `H X P0 P Sg'` satisfies the hypotheses.
  intro H X P0 P Sg' _ _ _ hconv
  exact absurd (hconv pole (pole_mem_excSet _ _ _ _) pole (pole_mem_excSet _ _ _ _) 0)
    (pole_prime_zero_no_limit _)

/-- Assembly theorem for P0054 page 8 display 2.21, proved directly from the leaves. -/
theorem assembly_221 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by
  obtain ⟨ε0, hε0, h1⟩ := leaf_constants_exist
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, H0, C, X0, hc⟩ := h1 ε hε hε0'
  refine ⟨c, H0, C, X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin⟩ := leaf_P_exists hHyp
  refine ⟨P, hP1, hP2, hFin, ?_⟩
  obtain ⟨Sg', hSg1⟩ := leaf_singular_series_converges H X P
  refine ⟨Sg', hSg1, ?_⟩
  exact leaf_main_term_bound_exists_C ε ε0 c H0 C X0 H X P0 P Sg' hHyp hP1 hP2 hSg1

/-- The exact convergence leaf fails at the pole and zero frequency. -/
theorem singular_series_leaf_false (H X P : ℝ) :
    ¬ (∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) := by
  rintro ⟨Sg', hconv⟩
  exact pole_prime_zero_no_limit (Sg' pole pole 0)
    (hconv pole (pole_mem_excSet _ _ _ _) pole (pole_mem_excSet _ _ _ _) 0)

/-- The parameter predicate permits a negative epsilon with an empty P interval. -/
theorem negative_epsilon_hyp : Thm1Hyp (-1) 0 0 0 4 1 := by
  refine ⟨le_refl _, ?_, by norm_num, le_refl _, ?_⟩
  · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  · exact Real.one_le_rpow (by norm_num) (by norm_num)

/-- The conclusion of the exact P leaf is false in that admitted parameter instance. -/
theorem negative_epsilon_no_P :
    ¬ (∃ P : ℝ, (1 : ℝ) * 4 ^ (-(-1 : ℝ)) ≤ P ∧ P ≤ 1 ∧
      (excSet 0 (Real.sqrt 4) P 4).Finite) := by
  rintro ⟨P, hlow, hupp, _⟩
  norm_num at hlow
  linarith

/-- The full universally quantified P leaf is false as stated. -/
theorem P_leaf_false :
    ¬ (∀ {ε H0 X0 H X P0 : ℝ}, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite) := by
  intro h
  exact negative_epsilon_no_P (h negative_epsilon_hyp)

/-- A compact set contains only finitely many zeros of a Dirichlet L function. -/
theorem compact_Lzeros_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {K : Set ℂ} (hK : IsCompact K) :
    {s ∈ K | χ.LFunction s = 0}.Finite := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    let f := DirichletCharacter.LFunctionTrivChar₁ N
    have ha : AnalyticOnNhd ℂ f Set.univ :=
      (analyticOnNhd_univ_iff_differentiable).mpr
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ N)
    have hn : f 1 ≠ 0 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N
    have hd := ha.preimage_zero_mem_codiscrete hn
    have hz : {s ∈ K | f s = 0}.Finite := by
      simpa only [Set.sdiff_eq, Set.preimage_compl, compl_compl, Set.preimage_singleton, Set.inter_ofPred_eq_sep] using
        hK.finite_sdiff_of_mem_codiscreteWithin
          (Filter.codiscreteWithin_mono (Set.subset_univ K) hd)
    apply (hz.insert 1).subset
    intro s hs
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · apply Or.inr
      refine ⟨hs.1, ?_⟩
      simp [f, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1, hs.2]
  · have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
      (analyticOnNhd_univ_iff_differentiable).mpr
        (DirichletCharacter.differentiable_LFunction hχ)
    have hn : χ.LFunction 2 ≠ 0 := by
      rw [χ.LFunction_eq_LSeries (by norm_num)]
      exact χ.LSeries_ne_zero_of_one_lt_re (by norm_num)
    have hd := ha.preimage_zero_mem_codiscrete hn
    simpa only [Set.sdiff_eq, Set.preimage_compl, compl_compl, Set.preimage_singleton, Set.inter_ofPred_eq_sep] using
      hK.finite_sdiff_of_mem_codiscreteWithin
        (Filter.codiscreteWithin_mono (Set.subset_univ K) hd)

/-- A lower real part bound and a height bound leave finitely many L zeros. -/
theorem bounded_Lzeros_finite {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a U : ℝ) :
    {s : ℂ | χ.LFunction s = 0 ∧ a ≤ s.re ∧ |s.im| ≤ U}.Finite := by
  let K : Set ℂ := Complex.equivRealProdCLM.symm ''
    (Set.Icc a 1 ×ˢ Set.Icc (-U) U)
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  apply (compact_Lzeros_finite χ hK).subset
  intro s hs
  have hright : s.re ≤ 1 := by
    by_contra! hn
    have hnzero := χ.LSeries_ne_zero_of_one_lt_re hn
    rw [← χ.LFunction_eq_LSeries hn] at hnzero
    exact hnzero hs.1
  refine ⟨?_, hs.1⟩
  refine ⟨(s.re, s.im), ⟨⟨hs.2.1, hright⟩, abs_le.mp hs.2.2⟩, ?_⟩
  apply Complex.ext <;> rfl


/-- The exact exceptional set is finite at every real choice of parameters. -/
theorem excSet_finite (H U P X : ℝ) : (excSet H U P X).Finite := by
  classical
  let F : ℕ+ → Set ExcPair := fun r =>
    ⋃ χ : DirichletCharacter ℂ (r : ℕ),
      (fun ρ => (⟨r, inferInstance, χ, ρ⟩ : ExcPair)) ''
        {s : ℂ | χ.LFunction s = 0 ∧ 1 - H / Real.log X ≤ s.re ∧ |s.im| ≤ U}
  have hF : ∀ r : ℕ+, (F r).Finite := by
    intro r
    exact Set.finite_iUnion fun χ =>
      (bounded_Lzeros_finite χ (1 - H / Real.log X) U).image _
  have hS : {r : ℕ+ | (r : ℝ) ≤ P}.Finite := by
    apply ((Set.finite_Iic ⌊P⌋₊).preimage
      (fun a _ b _ h => Subtype.ext h)).subset
    intro r hr
    exact Nat.le_floor hr
  apply ((hS.biUnion fun r _ => hF r).insert pole).subset
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · apply Or.inr
    rcases z with ⟨r, hr, χ, ρ⟩
    let n : ℕ+ := ⟨r, Nat.pos_of_ne_zero hr.out⟩
    refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hz.1, ?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨χ, ?_⟩
    refine ⟨ρ, ⟨hz.2.2.1, ?_, hz.2.2.2.2⟩, rfl⟩
    linarith [hz.2.2.2.1]

/-- With nonnegative epsilon and scale at least one, P0 itself is admissible. -/
theorem P_exists_of_nonneg {ε H U X P0 : ℝ} (hε : 0 ≤ ε) (hX : 1 ≤ X)
    (hP0 : 0 ≤ P0) :
    ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧ (excSet H U P X).Finite := by
  refine ⟨P0, ?_, le_refl _, excSet_finite H U P0 X⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos hX (neg_nonpos.mpr hε)) hP0

/-- The exact pole coefficient agrees with the earlier principal character template. -/
theorem pole_coefficient_eq_template (q m : ℕ) :
    cCoefPrime pole pole q m =
      CharacterSumsTask53.generalizedCoeff (fun _ => 1) (fun _ => 1) q (m : ℤ) true := by
  simp [cCoefPrime, Audit168.lift_pole, tau, Audit168.cRam_one,
    CharacterSumsTask53.generalizedCoeff, CharacterSumsTask53.gaussSum, div_eq_mul_inv]
  ring

/-- At positive frequency the exact pole coefficient series is absolutely convergent. -/
theorem pole_coeff_summable_norm (m : ℕ) (hm : 0 < m) :
    Summable (fun q : ℕ => ‖cCoefPrime pole pole q m‖) := by
  simpa only [pole_coefficient_eq_template] using
    PrincipalSeriesTask99.principal_summable_norm m hm true

/-- At positive even frequency the exact pole series sums to Sing. -/
theorem pole_hasSum (m : ℕ) (hm : 0 < m) (he : Even m) :
    HasSum (fun q : ℕ => cCoefPrime pole pole q m) (Sing m : ℂ) := by
  simpa only [pole_coefficient_eq_template] using
    PrincipalSeriesTask99.principal_hasSum m hm he true

/-- The sealed partial sums converge to Sing at positive even frequency for the pole pair. -/
theorem pole_partial_tendsto (m : ℕ) (hm : 0 < m) (he : Even m) :
    Tendsto (singPartialPrime pole pole m) atTop (𝓝 (Sing m : ℂ)) := by
  have hz : cCoefPrime pole pole 0 m = 0 := by simp [cCoefPrime]
  have hlim := (pole_hasSum m hm he).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert hlim using 1
  funext Q
  simp only [Function.comp_apply]
  have hIco : Ico 1 (Q + 1) = Icc 1 Q := by ext q; simp only [mem_Ico, mem_Icc]; omega
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos Q), hIco]
  simp [singPartialPrime, show pole.r = 1 from rfl, hz]

/-- The repaired sealed truncated main term equals the finite retained pair sum. -/
theorem truncatedPrime_eq_finite (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P U : ℝ) (m : ℕ) :
    mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m =
      Truncation168.truncatedPrime E Sg ε X P U m := by
  have hmem (z : ExcPair) :
      (z ∈ (E : Set ExcPair) ∧ |z.ρ.im| ≤ U) =
        (z ∈ ((E.filter fun z => |z.ρ.im| ≤ U) : Set ExcPair)) := by
    apply propext
    simp
  simp only [mainTermTruncatedPrime]
  simp_rw [hmem]
  simp only [finsum_mem_coe_finset, Truncation168.truncatedPrime,
    Truncation168.retainedPairs, Truncation168.pairTerm, sum_filter, sum_product]
  apply sum_congr rfl
  intro z hz
  by_cases hzU : |z.ρ.im| ≤ U
  · simp only [hzU, ite_true, true_and]
    apply sum_congr rfl
    intro w hw
    by_cases hwU : |w.ρ.im| ≤ U <;> simp [hwU]
  · simp [hzU]

/-- Every exceptional parameter has real part at most one. -/
theorem excSet_re_le_one {H U P X : ℝ} {z : ExcPair}
    (hz : z ∈ excSet H U P X) : z.ρ.re ≤ 1 := by
  rcases hz with hz | hz
  · subst z
    norm_num [pole]
  · let := z.hr
    by_contra! hn
    have hnzero := z.χ.LSeries_ne_zero_of_one_lt_re hn
    rw [← z.χ.LFunction_eq_LSeries hn] at hnzero
    exact hnzero hz.2.2.1

/-- The actual truncated main term error is bounded by discarded series mass. -/
theorem actual_truncation_error_le_mass (H : ℝ) {X : ℝ} (hX : 0 ≤ X)
    (P U ε : ℝ) (m : ℕ) (Sg : ExcPair → ExcPair → ℕ → ℂ)
    (E : Finset ExcPair) (hE : (E : Set ExcPair) = excSet H (Real.sqrt X) P X) :
    ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X m -
      mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg ε X P U m‖ ≤
      X * ∑ p ∈ (E ×ˢ E) \ Truncation168.retainedPairs E P U m,
        ((mult p.1 * mult p.2 : ℕ) : ℝ) * ‖Sg p.1 p.2 m‖ := by
  rw [← hE, truncatedPrime_eq_finite]
  exact Truncation168.norm_truncation_error_le_mass E Sg ε hX P U m
    (fun z hz => excSet_re_le_one (by rw [← hE]; exact hz))

/-- Summability of the restricted coefficient sequence gives the exact partial sum limit. -/
theorem singPartialPrime_tendsto_of_summable (z w : ExcPair) (m : ℕ)
    (hs : Summable (fun q : ℕ =>
      if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0)) :
    Tendsto (singPartialPrime z w m) atTop
      (𝓝 (∑' q : ℕ, if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0)) := by
  let f : ℕ → ℂ := fun q => if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0
  have hz : f 0 = 0 := by simp [f, cCoefPrime]
  have hlim := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  convert hlim using 1
  funext Q
  simp only [Function.comp_apply]
  have hIco : Ico 1 (Q + 1) = Icc 1 Q := by
    ext q
    simp only [mem_Ico, mem_Icc]
    omega
  change singPartialPrime z w m Q = ∑ i ∈ range (Q + 1), f i
  rw [sum_range_eq_add_Ico _ (Nat.succ_pos Q), hIco, hz, zero_add]
  simp [singPartialPrime, f, sum_filter]

/-- The exact pole partial sums have a limit at every positive frequency. -/
theorem pole_partial_exists (m : ℕ) (hm : 0 < m) :
    ∃ s : ℂ, Tendsto (singPartialPrime pole pole m) atTop (𝓝 s) := by
  have hs := (pole_coeff_summable_norm m hm).of_norm
  have hs' : Summable (fun q : ℕ =>
      if Nat.lcm pole.r pole.r ∣ q then cCoefPrime pole pole q m else 0) := by
    simpa only [show pole.r = 1 from rfl, Nat.lcm_self, Nat.one_dvd, ite_true] using hs
  exact ⟨_, singPartialPrime_tendsto_of_summable pole pole m hs'⟩

/-- Inducing a character multiplies its integer values by the principal character. -/
theorem lift_apply_nat (z : ExcPair) {q : ℕ} (hq : z.r ∣ q) (a : ℕ) :
    lift z q (a : ZMod q) =
      z.χ (a : ZMod z.r) * CharacterSumsTask53.principalValue q a := by
  by_cases ha : a.Coprime q
  · have hc : lift z q (a : ZMod q) = z.χ (a : ZMod z.r) := by
      simp only [State1581.lift, hq, dite_true]
      simpa only [Int.cast_natCast] using
        DirichletCharacter.changeLevel_eq_cast_of_dvd' z.χ hq
          (Nat.isCoprime_iff_coprime.mpr ha)
    simp [hc, CharacterSumsTask53.principalValue, ha]
  · have hn : ¬ IsUnit (a : ZMod q) := fun h => ha ((ZMod.isUnit_iff_coprime a q).mp h)
    simp [MulChar.map_nonunit _ hn, CharacterSumsTask53.principalValue, ha]

/-- The exact induced Gauss factor agrees with the finite character template. -/
theorem tau_lift_inv (z : ExcPair) {q : ℕ} [NeZero q] (hq : z.r ∣ q) :
    tau q (lift z q)⁻¹ =
      CharacterSumsTask53.gaussSum
        (fun a => (starRingEnd ℂ) (z.χ (a : ZMod z.r)) *
          CharacterSumsTask53.principalValue q a) q := by
  unfold tau cRam CharacterSumsTask53.gaussSum CharacterSumsTask53.characterSum
  apply sum_congr rfl
  intro a _
  rw [← MulChar.star_apply', lift_apply_nat z hq a]
  by_cases ha : a.Coprime q
  · have hp : CharacterSumsTask53.principalValue q a = 1 := by exact ite_eq_left ha
    simp only [hp, mul_one]
    rfl
  · have hp : CharacterSumsTask53.principalValue q a = 0 := by exact ite_eq_right ha
    simp [hp]

/-- The exact induced mixed character sum agrees with the finite template. -/
theorem cRam_lifts (z w : ExcPair) {q : ℕ} [NeZero q]
    (hzq : z.r ∣ q) (hwq : w.r ∣ q) (m : ℤ) :
    cRam q (lift z q * (lift w q)⁻¹) m =
      CharacterSumsTask53.characterSum
        (fun a => z.χ (a : ZMod z.r) * (starRingEnd ℂ) (w.χ (a : ZMod w.r)) *
          CharacterSumsTask53.principalValue q a) q m := by
  unfold cRam CharacterSumsTask53.characterSum
  apply sum_congr rfl
  intro a _
  simp only [MulChar.mul_apply]
  rw [← MulChar.star_apply', lift_apply_nat z hzq a, lift_apply_nat w hwq a]
  by_cases ha : a.Coprime q
  · have hp : CharacterSumsTask53.principalValue q a = 1 := by exact ite_eq_left ha
    simp only [hp, mul_one]
    rfl
  · have hp : CharacterSumsTask53.principalValue q a = 0 := by exact ite_eq_right ha
    simp [hp]

/-- The sealed coefficient agrees with the earlier template at every common multiple. -/
theorem exact_coefficient_eq_template (z w : ExcPair) {q : ℕ}
    (hzq : z.r ∣ q) (hwq : w.r ∣ q) (m : ℕ) :
    cCoefPrime z w q m = CharacterSumsTask53.generalizedCoeff
      (fun a => z.χ (a : ZMod z.r)) (fun a => w.χ (a : ZMod w.r)) q (m : ℤ) true := by
  by_cases hq0 : q = 0
  · subst q
    simp [cCoefPrime, CharacterSumsTask53.generalizedCoeff]
  let : NeZero q := ⟨hq0⟩
  rw [cCoefPrime, cRam_lifts z w hzq hwq,
    tau_lift_inv z hzq, tau_lift_inv w hwq]
  unfold CharacterSumsTask53.generalizedCoeff
  simp only [ite_true, div_eq_mul_inv]
  ring

/-- CONDITIONAL ON absolute summability of the template, the exact series has a limit. -/
theorem series_exists_of_template_summable (z w : ExcPair) (m : ℕ)
    (hs : Summable (fun q : ℕ => ‖CharacterSumsTask53.generalizedCoeff
      (fun a => z.χ (a : ZMod z.r)) (fun a => w.χ (a : ZMod w.r)) q (m : ℤ) true‖)) :
    ∃ s : ℂ, Tendsto (singPartialPrime z w m) atTop (𝓝 s) := by
  have hbase := hs.of_norm
  have hmasked := hbase.indicator {q : ℕ | Nat.lcm z.r w.r ∣ q}
  have hexact : (fun q : ℕ => if Nat.lcm z.r w.r ∣ q then cCoefPrime z w q m else 0) =
      {q : ℕ | Nat.lcm z.r w.r ∣ q}.indicator
        (fun q => CharacterSumsTask53.generalizedCoeff
          (fun a => z.χ (a : ZMod z.r)) (fun a => w.χ (a : ZMod w.r)) q (m : ℤ) true) := by
    funext q
    by_cases hq : Nat.lcm z.r w.r ∣ q
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hq, ite_true]
      exact exact_coefficient_eq_template z w
        (dvd_trans (Nat.dvd_lcm_left _ _) hq) (dvd_trans (Nat.dvd_lcm_right _ _) hq) m
    · simp [hq]
  rw [← hexact] at hmasked
  exact ⟨_, singPartialPrime_tendsto_of_summable z w m hmasked⟩

/-- At level at most one, every actual exceptional parameter has modulus one. -/
theorem modulus_one_of_mem {H U P X : ℝ} (hP : P ≤ 1) {z : ExcPair}
    (hz : z ∈ excSet H U P X) : z.r = 1 := by
  rcases hz with hz | hz
  · subst z
    rfl
  · have hr : z.r ≤ 1 := by exact_mod_cast hz.1.trans hP
    exact Nat.le_antisymm hr (Nat.pos_of_ne_zero z.hr.out)

/-- A modulus one parameter induces the same characters as the pole. -/
theorem lift_eq_pole_of_modulus_one (z : ExcPair) (hr : z.r = 1) (q : ℕ) :
    State1581.lift z q = State1581.lift pole q := by
  rcases z with ⟨r, h, χ, ρ⟩
  dsimp at hr
  subst r
  have hχ : χ = 1 := Subsingleton.elim _ _
  simp only [State1581.lift, Nat.one_dvd, dite_true, hχ, map_one]
  exact (Audit168.lift_pole q).symm

/-- Two modulus one parameters have the same exact partial sums as the pole pair. -/
theorem partial_eq_pole_of_modulus_one (z w : ExcPair) (hz : z.r = 1) (hw : w.r = 1)
    (m : ℕ) : singPartialPrime z w m = singPartialPrime pole pole m := by
  funext Q
  simp only [singPartialPrime, hz, hw, show pole.r = 1 from rfl]
  apply sum_congr rfl
  intro q _
  simp only [cCoefPrime, lift_eq_pole_of_modulus_one z hz q,
    lift_eq_pole_of_modulus_one w hw q]

/-- At level at most one all actual exceptional pairs have convergent positive frequency series. -/
theorem level_one_series_converges (H X P : ℝ) (hP : P ≤ 1) :
    ∃ Sg : ExcPair → ExcPair → ℕ → ℂ,
      ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X,
        ∀ m : ℕ, 0 < m → Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg z w m)) := by
  refine ⟨fun _ _ m => ∑' q : ℕ, cCoefPrime pole pole q m, ?_⟩
  intro z hz w hw m hm
  rw [partial_eq_pole_of_modulus_one z w (modulus_one_of_mem hP hz) (modulus_one_of_mem hP hw)]
  have hs := (pole_coeff_summable_norm m hm).of_norm
  have hs' : Summable (fun q : ℕ =>
      if Nat.lcm pole.r pole.r ∣ q then cCoefPrime pole pole q m else 0) := by
    simpa only [show pole.r = 1 from rfl, Nat.lcm_self, Nat.one_dvd, ite_true] using hs
  simpa only [show pole.r = 1 from rfl, Nat.lcm_self, Nat.one_dvd, ite_true] using
    singPartialPrime_tendsto_of_summable pole pole m hs'

/-- At level at most one the positive even frequency series has the classical value. -/
theorem level_one_series_value {H X P : ℝ} (hP : P ≤ 1) {z w : ExcPair}
    (hz : z ∈ excSet H (Real.sqrt X) P X) (hw : w ∈ excSet H (Real.sqrt X) P X)
    {m : ℕ} (hm : 0 < m) (he : Even m) {s : ℂ}
    (hs : Tendsto (singPartialPrime z w m) atTop (𝓝 s)) : s = (Sing m : ℂ) := by
  rw [partial_eq_pole_of_modulus_one z w (modulus_one_of_mem hP hz) (modulus_one_of_mem hP hw)] at hs
  exact tendsto_nhds_unique hs (pole_partial_tendsto m hm he)

/-- Changing only the pole pair value at zero scales the exact pole kernel. -/
theorem mainTerm_zero_supported (H P X ε : ℝ) (t : ℂ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) :
    mainTermPrime (excSet H (Real.sqrt X) P X)
      (fun z w m => if m = 0 then (if z = pole ∧ w = pole then t else 0) else Sg z w m)
      ε X 0 = t * WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true := by
  unfold mainTermPrime
  simp only [ite_true]
  simp_rw [finsum_eq_if]
  rw [finsum_eq_single _ pole (by intro z hz; simp [hz])]
  simp only [pole_mem_excSet, ite_true]
  rw [finsum_eq_single _ pole (by intro w hw; simp [hw])]
  simp [pole_mem_excSet, mult_pole, Asign_pole, show pole.ρ = 1 from rfl]

/-- Positive convergence alone cannot bound the zero frequency error uniformly in supplied values. -/
theorem zero_frequency_no_uniform_bound (H X P ε : ℝ) (hP : P ≤ 1)
    (hK : WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true ≠ 0) :
    ¬ (∃ B : ℝ, ∀ Sg : ExcPair → ExcPair → ℕ → ℂ,
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X,
        ∀ m : ℕ, 0 < m → Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg z w m))) →
      ‖R1majPrime ε X P 0 - mainTermPrime (excSet H (Real.sqrt X) P X) Sg ε X 0‖ ≤ B) := by
  rintro ⟨B, hB⟩
  obtain ⟨Sg, hSg⟩ := level_one_series_converges H X P hP
  let A : ℂ := R1majPrime ε X P 0
  let K : ℂ := WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true
  let t : ℂ := (A - ((|B| + 1 : ℝ) : ℂ)) / K
  let Sg' := fun z w m => if m = 0 then (if z = pole ∧ w = pole then t else 0) else Sg z w m
  have hc : ∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X,
      ∀ m : ℕ, 0 < m → Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m)) := by
    intro z hz w hw m hm
    simpa only [Sg', Nat.ne_of_gt hm, ite_false] using hSg z hz w hw m hm
  have hb := hB Sg' hc
  change ‖A - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X 0‖ ≤ B at hb
  rw [show mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X 0 = t * K from
    mainTerm_zero_supported H P X ε t Sg] at hb
  have ht : t * K = A - ((|B| + 1 : ℝ) : ℂ) := div_mul_cancel₀ _ hK
  rw [ht, sub_sub_cancel] at hb
  have hn : ‖((|B| + 1 : ℝ) : ℂ)‖ = |B| + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hn] at hb
  linarith [le_abs_self B]

/-- The zero frequency kernel is nonzero at a concrete small positive epsilon. -/
theorem zero_kernel_nonzero_instance :
    WeightedKernelsTask08.weightedKernel (X1 (1 / 9) 4) 4 1 1 0 true ≠ 0 := by
  rw [WeightedKernelsTask08.weightedKernel_poles]
  apply Nat.cast_ne_zero.mpr
  apply Finset.card_ne_zero.mpr
  refine ⟨(4, 4), ?_⟩
  have hcut : X1 (1 / 9) 4 < 4 := by
    unfold X1
    calc
      _ < (4 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 4 := Real.rpow_one _
  norm_num [WeightedKernelsTask08.kernelPairs, hcut]

/-- At sufficiently large scale the zero frequency pole kernel is nonzero. -/
theorem zero_kernel_ne_zero_of_large_scale {ε X : ℝ} (hX : 4 ≤ X)
    (hp : 2 ≤ X ^ ε) :
    WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true ≠ 0 := by
  have hX0 : 0 < X := by linarith
  have hcut : X1 ε X ≤ X / 2 := by
    rw [X1, Real.rpow_sub hX0, Real.rpow_one]
    exact div_le_div_of_nonneg_left hX0.le (by norm_num) hp
  have hfloor : X / 2 < (⌊X⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one X
    linarith
  have hk : X1 ε X < (⌊X⌋₊ : ℝ) := hcut.trans_lt hfloor
  have hk1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by norm_num; linarith)
  rw [WeightedKernelsTask08.weightedKernel_poles]
  apply Nat.cast_ne_zero.mpr
  apply Finset.card_ne_zero.mpr
  refine ⟨(⌊X⌋₊, ⌊X⌋₊), ?_⟩
  simp [WeightedKernelsTask08.kernelPairs, hk, hk1]

/-- Every allowed positive epsilon admits arbitrarily thresholded level one parameters with nonzero zero kernel. -/
theorem level_one_large_hyp {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 4 / 9)
    (H0 X0 : ℝ) :
    ∃ H X : ℝ, Thm1Hyp ε H0 X0 H X 1 ∧ 4 ≤ X ∧
      (1 : ℝ) * X ^ (-ε) ≤ 1 ∧
      WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 0 true ≠ 0 := by
  let H := max H0 0
  let T := max (2 * H) (max (Real.log (max X0 4)) (Real.log 2 / ε))
  let X := Real.exp T
  have hT_H : 2 * H ≤ T := le_max_left _ _
  have hT_X : Real.log (max X0 4) ≤ T :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hT_ε : Real.log 2 / ε ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hlarge : max X0 4 ≤ X := by
    calc
      _ = Real.exp (Real.log (max X0 4)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hT_X
  have hX4 : 4 ≤ X := (le_max_right _ _).trans hlarge
  have hX1 : 1 ≤ X := by linarith
  have hpow : 2 ≤ X ^ ε := by
    have ht : Real.log 2 ≤ T * ε := (div_le_iff₀ hε).mp hT_ε
    have he := Real.exp_le_exp.mpr ht
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_mul, X] using he
  refine ⟨H, X, ?_, hX4, ?_, zero_kernel_ne_zero_of_large_scale hX4 hpow⟩
  · refine ⟨le_max_left _ _, ?_, (le_max_left _ _).trans hlarge, le_refl _, ?_⟩
    · change H ≤ Real.log (Real.exp T) / 2
      rw [Real.log_exp]
      linarith
    · exact Real.one_le_rpow hX1 (by linarith)
  · simpa only [one_mul] using
      Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith : -ε ≤ 0)

/-- The exact repaired task579 main bound is false because its supplied value at zero is unrestricted. -/
theorem main_term_leaf579_false : ¬ (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 P : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ,
      Thm1Hyp ε H0 X0 H X P0 →
      P0 * X ^ (-ε) ≤ P → P ≤ P0 →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ, 0 < m →
        Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) →
      ∀ m : ℕ, (m : ℝ) ≤ X →
        ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
          C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0))) := by

  rintro ⟨ε0, hε0, h⟩
  let ε := min (ε0 / 2) (1 / 9)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε0' : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε < 4 / 9 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨c, H0, C, X0, _, hbound⟩ := h ε hε hε0'
  obtain ⟨H, X, hHyp, hX4, hlow, hK⟩ := level_one_large_hyp hε hε4 H0 X0
  apply zero_frequency_no_uniform_bound H X 1 ε (by norm_num) hK
  refine ⟨C * (Sing 0 * X * Real.exp (-(c * H)) + X ^ (1 - ε0)), ?_⟩
  intro Sg hconv
  exact hbound H X 1 1 Sg hHyp hlow (le_refl _) hconv 0 (by
    simp only [Nat.cast_zero]
    linarith)

/-- At level below one the exact exceptional set consists only of the pole. -/
theorem excSet_eq_pole_of_level_lt_one (H U P X : ℝ) (hP : P < 1) :
    excSet H U P X = {pole} := by
  ext z
  constructor
  · intro hz
    rcases hz with hz | hz
    · exact hz
    · have hr : (1 : ℝ) ≤ z.r := by
        exact_mod_cast Nat.pos_of_ne_zero z.hr.out
      linarith [hz.1]
  · intro hz
    exact hz ▸ pole_mem_excSet H U P X

/-- A singleton pole main term is the supplied value times the exact pole kernel. -/
theorem mainTerm_singleton_pole (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X : ℝ) (m : ℕ) :
    mainTermPrime {pole} Sg ε X m =
      Sg pole pole m * WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 m true := by
  have h := Truncation168.mainTermPrime_eq_sum ({pole} : Finset ExcPair) Sg ε X m
  simpa [Truncation168.pairTerm, mult_pole, Asign_pole, show pole.ρ = 1 from rfl] using h

/-- At level zero the repaired lcm cutoff removes the pole at every U. -/
theorem truncated_level_zero (H X U ε : ℝ) (m : ℕ)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) :
    mainTermTruncatedPrime (excSet H (Real.sqrt X) 0 X) Sg ε X 0 U m = 0 := by
  rw [excSet_eq_pole_of_level_lt_one H (Real.sqrt X) 0 X (by norm_num)]
  have he : ({pole} : Set ExcPair) = (({pole} : Finset ExcPair) : Set ExcPair) := by simp
  rw [he, truncatedPrime_eq_finite]
  have hp : Truncation168.retainedPairs ({pole} : Finset ExcPair) 0 U m = ∅ := by
    ext ⟨z, w⟩
    simp only [Truncation168.mem_retainedPairs, mem_singleton, Finset.notMem_empty]
    constructor
    · rintro ⟨rfl, rfl, _, _, hl, _⟩
      norm_num [pole] at hl
    · intro h
      exact h.elim
  rw [Truncation168.truncatedPrime, hp, sum_empty]

/-- At level zero a nonzero positive even pole term cannot satisfy the proposed decaying tail bound. -/
theorem level_zero_tail_bound_impossible (H X ε C : ℝ) (m : ℕ) (hm : 0 < m) (he : Even m)
    (hK : WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 m true ≠ 0) :
    ¬ (∀ U : ℝ, 2 ≤ U → ∀ Sg : ExcPair → ExcPair → ℕ → ℂ,
      (∀ z ∈ excSet H (Real.sqrt X) 0 X, ∀ w ∈ excSet H (Real.sqrt X) 0 X,
        ∀ n : ℕ, 0 < n → Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg z w n))) →
      ‖mainTermPrime (excSet H (Real.sqrt X) 0 X) Sg ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) 0 X) Sg ε X 0 U m‖ ≤
        C * (Sing m * X * Real.log U / Real.sqrt U)) := by
  intro h
  obtain ⟨Sg, hSg⟩ := level_one_series_converges H X 0 (by norm_num)
  have hval : Sg pole pole m = (Sing m : ℂ) :=
    level_one_series_value (H := H) (X := X) (by norm_num : (0 : ℝ) ≤ 1)
      (pole_mem_excSet _ _ _ _) (pole_mem_excSet _ _ _ _) hm he
      (hSg pole (pole_mem_excSet _ _ _ _) pole (pole_mem_excSet _ _ _ _) m hm)
  let K := WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 m true
  have hpos : 0 < ‖(Sing m : ℂ) * K‖ := by
    apply norm_pos_iff.mpr
    exact mul_ne_zero (by exact_mod_cast (Applications.Sing_pos m).ne') hK
  have hlim : Tendsto (fun U : ℝ => C * (Sing m * X * Real.log U / Real.sqrt U)) atTop (𝓝 0) := by
    have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    convert hlog.const_mul (C * (Sing m * X)) using 1
    · funext U
      rw [Real.sqrt_eq_rpow]
      ring
    · simp
  have hle : ‖(Sing m : ℂ) * K‖ ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with U hU
    have hb := h U hU Sg hSg
    rw [truncated_level_zero, sub_zero,
      excSet_eq_pole_of_level_lt_one H (Real.sqrt X) 0 X (by norm_num),
      mainTerm_singleton_pole, hval] at hb
    exact hb
  linarith

/-- Large scale admits a positive even frequency in the paper interval with nonzero pole kernel. -/
theorem positive_even_kernel_in_range {ε X : ℝ} (hX : 16 ≤ X) (hp : 4 ≤ X ^ ε) :
    ∃ m : ℕ, 0 < m ∧ Even m ∧ X / 4 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X / 2 ∧
      WeightedKernelsTask08.weightedKernel (X1 ε X) X 1 1 m true ≠ 0 := by
  let j := ⌊X / 4⌋₊
  let k := ⌊X⌋₊
  let m := 2 * j
  have hjlow : X / 4 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjhigh : (j : ℝ) ≤ X / 4 := Nat.floor_le (by linarith)
  have hk : X < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmhigh : (m : ℝ) ≤ X / 2 := by dsimp [m]; push_cast; linarith
  have hmlow : X / 4 ≤ (m : ℝ) := by dsimp [m]; push_cast; linarith
  have hmpos : 0 < m := by
    have hr : (0 : ℝ) < m := by linarith
    exact_mod_cast hr
  have hmk : m ≤ k := by
    have hr : (m : ℝ) ≤ k := by linarith
    exact_mod_cast hr
  have hcut : X1 ε X ≤ X / 4 := by
    rw [X1, Real.rpow_sub (by linarith : 0 < X), Real.rpow_one]
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) hp
  have hcutk : X1 ε X < (k : ℝ) := by linarith
  have hcutl : X1 ε X < ((k - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmk]
    linarith
  have hk1 : 1 ≤ k := by
    apply Nat.le_floor
    norm_num
    linarith
  have hl1 : 1 ≤ k - m := by
    have hr : (1 : ℝ) ≤ ((k - m : ℕ) : ℝ) := by
      rw [Nat.cast_sub hmk]
      linarith
    exact_mod_cast hr
  refine ⟨m, hmpos, ⟨j, by dsimp [m]; omega⟩, hmlow, hmhigh, ?_⟩
  rw [WeightedKernelsTask08.weightedKernel_poles]
  apply Nat.cast_ne_zero.mpr
  apply Finset.card_ne_zero.mpr
  refine ⟨(k, k - m), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, le_refl _⟩,
      Finset.mem_Icc.mpr ⟨hl1, Nat.sub_le _ _⟩⟩
  · simp only [ite_true]
    refine ⟨hcutk, hcutl, ?_⟩
    omega

/-- The paper parameter range has arbitrarily thresholded scales suitable for the tail audit. -/
theorem level_one_tail_hyp {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 4 / 9)
    (H0 X0 : ℝ) :
    ∃ H X : ℝ, Thm1Hyp ε H0 X0 H X 1 ∧ 16 ≤ X ∧ 4 ≤ X ^ ε := by
  let H := max H0 0
  let T := max (2 * H) (max (Real.log (max X0 16)) (Real.log 4 / ε))
  let X := Real.exp T
  have hT_H : 2 * H ≤ T := le_max_left _ _
  have hT_X : Real.log (max X0 16) ≤ T :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hT_ε : Real.log 4 / ε ≤ T :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hlarge : max X0 16 ≤ X := by
    calc
      _ = Real.exp (Real.log (max X0 16)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hT_X
  have hX4 : 16 ≤ X := (le_max_right _ _).trans hlarge
  have hX1 : 1 ≤ X := by linarith
  have hpow : 4 ≤ X ^ ε := by
    have ht : Real.log 4 ≤ T * ε := (div_le_iff₀ hε).mp hT_ε
    have he := Real.exp_le_exp.mpr ht
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_mul, X] using he
  refine ⟨H, X, ?_, hX4, hpow⟩
  · refine ⟨le_max_left _ _, ?_, (le_max_left _ _).trans hlarge, le_refl _, ?_⟩
    · change H ≤ Real.log (Real.exp T) / 2
      rw [Real.log_exp]
      linarith
    · exact Real.one_le_rpow hX1 (by linarith)

/-- The literal repaired task281 tail leaf is false because it permits P zero. -/
theorem truncation_leaf281_false : ¬ (∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ H0 C' X0 : ℝ, 0 < C' ∧ ∀ H X P0 P U : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
      Thm1Hyp ε H0 X0 H X P0 → P ≤ P0 →
      (excSet H (Real.sqrt X) P X).Finite →
      (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ n : ℕ, 0 < n →
        Tendsto (singPartialPrime z w n) atTop (𝓝 (Sg' z w n))) →
      X / 4 ≤ m → (m : ℝ) ≤ X / 2 → 2 ≤ U →
      ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
        mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X P U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U)) := by

  rintro ⟨ε0, hε0, h⟩
  let ε := min (ε0 / 2) (1 / 9)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε0' : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε4 : ε < 4 / 9 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨H0, C, X0, _, hbound⟩ := h ε hε hε0'
  obtain ⟨H, X, hHyp, hX16, hpow⟩ := level_one_tail_hyp hε hε4 H0 X0
  obtain ⟨m, hm, he, hmlow, hmhigh, hK⟩ := positive_even_kernel_in_range hX16 hpow
  apply level_zero_tail_bound_impossible H X ε C m hm he hK
  intro U hU Sg hconv
  exact hbound H X 1 0 U Sg m hHyp (by norm_num)
    (excSet_finite H (Real.sqrt X) 0 X) hconv hmlow hmhigh hU

end
end LeanLab.Pintz2021.DecompJ665

#print axioms LeanLab.Pintz2021.DecompJ665.leaf_constants_exist
#print axioms LeanLab.Pintz2021.DecompJ665.leaf_main_term_bound_exists_C
#print axioms LeanLab.Pintz2021.DecompJ665.singular_series_leaf_false
#print axioms LeanLab.Pintz2021.DecompJ665.negative_epsilon_hyp
#print axioms LeanLab.Pintz2021.DecompJ665.negative_epsilon_no_P
#print axioms LeanLab.Pintz2021.DecompJ665.P_leaf_false

#print axioms LeanLab.Pintz2021.DecompJ665.compact_Lzeros_finite

#print axioms LeanLab.Pintz2021.DecompJ665.bounded_Lzeros_finite

#print axioms LeanLab.Pintz2021.DecompJ665.excSet_finite

#print axioms LeanLab.Pintz2021.DecompJ665.P_exists_of_nonneg

#print axioms LeanLab.Pintz2021.DecompJ665.pole_coefficient_eq_template

#print axioms LeanLab.Pintz2021.DecompJ665.pole_coeff_summable_norm

#print axioms LeanLab.Pintz2021.DecompJ665.pole_hasSum

#print axioms LeanLab.Pintz2021.DecompJ665.pole_partial_tendsto

#print axioms LeanLab.Pintz2021.DecompJ665.truncatedPrime_eq_finite

#print axioms LeanLab.Pintz2021.DecompJ665.excSet_re_le_one

#print axioms LeanLab.Pintz2021.DecompJ665.actual_truncation_error_le_mass

#print axioms LeanLab.Pintz2021.DecompJ665.singPartialPrime_tendsto_of_summable

#print axioms LeanLab.Pintz2021.DecompJ665.pole_partial_exists

#print axioms LeanLab.Pintz2021.DecompJ665.lift_apply_nat

#print axioms LeanLab.Pintz2021.DecompJ665.tau_lift_inv

#print axioms LeanLab.Pintz2021.DecompJ665.cRam_lifts

#print axioms LeanLab.Pintz2021.DecompJ665.exact_coefficient_eq_template

#print axioms LeanLab.Pintz2021.DecompJ665.series_exists_of_template_summable

#print axioms LeanLab.Pintz2021.DecompJ665.modulus_one_of_mem

#print axioms LeanLab.Pintz2021.DecompJ665.lift_eq_pole_of_modulus_one

#print axioms LeanLab.Pintz2021.DecompJ665.partial_eq_pole_of_modulus_one

#print axioms LeanLab.Pintz2021.DecompJ665.level_one_series_converges

#print axioms LeanLab.Pintz2021.DecompJ665.level_one_series_value

#print axioms LeanLab.Pintz2021.DecompJ665.mainTerm_zero_supported

#print axioms LeanLab.Pintz2021.DecompJ665.zero_frequency_no_uniform_bound

#print axioms LeanLab.Pintz2021.DecompJ665.zero_kernel_nonzero_instance

#print axioms LeanLab.Pintz2021.DecompJ665.zero_kernel_ne_zero_of_large_scale

#print axioms LeanLab.Pintz2021.DecompJ665.level_one_large_hyp

#print axioms LeanLab.Pintz2021.DecompJ665.main_term_leaf579_false

#print axioms LeanLab.Pintz2021.DecompJ665.excSet_eq_pole_of_level_lt_one

#print axioms LeanLab.Pintz2021.DecompJ665.mainTerm_singleton_pole

#print axioms LeanLab.Pintz2021.DecompJ665.truncated_level_zero

#print axioms LeanLab.Pintz2021.DecompJ665.level_zero_tail_bound_impossible

#print axioms LeanLab.Pintz2021.DecompJ665.positive_even_kernel_in_range

#print axioms LeanLab.Pintz2021.DecompJ665.level_one_tail_hyp

#print axioms LeanLab.Pintz2021.DecompJ665.truncation_leaf281_false
