/-
A split of `primitive_psi_zero_expansion508` into three leaves plus an assembly.

The statement is a sharp explicit formula with zeros: for a primitive character of modulus
`q ≤ √X` there is a height `T` between `X` and `2X` and the finite list `Z` of the zeros with
`|Im ρ| ≤ T`, such that the twisted von Mangoldt sum up to `n` differs from the main term
minus the zero sum by a uniform `O((log X)²)`.

The three leaves are (1) the height and the zero list: up to any height at least `X` the zeros
in the open strip form a finite set, so a finset characterised exactly by the zero condition
exists; (2) the error estimate away from the trivial character, where the main term vanishes;
(3) the same estimate for the trivial character, where the main term is `n` itself. Leaves (2)
and (3) take `T` and `Z` as given, so neither of them has to produce the height or the list;
the assembly takes them from leaf (1) and splits on whether the character is trivial, keeping
the larger of the two constants.

AI wrote the Lean code. Binary Goldbach is open. The three leaves are open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp508a

namespace LeanLab.BhowmikGrimmelt2026

open Set Filter

open scoped Topology

/-- The `L`-function of a Dirichlet character is nonzero at `2`. -/
private lemma LFunction_two_ne_zero508 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)

/-- `{1}ᶜ` is preconnected in `ℂ`. -/
private lemma isPreconnected_compl_one508 : IsPreconnected ({1}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
    (1 : ℂ)).isPreconnected

/-- The `L`-function of `χ` is analytic on a neighbourhood of each point `≠ 1`. -/
private lemma analyticOnNhd_LFunction_compl_one508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := fun _s hs =>
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun t ht =>
      (DirichletCharacter.differentiableAt_LFunction χ t (Or.inl ht)).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- A zero of the `L`-function away from `1` is isolated. -/
private lemma LFunction_zero_isolated508 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz1 : z ≠ 1) (hz : DirichletCharacter.LFunction χ z = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, w ≠ z → ‖w - z‖ < r →
      DirichletCharacter.LFunction χ w ≠ 0 := by
  classical
  set f : ℂ → ℂ := DirichletCharacter.LFunction χ with hf
  have hnot : ¬ ∀ᶠ w in 𝓝 z, f w = 0 := by
    intro h
    have hEq : EqOn f 0 ({1}ᶜ : Set ℂ) :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (analyticOnNhd_LFunction_compl_one508 χ) isPreconnected_compl_one508
        (by simpa using hz1) h
    have h2 : f 2 = 0 := hEq (by simp)
    exact LFunction_two_ne_zero508 χ h2
  have hzmem : z ∈ ({1}ᶜ : Set ℂ) := by simpa using hz1
  have hzan : AnalyticAt ℂ f z := analyticOnNhd_LFunction_compl_one508 χ z hzmem
  have h2 : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 :=
    (hzan.eventually_eq_zero_or_eventually_ne_zero).resolve_left hnot
  rw [eventually_nhdsWithin_iff] at h2
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp h2
  refine ⟨ε, hε, fun w hw hd => ?_⟩
  exact hsub (by simpa [Metric.mem_ball, dist_eq_norm] using hd) hw

set_option maxHeartbeats 800000 in
/-- There are no zeros of `L(s, χ)` in a punctured neighbourhood of `1`. -/
private lemma LFunction_eventually_ne_zero_near_one508 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, w ≠ 1 → ‖w - 1‖ < ε →
      DirichletCharacter.LFunction χ w ≠ 0 := by
  classical
  by_cases hχ : χ = 1
  · have hres := DirichletCharacter.LFunctionTrivChar_residue_one (N := q)
    set v : ℂ := ∏ p ∈ q.primeFactors, (1 - (p : ℂ)⁻¹) with hv
    have hvne : v ≠ 0 := by
      rw [hv]
      refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
      have hp1 : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have hpp : (0 : ℝ) < (p : ℝ) := by linarith
      have hlt : ‖((p : ℂ))⁻¹‖ < 1 := by
        rw [norm_inv, RCLike.norm_natCast, ← one_div, div_lt_one hpp]
        exact hp1
      intro hh
      have h1 : ((p : ℂ))⁻¹ = 1 := (sub_eq_zero.mp hh).symm
      rw [h1, norm_one] at hlt
      exact lt_irrefl _ hlt
    have hnorm : Tendsto
        (fun s : ℂ => ‖(s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖)
        (𝓝[≠] 1) (𝓝 ‖v‖) := by
      have := hres.norm
      rw [hv]
      exact this
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ),
        ‖(s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s‖ > ‖v‖ / 2 :=
      hnorm (isOpen_Ioi.mem_nhds (by linarith : ‖v‖ / 2 < ‖v‖))
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hev
    refine ⟨ε, hε, fun w hw hd => ?_⟩
    rw [hχ]
    have hmem : w ∈ Metric.ball (1 : ℂ) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hd
    have hgt := hsub hmem hw
    intro hz
    rw [hz, mul_zero, norm_zero] at hgt
    linarith
  · have hcont : ContinuousAt (DirichletCharacter.LFunction χ) 1 :=
      (DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr hχ)).continuousAt
    have hne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
      DirichletCharacter.LFunction_apply_one_ne_zero hχ
    have hmem : {w : ℂ | DirichletCharacter.LFunction χ w ≠ 0} ∈ 𝓝 (1 : ℂ) :=
      hcont.eventually_ne hne
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨ε, hε, fun w _ hd => ?_⟩
    exact hsub (by simpa [Metric.mem_ball, dist_eq_norm] using hd)

set_option maxHeartbeats 1600000 in
/-- The zeros of `L(s, χ)` in the open strip with `|Im ρ| ≤ T` form a finite set. -/
private lemma zero_set_finite508 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hT : 0 ≤ T) :
    {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  classical
  let S : Set ℂ := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
    |ρ.im| ≤ T}
  let K : Set ℂ := {z : ℂ | ‖z‖ ≤ |T| + 2 ∧ 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}
  change S.Finite
  have hSsub : S ⊆ K := by
    intro z hz
    refine ⟨?_, hz.2.1.le, hz.2.2.1.le, hz.2.2.2⟩
    have hz1 : |z.re| ≤ 1 := by rw [abs_of_pos hz.2.1]; exact hz.2.2.1.le
    have hz4 : |z.im| ≤ T := hz.2.2.2
    have h := Complex.norm_le_abs_re_add_abs_im z
    have hTabs : |T| = T := abs_of_nonneg hT
    rw [hTabs]
    linarith
  have hKc : IsCompact K := by
    have h1 : IsClosed {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1} :=
      isClosed_Icc.preimage Complex.continuous_re
    have h2 : IsClosed {z : ℂ | z.im ∈ Set.Icc (-T) T} :=
      isClosed_Icc.preimage Complex.continuous_im
    have hEq : K = Metric.closedBall (0 : ℂ) (|T| + 2) ∩
        {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 1} ∩ {z : ℂ | z.im ∈ Set.Icc (-T) T} := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
        Set.mem_Icc, abs_le]
      tauto
    rw [hEq]
    exact ((isCompact_closedBall (0 : ℂ) (|T| + 2)).inter_right h1).inter_right h2
  have hiso : ∀ x : {z : ℂ // z ∈ K ∧ DirichletCharacter.LFunction χ z = 0 ∧ z ≠ 1},
      ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, w ≠ (x : ℂ) → ‖w - (x : ℂ)‖ < r →
        DirichletCharacter.LFunction χ w ≠ 0 :=
    fun x => LFunction_zero_isolated508 χ x.2.2.2 x.2.2.1
  choose r hr using hiso
  have hzerone := LFunction_eventually_ne_zero_near_one508 χ
  obtain ⟨ε, hε, hzerone'⟩ := hzerone
  have hloc : ∀ x : ↥K, ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, ‖w - (x : ℂ)‖ < ρ →
      DirichletCharacter.LFunction χ w = 0 → w = (x : ℂ) := by
    rintro ⟨x, hxK⟩
    by_cases hx1 : x = 1
    · refine ⟨ε, hε, fun w hw hw0 => ?_⟩
      show w = x
      rw [hx1]
      by_contra hne
      exact absurd hw0 (hzerone' w hne (by simpa [hx1] using hw))
    · by_cases hx0 : DirichletCharacter.LFunction χ x = 0
      · refine ⟨r ⟨x, hxK, hx0, hx1⟩, (hr ⟨x, hxK, hx0, hx1⟩).1, fun w hw hw0 => ?_⟩
        by_contra hne
        exact (hr ⟨x, hxK, hx0, hx1⟩).2 w hne hw hw0
      · have hcont : ContinuousAt (DirichletCharacter.LFunction χ) x :=
          (DirichletCharacter.differentiableAt_LFunction χ x (Or.inl hx1)).continuousAt
        have hmem : {w : ℂ | DirichletCharacter.LFunction χ w ≠ 0} ∈ 𝓝 x :=
          hcont.eventually_ne hx0
        obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hmem
        refine ⟨δ, hδ, fun w hw hw0 => ?_⟩
        exact absurd hw0 (hδsub (by simpa [Metric.mem_ball, dist_eq_norm] using hw))
  choose ρ hρpos hρ using hloc
  have hcover : K ⊆ ⋃ x : ↥K, Metric.ball (x : ℂ) (ρ x / 2) := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, Subtype.coe_mk, sub_self, norm_zero]
    have := hρpos ⟨z, hz⟩
    linarith
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun x : ↥K => Metric.ball (x : ℂ) (ρ x / 2))
    (fun _ => Metric.isOpen_ball) hcover
  have hfin : S ⊆ ↑(t.image (fun x : ↥K => (x : ℂ))) := by
    intro w hw
    have hwK : w ∈ K := hSsub hw
    have hmem := ht hwK
    rw [Set.mem_iUnion] at hmem
    obtain ⟨x, hx⟩ := hmem
    rw [Set.mem_iUnion] at hx
    obtain ⟨hxt, hxball⟩ := hx
    rw [Metric.mem_ball, dist_eq_norm] at hxball
    have hlt : ‖w - (x : ℂ)‖ < ρ x := by
      have := hρpos x
      linarith
    have hwx : w = (x : ℂ) := hρ x w hlt hw.1
    rw [hwx]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hxt, rfl⟩)
  exact (t.image (fun x : ↥K => (x : ℂ))).finite_toSet.subset hfin


/-- LEAF. Step 1, the height and the zero list: for a primitive `χ` of modulus `q` and any
`X ≥ 2` there is a height `T` between `X` and `2X` and a finset `Z` of complex numbers whose
members are exactly the zeros of the `L`-function of `χ` in the open strip with imaginary part
of absolute value at most `T`. This is the finiteness and the selection step; it produces no
estimate at all, and leaves (2) and (3) only use the characterisation it gives. -/
theorem zero_set_window508 {X q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hX : 2 ≤ X) (hprim : χ.IsPrimitive) :
    ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) := by
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by linarith
  have hTmem : (X : ℝ) ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)) := by
    refine ⟨le_rfl, ?_⟩
    linarith
  refine ⟨(X : ℝ), hTmem, ?_⟩
  have hfin := zero_set_finite508 (T := (X : ℝ)) χ hX0
  exact ⟨hfin.toFinset, fun ρ => Set.Finite.mem_toFinset hfin⟩


/-- LEAF. Step 2, the error estimate away from the trivial character: for a primitive
`χ ≠ 1`, a height `T` of the size of `X` and the zero list `Z` up to that height, the twisted
von Mangoldt sum up to `n` plus the zero sum `∑ ρ ∈ Z, mult χ ρ * n ^ ρ / ρ` has size at most
`C * (log X)²`, with `C` independent of `X`, `q`, `χ`, `T`, `Z` and `n`. The main term of the
explicit formula vanishes here, so this is the leaf (2) of the header with the trivial
character removed: it does not produce `T` or `Z`. -/
theorem nonprincipal_psi_zero_bound508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  sorry

/-- LEAF. Step 3, the error estimate for the trivial character: for `χ = 1` primitive, a
height `T` of the size of `X` and the zero list `Z` up to that height, the twisted von
Mangoldt sum up to `n` minus `n` plus the zero sum `∑ ρ ∈ Z, mult χ ρ * n ^ ρ / ρ` has size at
most `C * (log X)²`, again with a constant independent of everything but the hypothesis on the
zeros. The main term of the explicit formula is `n` here, which is the whole difference from
step 2: the leaf takes `T` and `Z` as given instead of producing them. -/
theorem principal_psi_zero_bound508 (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ = 1 →
      ∀ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∀ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) - (n : ℂ) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  sorry

/-- The sharp explicit formula with zeros, assembled from the three leaves above. Leaf 1 gives
the height `T` and the zero list `Z`; the character being trivial or not selects leaf 3 or
leaf 2 for the estimate, and the two constants are merged into their maximum. -/
theorem primitive_psi_zero_expansion508_split (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ (q : ℕ) [NeZero q],
      q ≤ Nat.sqrt X → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∃ T ∈ Set.Icc (X : ℝ) (2 * (X : ℝ)), ∃ Z : Finset ℂ,
        (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) ∧
        ∀ n : ℕ, 1 ≤ n → n ≤ X →
          ‖(∑ m ∈ Finset.range (n + 1),
              (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (n : ℂ) else 0) +
            ∑ ρ ∈ Z, (mult χ ρ : ℂ) * (n : ℂ) ^ ρ / ρ‖ ≤ C * Real.log X ^ 2 := by
  obtain ⟨C₂, hC₂, hnp⟩ := nonprincipal_psi_zero_bound508 Θ hΘ hZ
  obtain ⟨C₃, hC₃, hpr⟩ := principal_psi_zero_bound508 Θ hΘ hZ
  refine ⟨max C₂ C₃, hC₂.trans (le_max_left C₂ C₃), ?_⟩
  intro X hX q _ hqQ χ hprim
  obtain ⟨T, hT, Z, hchar⟩ := zero_set_window508 χ hX hprim
  refine ⟨T, hT, Z, hchar, ?_⟩
  intro n hn1 hnX
  have hlog : (0 : ℝ) ≤ Real.log X ^ 2 := sq_nonneg (Real.log X)
  rcases eq_or_ne χ 1 with h1 | h1
  · subst h1
    have hmain : (if (1 : DirichletCharacter ℂ q) = 1 then (n : ℂ) else 0) = (n : ℂ) := by
      simp
    rw [hmain]
    exact (hpr X hX q hqQ 1 hprim rfl T hT Z hchar n hn1 hnX).trans
      (mul_le_mul_of_nonneg_right (le_max_right C₂ C₃) hlog)
  · have hmain : (if χ = 1 then (n : ℂ) else 0) = 0 := by
      simp only [ite_eq_right h1]
    rw [hmain, sub_zero]
    exact (hnp X hX q hqQ χ hprim h1 T hT Z hchar n hn1 hnX).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₂ C₃) hlog)

end LeanLab.BhowmikGrimmelt2026
