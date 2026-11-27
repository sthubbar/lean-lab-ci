/-
KEEP GOING split of `SplitS5LuZeros.leaf_mass39_display`, CLOUD S5 burst-20261127, unit S5-01b.

P0095 W. C. Lu, Exceptional set of Goldbach number, J. Number Theory 130 (2010) 2359-2392,
p. 2368 the sum `W₀(q, T, x)` and p. 2369 display (39).

The leaf `leaf_mass39_display` of `SPLIT_s5_S5_01_luzeros` has two conjuncts: the zero set
`luZeroSet` is finite, and its total weight is bounded.  This file PROVES the first conjunct for
every height function and every `N`, so that the definition `luFamilyH` is never the fallback `∅`:
* the zeros of `L(s, χ)` in the box `0 < Re s < 1`, `|Im s| ≤ T` are finite, by the identity
  theorem; for the trivial character through `(s - 1) L(s, χ)`, which Mathlib proves entire and
  nonzero at `1`; for a nontrivial character since `L(2, χ) ≠ 0`;
* the analytic order of `L(s, χ)` is finite at every point, so each zero has finite multiplicity;
* finitely many moduli `q ≤ P` and finitely many characters of each modulus.
What remains is the analytic bound (39) for the weights, the single LEAF `leaf_mass39_sum`.

AI wrote this Lean code.  Binary Goldbach is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_01_luzeros

namespace LeanLab.ExceptionalSet.SplitS5LuZerosFinite
open LeanLab.ExceptionalSet
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010ZeroIntegral
open LeanLab.ExceptionalSet.SplitS5LuZeros

/-- An entire function not identically zero has finitely many zeros in a compact set. -/
theorem zeros_finite_of_entire {g : ℂ → ℂ} (hg : Differentiable ℂ g) {z0 : ℂ} (hz0 : g z0 ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : {z | z ∈ K ∧ g z = 0}.Finite := by
  have hA : AnalyticOnNhd ℂ g Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
  have hc : g ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ := hA.preimage_zero_mem_codiscrete hz0
  have hc' : g ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K) hc
  refine (hK.finite_sdiff_of_mem_codiscreteWithin hc').subset ?_
  rintro z ⟨hzK, hz⟩
  exact ⟨hzK, by simp [hz]⟩

/-- The zeros of `L(s, χ)` with `0 < Re s < 1` and `|Im s| ≤ T` are finitely many. -/
theorem zeros_box_finite (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}.Finite := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (1 + |T|)) := isCompact_closedBall _ _
  have hsub : ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T →
      ρ ∈ Metric.closedBall (0 : ℂ) (1 + |T|) := by
    intro ρ h0 h1 hT
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + |T| := by
        have : |ρ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        have : |ρ.im| ≤ |T| := hT.trans (le_abs_self T)
        linarith
  by_cases hχ : χ = 1
  · subst hχ
    have hg := DirichletCharacter.differentiable_LFunctionTrivChar₁ q
    refine (zeros_finite_of_entire hg (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q)
      hK).subset ?_
    rintro ρ ⟨h0, h1, hT, hz⟩
    refine ⟨hsub ρ h0 h1 hT, ?_⟩
    have hρ : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
    simp only [Function.update_of_ne hρ]
    rw [show DirichletCharacter.LFunctionTrivChar q ρ = 0 from hz, mul_zero]
  · have hg : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
      DirichletCharacter.differentiable_LFunction hχ
    have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    refine (zeros_finite_of_entire hg h2 hK).subset ?_
    rintro ρ ⟨h0, h1, hT, hz⟩
    exact ⟨hsub ρ h0 h1 hT, hz⟩

/-- The analytic order of `L(s, χ)` is finite at every point. -/
theorem order_ne_top (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
  set L := DirichletCharacter.LFunction χ with hL
  have hA : AnalyticOnNhd ℂ L {1}ᶜ := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_compl_singleton
    exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have h2 : analyticOrderAt L 2 ≠ ⊤ := by
    have h0 : analyticOrderAt L 2 = 0 := by
      refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num))
        (by norm_num)
    rw [h0]; exact ENat.zero_ne_top
  have h2U : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  by_cases ha : AnalyticAt ℂ L ρ
  swap
  · rw [analyticOrderAt_eq_zero.mpr (Or.inl ha)]; exact ENat.zero_ne_top
  by_cases hρ : ρ = 1
  · subst hρ
    have hU : AnalyticOnNhd ℂ L Set.univ := fun z _ => by
      by_cases hz : z = 1
      · subst hz; exact ha
      · exact hA z hz
    exact hU.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial h2
  · have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank
        (by simp [Complex.rank_real_complex]) 1).isPreconnected
    exact hA.analyticOrderAt_ne_top_of_isPreconnected hconn h2U hρ h2

/-- The exponents of `luZeroSet` with a fixed modulus and character are finitely many. -/
theorem fiber_finite (H : ℕ → ℝ) (N q : ℕ) (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    {x : Exponent | (⟨x.modulus, x.character⟩ : Σ q, DirichletCharacter ℂ q) = ⟨q, χ⟩ ∧
      x ∈ luZeroSet H N}.Finite := by
  have : NeZero q := ⟨by omega⟩
  have hZ := zeros_box_finite q χ (H q)
  let Z := {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ H q ∧ DirichletCharacter.LFunction χ ρ = 0}
  have hW : (⋃ ρ ∈ Z, ({ρ} : Set ℂ) ×ˢ
      (Set.Iio (analyticOrderAt (DirichletCharacter.LFunction χ) ρ).toNat)).Finite :=
    hZ.biUnion (fun ρ _ => (Set.finite_singleton ρ).prod (Set.finite_Iio _))
  refine Set.Finite.of_finite_image (f := fun x : Exponent => (x.rho, x.label)) (hW.subset ?_) ?_
  · rintro _ ⟨x, ⟨hx, hmem⟩, rfl⟩
    obtain ⟨l, q', hq', χ', hp', ρ, h1, h2⟩ := x
    simp only [Sigma.mk.inj_iff] at hx
    obtain ⟨rfl, hχ⟩ := hx
    cases hχ
    obtain ⟨_, hre0, hre1, him, hlab⟩ := hmem
    simp only at hre0 hre1 him hlab
    have hne : analyticOrderAt (DirichletCharacter.LFunction χ') ρ ≠ 0 := by
      intro h0; rw [h0] at hlab; exact absurd hlab (by simp)
    have hz : DirichletCharacter.LFunction χ' ρ = 0 := by
      by_contra hc
      exact hne (analyticOrderAt_eq_zero.mpr (Or.inr hc))
    have htop := order_ne_top q' χ' ρ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Iio]
    refine ⟨ρ, ⟨hre0, hre1, him, hz⟩, rfl, ?_⟩
    rw [← hn] at hlab ⊢
    simpa using hlab
  · rintro ⟨l, q', hq', χ', hp', ρ, h1, h2⟩ ⟨hx, _⟩ ⟨l2, q2, hq2, χ2, hp2, ρ2, h12, h22⟩ ⟨hy, _⟩ he
    simp only [Sigma.mk.inj_iff] at hx hy
    obtain ⟨rfl, hχ⟩ := hx
    obtain ⟨rfl, hχ2⟩ := hy
    cases hχ; cases hχ2
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rfl

/-- Lu's zero set is finite, for every height function and every `N`. -/
theorem luZeroSet_finite (H : ℕ → ℝ) (N : ℕ) : (luZeroSet H N).Finite := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, PP N ≤ B := exists_nat_ge _
  have hS : ((Set.Icc 1 B).sigma (fun q => (Set.univ : Set (DirichletCharacter ℂ q)))).Finite := by
    refine (Set.finite_Icc 1 B).sigma (fun q hq => ?_)
    have : NeZero q := ⟨by have := hq.1; omega⟩
    exact Set.toFinite _
  refine (hS.biUnion (fun b hb => fiber_finite H N b.1 hb.1.1 b.2)).subset ?_
  intro x hx
  simp only [Set.mem_iUnion]
  refine ⟨⟨x.modulus, x.character⟩, ?_, rfl, hx⟩
  refine ⟨⟨x.modulus_pos, ?_⟩, trivial⟩
  have h1 := hx.1
  exact_mod_cast h1.trans hB

/-- LEAF: Lu 2010, p. 2369 display (39), the weight bound `Σ_{q ≤ P} W₀(q, 4πN/(qQ), N) ≪ 1`. HARD.
Cited: Lu derives it from the zero density estimates (37), (38) of Huxley and Jutila by the
usual method; the family is the true finite zero family by `luZeroSet_finite`. -/
theorem leaf_mass39_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ x ∈ luFamilyH height39 N, weight N x.rho ≤ C := by
  sorry

/-- `leaf_mass39_display` of `SplitS5LuZeros`, statement verbatim, from `leaf_mass39_sum` and the
proved finiteness. -/
theorem leaf_mass39_display_of_leaves :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (luZeroSet (height39 N) N).Finite ∧
      ∑ x ∈ luFamilyH height39 N, weight N x.rho ≤ C := by
  obtain ⟨C, hC, N0, h⟩ := leaf_mass39_sum
  exact ⟨C, hC, N0, fun N hN => ⟨luZeroSet_finite _ N, h N hN⟩⟩

example : type_of% @LeanLab.ExceptionalSet.SplitS5LuZeros.leaf_mass39_display :=
  leaf_mass39_display_of_leaves

end LeanLab.ExceptionalSet.SplitS5LuZerosFinite

#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosFinite.zeros_finite_of_entire
#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosFinite.zeros_box_finite
#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosFinite.order_ne_top
#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosFinite.fiber_finite
#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosFinite.luZeroSet_finite
#print axioms LeanLab.ExceptionalSet.SplitS5LuZerosFinite.leaf_mass39_display_of_leaves
