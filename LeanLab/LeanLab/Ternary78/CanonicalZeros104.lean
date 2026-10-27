import Mathlib

/-
AI wrote this Lean code. Binary Goldbach is open.
The zero set is the analytic L-function zero set, with its actual locations.
Source for the count convention is Bennett et al., arXiv 2005.02989, page 1.
These elementary finiteness facts do not prove the cited Bennett estimate.
-/

namespace LeanLab.Ternary78.Bennett
open Filter

/-- Finite nontrivial L-function zeros through a bounded height.
The nonprincipal hypothesis makes the L-function entire.
Source: the zero count definition on page 1 of arXiv 2005.02989. -/
theorem lfunction_strip_zeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ DirichletCharacter.LFunction χ z = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
  have hn : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  have hc := ha.preimage_zero_mem_codiscrete hn
  have hz : IsClosed (DirichletCharacter.LFunction χ ⁻¹' ({0} : Set ℂ)) ∧
      IsDiscrete (DirichletCharacter.LFunction χ ⁻¹' ({0} : Set ℂ)) := by
    simpa using (mem_codiscrete'.mp hc)
  have hfin := ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_right hz.1).finite
    (hz.2.mono Set.inter_subset_right)
  apply hfin.subset
  intro z ⟨hr0, hr1, hi, hzero⟩
  refine ⟨?_, hzero⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + |T| := by rw [abs_of_pos hr0]; linarith [le_abs_self T]

#print axioms lfunction_strip_zeros_finite

/-- Zero occurrence indices for the multiset Z of Bennett page 1, equation 1.2.
A zero of order r has occurrence indices 0 through r minus one.
No height cutoff is imposed here. -/
noncomputable def zeroOccurrences {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :=
  {w : ℂ × ℕ // 0 < w.1.re ∧ w.1.re < 1 ∧
    DirichletCharacter.LFunction χ w.1 = 0 ∧
      w.2 < analyticOrderNatAt (DirichletCharacter.LFunction χ) w.1}
/-- Every bounded height sublevel of the actual zero occurrence type is finite.
Source: Bennett pages 1 and 2, multiset and height count convention. -/
theorem zeroOccurrences_bounded_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    Finite {w : zeroOccurrences χ // |w.val.1.im| ≤ T} := by
  classical
  let S := {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T ∧ DirichletCharacter.LFunction χ z = 0}
  have hs : S.Finite := lfunction_strip_zeros_finite χ hχ T
  have : Finite S := hs.to_subtype
  let incl (w : {w : zeroOccurrences χ // |w.val.1.im| ≤ T}) :
      Σ z : S, Fin (analyticOrderNatAt (DirichletCharacter.LFunction χ) z) :=
    ⟨⟨w.val.val.1, w.val.property.1, w.val.property.2.1, w.property, w.val.property.2.2.1⟩,
      ⟨w.val.val.2, w.val.property.2.2.2⟩⟩
  apply Finite.of_injective incl
  intro w v h
  apply Subtype.ext
  apply Subtype.ext
  have hz := congrArg (fun w => w.1.val) h
  have hn := congrArg (fun w => w.2.val) h
  exact Prod.ext hz hn

#print axioms zeroOccurrences_bounded_finite

/-- No zero of a nonprincipal Dirichlet L-function has infinite analytic order.
Thus analyticOrderNatAt retains the actual finite multiplicity. -/
theorem lfunction_order_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ ⊤ := by
  have ha : ∀ z, AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    fun z => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  intro horder
  have h := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z ha).mp horder
  have hn := χ.LFunction_ne_zero_of_one_le_re (s := (2 : ℂ)) (Or.inl hχ) (by norm_num)
  exact hn (congrFun h 2)

#print axioms lfunction_order_ne_top

/-- Primitive characters of conductor greater than one are nonprincipal.
This discharges the entire L-function hypothesis for the Bennett domain. -/
theorem primitive_ne_one {q : ℕ} [NeZero q] (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    χ ≠ 1 := by
  intro heq
  rw [heq] at hχ
  have hc : (1 : ℕ) = q := by
    simpa only [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] using hχ
  omega

#print axioms primitive_ne_one

/-- Natural multiplicity is positive exactly at actual zeros of a nonprincipal L-function.
This checks the multiplicity convention in Bennett page 1 equation 1.2. -/
theorem lfunction_order_pos_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    0 < analyticOrderNatAt (DirichletCharacter.LFunction χ) z ↔
      DirichletCharacter.LFunction χ z = 0 := by
  constructor
  · intro hp
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.ne_of_gt hp)
  · intro hz
    have ha := (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
    have ho : analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ 0 :=
      ha.analyticOrderAt_ne_zero.mpr hz
    have hc := Nat.cast_analyticOrderNatAt (lfunction_order_ne_top χ hχ z)
    by_contra hn
    have hn0 : analyticOrderNatAt (DirichletCharacter.LFunction χ) z = 0 := by omega
    rw [hn0] at hc
    exact ho hc.symm

#print axioms lfunction_order_pos_iff

/-- Concrete nonvacuity for every primitive and nonprincipal character hypothesis
used by the canonical count and gamma results. -/
theorem primitive_mod_three_exists : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 ∧ χ.IsPrimitive := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (a := (2 : ZMod 3)) (by decide)
  have hn : χ ≠ 1 := by
    intro heq
    rw [heq] at hχ
    have hu : IsUnit (2 : ZMod 3) := by decide
    exact hχ (MulChar.one_apply hu)
  refine ⟨χ, hn, ?_⟩
  have hd := χ.conductor_dvd_level
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with hc | hc
  · exact (hn (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc)).elim
  · exact hc

#print axioms primitive_mod_three_exists

end LeanLab.Ternary78.Bennett
