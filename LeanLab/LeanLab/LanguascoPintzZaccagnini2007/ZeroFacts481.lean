import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a
import LeanLab.PNTPort.DirichletZF.U1482Jensen

/-!
Finiteness of the actual exceptional zero box of P0045 displays 8 and Lemma 4.1.
These are qualitative analytic facts and contain no zero density assertion.
The pole is excluded by the strict upper real part in zeroBox481.
The approach follows task373, with Mathlib's identity principle used directly on a compact set.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Complex Real Set Metric
open LeanLab.PNTPort.DirichletZF.U1482

/-- P0045 pages 4 and 5, the finite zero family of display 8.
A nonzero entire function has finitely many zeros in a compact set. -/
theorem compact_zeros_finite481 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h2 : f 2 ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ f z = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨x, _, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK (fun _ hz => hz.1)
  have hfeq : EqOn f 0 Set.univ := by
    refine AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
      (fun z _ => hf.analyticAt z) isPreconnected_univ (Set.mem_univ x) ?_
    simp only [mem_closure_iff_clusterPt, ← accPt_principal_iff_clusterPt]
    exact hacc.mono (Filter.principal_mono.mpr fun _ hz => hz.2)
  exact h2 (hfeq (Set.mem_univ 2))

/-- P0045 pages 4 and 5, display 8: the compact rectangle version for an entire function. -/
theorem rectangle_zeros_finite481 (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h2 : f 2 ≠ 0) (a T : ℝ) :
    {z : ℂ | f z = 0 ∧ a ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}.Finite := by
  let C : ℝ := |a| + |T| + 2
  refine (compact_zeros_finite481 f hf h2 (isCompact_closedBall 0 C)).subset ?_
  intro z hz
  refine ⟨?_, hz.1⟩
  rw [mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ |a| + 1 := abs_le.mpr
    ⟨by linarith [neg_abs_le a, hz.2.1], by linarith [abs_nonneg a, hz.2.2.1]⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|a| + 1) + |T| := add_le_add hre (hz.2.2.2.trans (le_abs_self T))
    _ ≤ C := by dsimp [C]; linarith

/-- P0045 display 8: a primitive character has finitely many zeros in the bounded box.
The primitive principal character has modulus one. Its pole is removed using gZ. -/
theorem primitive_zeros_finite481 {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (a T : ℝ) :
    {ρ : ℂ | Lfun481 χ ρ = 0 ∧ a ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}.Finite := by
  have hr0 : r ≠ 0 := by omega
  haveI : NeZero r := ⟨hr0⟩
  by_cases hχ : χ = 1
  · have hr1 : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hdiff : Differentiable ℂ gZ := fun z => (gZ_analyticAt z).differentiableAt
    have h2 : gZ 2 ≠ 0 := by
      rw [gZ_of_ne (by norm_num)]
      exact mul_ne_zero (by norm_num)
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))
    refine (rectangle_zeros_finite481 gZ hdiff h2 a T).subset ?_
    intro ρ hz
    have hzζ : riemannZeta ρ = 0 := by
      simpa [Lfun481, hχ, DirichletCharacter.LFunction_modOne_eq] using hz.1
    have hne : ρ ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    refine ⟨?_, hz.2.1, hz.2.2.1.le, hz.2.2.2⟩
    rw [gZ_of_ne hne, hzζ, mul_zero]
  · have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    refine (rectangle_zeros_finite481 _ (DirichletCharacter.differentiable_LFunction hχ)
      h2 a T).subset ?_
    intro ρ hz
    exact ⟨by simpa [Lfun481, hr0] using hz.1, hz.2.1, hz.2.2.1.le, hz.2.2.2⟩

/-- P0045 pages 4 and 5, display 8: the entire exceptional zero box is finite.
This statement does not bound its cardinality or its analytic multiplicity sum. -/
theorem zeroBox_finite481 (X : ℕ) (H T P : ℝ) : (zeroBox481 X H T P).Finite := by
  classical
  let F (r : ℕ) : Set (DirichletCharacter ℂ r × ℂ) :=
    {w | w.1.IsPrimitive ∧ Lfun481 w.1 w.2 = 0 ∧
      1 - H / Real.log X ≤ w.2.re ∧ w.2.re < 1 ∧ |w.2.im| ≤ T}
  have hF : ∀ r ∈ Set.Icc 1 ⌊P⌋₊, (F r).Finite := by
    intro r hr
    have hfinite := (Set.toFinite {χ : DirichletCharacter ℂ r | χ.IsPrimitive}).biUnion
      (fun χ hχ => (primitive_zeros_finite481 hr.1 χ hχ (1 - H / Real.log X) T).image
        (fun ρ : ℂ => (χ, ρ)))
    refine hfinite.subset ?_
    intro w hw
    exact Set.mem_iUnion.2 ⟨w.1, Set.mem_iUnion.2 ⟨hw.1, w.2, hw.2, rfl⟩⟩
  refine ((Set.finite_Icc 1 ⌊P⌋₊).sigma hF).subset ?_
  intro z hz
  exact ⟨⟨hz.1, Nat.le_floor hz.2.1⟩, hz.2.2.1, hz.2.2.2⟩

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.compact_zeros_finite481
#print axioms LeanLab.LPZ2007.rectangle_zeros_finite481
#print axioms LeanLab.LPZ2007.primitive_zeros_finite481
#print axioms LeanLab.LPZ2007.zeroBox_finite481
