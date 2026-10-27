import LeanLab.LanguascoPerelli1996.Statements

/-!
Finite zero sets used in P0071 pages 349 and 354.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Zeros108
open Complex Filter Topology

/-- Standard isolated zero fact behind the finite sums in page 354 display 11. -/
theorem finite_bounded_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {x : ℂ} (hx : f x ≠ 0) (r : ℝ) :
    {z : ℂ | ‖z‖ ≤ r ∧ f z = 0}.Finite := by
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hc := ha.preimage_zero_mem_codiscrete hx
  have hc' : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (Metric.closedBall (0 : ℂ) r) :=
    codiscreteWithin_mono (Set.subset_univ _) hc
  have hh := (isCompact_closedBall (0 : ℂ) r).finite_sdiff_of_mem_codiscreteWithin hc'
  exact hh.subset fun z hz => ⟨by simpa using hz.1, by simpa using hz.2⟩

/-- The zero set in the sealed definition is finite for every character and height.
Source pages 349 and 354. The principal character uses Mathlib's entire regularization. -/
theorem ntZeros_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    (ntZeros χ T).Finite := by
  have hb : ∀ z ∈ ntZeros χ T, ‖z‖ ≤ 1 + |T| := by
    intro z hz
    rcases hz with ⟨hz, hre0, hre1, him⟩
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 1 + |T| := by rw [abs_of_pos hre0]; linarith [le_abs_self T]
  by_cases hχ : χ = 1
  · subst χ
    have hf := finite_bounded_zeros (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
      (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q) (1 + |T|)
    apply hf.subset
    intro z hz
    refine ⟨hb z hz, ?_⟩
    have hz1 : z ≠ 1 := by
      intro heq
      have := hz.2.2.1
      simp [heq] at this
    change Function.update (fun s => (s - 1) * DirichletCharacter.LFunctionTrivChar q s) 1 _ z = 0
    rw [Function.update_of_ne hz1]
    change (z - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z = 0
    rw [hz.1, mul_zero]
  · have hn : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
      χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
    exact (finite_bounded_zeros (DirichletCharacter.differentiable_LFunction hχ) hn
      (1 + |T|)).subset fun z hz => ⟨hb z hz, hz.1⟩

end LeanLab.LanguascoPerelli1996.Zeros108
