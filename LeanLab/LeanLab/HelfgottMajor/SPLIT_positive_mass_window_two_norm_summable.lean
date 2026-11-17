import LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le

/-!
Refinement of `positive_mass_window_two_norm_summable` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_window_two_le`.

The statement refined here says that the nonnegative family of the Gaussian Mellin norms attached
to the zeros of a Dirichlet `L`-function in the strip `0 < re < 1` and below height `T` is
summable. Nothing in the statement restricts the zeros, so the only thing that can make the
family converge is that there are finitely many of them below a fixed height.

The first cut of this step had three open pieces, and its third piece was false as it stood:
pairwise isolated points inside a closed ball need not be finite, the points `1/(n+1)` of the real
axis being infinitely many, isolated from each other, and all inside the closed unit ball. What
the finiteness needs in addition is that the set has no accumulation point anywhere in the plane,
which is what makes it closed.

Nothing in this file is open. A closed set of isolated points has no accumulation point, and the
zero set of a differentiable function that is not identically zero is both: closed, as a preimage
of a closed set under a continuous function, and a set of isolated points, as the zeros of an
analytic function that is not identically zero. For the trivial character the `L`-function is an
update of an entire function at the pole, so its zero set sits in the union of the zero set of that
entire function and the single point one, and neither of those has an accumulation point. The
strip zeros then lie in the closed ball of radius `T` plus two, since the real part is below one
and the ordinate is at most `T` in absolute value, and a closed set of isolated points inside a
closed ball is finite, the ball being compact, and a finite index set makes a real valued family
summable. That is the statement refined here, proved with no gap and with no zero count imported.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real Filter LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-! ### The analytic piece -/

/-- A closed set of isolated points has no accumulation point anywhere. A cluster point of such a
set lies in its closure, hence in the set, and there one of the open neighbourhoods that isolates
the point meets the set only at that point, which contradicts the definition of an accumulation
point. -/
theorem positive_mass_window_two_no_accPt_of_isClosed_isDiscrete (S : Set ℂ) (hc : IsClosed S)
    (hd : IsDiscrete S) : ∀ z : ℂ, ¬ AccPt z (𝓟 S) := by
  intro z hz
  have hzS : z ∈ S := hc.closure_eq ▸ hz.clusterPt.mem_closure
  obtain ⟨u, hu, huint⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hd z hzS
  have hzu : z ∈ u := by
    have h : z ∈ u ∩ S := by rw [huint]; exact rfl
    exact h.1
  obtain ⟨y, hyuS, hyne⟩ := accPt_iff_nhds.mp hz u (hu.mem_nhds hzu)
  obtain ⟨hyu, hyS⟩ := hyuS
  have hmem : y ∈ u ∩ S := ⟨hyu, hyS⟩
  rw [huint] at hmem
  exact hyne (by simpa using hmem)

/-- A differentiable complex function that is not identically zero has no accumulation point in
its zero set. That zero set is codiscrete, because the zeros of an analytic function that is not
identically zero are isolated, and it is closed, being the preimage of a closed set under a
continuous function. -/
theorem positive_mass_window_two_no_accPt_zeroSet (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hw : ∃ w : ℂ, f w ≠ 0) :
    ∀ z : ℂ, ¬ AccPt z (𝓟 {w : ℂ | f w = 0}) := by
  obtain ⟨w, hw⟩ := hw
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hd : f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ := by
    simpa [Filter.codiscrete] using
      ha.preimage_zero_mem_codiscreteWithin hw (Set.mem_univ w) isConnected_univ
  have hdisc : IsDiscrete {w : ℂ | f w = 0} := by
    have hset : {w : ℂ | f w = 0} = (f ⁻¹' {0}ᶜ)ᶜ := by
      ext w
      simp
    rw [hset]
    exact (mem_codiscrete'.mp hd).2
  have hclosed : IsClosed {w : ℂ | f w = 0} := by
    have hset : {w : ℂ | f w = 0} = f ⁻¹' {0} := by
      ext w
      simp
    rw [hset]
    exact isClosed_singleton.preimage hf.continuous
  exact positive_mass_window_two_no_accPt_of_isClosed_isDiscrete _ hclosed hdisc

/-- The no accumulation point property for the full zero set of the `L`-function, including the
trivial character, where the function is an update at the pole away from an entire function. -/
theorem positive_mass_window_two_zeros_no_accPt (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∀ z : ℂ, ¬ AccPt z (𝓟 {w : ℂ | DirichletCharacter.LFunction χ w = 0}) := by
  by_cases hχ : χ = 1
  · subst hχ
    have hbase : ∀ z : ℂ,
        ¬ AccPt z (𝓟 {w : ℂ | DirichletCharacter.LFunctionTrivChar₁ q w = 0}) :=
      positive_mass_window_two_no_accPt_zeroSet _
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ q)
        ⟨1, DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q⟩
    have hone : ∀ z : ℂ, ¬ AccPt z (𝓟 ({1} : Set ℂ)) := by
      have h := positive_mass_window_two_no_accPt_zeroSet (fun z : ℂ => z - 1)
        (by fun_prop) ⟨0, by norm_num⟩
      simpa [sub_eq_zero] using h
    intro z hz
    have hsub : {w : ℂ | DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w = 0} ⊆
        {w : ℂ | DirichletCharacter.LFunctionTrivChar₁ q w = 0} ∪ {1} := by
      intro w hw
      by_cases hw1 : w = 1
      · exact Or.inr hw1
      · left
        show DirichletCharacter.LFunctionTrivChar₁ q w = 0
        rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hw1]
        exact mul_eq_zero_of_right _ hw
    have h' := hz.mono (principal_mono.mpr hsub)
    rw [← sup_principal, accPt_sup] at h'
    rcases h' with h' | h'
    · exact hbase z h'
    · exact hone z h'
  · exact positive_mass_window_two_no_accPt_zeroSet _
      (DirichletCharacter.differentiable_LFunction hχ)
      ⟨2, DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)⟩

/-! ### The proved pieces -/

/-- The arithmetic ingredient. A zero of the open strip whose ordinate is at most `T` in absolute
value has modulus at most `T` plus two, so the whole family sits inside one closed ball. The norm
of a complex number is at most the sum of the absolute values of its parts, the real part lies
between zero and one, and the ordinate is at most `T` in absolute value. At negative `T` the set
is empty, since an absolute value is nonnegative. -/
theorem positive_mass_window_two_strip_zeros_subset_ball (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {z : ℂ | DirichletCharacter.LFunction χ z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T} ⊆
      Metric.closedBall (0 : ℂ) (|T| + 2) := by
  intro z hz
  obtain ⟨_, hpos, hlt, him⟩ := hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |z.re| ≤ 1 := by
    rw [abs_of_pos hpos]
    linarith
  have him' : |z.im| ≤ |T| := le_trans him (le_abs_self T)
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + |T| := by linarith
    _ ≤ |T| + 2 := by linarith

/-- The topological ingredient. A set of points of the plane with no accumulation point is
closed, and a closed set of isolated points inside a closed ball is finite. A point of the closure
outside the set would be an accumulation point, so the set is closed; the closed ball is bounded,
so the set meets its closure in a compact set of isolated points, which is finite. -/
theorem positive_mass_window_two_finite_of_no_accPt (S : Set ℂ) (R : ℝ)
    (h : ∀ x : ℂ, ¬ AccPt x (𝓟 S)) (hsub : S ⊆ Metric.closedBall (0 : ℂ) R) :
    S.Finite := by
  have hclosed : IsClosed S := by
    rw [isClosed_iff_clusterPt]
    intro x hx
    by_contra hxS
    refine h x ?_
    rw [accPt_iff_frequently]
    exact (clusterPt_principal_iff_frequently.mp hx).mono
      fun y hy => ⟨fun hyx => hxS (hyx ▸ hy), hy⟩
  have hdisc : IsDiscrete S :=
    isDiscrete_iff_discreteTopology.mpr (discreteTopology_of_noAccPts fun x _ => h x)
  exact (Metric.finite_isBounded_inter_isClosed (K := Metric.closedBall (0 : ℂ) R) hdisc
    Metric.isBounded_closedBall hclosed).subset fun z hz => ⟨hsub hz, hz⟩

/-! ### The assembly -/

/-- The assembly: the strip zeros have no accumulation point because the whole zero set has none
and they are a subset of it, they lie in the closed ball of radius `T` plus two by the arithmetic
piece, so they are finite by the topological piece, and a real valued family over a finite index
set is summable. -/
theorem positive_mass_window_two_norm_summable_split (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hT : 1 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} => ‖mellinMassTerm χ δ ρ.val‖) := by
  have hno := positive_mass_window_two_zeros_no_accPt q χ
  have hsub := positive_mass_window_two_strip_zeros_subset_ball q χ T
  have hno' : ∀ z : ℂ,
      ¬ AccPt z (𝓟 {w : ℂ | DirichletCharacter.LFunction χ w = 0 ∧ 0 < w.re ∧
        w.re < 1 ∧ |w.im| ≤ T}) := fun z hz =>
    hno z (hz.mono (principal_mono.mpr fun w hw => hw.1))
  exact (positive_mass_window_two_finite_of_no_accPt _ (|T| + 2) hno' hsub).summable
    (fun z => ‖mellinMassTerm χ δ z‖)

end LeanLab.HelfgottMajor.Decomp431a
