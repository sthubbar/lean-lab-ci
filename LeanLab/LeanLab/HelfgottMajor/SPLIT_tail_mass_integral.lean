import LeanLab.HelfgottMajor.Decomp269c

/-!
Splitting the tail mass bound `Decomp269c.tail_mass_integral` into three smaller steps.

The bound has two halves: the multiplicity weighted Mellin mass of the zeros of `L(s, χ)`
inside the critical strip above height `T` is summable, and its total is at most `4.226`
times the sum of the two tail integrals `expTailIntegral` and `gaussianTailIntegral`.

The split isolates

* the pointwise size of one zero's mass against the two branch decay envelope,
* the counting of the exponentially decaying branch against the exponential tail integral,
* the counting of the Gaussian branch against the Gaussian tail integral.

The first step carries the Mellin and multiplicity bookkeeping, the last two carry the
zero count against the density `countDensity`. `tail_mass_integral_split` assembles them by
a comparison of series and two multiplications by a nonnegative constant.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter

/-- LEAF. The pointwise step: a zero of the strip above height `T` contributes at most the
sum of the two decay branches, its analytic multiplicity folded into the constant `4.226`,
and no branch at all in the zero shift case. -/
theorem mass_pointwise_envelope (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : 100 ≤ T) :
    ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
      mellinMassTerm χ δ ρ.val ≤
        4.226 * (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  sorry

/-- LEAF. The counting step for the exponential branch: the zeros above height `T` are
sparse enough that the series of the exponential decay is summable, and its total is at
most the density weighted exponential tail integral. -/
theorem exp_count_le_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ)
    (hT : 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => exp (-0.1598 * |ρ.val.im|)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) ≤
      expTailIntegral q T := by
  sorry

/-- LEAF. The counting step for the Gaussian branch: the series of the Gaussian decay of
the zero heights is summable, and its total is at most the density weighted Gaussian tail
integral. The branch is absent at zero shift, where the tail integral is zero. -/
theorem gaussian_count_le_integral (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  sorry

/-- The tail mass bound, assembled from the three smaller steps. The summand is majorised
term by term by the envelope, the two envelope series are summed against the two tail
integrals, and the constant `4.226` is carried outside. -/
theorem tail_mass_integral_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val) ≤
      4.226 * (expTailIntegral q T + gaussianTailIntegral q δ T) := by
  classical
  have hT100 : (100 : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hpoint := mass_pointwise_envelope q χ δ T hT100
  obtain ⟨hs1, hle1⟩ := exp_count_le_integral q χ T hT100
  obtain ⟨hs2, hle2⟩ := gaussian_count_le_integral q χ δ T hT
  have henv : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        4.226 * (exp (-0.1598 * |ρ.val.im|) +
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :=
    (hs1.add hs2).mul_left 4.226
  have hmass : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => mellinMassTerm χ δ ρ.val) := by
    refine Summable.of_norm_bounded henv (fun ρ => ?_)
    rw [Real.norm_of_nonneg (by simp only [mellinMassTerm]; positivity)]
    exact hpoint ρ
  refine ⟨hmass, ?_⟩
  calc (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, mellinMassTerm χ δ ρ.val)
      ≤ ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          4.226 * (exp (-0.1598 * |ρ.val.im|) +
            if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) :=
        hmass.tsum_le_tsum hpoint henv
    _ = 4.226 * ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, exp (-0.1598 * |ρ.val.im|)) +
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
              if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) := by
        rw [tsum_mul_left]
        rw [hs1.tsum_add hs2]
    _ ≤ 4.226 * (expTailIntegral q T + gaussianTailIntegral q δ T) :=
        mul_le_mul_of_nonneg_left (add_le_add hle1 hle2) (by norm_num)

end LeanLab.HelfgottMajor.Decomp269c
