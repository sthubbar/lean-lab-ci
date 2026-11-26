import Mathlib

/-!
# Split of `Display10LderivSplit.leaf_Lderiv_series`

Burst burst-20261122, Claude cloud session S150. AI wrote the Lean code. Binary Goldbach is open.

`leaf_Lderiv_series_of_leaves` is the exact type twin of
`Display10LderivSplit.leaf_Lderiv_series`, proved from one leaf: the locally uniform convergence
of the partial sums of the Dirichlet series of `L(s, χ)` on `Re s > 0` for nonprincipal `χ`.
Termwise differentiation, Weierstrass, then gives the derivative statement.
-/

namespace LeanLab.ExceptionalSet.UpJ200.LderivSeriesSplit

open Real Filter Topology

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 4 with chapter 14, Abel summation
continuation of `L(s, χ)` to `Re s > 0` for nonprincipal `χ`, class MEDIUM: using bounded
character sums, the partial sums `∑_{n < M} χ(n) n^{-s}` converge locally uniformly on the open
half plane `Re s > 0`, and their limit is Mathlib's continued `LFunction`, by agreement with
`LSeries` on `Re s > 1` and the identity theorem. -/
theorem leaf_partial_sums_tendstoLocallyUniformlyOn (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (s : ℂ) => ∑ n ∈ Finset.range M, χ n * (n : ℂ) ^ (-s))
      χ.LFunction atTop {s : ℂ | 0 < s.re} := by
  sorry

/-- Termwise derivative of `n^{-s}`, valid also for `n = 0` away from `s = 0`. -/
lemma hasDerivAt_natCast_cpow_neg (n : ℕ) (s : ℂ) (hs : s ≠ 0) :
    HasDerivAt (fun s : ℂ => (n : ℂ) ^ (-s)) (-((Real.log n : ℂ) * (n : ℂ) ^ (-s))) s := by
  have h1 : HasStrictDerivAt (fun y : ℂ => (n : ℂ) ^ y)
      ((n : ℂ) ^ (-s) * Complex.log n) (-s) :=
    Complex.hasStrictDerivAt_const_cpow (Or.inr (neg_ne_zero.mpr hs))
  have h2 : HasDerivAt (fun s : ℂ => (n : ℂ) ^ (-s))
      ((n : ℂ) ^ (-s) * Complex.log n * -1) s :=
    h1.hasDerivAt.comp s (hasDerivAt_neg s)
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  convert h2 using 1
  rw [hlog]; ring

/-- Exact type twin of `Display10LderivSplit.leaf_Lderiv_series`, proved from the leaf above. -/
theorem leaf_Lderiv_series_of_leaves : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r),
    χ ≠ 1 →
    ∀ σ : ℝ, 0 < σ →
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
          χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))))
        atTop (𝓝 (-deriv χ.LFunction (σ : ℂ))) := by
  intro r hr χ hχ σ hσ
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hUdef
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hL := leaf_partial_sums_tendstoLocallyUniformlyOn r χ hχ
  have hdiff : ∀ᶠ M : ℕ in atTop, DifferentiableOn ℂ
      (fun s : ℂ => ∑ n ∈ Finset.range M, χ n * (n : ℂ) ^ (-s)) U := by
    refine Eventually.of_forall fun M s hs => ?_
    have hs0 : s ≠ 0 := by
      rintro rfl; simp [hUdef] at hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun n _ => ?_
    exact ((hasDerivAt_natCast_cpow_neg n s hs0).differentiableAt).const_mul _
  have hD := hL.deriv hdiff hUo
  have hσU : (σ : ℂ) ∈ U := by simp [hUdef, hσ]
  have hpt := hD.tendsto_at hσU
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  have heq : ∀ M : ℕ, (deriv ∘ fun (M : ℕ) (s : ℂ) =>
      ∑ n ∈ Finset.range M, χ n * (n : ℂ) ^ (-s)) M (σ : ℂ) =
      -∑ n ∈ Finset.range M, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))) := by
    intro M
    have : HasDerivAt (fun s : ℂ => ∑ n ∈ Finset.range M, χ n * (n : ℂ) ^ (-s))
        (∑ n ∈ Finset.range M, χ n * -((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))) σ := by
      have := HasDerivAt.fun_sum (u := Finset.range M) (A := fun n s => χ n * (n : ℂ) ^ (-s))
        (A' := fun n => χ n * -((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))) (x := (σ : ℂ))
        (fun n _ => (hasDerivAt_natCast_cpow_neg n σ hσ0).const_mul _)
      exact this
    simp only [Function.comp_apply, this.deriv, mul_neg, Finset.sum_neg_distrib]
  simp_rw [heq] at hpt
  have := hpt.neg
  simpa using this

#print axioms leaf_Lderiv_series_of_leaves
#print axioms hasDerivAt_natCast_cpow_neg

end LeanLab.ExceptionalSet.UpJ200.LderivSeriesSplit
