import LeanLab.HelfgottMajor.SPLIT_gaussian_count_le_integral

/-!
A conditional Lean refutation of the leaf `gaussian_count_tsum_le` of
`SPLIT_gaussian_count_le_integral`.

That leaf asks that the total Gaussian weight of the strip zeros of `L(s, χ)` above height `T`
be at most `gaussianTailIntegral q δ T`.  Burst burst-20261122, sessions S94 and S97, reported it
FALSE numerically at `q = 1`, `δ = 1`, `T` just below the zero of `ζ` at ordinate
`101.3178510057`, see `notes/burst-20261122/HelfgottMajor-feed1122-SPLIT_gaussian_count_le_integral.md`:
the sum runs over both signs of the ordinate while `countDensity` is the one sided density, and a
zero just above `T` carries almost the whole weight `exp (-0.1065 (T/π)²)` twice.

This file turns that report into a kernel checked implication at `q = 1`, `δ = 1`,
`T = 101.3`.  Its one input, `hzero`, is a single zero of `ζ` on the critical line with
ordinate `γ` in `(101.3, 101.4]`; the ordinate `101.3178510057` is the 30th zero of `ζ` with positive ordinate, in the
tables of Odlyzko and of the LMFDB.  The upper side uses the proved bound
`Decomp269c.gaussian_integral_bound`, display 4.41 of P0014, so no integral is computed here:
the integral is at most `0.18787 · log (T/2π) · exp (-0.1065 (T/π)²) < 0.57 exp (-0.1065 (T/π)²)`,
while the zero and its conjugate alone give more than `1.5 exp (-0.1065 (T/π)²)`.

The theorem is CONDITIONAL ON that one input.  The leaf itself stays open in its file; no
statement is changed.  AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp269c.RefuteGaussianTsum
open Real

/-- Numerical core.  For `101.3 < γ ≤ 101.4`, twice the Gaussian weight at `γ` beats the
bound of display 4.41 at `T = 101.3`, `δ = 1`, `q = 1`. -/
theorem gaussian_numeric_beat (γ : ℝ) (h1 : 101.3 < γ) (h2 : γ ≤ 101.4) :
    0.18787 * |(1 : ℝ)| * log (((1 : ℕ) : ℝ) * 101.3 / (2 * π)) *
        exp (-0.1065 * (101.3 / (π * |(1 : ℝ)|)) ^ 2) <
      exp (-0.1065 * (γ / (π * |(1 : ℝ)|)) ^ 2) +
        exp (-0.1065 * (γ / (π * |(1 : ℝ)|)) ^ 2) := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hπ : 0 < π := Real.pi_pos
  simp only [abs_one, mul_one, Nat.cast_one, one_mul]
  set A : ℝ := 0.1065 * (101.3 / π) ^ 2 with hA
  set B : ℝ := 0.1065 * (γ / π) ^ 2 with hB
  have hBA : B - A ≤ 0.23 := by
    have heq : B - A = 0.1065 * (γ ^ 2 - 101.3 ^ 2) / π ^ 2 := by
      rw [hA, hB]; field_simp
    rw [heq, div_le_iff₀ (by positivity)]
    have hsq : γ ^ 2 - 101.3 ^ 2 ≤ 0.1 * 202.8 := by nlinarith
    nlinarith
  have hexpB : exp (-B) ≥ 0.77 * exp (-A) := by
    have h := Real.add_one_le_exp (-(B - A))
    have hsplit : exp (-B) = exp (-A) * exp (-(B - A)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have hA0 : 0 < exp (-A) := Real.exp_pos _
    nlinarith
  have hlog : log (101.3 / (2 * π)) < 3 := by
    have hx : 0 < 101.3 / (2 * π) := by positivity
    rw [Real.log_lt_iff_lt_exp hx]
    have he : (2.7 : ℝ) ^ 3 < exp 3 := by
      have h := Real.exp_one_gt_d9
      have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      exact pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    have hq : 101.3 / (2 * π) < 16.2 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hA0 : 0 < exp (-A) := Real.exp_pos _
  have hlA : 0.18787 * log (101.3 / (2 * π)) * exp (-A) ≤ 0.18787 * 3 * exp (-A) := by
    have := mul_le_mul_of_nonneg_left hlog.le (by norm_num : (0 : ℝ) ≤ 0.18787)
    exact mul_le_mul_of_nonneg_right this hA0.le
  have hnegA : -0.1065 * (101.3 / π) ^ 2 = -A := by rw [hA]; ring
  have hnegB : -0.1065 * (γ / π) ^ 2 = -B := by rw [hB]; ring
  rw [hnegA, hnegB]
  linarith

/-- Conditional refutation of `gaussian_count_tsum_le`.  CONDITIONAL ON `hzero`, one zero of
`ζ` on the critical line with ordinate in `(101.3, 101.4]`, cited in the module note.  At
`q = 1`, the trivial character, `δ = 1` and `T = 101.3` the zero and its conjugate already give
more Gaussian weight than the proved bound `gaussian_integral_bound` allows for the integral. -/
theorem not_gaussian_count_tsum_le (γ : ℝ) (h1 : 101.3 < γ) (h2 : γ ≤ 101.4)
    (hzero : riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    ¬ (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hδ : δ ≠ 0)
        (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
        (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
              exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))),
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
              exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
          gaussianTailIntegral q δ T) := by
  intro hleaf
  set χ : DirichletCharacter ℂ 1 := 1 with hχdef
  have hL : DirichletCharacter.LFunction χ = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  have hδ : (1 : ℝ) ≠ 0 := one_ne_zero
  have hT : max (4 * π ^ 2 * |(1 : ℝ)|) 100 ≤ (101.3 : ℝ) := by
    have hpi2 := Real.pi_lt_d2
    have hπ : 0 < π := Real.pi_pos
    rw [abs_one, mul_one]
    apply max_le _ (by norm_num)
    nlinarith
  have hs := gaussian_count_summable 1 χ 1 101.3 hδ hT
  have hle := hleaf 1 χ 1 101.3 hδ hT hs
  have hbound := gaussian_integral_bound 1 1 101.3 hδ hT
  -- the zero and its conjugate
  set z₁ : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I with hz₁
  set z₂ : ℂ := (1 / 2 : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I with hz₂
  have hz2zero : riemannZeta z₂ = 0 := by
    have hc : z₂ = (starRingEnd ℂ) z₁ := by
      apply Complex.ext <;> simp [hz₁, hz₂]
    rw [hc, riemannZeta_conj, hzero, map_zero]
  have hγ0 : 0 < γ := by linarith
  have hm₁ : DirichletCharacter.LFunction χ z₁ = 0 ∧ 0 < z₁.re ∧ z₁.re < 1 ∧
      (101.3 : ℝ) < |z₁.im| := by
    refine ⟨by rw [hL]; exact hzero, by simp [hz₁], by norm_num [hz₁], ?_⟩
    simp [hz₁, abs_of_pos hγ0]; linarith
  have hm₂ : DirichletCharacter.LFunction χ z₂ = 0 ∧ 0 < z₂.re ∧ z₂.re < 1 ∧
      (101.3 : ℝ) < |z₂.im| := by
    refine ⟨by rw [hL]; exact hz2zero, by simp [hz₂], by norm_num [hz₂], ?_⟩
    simp [hz₂, abs_of_pos hγ0]; linarith
  let a : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ (101.3 : ℝ) < |ρ.im|} := ⟨z₁, hm₁⟩
  let b : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ (101.3 : ℝ) < |ρ.im|} := ⟨z₂, hm₂⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg (fun x => x.val.im) h
    simp [a, b, hz₁, hz₂] at this
    linarith
  have hsle := hs.sum_le_tsum {a, b} (fun ρ _ => (Real.exp_pos _).le)
  rw [Finset.sum_pair hab] at hsle
  have ha : |a.val.im| = γ := by simp [a, hz₁, abs_of_pos hγ0]
  have hb : |b.val.im| = γ := by simp [b, hz₂, abs_of_pos hγ0]
  rw [ha, hb] at hsle
  have hnum := gaussian_numeric_beat γ h1 h2
  linarith

end LeanLab.HelfgottMajor.Decomp269c.RefuteGaussianTsum

#print axioms LeanLab.HelfgottMajor.Decomp269c.RefuteGaussianTsum.not_gaussian_count_tsum_le
