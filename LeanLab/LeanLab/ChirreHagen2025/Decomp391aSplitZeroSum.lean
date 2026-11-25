import LeanLab.ChirreHagen2025.Decomp391a

/-!
Split of `Decomp391aSplitExplicit.zeroTerm_summable`, burst-20261122, session S149.
Chirre, Hagen and Simonic page 4 equation 3.3, absolute convergence of the zero sum,
https://arxiv.org/abs/2206.00819 .
The cited input is Ramare 2013 page 118 Lemma 4.3 and Lemma 4.2, https://doi.org/10.4064/aa159-2-2 ,
the bound 0.0462 plus 0.0008 on the multiplicity weighted reciprocal mass.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp391aSplitZeroSum
open LeanLab.ChirreHagen2025.Decomp391a

/-- LEAF: Ramare 2013 page 118 Lemma 4.3 and Lemma 4.2, the reciprocal mass of the
nontrivial zeros. Every finite set of nontrivial zeros has multiplicity weighted
reciprocal mass at most 0.047, the low part 0.0462 and the high part 0.0008.
This is the same statement as the LEAFs low_reciprocal_mass plus high_reciprocal_mass
of Decomp536aSplitMass combined. Class HARD, CITED. -/
theorem reciprocal_mass_le (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / ‖z * (z - 1)‖) ≤ 0.047 := by
  sorry

/-- CHS page 4 equation 3.3: the norm of a zero term is at most the weighted
reciprocal of the zero denominator, since x to the power re rho minus 1 is at most one. -/
theorem norm_zeroTerm_le (x : ℝ) (hx : 1 ≤ x)
    (ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}) :
    ‖zeroTerm x ρ‖ ≤
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) - 1)‖ := by
  have hx0 : 0 < x := by linarith
  have hpow : ‖(x : ℂ) ^ ((ρ : ℂ) - 1)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    apply Real.rpow_le_one_of_one_le_of_nonpos hx
    have := ρ.2.2.2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  unfold zeroTerm
  rw [norm_div, norm_mul]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have hm : ‖(analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ)‖ =
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) := by
    rw [Complex.norm_natCast]
  rw [hm]
  calc (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * ‖(x : ℂ) ^ ((ρ : ℂ) - 1)‖
      ≤ (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ = _ := mul_one _

/-- CHS page 4 equation 3.3, absolute convergence of the zero sum.
CONDITIONAL ON the LEAF reciprocal_mass_le. -/
theorem zeroTerm_summable_of_leaves (x : ℝ) (hx : 1 ≤ x) : Summable (zeroTerm x) := by
  have hg : Summable (fun ρ : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) - 1)‖) := by
    refine summable_of_sum_le (c := 0.047) (fun ρ => div_nonneg (Nat.cast_nonneg _)
      (norm_nonneg _)) (fun u => ?_)
    have h := reciprocal_mass_le (u.map ⟨Subtype.val, Subtype.val_injective⟩)
      (fun z hz => by
        rw [Finset.mem_map] at hz
        obtain ⟨ρ, _, rfl⟩ := hz
        exact ρ.2)
    rwa [Finset.sum_map] at h
  exact Summable.of_norm_bounded hg (norm_zeroTerm_le x hx)

end LeanLab.ChirreHagen2025.Decomp391aSplitZeroSum
