import LeanLab.LPZ2007.RealZeroProof
import LeanLab.HardyLittlewood1923.U1503LogDeriv

/-!
The finiteness part of the exceptional zero family on P0045 pages 4 and 5.
Jutila 1977 page 46 counts primitive zeros in a bounded rectangle.
Only finiteness is established here. The uniform density bound stays open.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007.ZeroFamily373

open Complex Real Set Metric
open LeanLab.HardyLittlewood1923.U1503
open LeanLab.PNTPort.DirichletZF.U1482

/-- P0045 page 5, bounded zero families.
A nonzero entire function has finitely many zeros in any fixed rectangle. -/
theorem rectangle_zeros_finite (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h2 : f 2 ≠ 0) (a T : ℝ) :
    {z : ℂ | f z = 0 ∧ a ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T}.Finite := by
  let C : ℝ := |a| + |T| + 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hCn : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let g : ℂ → ℂ := fun w => f (2 + (C : ℂ) * w)
  have hg : Differentiable ℂ g := hf.comp (by fun_prop)
  have hg0 : g 0 ≠ 0 := by simpa [g] using h2
  refine ((finite_zeros_of_entire hg hg0).image (fun w : ℂ => 2 + (C : ℂ) * w)).subset ?_
  intro z hz
  have hnorm : ‖z - 2‖ ≤ C := by
    have hre : |(z - 2).re| ≤ 2 + |a| := by
      change |z.re - 2| ≤ 2 + |a|
      rw [abs_of_nonpos (by linarith [hz.2.2.1])]
      linarith [neg_abs_le a, hz.2.1]
    have him : |(z - 2).im| ≤ |T| := by
      simpa using hz.2.2.2.trans (le_abs_self T)
    calc
      ‖z - 2‖ ≤ |(z - 2).re| + |(z - 2).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (2 + |a|) + |T| := add_le_add hre him
      _ ≤ C := by dsimp [C]; linarith
  have he : 2 + (C : ℂ) * ((z - 2) / C) = z := by field_simp; ring
  refine ⟨(z - 2) / C, ?_, he⟩
  change ‖(z - 2) / (C : ℂ)‖ ≤ 1 ∧ g ((z - 2) / C) = 0
  constructor
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC,
      div_le_one hC]
    exact hnorm
  · simpa only [g, he] using hz.1

/-- P0045 page 4, display 8. Actual zeros of a primitive character lie left of one.
The primitive principal case has modulus one and is the zeta function. -/
theorem primitive_zero_re_lt_one {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    {ρ : ℂ} (hz : Lfun χ ρ = 0) : ρ.re < 1 := by
  have hr0 : r ≠ 0 := by omega
  haveI : NeZero r := ⟨hr0⟩
  have hzL : DirichletCharacter.LFunction χ ρ = 0 := by simpa [Lfun, hr0] using hz
  by_contra h
  have hρ : 1 ≤ ρ.re := le_of_not_gt h
  by_cases hχ : χ = 1
  · have hr1 : r = 1 := by
      rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one] at hprim
      exact hprim.symm
    subst r
    have hzζ : riemannZeta ρ = 0 := by
      simpa [hχ, DirichletCharacter.LFunction_modOne_eq] using hzL
    exact riemannZeta_ne_zero_of_one_le_re hρ hzζ
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hρ hzL

/-- P0045 pages 4 and 5, display 8. A primitive character has finitely many
zeros in the bounded strip used for the exceptional family. -/
theorem primitive_zeros_finite {r : ℕ} (hr : 1 ≤ r)
    (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive) (a T : ℝ) :
    {ρ : ℂ | Lfun χ ρ = 0 ∧ a ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite := by
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
    refine (rectangle_zeros_finite gZ hdiff h2 a T).subset ?_
    intro ρ hz
    have hzζ : riemannZeta ρ = 0 := by
      simpa [Lfun, hχ, DirichletCharacter.LFunction_modOne_eq] using hz.1
    have hne : ρ ≠ 1 := by intro he; exact riemannZeta_one_ne_zero (he ▸ hzζ)
    refine ⟨?_, hz.2.1, (primitive_zero_re_lt_one (by norm_num) χ hprim hz.1).le, hz.2.2⟩
    rw [gZ_of_ne hne, hzζ, mul_zero]
  · have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
    refine (rectangle_zeros_finite _ (DirichletCharacter.differentiable_LFunction hχ) h2 a T).subset ?_
    intro ρ hz
    exact ⟨by simpa [Lfun, hr0] using hz.1, hz.2.1,
      (primitive_zero_re_lt_one hr χ hprim hz.1).le, hz.2.2⟩

/-- P0045 pages 4 and 5, display 8. The entire exceptional zero set is finite.
This supplies only the finiteness clause of JutilaBound, with no density assertion. -/
theorem EZero_finite (X H T P : ℝ) : (EZero X H T P).Finite := by
  classical
  let F (r : ℕ) : Set (DirichletCharacter ℂ r × ℂ) :=
    {w | w.1.IsPrimitive ∧ Lfun w.1 w.2 = 0 ∧
      1 - H / Real.log X ≤ w.2.re ∧ |w.2.im| ≤ T}
  have hF : ∀ r ∈ Set.Icc 1 ⌊P⌋₊, (F r).Finite := by
    intro r hr
    have hfinite := (Set.toFinite {χ : DirichletCharacter ℂ r | χ.IsPrimitive}).biUnion
      (fun χ hχ => (primitive_zeros_finite hr.1 χ hχ (1 - H / Real.log X) T).image
        (fun ρ : ℂ => (χ, ρ)))
    refine hfinite.subset ?_
    intro w hw
    exact Set.mem_iUnion.2 ⟨w.1, Set.mem_iUnion.2 ⟨hw.1, w.2, hw.2, rfl⟩⟩
  refine ((Set.finite_Icc 1 ⌊P⌋₊).sigma hF).subset ?_
  intro z hz
  exact ⟨⟨hz.1, Nat.le_floor hz.2.1⟩, hz.2.2.1, hz.2.2.2.1,
    hz.2.2.2.2.1, hz.2.2.2.2.2⟩

end LeanLab.LPZ2007.ZeroFamily373

#print axioms LeanLab.LPZ2007.ZeroFamily373.rectangle_zeros_finite
#print axioms LeanLab.LPZ2007.ZeroFamily373.primitive_zero_re_lt_one
#print axioms LeanLab.LPZ2007.ZeroFamily373.primitive_zeros_finite
#print axioms LeanLab.LPZ2007.ZeroFamily373.EZero_finite
