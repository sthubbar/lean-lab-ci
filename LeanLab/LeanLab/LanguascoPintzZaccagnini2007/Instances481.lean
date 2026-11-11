import LeanLab.LanguascoPintzZaccagnini2007.Assembly481

/-!
Concrete checks of the parameter domains and pole normalization of P0045 pages 5 and 6.
No finite check here is presented as a proof of an analytic input.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

/-- P0045 page 5, Lemma 4.1: the pole pair contributes n. -/
theorem gammaPair_pole481 (n : ℕ) : gammaPair481 1 1 n = (n : ℂ) := by
  norm_num [gammaPair481]

/-- P0045 page 5: a family with one zero has the two required signs. -/
theorem signs_instance481 :
    zeroSign481 (0 : Fin 2) = 1 ∧ zeroSign481 (1 : Fin 2) = -1 := by
  norm_num [zeroSign481]

/-- P0045 page 6, first proof paragraph: the factor eight case attains the transfer bound. -/
theorem radical_transfer_instance481 :
    oddRad131 8 = 1 ∧ (8 : ℝ) / 8 = (oddRad131 8 : ℝ) := by
  have hpf : Nat.primeFactors 8 = {2} := by
    simpa only [show (2 : ℕ) ^ 3 = 8 by norm_num] using
      Nat.primeFactors_prime_pow (by decide : (3 : ℕ) ≠ 0) Nat.prime_two
  have hrad : oddRad131 8 = 1 := by norm_num [oddRad131, hpf]
  exact ⟨hrad, by rw [hrad]; norm_num⟩

/-- P0045 display 8: a strip of zero width below one contains no zeros. -/
theorem zeroBox_empty_instance481 : zeroBox481 16 0 1 4 = ∅ := by
  ext z
  simp only [zeroBox481, Set.mem_ofPred_eq, zero_div, sub_zero, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨_, _, _, _, hlo, hhi, _⟩
  linarith

/-- P0045 page 6: the unique character modulo one is a real primitive character. -/
theorem primitive_real_instance481 :
    (1 : DirichletCharacter ℂ 1).IsPrimitive ∧
      (∀ a : ZMod 1, ((1 : DirichletCharacter ℂ 1) a).im = 0) := by
  refine ⟨DirichletCharacter.isPrimitive_one_level_one, ?_⟩
  intro a
  rw [MulChar.one_apply (isUnit_of_subsingleton a)]
  norm_num

/-- P0045 page 5, the real zero lower bound: delta three gives a genuine trivial zero. -/
theorem real_zero_instance481 : Lfun481 (1 : DirichletCharacter ℂ 1) (1 - (3 : ℂ)) = 0 := by
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (1 - (3 : ℂ)) = 0
  rw [DirichletCharacter.LFunction_modOne_eq]
  convert riemannZeta_neg_two_mul_nat_add_one 0 using 1; norm_num

/-- P0045 display 8: the box has a genuine zero when its real strip is wide enough.
This finite parameter example uses the zeta trivial zero at minus two. -/
theorem zeroBox_nonempty_instance481 :
    (⟨1, (1 : DirichletCharacter ℂ 1), -2⟩ : Σ r : ℕ, DirichletCharacter ℂ r × ℂ) ∈
      zeroBox481 2 (3 * Real.log 2) 1 2 := by
  refine ⟨by norm_num, by norm_num, DirichletCharacter.isPrimitive_one_level_one,
    ?_, ?_, by norm_num, by norm_num⟩
  · convert real_zero_instance481 using 1; norm_num
  · have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hcancel : 3 * Real.log (2 : ℝ) / Real.log 2 = 3 := mul_div_cancel_right₀ _ hlog
    norm_num [hcancel]

/-- P0045 page 6, Corollary 4.2: a positive even right endpoint belongs to J. -/
theorem J_endpoint_instance481 {X : ℕ} (hX : 0 < X) (he : Even X) : X ∈ evenJ131 X := by
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hX, le_rfl⟩, he, by
    have hx : (0 : ℝ) ≤ X := Nat.cast_nonneg _
    linarith⟩

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.gammaPair_pole481
#print axioms LeanLab.LPZ2007.signs_instance481
#print axioms LeanLab.LPZ2007.radical_transfer_instance481
#print axioms LeanLab.LPZ2007.zeroBox_empty_instance481
#print axioms LeanLab.LPZ2007.primitive_real_instance481
#print axioms LeanLab.LPZ2007.real_zero_instance481
#print axioms LeanLab.LPZ2007.zeroBox_nonempty_instance481
#print axioms LeanLab.LPZ2007.J_endpoint_instance481
