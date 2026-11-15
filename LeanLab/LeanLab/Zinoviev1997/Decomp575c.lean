/-
AI wrote this Lean code. Codex task575, 2026-11-15.
Character inputs for the endpoint estimate in Proposition 1.4, pp. 340 to 341.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Decomp575a
import LeanLab.PNTPort.BV.Helpers

namespace LeanLab.Zinoviev1997.Decomp575c
open LeanLab.Zinoviev1997.State1546 ArithmeticFunction

/-- A nonprincipal character has conductor at least three, supporting p. 340. -/
theorem nonprincipal_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) : 3 ≤ χ.conductor := by
  have hzero := χ.conductor_ne_zero
  have : NeZero χ.conductor := ⟨hzero⟩
  have hone : χ.conductor ≠ 1 := fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have htwo : χ.conductor ≠ 2 := by
    intro htwo
    have hcard : Nat.card (DirichletCharacter ℂ χ.conductor) = 1 := by
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, htwo]
      decide
    have hfc : Fintype.card (DirichletCharacter ℂ χ.conductor) ≤ 1 := by
      rw [← Nat.card_eq_fintype_card, hcard]
    have hsub : Subsingleton (DirichletCharacter ℂ χ.conductor) :=
      Fintype.card_le_one_iff_subsingleton.mp hfc
    have hp : χ.primitiveCharacter = 1 :=
      @Subsingleton.elim (DirichletCharacter ℂ χ.conductor) hsub _ _
    have he := χ.changeLevel_primitiveCharacter
    rw [hp, DirichletCharacter.changeLevel_one] at he
    exact hχ he.symm
  omega

/-- The excluded Mangoldt mass in the p. 340 character induction comparison. -/
noncomputable def excludedMangoldt (x : ℝ) (q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, if Nat.Coprime n q then 0 else vonMangoldt n

/-- The p. 340 excluded mass bound from the existing lab psiBad estimate. -/
theorem excludedMangoldt_bound {q : ℕ} [NeZero q] {x : ℝ}
    (hx : 10 ^ 9 ≤ x) (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    excludedMangoldt x q ≤ Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hq : 0 < q := NeZero.pos q
  have hqlog : Real.log (q : ℝ) ≤ 0.37 * Real.log x := by
    have hh := Real.log_le_log (by exact_mod_cast hq : (0 : ℝ) < q) hqx
    rwa [Real.log_rpow hx0] at hh
  have he : excludedMangoldt x q = LeanLab.PNTPort.BV.psiBad x q := by
    unfold excludedMangoldt LeanLab.PNTPort.BV.psiBad
    rw [Finset.sum_filter]
    have hset : Finset.Iic ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    have hz : (if Nat.Coprime 0 q then (0 : ℝ) else vonMangoldt 0) = 0 := by
      split_ifs <;> rfl
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : Nat.Coprime n q <;> simp [h]
  calc
    _ = LeanLab.PNTPort.BV.psiBad x q := he
    _ ≤ Real.log q / Real.log 2 * Real.log x :=
      LeanLab.PNTPort.BV.psiBad_le (by linarith) (by omega)
    _ ≤ Real.log x ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h2]
      have hh := mul_le_mul_of_nonneg_right hqlog hL
      have hh2 := mul_le_mul_of_nonneg_right (show (0.37 : ℝ) ≤ Real.log 2 by
        linarith [Real.log_two_gt_d9]) (sq_nonneg (Real.log x))
      nlinarith

/-- Character induction changes psi by at most the excluded Mangoldt mass, p. 340. -/
theorem induced_difference_le_excluded {q d : ℕ} [NeZero q] [NeZero d] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (x : ℝ) :
    ‖psiChi (DirichletCharacter.changeLevel hd χ) x - psiChi χ x‖ ≤ excludedMangoldt x q := by
  unfold psiChi excludedMangoldt
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  by_cases hcop : Nat.Coprime n q
  · have he := χ.changeLevel_eq_cast_of_dvd hd (ZMod.unitOfCoprime n hcop)
    simp only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] at he
    rw [ite_eq_left hcop, he, sub_self, norm_zero]
  · have hnu : ¬ IsUnit (n : ZMod q) := by
      intro hu
      exact hcop ((ZMod.isUnit_iff_coprime n q).mp hu)
    rw [(DirichletCharacter.changeLevel hd χ).map_nonunit hnu]
    simp only [zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      ite_eq_right hcop]
    have he := mul_le_mul_of_nonneg_right (χ.norm_le_one (n : ZMod d))
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    simpa only [one_mul] using he

/-- Proposition 1.4, p. 340, the displayed imprimitive character comparison.
The induced primitive character differs only at integers not coprime to the level.
The stated modulus range is retained when bounding that excluded Mangoldt mass. -/
theorem induced_psi_difference {q d : ℕ} [NeZero q] [NeZero d] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ‖psiChi (DirichletCharacter.changeLevel hd χ) x - psiChi χ x‖ ≤ Real.log x ^ 2 := by
  exact (induced_difference_le_excluded hd χ x).trans (excludedMangoldt_bound hx hqx)

/-- LEAF. Proposition 1.4, p. 341, first display, quoted from reference 4.
Schoenfeld 1976 bounds the ordinary psi error under RH by square root x times
log squared x divided by eight pi for x greater than 75. GRH supplies RH here. -/
theorem schoenfeld_psi (hG : LeanLab.DERZ1997.GRH) {x : ℝ} (hx : 75 < x) :
    |Chebyshev.psi x - x| ≤ 1 / (8 * Real.pi) * Real.sqrt x * Real.log x ^ 2 := by
  sorry

/-- The level one twisted psi sum is ordinary psi, supporting p. 341. -/
theorem psiChi_level_one (x : ℝ) :
    psiChi (1 : DirichletCharacter ℂ 1) x = (Chebyshev.psi x : ℂ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Complex.ofReal_sum]
  unfold psiChi
  apply Finset.sum_congr rfl
  intro n hn
  rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n 1).mpr (by simp)), one_mul]

/-- The endpoint character errors on p. 340 from the primitive and Schoenfeld inputs.
CONDITIONAL ON schoenfeld_psi and the unchanged lemma13.
The character induction correction is proved. -/
theorem character_error (hG : LeanLab.DERZ1997.GRH) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ‖psiChi χ x - if χ = 1 then (x : ℂ) else 0‖ ≤
      0.85 * Real.sqrt x * Real.log x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 100 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by linarith)
  have hsq : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hsmall : Real.log x ^ 2 ≤ 0.01 * Real.sqrt x * Real.log x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hs hsq]
  by_cases hχ : χ = 1
  · subst χ
    simp only [ite_true]
    have hd := induced_psi_difference (q := q) (d := 1) (one_dvd q)
      (1 : DirichletCharacter ℂ 1) hx hqx
    rw [DirichletCharacter.changeLevel_one, psiChi_level_one] at hd
    have hp := schoenfeld_psi hG (show 75 < x by linarith)
    have hp' : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ ≤
        0.05 * Real.sqrt x * Real.log x ^ 2 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine hp.trans ?_
      have hc : 1 / (8 * Real.pi) ≤ (0.05 : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        linarith [Real.pi_gt_three]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg x)) hsq
    have ht : ‖psiChi (1 : DirichletCharacter ℂ q) x - (x : ℂ)‖ ≤
        ‖psiChi (1 : DirichletCharacter ℂ q) x - (Chebyshev.psi x : ℂ)‖ +
          ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := by
      calc
        _ = ‖(psiChi (1 : DirichletCharacter ℂ q) x - (Chebyshev.psi x : ℂ)) +
            ((Chebyshev.psi x : ℂ) - (x : ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) hsq]
  · simp only [ite_eq_right hχ, sub_zero]
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hc : (χ.conductor : ℝ) ≤ x ^ (0.37 : ℝ) := by
      have hle : (χ.conductor : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
      exact hle.trans hqx
    have hp := lemma13 hG (nonprincipal_conductor χ hχ) χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive hx hc
    have hd := induced_psi_difference χ.conductor_dvd_level χ.primitiveCharacter hx hqx
    rw [χ.changeLevel_primitiveCharacter] at hd
    have ht : ‖psiChi χ x‖ ≤ ‖psiChi χ x - psiChi χ.primitiveCharacter x‖ +
        ‖psiChi χ.primitiveCharacter x‖ := by
      calc
        _ = ‖(psiChi χ x - psiChi χ.primitiveCharacter x) + psiChi χ.primitiveCharacter x‖ := by
          congr 1; ring
        _ ≤ _ := norm_add_le _ _
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) hsq]

end LeanLab.Zinoviev1997.Decomp575c
