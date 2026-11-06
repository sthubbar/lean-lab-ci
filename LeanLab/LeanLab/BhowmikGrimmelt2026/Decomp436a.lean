/-
Supply for the coefficient majorant in Decomp247a.
Source: Pintz Part I page 20 display 7.13.
The residue fiber proof is Montgomery Vaughan 1975 pages 359 and 360.
Existing statements remain sealed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp247a
import LeanLab.BhowmikGrimmelt2026.TotientRatio247

namespace LeanLab.BhowmikGrimmelt2026

/-- The integer frequency twisted sum is a shifted standard Gauss sum.
Source: Montgomery Vaughan page 359 display 5.3, before grouping residue fibers. -/
theorem cChi_int_gauss436 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℤ) :
    cChi χ N = gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)) := by
  unfold cChi gaussSum
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [AddChar.mulShift_apply]
  have he : (N : ZMod q) * a = ((N * (a.val : ℤ) : ℤ) : ZMod q) := by simp
  rw [he, ZMod.stdAddChar_coe]
  unfold ee
  congr 1
  push_cast
  ring

/-- LEAF. Montgomery Vaughan 1975 page 359, Case 1 after display 5.3.
Pintz Part I page 11 Lemma 4.4 gives the same vanishing alternative.
Residue fiber cancellation when the primitive conductor does not divide q1.
This concerns one finite character sum and no coefficient denominator or series. -/
theorem twisted_fiber_vanish436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hbad : ¬ r ∣ q / Nat.gcd q N.natAbs) :
    cChi (DirichletCharacter.changeLevel hd χ) N = 0 := by
  by_contra hn
  rw [cChi_int_gauss436] at hn
  let d := q / Nat.gcd q N.natAbs
  have hdq : d ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q N.natAbs)
  have hmul : q ∣ N.natAbs * d := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right q N.natAbs
    refine ⟨k, ?_⟩
    calc
      N.natAbs * d = (Nat.gcd q N.natAbs * k) * d := by conv_lhs => rw [hk]
      _ = (d * Nat.gcd q N.natAbs) * k := by ring
      _ = q * k := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left q N.natAbs)]
  have hmulInt : (q : ℤ) ∣ N * (d : ℤ) := Int.natCast_dvd.mpr (by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hmul)
  have hz : (N : ZMod q) * (d : ZMod q) = 0 := by
    rw [← Int.cast_natCast d, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmulInt
  have hp : ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)).mulShift (d : ZMod q) = 1 := by
    ext a
    simp only [AddChar.mulShift_apply, ← mul_assoc, hz, zero_mul, AddChar.map_zero_eq_one,
      AddChar.one_apply]
  have hf := factorsThrough_of_gaussSum_ne_zero
    ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)) hdq hp hn
  have hc := DirichletCharacter.conductor_dvd_of_mem_conductorSet
    (DirichletCharacter.changeLevel hd χ) hf
  rw [DirichletCharacter.conductor_changeLevel, hχ] at hc
  exact hbad hc

/-- LEAF. Montgomery Vaughan 1975 pages 359 and 360, Case 2 and display 5.1.
Pintz Part I page 11 display 4.3 and page 20 display 7.13.
OPEN norm consequence of the residue fiber formula and the primitive Gauss norm.
Only the nonvanishing conductor alternative is required.
The totient quotient and one primitive conductor remain explicit. -/
theorem twisted_fiber_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hgood : r ∣ q / Nat.gcd q N.natAbs) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (Nat.totient q : ℝ) / (Nat.totient (q / Nat.gcd q N.natAbs) : ℝ) *
        Real.sqrt r := by
  sorry

/-- The positive frequency bound follows by the two residue fiber alternatives.
Source: Pintz page 20 display 7.13 and the totient quotient in display 4.3.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem twisted_primitive_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hd : r ∣ q)
    (N : ℤ) (hN : 1 ≤ N) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (N.natAbs : ℝ) * Real.sqrt r := by
  by_cases hgood : r ∣ q / Nat.gcd q N.natAbs
  · exact (twisted_fiber_bound436 χ hχ hd N hgood).trans
      (mul_le_mul_of_nonneg_right (totient_gcd_ratio247 q N.natAbs
        (Nat.pos_of_ne_zero (NeZero.ne q))
        (Int.natAbs_pos.mpr (by omega))) (Real.sqrt_nonneg _))
  · rw [twisted_fiber_vanish436 χ hχ hd N hgood, norm_zero]
    positivity

/-- Passing to the primitive character gives the same bound at any fixed source level.
Source: the primitive inducing character in Pintz page 11 Lemma 4.4.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem twisted_lift_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) (N : ℤ) (hN : 1 ≤ N) :
    ‖cChi (DirichletCharacter.changeLevel hd χ) N‖ ≤
      (N.natAbs : ℝ) * Real.sqrt r := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := twisted_primitive_bound436 χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
    (χ.conductor_dvd_level.trans hd) N hN
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level hd,
    DirichletCharacter.changeLevel_primitiveCharacter] at h
  have hcr : (χ.conductor : ℝ) ≤ r := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne r)) χ.conductor_dvd_level
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcr) (by positivity))

/-- A conjugate Gauss sum is the inverse character twisted sum at frequency one.
Source: Pintz page 11 displays 4.1 and 4.2, with the local conjugation convention. -/
theorem tauConj_eq_cChi_inv436 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = cChi χ⁻¹ 1 := by
  unfold tauConj cChi
  apply Finset.sum_congr rfl
  intro a ha
  rw [show (starRingEnd ℂ) (χ a) = star (χ a) from rfl, MulChar.star_apply']
  simp

/-- The lifted conjugate Gauss norm is bounded by the square root of its source level.
Source: Pintz page 11 Lemmas 4.1 to 4.4, frequency one specialization.
CONDITIONAL ON twisted_fiber_bound436. -/
theorem tau_lift_bound436 {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hd : r ∣ q) :
    ‖tauConj (DirichletCharacter.changeLevel hd χ)‖ ≤ Real.sqrt r := by
  rw [tauConj_eq_cChi_inv436, ← map_inv]
  simpa using twisted_lift_bound436 χ⁻¹ hd 1 (by norm_num)

/-- Lifting the product at the least common multiple agrees with multiplying the two lifts.
Source: Pintz page 20 display 7.13, the primitive character inducing the product. -/
theorem lifted_product436 {r₁ r₂ q : ℕ}
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (h₁ : r₁ ∣ q) (h₂ : r₂ ∣ q) :
    DirichletCharacter.changeLevel (Nat.lcm_dvd h₁ h₂) (χ₁.mul χ₂) =
      DirichletCharacter.changeLevel h₁ χ₁ * DirichletCharacter.changeLevel h₂ χ₂ := by
  rw [DirichletCharacter.mul, map_mul, ← DirichletCharacter.changeLevel_trans,
    ← DirichletCharacter.changeLevel_trans]

/-- Exact aqZero247_totient_bound statement assembled from the smaller residue fiber leaves.
CONDITIONAL ON twisted_fiber_bound436.
Source: Pintz page 20 display 7.13. No original coefficient leaf is used. -/
theorem aqZero247_totient_supply436 {r₁ r₂ : ℕ} [NeZero r₁] [NeZero r₂]
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (N : ℤ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 0 < q →
      ‖aqZero247 χ₁ χ₂ N q‖ ≤ C * (1 / (Nat.totient q : ℝ) ^ 2) := by
  refine ⟨Real.sqrt r₁ * Real.sqrt r₂ * ((N.natAbs : ℝ) * Real.sqrt (Nat.lcm r₁ r₂)),
    by positivity, ?_⟩
  intro q hq
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (Nat.lcm r₁ r₂) := ⟨Nat.lcm_ne_zero (NeZero.ne r₁) (NeZero.ne r₂)⟩
  by_cases hd : r₁ ∣ q ∧ r₂ ∣ q
  · have h₁ := tau_lift_bound436 χ₁ hd.1
    have h₂ := tau_lift_bound436 χ₂ hd.2
    have h₃ := twisted_lift_bound436 (χ₁.mul χ₂) (Nat.lcm_dvd hd.1 hd.2) N hN
    rw [lifted_product436 χ₁ χ₂ hd.1 hd.2] at h₃
    have hn := mul_le_mul h₁ h₂ (norm_nonneg _) (Real.sqrt_nonneg _)
    have hn' := mul_le_mul hn h₃ (norm_nonneg _) (by positivity)
    simp only [aqZero247, dif_neg (Nat.ne_of_gt hq), Aq, dif_pos hd, norm_div, norm_mul,
      norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (Real.sqrt r₁ * Real.sqrt r₂ * ((N.natAbs : ℝ) * Real.sqrt (Nat.lcm r₁ r₂))) /
          (Nat.totient q : ℝ) ^ 2 := div_le_div_of_nonneg_right hn' (by positivity)
      _ = _ := by ring
  · simp [aqZero247, Nat.ne_of_gt hq, Aq, hd]
    positivity

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.cChi_int_gauss436
#print axioms LeanLab.BhowmikGrimmelt2026.twisted_fiber_vanish436
#print axioms LeanLab.BhowmikGrimmelt2026.twisted_fiber_bound436
#print axioms LeanLab.BhowmikGrimmelt2026.twisted_primitive_bound436
#print axioms LeanLab.BhowmikGrimmelt2026.twisted_lift_bound436
#print axioms LeanLab.BhowmikGrimmelt2026.tauConj_eq_cChi_inv436
#print axioms LeanLab.BhowmikGrimmelt2026.tau_lift_bound436
#print axioms LeanLab.BhowmikGrimmelt2026.lifted_product436
#print axioms LeanLab.BhowmikGrimmelt2026.aqZero247_totient_supply436
