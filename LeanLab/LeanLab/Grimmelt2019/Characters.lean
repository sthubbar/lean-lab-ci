/-
AI wrote this Lean code for CODEX task03.
Finite character orthogonality for condition 29 of P0074, page 12,
and the main term computation on pages 13 and 14.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.MainTerm
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace LeanLab.Grimmelt2019.MainTerm

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite weighted character inversion at a unit residue. -/
theorem character_inversion {q : ℕ} [NeZero q] (W : Finset ℤ) (ω : ℤ → ℝ)
    (a : ZMod q) (ha : IsUnit a) :
    (q.totient : ℂ) * ∑ m ∈ W.filter (fun m : ℤ => (m : ZMod q) = a), (ω m : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (if (m : ZMod q) = a then (q.totient : ℂ) * (ω m : ℂ) else 0) =
        (ω m : ℂ) * (if a = (m : ZMod q) then (q.totient : ℂ) else 0) := by
          by_cases h : (m : ZMod q) = a
          · simp [h, mul_comm]
          · simp [h, Ne.symm h]
    _ = (ω m : ℂ) * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (m : ZMod q) := by
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
    _ = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ((ω m : ℂ) * χ (m : ZMod q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring

/-- Uniform bounds for the character sums on one finite window. -/
def CharacterEquidist (W : Finset ℤ) (q : ℕ) (ω : ℤ → ℝ) (M E : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ q,
    ‖(∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q)) -
      (if χ = 1 then (M : ℂ) else 0)‖ ≤ E

/-- Character equidistribution implies residue equidistribution at every unit. -/
theorem residue_bound_of_characters {q : ℕ} [NeZero q] {W : Finset ℤ} {ω : ℤ → ℝ}
    {M E : ℝ} (hχ : CharacterEquidist W q ω M E) (a : ZMod q) (ha : IsUnit a) :
    |(∑ m ∈ W.filter (fun m : ℤ => (m : ZMod q) = a), ω m) - M / q.totient| ≤ E := by
  classical
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      χ a⁻¹ * (if χ = 1 then (M : ℂ) else 0)) = M := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hainv : IsUnit a⁻¹ := by
      rw [← ha.unit_spec, ZMod.inv_coe_unit]
      exact Units.isUnit _
    rw [MulChar.one_apply hainv, one_mul]
  have heq : (q.totient : ℂ) *
      ((∑ m ∈ W.filter (fun m : ℤ => (m : ZMod q) = a), (ω m : ℂ)) -
        (M : ℂ) / q.totient) =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        ((∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q)) -
          (if χ = 1 then (M : ℂ) else 0)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hmain, ← character_inversion W ω a ha]
    field_simp
  have hnorm : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        ((∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q)) -
          (if χ = 1 then (M : ℂ) else 0))‖ ≤ (q.totient : ℝ) * E := by
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ a⁻¹ *
          ((∑ m ∈ W, (ω m : ℂ) * χ (m : ZMod q)) -
            (if χ = 1 then (M : ℂ) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E := by
        apply Finset.sum_le_sum
        intro χ hmem
        rw [norm_mul]
        exact le_trans (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _))
          (by
            by_cases hc : χ = 1
            · simpa [hc] using hχ χ
            · simpa [hc] using hχ χ)
      _ = (q.totient : ℝ) * E := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [← heq, norm_mul] at hnorm
  have hcast :
      (∑ m ∈ W.filter (fun m : ℤ => (m : ZMod q) = a), (ω m : ℂ)) -
        (M : ℂ) / q.totient =
      (((∑ m ∈ W.filter (fun m : ℤ => (m : ZMod q) = a), ω m) -
        M / q.totient : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hφnorm : ‖(q.totient : ℂ)‖ = (q.totient : ℝ) := by simp
  rw [hφnorm] at hnorm
  exact (mul_le_mul_iff_right₀ hφ).mp hnorm

/-- The character form on the exact convolution window gives `APEquidist`.
The support condition is the consequence of Q-roughness used in this step. -/
theorem apEquidist_of_characters {X Y cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ} {n : ℤ}
    (hE : 0 ≤ E)
    (hχ : ∀ q ∈ Finset.Icc 1 Q, CharacterEquidist (Wn X Y n) q ω (cω * Y) E)
    (hrough : ∀ q ∈ Finset.Icc 1 Q, ∀ m ∈ Wn X Y n,
      Int.gcd m q ≠ 1 → ω m = 0) :
    APEquidist X Y Q ω cω E n := by
  classical
  intro q hq r hr
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  letI : NeZero q := ⟨by omega⟩
  have hr0 : 0 ≤ r := (Finset.mem_Ico.mp hr).1
  have hrq : r < q := (Finset.mem_Ico.mp hr).2
  have hfilter : (Wn X Y n).filter (fun m => m % (q : ℤ) = r) =
      (Wn X Y n).filter (fun m : ℤ => (m : ZMod q) = (r : ZMod q)) := by
    ext m
    simp only [Finset.mem_filter, ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hr0 hrq]
  by_cases hc : Int.gcd r q = 1
  · rw [if_pos hc, hfilter]
    apply residue_bound_of_characters (hχ q hq)
    rw [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]
    exact hc
  · rw [if_neg hc]
    have hz : ∑ m ∈ (Wn X Y n).filter (fun m => m % (q : ℤ) = r), ω m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      obtain ⟨hmW, hmr⟩ := Finset.mem_filter.mp hm
      apply hrough q hq m hmW
      rwa [← Int.gcd_emod, hmr]
    simpa [hz] using hE

/-- A Q-rough integer has no prime divisor at most Q. -/
def QRough (Q : ℕ) (m : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ m

/-- Roughness implies coprimality to every positive modulus at most Q. -/
theorem QRough.gcd_eq_one {Q : ℕ} {m : ℤ} (hm : QRough Q m)
    {q : ℕ} (hq0 : 0 < q) (hq : q ≤ Q) : Int.gcd m q = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpq : (p : ℤ) ∣ (q : ℤ) :=
    dvd_trans (by exact_mod_cast hpd) (Int.gcd_dvd_right m q)
  have hpqn : p ∣ q := by exact_mod_cast hpq
  have hpQ : p ≤ Q := le_trans (Nat.le_of_dvd hq0 hpqn) hq
  exact hm p hp hpQ (dvd_trans (by exact_mod_cast hpd) (Int.gcd_dvd_left m q))

/-- The support form of Q-roughness supplies the nonunit zero classes. -/
theorem apEquidist_of_characters_of_QRough {X Y cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ} {n : ℤ}
    (hE : 0 ≤ E)
    (hχ : ∀ q ∈ Finset.Icc 1 Q, CharacterEquidist (Wn X Y n) q ω (cω * Y) E)
    (hrough : ∀ m ∈ Wn X Y n, ω m ≠ 0 → QRough Q m) :
    APEquidist X Y Q ω cω E n := by
  apply apEquidist_of_characters hE hχ
  intro q hq m hm hbad
  by_contra hne
  have hqr := Finset.mem_Icc.mp hq
  exact hbad ((hrough m hm hne).gcd_eq_one (by omega) hqr.2)

#print axioms QRough.gcd_eq_one
#print axioms apEquidist_of_characters_of_QRough
#print axioms apEquidist_of_characters
#print axioms character_inversion
#print axioms residue_bound_of_characters

end LeanLab.Grimmelt2019.MainTerm
