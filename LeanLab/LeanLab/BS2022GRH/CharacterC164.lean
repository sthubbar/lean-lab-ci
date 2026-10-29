/- AI wrote the Lean code for CODEX task164.
Elementary character algebra for journal Lemma 8 p. 1223.
Goldbach is open. -/
import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
namespace LeanLab.BS2022GRH.CharacterC164
open Real Finset Classical
/-- Exact nonprincipal character expansion of a reduced residue indicator. -/
theorem indicator (d b x : ℕ) (hd : 0 < d) (hb : Nat.Coprime b d) :
    (if x % d = b % d then (1 : ℂ) else 0) -
      (d.totient : ℂ)⁻¹ * (if Nat.Coprime x d then 1 else 0) =
      (d.totient : ℂ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
          χ (b : ZMod d)⁻¹ * χ (x : ZMod d) := by
  letI charFintype : Fintype (DirichletCharacter ℂ d) := inferInstance
  letI : NeZero d := ⟨by omega⟩
  classical
  letI : DecidableEq (DirichletCharacter ℂ d) := Classical.decEq _
  have hu : IsUnit (b : ZMod d) := (ZMod.isUnit_iff_coprime b d).mpr hb
  have ht : (d.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hd).ne'
  have hall := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (x : ZMod d)
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (DirichletCharacter ℂ d))
    (fun χ => χ ≠ 1) (fun χ => χ (b : ZMod d)⁻¹ * χ (x : ZMod d))
  have hb1 : (1 : DirichletCharacter ℂ d) (b : ZMod d)⁻¹ = 1 := by
    obtain ⟨v, hv⟩ := hu
    rw [← hv, ZMod.inv_coe_unit]
    exact MulChar.one_apply_coe _
  have hx1 : (1 : DirichletCharacter ℂ d) (x : ZMod d) =
      if Nat.Coprime x d then 1 else 0 := by
    by_cases hx : Nat.Coprime x d
    · simp [hx, MulChar.one_apply ((ZMod.isUnit_iff_coprime x d).mpr hx)]
    · have hnu : ¬ IsUnit (x : ZMod d) := by rwa [ZMod.isUnit_iff_coprime]
      simpa only [hx, ite_false] using (1 : DirichletCharacter ℂ d).map_nonunit hnu
  simp only [not_not] at hsplit
  have hsone : (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ = 1) = {1} := by
    ext χ; simp
  rw [hsone, Finset.sum_singleton, hb1, one_mul, hx1] at hsplit
  have heq : ((b : ZMod d) = (x : ZMod d)) ↔ x % d = b % d := by
    rw [ZMod.natCast_eq_natCast_iff']
    exact eq_comm
  simp only [heq] at hall
  rw [hall] at hsplit
  have hs := eq_sub_of_add_eq hsplit
  have hs' : (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
      χ (b : ZMod d)⁻¹ * χ (x : ZMod d)) =
      (if x % d = b % d then (d.totient : ℂ) else 0) - (if Nat.Coprime x d then 1 else 0) := by
    convert hs using 1
  rw [hs']
  by_cases hxb : x % d = b % d <;> by_cases hxc : Nat.Coprime x d <;>
    simp [hxb, hxc, ht, mul_sub]
/-- Sum the residue indicator over two independent finite index sets. -/
theorem expansion (s t : Finset ℕ) (c : ℕ → ℂ) (d b : ℕ)
    (hd : 0 < d) (hb : Nat.Coprime b d) :
    (∑ n ∈ s, ∑ p ∈ t.filter (fun p => (n * p) % d = b % d), c n) -
      (d.totient : ℂ)⁻¹ *
        (∑ n ∈ s, ∑ p ∈ t.filter (fun p => Nat.Coprime (n * p) d), c n) =
      (d.totient : ℂ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
          χ (b : ZMod d)⁻¹ * (∑ n ∈ s, c n * χ n) * (∑ p ∈ t, χ p) := by
  classical
  letI : DecidableEq (DirichletCharacter ℂ d) := Classical.decEq _
  let F := (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1)
  calc
    _ = ∑ n ∈ s, ∑ p ∈ t, c n *
        ((if (n * p) % d = b % d then (1 : ℂ) else 0) -
          (d.totient : ℂ)⁻¹ * (if Nat.Coprime (n * p) d then 1 else 0)) := by
      simp only [Finset.sum_filter, mul_sub, mul_ite, mul_one, mul_zero,
        Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      ext p
      split_ifs <;> ring
    _ = ∑ n ∈ s, ∑ p ∈ t, c n * ((d.totient : ℂ)⁻¹ *
        ∑ χ ∈ F, χ (b : ZMod d)⁻¹ * χ (n * p : ℕ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro p hp
      rw [indicator d b (n * p) hd hb]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := t) (t := F)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      simp_rw [Nat.cast_mul, map_mul, Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro p hp
      ring
/-- Triangle inequality for the finite nonprincipal character expansion. -/
theorem error_norm_le (s t : Finset ℕ) (c : ℕ → ℂ) (d b : ℕ)
    (hd : 0 < d) (hb : Nat.Coprime b d) :
    ‖(∑ n ∈ s, ∑ p ∈ t.filter (fun p => (n * p) % d = b % d), c n) -
      (d.totient : ℂ)⁻¹ *
        (∑ n ∈ s, ∑ p ∈ t.filter (fun p => Nat.Coprime (n * p) d), c n)‖ ≤
      (d.totient : ℝ)⁻¹ *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ ≠ 1),
          ‖∑ n ∈ s, c n * χ n‖ * ‖∑ p ∈ t, χ p‖ := by
  classical
  letI : DecidableEq (DirichletCharacter ℂ d) := Classical.decEq _
  rw [expansion s t c d b hd hb, norm_mul]
  simp only [norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro χ hχ
  rw [norm_mul, norm_mul]
  calc ‖χ (b : ZMod d)⁻¹‖ * ‖∑ n ∈ s, c n * χ n‖ * ‖∑ p ∈ t, χ p‖
      ≤ 1 * ‖∑ n ∈ s, c n * χ n‖ * ‖∑ p ∈ t, χ p‖ := by
        gcongr
        exact χ.norm_le_one _
    _ = _ := by ring
end LeanLab.BS2022GRH.CharacterC164
#print axioms LeanLab.BS2022GRH.CharacterC164.indicator
#print axioms LeanLab.BS2022GRH.CharacterC164.expansion
#print axioms LeanLab.BS2022GRH.CharacterC164.error_norm_le
