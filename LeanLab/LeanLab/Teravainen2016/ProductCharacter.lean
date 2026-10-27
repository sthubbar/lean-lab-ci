/-
P0076 Lemma 5.4, pages 19 to 20. Finite product Fourier sums and primitive local factors.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.CRTCharacter

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Translation orthogonality for an arbitrary additive character. -/
theorem weighted_addChar_sum_eq_zero {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ : AddChar A ℂ) (t : A) (ht : ψ t ≠ 1) (w : A → ℂ)
    (hw : ∀ x, w (x + t) = w x) : ∑ x, w x * ψ x = 0 := by
  have hs : (∑ x, w x * ψ x) * ψ t = ∑ x, w x * ψ x := by
    calc
      _ = ∑ x, w (x + t) * ψ (x + t) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro x _
        rw [hw, AddChar.map_add_eq_mul]
        ring
      _ = _ := Equiv.sum_comp (Equiv.addRight t) (fun x => w x * ψ x)
  have hz : (∑ x, w x * ψ x) * (ψ t - 1) = 0 := by linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr ht)

/-- Every injective cyclic character annihilates a weight lifted from a proper divisor. -/
theorem lifted_weight_addChar_sum_eq_zero {N d : ℕ} [NeZero N]
    (hd0 : 0 < d) (hdN : d < N) (hd : d ∣ N)
    (ψ : AddChar (ZMod N) ℂ) (hψ : Function.Injective ψ) (w : ZMod d → ℂ) :
    ∑ x : ZMod N, w (ZMod.castHom hd (ZMod d) x) * ψ x = 0 := by
  have ht : (d : ZMod N) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd0 hdN
  have hchar : ψ (d : ZMod N) ≠ 1 := by
    intro he
    exact ht (hψ (by simpa using he))
  apply weighted_addChar_sum_eq_zero ψ d hchar (fun x => w (ZMod.castHom hd (ZMod d) x))
  intro x
  simp only [map_add, map_natCast, ZMod.natCast_self, add_zero]

/-- A weighted character on a finite product factors into its coordinate sums. -/
theorem pi_weighted_character_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Fintype (A i)]
    (ψ : AddChar (∀ i, A i) ℂ) (F : ∀ i, A i → ℂ) :
    (∑ x : ∀ i, A i, (∏ i, F i (x i)) * ψ x) =
      ∏ i, ∑ z : A i, F i z * ψ (Pi.single i z) := by
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x _
  have hsum : (∑ i, Pi.single i (x i)) = x := by
    ext i
    simp only [Finset.sum_apply, Fintype.sum_pi_single]
  have hmap : ∀ s : Finset ι, ψ (∑ i ∈ s, Pi.single i (x i)) =
      ∏ i ∈ s, ψ (Pi.single i (x i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [sum_insert hi, prod_insert hi, AddChar.map_add_eq_mul, ih]
  rw [prod_mul_distrib, ← hmap univ, hsum]

/-- Bounds for all coordinate sums multiply to bound the product character sum. -/
theorem pi_weighted_character_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Fintype (A i)]
    (ψ : AddChar (∀ i, A i) ℂ) (F : ∀ i, A i → ℂ) (B : ι → ℝ)
    (hB : ∀ i, ‖∑ z : A i, F i z * ψ (Pi.single i z)‖ ≤ B i) :
    ‖∑ x : ∀ i, A i, (∏ i, F i (x i)) * ψ x‖ ≤ ∏ i, B i := by
  rw [pi_weighted_character_factor, norm_prod]
  gcongr with i hi
  exact hB i

/-- The primitive cyclic character stays injective on every CRT coordinate. -/
theorem crt_pi_coordinate_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] [NeZero (∏ i, m i)] (h : Pairwise (fun i j => (m i).Coprime (m j)))
    (a : ZMod (∏ i, m i)) (ha : IsUnit a) (i : ι) :
    Function.Injective (fun z : ZMod (m i) =>
      ZMod.stdAddChar (a * (ZMod.prodEquivPi m h).symm (Pi.single i z))) := by
  intro z w he
  have h1 := ZMod.injective_stdAddChar he
  have h2 := ha.mul_right_injective h1
  have h3 := (ZMod.prodEquivPi m h).symm.injective h2
  have h4 := congrFun h3 i
  simpa using h4

example : ∑ x : ZMod 4, (1 : ℂ) * ZMod.stdAddChar x = 0 := by
  apply weighted_addChar_sum_eq_zero ZMod.stdAddChar (2 : ZMod 4) _ _ (fun _ => rfl)
  intro he
  have h0 : (2 : ZMod 4) = 0 := ZMod.injective_stdAddChar (by simpa using he)
  exact (by decide : (2 : ZMod 4) ≠ 0) h0

#print axioms weighted_addChar_sum_eq_zero
#print axioms lifted_weight_addChar_sum_eq_zero
#print axioms pi_weighted_character_factor
#print axioms pi_weighted_character_bound
#print axioms crt_pi_coordinate_injective

end LeanLab.Teravainen2016
