/-
P0076 Lemma 5.4, pages 19 to 20. Chinese remainder factorization of local Fourier sums.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.PeriodicCharacter

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- A nontrivial additive character summed off a forbidden set costs its cardinality. -/
theorem addChar_complement_bound {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (ψ : AddChar A ℂ) (hψ : ψ ≠ 0) (T : Finset A) :
    ‖∑ x ∈ Tᶜ, ψ x‖ ≤ (T.card : ℝ) := by
  have hsum : ∑ x, ψ x = 0 := by simp [AddChar.sum_eq_ite, hψ]
  have hs := sum_add_sum_compl T (fun x => ψ x)
  rw [hsum] at hs
  have he : ∑ x ∈ Tᶜ, ψ x = -(∑ x ∈ T, ψ x) := by linear_combination hs
  rw [he, norm_neg]
  calc
    _ ≤ ∑ x ∈ T, ‖ψ x‖ := norm_sum_le _ _
    _ = _ := by simp [ψ.norm_apply]

/-- A weighted Fourier sum factors under the Chinese remainder equivalence. -/
theorem crt_weighted_sum_factor {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ZMod (m * n)) (F : ZMod m → ℂ) (G : ZMod n → ℂ) :
    let E := ZMod.chineseRemainder h
    (∑ x : ZMod (m * n), F (E x).1 * G (E x).2 * ZMod.stdAddChar (a * x)) =
      (∑ u : ZMod m, F u * ZMod.stdAddChar (a * E.symm (u, 0))) *
      (∑ v : ZMod n, G v * ZMod.stdAddChar (a * E.symm (0, v))) := by
  dsimp only
  let E := ZMod.chineseRemainder h
  change (∑ x : ZMod (m * n), F (E x).1 * G (E x).2 * ZMod.stdAddChar (a * x)) = _
  calc
    _ = ∑ y : ZMod m × ZMod n, F y.1 * G y.2 * ZMod.stdAddChar (a * E.symm y) := by
      apply Fintype.sum_equiv E.toEquiv
      intro x
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type, sum_mul_sum]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      have he : E.symm (u, v) = E.symm (u, 0) + E.symm (0, v) := by
        rw [← map_add]
        simp
      rw [he, mul_add, AddChar.map_add_eq_mul]
      ring

/-- Unit frequency gives a nontrivial character on each nontrivial CRT factor. -/
theorem crt_component_chars_nontrivial {m n : ℕ} [NeZero m] [NeZero n]
    (hm : 1 < m) (hn : 1 < n) (h : m.Coprime n)
    (a : ZMod (m * n)) (ha : IsUnit a) :
    let E := ZMod.chineseRemainder h
    let ψ := (ZMod.stdAddChar.mulShift a).compAddMonoidHom E.symm.toAddMonoidHom
    ψ.compAddMonoidHom (AddMonoidHom.inl (ZMod m) (ZMod n)) ≠ 0 ∧
      ψ.compAddMonoidHom (AddMonoidHom.inr (ZMod m) (ZMod n)) ≠ 0 := by
  dsimp only
  let E := ZMod.chineseRemainder h
  constructor
  · intro hz
    have hone : ZMod.stdAddChar (a * E.symm (1, 0)) = 1 := by
      have hv := congrArg (fun f : AddChar (ZMod m) ℂ => f 1) hz
      simpa using hv
    have he0 : a * E.symm (1, 0) = 0 :=
      ZMod.injective_stdAddChar (by simpa using hone)
    have hE0 : E.symm (1, 0) = 0 := ha.mul_right_injective (by simpa using he0)
    have hc : (1 : ZMod m) = 0 := by
      have he := congrArg E hE0
      simpa using congrArg Prod.fst he
    have hd : m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 m).mp (by simpa using hc)
    exact (by omega : m ≠ 1) (Nat.dvd_one.mp hd)
  · intro hz
    have hone : ZMod.stdAddChar (a * E.symm (0, 1)) = 1 := by
      have hv := congrArg (fun f : AddChar (ZMod n) ℂ => f 1) hz
      simpa using hv
    have he0 : a * E.symm (0, 1) = 0 :=
      ZMod.injective_stdAddChar (by simpa using hone)
    have hE0 : E.symm (0, 1) = 0 := ha.mul_right_injective (by simpa using he0)
    have hc : (1 : ZMod n) = 0 := by
      have he := congrArg E hE0
      simpa using congrArg Prod.snd he
    have hd : n ∣ 1 := (ZMod.natCast_eq_zero_iff 1 n).mp (by simpa using hc)
    exact (by omega : n ≠ 1) (Nat.dvd_one.mp hd)

/-- Excluding rectangular forbidden sets costs the product of their cardinalities. -/
theorem crt_sifted_character_bound {m n : ℕ} [NeZero m] [NeZero n]
    (hm : 1 < m) (hn : 1 < n) (h : m.Coprime n)
    (a : ZMod (m * n)) (ha : IsUnit a) (T : Finset (ZMod m)) (U : Finset (ZMod n)) :
    let E := ZMod.chineseRemainder h
    ‖∑ x ∈ (univ : Finset (ZMod (m * n))).filter (fun x => (E x).1 ∉ T ∧ (E x).2 ∉ U),
      ZMod.stdAddChar (a * x)‖ ≤ (T.card : ℝ) * U.card := by
  dsimp only
  let E := ZMod.chineseRemainder h
  let ψ := (ZMod.stdAddChar.mulShift a).compAddMonoidHom E.symm.toAddMonoidHom
  let ψm := ψ.compAddMonoidHom (AddMonoidHom.inl (ZMod m) (ZMod n))
  let ψn := ψ.compAddMonoidHom (AddMonoidHom.inr (ZMod m) (ZMod n))
  have hne := crt_component_chars_nontrivial hm hn h a ha
  have hbm := addChar_complement_bound ψm hne.1 T
  have hbn := addChar_complement_bound ψn hne.2 U
  have hfac := crt_weighted_sum_factor h a
    (fun u => if u ∉ T then (1 : ℂ) else 0) (fun v => if v ∉ U then (1 : ℂ) else 0)
  have he : (∑ x ∈ (univ : Finset (ZMod (m * n))).filter
      (fun x => (E x).1 ∉ T ∧ (E x).2 ∉ U), ZMod.stdAddChar (a * x)) =
      (∑ u ∈ Tᶜ, ψm u) * ∑ v ∈ Uᶜ, ψn v := by
    have hT : Tᶜ = (univ : Finset (ZMod m)).filter (fun u => u ∉ T) := by ext u; simp
    have hU : Uᶜ = (univ : Finset (ZMod n)).filter (fun v => v ∉ U) := by ext v; simp
    convert hfac using 1
    · simp only [sum_filter, ite_mul, mul_ite, one_mul, zero_mul]
      apply sum_congr rfl
      intro x _
      split_ifs <;> simp_all [E]
    · rw [hT, hU]
      simp only [sum_filter, ψm, ψn, ψ, E, AddChar.compAddMonoidHom_apply,
        AddChar.mulShift_apply, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
        ite_mul, one_mul, zero_mul]
      rfl
  rw [he, norm_mul]
  exact mul_le_mul hbm hbn (norm_nonneg _) (by positivity)

example : ‖∑ x ∈ (univ : Finset (ZMod 15)).filter (fun x =>
    ((ZMod.chineseRemainder (by decide : Nat.Coprime 3 5)) x).1 ∉ ({0} : Finset (ZMod 3)) ∧
    ((ZMod.chineseRemainder (by decide : Nat.Coprime 3 5)) x).2 ∉ ({0, 1} : Finset (ZMod 5))),
    ZMod.stdAddChar ((1 : ZMod 15) * x)‖ ≤ 2 := by
  have hc : ({0, 1} : Finset (ZMod 5)).card = 2 := by decide
  simpa only [card_singleton, hc, Nat.cast_one, one_mul, Nat.cast_ofNat] using crt_sifted_character_bound (by decide : 1 < 3) (by decide : 1 < 5)
    (by decide : Nat.Coprime 3 5) 1 isUnit_one ({0} : Finset (ZMod 3)) ({0, 1} : Finset (ZMod 5))

#print axioms addChar_complement_bound
#print axioms crt_weighted_sum_factor
#print axioms crt_component_chars_nontrivial
#print axioms crt_sifted_character_bound

end LeanLab.Teravainen2016
