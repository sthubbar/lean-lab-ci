/-
AI-written Lean code by OpenAI Codex for task113, 2026-10-26.
P0064, pages 27 and 28. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.Tchudakov1938.Decomp113

open scoped BigOperators
open Complex

/-- The reduced residue exponential sum on paper page 27.
Units give one representative of each reduced residue class. -/
noncomputable def residueSum (m : ℕ) (q : ℕ+) : ℂ :=
  ∑ a : (ZMod (q : ℕ))ˣ, ZMod.stdAddChar (-(m : ZMod (q : ℕ)) * (a : ZMod (q : ℕ)))

/-- The coefficient `A_m(q)` defined on paper page 27. -/
noncomputable def coefficient (m : ℕ) (q : ℕ+) : ℂ :=
  ((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 /
    (Nat.totient (q : ℕ) : ℂ) ^ 2) * residueSum m q

/-- CITED. P0064, Lemma 3, page 28. Multiplicativity of `A_m`. -/
def lemma3Statement : Prop :=
  ∀ (m : ℕ) (q r : ℕ+), Nat.Coprime (q : ℕ) (r : ℕ) →
    coefficient m (q * r) = coefficient m q * coefficient m r

/-- LEAF. P0064, Lemma 3 proof, page 28, first display.
Möbius and totient multiplicativity give multiplicativity of the weight. -/
theorem weight_mul (q r : ℕ+) (h : Nat.Coprime (q : ℕ) (r : ℕ)) :
    ((ArithmeticFunction.moebius ((q * r : ℕ+) : ℕ) : ℂ) ^ 2 /
      (Nat.totient ((q * r : ℕ+) : ℕ) : ℂ) ^ 2) =
    ((ArithmeticFunction.moebius (q : ℕ) : ℂ) ^ 2 /
      (Nat.totient (q : ℕ) : ℂ) ^ 2) *
    ((ArithmeticFunction.moebius (r : ℕ) : ℂ) ^ 2 /
      (Nat.totient (r : ℕ) : ℂ) ^ 2) := by
  change ((ArithmeticFunction.moebius ((q : ℕ) * (r : ℕ)) : ℂ) ^ 2 /
    (Nat.totient ((q : ℕ) * (r : ℕ)) : ℂ) ^ 2) = _
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h,
    Nat.totient_mul h]
  push_cast
  rw [mul_pow, mul_pow, mul_div_mul_comm]

/-- LEAF. P0064, page 28, the phase denominator identity.
Multiplying a numerator by r embeds a q phase into a qr phase. -/
theorem character_lift (q r : ℕ) [NeZero q] [NeZero r] (j : ℤ) :
    ZMod.stdAddChar (N := q * r) ((r : ZMod (q * r)) * j) =
      ZMod.stdAddChar (N := q) (j : ZMod q) := by
  rw [← Int.cast_natCast r, ← Int.cast_mul,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  field_simp

/-- LEAF. P0064, page 28, reduced residue system claim.
The pairs of reduced residues map bijectively to r a plus q b modulo qr. -/
theorem residueEquiv_exists (q r : ℕ) [NeZero q] [NeZero r]
    (h : Nat.Coprime q r) :
    ∃ e : (ZMod q)ˣ × (ZMod r)ˣ ≃ (ZMod (q * r))ˣ,
      ∀ a, (e a).val = (r * a.1.val.val + q * a.2.val.val : ℕ) := by
  let e₀ := (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    (MulEquiv.prodUnits : (ZMod q × ZMod r)ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ)
  let s := Equiv.prodCongr
    (Equiv.mulLeft (ZMod.unitOfCoprime r h.symm))
    (Equiv.mulLeft (ZMod.unitOfCoprime q h))
  let e := s.trans e₀.symm.toEquiv
  refine ⟨e, fun a => ?_⟩
  apply (ZMod.chineseRemainder h).injective
  have he : e₀ (e a) = s a := e₀.apply_symm_apply (s a)
  have hv := congrArg (fun b : (ZMod q)ˣ × (ZMod r)ˣ =>
    ((b.1 : ZMod q), (b.2 : ZMod r))) he
  change (ZMod.chineseRemainder h) (e a).val = _ at hv
  rw [hv, map_natCast]
  ext <;> simp [s, Equiv.mulLeft, ZMod.coe_unitOfCoprime]

/-- LEAF. P0064, Lemma 3 proof, page 28, last two displays.
The Chinese remainder reindexing factors the reduced residue sum. -/
theorem residueSum_mul (m : ℕ) (q r : ℕ+)
    (h : Nat.Coprime (q : ℕ) (r : ℕ)) :
    residueSum m (q * r) = residueSum m q * residueSum m r := by
  classical
  obtain ⟨e, he⟩ := residueEquiv_exists (q : ℕ) (r : ℕ) h
  unfold residueSum
  change (∑ a : (ZMod ((q : ℕ) * (r : ℕ)))ˣ,
    ZMod.stdAddChar (-(m : ZMod ((q : ℕ) * (r : ℕ))) * a.val)) = _
  rw [← e.sum_comp]
  simp only [he, Nat.cast_add, Nat.cast_mul, mul_add]
  simp_rw [show ∀ (a : (ZMod (q : ℕ))ˣ × (ZMod (r : ℕ))ˣ),
    -(m : ZMod ((q : ℕ) * (r : ℕ))) * ((r : ℕ) * a.1.val.val) =
      (r : ℕ) * ((-((m : ℤ) * a.1.val.val) : ℤ) : ZMod ((q : ℕ) * (r : ℕ)))
    from fun a => by push_cast; ring]
  simp_rw [show ∀ (a : (ZMod (q : ℕ))ˣ × (ZMod (r : ℕ))ˣ),
    -(m : ZMod ((q : ℕ) * (r : ℕ))) * ((q : ℕ) * a.2.val.val) =
      (q : ℕ) * ((-((m : ℤ) * a.2.val.val) : ℤ) : ZMod ((q : ℕ) * (r : ℕ)))
    from fun a => by push_cast; ring]
  have hchar₂ (j : ℤ) :
      ZMod.stdAddChar (N := (q : ℕ) * (r : ℕ)) ((q : ℕ) * j) =
        ZMod.stdAddChar (N := (r : ℕ)) (j : ZMod (r : ℕ)) := by
    rw [← Int.cast_natCast (q : ℕ), ← Int.cast_mul,
      ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
    have hr : (r : ℂ) ≠ 0 := by exact_mod_cast r.ne_zero
    field_simp
  simp_rw [AddChar.map_add_eq_mul, character_lift (q : ℕ) (r : ℕ), hchar₂]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul_sum, neg_mul]

/-- P0064, Lemma 3, page 28. Assembly from the two leaves.
This has exactly the cited proposition as its type. -/
theorem lemma3 : lemma3Statement := by
  intro m q r h
  unfold coefficient
  rw [weight_mul q r h, residueSum_mul m q r h]
  ring

end LeanLab.Tchudakov1938.Decomp113
