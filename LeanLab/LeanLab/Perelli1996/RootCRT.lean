/-
P0083, page 488. Multiplicativity of polynomial root counts.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Roots

namespace LeanLab.Perelli1996.Roots
open Finset Polynomial

/-- Polynomial root counts multiply over coprime positive moduli. -/
theorem root_count_mul (F : ℤ[X]) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    (rootResidues F (m * n)).card = (rootResidues F m).card * (rootResidues F n).card := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)⟩
  let ev (k : ℕ) (z : ZMod k) := F.eval₂ (Int.castRingHom (ZMod k)) z
  let e := ZMod.chineseRemainder hcop
  let f₁ : ZMod (m * n) →+* ZMod m := (RingHom.fst (ZMod m) (ZMod n)).comp e.toRingHom
  let f₂ : ZMod (m * n) →+* ZMod n := (RingHom.snd (ZMod m) (ZMod n)).comp e.toRingHom
  have he₁ (z : ZMod (m * n)) : (e (ev (m * n) z)).1 = ev m (e z).1 := by
    have h := F.hom_eval₂ (Int.castRingHom (ZMod (m * n))) f₁ z
    rw [RingHom.ext_int (f₁.comp (Int.castRingHom (ZMod (m * n))))
      (Int.castRingHom (ZMod m))] at h
    exact h
  have he₂ (z : ZMod (m * n)) : (e (ev (m * n) z)).2 = ev n (e z).2 := by
    have h := F.hom_eval₂ (Int.castRingHom (ZMod (m * n))) f₂ z
    rw [RingHom.ext_int (f₂.comp (Int.castRingHom (ZMod (m * n))))
      (Int.castRingHom (ZMod n))] at h
    exact h
  have he (z : ZMod (m * n)) : ev (m * n) z = 0 ↔ ev m (e z).1 = 0 ∧ ev n (e z).2 = 0 := by
    constructor
    · intro hz
      have hz' : e (ev (m * n) z) = 0 := by rw [hz, map_zero]
      constructor
      · have h := congrArg Prod.fst hz'
        change (e (ev (m * n) z)).1 = 0 at h
        rwa [he₁] at h
      · have h := congrArg Prod.snd hz'
        change (e (ev (m * n) z)).2 = 0 at h
        rwa [he₂] at h
    · rintro ⟨hz₁, hz₂⟩
      apply e.map_eq_zero_iff.mp
      apply Prod.ext
      · change (e (ev (m * n) z)).1 = 0
        rwa [he₁]
      · change (e (ev (m * n) z)).2 = 0
        rwa [he₂]
  let er : {z : ZMod (m * n) // ev (m * n) z = 0} ≃
      ({z : ZMod m // ev m z = 0} × {z : ZMod n // ev n z = 0}) :=
    (Equiv.subtypeEquiv (q := fun z : ZMod m × ZMod n => ev m z.1 = 0 ∧ ev n z.2 = 0)
      e.toEquiv he).trans (Equiv.subtypeProdEquivProd
        (p := fun z : ZMod m => ev m z = 0) (q := fun z : ZMod n => ev n z = 0))
  have hcard (k : ℕ) [NeZero k] :
      (rootResidues F k).card = Fintype.card {z : ZMod k // ev k z = 0} := by
    rw [card_rootResidues_eq_rho]
    unfold rho
    simp only [Polynomial.eval_map]
    exact (Fintype.card_subtype _).symm
  rw [hcard (m * n), hcard m, hcard n, Fintype.card_congr er, Fintype.card_prod]

end LeanLab.Perelli1996.Roots
