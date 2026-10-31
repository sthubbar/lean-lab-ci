/-
P0069, page 11, the well spaced sets used in Lemma 1.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Statements

namespace LeanLab.BakerHarmanPintz1997
open Finset
attribute [local instance] Classical.propDecidable

/-- Pack each character's ordinates into distinct unit intervals. -/
theorem wellSpaced_card_le (c : Cfg) (hT : 0 ≤ c.T) (hq : 0 < c.q) (h : c.WellSpaced) :
    c.S.card ≤ Nat.totient c.q * (⌊2 * c.T⌋₊ + 1) := by
  letI : NeZero c.q := ⟨by omega⟩
  let encode : (ℝ × DirichletCharacter ℂ c.q) → (DirichletCharacter ℂ c.q × ℕ) :=
    fun e => (e.2, ⌊e.1 + c.T⌋₊)
  have hinj : Set.InjOn encode c.S := by
    intro e he f hf heq
    have hχ : e.2 = f.2 := congrArg Prod.fst heq
    have hfloor : ⌊e.1 + c.T⌋₊ = ⌊f.1 + c.T⌋₊ := congrArg Prod.snd heq
    have heT := (abs_le.mp (h e he).1)
    have hfT := (abs_le.mp (h f hf).1)
    have helo : (⌊e.1 + c.T⌋₊ : ℝ) ≤ e.1 + c.T := Nat.floor_le (by linarith)
    have hflo : (⌊f.1 + c.T⌋₊ : ℝ) ≤ f.1 + c.T := Nat.floor_le (by linarith)
    have hehi := Nat.lt_floor_add_one (e.1 + c.T)
    have hfhi := Nat.lt_floor_add_one (f.1 + c.T)
    by_contra hne
    have hsep := (h e he).2 f hf hχ hne
    rw [hfloor] at helo hehi
    have hclose : |e.1 - f.1| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have hsub : c.S.image encode ⊆
      (univ : Finset (DirichletCharacter ℂ c.q)) ×ˢ range (⌊2 * c.T⌋₊ + 1) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    simp only [mem_product, mem_univ, true_and, mem_range]
    have hbound : ⌊f.1 + c.T⌋₊ ≤ ⌊2 * c.T⌋₊ :=
      Nat.floor_mono (by have := (abs_le.mp (h f hf).1).2; linarith)
    exact Nat.lt_succ_of_le hbound
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj, card_product, card_univ, card_range] at hcard
  have hchars : Fintype.card (DirichletCharacter ℂ c.q) = Nat.totient c.q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ c.q
  rwa [hchars] at hcard

/-- The elementary packing bound has size at most q times 2T + 1. -/
theorem wellSpaced_card_le_real (c : Cfg) (hT : 0 ≤ c.T) (hq : 0 < c.q) (h : c.WellSpaced) :
    (c.S.card : ℝ) ≤ (c.q : ℝ) * (2 * c.T + 1) := by
  have hcard : (c.S.card : ℝ) ≤ (Nat.totient c.q : ℝ) * (⌊2 * c.T⌋₊ + 1) := by
    exact_mod_cast wellSpaced_card_le c hT hq h
  have hphi : (Nat.totient c.q : ℝ) ≤ c.q := by exact_mod_cast Nat.totient_le c.q
  have hfloor : (⌊2 * c.T⌋₊ : ℝ) ≤ 2 * c.T := Nat.floor_le (by positivity)
  refine hcard.trans ?_
  exact mul_le_mul hphi (by linarith) (by positivity) (by positivity)

#print axioms wellSpaced_card_le
#print axioms wellSpaced_card_le_real
end LeanLab.BakerHarmanPintz1997
