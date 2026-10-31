/-
I-0031. Alsetri Theorem 1.2 for the class 2 mod 3, by negation, and the cited
`alsetri_1_2` restated without sorry. When 3 ∣ m, a ↦ −a swaps the classes 1 and 2 mod 3 and
fixes the class 0, so the local theorem for primes ≡ 2 mod 3 follows from the one for ≡ 1.
Local, finite statements only; the global density analogue of Theorem 1.1 for primes ≡ 2 mod 3
is not touched. Ternary Goldbach is a theorem; binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.Alsetri2025
import LeanLab.DensityGoldbach.AlsetriFull

open Finset

namespace LeanLab.DensityGoldbach

/-- `alsetri_1_2` with the proof from `alsetri12_proved`: P0085 Theorem 1.2, zero sorry. -/
theorem alsetri_1_2_proved (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (h3 : 3 ∣ m) : Alsetri12 m := alsetri12_proved m hodd hsq h3

/-- `a.val % 3` is the class of `a` in `ZMod 3` when `3 ∣ m`. -/
lemma val_mod_three {m : ℕ} [NeZero m] (h3 : 3 ∣ m) (a : ZMod m) :
    a.val % 3 = (ZMod.castHom h3 (ZMod 3) a).val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

lemma neg_val_mod_three {m : ℕ} [NeZero m] (h3 : 3 ∣ m) (a : ZMod m) :
    (-a).val % 3 = (-(ZMod.castHom h3 (ZMod 3) a)).val := by
  rw [val_mod_three h3, map_neg]

/-- Theorem 1.2 for the class `2 mod 3`. -/
def Alsetri12Two (m : ℕ) [NeZero m] : Prop := ∀ f : ZMod m → ℝ,
  (∀ a, 0 ≤ f a ∧ f a ≤ 1) → (∀ a, a.val % 3 ≠ 2 → f a = 0) →
  (m.totient : ℝ) / 4 < ∑ a ∈ unitsMod m, f a → AlsetriConcl m f

theorem alsetri12Two_of {m : ℕ} [NeZero m] (h3 : 3 ∣ m) (H : Alsetri12 m) :
    Alsetri12Two m := by
  intro f hf hsupp hsum x hx
  set g : ZMod m → ℝ := fun a => f (-a) with hg
  have hgf : ∀ a, 0 ≤ g a ∧ g a ≤ 1 := fun a => hf (-a)
  have hgs : ∀ a : ZMod m, a.val % 3 ≠ 1 → g a = 0 := by
    intro a ha
    apply hsupp
    rw [neg_val_mod_three h3]
    rw [val_mod_three h3] at ha
    exact (by decide : ∀ b : ZMod 3, b.val ≠ 1 → (-b).val ≠ 2) _ ha
  have hsumg : ∑ a ∈ unitsMod m, g a = ∑ a ∈ unitsMod m, f a := by
    apply Finset.sum_nbij' (fun a => -a) (fun a => -a)
    · intro a ha; simp only [unitsMod, mem_filter, mem_univ, true_and] at ha ⊢; exact ha.neg
    · intro a ha; simp only [unitsMod, mem_filter, mem_univ, true_and] at ha ⊢; exact ha.neg
    · intro a _; simp
    · intro a _; simp
    · intro a _; simp [hg]
  have hx' : (-x).val % 3 = 0 := by
    rw [neg_val_mod_three h3]; rw [val_mod_three h3] at hx
    exact (by decide : ∀ b : ZMod 3, b.val = 0 → (-b).val = 0) _ hx
  obtain ⟨a₁, h1, a₂, h2, a₃, h3', he, p1, p2, p3, hs⟩ :=
    H g hgf hgs (by rw [hsumg]; exact hsum) (-x) hx'
  have hu : ∀ a ∈ unitsMod m, -a ∈ unitsMod m := by
    intro a ha; simp only [unitsMod, mem_filter, mem_univ, true_and] at ha ⊢; exact ha.neg
  refine ⟨-a₁, hu _ h1, -a₂, hu _ h2, -a₃, hu _ h3', ?_, p1, p2, p3, hs⟩
  rw [show x = -(-x) by simp, he]; ring

/-- Alsetri Theorem 1.2 for the class `2 mod 3`, every odd squarefree `m` with `3 ∣ m`. -/
theorem alsetri12Two_proved (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (h3 : 3 ∣ m) : Alsetri12Two m :=
  alsetri12Two_of h3 (alsetri12_proved m hodd hsq h3)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.alsetri12Two_proved
#print axioms LeanLab.DensityGoldbach.alsetri_1_2_proved
