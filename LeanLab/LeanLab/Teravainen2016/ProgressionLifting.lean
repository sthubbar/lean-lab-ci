/-
P0076 Theorem 1.3, page 17, final paragraph of Section 4.
Modular progressions in the open middle third lift to integer progressions.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Definitions

open scoped Classical

namespace LeanLab.Teravainen2016

/-- A congruence between two sums in the middle third has no wraparound. -/
theorem middle_third_modEq_eq {N a b c : ℕ}
    (ha : N < 3 * a) (ha' : 3 * a < 2 * N)
    (hb : N < 3 * b) (hb' : 3 * b < 2 * N)
    (hc : N < 3 * c) (hc' : 3 * c < 2 * N)
    (h : (a : ZMod N) + c = 2 * b) : a + c = 2 * b := by
  have hmod : (a + c : ℤ) ≡ 2 * b [ZMOD (N : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    push_cast
    exact h
  obtain ⟨k, hk⟩ := hmod.dvd
  have ha0 : (N : ℤ) < 3 * a := by exact_mod_cast ha
  have ha1 : (3 : ℤ) * a < 2 * N := by exact_mod_cast ha'
  have hb0 : (N : ℤ) < 3 * b := by exact_mod_cast hb
  have hb1 : (3 : ℤ) * b < 2 * N := by exact_mod_cast hb'
  have hc0 : (N : ℤ) < 3 * c := by exact_mod_cast hc
  have hc1 : (3 : ℤ) * c < 2 * N := by exact_mod_cast hc'
  have hN : (0 : ℤ) < N := by omega
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : k ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ k := by omega
      nlinarith
  simp only [hk0, mul_zero] at hk
  exact_mod_cast (by linarith : (a : ℤ) + c = 2 * b)

/-- A distinct modular triple in the middle third gives a nontrivial natural progression. -/
theorem middle_third_progression {A : Set ℕ} {N a b c : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (ha0 : N < 3 * a) (ha1 : 3 * a < 2 * N)
    (hb0 : N < 3 * b) (hb1 : 3 * b < 2 * N)
    (hc0 : N < 3 * c) (hc1 : 3 * c < 2 * N)
    (hab : a ≠ b) (h : (a : ZMod N) + c = 2 * b) :
    ∃ x d : ℕ, 0 < d ∧ x ∈ A ∧ x + d ∈ A ∧ x + 2 * d ∈ A ∧ N < 3 * x := by
  have he := middle_third_modEq_eq ha0 ha1 hb0 hb1 hc0 hc1 h
  rcases lt_or_gt_of_ne hab with hab | hab
  · refine ⟨a, b - a, by omega, ha, ?_, ?_, ha0⟩
    · convert hb using 1 <;> omega
    · convert hc using 1 <;> omega
  · refine ⟨c, b - c, by omega, hc, ?_, ?_, hc0⟩
    · convert hb using 1 <;> omega
    · convert ha using 1 <;> omega

/-- Progressions in middle thirds at unbounded scales give infinitely many progressions. -/
theorem infinitelyMany3AP_of_middle_thirds {A : Set ℕ}
    (h : ∀ X : ℕ, ∃ N a b c : ℕ, X ≤ N ∧
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧
      N < 3 * a ∧ 3 * a < 2 * N ∧
      N < 3 * b ∧ 3 * b < 2 * N ∧
      N < 3 * c ∧ 3 * c < 2 * N ∧
      a ≠ b ∧ (a : ZMod N) + c = 2 * b) : InfinitelyMany3AP A := by
  let T : Set (ℕ × ℕ) := {t | 0 < t.2 ∧ t.1 ∈ A ∧
    t.1 + t.2 ∈ A ∧ t.1 + 2 * t.2 ∈ A}
  have himg : (Prod.fst '' T).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro X
    obtain ⟨N, a, b, c, hN, ha, hb, hc, ha0, ha1, hb0, hb1, hc0, hc1, hab, he⟩ := h (3 * X)
    obtain ⟨x, d, hd, hx, hxd, hx2d, hNx⟩ :=
      middle_third_progression ha hb hc ha0 ha1 hb0 hb1 hc0 hc1 hab he
    exact ⟨x, ⟨(x, d), ⟨hd, hx, hxd, hx2d⟩, rfl⟩, by omega⟩
  exact Set.Infinite.of_image Prod.fst himg

example : ∃ x d : ℕ, 0 < d ∧ x ∈ (Set.univ : Set ℕ) ∧
    x + d ∈ (Set.univ : Set ℕ) ∧ x + 2 * d ∈ (Set.univ : Set ℕ) ∧ 12 < 3 * x := by
  exact middle_third_progression (N := 12) (a := 5) (b := 6) (c := 7)
    (by trivial) (by trivial) (by trivial) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

#print axioms middle_third_modEq_eq
#print axioms middle_third_progression
#print axioms infinitelyMany3AP_of_middle_thirds

end LeanLab.Teravainen2016
