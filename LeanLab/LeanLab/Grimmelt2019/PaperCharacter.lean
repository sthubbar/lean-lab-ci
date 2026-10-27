/-
AI wrote this Lean code for CODEX task03.
P0074, page 12, condition 29, and page 13, the main term character sums.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Windows

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The paper support interval for omega. -/
noncomputable def omegaRange (X Y : ℝ) : Finset ℤ :=
  Finset.Ioc ⌊X - 3 * Y⌋ ⌊X - Y⌋

theorem mem_omegaRange (X Y : ℝ) (m : ℤ) :
    m ∈ omegaRange X Y ↔ X - 3 * Y < (m : ℝ) ∧ (m : ℝ) ≤ X - Y := by
  simp only [omegaRange, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

/-- The paper support lies inside the common finite support at the relevant scales. -/
theorem omegaRange_subset_supp {X Y : ℝ} (hY : 0 ≤ Y) (hX : 1 ≤ X - 3 * Y) :
    omegaRange X Y ⊆ Prop21.supp X := by
  intro m hm
  obtain ⟨hl, hr⟩ := (mem_omegaRange X Y m).mp hm
  rw [Prop21.supp, Finset.mem_Icc]
  constructor
  · exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  · exact Int.le_floor.mpr (by linarith)

/-- Every convolution window lies inside the paper support when H is less than Y. -/
theorem Wn_subset_omegaRange {X Y H : ℝ} {n : ℤ} (hH : H < Y)
    (hn : n ∈ Prop21.win X H) : Wn X Y n ⊆ omegaRange X Y := by
  intro m hm
  obtain ⟨hmS, hl, hr⟩ := Finset.mem_filter.mp hm
  have hn' : X - H ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
    simpa only [Prop21.win, Finset.mem_Icc, Int.ceil_le, Int.le_floor] using hn
  rw [mem_omegaRange]
  constructor <;> linarith

/-- Filtering an intermediate support gives exactly the convolution window. -/
theorem Wn_eq_support_filter {X Y : ℝ} {n : ℤ} (S : Finset ℤ)
    (hS : S ⊆ Prop21.supp X) (hW : Wn X Y n ⊆ S) :
    Wn X Y n = S.filter (fun m => ⌈(n : ℝ) - 2 * Y⌉ ≤ m ∧ m < ⌈(n : ℝ) - Y⌉) := by
  ext m
  simp only [Finset.mem_filter, Int.ceil_le, Int.lt_ceil]
  constructor
  · intro hm
    exact ⟨hW hm, (Finset.mem_filter.mp hm).2⟩
  · rintro ⟨hm, hl, hr⟩
    exact Finset.mem_filter.mpr ⟨hS hm, hl, hr⟩

/-- The exact paper prefixes imply the character estimate on the convolution window.
The error includes both prefix errors and the integer endpoint error. -/
theorem character_window_of_prefix {X Y cω E : ℝ} {n : ℤ} {q : ℕ} {ω : ℤ → ℝ} (S : Finset ℤ)
    (hY : 0 ≤ Y) (hleft : 1 ≤ (n : ℝ) - 2 * Y) (hright : (n : ℝ) - Y ≤ X)
    (hS : S ⊆ Prop21.supp X) (hW : Wn X Y n ⊆ S)
    (hprefix : PrefixCharacterBound S q ω cω E) :
    CharacterEquidist (Wn X Y n) q ω (cω * Y) (2 * E + |cω|) := by
  have hab : ⌈(n : ℝ) - 2 * Y⌉ ≤ ⌈(n : ℝ) - Y⌉ := Int.ceil_le_ceil (by linarith)
  have h := character_interval_bound hprefix _ _ hab
  rw [← Wn_eq_support_filter S hS hW] at h
  apply h.change_center
  · rw [← mul_sub, abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left (Wn_card_error hY hleft hright) (abs_nonneg cω))
      (by simp)
  · exact abs_nonneg _

/-- Condition 29 and Q-rough support imply APEquidist at every convolution window. -/
theorem apEquidist_of_condition29 {X Y H cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ}
    (hY : 0 ≤ Y) (hX : 1 ≤ X - 3 * Y) (hH : H < Y) (hE : 0 ≤ E)
    (hprefix : ∀ q ∈ Finset.Icc 1 Q, PrefixCharacterBound (omegaRange X Y) q ω cω E)
    (hrough : ∀ m ∈ omegaRange X Y, ω m ≠ 0 → QRough Q m) :
    ∀ n ∈ Prop21.win X H, APEquidist X Y Q ω cω (2 * E + |cω|) n := by
  intro n hn
  have hn' : X - H ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
    simpa only [Prop21.win, Finset.mem_Icc, Int.ceil_le, Int.le_floor] using hn
  have hleft : 1 ≤ (n : ℝ) - 2 * Y := by linarith
  have hright : (n : ℝ) - Y ≤ X := by linarith
  have hW := Wn_subset_omegaRange hH hn
  apply apEquidist_of_characters_of_QRough (by positivity)
  · intro q hq
    exact character_window_of_prefix (omegaRange X Y) hY hleft hright
      (omegaRange_subset_supp hY hX) hW (hprefix q hq)
  · intro m hm hne
    exact hrough m (hW hm) hne

/-- Condition 29 with its real cutoff restricted to t at most X. -/
def PaperCondition29 (X Y : ℝ) (q : ℕ) (ω : ℤ → ℝ) (cω E : ℝ) : Prop :=
  ∀ t : ℝ, t ≤ X → ∀ χ : DirichletCharacter ℂ q,
    ‖∑ m ∈ (omegaRange X Y).filter (fun m : ℤ => (m : ℝ) ≤ t),
      ((ω m : ℂ) * χ (m : ZMod q) - if χ = 1 then (cω : ℂ) else 0)‖ ≤ E

/-- Clamping the integer cutoff to X gives every prefix needed by the finite bridge. -/
theorem prefix_of_paperCondition29 {X Y cω E : ℝ} {q : ℕ} {ω : ℤ → ℝ}
    (hY : 0 ≤ Y) (h : PaperCondition29 X Y q ω cω E) :
    PrefixCharacterBound (omegaRange X Y) q ω cω E := by
  intro t χ
  have hs : ∀ m ∈ omegaRange X Y, (m : ℝ) ≤ X := by
    intro m hm
    have := ((mem_omegaRange X Y m).mp hm).2
    linarith
  have hfilter : (omegaRange X Y).filter (fun m : ℤ => (m : ℝ) ≤ min (t : ℝ) X) =
      (omegaRange X Y).filter (fun m => m ≤ t) := by
    ext m
    simp only [Finset.mem_filter, le_min_iff]
    constructor
    · rintro ⟨hm, ht, hx⟩
      exact ⟨hm, by exact_mod_cast ht⟩
    · rintro ⟨hm, ht⟩
      exact ⟨hm, by exact_mod_cast ht, hs m hm⟩
  have hbound := h (min (t : ℝ) X) (min_le_right _ _) χ
  rw [hfilter] at hbound
  exact hbound

/-- The paper's character condition and rough support give the existing residue estimate. -/
theorem apEquidist_of_paperCondition29 {X Y H cω E : ℝ} {Q : ℕ} {ω : ℤ → ℝ}
    (hY : 0 ≤ Y) (hX : 1 ≤ X - 3 * Y) (hH : H < Y) (hE : 0 ≤ E)
    (h29 : ∀ q ∈ Finset.Icc 1 Q, PaperCondition29 X Y q ω cω E)
    (hrough : ∀ m ∈ omegaRange X Y, ω m ≠ 0 → QRough Q m) :
    ∀ n ∈ Prop21.win X H, APEquidist X Y Q ω cω (2 * E + |cω|) n :=
  apEquidist_of_condition29 hY hX hH hE
    (fun q hq => prefix_of_paperCondition29 hY (h29 q hq)) hrough

#print axioms prefix_of_paperCondition29
#print axioms apEquidist_of_paperCondition29
#print axioms mem_omegaRange
#print axioms omegaRange_subset_supp
#print axioms Wn_subset_omegaRange
#print axioms Wn_eq_support_filter
#print axioms character_window_of_prefix
#print axioms apEquidist_of_condition29
end LeanLab.Grimmelt2019.MainTerm
