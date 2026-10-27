/-
Maynard-Pandey-Radziwiłł arXiv 2608.14777v1: the repair of F-0052 item 4 that Maksym Radziwiłł
sent on 2026-10-20, REPLIES.md line 37. Unit U-1150, PC run 20261020T0303Z-988, I-0082.

Item 4 was: Lemma 3.6 quotes Chen-Gupta-Li Theorem 1.1 without its length hypothesis
`N ≥ (qT)^{2/3}`; at the corner `M1 = M2 = x^{5/12}`, `M3 = x^{1/6}`, `qT = x^{1/2}` of the
Lemma 3.7 region the length `M3² = x^{1/3}` meets it only with equality, so any `x^{o(1)}` loss
breaks it.

The repair, as the author states it: Lemma 3.2 with `1/3 + 2η` in place of `1/3`; the hypothesis
`N ≥ (qT)^{2/3}` and primitivity in Lemma 3.6; `M1, M2, M3² ≥ (qT)^{2/3}` in Lemma 3.7; `η` with
`x^{1/3+2η} ≫ (qT)^{2/3}` in Lemma 3.9.

PROVED here, log_x units as in MPR2026Exponents.lean:
* `lemma32_eta`: Lemma 3.2 for every k ≥ 5 with the repaired partition `2 Σ_{I3} ≥ 1/3 + 2η`,
  and `lemma32_eta_sharp`, the same with `1/3 + 4η`, strict.
* `corner_tight`: the unrepaired region contains a point where `2 m3 = 2Q/3` exactly.
* `lengths_ok`: on the repaired region every length `m1, m2, 2 m3` is at least `2Q/3 + 2η`.
* `region_of_eta`: the repaired region sits inside the old one, so all eight cases of
  Lemma 3.7 in MPR2026Exponents.lean hold on it unchanged.
* `lemma39_margin`: `1/3 + 2η > 2Q/3` for every `η > 0` and `Q ≤ 1/2`.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.MPR2026Exponents
import LeanLab.ExceptionalSet.MPR2026Lemma32

namespace LeanLab.ExceptionalSet.MPR2026

/-- **Repaired Lemma 3.2, every `k ≥ 5`**: the partition branch now has `2 Σ_{I3} ≥ 1/3 + 2η`. -/
theorem lemma32_eta {a0 a1 a2 a3 a4 η : ℝ} {t : List ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 100)
    (h01 : a1 ≤ a0) (h12 : a2 ≤ a1) (h23 : a3 ≤ a2) (h34 : a4 ≤ a3)
    (ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ a4)
    (hsum : a0 + a1 + a2 + a3 + a4 + t.sum = 1)
    (hp5 : 2 / 9 - η ≤ a3 + a4) (hp6 : ∀ b ∈ t.head?, 2 / 9 - η ≤ a4 + b) :
    (∃ s : List ℝ, s.Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) ∧ Win η s.sum) ∨
    (t = [] ∧ a0 + a1 ≤ 5 / 12 ∧ a2 + a3 ≤ a0 + a1 ∧ 2 * a4 ≤ a2 + a3 ∧
      1 / 3 + 4 * η < 2 * a4) := by
  rcases lemma32 hη0 hη h01 h12 h23 h34 ht hsum hp5 hp6 with h | ⟨rfl, h1, h2, h3, _⟩
  · exact Or.inl h
  by_cases w2 : Win η (a0 + a1)
  · left
    exact ⟨[a0, a1], List.Sublist.cons₂ a0 (List.Sublist.cons₂ a1 (List.nil_sublist _)),
      by simpa using w2⟩
  right
  have f2 : a0 + a1 < 5 / 12 - η := by
    unfold Win at w2; push_neg at w2
    by_contra h; push_neg at h; have := w2 h; linarith
  simp at hsum
  refine ⟨rfl, h1, h2, h3, ?_⟩
  linarith

/-- The author's form, `1/3 + 2η ≤ 2 Σ_{I3}`. -/
theorem lemma32_eta_sharp {a0 a1 a2 a3 a4 η : ℝ} {t : List ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 100)
    (h01 : a1 ≤ a0) (h12 : a2 ≤ a1) (h23 : a3 ≤ a2) (h34 : a4 ≤ a3)
    (ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ a4)
    (hsum : a0 + a1 + a2 + a3 + a4 + t.sum = 1)
    (hp5 : 2 / 9 - η ≤ a3 + a4) (hp6 : ∀ b ∈ t.head?, 2 / 9 - η ≤ a4 + b) :
    (∃ s : List ℝ, s.Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) ∧ Win η s.sum) ∨
    (t = [] ∧ a0 + a1 ≤ 5 / 12 ∧ a2 + a3 ≤ a0 + a1 ∧ 2 * a4 ≤ a2 + a3 ∧
      1 / 3 + 2 * η ≤ 2 * a4) := by
  rcases lemma32_eta hη0 hη h01 h12 h23 h34 ht hsum hp5 hp6 with h | ⟨h0, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨h0, h1, h2, h3, by linarith⟩

/-- The repaired Lemma 3.7 region: `1/3 + 2η ≤ 2 m3`. -/
structure RegionEta (η m1 m2 m3 Q : ℝ) : Prop where
  hη : 0 ≤ η
  h1 : m1 ≤ 5 / 12
  h2 : m2 ≤ m1
  h3 : 2 * m3 ≤ m2
  h4 : 1 / 3 + 2 * η ≤ 2 * m3
  hsum : m1 + m2 + m3 = 1
  hQ1 : 5 / 12 < Q
  hQ2 : Q ≤ 1 / 2

/-- The repaired region lies inside the old one, so every Lemma 3.7 case applies. -/
theorem region_of_eta {η m1 m2 m3 Q : ℝ} (R : RegionEta η m1 m2 m3 Q) : Region m1 m2 m3 Q :=
  ⟨R.h1, R.h2, R.h3, by linarith [R.h4, R.hη], R.hsum, R.hQ1, R.hQ2⟩

/-- Item 4, the gap: in the old region the corner `(5/12, 5/12, 1/6)`, `Q = 1/2` has
`2 m3 = 2Q/3` exactly, so `M3² ≥ (qT)^{2/3}` holds there with no room for an `x^{o(1)}` loss. -/
theorem corner_tight : Region (5 / 12) (5 / 12) (1 / 6) (1 / 2) ∧
    2 * (1 / 6 : ℝ) = 2 / 3 * (1 / 2) := by
  refine ⟨⟨by norm_num, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl⟩,
    by norm_num⟩

/-- Item 4, the repair: on the repaired region each length `M1, M2, M3²` is at least
`(qT)^{2/3} x^{2η}`. -/
theorem lengths_ok {η m1 m2 m3 Q : ℝ} (R : RegionEta η m1 m2 m3 Q) :
    2 / 3 * Q + 2 * η ≤ 2 * m3 ∧ 2 / 3 * Q + 2 * η ≤ m2 ∧ 2 / 3 * Q + 2 * η ≤ m1 := by
  have := R.h2; have := R.h3; have := R.h4; have := R.hQ2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Lemma 3.9's choice of `η`: any `η > 0` gives `x^{1/3 + 2η} ≥ x^{η} (qT)^{2/3}`. -/
theorem lemma39_margin {η Q : ℝ} (hη : 0 < η) (hQ : Q ≤ 1 / 2) :
    2 / 3 * Q + η < 1 / 3 + 2 * η := by linarith

/-- Vacuity: the repaired region is nonempty for `η = 1/100`. -/
theorem regionEta_nonempty :
    RegionEta (1 / 100) (2 / 5) (2 / 5) (1 / 5) (1 / 2) :=
  ⟨by norm_num, by norm_num, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, le_rfl⟩

/-- Vacuity for `lemma32_eta`: `(41, 41, 41, 41, 36)/200`, `η = 0`. -/
example : True := by
  have := lemma32_eta (a0 := 41 / 200) (a1 := 41 / 200) (a2 := 41 / 200) (a3 := 41 / 200)
    (a4 := 36 / 200) (η := 0) (t := []) le_rfl (by norm_num) le_rfl le_rfl le_rfl (by norm_num)
    (by simp) (by norm_num) (by norm_num) (by simp)
  trivial

end LeanLab.ExceptionalSet.MPR2026
