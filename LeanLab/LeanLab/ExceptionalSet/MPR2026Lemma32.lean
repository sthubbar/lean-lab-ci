/-
Maynard-Pandey-Radziwiłł arXiv 2608.14777v1, Lemma 3.2 for every k ≥ 5. Unit U-1111,
PC run 20261019T2003Z-20508, I-0082.

Lemma 3.2: `0 ≤ η ≤ 1/100`, `a_1 ≥ … ≥ a_k ≥ 0`, `k ≥ 5`, `Σ a_i = 1`, `a_i + a_j ≥ 2/9 − η`
for `i ≠ j`. Then some subsum lies in `[5/12 − η, 7/12 + η]`, or there is a partition with
`5/12 ≥ Σ_{I1} ≥ Σ_{I2} ≥ 2 Σ_{I3} ≥ 1/3`.

Here the list is `a0 :: a1 :: a2 :: a3 :: a4 :: t`, sorted, every element of `t` at most `a4`.
For a sorted list the pairwise hypothesis is the last pair; the proof uses `a3 + a4 ≥ 2/9 − η`
and, when `t ≠ []`, `a4 + b ≥ 2/9 − η` for the head `b` of `t`, both implied by it. The
conclusion's partition is `{a0, a1}, {a2, a3}, {a4}` and occurs only for `k = 5`, as in the
paper. A subsum is the sum of a sublist.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.MPR2026

/-- Prefix sums cross a window of width `w` without jumping over it when every step is at most
`w`: if `s0 < L` and `s0 + Σ l > L + w`, some prefix lands in `[L, L + w]`. -/
theorem prefix_in_window (L w : ℝ) (hw : 0 ≤ w) :
    ∀ (l : List ℝ) (s0 : ℝ), (∀ x ∈ l, x ≤ w) → s0 < L → L + w < s0 + l.sum →
      ∃ n, L ≤ s0 + (l.take n).sum ∧ s0 + (l.take n).sum ≤ L + w := by
  intro l
  induction l with
  | nil => intro s0 _ h1 h2; simp at h2; linarith
  | cons x l ih =>
    intro s0 hl h1 h2
    have hx : x ≤ w := hl x (by simp)
    by_cases hc : L ≤ s0 + x
    · exact ⟨1, by simpa using hc, by simp; linarith⟩
    · push_neg at hc
      obtain ⟨n, hn1, hn2⟩ := ih (s0 + x) (fun y hy => hl y (by simp [hy])) hc
        (by simp [List.sum_cons] at h2; linarith)
      refine ⟨n + 1, ?_, ?_⟩ <;> simp [List.take_succ_cons, List.sum_cons] <;> linarith

/-- The window. -/
def Win (η s : ℝ) : Prop := 5 / 12 - η ≤ s ∧ s ≤ 7 / 12 + η

/-- **Lemma 3.2, every `k ≥ 5`.** -/
theorem lemma32 {a0 a1 a2 a3 a4 η : ℝ} {t : List ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 100)
    (h01 : a1 ≤ a0) (h12 : a2 ≤ a1) (h23 : a3 ≤ a2) (h34 : a4 ≤ a3)
    (ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ a4)
    (hsum : a0 + a1 + a2 + a3 + a4 + t.sum = 1)
    (hp5 : 2 / 9 - η ≤ a3 + a4) (hp6 : ∀ b ∈ t.head?, 2 / 9 - η ≤ a4 + b) :
    (∃ s : List ℝ, s.Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) ∧ Win η s.sum) ∨
    (t = [] ∧ a0 + a1 ≤ 5 / 12 ∧ a2 + a3 ≤ a0 + a1 ∧ 2 * a4 ≤ a2 + a3 ∧ 1 / 3 ≤ 2 * a4) := by
  have hT : 0 ≤ t.sum := List.sum_nonneg (fun x hx => (ht x hx).1)
  -- the head of t, if any, is at most the sum of t
  have hhead : ∀ b ∈ t.head?, b ≤ t.sum := by
    intro b hb
    cases t with
    | nil => simp at hb
    | cons c t' =>
      simp at hb; subst hb
      have : 0 ≤ t'.sum := List.sum_nonneg (fun x hx => (ht x (by simp [hx])).1)
      simp [List.sum_cons]; linarith
  have hw : (0 : ℝ) ≤ 1 / 6 + 2 * η := by linarith
  -- the sublists used
  have s1 : [a0].Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) :=
    List.Sublist.cons₂ a0 (List.nil_sublist _)
  have s2 : [a0, a1].Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) :=
    List.Sublist.cons₂ a0 (List.Sublist.cons₂ a1 (List.nil_sublist _))
  have s4 : [a0, a2].Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) :=
    List.Sublist.cons₂ a0 (List.Sublist.cons a1 (List.Sublist.cons₂ a2 (List.nil_sublist _)))
  have s5 : [a0, a4].Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) :=
    List.Sublist.cons₂ a0 (List.Sublist.cons a1 (List.Sublist.cons a2
      (List.Sublist.cons a3 (List.Sublist.cons₂ a4 (List.nil_sublist _)))))
  have s3 : [a0, a1, a2].Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) :=
    List.Sublist.cons₂ a0 (List.Sublist.cons₂ a1 (List.Sublist.cons₂ a2 (List.nil_sublist _)))
  have s7 : [a2, a3, a4].Sublist (a0 :: a1 :: a2 :: a3 :: a4 :: t) :=
    List.Sublist.cons a0 (List.Sublist.cons a1 (List.Sublist.cons₂ a2
      (List.Sublist.cons₂ a3 (List.Sublist.cons₂ a4 (List.nil_sublist _)))))
  by_cases w1 : Win η a0
  · exact Or.inl ⟨_, s1, by simpa using w1⟩
  by_cases w2 : Win η (a0 + a1)
  · exact Or.inl ⟨_, s2, by simpa using w2⟩
  by_cases w4 : Win η (a0 + a2)
  · exact Or.inl ⟨_, s4, by simpa using w4⟩
  by_cases w5 : Win η (a0 + a4)
  · exact Or.inl ⟨_, s5, by simpa using w5⟩
  unfold Win at w1 w2 w4 w5
  push_neg at w1 w2 w4 w5
  -- j = 0 impossible
  have f1 : a0 < 5 / 12 - η := by
    by_contra h; push_neg at h; have := w1 h; linarith
  -- j = 1 impossible
  have f2 : a0 + a1 < 5 / 12 - η := by
    by_contra h; push_neg at h
    have hbig := w2 h
    cases t with
    | cons b t' =>
      have hb := hp6 b (by simp)
      have hbs := hhead b (by simp)
      linarith
    | nil =>
      simp at hsum
      -- a0 + a2 above the window, a0 + a4 below it, then a3 + a4 is too small
      have g4 : 7 / 12 + η < a0 + a2 := by
        by_contra g; push_neg at g
        have := w4 (by linarith); linarith
      have g5 : a0 + a4 < 5 / 12 - η := by
        by_contra g; push_neg at g
        have := w5 g; linarith
      linarith
  -- j ≥ 3 lands in the window by prefix sums
  by_cases f3 : a0 + a1 + a2 < 5 / 12 - η
  · left
    have hsmall : ∀ x ∈ a3 :: a4 :: t, x ≤ 1 / 6 + 2 * η := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | hx
      · linarith
      · linarith
      · have := (ht x hx).2; linarith
    obtain ⟨n, hn1, hn2⟩ := prefix_in_window (5 / 12 - η) (1 / 6 + 2 * η) hw (a3 :: a4 :: t)
      (a0 + a1 + a2) hsmall f3 (by simp [List.sum_cons]; linarith)
    refine ⟨(a0 :: a1 :: a2 :: a3 :: a4 :: t).take (n + 3), List.take_sublist _ _, ?_⟩
    simp only [List.take_succ_cons, List.sum_cons]
    unfold Win; constructor <;> linarith
  push_neg at f3
  by_cases w3 : Win η (a0 + a1 + a2)
  · exact Or.inl ⟨_, s3, by simpa [add_assoc] using w3⟩
  unfold Win at w3; push_neg at w3
  have g3 : 7 / 12 + η < a0 + a1 + a2 := w3 f3
  -- the tail step m: a2 + a3 + a4
  by_cases w7 : Win η (a2 + a3 + a4)
  · exact Or.inl ⟨_, s7, by simpa [add_assoc] using w7⟩
  unfold Win at w7; push_neg at w7
  by_cases f7 : a2 + a3 + a4 < 5 / 12 - η
  · left
    have hsmall : ∀ x ∈ t, x ≤ 1 / 6 + 2 * η := by
      intro x hx; have := (ht x hx).2; linarith
    obtain ⟨n, hn1, hn2⟩ := prefix_in_window (5 / 12 - η) (1 / 6 + 2 * η) hw t
      (a2 + a3 + a4) hsmall f7 (by linarith)
    refine ⟨a2 :: a3 :: a4 :: t.take n,
      List.Sublist.cons a0 (List.Sublist.cons a1 (List.Sublist.cons₂ a2
        (List.Sublist.cons₂ a3 (List.Sublist.cons₂ a4 (List.take_sublist n t))))), ?_⟩
    simp only [List.sum_cons]
    unfold Win; constructor <;> linarith
  push_neg at f7
  have g7 : 7 / 12 + η < a2 + a3 + a4 := w7 f7
  -- k = 5 is forced, and the partition holds
  right
  cases t with
  | cons b t' =>
    exfalso
    have hb := hp6 b (by simp)
    have hbs := hhead b (by simp)
    linarith
  | nil =>
    simp at hsum
    refine ⟨rfl, by linarith, by linarith, by linarith, by linarith⟩

/-- Vacuity: the k = 5 instance `(41, 41, 41, 41, 36)/200`, `η = 0`, meets every hypothesis. -/
example : True := by
  have := lemma32 (a0 := 41 / 200) (a1 := 41 / 200) (a2 := 41 / 200) (a3 := 41 / 200)
    (a4 := 36 / 200) (η := 0) (t := []) le_rfl (by norm_num) le_rfl le_rfl le_rfl (by norm_num)
    (by simp) (by norm_num) (by norm_num) (by simp)
  trivial

end LeanLab.ExceptionalSet.MPR2026
