import LeanLab.ExceptionalSet.Decomp371c

/-!
The even and odd coefficient separation at P0082 page 362, Lemma 7.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Adjacent446

open Real Finset
open LeanLab.ExceptionalSet.U1539 (nu nuOdd)

/-- The even one of the two integers next to F of n.
Source: P0082 page 354 and page 362 before Lemma 6. -/
noncomputable def evenAdjacent (γ : ℝ) (n : ℕ) : ℤ :=
  if Even (nu γ n) then nu γ n else nu γ n + 1

/-- P0082 page 362, first sentence of the Lemma 7 proof.
The even and odd coefficients sum to the two adjacent coefficients. -/
theorem adjacent_sum (f : ℤ → ℂ) (γ : ℝ) (n : ℕ) :
    f (evenAdjacent γ n) + f (nuOdd γ n) = f (nu γ n) + f (nu γ n + 1) := by
  by_cases he : Even (nu γ n)
  · have ho : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr he
    simp [evenAdjacent, nuOdd, he, ho]
  · have ho : Odd (nu γ n) := Int.not_even_iff_odd.mp he
    simp [evenAdjacent, nuOdd, he, ho, add_comm]

/-- P0082 page 362, first sentence of the Lemma 7 proof.
A small real part of the sum forces a small first real part or a large
second norm. The finite union bound is explicit. -/
theorem bad_pair_count {ι : Type*} (s : Finset ι) (f g : ι → ℂ) (T : ℝ) :
    (s.filter (fun n => (f n + g n).re < T)).card ≤
      (s.filter (fun n => (f n).re < 2 * T)).card +
        (s.filter (fun n => T < ‖g n‖)).card := by
  classical
  have hsub : s.filter (fun n => (f n + g n).re < T) ⊆
      s.filter (fun n => (f n).re < 2 * T) ∪ s.filter (fun n => T < ‖g n‖) := by
    intro n hn
    simp only [mem_filter, mem_union] at hn ⊢
    by_cases hf : (f n).re < 2 * T
    · exact Or.inl ⟨hn.1, hf⟩
    · right
      refine ⟨hn.1, ?_⟩
      have hr := (abs_le.mp (Complex.abs_re_le_norm (g n))).1
      simp only [Complex.add_re] at hn
      by_contra hg
      have hff := le_of_not_gt hf
      have hgg := le_of_not_gt hg
      linarith
  exact (card_le_card hsub).trans (card_union_le _ _)

end LeanLab.ExceptionalSet.Adjacent446
