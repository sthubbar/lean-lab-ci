import LeanLab.ExceptionalSet.SPLIT_leaf_mean_square

/-!
Split of the sealed statement `leaf_window_energy_four_dvd` of
`LeanLab.ExceptionalSet.SPLIT_leaf_mean_square` into three sub-window steps, plus an assembly
`leaf_window_energy_four_dvd_split` whose statement is the sealed statement and whose proof uses
only those three leaves.

`leaf_window_energy_four_dvd` bounds the second moment of the weighted error `error n` over the
even indices divisible by `4` in the window `(Y/2, Y]`, by `C Y ^ (3/2 + 2 Θ + ε)`.  The window is
where the uniform arc estimate is used, once, at one scale, so the cut is taken along the range:
the window is split at `3Y/4` and `7Y/8` into three consecutive pieces.

The steps are:
* a bound on the piece `(Y/2, 3Y/4]`;
* a bound on the piece `(3Y/4, 7Y/8]`;
* a bound on the piece `(7Y/8, Y]`.

Each leaf sums over a strictly smaller index set than the sealed statement and carries its own
constant and its own threshold, so each is strictly weaker: the sealed statement returns each of
them at once with its own `C`, and no one of them returns the whole window.

The assembly recombines the three pieces by splitting the window twice, at `3Y/4` and at `7Y/8`,
adds the three constants and takes the largest of the three thresholds.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- LEAF 1 of 3, the first piece of the window: some nonnegative `C` bounds the second moment of
`error` over the even indices divisible by `4` in the range `(Y/2, 3Y/4]`, by
`C Y ^ (3/2 + 2 Θ + ε)`, for every `Y` past a fixed threshold.  This is a sum over a strict
subrange of the window of the sealed statement, so it is weaker than it. -/
theorem leaf_four_dvd_lower_window (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) (3 * Y / 4)).filter (fun n => Even n ∧ 4 ∣ n),
          (error n) ^ 2 ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF 2 of 3, the middle piece of the window: some nonnegative `C` bounds the second moment of
`error` over the even indices divisible by `4` in the range `(3Y/4, 7Y/8]`, by
`C Y ^ (3/2 + 2 Θ + ε)`, for every `Y` past a fixed threshold.  Again a sum over a strict
subrange of the window of the sealed statement. -/
theorem leaf_four_dvd_middle_window (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (3 * Y / 4 + 1) (7 * Y / 8)).filter (fun n => Even n ∧ 4 ∣ n),
          (error n) ^ 2 ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF 3 of 3, the last piece of the window: some nonnegative `C` bounds the second moment of
`error` over the even indices divisible by `4` in the range `(7Y/8, Y]`, by
`C Y ^ (3/2 + 2 Θ + ε)`, for every `Y` past a fixed threshold.  The top piece of the three, and
the only one that reaches the endpoint `Y`. -/
theorem leaf_four_dvd_upper_window (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (7 * Y / 8 + 1) Y).filter (fun n => Even n ∧ 4 ∣ n),
          (error n) ^ 2 ≤ C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Splitting an interval sum at an interior point: when `a ≤ c + 1` and `c ≤ b`, the terms of
`Icc a b` selected by `P` are the disjoint union of those of `Icc a c` and of `Icc (c + 1) b`. -/
private lemma sum_Icc_filter_split {f : ℕ → ℝ} {P : ℕ → Prop} [DecidablePred P] {a b c : ℕ}
    (h1 : a ≤ c + 1) (h2 : c ≤ b) :
    ∑ n ∈ (Finset.Icc a b).filter P, f n =
      ∑ n ∈ (Finset.Icc a c).filter P, f n
        + ∑ n ∈ (Finset.Icc (c + 1) b).filter P, f n := by
  have hunion : (Finset.Icc a b).filter P
      = (Finset.Icc a c).filter P ∪ (Finset.Icc (c + 1) b).filter P := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨⟨ha, hb⟩, hP⟩
      by_cases hnc : n ≤ c
      · exact Or.inl ⟨⟨ha, hnc⟩, hP⟩
      · exact Or.inr ⟨⟨by omega, hb⟩, hP⟩
    · rintro (⟨⟨ha, hc⟩, hP⟩ | ⟨⟨hc, hb⟩, hP⟩)
      · exact ⟨⟨ha, by omega⟩, hP⟩
      · exact ⟨⟨by omega, hb⟩, hP⟩
  have hdisj : Disjoint ((Finset.Icc a c).filter P) ((Finset.Icc (c + 1) b).filter P) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn hn'
    omega
  rw [hunion, Finset.sum_union hdisj]

/-- `leaf_window_energy_four_dvd` of `LeanLab.ExceptionalSet.SPLIT_leaf_mean_square`, assembled
from the three pieces of the window: split the range `(Y/2, Y]` at `3Y/4` and at `7Y/8`, apply the
matching leaf on each piece, and add the three constants. -/
theorem leaf_window_energy_four_dvd_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨C1, hC1, Y1, hY1, hlow⟩ :=
    leaf_four_dvd_lower_window Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, Y2, hY2, hmid⟩ :=
    leaf_four_dvd_middle_window Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C3, hC3, Y3, hY3, hup⟩ :=
    leaf_four_dvd_upper_window Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C1 + C2 + C3, by linarith, max (max Y1 Y2) Y3, ?_, ?_⟩
  · exact le_trans hY1 (le_trans (le_max_left Y1 Y2) (le_max_left (max Y1 Y2) Y3))
  · intro Y hY
    have hY1' : Y1 ≤ Y :=
      le_trans (le_trans (le_max_left Y1 Y2) (le_max_left (max Y1 Y2) Y3)) hY
    have hY2' : Y2 ≤ Y :=
      le_trans (le_trans (le_max_right Y1 Y2) (le_max_left (max Y1 Y2) Y3)) hY
    have hY3' : Y3 ≤ Y := le_trans (le_max_right (max Y1 Y2) Y3) hY
    have hsp1 := sum_Icc_filter_split (f := fun n => (error n) ^ 2)
      (P := fun n => Even n ∧ 4 ∣ n) (a := Y / 2 + 1) (c := 3 * Y / 4) (b := Y)
      (by omega) (by omega)
    have hsp2 := sum_Icc_filter_split (f := fun n => (error n) ^ 2)
      (P := fun n => Even n ∧ 4 ∣ n) (a := 3 * Y / 4 + 1) (c := 7 * Y / 8) (b := Y)
      (by omega) (by omega)
    rw [hsp1, hsp2]
    have hsum := add_le_add (hlow Y hY1') (add_le_add (hmid Y hY2') (hup Y hY3'))
    refine le_trans hsum (le_of_eq ?_)
    ring

-- Axiom audit drivers.
#print axioms leaf_window_energy_four_dvd_split

end LeanLab.ExceptionalSet.BG2026.Supply385
