import LeanLab.ExceptionalSet.SPLIT_leaf_mean_square

/-!
Split of the sealed statement `leaf_window_energy_four_not_dvd` of
`LeanLab.ExceptionalSet.SPLIT_leaf_mean_square` into three strictly smaller steps, plus an
assembly `leaf_window_energy_four_not_dvd_split` whose statement is the sealed statement and whose
proof uses only those three leaves.

The sealed statement bounds the second moment of `error` over one window `(Y/2, Y]`, restricted to
the even indices that are not divisible by `4`, that is to the indices `n ≡ 2 (mod 4)`, by
`C Y ^ (3/2 + 2 Θ + ε)`.  Such an `n` is `2 m` for exactly one odd `m`, and the window `(Y/2, Y]`
in `n` becomes the half window `(Y/4, Y/2]` in `m`.  The first leaf is that reindexing, an exact
identity.

Inside that set of indices the singular series still has two shapes, according to whether the
prime `3` divides the index or not.  The second and the third leaf keep those two shapes apart: each bounds
the second moment over one of them at the halved scale.  Each of the two index sets is a subset of
the index set of the sealed statement, so each leaf is strictly weaker than it.

The assembly reindexes, splits the odd `m` by `3 ∣ m`, applies the two index-set leaves at the common
threshold `max Y₀ Y₀'`, and adds the constants, using `(Y/2) ^ p ≤ Y ^ p` for the positive
exponent `p = 3/2 + 2 Θ + ε`.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- Splitting a filtered sum by one further predicate: the part on which `q` holds plus the part on
which it fails. -/
private lemma sum_filter_split_one {f : ℕ → ℝ} {s : Finset ℕ} (p q : ℕ → Prop)
    [DecidablePred p] [DecidablePred q] :
    ∑ n ∈ s.filter p, f n =
      ∑ n ∈ s.filter (fun n => p n ∧ q n), f n +
        ∑ n ∈ s.filter (fun n => p n ∧ ¬ q n), f n := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : p n <;> by_cases h2 : q n <;> simp [h1, h2]

/-- LEAF 1 of 3, the reindexing of the index set: an index `n` with `n ≡ 2 (mod 4)` is `2 m` for
exactly one odd `m`, and the window `(Y/2, Y]` in `n` becomes the half window `(Y/4, Y/2]` in `m`.
So the second moment over those indices in the window equals the second moment over the odd `m` in the
half window, at the argument `2 m`.  This is an identity between two finite sums, not an estimate;
it holds also at `Y = 0`, where both sides are the empty sum. -/
theorem leaf_window_two_mod_four_reindex (Y : ℕ) :
    ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 =
      ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter Odd, (error (2 * m)) ^ 2 := by
  sorry

/-- LEAF 2 of 3, the shape with `3 ∣ n`: at the halved scale, the second moment over the odd
`m` in `(Y/4, Y/2]` that are divisible by `3` is at most `C (Y/2) ^ (3/2 + 2 Θ + ε)`.  This is one
of the two shapes of the singular series inside the index set of the sealed statement, and its
index set is a subset of that set, so it is strictly weaker than the sealed statement. -/
theorem leaf_odd_half_window_three_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ 3 ∣ m),
          (error (2 * m)) ^ 2 ≤
        C * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF 3 of 3, the other shape, with `3 ∤ n`: the same second moment at the halved scale,
now over the odd `m` in `(Y/4, Y/2]` that are not divisible by `3`.  Together with the previous
leaf it covers the index set of the sealed statement; each alone covers only a subset of it, and
the
terms are squares, so each is strictly weaker than the sealed statement. -/
theorem leaf_odd_half_window_three_not_dvd (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ ¬ 3 ∣ m),
          (error (2 * m)) ^ 2 ≤
        C * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- `leaf_window_energy_four_not_dvd` of `LeanLab.ExceptionalSet.SPLIT_leaf_mean_square`,
assembled from the three leaves: reindex to the odd `m` in the half window, split those
`m` by `3 ∣ m`, bound each part by its leaf, and add the constants. -/
theorem leaf_window_energy_four_not_dvd_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨C₂, hC₂0, Y₂, hY₂, hbound₂⟩ :=
    leaf_odd_half_window_three_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C₃, hC₃0, Y₃, hY₃, hbound₃⟩ :=
    leaf_odd_half_window_three_not_dvd Θ hΘ1 hΘ2 hZF ε hε hsublinear
  have hP : 0 < 3 / 2 + 2 * Θ + ε := by linarith
  refine ⟨C₂ + C₃, by linarith, max Y₂ Y₃, le_max_of_le_left hY₂, ?_⟩
  intro Y hY
  have hY₂' : Y₂ ≤ Y := le_trans (le_max_left Y₂ Y₃) hY
  have hY₃' : Y₃ ≤ Y := le_trans (le_max_right Y₂ Y₃) hY
  have hb₂ := hbound₂ Y hY₂'
  have hb₃ := hbound₃ Y hY₃'
  have hmono : ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) ≤ (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    refine Real.rpow_le_rpow (by positivity) (by linarith) hP.le
  calc ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2
      = ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter Odd, (error (2 * m)) ^ 2 :=
        leaf_window_two_mod_four_reindex Y
    _ = ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ 3 ∣ m),
            (error (2 * m)) ^ 2
          + ∑ m ∈ (Finset.Icc (Y / 4 + 1) (Y / 2)).filter (fun m => Odd m ∧ ¬ 3 ∣ m),
            (error (2 * m)) ^ 2 :=
        sum_filter_split_one Odd (fun m => 3 ∣ m)
    _ ≤ C₂ * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) + C₃ * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) :=
        add_le_add hb₂ hb₃
    _ = (C₂ + C₃) * ((Y : ℝ) / 2) ^ (3 / 2 + 2 * Θ + ε) := by ring
    _ ≤ (C₂ + C₃) * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
        mul_le_mul_of_nonneg_left hmono (by linarith)

