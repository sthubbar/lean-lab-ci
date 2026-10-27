/-
P0087 Akeno 2026 pages 4 to 6, support and reindexing in the Type I estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Statements

namespace LeanLab.Akeno2026.Weight86
open Set
/-- LEAF. Page 4 support convention, a continuous unit interval weight vanishes at both endpoints. -/
theorem weight_endpoints {w : ℝ → ℝ} (hw : Continuous w) (hs : Function.support w ⊆ Icc 0 1) :
    w 0 = 0 ∧ w 1 = 0 := by
  have hz : IsClosed {x : ℝ | w x = 0} := isClosed_eq hw continuous_const
  constructor
  · have hsub : Iio (0 : ℝ) ⊆ {x : ℝ | w x = 0} := by
      intro x hx
      by_contra hh
      have h0 := (hs hh).1
      exact (not_lt_of_ge h0) hx
    have hc := closure_minimal hsub hz
    rw [closure_Iio] at hc
    exact hc (by simp)
  · have hsub : Ioi (1 : ℝ) ⊆ {x : ℝ | w x = 0} := by
      intro x hx
      by_contra hh
      have h1 := (hs hh).2
      exact (not_lt_of_ge h1) hx
    have hc := closure_minimal hsub hz
    rw [closure_Ioi] at hc
    exact hc (by simp)

/-- LEAF. Pages 4 to 6, the natural and integer finite sum conventions agree at nonnegative scale. -/
theorem nat_int_sum (f : ℤ → ℂ) {Y : ℝ} (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), f (n : ℤ)) =
      ∑ n ∈ Finset.Icc (0 : ℤ) ⌊Y⌋, f n := by
  apply Finset.sum_bij (fun (n : ℕ) (_ : n ∈ Finset.range (⌊Y⌋₊ + 1)) => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_Icc, Int.le_floor]
    constructor
    · exact_mod_cast Nat.zero_le n
    · exact (Nat.le_floor_iff hY).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  · intro a ha b hb hab
    exact_mod_cast hab
  · intro z hz
    obtain ⟨hz0, hzY⟩ := Finset.mem_Icc.mp hz
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hreal : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hcast
    refine ⟨z.toNat, ?_, hcast⟩
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_iff.mpr
    apply Nat.le_floor
    rw [hreal]
    exact Int.le_floor.mp hzY
  · intro n hn
    rfl

open LeanLab.Akeno2026
/-- LEAF. Page 6 Type I localization, rescale the inner sum by X over m without changing the weight. -/
theorem typeI_inner_sum {w : ℝ → ℝ} (hs : Function.support w ⊆ Set.Icc 0 1)
    {X : ℝ} (hX : 0 < X) {m : ℕ} (hm : 1 ≤ m) (β : ℝ) :
    (∑ n ∈ Finset.range (⌊X⌋₊ + 1), e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)) =
      ∑ n ∈ Finset.Icc (0 : ℤ) ⌊X / m⌋,
        e ((β * m) * n) * (w ((n : ℝ) / (X / m)) : ℂ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hY0 : 0 < X / m := div_pos hX hm0
  have hYle : X / m ≤ X := div_le_self hX.le hm1
  have hsub : Finset.range (⌊X / m⌋₊ + 1) ⊆ Finset.range (⌊X⌋₊ + 1) :=
    Finset.range_mono (by have hh := Nat.floor_mono hYle; omega)
  let f : ℕ → ℂ := fun n => e (β * m * n) * (w ((m : ℝ) * n / X) : ℂ)
  have heq : (∑ n ∈ Finset.range (⌊X / m⌋₊ + 1), f n) =
      ∑ n ∈ Finset.range (⌊X⌋₊ + 1), f n := by
    apply Finset.sum_subset hsub
    intro n hn hnot
    have hnf : ⌊X / m⌋₊ < n := by simpa using hnot
    have hYn : X / m < (n : ℝ) := (Nat.floor_lt hY0.le).mp hnf
    have hh : X < (n : ℝ) * m := (div_lt_iff₀ hm0).mp hYn
    have hu : 1 < (m : ℝ) * n / X := (lt_div_iff₀ hX).mpr (by nlinarith)
    have hw0 : w ((m : ℝ) * n / X) = 0 := by
      by_contra hnz
      have hb := (hs hnz).2
      linarith
    simp [f, hw0]
  calc
    _ = ∑ n ∈ Finset.range (⌊X / m⌋₊ + 1), f n := heq.symm
    _ = ∑ n ∈ Finset.range (⌊X / m⌋₊ + 1),
        e ((β * m) * n) * (w ((n : ℝ) / (X / m)) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [f]
      congr 2
      field_simp
    _ = _ := by
      simpa only [Int.cast_natCast] using
        nat_int_sum (fun n : ℤ => e ((β * m) * n) * (w ((n : ℝ) / (X / m)) : ℂ)) hY0.le

end LeanLab.Akeno2026.Weight86
