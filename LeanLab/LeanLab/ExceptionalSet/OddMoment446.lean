import LeanLab.ExceptionalSet.Adjacent446

/-!
The odd coefficient control used in P0082 page 362, Lemma 7.
The two parity moment inputs remain OPEN in Decomp371c.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.OddMoment446

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page 362 Lemma 6 and pages 366 to 369 displays 29 and 30.
The two inherited parity moments combine on the literal floor window.
This remains conditional on those two moments. -/
theorem odd_moment_uniform (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N,
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δa, hδa, ha⟩ := Decomp371c.leaf_even_moment γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := Decomp371c.leaf_odd_moment γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨Ba + Bb, add_pos hBa hBb, max 16 (max Na Nb), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let s := Finset.Icc ((N + 1) / 2) N
  let f := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  have hsub : window γ N ⊆ s := by
    intro n hn
    have hi := Finset.mem_Ioc.mp (Decomp371a.window_subset_Ioc γ h1 N hN16 hn)
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  calc
    _ ≤ ∑ n ∈ s, ‖f n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = (∑ n ∈ s.filter (fun n => Even (nu γ n)), ‖f n‖ ^ 2) +
        ∑ n ∈ s.filter (fun n => ¬ Even (nu γ n)), ‖f n‖ ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not s (fun n => Even (nu γ n)) _).symm
    _ ≤ Ba * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
        Bb * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
      apply add_le_add
      · convert ha N hNa using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnE := (Finset.mem_filter.mp hn).2
        have hnO : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr hnE
        simp [f, nuOdd, hnO]
      · convert hb N hNb using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnO : Odd (nu γ n) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hn).2
        simp [f, nuOdd, hnO]
    _ = _ := by ring

/-- P0082 page 362, Lemma 6 applied in the proof of Lemma 7.
A second moment with exponent minus one third controls an odd coefficient
at a fixed positive multiple of the larger minus one tenth threshold. -/
theorem odd_bad_count (s : Finset ℕ) (f : ℕ → ℂ)
    (c B X E : ℝ) (N : ℕ) (hc : 0 < c) (hB : 0 ≤ B) (hX : 0 < X) (hE : 1 ≤ E)
    (hm : (∑ n ∈ s, ‖f n‖ ^ 2) ≤ B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) :
    ((s.filter (fun n => c / 2 * X * E ^ (-(1 / 10 : ℝ)) < ‖f n‖)).card : ℝ) ≤
      (16 * B / c ^ 2) * N * E ^ (-(1 / 12 : ℝ)) := by
  classical
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  let T := c / 2 * X * E ^ (-(1 / 10 : ℝ))
  have hT : 0 < T := by dsimp [T]; positivity
  have hh := Decomp371b.count_of_tail_and_moment s f f T
    (B * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) hT
    (fun n _ => by simpa using (half_pos hT).le) hm
  have hp : E ^ (-(1 / 3 : ℝ)) ≤
      E ^ (-(1 / 12 : ℝ)) * (E ^ (-(1 / 10 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE0.le, ← Real.rpow_add hE0]
    exact Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hf : B * (N : ℝ) * X ^ 2 * E ^ (-(1 / 3 : ℝ)) ≤
      ((16 * B / c ^ 2) * N * E ^ (-(1 / 12 : ℝ))) * (T / 2) ^ 2 := by
    calc
      _ ≤ B * N * X ^ 2 * (E ^ (-(1 / 12 : ℝ)) * (E ^ (-(1 / 10 : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by
        dsimp [T]
        field_simp [hc.ne']
        <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp (hh.trans hf)

end LeanLab.ExceptionalSet.OddMoment446
