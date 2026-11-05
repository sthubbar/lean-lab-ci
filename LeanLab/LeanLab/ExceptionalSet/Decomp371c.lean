import LeanLab.ExceptionalSet.Decomp371b

/-!
Task371 decomposes P0082 Lemma 6 through the two parity moments of section 6.
Source: https://doi.org/10.5802/aif.1621 pages 366 to 369, displays 28 to 39.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp371c

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE)
open LeanLab.ExceptionalSet.DecompJ200

/-- LEAF. P0082 pages 366 to 369, displays 28 and 29. For even nu, the adjacent
odd coefficient is minus the minor coefficient. Display 29 bounds its second
moment. Including the possible lower endpoint adds one term, absorbed eventually. -/
theorem leaf_even_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- LEAF. P0082 pages 366 to 369, displays 28 and 30. For odd nu, nu itself is
odd. Display 30 and the reflected kernel give its second moment. Not even is
exactly odd for integers. The possible lower endpoint is absorbed eventually. -/
theorem leaf_odd_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  sorry

/-- Assembly. The exact existing State1539 Lemma6, from the two parity moments.
Conditional on the two analytic leaves above. -/
theorem lemma6_assembly : LeanLab.ExceptionalSet.U1539.Lemma6 := by
  classical
  intro γ h1 h2
  obtain ⟨δa, hδa, ha⟩ := leaf_even_moment γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_moment γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  let κ := min κa κb
  have hκ : 0 < κ := lt_min hκa hκb
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ (min_le_left _ _)
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (min_le_right _ _)
  let B : ℝ := 4 * (Ba + Bb + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨κ, B, hκ, max Na Nb, fun N hN => ?_⟩
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_right _ _).trans hN
  let s := Finset.Icc ((N + 1) / 2) N
  let f := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  have hmoment : (∑ n ∈ s, ‖f n‖ ^ 2) ≤
      (Ba + Bb) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not s (fun n => Even (nu γ n))]
    have he : (∑ n ∈ s.filter (fun n => Even (nu γ n)), ‖f n‖ ^ 2) =
        ∑ n ∈ s.filter (fun n => Even (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnE := (Finset.mem_filter.mp hn).2
      have hnO : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr hnE
      simp [f, nuOdd, hnO]
    have ho : (∑ n ∈ s.filter (fun n => ¬ Even (nu γ n)), ‖f n‖ ^ 2) =
        ∑ n ∈ s.filter (fun n => ¬ Even (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnO : Odd (nu γ n) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hn).2
      simp [f, nuOdd, hnO]
    rw [he, ho]
    calc _ ≤ Ba * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
          Bb * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
      _ = _ := by ring
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hT : 0 < B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by positivity
  have hc := Decomp371b.count_of_tail_and_moment s f f
    (B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ)))
    ((Ba + Bb) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) hT
    (fun n _ => by simpa using (half_pos hT).le) hmoment
  have hp : calE γ κ N ^ (-(1 / 3 : ℝ)) =
      calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
  have hcoef : Ba + Bb ≤ B ^ 3 / 4 := by
    have ha0 := hBa.le
    have hb0 := hBb.le
    have hB1 : 4 ≤ B := by dsimp [B]; linarith
    have hs : 4 * (Ba + Bb) ≤ B := by dsimp [B]; linarith
    nlinarith [sq_nonneg (B - 1)]
  have hbound : (Ba + Bb) * (N : ℝ) * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) ≤
      (B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) *
        (B * F γ N * calE γ κ N ^ (-(1 / 8 : ℝ)) / 2) ^ 2 := by
    rw [hp]
    calc
      _ ≤ (B ^ 3 / 4) * N * F γ N ^ 2 *
          (calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2) := by
        gcongr
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp (hc.trans hbound)

/-- Bridge. P0082 page 365 Lemma 8 follows by choosing the cap itself as kappa
in the stronger uniform major assembly. Conditional on its three analytic inputs. -/
theorem lemma8_assembly : LeanLab.ExceptionalSet.U1539.Lemma8 := by
  classical
  intro γ h1 h2
  obtain ⟨δ₀, hδ₀, h⟩ := Decomp371a.major_bound_assembly γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  obtain ⟨c₀, B, hc₀, hB, N₀, h⟩ := h κ₀ hκ₀ le_rfl
  refine ⟨κ₀, c₀, B, hκ₀, hc₀, N₀, fun N hN => ?_⟩
  simpa [Eγ_major_block, window, majorInt, Finset.filter_filter, and_assoc] using h N hN

end LeanLab.ExceptionalSet.Decomp371c
