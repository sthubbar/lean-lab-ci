/-
Feed split of bhp_endpoint_lower from Decomp379a.
Baker, Harman and Pintz 1997, P0069, page 4, proof of Theorem 3 part I:
a sieve minorant a0 below the prime indicator satisfies item i of Theorem 2,
with associated constant above 0.9953 by page 41, and residue classes are
picked out by characters. MMS https://arxiv.org/abs/1610.02017v2 page 3.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379a

namespace LeanLab.Ternary.MMS.Task379
open Finset

/-- LEAF: BHP 1997 page 4, proof of Theorem 3 part I, HARD for Codex.
The section 4 sieve construction gives a minorant a0 of the prime indicator,
allowed to depend on the scale y, whose associated constant u0 exceeds 0.9953
by the page 41 display. Item i of Theorem 2, display 1.7, with residue classes
picked out by characters, gives the short interval progression asymptotic with
main term u0 times the logarithmic integral of the interval over the totient.
This is a cited published input. -/
theorem bhp_minorant_progression_asymptotic (σ : ℝ) (hσ : 11 / 20 < σ) (hσ1 : σ < 1) :
    ∃ a0 : ℝ → ℕ → ℝ, (∀ y : ℝ, ∀ n : ℕ, a0 y n ≤ ρ n) ∧
      ∃ u0 : ℝ, 0.9953 < u0 ∧ ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y →
        ∀ h : ℝ, y ^ σ ≤ h → h ≤ y / Real.log y → ∀ d c : ℕ,
        1 ≤ d → (d : ℝ) ≤ Real.log y ^ (2 : ℕ) → Nat.Coprime c d →
        |∑ n ∈ (ints (y - h) y).filter (fun n => n ≡ c [MOD d]), a0 y n -
            u0 / d.totient * ∫ t in (y - h)..y, 1 / Real.log t| ≤
          ε * h / (d.totient * Real.log y) := by
  sorry

/-- The logarithmic integral of a short interval is at least its length over log y.
Derived elementary step behind the main term in BHP page 4, Theorem 3 part I. -/
theorem logIntegral_ge_short {y h : ℝ} (hh : 0 ≤ h) (hyh : 1 < y - h) :
    h / Real.log y ≤ ∫ t in (y - h)..y, 1 / Real.log t := by
  have hy1 : 1 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Icc (y - h) y) := by
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (by linarith [ht.1] : (0 : ℝ) < t).ne')
    · intro t ht
      exact (Real.log_pos (by linarith [ht.1])).ne'
  have hab : y - h ≤ y := by linarith
  have hmono : ∫ t in (y - h)..y, (1 / Real.log y) ≤ ∫ t in (y - h)..y, 1 / Real.log t := by
    apply intervalIntegral.integral_mono_on hab
    · exact intervalIntegrable_const
    · exact hcont.intervalIntegrable_of_Icc hab
    · intro t ht
      have ht0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have : (y - (y - h)) * (1 / Real.log y) = h / Real.log y := by ring
  linarith

/-- The exact endpoint input of Decomp379a from the cited minorant asymptotic.
BHP page 4 Theorem 3 part I, with the margin 0.9953 minus 0.0003 above 0.995.
CONDITIONAL ON bhp_minorant_progression_asymptotic. -/
theorem bhp_endpoint_lower_of_leaves (σ : ℝ) (hσ : 11 / 20 < σ) (hσ1 : σ < 1) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y → ∀ h : ℝ,
      y ^ σ ≤ h → h ≤ y / Real.log y → ∀ d c : ℕ,
      1 ≤ d → (d : ℝ) ≤ Real.log y ^ (2 : ℕ) → Nat.Coprime c d →
      0.995 * h / (d.totient * Real.log y) ≤
        ∑ n ∈ (ints (y - h) y).filter (fun n => n ≡ c [MOD d]), ρ n := by
  obtain ⟨a0, ha0, u0, hu0, hasym⟩ := bhp_minorant_progression_asymptotic σ hσ hσ1
  obtain ⟨Y₀, hY₀, hY⟩ := hasym 0.0003 (by norm_num)
  obtain ⟨Y₁, hY₁⟩ := (Real.tendsto_log_atTop.eventually_ge_atTop 4).exists_forall_of_atTop
  refine ⟨max Y₀ (max Y₁ 4), lt_of_lt_of_le hY₀ (le_max_left _ _), ?_⟩
  intro y hy h hlow hupp d c hd hdlog hcd
  have hyY₀ : Y₀ ≤ y := (le_max_left _ _).trans hy
  have hyY₁ : Y₁ ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy
  have hy4 : 4 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy
  have hl4 : 4 ≤ Real.log y := hY₁ y hyY₁
  have hly : 0 < Real.log y := by linarith
  have hh0 : 0 ≤ h := (Real.rpow_nonneg (by linarith) σ).trans hlow
  have hhy : h ≤ y / 4 := hupp.trans (div_le_div_of_nonneg_left (by linarith) (by norm_num) hl4)
  have hyh : 1 < y - h := by linarith
  have ht : 0 < (d.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
  have hA := hY y hyY₀ h hlow hupp d c hd hdlog hcd
  have hLI := logIntegral_ge_short hh0 hyh
  have hsumρ : ∑ n ∈ (ints (y - h) y).filter (fun n => n ≡ c [MOD d]), a0 y n ≤
      ∑ n ∈ (ints (y - h) y).filter (fun n => n ≡ c [MOD d]), ρ n :=
    sum_le_sum (fun n _ => ha0 y n)
  have hmain : u0 * h / (d.totient * Real.log y) ≤
      u0 / d.totient * ∫ t in (y - h)..y, 1 / Real.log t := by
    have hu : 0 ≤ u0 / d.totient := div_nonneg (by linarith) ht.le
    have := mul_le_mul_of_nonneg_left hLI hu
    calc u0 * h / (d.totient * Real.log y) = u0 / d.totient * (h / Real.log y) := by
          field_simp
      _ ≤ _ := this
  have hlo := (abs_le.mp hA).1
  have hfin : 0.995 * h / (d.totient * Real.log y) ≤
      u0 * h / (d.totient * Real.log y) - 0.0003 * h / (d.totient * Real.log y) := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (mul_pos ht hly).le
    nlinarith
  linarith

end LeanLab.Ternary.MMS.Task379
