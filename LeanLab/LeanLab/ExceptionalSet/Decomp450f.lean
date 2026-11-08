import LeanLab.ExceptionalSet.Decomp371c

/-!
Elementary companion supplies for P0082 pages 366 to 370.
Source: https://doi.org/10.5802/aif.1621
The height domination claim in SPLIT_lemma9 is a false auxiliary statement.
The paper instead truncates the Fourier index using coefficient decay on page 370.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450f

open Real Filter Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE R1 nu nuOdd)

/-- P0082 page 370, auxiliary unit bound used in the formal split of Lemma 9. -/
theorem gap_unit_supplied (γ : ℝ) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (N : ℕ) (hN : 3 ≤ N) : F γ N ^ (δ - 1) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
  apply Real.one_le_exp_iff.mpr
  exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _

/-- P0082 pages 366 and 369, exact finite parity split in SPLIT_lemma6. -/
theorem moment_parity_supplied (γ δ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc ((N + 1) / 2) N,
        ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2)
      = (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => Even (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2)
        + (∑ n ∈ (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
          ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Icc ((N + 1) / 2) N) (fun n => Even (nu γ n))]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hnO : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr (Finset.mem_filter.mp hn).2
    simp [nuOdd, hnO]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnO : Odd (nu γ n) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hn).2
    simp [nuOdd, hnO]

/-- P0082 page 369 after displays 29 and 30, exact finite Chebyshev leaf.
No sign assumption on g outside the bad set is needed. -/
theorem count_of_moment_supplied (s : Finset ℕ) (g : ℕ → ℝ) (T A : ℝ) (hT : 0 < T)
    (hmoment : (∑ n ∈ s, g n ^ 2) ≤ A) :
    (((s.filter (fun n => T < g n)).card : ℝ) * T ^ 2) ≤ A := by
  classical
  calc
    _ ≤ ∑ n ∈ s.filter (fun n => T < g n), g n ^ 2 := by
      simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum
        (s.filter (fun n => T < g n)) (fun n => g n ^ 2) (T ^ 2)
        (fun n hn => pow_le_pow_left₀ hT.le (Finset.mem_filter.mp hn).2.le 2)
    _ ≤ ∑ n ∈ s, g n ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _)
    _ ≤ A := hmoment

/-- The exact height domination conclusion of SPLIT_lemma9 is false for every
admissible parameter tuple. F grows faster than calE, so the displayed inequality
fails beyond a threshold. This is an audit of the formal helper, not the paper. -/
theorem not_height_domination (γ : ℝ) (hγ₁ : 1 < γ) (hγ₂ : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ¬ (∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 2 * F γ N ^ δ + 2 ≤ calE γ κ N ^ (2 / 3 : ℝ)) := by
  have ht : Tendsto (fun N : ℕ => δ * Real.log (N : ℝ) ^ (3 * γ - 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 3 * γ - 3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hδ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (κ * (2 / 3)))
  rintro ⟨N₁, hN₁⟩
  let N : ℕ := max 2 (max N₁ N₂)
  have hN2 : 2 ≤ N := le_max_left _ _
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hrate := hN₂ N hN₂'
  have he : (3 - 2 * γ) + (3 * γ - 3) = γ := by ring
  have hexponent : (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3) ≤
      Real.log (N : ℝ) ^ γ * δ := by
    calc
      _ = Real.log (N : ℝ) ^ (3 - 2 * γ) * (κ * (2 / 3)) := by ring
      _ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) * (δ * Real.log (N : ℝ) ^ (3 * γ - 3)) :=
        mul_le_mul_of_nonneg_left hrate (Real.rpow_nonneg hlog.le _)
      _ = _ := by
        rw [mul_left_comm _ δ, ← Real.rpow_add hlog, he]
        ring
  have hreverse : calE γ κ N ^ (2 / 3 : ℝ) ≤ F γ N ^ δ := by
    rw [calE, F, ← Real.exp_mul, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr hexponent
  have hbad := hN₁ N hN₁'
  have hpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  linarith

end LeanLab.ExceptionalSet.Decomp450f
