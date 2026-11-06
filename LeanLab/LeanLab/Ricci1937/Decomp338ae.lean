import LeanLab.Ricci1937.Decomp338ad
import LeanLab.Ricci1937.Decomp338m

/-!
Ricci 1937, the distinct case four support profile.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary case four profile estimate for first memoir page 89, the tau bar display.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/
lemma decomp338_case_four_perturbation (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
        exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε)) < (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + η := by
  let g : ℝ → ℝ := fun ε => exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
    exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε))
  have hd : 1 - exp (-0.50 / 2 : ℝ) ≠ 0 := by
    have he : exp (-0.50 / 2 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hg0 : g 0 = (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) := by
    dsimp [g]
    simp only [mul_zero, add_zero]
    have h2 : exp (-(1.46 + Real.log (4 : ℝ)) / 2) = exp (-Real.log 4 / 2) * exp (-1.46 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    have h3 : exp (-(1.98 + Real.log (4 : ℝ)) / 2) = exp (-Real.log 4 / 2) * exp (-1.98 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    rw [h2, h3]
    ring
  have hcont : ContinuousAt g 0 := by
    dsimp [g]
    fun_prop (disch := simpa using hd)
  have hnear : ∀ᶠ ε : ℝ in nhds 0, g ε < (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + η :=
    hcont.tendsto.eventually (eventually_lt_nhds (by rw [hg0]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ε, hε, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos hε] using hεδ

/-- Auxiliary case four profile estimate for first memoir page 89, the tau bar display.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/
lemma decomp338_case_four_geometric_sum (ε : ℝ) (hε : ε < 1 / 4) (n : ℕ) :
    let a : ℕ → ℝ := fun i => if i = 0 then exp (-0.90 + 2 * ε)
      else if i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
      else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ (i - 2)
    (∑ i ∈ range n, a i) ≤
      exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
        exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε)) := by
  dsimp only
  let q := exp (-0.50 / 2 + ε)
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hgeom (k : ℕ) : (∑ i ∈ range k, q ^ i) ≤ 1 / (1 - q) := by
    have hsum := (hasSum_geometric_of_lt_one hq0 hq1).summable.sum_le_tsum
      (range k) (fun i _ => pow_nonneg hq0 i)
    simpa only [(hasSum_geometric_of_lt_one hq0 hq1).tsum_eq, one_div] using hsum
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  rcases n with _ | n
  · simp only [Nat.zero_add, range_one, sum_singleton]
    have hd : 0 < 1 - q := sub_pos.mpr hq1
    change exp (-0.90 + 2 * ε) ≤ exp (-0.90 + 2 * ε) +
      exp (-(1.46 + Real.log 4) / 2 + 2 * ε) + exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - q)
    have hcdiv : 0 ≤ exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - q) :=
      div_nonneg (exp_pos _).le hd.le
    linarith [exp_pos (-(1.46 + Real.log 4) / 2 + 2 * ε)]
  · rw [show n + 1 + 1 = 2 + n by omega, sum_range_add]
    have hhead : (∑ i ∈ range 2, if i = 0 then exp (-0.90 + 2 * ε)
        else if i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
        else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ (i - 2)) =
          exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) := by
      norm_num [sum_range_succ]
    rw [hhead]
    have htail : (∑ i ∈ range n,
        if 2 + i = 0 then exp (-0.90 + 2 * ε)
        else if 2 + i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
        else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ (2 + i - 2)) =
          exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * ∑ i ∈ range n, q ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have h1 : 2 + i ≠ 1 := by omega
      simp [h1, show 2 + i - 2 = i by omega]
    change _ ≤ exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
      exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - q)
    rw [htail]
    have hh := mul_le_mul_of_nonneg_left (hgeom n) (exp_pos (-(1.98 + Real.log 4) / 2 + 3 * ε)).le
    simpa only [mul_one_div, add_comm] using add_le_add_left hh
      (exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε))

/-- Auxiliary case four profile estimate for first memoir page 89, the tau bar display.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/
lemma decomp338_case_four_support_profile (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ α : ℕ → ℝ, 0 < ε ∧ ε < 1 / 4 ∧ α 0 = 1 ∧
      (∀ i, 0 < α i) ∧ (∀ i, α (i + 1) ≤ α i) ∧
      (∀ n, (∑ i ∈ range n, α (i + 1)) ≤ (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + η) ∧
      α 1 = exp (-0.90 + 2 * ε) ∧ α 2 = exp (-(1.46 + Real.log 4) / 2 + 2 * ε) ∧
      ∀ i, α (i + 3) = exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i := by
  obtain ⟨ε, hε0, hε, hsum⟩ := decomp338_case_four_perturbation η hη
  have hlog4 : (0.34 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  let q := exp (-0.50 / 2 + ε)
  let α : ℕ → ℝ := fun i => if i = 0 then 1 else if i = 1 then exp (-0.90 + 2 * ε)
    else if i = 2 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
    else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ (i - 3)
  have hq : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hpos (i : ℕ) : 0 < α i := by
    dsimp [α]
    split_ifs <;> positivity
  have hmono (i : ℕ) : α (i + 1) ≤ α i := by
    rcases i with _ | i
    · simpa [α] using exp_le_one_iff.mpr (show -0.90 + 2 * ε ≤ 0 by linarith)
    rcases i with _ | i
    · simp only [Nat.zero_add]
      change exp (-(1.46 + Real.log 4) / 2 + 2 * ε) ≤ exp (-0.90 + 2 * ε)
      exact exp_le_exp.mpr (by linarith)
    rcases i with _ | i
    · change exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ 0 ≤ exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
      rw [pow_zero, mul_one]
      exact exp_le_exp.mpr (by linarith)
    · have hne0 : i + 1 + 1 + 1 ≠ 0 := by omega
      have hne1 : i + 1 + 1 + 1 ≠ 1 := by omega
      have hne2 : i + 1 + 1 + 1 ≠ 2 := by omega
      have hne0' : i + 1 + 1 + 1 + 1 ≠ 0 := by omega
      have hne1' : i + 1 + 1 + 1 + 1 ≠ 1 := by omega
      have hne2' : i + 1 + 1 + 1 + 1 ≠ 2 := by omega
      simp only [α, ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
        ite_eq_right hne0', ite_eq_right hne1', ite_eq_right hne2']
      rw [show i + 1 + 1 + 1 - 3 = i by omega,
        show i + 1 + 1 + 1 + 1 - 3 = i + 1 by omega, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hq.le
        (show 0 ≤ exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ i by positivity)]
  have hshift (i : ℕ) : α (i + 1) = if i = 0 then exp (-0.90 + 2 * ε)
      else if i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
      else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ (i - 2) := by
    by_cases hi0 : i = 0
    · subst i
      norm_num [α]
    by_cases hi1 : i = 1
    · subst i
      norm_num [α]
    have h2 : i + 1 ≠ 2 := by omega
    simp [α, hi0, hi1, h2, show i + 1 - 3 = i - 2 by omega]
  refine ⟨ε, α, hε0, hε, by simp [α], hpos, hmono, ?_, by simp [α], by simp [α], ?_⟩
  · intro n
    simp_rw [hshift]
    exact (decomp338_case_four_geometric_sum ε hε n).trans hsum.le
  · intro i
    have h1 : i + 3 ≠ 1 := by omega
    have h2 : i + 3 ≠ 2 := by omega
    simp [α, h1, h2, show i + 3 - 3 = i by omega, q]

end
end LeanLab.Ricci1937
