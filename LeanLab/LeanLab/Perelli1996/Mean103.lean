/-
P0083 Perelli 1996, pages 487 and 489, equations 30, 32 and 37.
Theorem 2 from its analytic prime mean input and the proved singular average.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Average88

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial
noncomputable section

/-- A fixed power error is absorbed by a larger interval power with any logarithmic saving. -/
theorem power_error_log_saving (δ A : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → N ^ (2 * δ) ≤ H →
      N ^ δ ≤ H * Real.log N ^ (-A) := by
  have hb := (isLittleO_log_rpow_rpow_atTop A hδ).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog := hN₁ N ((le_max_right _ _).trans hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le A),
    abs_of_nonneg (Real.rpow_nonneg hN0.le δ), one_mul] at hlog
  have hmul : N ^ δ * Real.log N ^ A ≤ H := by
    calc
      _ ≤ N ^ δ * N ^ δ := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hN0.le _)
      _ = N ^ (2 * δ) := by rw [← Real.rpow_add hN0]; congr 1; ring
      _ ≤ H := hH
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).mpr hmul

/-- Theorem 2, CONDITIONAL ON the prime mean estimate of equations 30 and 32.
The singular average input of equation 37 is supplied by its existing proof. -/
theorem theorem2_of_prime_mean (F : ℤ[X])
    (hmean : Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
        |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
            C * H * N * Real.log N ^ (-A)) : Theorem2 F := by
  intro hF A ε hA hε
  let k : ℝ := F.natDegree
  let δ := 1 / (12 * k)
  have hk : 0 < k := by dsimp [k]; exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha : 0 < (F.leadingCoeff : ℝ) := by exact_mod_cast hF.2
  obtain ⟨CM, NM, hm⟩ := hmean hF A ε hA hε
  obtain ⟨CS, NS, hs⟩ := singularAverage F hF δ hδ
  obtain ⟨NP, hNP, hp⟩ := power_error_log_saving δ A hδ
  refine ⟨|CM| + (F.leadingCoeff : ℝ) * |CS|, max 3 (max NM (max NS NP)), ?_⟩
  intro N H hN hH hHu
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hNM := (le_max_left NM (max NS NP)).trans ((le_max_right 3 (max NM (max NS NP))).trans hN)
  have hNS := (le_max_left NS NP).trans ((le_max_right NM (max NS NP)).trans
    ((le_max_right 3 (max NM (max NS NP))).trans hN))
  have hNP' := (le_max_right NS NP).trans ((le_max_right NM (max NS NP)).trans
    ((le_max_right 3 (max NM (max NS NP))).trans hN))
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hupper : H ≤ N ^ (1 / (F.natDegree : ℝ)) :=
    hHu.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hexp : 2 * δ ≤ 1 / (6 * (F.natDegree : ℝ)) + ε := by
    dsimp [δ, k]
    have heq : 2 * (1 / (12 * (F.natDegree : ℝ))) = 1 / (6 * (F.natDegree : ℝ)) := by ring
    rw [heq]
    linarith
  have hpower := hp N H hNP' ((Real.rpow_le_rpow_of_exponent_le hN1 hexp).trans hH)
  have hm' := hm N H hNM hH hHu
  have hs' := hs N H hNS hH0.le hupper
  let J := ((Roots.rootResidues F 2).card : ℝ) / 2 * H * singularConstant *
    ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
      (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))
  have hconst : averageConstant F * H * N = (F.leadingCoeff : ℝ) * N * J := by
    dsimp [averageConstant, J]
    ring
  have hsabs : |(∑ n ∈ win F N H, Sing (Fv F n).toNat) - J| ≤
      |CS| * H * Real.log N ^ (-A) := by
    calc
      _ ≤ CS * N ^ δ := hs'
      _ ≤ |CS| * N ^ δ := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hN0.le _)
      _ ≤ |CS| * (H * Real.log N ^ (-A)) := mul_le_mul_of_nonneg_left hpower (abs_nonneg _)
      _ = _ := by ring
  rw [hconst]
  calc
    _ ≤ |(∑ n ∈ win F N H, R (Fv F n).toNat) -
        (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| +
      |(F.leadingCoeff : ℝ) * N * (∑ n ∈ win F N H, Sing (Fv F n).toNat) -
        (F.leadingCoeff : ℝ) * N * J| := abs_sub_le _ _ _
    _ ≤ |CM| * H * N * Real.log N ^ (-A) +
      ((F.leadingCoeff : ℝ) * N) * (|CS| * H * Real.log N ^ (-A)) := by
      apply add_le_add
      · exact hm'.trans (by gcongr; exact le_abs_self _)
      · rw [← mul_sub, abs_mul, abs_of_pos (mul_pos ha hN0)]
        exact mul_le_mul_of_nonneg_left hsabs (by positivity)
    _ = _ := by ring

end
end LeanLab.Perelli1996.Section3
