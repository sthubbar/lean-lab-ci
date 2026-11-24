/-
P0083 Perelli 1996, pages 479 and 484 to 489, equations 18 through 32.
Feed 1122 split of DecompJ228.leaf_prime_mean_estimate.
The assembly below has the identical statement of its DecompJ228 parent. It
repeats the sorry free assembly of Decomp289a.leaf_prime_mean_estimate, but
draws the weighted mean and remainder mean steps from their independent
supplies instead of the two open Decomp289a leaves:
* equations 26 to 28 from Decomp582c.weighted_mean, which needs the higher
  degree Weyl input Decomp88.leaf_weyl together with proved cutoff, singular
  tail and principal mean pieces;
* equation 29 from the proved Decomp289a.leaf_leading_term;
* equations 31 and 32 from Decomp582a.remainder_mean, which needs
  Decomp582a.leaf_zero_density, page 485 equation 21, and
  Decomp582a.leaf_short_character_mean, pages 484 and 485 equations 18 to 25.
CONDITIONAL ON those inputs. No new sorry and no new LEAF in this file.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.DecompJ228
import LeanLab.Perelli1996.Decomp289a
import LeanLab.Perelli1996.Decomp582a
import LeanLab.Perelli1996.Decomp582c

namespace LeanLab.Perelli1996.Feed1122DecompJ228Split
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
noncomputable section

/-- Pages 487 and 489, equations 30 and 32. Identical statement to
`DecompJ228.leaf_prime_mean_estimate`. CONDITIONAL ON the inputs of
`Decomp582c.weighted_mean` and of `Decomp582a.remainder_mean`, with the
leading term step `Decomp289a.leaf_leading_term`. The assembly has no sorry. -/
theorem leaf_prime_mean_estimate_split (F : ℤ[X]) (hF : Admissible F) :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
        |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
            C * H * N * Real.log N ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, c, CW, NW, hB, hc, hCW, hNW, hw⟩ := Decomp582c.weighted_mean F hF A ε hA hε
  obtain ⟨CT, NT, hCT, hNT, ht⟩ := Decomp289a.leaf_leading_term F hF A ε hA hε
  obtain ⟨CR, NR, hCR, hNR, hr⟩ := Decomp582a.remainder_mean F hF c B A ε hc hB hA hε
  refine ⟨CW * (CR + Real.sqrt CR + 1) + CT,
    max (Real.exp 1 + 3) (max NW (max NT NR)), ?_⟩
  intro N H hN hH hHu
  have hNexp : Real.exp 1 + 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by have := Real.exp_pos 1; linarith
  have hL : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ N by linarith)
    simpa using this
  have hL0 : 0 < Real.log N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hNW' := (le_max_left NW (max NT NR)).trans ((le_max_right _ _).trans hN)
  have hNT' := (le_max_left NT NR).trans ((le_max_right NW _).trans ((le_max_right _ _).trans hN))
  have hNR' := (le_max_right NT NR).trans ((le_max_right NW _).trans ((le_max_right _ _).trans hN))
  have hr' := hr N H hNR' hH hHu
  have hpow := Real.rpow_le_rpow_of_exponent_le hL (show -2 * A - 1 ≤ -A by linarith)
  have hsmall : remainderMass F c N H B ≤ CR * N * Real.log N ^ (-A) :=
    hr'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hsq : Real.sqrt (N * Real.log N * remainderMass F c N H B) ≤
      Real.sqrt CR * N * Real.log N ^ (-A) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    calc N * Real.log N * remainderMass F c N H B
        ≤ N * Real.log N * (CR * N * Real.log N ^ (-2 * A - 1)) :=
          mul_le_mul_of_nonneg_left hr' (by positivity)
      _ = (Real.sqrt CR * N * Real.log N ^ (-A)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hCR.le,
          ← Real.rpow_mul_natCast hL0.le]
        have he : Real.log N * Real.log N ^ (-2 * A - 1) = Real.log N ^ (-A * 2) := by
          calc
            _ = Real.log N ^ (1 : ℝ) * Real.log N ^ (-2 * A - 1) := by rw [Real.rpow_one]
            _ = Real.log N ^ (1 + (-2 * A - 1)) := (Real.rpow_add hL0 _ _).symm
            _ = _ := by congr 1; ring
        calc _ = CR * N ^ 2 * (Real.log N * Real.log N ^ (-2 * A - 1)) := by ring
          _ = _ := by rw [he]; norm_num
  calc _ ≤ |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| +
        |(∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| :=
          abs_sub_le _ _ _
    _ ≤ (CW * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
          CW * H * N * Real.log N ^ (-A)) + CT * H * N * Real.log N ^ (-A) :=
          add_le_add (hw N H hNW' hH hHu) (ht N H hNT' hH hHu)
    _ ≤ (CW * H * (CR * N * Real.log N ^ (-A) +
          Real.sqrt CR * N * Real.log N ^ (-A)) +
          CW * H * N * Real.log N ^ (-A)) + CT * H * N * Real.log N ^ (-A) := by
          gcongr
    _ = _ := by ring

/-- Statement twin check: the split has the parent's type. -/
example : type_of% @leaf_prime_mean_estimate_split =
    type_of% @DecompJ228.leaf_prime_mean_estimate := rfl

end
end LeanLab.Perelli1996.Feed1122DecompJ228Split
