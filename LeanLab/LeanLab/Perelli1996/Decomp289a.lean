/-
P0083 Perelli 1996, pages 486 and 487, equations 26 through 32.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.DecompJ228
import LeanLab.Perelli1996.Definitions103

namespace LeanLab.Perelli1996.Decomp289a
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88
noncomputable section

/-- The order Q of the Section 3 dissection on page 486. -/
def meanOrder (F : ℤ[X]) (N H B : ℝ) : ℝ :=
  H ^ F.natDegree * Real.log N ^ (-B)

/-- The nonnegative remainder sum Sigma P below equation 27 on page 486.
Reduced residues use representatives one through q, as in the paper.
The existing characterRemainder uses an inclusive cutoff with a zero term
in its principal kernel. This is the endpoint variant of the printed sum. -/
def remainderMass (F : ℤ[X]) (c N H B : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
    ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      ∫ η in Set.Icc (-(1 / ((q : ℝ) * meanOrder F N H B)))
        (1 / ((q : ℝ) * meanOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q (a : ℤ) η‖ ^ 2

/-- The remainder mass is nonnegative, as a sum of squared norms. -/
theorem remainderMass_nonneg (F : ℤ[X]) (c N H B : ℝ) :
    0 ≤ remainderMass F c N H B := by
  unfold remainderMass
  positivity

/-- LEAF. Pages 486 and 487, equations 26 through 28.
The circle method compares the prime mean with the weighted singular mean.
This retains the character remainder instead of assuming its saving. -/
theorem leaf_weighted_mean (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B c C N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, R (Fv F n).toNat) -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
        C * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
        C * H * N * Real.log N ^ (-A) := by
  sorry

/-- LEAF. Page 487 equation 29.
Replace F n by its leading term on the shorter polynomial window.
This leaf involves the singular series but no prime representation count. -/
theorem leaf_leading_term (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat) -
        (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
        C * H * N * Real.log N ^ (-A) := by
  sorry

/-- LEAF. Page 487 equations 31 and 32.
Character orthogonality followed by the zero free region and zero density
estimate gives Sigma P at most N times L to the power minus two A minus one.
The cutoff c is fixed before N tends to infinity. -/
theorem leaf_remainder_mean (F : ℤ[X]) (hF : Admissible F)
    (c B A ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      remainderMass F c N H B ≤ C * N * Real.log N ^ (-2 * A - 1) := by
  sorry

/-- The exact existing prime mean target from the three smaller leaves.
CONDITIONAL ON weighted mean, leading term and character remainder leaves. -/
theorem leaf_prime_mean_estimate (F : ℤ[X]) (hF : Admissible F) :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
        |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
            C * H * N * Real.log N ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, c, CW, NW, hB, hc, hCW, hNW, hw⟩ := leaf_weighted_mean F hF A ε hA hε
  obtain ⟨CT, NT, hCT, hNT, ht⟩ := leaf_leading_term F hF A ε hA hε
  obtain ⟨CR, NR, hCR, hNR, hr⟩ := leaf_remainder_mean F hF c B A ε hc hB hA hε
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

end
end LeanLab.Perelli1996.Decomp289a
