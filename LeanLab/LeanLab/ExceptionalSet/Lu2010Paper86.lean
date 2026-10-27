/-
P0095 Lu 2010, page 2392 equation 86 with the full printed window.
CODEX task47, unit U-8107. AI wrote this Lean code. Binary Goldbach is open.
The finite expression 63 satisfies the printed mean square bound conditional on Mass39.
-/
import LeanLab.ExceptionalSet.Lu2010Eq63

namespace LeanLab.ExceptionalSet.Lu2010Paper86
open Finset Real
open LeanLab.PNTPort.LargeSieve
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010ZeroIntegral
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010Expansion63
open LeanLab.ExceptionalSet.Lu2010Eq86
open LeanLab.ExceptionalSet.Lu2010Eq86Scale
open LeanLab.ExceptionalSet.Lu2010Eq63

noncomputable def paperRad (N : ℕ) : ℕ := ⌊dd N * (N : ℝ) ^ (-0.0001 : ℝ)⌋₊

/-- The full window of equation 86, in contrast to the narrower Lemma 1 window. -/
noncomputable def paperWin (N : ℕ) : Finset ℕ := Icc (N - paperRad N) (N + paperRad N)

/-- The large sieve cost on the full printed window is still at most five d. -/
theorem paper_window_bound {N : ℕ} (hN : 1 ≤ N) (B : ℕ × ℕ → ℂ) :
    ∑ k ∈ paperWin N, ‖rationalSum ⌊PP N⌋₊ B (k : ℤ)‖ ^ 2 ≤
      5 * dd N * ∑ p ∈ farey ⌊PP N⌋₊, ‖B p‖ ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd1 : 1 ≤ dd N := Real.one_le_rpow hN1 (by norm_num)
  have hQ1 : 1 ≤ ⌊PP N⌋₊ := Nat.one_le_floor_iff _ |>.2
    (Real.one_le_rpow hN1 (by unfold c; norm_num))
  have hr : (paperRad N : ℝ) ≤ dd N := by
    refine (Nat.floor_le (by unfold dd; positivity)).trans ?_
    have hsmall : (N : ℝ) ^ (-0.0001 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
    exact (mul_le_mul_of_nonneg_left hsmall (by unfold dd; positivity)).trans_eq (mul_one _)
  have hq2 : (⌊PP N⌋₊ : ℝ) ^ 2 ≤ dd N := by
    have hq : (⌊PP N⌋₊ : ℝ) ≤ PP N := Nat.floor_le (by unfold PP; positivity)
    calc (⌊PP N⌋₊ : ℝ) ^ 2 ≤ (PP N) ^ 2 := by gcongr
      _ = (N : ℝ) ^ (2 * c) := by
        unfold PP
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ dd N := Real.rpow_le_rpow_of_exponent_le hN1 (by unfold c; norm_num)
  have hAB : N - paperRad N ≤ N + paperRad N := by omega
  have h := rationalSum_Icc hQ1 hAB B
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  have hlen : N + paperRad N + 1 - (N - paperRad N) ≤ 2 * paperRad N + 1 := by omega
  have hlenr : ((N + paperRad N + 1 - (N - paperRad N) : ℕ) : ℝ) ≤ 2 * paperRad N + 1 := by
    exact_mod_cast hlen
  linarith

/-- Coefficient energy from equation 63 and the cited zero mass, before choosing a k window. -/
theorem B_energy_of_mass39 (family : ℕ → Finset Exponent) (M : ℕ → ℝ) (h39 : Mass39 family) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ p ∈ farey ⌊PP N⌋₊, ‖B N (family N) (M N) p‖ ^ 2 ≤
        Cb * PP N ^ (-1 : ℝ) * (N : ℝ) ^ (2.0003 : ℝ) := by
  classical
  obtain ⟨C, hC, N0, hmass⟩ := h39
  obtain ⟨Ck, hCk, hK⟩ := K_cube_bound
  refine ⟨2 * (3 * C ^ 2) ^ 2 * Ck, by positivity, max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNm : N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR : 0 < PP N * (N : ℝ) ^ (-0.0001 : ℝ) := by unfold PP; positivity
  have hw : ∀ p ∈ pairs N (family N) (M N), 0 ≤ W N p := fun p _ => (W_pos hN1 p).le
  have hr : ∀ p ∈ pairs N (family N) (M N), PP N * (N : ℝ) ^ (-0.0001 : ℝ) ≤ pairMod p :=
    fun p hp => (mem_filter.mp hp).2.1.le
  have hz : ∀ p ∈ pairs N (family N) (M N), ∀ q ∈ Icc 1 ⌊PP N⌋₊, ‖factor N p q‖ ≤ pairMod p :=
    fun p _ q hq => factor_bound hN1 p q (mem_Icc.mp hq).1
  have hE := coefficients_energy (pairs N (family N) (M N)) (W N) pairMod (factor N) pairChar
    ⌊PP N⌋₊ hR (K_nonneg hN1) hw hr (totient_cost hN1) hz
  have hm0 : 0 ≤ ∑ x ∈ family N, weight N x.rho := by
    apply sum_nonneg
    intro x _
    unfold weight
    positivity
  have hm2 := pow_le_pow_left₀ hm0 (hmass N hNm hN1) 2
  have hW : (∑ p ∈ pairs N (family N) (M N), W N p) ≤ (3 * C ^ 2) * N := by
    refine (W_total hN1 _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hm2 (show (0 : ℝ) ≤ 3 * N by positivity)]
  have hW0 : 0 ≤ ∑ p ∈ pairs N (family N) (M N), W N p := sum_nonneg hw
  have hW2 := pow_le_pow_left₀ hW0 hW 2
  have hKN0 := K_nonneg hN1
  calc (∑ p ∈ farey ⌊PP N⌋₊, ‖B N (family N) (M N) p‖ ^ 2)
      ≤ (∑ p ∈ pairs N (family N) (M N), W N p) ^ 2 *
          (2 * K N ^ 3 / (PP N * (N : ℝ) ^ (-0.0001 : ℝ))) := hE
    _ ≤ ((3 * C ^ 2) * N) ^ 2 *
          (2 * (Ck * (N : ℝ) ^ (0.0002 : ℝ)) / (PP N * (N : ℝ) ^ (-0.0001 : ℝ))) := by
      exact mul_le_mul hW2
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK N hN1) (by norm_num)) hR.le)
        (by positivity) (sq_nonneg _)
    _ = (2 * (3 * C ^ 2) ^ 2 * Ck) * PP N ^ (-1 : ℝ) *
          ((N : ℝ) ^ 2 * (N : ℝ) ^ (0.0002 : ℝ) / (N : ℝ) ^ (-0.0001 : ℝ)) := by
      rw [Real.rpow_neg_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [exponent86 hN1]

/-- Equation 86 on its full printed window, for the finite Gauss expression 63. -/
theorem equation86 (family : ℕ → Finset Exponent) (M : ℕ → ℝ) (h39 : Mass39 family) :
    ∃ C86 : ℝ, 0 ≤ C86 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ k ∈ paperWin N, ‖printed63 N (family N) (M N) k‖ ^ 2 ≤
        C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) := by
  obtain ⟨Cb, hCb, N0, hB⟩ := B_energy_of_mass39 family M h39
  refine ⟨5 * Cb, by positivity, max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  simp_rw [← D6_eq_printed63 hN1]
  calc (∑ k ∈ paperWin N, ‖D6 N (family N) (M N) k‖ ^ 2)
      ≤ 5 * dd N * ∑ p ∈ farey ⌊PP N⌋₊, ‖B N (family N) (M N) p‖ ^ 2 := paper_window_bound hN1 _
    _ ≤ 5 * dd N * (Cb * PP N ^ (-1 : ℝ) * (N : ℝ) ^ (2.0003 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hB N (le_trans (le_max_left _ _) hN)) (by unfold dd; positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Lu2010Paper86

#print axioms LeanLab.ExceptionalSet.Lu2010Paper86.paper_window_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Paper86.B_energy_of_mass39
#print axioms LeanLab.ExceptionalSet.Lu2010Paper86.equation86
