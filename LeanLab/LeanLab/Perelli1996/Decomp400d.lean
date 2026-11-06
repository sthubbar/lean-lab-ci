/-
Perelli 1996, page 482, the named Weyl lemma.
Extend the existing large N statement over the bounded initial range.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp400a

namespace LeanLab.Perelli1996.Decomp400d
open Finset Real Polynomial
noncomputable section

/-- Page 480. Both encodings use the same polynomial exponential kernel. -/
theorem polynomialKernel_eq (F : ℤ[X]) (N H α : ℝ) :
    Section2.polynomialKernel F N H α = EncA.Kexp F N H α := by
  unfold Section2.polynomialKernel EncA.Kexp
  apply Finset.sum_congr rfl
  intro n hn
  unfold Kernel.e LeanLab.PerelliPintz1992.e Fv
  congr 1
  push_cast
  ring

/-- Page 480. The kernel norm is bounded by H plus one on a nonnegative window. -/
theorem norm_polynomialKernel_le (F : ℤ[X]) (N H α : ℝ)
    (hN : 0 ≤ N) (hH : 0 ≤ H) :
    ‖Section2.polynomialKernel F N H α‖ ≤ H + 1 := by
  calc
    _ ≤ ∑ n ∈ win F N H, ‖Kernel.e ((Fv F n : ℝ) * α)‖ := norm_sum_le _ _
    _ = ((win F N H).card : ℝ) := by simp [Kernel.e, Complex.norm_exp]
    _ ≤ H + 1 := Decomp103.card_win_le F hN hH

/-- Page 482 named Lemma. The large N Weyl input implies encoding A's exact statement.
The bounded initial range uses only the trivial kernel bound.
CONDITIONAL ON the explicit current Weyl input. -/
theorem weylLemma_encA_of (F : ℤ[X]) (hW : Section2.WeylLemma F) : EncA.WeylLemma F := by
  intro hF D hD
  obtain ⟨C, N₀, hC, hN₀, hw⟩ := hW hF D hD
  let K := Section2.weylExponent F
  let v := (D + 1) / K
  let T := N₀ ^ (1 / (F.natDegree : ℝ))
  let b := (1 / T) ^ (1 / K) * Real.log 2 ^ v
  have hK : 0 < K := by dsimp [K, Section2.weylExponent]; positivity
  have hT : 0 < T := Real.rpow_pos_of_pos (by linarith) _
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hcast : ((F.natDegree - 1 : ℕ) : ℝ) = (F.natDegree : ℝ) - 1 := by
    rw [Nat.cast_sub hF.1, Nat.cast_one]
  have hpow : (2 : ℝ) ^ (EncA.deg F - 1) = K := by
    dsimp [EncA.deg, K, Section2.weylExponent]
    rw [← hcast, Real.rpow_natCast]
  refine ⟨max C (2 / b), ?_⟩
  intro N H α hN hH hHu a q hq hcop happ
  rw [hpow, ← polynomialKernel_eq]
  simp only [EncA.deg, Real.rpow_natCast]
  have hN0 : 0 ≤ N := by linarith
  have hH0 : 0 < H := by linarith
  let R := 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
    Real.log N ^ (-2 * D + (F.natDegree : ℝ) ^ 2 - 2)
  have hlog : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hlog0 : 0 ≤ Real.log N := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans hlog
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfac : 0 ≤ H * R ^ (1 / K) * Real.log N ^ v := by positivity
  by_cases hlarge : N₀ ≤ N
  · have ht := hw N H α hlarge hH hHu (a : ℤ) q hq hcop happ
    change ‖Section2.polynomialKernel F N H α‖ ≤ C * H * R ^ (1 / K) * Real.log N ^ v at ht
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right (le_max_left C (2 / b)) hfac])
  · have hHT : H ≤ T := hHu.trans
      (Real.rpow_le_rpow hN0 (lt_of_not_ge hlarge).le (by positivity : (0 : ℝ) ≤ 1 / (F.natDegree : ℝ)))
    have hi : 1 / T ≤ R := by
      have hrec := one_div_le_one_div_of_le hH0 hHT
      have hrest : 0 ≤ 1 / (q : ℝ) + (q : ℝ) / H ^ F.natDegree +
          Real.log N ^ (-2 * D + (F.natDegree : ℝ) ^ 2 - 2) := by positivity
      dsimp [R]
      linarith
    have hbR : b ≤ R ^ (1 / K) * Real.log N ^ v :=
      mul_le_mul (Real.rpow_le_rpow (by positivity) hi (by positivity))
        (Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) hlog hv)
        (by positivity) (by positivity)
    have htwo : 2 ≤ max C (2 / b) * (R ^ (1 / K) * Real.log N ^ v) := by
      calc
        2 = (2 / b) * b := by field_simp
        _ ≤ max C (2 / b) * (R ^ (1 / K) * Real.log N ^ v) :=
          mul_le_mul (le_max_right _ _) hbR hb.le (by positivity)
    have ht := norm_polynomialKernel_le F N H α hN0 hH0.le
    calc
      _ ≤ 2 * H := ht.trans (by linarith)
      _ ≤ H * (max C (2 / b) * (R ^ (1 / K) * Real.log N ^ v)) :=
        by nlinarith [mul_le_mul_of_nonneg_left htwo hH0.le]
      _ = _ := by ring

/-- Page 482 named Lemma. Encoding A uses the existing Weyl decomposition.
CONDITIONAL ON the named higher degree analytic leaf. -/
theorem weylLemma (F : ℤ[X]) : EncA.WeylLemma F :=
  weylLemma_encA_of F (Decomp88.leaf_weyl F)

/-- Page 482 named Lemma. Encoding A's complete degree one case has no cited input. -/
theorem weylLemma_of_natDegree_one (F : ℤ[X]) (hdeg : F.natDegree = 1) :
    EncA.WeylLemma F :=
  weylLemma_encA_of F (Section2.weyl_of_natDegree_one F hdeg)

end
end LeanLab.Perelli1996.Decomp400d
