import LeanLab.ChenDoubleSieve.TupleInstance
import LeanLab.ChenDoubleSieve.Section3Supremum

/-!
# Positivity of the weighted normalizer

Source: https://arxiv.org/pdf/0705.1652, pages 9 and 10,
the definition of Theta and equation 3.7.
No prime distribution estimate is used. A tuple witness remains explicit.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Set
namespace LeanLab.ChenDoubleSieve.Wu04

/-- The logarithmic integral from two is positive above two. -/
theorem li_positive {x : ℝ} (hx : 2 < x) : 0 < li x := by
  apply intervalIntegral.integral_pos hx
  · apply ContinuousOn.inv₀
    · apply ContinuousOn.log continuousOn_id
      intro t ht
      change t ≠ 0
      linarith [ht.1]
    · intro t ht
      exact (log_pos (by linarith [ht.1] : 1 < t)).ne'
  · intro t ht
    exact inv_nonneg.mpr (log_nonneg (by linarith [ht.1]))
  · exact ⟨2, ⟨le_rfl, hx.le⟩, inv_pos.mpr (log_pos (by norm_num))⟩

/-- Every summand in Theta is positive for a nonempty admissible tuple. -/
theorem theta_summand_positive {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hU : UkData δ k N (n+1) V Δ)
    {t : Fin (n+1) → ℕ} (ht : t ∈ Wu41.Tset N (n+1) V Δ) :
    0 < CN (modulus t * N) / ((Nat.totient (modulus t) : ℝ) * log (Q δ N/modulus t)) := by
  have hd : 0 < modulus t := prod_pos fun j hj => (Wu41.T_prime ht j).pos
  have hphi : (0 : ℝ) < Nat.totient (modulus t) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hW : 1 < W δ k N := Real.one_lt_rpow hNr (pow_pos hδ _)
  have hlog := log_pos (hW.trans_le (residual_level_ge_W (by omega) hU ht))
  exact div_pos (CN_pos _) (mul_pos hphi hlog)

/-- An actual tuple witness supplies strict positivity of Theta. -/
theorem Theta_positive {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 3 ≤ N) (hδ : 0 < δ) (hU : UkData δ k N (n+1) V Δ)
    (hT : (Wu41.Tset N (n+1) V Δ).Nonempty) : 0 < Theta δ N (n+1) V Δ := by
  have hli : 0 < li (N : ℝ) := li_positive (by exact_mod_cast (show 2 < N by omega))
  have hs := sum_pos (fun t ht => theta_summand_positive (by omega) hδ hU ht) hT
  exact mul_pos (mul_pos (by norm_num) hli) hs

/-- Concrete positive normalizer with positive delta and a genuine prime tuple. -/
theorem Theta_positive_instance :
    0 < Theta (1/4) 65536 1 (fun _ => 3+positiveEps) (1+3/2*positiveEps) :=
  Theta_positive (by norm_num) (by norm_num) positive_delta_instance ⟨_, positive_tuple_mem⟩

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.li_positive
#print axioms LeanLab.ChenDoubleSieve.Wu04.theta_summand_positive
#print axioms LeanLab.ChenDoubleSieve.Wu04.Theta_positive
#print axioms LeanLab.ChenDoubleSieve.Wu04.Theta_positive_instance
