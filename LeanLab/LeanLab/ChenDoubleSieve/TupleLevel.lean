import LeanLab.ChenDoubleSieve.Section3
import LeanLab.ChenDoubleSieve.PowerRemainder

/-!
# Tuple level bounds from Wu's prefix conditions

Source: https://arxiv.org/pdf/0705.1652, page 9, equation 3.1,
and pages 15 and 17, Lemmas 4.1 and 4.2.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Wu04

/-- The final prefix condition reserves a factor W after the full endpoint product. -/
theorem endpoint_product_level {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 0 < N) (hU : UkData δ k N (n+1) V Δ) :
    (∏ j, V j) * W δ k N ≤ Q δ N := by
  have hW : 0 < W δ k N := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hV : ∀ j, 0 < V j := fun j => hW.trans_le (hU.lower j)
  have hfilter : univ.filter (· < Fin.last n) = univ.erase (Fin.last n) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact ⟨fun h => ne_of_lt h, fun h => lt_of_le_of_ne (Fin.le_last j) h⟩
  have hlevel := hU.level (Fin.last n)
  rw [hfilter] at hlevel
  have hp : ∏ j, V j = (∏ j ∈ univ.erase (Fin.last n), V j) * V (Fin.last n) :=
    (prod_erase_mul _ _ (mem_univ _)).symm
  rw [hp]
  have hpre : 0 ≤ ∏ j ∈ univ.erase (Fin.last n), V j :=
    prod_nonneg fun j hj => (hV j).le
  have hlast : V (Fin.last n) * W δ k N ≤ V (Fin.last n) ^ 2 := by
    nlinarith [hU.lower (Fin.last n)]
  calc _ = (∏ j ∈ univ.erase (Fin.last n), V j) * (V (Fin.last n) * W δ k N) := by ring
       _ ≤ (∏ j ∈ univ.erase (Fin.last n), V j) * V (Fin.last n) ^ 2 :=
         mul_le_mul_of_nonneg_left hlast hpre
       _ ≤ Q δ N := hlevel

/-- A prime tuple modulus is bounded by the endpoint product. -/
theorem tuple_modulus_le {N i : ℕ} {V : Fin i → ℝ} {Δ : ℝ} {t : Fin i → ℕ}
    (ht : t ∈ Wu41.Tset N i V Δ) : (modulus t : ℝ) ≤ ∏ j, V j := by
  unfold modulus
  push_cast
  apply prod_le_prod₀ (fun j hj => Nat.cast_nonneg _)
  intro j hj
  exact (Wu41.mem_Pset.mp (Fintype.mem_piFinset.mp ht j)).2.2.1.le

/-- The residual level is at least W for every nonempty admissible prime tuple. -/
theorem residual_level_ge_W {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 0 < N) (hU : UkData δ k N (n+1) V Δ) {t : Fin (n+1) → ℕ}
    (ht : t ∈ Wu41.Tset N (n+1) V Δ) :
    W δ k N ≤ Q δ N / (modulus t : ℝ) := by
  have hd : 0 < (modulus t : ℝ) := by
    unfold modulus
    exact_mod_cast prod_pos (fun j hj => (Wu41.T_prime ht j).pos)
  rw [le_div_iff₀ hd]
  have hW : 0 ≤ W δ k N := (Real.rpow_pos_of_pos (by exact_mod_cast hN) _).le
  calc W δ k N * (modulus t : ℝ) ≤ W δ k N * (∏ j, V j) :=
         mul_le_mul_of_nonneg_left (tuple_modulus_le ht) hW
       _ = (∏ j, V j) * W δ k N := by ring
       _ ≤ Q δ N := endpoint_product_level hN hU

/-- The tenth root level supplies the precise remainder exponent used by Wu. -/
theorem residual_tenth_power {δ Δ : ℝ} {k N n : ℕ} {V : Fin (n+1) → ℝ}
    (hN : 0 < N) (hU : UkData δ k N (n+1) V Δ) {t : Fin (n+1) → ℕ}
    (ht : t ∈ Wu41.Tset N (n+1) V Δ) :
    (N : ℝ) ^ (δ ^ (k+1) / 10) ≤ (Q δ N / (modulus t : ℝ)) ^ (1/10 : ℝ) := by
  have hW : 0 ≤ W δ k N := (Real.rpow_pos_of_pos (by exact_mod_cast hN) _).le
  have he := Real.rpow_le_rpow hW (residual_level_ge_W hN hU ht) (by norm_num : (0 : ℝ) ≤ 1/10)
  simpa [W, ← Real.rpow_mul (by exact_mod_cast hN.le : (0 : ℝ) ≤ N), div_eq_mul_inv] using he

end LeanLab.ChenDoubleSieve.Wu04

#print axioms LeanLab.ChenDoubleSieve.Wu04.endpoint_product_level
#print axioms LeanLab.ChenDoubleSieve.Wu04.tuple_modulus_le
#print axioms LeanLab.ChenDoubleSieve.Wu04.residual_level_ge_W
#print axioms LeanLab.ChenDoubleSieve.Wu04.residual_tenth_power
