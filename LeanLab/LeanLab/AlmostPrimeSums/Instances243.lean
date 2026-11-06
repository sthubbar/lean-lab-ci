import LeanLab.AlmostPrimeSums.Decomp243c
import LeanLab.AlmostPrimeSums.Remainder243
import LeanLab.AlmostPrimeSums.Error243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Concrete nonempty domains and exact supply type checks.
The global distribution hypotheses are cited inputs. No example asserts them.
-/

open Finset Real Filter Topology LeanLab.ChenExplicit
open LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.AlmostPrimeSums.Decomp243a
open LeanLab.AlmostPrimeSums.Remainder243

example : sieveProduct 10 1 = (5 / 12 : ℝ) := by
  norm_num [sieveProduct, Finset.prod_filter, Finset.prod_range_succ]

example : 0 < idealMass 2 (1 / 8) := by
  exact mul_pos (div_pos (by norm_num) (log_pos (by norm_num))) (sieveProduct_pos _ _)

example : sieveLevel 4 0 = 2 := by norm_num [sieveLevel]

example : 0 < sieveError 2 := by
  exact div_pos (Mchen_pos 2 (by norm_num)) (rpow_pos_of_pos (log_pos (by norm_num)) _)

example : Tendsto (fun N : ℕ => idealMass N (1 / 8) / Mchen N) atTop
    (𝓝 (4 / exp eulerMascheroniConstant)) := by
  convert idealMass_ratio (1 / 8) (by norm_num) (by norm_num) using 1 <;> ring

example : Tendsto (fun N : ℕ => lowerMain N 1 / Mchen N) atTop (𝓝 (2 * log 3)) :=
  lowerMain_ratio 1

example : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → (2 - η : ℝ) ≤ 2 := by
  simpa using lower_from_limits (fun _ => 2) (fun _ => 0) (fun _ => 1) (fun _ => 2) 2 3
    (Eventually.of_forall (fun _ => zero_lt_one))
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)))
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    (Eventually.of_forall (by intro N hN; norm_num))

example : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → (2 : ℝ) ≤ 2 + η := by
  simpa using LeanLab.AlmostPrimeSums.Decomp243b.upper_from_limits
    (fun _ => 2) (fun _ => 0) (fun _ => 1) (fun _ => 2) 2 3
    (Eventually.of_forall (fun _ => zero_lt_one))
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)))
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    (Eventually.of_forall (by intro N hN; norm_num))

example : 867 ∈ TSet 4096 ((4096 : ℝ) ^ ((1 : ℝ) / 8))
    ((4096 : ℝ) ^ ((1 : ℝ) / 3)) := by
  have hcube : (4096 : ℝ) ^ ((1 : ℝ) / 3) = 16 := by
    rw [show (4096 : ℝ) = 16 ^ (3 : ℝ) by norm_num, ← rpow_mul (by norm_num)]
    norm_num
  have hcut : (4096 : ℝ) ^ ((1 : ℝ) / 8) ≤ 3 := by
    have h := rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4096)
      (by norm_num : (4096 : ℝ) ≤ 3 ^ (8 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 3)] at h
    norm_num at h
    exact h
  simp only [TSet, mem_filter, mem_range, hcube]
  refine ⟨by norm_num, by norm_num, 3, 17, 17, ?_⟩
  norm_num [hcut]

example : Set.InjOn (fun qd : ℕ × ℕ => qd.1 * qd.2)
    (({5, 7} : Finset ℕ).product {1, 2, 3}) := by
  apply large_prime_product_injective _ _ 5
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
      norm_num [(by decide : Nat.Prime 2).primeFactors, (by decide : Nat.Prime 3).primeFactors]

example : (∑ qd ∈ (({5, 7} : Finset ℕ).product {1, 2, 3}).filter
    (fun qd => qd.1 * qd.2 ≤ 21), |(1 : ℝ)|) ≤ ∑ d ∈ Icc 1 21, |(1 : ℝ)| := by
  apply double_absolute_remainder_le _ _ 5 21 (fun _ => 1)
  · intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl <;> norm_num
  · intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
      norm_num [(by decide : Nat.Prime 2).primeFactors, (by decide : Nat.Prime 3).primeFactors]

example : ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ ((7 : ℝ) / 8) * (1 + log N) ^ 2 ≤ sieveError N := by
  simpa using LeanLab.AlmostPrimeSums.Error243.switched_error_small 1 (by norm_num)

#check (LeanLab.AlmostPrimeSums.Decomp243a.SA_lower :
  LevelBV → ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
    (2 * log 3 - η) * Mchen N ≤ SA N ((N : ℝ) ^ ((1 : ℝ) / 8)))

#check (LeanLab.AlmostPrimeSums.Decomp243b.sumSAq_upper :
  LevelBV → ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
    (sumSAq N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      ≤ (log 6 + η) * Mchen N)

#check (LeanLab.AlmostPrimeSums.Decomp243c.SB_upper :
  LevelBVTriples → ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N →
    (SB N ((N : ℝ) ^ ((1 : ℝ) / 8)) ((N : ℝ) ^ ((1 : ℝ) / 3)) : ℝ) / 2
      ≤ ((∫ β in (1 / 8 : ℝ)..(1 / 3), log (2 - 3 * β) / (β * (1 - β))) + η) * Mchen N)
