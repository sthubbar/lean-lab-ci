/-
P0038 Shao 2012, sharpness of 5/8 in Corollary 1.5 for every m = 15 k with gcd(k, 15) = 1:
the reduced residues whose class mod 15 lies in {1, 2, 4, 7, 13} are exactly 5/8 of φ(m), and
no three of them sum to the class of (14, 0) under CRT. Shao gives the example mod 15 only.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0131, idea I-0015.
-/
import LeanLab.DensityGoldbach.Prop31Step
import LeanLab.DensityGoldbach.Local

open Finset

namespace LeanLab.DensityGoldbach

lemma card_unitsMod_eq (m : ℕ) [NeZero m] : #(unitsMod m) = m.totient := by
  rw [unitsMod, ← ZMod.card_units_eq_totient, ← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := fun u => IsUnit.unit (mem_filter.1 u.2).2
      invFun := fun u => ⟨(u : ZMod m), mem_filter.2 ⟨mem_univ _, u.isUnit⟩⟩
      left_inv := fun u => by simp
      right_inv := fun u => by ext; simp }

/-- **Cor 1.5 is sharp for every `m = 15 k`, `gcd(k, 15) = 1`.** -/
theorem cor15_sharp (k : ℕ) [NeZero k] [NeZero (15 * k)] (hk : Nat.Coprime 15 k) :
    ∃ A ⊆ unitsMod (15 * k), 8 * #A = 5 * (15 * k).totient ∧
      ∃ x : ZMod (15 * k), ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b + c ≠ x := by
  have : NeZero 15 := ⟨by norm_num⟩
  set e := ZMod.chineseRemainder hk with he
  set A := (unitsMod (15 * k)).filter (fun r => (e r).1 ∈ S15) with hA
  refine ⟨A, filter_subset _ _, ?_, e.symm (14, 0), ?_⟩
  · have hc : (#A : ℝ) = ∑ r ∈ unitsMod (15 * k), (if (e r).1 ∈ S15 then (1 : ℝ) else 0) := by
      rw [sum_boole, Nat.cast_inj]
    rw [sum_unitsMod_crt hk] at hc
    rw [← he] at hc
    simp only [RingEquiv.apply_symm_apply, sum_const, nsmul_eq_mul, card_unitsMod_eq k] at hc
    rw [← mul_sum, sum_boole] at hc
    have h5 : ((unitsMod 15).filter (fun b => b ∈ S15)) = S15 := by
      rw [filter_mem_eq_inter, inter_eq_right.2 S15_sub_units]
    rw [h5, card_S15] at hc
    rw [Nat.totient_mul hk, totient15]
    have : (8 * #A : ℝ) = 5 * (8 * k.totient) := by rw [hc]; push_cast; ring
    exact_mod_cast this
  · intro a ha b hb c hc h
    have h1 := congrArg (fun z => (e z).1) h
    simp only [map_add, Prod.fst_add, RingEquiv.apply_symm_apply] at h1
    exact S15_misses_14 _ (mem_filter.1 ha).2 _ (mem_filter.1 hb).2 _ (mem_filter.1 hc).2 h1

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.cor15_sharp
