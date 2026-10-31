/-
P0083, page 488, equation 35 restricted to squarefree moduli.
This is the restriction needed after multiplication by Moebius squared.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.RootCRT
import LeanLab.Perelli1996.EulerConvergence

namespace LeanLab.Perelli1996.Roots
open Finset Real Polynomial Filter Topology

/-- The squarefree version of the root estimate used in equation 37. -/
def SquarefreeRootGrowth (F : ℤ[X]) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, Squarefree d →
    ((rootResidues F d).card : ℝ) ≤ C * (d : ℝ) ^ ε

/-- The root estimate needed on the support of f is elementary and unconditional. -/
theorem squarefreeRootGrowth (F : ℤ[X]) (hF : Admissible F) : SquarefreeRootGrowth F := by
  classical
  intro ε hε
  have ht := (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (F.natDegree : ℝ))
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ht
  let T : ℕ := max F.leadingCoeff.natAbs ⌈X⌉₊
  let A (p : ℕ) : ℝ := if p ≤ T then max 1 ((rootResidues F p).card : ℝ) else 1
  let C : ℝ := ∏ p ∈ range (T + 1), A p
  have hA (p : ℕ) : 1 ≤ A p := by dsimp [A]; split_ifs <;> simp
  have hC : 1 ≤ C := by
    calc (1 : ℝ) = ∏ _p ∈ range (T + 1), (1 : ℝ) := by simp
      _ ≤ C := Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun p _ => hA p)
  have hprodA (s : Finset ℕ) : ∏ p ∈ s, A p ≤ C := by
    have heq : (∏ p ∈ s ∩ range (T + 1), A p) = ∏ p ∈ s, A p := by
      apply Finset.prod_subset Finset.inter_subset_left
      intro p hp hpnot
      have hpT : ¬ p ≤ T := by
        intro h
        exact hpnot (Finset.mem_inter.mpr ⟨hp, Finset.mem_range.mpr (by omega)⟩)
      simp [A, hpT]
    rw [← heq]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ Finset.inter_subset_right
      (fun p _ => le_trans (by norm_num) (hA p)) (fun p _ _ => hA p)
  have hpbound (p : ℕ) (hp : p.Prime) :
      ((rootResidues F p).card : ℝ) ≤ A p * (p : ℝ) ^ ε := by
    by_cases hpT : p ≤ T
    · have hρ : ((rootResidues F p).card : ℝ) ≤ A p := by
        simp only [A, if_pos hpT]
        exact le_max_right _ _
      have hpPow : 1 ≤ (p : ℝ) ^ ε :=
        Real.one_le_rpow (by exact_mod_cast hp.one_le) hε.le
      have hA0 : 0 ≤ A p := le_trans (by norm_num) (hA p)
      nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hpPow)]
    · have hTp : T < p := lt_of_not_ge hpT
      have hpLc : F.leadingCoeff.natAbs < p := lt_of_le_of_lt (le_max_left _ _) hTp
      have hlc : (F.leadingCoeff : ZMod p) ≠ 0 := by
        rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
        intro hd
        have hdn : p ∣ F.leadingCoeff.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
        have hlead : 0 < F.leadingCoeff.natAbs := Int.natAbs_pos.mpr (ne_of_gt hF.2)
        exact (not_le_of_gt hpLc) (Nat.le_of_dvd hlead hdn)
      have hρ : ((rootResidues F p).card : ℝ) ≤ F.natDegree := by
        exact_mod_cast Section3.prime_roots_le_degree F p hp hlc
      have hpX : X ≤ (p : ℝ) := by
        have hpceil : ⌈X⌉₊ ≤ p := le_trans (le_max_right _ _) hTp.le
        exact (Nat.le_ceil X).trans (by exact_mod_cast hpceil)
      calc ((rootResidues F p).card : ℝ) ≤ F.natDegree := hρ
        _ ≤ (p : ℝ) ^ ε := hX p hpX
        _ = A p * (p : ℝ) ^ ε := by simp [A, hpT]
  let af : ArithmeticFunction ℕ := ⟨fun k => (rootResidues F k).card, by simp [rootResidues]⟩
  have haf : af.IsMultiplicative := by
    refine ⟨by simp [af, rootResidues], fun {m n} hcop => ?_⟩
    change (rootResidues F (m * n)).card = (rootResidues F m).card * (rootResidues F n).card
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [rootResidues]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [rootResidues]
    exact root_count_mul F m n hm hn hcop
  refine ⟨C, by linarith, fun d hd => ?_⟩
  have hfactor : ((rootResidues F d).card : ℝ) =
      ∏ p ∈ d.primeFactors, ((rootResidues F p).card : ℝ) := by
    have heq := haf.prod_primeFactors hd
    change (∏ p ∈ d.primeFactors, (rootResidues F p).card) = (rootResidues F d).card at heq
    exact_mod_cast heq.symm
  have hpow : (∏ p ∈ d.primeFactors, (p : ℝ) ^ ε) = (d : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε,
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  calc ((rootResidues F d).card : ℝ) = ∏ p ∈ d.primeFactors, ((rootResidues F p).card : ℝ) := hfactor
    _ ≤ ∏ p ∈ d.primeFactors, A p * (p : ℝ) ^ ε := by
      apply Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _)
      intro p hp
      exact hpbound p (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ d.primeFactors, A p) * (d : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpow]
    _ ≤ C * (d : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (hprodA d.primeFactors) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

end LeanLab.Perelli1996.Roots
