/-
P0083, pages 479 and 489. Convergence of the polynomial Euler factor.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Section3
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial Filter Topology

/-- Over a prime field a nonzero leading coefficient gives at most degree many roots. -/
theorem prime_roots_le_degree (F : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hlc : (F.leadingCoeff : ZMod p) ≠ 0) :
    (Roots.rootResidues F p).card ≤ F.natDegree := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let G := F.map (Int.castRingHom (ZMod p))
  have hG : G ≠ 0 := by
    intro hz
    apply hlc
    have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff F.natDegree) hz
    simpa [G] using hc
  rw [Roots.card_rootResidues_eq_rho]
  let S : Finset (ZMod p) := univ.filter (fun z => G.eval z = 0)
  have hS : S.val ⊆ G.roots := by
    intro z hz
    apply (Polynomial.mem_roots hG).2
    exact (Finset.mem_filter.mp hz).2
  exact (Polynomial.card_le_degree_of_subset_roots hS).trans Polynomial.natDegree_map_le

/-- The positive perturbation in the Euler product for C of F. -/
noncomputable def primeRootTerm (F : ℤ[X]) (p : {p : ℕ // p.Prime ∧ 2 < p}) : ℝ :=
  ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2))

/-- These perturbations are summable without the general composite modulus root estimate. -/
theorem summable_primeRootTerm (F : ℤ[X]) (hF : Admissible F) :
    Summable (primeRootTerm F) := by
  have hs : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      (3 * (F.natDegree : ℝ)) / (p.1 : ℝ) ^ 2) := by
    have hn : Summable (fun n : ℕ => (3 * (F.natDegree : ℝ)) / (n : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using
        (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left (3 * (F.natDegree : ℝ))
    exact hn.subtype _
  apply Summable.of_norm_bounded_eventually hs
  have hfin : {p : {p : ℕ // p.Prime ∧ 2 < p} | ¬ F.leadingCoeff.natAbs < p.1}.Finite := by
    apply Set.Finite.of_finite_image (f := Subtype.val) _ Subtype.val_injective.injOn
    apply (Set.finite_Iic F.leadingCoeff.natAbs).subset
    rintro _ ⟨p, hp, rfl⟩
    simp only [Set.mem_ofPred_eq, not_lt] at hp
    exact hp
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hp
  have hlc : (F.leadingCoeff : ZMod p.1) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have hdn : p.1 ∣ F.leadingCoeff.natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hd
    have hlead : 0 < F.leadingCoeff.natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt hF.2)
    exact (not_le_of_gt hp) (Nat.le_of_dvd hlead hdn)
  have hroots : ((Roots.rootResidues F p.1).card : ℝ) ≤ F.natDegree := by
    exact_mod_cast prime_roots_le_degree F p.1 p.2.1 hlc
  have hp3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
  have hden : 0 < (p.1 : ℝ) * ((p.1 : ℝ) - 2) := by
    apply mul_pos <;> linarith
  have hterm : 0 ≤ primeRootTerm F p := by
    exact div_nonneg (Nat.cast_nonneg _) hden.le
  rw [Real.norm_eq_abs, abs_of_nonneg hterm]
  unfold primeRootTerm
  calc ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2))
      ≤ (F.natDegree : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)) :=
        div_le_div_of_nonneg_right hroots hden.le
    _ ≤ (3 * (F.natDegree : ℝ)) / (p.1 : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ hden (by positivity)).2
      have hpos := mul_nonneg (Nat.cast_nonneg F.natDegree)
        (mul_nonneg (show (0 : ℝ) ≤ p.1 by positivity) (sub_nonneg.mpr hp3))
      nlinarith

/-- The odd prime Euler product in C of F converges. -/
theorem average_product_multipliable (F : ℤ[X]) (hF : Admissible F) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))) :=
  Real.multipliable_one_add_of_summable (summable_primeRootTerm F hF)

/-- C of F is positive whenever the polynomial has an even residue class. -/
theorem averageConstant_pos (F : ℤ[X]) (hF : Admissible F)
    (hρ : (Roots.rootResidues F 2).card ≠ 0) : 0 < averageConstant F := by
  have hprod : 1 ≤ ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 + primeRootTerm F p) := by
    apply ge_of_tendsto (average_product_multipliable F hF).hasProd
    filter_upwards with s
    calc (1 : ℝ) = ∏ _p ∈ s, (1 : ℝ) := by simp
      _ ≤ ∏ p ∈ s, (1 + primeRootTerm F p) := by
        apply Finset.prod_le_prod₀ (fun _ _ => by norm_num)
        intro p _
        have hpR : (2 : ℝ) < p.1 := by exact_mod_cast p.2.2
        have ht : 0 ≤ primeRootTerm F p := by
          unfold primeRootTerm
          apply div_nonneg (Nat.cast_nonneg _)
          apply mul_nonneg <;> linarith
        linarith
  have hlc : (0 : ℝ) < F.leadingCoeff := by exact_mod_cast hF.2
  have hρR : (0 : ℝ) < (Roots.rootResidues F 2).card := by
    exact_mod_cast Nat.pos_of_ne_zero hρ
  have hsing : 0 < singularConstant :=
    mul_pos (by norm_num) LeanLab.ChenExplicit.twinC_pos
  unfold averageConstant
  exact mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one hprod)

end LeanLab.Perelli1996.Section3
