/-
Concrete checks of the task279 source twins.
These are source instances, not an extension of a Goldbach computation range.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp279b

namespace LeanLab.Languasco2004.Instances279
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Jia page 262 display 43: the pair 2 and 2 is counted at N = 3, Y = 2. -/
theorem jia_representation_instance : Decomp279a.representations 3 2 4 = 1 := by
  norm_num [Decomp279a.representations, Finset.range_add_one, Finset.filter_insert,
    Finset.filter_singleton]

/-- Jia page 262 sieve definition: at cutoff 1 the two admissible a are 1 and 2. -/
theorem jia_sifted_instance : Decomp279a.sifted 3 2 4 1 1 = 2 := by
  have hs : ((Icc 1 4).filter (fun a : ℕ => 1 ∣ a ∧ (4 - a).Prime ∧
      (3 : ℝ) - 2 < ((4 - a : ℕ) : ℝ) ∧ ((4 - a : ℕ) : ℝ) ≤ 3 ∧
      ∀ p : ℕ, p.Prime → (p : ℝ) < 1 → ¬ p ∣ 4 → ¬ p ∣ a)) = {1, 2} := by
    ext a
    have hprime : ∀ p : ℕ, p.Prime → ¬ (p : ℝ) < 1 := by
      intro p hp h
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    simp only [Finset.mem_filter, Finset.mem_Icc, one_dvd,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ha, ha4⟩, hprimea, hlow, hhigh, _⟩
      interval_cases a <;> norm_num at *
    · intro h
      rcases h with rfl | rfl <;> norm_num
      all_goals intro p hp h; subst p; exact False.elim ((by decide : ¬ Nat.Prime 0) hp)
  unfold Decomp279a.sifted
  rw [hs]
  norm_num

/-- PP page 43: the only pair at N = Y = 5 and m = 10 is 5 plus 5. -/
theorem pp_pairs_instance : Decomp279b.pairs 5 5 10 = {5} := by
  ext h
  simp only [Decomp279b.pairs, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h0, h10⟩, _, hh, hk⟩
    have hh' : h ≤ 5 := by exact_mod_cast hh
    have hk' : 10 - h ≤ 5 := by exact_mod_cast hk
    omega
  · rintro rfl
    norm_num

/-- PP page 43: M star is nonzero in the displayed pair instance. -/
theorem pp_unweighted_instance : Decomp279b.unweightedCount 5 5 10 = 1 := by
  simp [Decomp279b.unweightedCount, pp_pairs_instance]

/-- PP page 44: the two expressions for the basic interval length agree. -/
theorem pp_length_identity (N η : ℝ) (hN : 0 < N) :
    Decomp279b.windowLength N η = Decomp279b.localization N η ^ (1 / 3 + η) := by
  unfold Decomp279b.windowLength Decomp279b.localization Decomp279b.lengthExponent
  rw [Real.rpow_mul hN.le]

/-- PP page 43: the chosen major arc centre exists for concrete positive parameters. -/
theorem pp_major_centre_instance :
    (1 : ℝ) ∈ Decomp279b.majorSet (Real.exp 2) 10 1 := by
  refine ⟨1, 1, by norm_num, ?_, by norm_num, by norm_num, by decide, ?_⟩ <;>
    norm_num [Real.log_exp]

#print axioms jia_representation_instance
#print axioms jia_sifted_instance
#print axioms pp_pairs_instance
#print axioms pp_unweighted_instance
#print axioms pp_length_identity
#print axioms pp_major_centre_instance
end
end LeanLab.Languasco2004.Instances279
