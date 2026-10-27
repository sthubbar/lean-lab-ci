import LeanLab.LanguascoPintzZaccagnini2007.Minor131
import LeanLab.LanguascoPintzZaccagnini2007.Residues131

/-!
Concrete instances for task131 statements.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

/-- A concrete admissible arc parameter with a strict endpoint gap. -/
theorem parameter_instance131 :
    AdmissibleP131 32 4 ∧ (4 : ℝ) + 2 ≤ arcQ131 32 4 := by
  have he : (32 : ℝ) ^ ((2 : ℝ) / 5) = 4 := by
    calc (32 : ℝ) ^ ((2 : ℝ) / 5) = ((2 : ℝ) ^ (5 : ℝ)) ^ ((2 : ℝ) / 5) := by norm_num
      _ = (2 : ℝ) ^ (2 : ℝ) := by rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ = 4 := by norm_num
  constructor
  · refine ⟨he.le, ?_⟩
    rw [← he]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · norm_num [arcQ131]

/-- A nonempty even interval for the new exception statements. -/
theorem interval_instance131 : 32 ∈ evenJ131 32 := by
  norm_num [evenJ131]

/-- A concrete interior minor arc point for the new Vaughan estimate. -/
theorem minor_point_instance131 :
    (1 / 5 : ℝ) ∈ Set.Ioo (1 / arcQ131 32 4) (1 / arcQ131 32 4 + 1) ∧
      (1 / 5 : ℝ) ∉ majorArcs131 32 4 := by
  constructor
  · norm_num [arcQ131]
  · rintro ⟨q, a, hq, hq4, ha, hc, hα⟩
    have hq4' : q ≤ 4 := by exact_mod_cast hq4
    obtain ⟨ha1, haq⟩ := mem_Icc.mp ha
    interval_cases q <;> interval_cases a <;> norm_num [arcQ131] at *

/-- A concrete reduced approximation satisfying every hypothesis of Lemma 6.3. -/
theorem lemma63_hyp_instance131 :
    2 ≤ (32 : ℕ) ∧ 1 ≤ (1 : ℕ) ∧ (1 : ℕ) ≤ 32 ∧
      Int.gcd 0 1 = 1 ∧ |(0 : ℝ) - 0 / 1| < 1 / (1 : ℝ) ^ 2 := by
  norm_num

/-- The first nontrivial finite residue modulus is three. -/
theorem residueModulus_four131 : residueModulus131 4 = 3 := by
  classical
  have hr : range 4 = ({0, 1, 2, 3} : Finset ℕ) := by decide
  have h0 : ¬ OddSqf 0 := by norm_num [OddSqf]
  have h2 : ¬ OddSqf 2 := by norm_num [OddSqf]
  simp [residueModulus131, hr, Finset.filter_insert, Finset.filter_singleton, h0, h2, oddSqf_1, oddSqf_3]

/-- Nonidentical integers satisfy a concrete finite residue matching condition. -/
theorem finite_residue_instance131 (k : ℕ) : partialC131 4 k 4 = partialC131 4 k 7 := by
  apply partialC_periodic131
  rw [residueModulus_four131]
  norm_num

end LeanLab.LPZ2007
