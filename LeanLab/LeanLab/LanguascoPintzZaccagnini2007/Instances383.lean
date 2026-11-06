import LeanLab.LanguascoPintzZaccagnini2007.Decomp383a

/-!
Concrete nonempty instances for the arithmetic supply of displays 16 to 24.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real

/-- Journal page 772 display 2 at the positive even input n equals 2. -/
theorem singular_two383 : Sing 2 = 2 * LeanLab.ChenExplicit.twinC := by
  rw [singular_factorization383 even_two (by norm_num)]
  norm_num [H, Nat.prime_two.primeFactors, Finset.filter_singleton]

/-- Journal page 777 display 17. Retaining only d equals 1 counts all M exponents. -/
theorem divisorBlock_singleton383 (M N : ℕ) : divisorBlock383 1 M N 2 = M := by
  classical
  have hF : (range 2).filter OddSqf = {1} := by
    have hr : range 2 = ({0, 1} : Finset ℕ) := by decide
    have h0 : ¬ OddSqf 0 := by norm_num [OddSqf]
    simp [hr, Finset.filter_insert, Finset.filter_singleton, h0, oddSqf_1]
  simp [divisorBlock383, hF, fd_one, residueTupleCount131, Fintype.card_piFinset]

/-- Journal page 777 display 16. A nonempty tuple window with positive residuals. -/
theorem tuple_instance383 :
    (fun _ : Fin 1 => (1 : ℕ)) ∈ tuples131 1 16 ∧
      tuplePower131 (fun _ : Fin 1 => (1 : ℕ)) = 2 ∧
      16 ∈ evenJ131 16 := by
  have hL : Lg 16 = 4 := by
    unfold Lg
    norm_num only [Nat.cast_ofNat]
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.logb_pow]
    norm_num
  have hM : ⌊Lg 16 - √(Lg 16)⌋₊ = 2 := by rw [hL]; norm_num
  norm_num [tuples131, hM, exponentTuples131, Fintype.mem_piFinset, tuplePower131, evenJ131]

/-- Journal page 777 display 20. The quantitative tail hypotheses hold
at the positive cutoff X and N equal to 256 with one exponent. -/
theorem error_window_instance383 :
    256 ∈ evenJ131 256 ∧ 2 ≤ Lg 256 ∧
      6 * (0 + 1) * 2 ^ ⌊Lg 256 - √(Lg 256)⌋₊ ≤ (256 : ℕ) := by
  have hL : Lg 256 = 8 := by
    unfold Lg
    norm_num only [Nat.cast_ofNat]
    rw [show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.logb_pow]
    norm_num
  have hslo : (2 : ℝ) < √8 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hshi : √(8 : ℝ) ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hM : ⌊Lg 256 - √(Lg 256)⌋₊ = 5 := by
    rw [hL]
    exact (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  rw [hM]
  norm_num [evenJ131, hL]

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.singular_two383
#print axioms LeanLab.LPZ2007.divisorBlock_singleton383
#print axioms LeanLab.LPZ2007.tuple_instance383

#print axioms LeanLab.LPZ2007.error_window_instance383
