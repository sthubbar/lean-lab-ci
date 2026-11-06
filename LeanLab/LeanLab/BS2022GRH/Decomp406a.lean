/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Sharp large sieve reuse for journal p. 1225 display 15.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp374a
import LeanLab.Linnik.Decomp1532b

namespace LeanLab.BS2022GRH.Decomp406a
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp374a
noncomputable section

/-- Sparse coefficient specialization of the sharp large sieve used on p. 1225.
Zero extension preserves both the character sums and their coefficient energy. -/
theorem sparse_large_sieve (S : Finset ℕ) (a : ℕ → ℂ) (N Q : ℕ)
    (hS : S ⊆ Ioc 0 N) :
    (∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        ‖∑ n ∈ S, a n * χ n‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let b : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have hset : (Ioc 0 N).filter (fun n => n ∈ S) = S := by
    ext n
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hn => hS hn)
  have hsum {q : ℕ} (χ : DirichletCharacter ℂ q) :
      (∑ n ∈ Ioc 0 N, b n * χ n) = ∑ n ∈ S, a n * χ n := by
    simp only [b, ite_mul, zero_mul, ← sum_filter, hset]
  have henergy : (∑ n ∈ Ioc 0 N, ‖b n‖ ^ 2) = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    simp only [b, apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0),
      ← sum_filter, hset]
  simpa only [zero_add, hsum, henergy] using
    LeanLab.Linnik.Decomp1532b.large_sieve b 0 N Q

/-- A dyadic block is a subset of the sharp sieve conductor range, display 15. -/
theorem block_energy_le (S : Finset ℕ) (a : ℕ → ℂ) (X R : ℝ)
    (hX : 1 ≤ X) (hR : 1 ≤ R) (hS : S ⊆ nRange X) :
    blockEnergy R S a ≤ (X + 4 * R ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  let N := ⌈X⌉₊ - 1
  let Q := ⌈2 * R⌉₊ - 1
  have hN : S ⊆ Ioc 0 N := by
    intro n hn
    have hh := mem_Ico.mp (hS hn)
    exact mem_Ioc.mpr ⟨by omega, by dsimp [N]; omega⟩
  have hQ : blockModuli R ⊆ Icc 1 Q := by
    intro q hq
    have hh := mem_Ico.mp (mem_filter.mp hq).1
    exact mem_Icc.mpr ⟨by omega, by dsimp [Q]; omega⟩
  have hNX : (N : ℝ) ≤ X := by
    have hc : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    dsimp [N]
    rw [Nat.cast_sub hc, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one (show 0 ≤ X by linarith)]
  have hQR : (Q : ℝ) ≤ 2 * R := by
    have hc : 1 ≤ ⌈2 * R⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    dsimp [Q]
    rw [Nat.cast_sub hc, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one (show 0 ≤ 2 * R by linarith)]
  have hqsq : (Q : ℝ) ^ 2 ≤ 4 * R ^ 2 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q) hQR 2
    nlinarith
  calc
    blockEnergy R S a = ∑ q ∈ blockModuli R, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ S, a n * χ n‖ ^ 2 := by
      simp only [blockEnergy, blockCharacters, sum_sigma, mul_sum]
    _ ≤ ∑ q ∈ Icc 1 Q, ((q : ℝ) / q.totient) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ S, a n * χ n‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ S, ‖a n‖ ^ 2 :=
      sparse_large_sieve S a N Q hN
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sum_nonneg (fun _ _ => sq_nonneg _))

/-- Bounded coefficients on the positive support have energy at most X, display 15. -/
theorem coefficient_mass_le (S : Finset ℕ) (a : ℕ → ℂ) (X : ℝ)
    (hX : 1 ≤ X) (hS : S ⊆ nRange X) (ha : ∀ n, ‖a n‖ ≤ 1) :
    (∑ n ∈ S, ‖a n‖ ^ 2) ≤ X := by
  have hn : (S.card : ℝ) ≤ X := by
    have hcard := card_le_card hS
    have hceil : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    have hreal : ((nRange X).card : ℝ) ≤ X := by
      simp only [nRange, Nat.card_Ico]
      rw [Nat.cast_sub hceil, Nat.cast_one]
      linarith [Nat.ceil_lt_add_one (show 0 ≤ X by linarith)]
    exact (Nat.cast_le.mpr hcard).trans hreal
  calc
    _ ≤ ∑ _n ∈ S, (1 : ℝ) := sum_le_sum (fun n _ => by
      have hh := pow_le_pow_left₀ (norm_nonneg (a n)) (ha n) 2
      simpa using hh)
    _ = (S.card : ℝ) := by simp
    _ ≤ X := hn

/-- Exact statement of Decomp374a.coefficient_energy from the existing sharp sieve. -/
theorem coefficient_energy (c : ℕ → ℂ) (X R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hR : 1 ≤ R) :
    blockEnergy R ((nRange X).filter (fun n => Nat.Coprime n s)) c ≤
      (X + 4 * R ^ 2) * X := by
  have h1 : 1 ≤ X := by linarith
  have hs := filter_subset (fun n => Nat.Coprime n s) (nRange X)
  exact (block_energy_le _ c X R h1 hR hs).trans
    (mul_le_mul_of_nonneg_left (coefficient_mass_le _ c X h1 hs hc) (by positivity))

/-- Exact statement of Decomp374a.prime_energy from the same sharp sieve. -/
theorem prime_energy (Y Z R : ℝ) (s : ℕ)
    (hY : 25 ≤ Y) (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) ≤
      (Y + 4 * R ^ 2) * Y := by
  have hs : ((pRange Y Z).filter (fun p => ¬ p ∣ s)) ⊆ nRange Y := by
    intro p hp
    obtain ⟨hp, _⟩ := mem_filter.mp hp
    obtain ⟨hpr, hprime, _⟩ := mem_filter.mp hp
    exact mem_Ico.mpr ⟨hprime.one_lt.le, mem_range.mp hpr⟩
  have h1 : 1 ≤ Y := by linarith
  exact (block_energy_le _ (fun _ => 1) Y R h1 hR hs).trans
    (mul_le_mul_of_nonneg_left (coefficient_mass_le _ (fun _ => 1) Y h1 hs
      (fun _ => by simp)) (by positivity))

/-- Exact statement of Decomp148c.dyadic_block using proved moments, display 15. -/
theorem dyadic_block (c : ℕ → ℂ) (X Y Z R : ℝ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hR : 1 ≤ R) :
    (∑ r ∈ (Ico 3 ⌈2 * R⌉₊).filter (fun r : ℕ => R ≤ (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R := by
  apply (block_cauchy c X Y Z R s hR).trans
  apply div_le_div_of_nonneg_right _ (by linarith)
  apply Real.sqrt_le_sqrt
  have ha := coefficient_energy c X R s hc hX hR
  have hb := prime_energy Y Z R s hY hZ hZY hR
  have hnon : 0 ≤ blockEnergy R ((pRange Y Z).filter (fun p => ¬ p ∣ s)) (fun _ => 1) := by
    unfold blockEnergy
    exact sum_nonneg (fun _ _ => by positivity)
  have hx : 0 ≤ (X + 4 * R ^ 2) * X := by positivity
  convert mul_le_mul ha hb hnon hx using 1 <;> ring

end
end LeanLab.BS2022GRH.Decomp406a

#print axioms LeanLab.BS2022GRH.Decomp406a.sparse_large_sieve
#print axioms LeanLab.BS2022GRH.Decomp406a.block_energy_le
#print axioms LeanLab.BS2022GRH.Decomp406a.coefficient_mass_le
#print axioms LeanLab.BS2022GRH.Decomp406a.coefficient_energy
#print axioms LeanLab.BS2022GRH.Decomp406a.prime_energy
#print axioms LeanLab.BS2022GRH.Decomp406a.dyadic_block
