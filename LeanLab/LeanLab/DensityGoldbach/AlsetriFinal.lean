/-
P0085 Alsetri 2025, arXiv 2505.09648: Proposition 3.1 for every squarefree m coprime to 30
(`half31_coprime30`: base 1 or 7, then the fiber step for each prime ≥ 11), and Theorem 1.2,
`Alsetri12 m`, for every odd squarefree m with 3 | m and 5 ∤ m (`alsetri12_of_coprime5`).
The case 5 | m needs the paper's Proposition 3.2 at modulus 15 and is not covered here.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.AlsetriMain
import LeanLab.DensityGoldbach.AlsetriLemma21Six

open Finset

namespace LeanLab.DensityGoldbach

/-- **Alsetri Proposition 3.1**: every squarefree `m` coprime to `30`. -/
theorem half31_coprime30 (m : ℕ) [NeZero m] (hsq : Squarefree m) (h30 : m.Coprime 30) :
    Half31 m := by
  have hm : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsq
  have hfac : ∀ p ∈ m.primeFactors, p.Prime ∧ p.Coprime 30 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp,
      Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) h30⟩
  by_cases h7 : 7 ∈ m.primeFactors
  · have hS : ∀ p ∈ m.primeFactors.erase 7, p.Prime ∧ 11 ≤ p := fun p hp => by
      obtain ⟨hne, hp'⟩ := mem_erase.1 hp
      exact ⟨(hfac p hp').1, prime_ge_eleven (hfac p hp').1 (hfac p hp').2 hne⟩
    have hc : ∀ p ∈ m.primeFactors.erase 7, (7 : ℕ).Coprime p := fun p hp =>
      (Nat.coprime_primes (by norm_num) (hS p hp).1).2 (fun h => (mem_erase.1 hp).1 h.symm)
    have he : 7 * ∏ p ∈ m.primeFactors.erase 7, p = m := by
      rw [mul_prod_erase m.primeFactors (fun p => p) h7, hm]
    exact half31_prod 7 half31_seven _ hS hc m he.symm inferInstance
  · have hS : ∀ p ∈ m.primeFactors, p.Prime ∧ 11 ≤ p := fun p hp =>
      ⟨(hfac p hp).1, prime_ge_eleven (hfac p hp).1 (hfac p hp).2 (fun h => h7 (h ▸ hp))⟩
    have he : 1 * ∏ p ∈ m.primeFactors, p = m := by rw [one_mul, hm]
    exact half31_prod 1 half31_one _ hS (fun p _ => Nat.coprime_one_left p) m he.symm
      inferInstance

/-- **P0085 Theorem 1.2** for every odd squarefree `m` with `3 ∣ m` and `5 ∤ m`. -/
theorem alsetri12_of_coprime5 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (h3 : 3 ∣ m) (h5 : ¬ 5 ∣ m) : Alsetri12 m := by
  obtain ⟨m', rfl⟩ := h3
  have hm' : m' ≠ 0 := fun h => NeZero.ne (3 * m') (by simp [h])
  have : NeZero m' := ⟨hm'⟩
  have hsq' : Squarefree m' := hsq.of_mul_right
  have n3 : ¬ 3 ∣ m' := by
    rintro ⟨k, rfl⟩
    have := hsq 3 ⟨k, by ring⟩
    exact absurd (Nat.isUnit_iff.1 this) (by norm_num)
  have n2 : ¬ 2 ∣ m' := by
    rintro ⟨k, rfl⟩
    obtain ⟨r, hr⟩ := hodd
    omega
  have n5 : ¬ 5 ∣ m' := fun hd => h5 (Dvd.dvd.mul_left hd 3)
  have c2 : Nat.Coprime 2 m' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 n2
  have c3 : Nat.Coprime 3 m' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 n3
  have c5 : Nat.Coprime 5 m' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 n5
  have c30 : Nat.Coprime m' 30 := by
    have : Nat.Coprime (2 * 3 * 5) m' :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_left c2 c3) c5
    exact this.symm
  exact alsetri12_of_half31 m' c3 (half31_coprime30 m' hsq' c30)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.half31_coprime30
#print axioms LeanLab.DensityGoldbach.alsetri12_of_coprime5
