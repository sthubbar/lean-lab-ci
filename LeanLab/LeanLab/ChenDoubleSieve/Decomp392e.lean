import LeanLab.ChenDoubleSieve.Decomp363d

/-!
Finite lower rows obtained by the even prefix stopping rule.
Source: https://doi.org/10.4064/aa-37-1-307-320, page 313 lower coefficient
and Lemma 2, with the sieve definition on Wu 2004 page 5.
These recursive rows give a finite lower bound without a main term estimate.
No equality with a divisor coefficient expansion is asserted here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset List
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task392
open Task275 Task348 Task363

/-- The lower and upper recursive rows. Including a factor from a lower row
always continues. Including one from an upper row continues only when its
cube passes the lower Rosser support test. -/
def rosserRows : List ℕ → ℕ → ℝ → ℕ → ℝ × ℝ
  | [], _, _, _ => (1, 1)
  | p :: ps, m, D, a =>
    let r0 := rosserRows ps m D a
    let r1 := rosserRows ps (m * p) D a
    (r0.1 - if p ∣ a then r1.2 else 0,
      r0.2 - if p ∣ a ∧ (m : ℝ) * (p : ℝ) ^ 3 < D then r1.1 else 0)

/-- The recursive rows bracket the exact sifting indicator for every list.
The prefix product and the cutoff need no extra hypotheses. -/
theorem rosserRows_bounds (ps : List ℕ) (m : ℕ) (D : ℝ) (a : ℕ) :
    (rosserRows ps m D a).1 ≤ (if ∀ p ∈ ps, ¬p ∣ a then (1 : ℝ) else 0) ∧
      (if ∀ p ∈ ps, ¬p ∣ a then (1 : ℝ) else 0) ≤ (rosserRows ps m D a).2 := by
  induction ps generalizing m with
  | nil => simp [rosserRows]
  | cons p ps ih =>
    have h0 := ih m
    have h1 := ih (m * p)
    by_cases hp : p ∣ a
    · by_cases hc : (m : ℝ) * (p : ℝ) ^ 3 < D
      · have hh : (rosserRows ps m D a).1 - (rosserRows ps (m * p) D a).2 ≤ 0 ∧
            0 ≤ (rosserRows ps m D a).2 - (rosserRows ps (m * p) D a).1 :=
          ⟨by linarith [h0.1, h1.2], by linarith [h0.2, h1.1]⟩
        simpa [rosserRows, hp, hc] using hh
      · have hi : (0 : ℝ) ≤ if ∀ q ∈ ps, ¬q ∣ a then (1 : ℝ) else 0 := by
          split_ifs <;> norm_num
        have hh : (rosserRows ps m D a).1 - (rosserRows ps (m * p) D a).2 ≤ 0 ∧
            0 ≤ (rosserRows ps m D a).2 :=
          ⟨by linarith [h0.1, h1.2], hi.trans h0.2⟩
        simpa [rosserRows, hp, hc] using hh
    · simpa [rosserRows, hp] using h0

/-- A sifted element avoids exactly the finite prime list used by these rows. -/
theorem sifted_iff_avoids_list (N a : ℕ) (z : ℝ) :
    Wu41.Sifted N z a ↔ ∀ p ∈ (Wu41.PS N 0 z).toList, ¬p ∣ a := by
  constructor
  · intro h p hp
    obtain ⟨hprime, _, hpz, hcop⟩ := Wu41.mem_PS.mp (Finset.mem_toList.mp hp)
    exact h p hprime hpz (hprime.coprime_iff_not_dvd.mp hcop)
  · intro h p hprime hpz hnot
    apply h p
    apply Finset.mem_toList.mpr
    exact Wu41.mem_PS.mpr ⟨hprime, Nat.cast_nonneg _, hpz,
      hprime.coprime_iff_not_dvd.mpr hnot⟩

/-- Summing the recursive lower row bounds the actual finite sifted count. -/
theorem rosserRows_sum_lower (A : Finset ℕ) (N : ℕ) (z D : ℝ) :
    ∑ a ∈ A, (rosserRows (Wu41.PS N 0 z).toList 1 D a).1 ≤
      (Wu41.S A 1 N z : ℝ) := by
  rw [Wu41.S_eq_sum]
  push_cast
  apply Finset.sum_le_sum
  intro a ha
  have h := (rosserRows_bounds (Wu41.PS N 0 z).toList 1 D a).1
  simpa only [one_dvd, true_and, sifted_iff_avoids_list] using h

/-- The recursive row is a lower bound for the exact coordinate of the unit.
This uses no linear sieve function and no distribution estimate. -/
theorem rosserRows_lower_sieve0 (B : ℝ) (N : ℕ) :
    ∑ a ∈ primeSequence N,
      (rosserRows (Wu41.PS N 0 ((N : ℝ) ^ kappa1)).toList 1 (sieveLevel B N) a).1 ≤
        sieveTerms N 0 := by
  simpa only [sieveTerms, Matrix.cons_val_zero] using
    rosserRows_sum_lower (primeSequence N) N ((N : ℝ) ^ kappa1) (sieveLevel B N)

/-- A nonempty prime list with a genuine even stopping test gives a tight lower row. -/
theorem rosserRows_instance :
    (rosserRows [5, 3, 2] 1 150 30).1 = 0 ∧
      (rosserRows [5, 3, 2] 1 150 30).2 = 0 := by
  norm_num [rosserRows]

/-- The actual unit has a nonempty sifting prime domain at an even N.
This witness avoids an empty prime product at small N. -/
theorem sieve0_prime_instance :
    Even (4 ^ 12 : ℕ) ∧
      3 ∈ Wu41.PS (4 ^ 12) 0 (((4 ^ 12 : ℕ) : ℝ) ^ kappa1) := by
  constructor
  · norm_num
  have hz : (((4 ^ 12 : ℕ) : ℝ) ^ kappa1) = 4 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num [kappa1]
  rw [hz]
  apply Wu41.mem_PS.mpr
  norm_num

/-- The finite lower row bound also holds in the decreasing prime order
used by the explicit Rosser coefficient. -/
theorem rosserRows_sorted_sum_lower (A : Finset ℕ) (N : ℕ) (z D : ℝ) :
    ∑ a ∈ A, (rosserRows ((Wu41.PS N 0 z).sort (· ≥ ·)) 1 D a).1 ≤
      (Wu41.S A 1 N z : ℝ) := by
  rw [Wu41.S_eq_sum]
  push_cast
  apply Finset.sum_le_sum
  intro a ha
  have he : (∀ p ∈ (Wu41.PS N 0 z).sort (· ≥ ·), ¬p ∣ a) ↔ Wu41.Sifted N z a := by
    rw [sifted_iff_avoids_list]
    simp only [Finset.mem_sort, Finset.mem_toList]
  have h := (rosserRows_bounds ((Wu41.PS N 0 z).sort (· ≥ ·)) 1 D a).1
  simpa only [he, one_dvd, true_and] using h

/-- Decreasing prime order gives a lower row for the actual assigned coordinate.
The coefficient expansion and analytic main term estimate remain separate. -/
theorem rosserRows_sorted_lower_sieve0 (B : ℝ) (N : ℕ) :
    ∑ a ∈ primeSequence N,
      (rosserRows ((Wu41.PS N 0 ((N : ℝ) ^ kappa1)).sort (· ≥ ·))
        1 (sieveLevel B N) a).1 ≤ sieveTerms N 0 := by
  simpa only [sieveTerms, Matrix.cons_val_zero] using
    rosserRows_sorted_sum_lower (primeSequence N) N ((N : ℝ) ^ kappa1) (sieveLevel B N)

end LeanLab.ChenDoubleSieve.Task392
