/-
P0006 page 2, Section 2 step 4. With fixed witness bound, all Jacobi
choices are determined by one bounded residue of the candidate. The period
used here is a sufficient period, not a minimal one. AI wrote the Lean code.
Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.Algorithm98

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 2, fixed witness bound. A sufficient common period for denominator
reduction in all candidate Jacobi symbols. This period is derived here. -/
def jacobiPeriod (B : ℕ) : ℕ := 4 * B.factorial

/-- Page 2, step 4. For odd candidates congruent modulo the fixed period,
every prime witness at most B has the same Jacobi symbol. -/
theorem jacobi_eq_of_period {N N' B a : ℕ} (hN : Odd N) (hN' : Odd N')
    (hmod : N % jacobiPeriod B = N' % jacobiPeriod B)
    (ha : a.Prime) (haB : a ≤ B) : jacobiSym a N = jacobiSym a N' := by
  have hd : 4 * a ∣ jacobiPeriod B :=
    Nat.mul_dvd_mul_left 4 (Nat.dvd_factorial ha.pos haB)
  have hm : N % (4 * a) = N' % (4 * a) := by
    have h := congrArg (fun r => r % (4 * a)) hmod
    simpa only [Nat.mod_mod_of_dvd _ hd] using h
  rw [jacobiSym.mod_right' a hN, jacobiSym.mod_right' a hN', hm]

/-- Page 2, steps 3 to 5. The first witness search is determined by the
candidate residue modulo the fixed sufficient period, for odd candidates. -/
theorem firstWitness_eq_of_period {N N' B : ℕ} (hN : Odd N) (hN' : Odd N')
    (hmod : N % jacobiPeriod B = N' % jacobiPeriod B) :
    Task98.firstWitness N B = Task98.firstWitness N' B := by
  apply Option.ext
  intro a
  rw [Task98.firstWitness_eq_some, Task98.firstWitness_eq_some]
  constructor
  · rintro ⟨ha, haB, haJ, hmin⟩
    refine ⟨ha, haB, ?_, ?_⟩
    · rw [← jacobi_eq_of_period hN hN' hmod ha haB]
      exact haJ
    · intro q hqa hq hqJ
      apply hmin q hqa hq
      rw [jacobi_eq_of_period hN hN' hmod hq (by omega)]
      exact hqJ
  · rintro ⟨ha, haB, haJ, hmin⟩
    refine ⟨ha, haB, ?_, ?_⟩
    · rw [jacobi_eq_of_period hN hN' hmod ha haB]
      exact haJ
    · intro q hqa hq hqJ
      apply hmin q hqa hq
      rw [← jacobi_eq_of_period hN hN' hmod hq (by omega)]
      exact hqJ

/-- Page 2, step 4. The bounded witness search for an odd candidate can be
performed on its remainder modulo the sufficient common period. -/
theorem firstWitness_mod {N B : ℕ} (hN : Odd N) :
    Task98.firstWitness N B = Task98.firstWitness (N % jacobiPeriod B) B := by
  have he : Even (jacobiPeriod B) :=
    (by decide : Even (4 : ℕ)).mul_right B.factorial
  exact firstWitness_eq_of_period hN (hN.mod_even he) (by rw [Nat.mod_mod])

/-- Page 2, step 4. Finite lookup specification for a fixed witness bound.
It stores witness selection on each residue, rather than measured run time. -/
def witnessTable (B : ℕ) : Fin (jacobiPeriod B) → Option ℕ :=
  fun r => Task98.firstWitness r.val B

/-- Page 2, step 4. A lookup by the candidate remainder gives exactly the
original first witness search on an odd candidate. -/
theorem witnessTable_correct {N B : ℕ} (hN : Odd N) :
    witnessTable B ⟨N % jacobiPeriod B,
      Nat.mod_lt N (by unfold jacobiPeriod; positivity)⟩ = Task98.firstWitness N B :=
  (firstWitness_mod hN).symm

/-- Page 2, steps 5 and 6, using the finite witness table. The power test
still uses the original candidate modulus. -/
def lookupTest (k m B : ℕ) : Bool :=
  let N := k * 2 ^ (m + 1) + 1
  match witnessTable B ⟨N % jacobiPeriod B,
      Nat.mod_lt N (by unfold jacobiPeriod; positivity)⟩ with
  | none => false
  | some a => decide ((a : ZMod N) ^ ((N - 1) / 2) = -1)

/-- Page 2, the full test. Replacing the Jacobi search by finite residue
lookup leaves the Boolean result unchanged, including on composites. -/
theorem lookupTest_eq (k m B : ℕ) : lookupTest k m B = Task98.boundedTest k m B := by
  have hN : Odd (k * 2 ^ (m + 1) + 1) := by
    refine ⟨k * 2 ^ m, ?_⟩
    rw [pow_succ]
    ring
  dsimp only [lookupTest, Task98.boundedTest]
  rw [witnessTable_correct hN]
  rfl

/-- Page 2, finite table instances. The lookup agrees in successful,
exhausted and composite cases. These are model checks, not range checks. -/
theorem lookup_instances :
    jacobiPeriod 3 = 24 ∧ witnessTable 3 ⟨17, by decide⟩ = some 3 ∧
      lookupTest 3 1 2 = true ∧ lookupTest 1 3 2 = false ∧
        lookupTest 1 3 3 = true ∧ lookupTest 3 2 29 = false := by
  decide +kernel

end LeanLab.HelfgottPlatt.Task133
