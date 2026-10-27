/-
P0006 page 3, Section 4, the odd prime witnesses at bound 29.
These exact counts concern independent residue classes. They do not give
the observed failure rate on the paper's sampled primes.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottPlatt.ResidueCount133

namespace LeanLab.HelfgottPlatt.Task133

/-- Page 3, bound 29. The nine odd prime witnesses, excluding the always
useless witness two for Proth exponents at least three. -/
def oddWitnessPrime (i : Fin 9) : ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29].get i

/-- Page 3, the witness list arithmetic used in the independent residue
model. No candidates near the paper's computational bound are enumerated. -/
theorem oddWitnessPrime_spec :
    (∀ i, (oddWitnessPrime i).Prime) ∧ (∀ i, oddWitnessPrime i ≠ 2) ∧
      Pairwise (fun i j => (oddWitnessPrime i).Coprime (oddWitnessPrime j)) ∧
        (∏ i, oddWitnessPrime i) = 3234846615 ∧
          (∏ i, (oddWitnessPrime i - 1) / 2) = 1995840 ∧
            (∏ i, (oddWitnessPrime i - 1)) = 1021870080 := by
  unfold Pairwise
  decide +kernel

/-- Page 3, exact independent residue model at the printed witness bound.
There are 1995840 simultaneous Jacobi-one residues modulo the product of
the nine odd primes. This does not count sampled prime candidates. -/
theorem odd_witness_residue_count :
    Nat.card {x : ZMod 3234846615 // ∀ i, jacobiSym x.val (oddWitnessPrime i) = 1} =
      1995840 := by
  obtain ⟨hp, hodd, hc, hprod, hhalf, _⟩ := oddWitnessPrime_spec
  have h := crt_jacobi_one_val_card oddWitnessPrime hp hodd hc
  rw [hprod, hhalf] at h
  exact h

/-- Page 3, independent coefficient residue model. Multiplication by a
power of two followed by addition of one permutes residues modulo the odd
witness product. This does not impose the Proth size or primality conditions. -/
theorem proth_coefficient_residue_count (n : ℕ) :
    Nat.card {k : ZMod 3234846615 //
      ∀ i, jacobiSym (k * 2 ^ n + 1).val (oddWitnessPrime i) = 1} =
      1995840 := by
  let u := ZMod.unitOfCoprime (2 ^ n)
    ((by decide : Nat.Coprime 2 3234846615).pow_left n)
  let e : Equiv.Perm (ZMod 3234846615) := (Units.mulRight u).trans (Equiv.addRight 1)
  have he (k : ZMod 3234846615) : e k = k * 2 ^ n + 1 := by
    simp [e, u, ZMod.coe_unitOfCoprime]
  calc
    _ = Nat.card {x : ZMod 3234846615 //
      ∀ i, jacobiSym x.val (oddWitnessPrime i) = 1} := by
        apply Nat.card_congr
        exact e.subtypeEquiv (fun k => by simp only [he])
    _ = 1995840 := odd_witness_residue_count

/-- Page 3, exact reference population for the independent residue model.
There are 1021870080 residues nonzero at all nine odd witness primes. -/
theorem odd_witness_nonzero_count :
    Nat.card {x : ZMod 3234846615 // ∀ i, (x.val : ZMod (oddWitnessPrime i)) ≠ 0} =
      1021870080 := by
  obtain ⟨hp, _, hc, hprod, _, hnonzero⟩ := oddWitnessPrime_spec
  have h := crt_nonzero_val_card oddWitnessPrime (fun i => (hp i).pos) hc
  rw [hprod, hnonzero] at h
  exact h

/-- Page 3, exact one in 512 ratio within the independent nonzero residue
population. This is not the observed failure rate among prime candidates. -/
theorem odd_witness_failure_ratio :
    512 * Nat.card {x : ZMod 3234846615 // ∀ i, jacobiSym x.val (oddWitnessPrime i) = 1} =
      Nat.card {x : ZMod 3234846615 // ∀ i, (x.val : ZMod (oddWitnessPrime i)) ≠ 0} := by
  rw [odd_witness_residue_count, odd_witness_nonzero_count]
  all_goals norm_num

end LeanLab.HelfgottPlatt.Task133
