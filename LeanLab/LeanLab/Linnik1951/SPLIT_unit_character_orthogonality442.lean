/-
Split of `unit_character_orthogonality442` into four leaves.

The statement is the mean square over the reduced residue classes of the
transformed coset series, bounded by the totient inverse times the principal
character prime sum squared plus the modulus times the non principal character
prime sums squared. There are exactly two ingredients. First the character
table of the unit group: expanding each coset series in the characters turns
the transformed coset sums into the character prime sums weighted by Gauss
numbers, and character orthogonality collapses the square, so the mean square
is the totient inverse times the squared character prime sums weighted by the
squared Gauss numbers. Second the two modulus bounds on those Gauss numbers:
the principal one is a Ramanujan sum, of modulus at most one, and every other
one is a Gauss sum, of squared modulus at most the modulus. The principal
weight is what makes the constant of the principal term `1` instead of `q`.

Leaves 1 to 4 record these four steps. The theorem
`unit_character_orthogonality442_split` below restates
`unit_character_orthogonality442` character for character and proves it from
the leaves without using the original theorem.
-/
import LeanLab.Linnik1951.SPLIT_rational_pointwise_characters442

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- LEAF. Step 1 of 4: the character prime series is the character weighted sum
of the residue coset series. Classify each prime by its residue class modulo
the modulus and pull the character value out of each class: a prime and its
class have the same character value, a character vanishes at the prime
divisors of the modulus, whose class is not a reduced residue, and the class
series is absolutely convergent, so exchanging the finite residue sum with
the series over primes is an identity and no estimate is involved. -/
theorem character_coset_expansion442 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q)
    (z : ℝ) (χ : DirichletCharacter ℂ q) :
    characterPrime280 χ N z = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  sorry

/-- LEAF. Step 2 of 4: the orthogonality identity of the reduced residue classes
with the Gauss numbers. Expanding each coset series in the character table of
the unit group writes the transformed coset sums as the character prime sums
weighted by Gauss numbers divided by the totient, and character orthogonality
over the reduced residues collapses the square of that sum, so the mean square
of the transformed coset series is the totient inverse times the squared
character prime sums weighted by the squared Gauss numbers, the principal
term separated from the rest. This is an identity: no bound on a Gauss number
and no estimate on a prime sum enters, those are the next two leaves. -/
theorem coset_orthogonality442 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) :
    (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) =
      1 / (q.totient : ℝ) * (‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), ((1 : DirichletCharacter ℂ q) c) * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) := by
  sorry

/-- LEAF. Step 3 of 4: the principal Gauss number has modulus at most one. It
is the sum of the unit phases, that is the Ramanujan sum of the reduced
residue system, whose value is a product of minus ones over the prime divisors
of the modulus, so its modulus is one at a squarefree modulus and zero
otherwise, in particular at most one. -/
theorem gauss_principal442 (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), ((1 : DirichletCharacter ℂ q) c) * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 ≤ 1 := by
  sorry

/-- LEAF. Step 4 of 4: every non principal Gauss number has squared modulus at
most the modulus. The unit phases summed against a non principal character
form its Gauss sum, whose modulus is the square root of the conductor of the
character, and the conductor divides the modulus, so the squared modulus is
the conductor and at most the modulus. -/
theorem gauss_nonprincipal442 (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 ≤ (q : ℝ) := by
  sorry

/-- Assembly of `unit_character_orthogonality442` from the four leaves: the
orthogonality identity, the two modulus bounds on the Gauss numbers and the
identification of the character prime sums with the coset series. Only the
principal weight is replaced by `1` and every other weight by the modulus, so
the mean square is at most the totient inverse times the principal squared
character prime sum plus the modulus times the non principal ones. -/
theorem unit_character_orthogonality442_split (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤ 1 / (q.totient : ℝ) * (‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2 + (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖characterPrime280 χ N z‖ ^ 2) := by
  classical
  have hφ : (0 : ℝ) < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hsig : ∀ χ : DirichletCharacter ℂ q, ‖characterPrime280 χ N z‖ ^ 2 = ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
    intro χ
    rw [character_coset_expansion442 N q hN hq z χ]
  have hsum : (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖characterPrime280 χ N z‖ ^ 2) =
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
    exact Finset.sum_congr rfl (fun χ _ => hsig χ)
  have hinner : ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), ((1 : DirichletCharacter ℂ q) c) * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 +
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 ≤
      ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
    have hA : ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), ((1 : DirichletCharacter ℂ q) c) * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 ≤
        1 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (gauss_principal442 q hq) (sq_nonneg _)
    have hB : (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤
        (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun χ hχ => mul_le_mul_of_nonneg_right
        (gauss_nonprincipal442 q hq χ (Finset.mem_filter.mp hχ).2) (sq_nonneg _))
    linarith
  have hmul : 1 / (q.totient : ℝ) * (‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), ((1 : DirichletCharacter ℂ q) c) * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), χ c * Complex.exp (((2 * Real.pi * ((c : ℝ) / (q : ℝ))) : ℝ) * Complex.I)‖ ^ 2 * ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) ≤ 1 / (q.totient : ℝ) * (‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), ((1 : DirichletCharacter ℂ q) b) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2 + (q : ℝ) * ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), ‖∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), χ b * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hinner (div_nonneg zero_le_one hφ.le)
  refine le_trans (le_of_eq (coset_orthogonality442 N q hN hq z)) (le_trans hmul ?_)
  rw [hsig 1, hsum]

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.unit_character_orthogonality442_split
