/-
Split of `prime_class_split442` into six leaves. The identity expresses the
damped prime Fourier series at a shifted reduced fraction as the sum over the
residue classes of the modulus, split into the classes coprime to the modulus
and the rest. The layers are: the pointwise periodicity of the phase on a
residue class, the summability of one class series with and without the class
phase, the collapse of the residue classes inside the prime series, the
interchange of the prime sum with the finite residue sum, and the constant
factor rule pulling the class phase out of a class series. The assembly at the
end has no sorry and does not use `prime_class_split442`.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_rational_pointwise_characters442

/- Task468 audit. The sealed prime_phase_periodic442 type uses real field remainder. Its concrete counterexample is below. The proved natural remainder helper supplies the phase identity used by the closed assembly. The sealed type is unchanged. -/

namespace LeanLab.Linnik1951

open MeasureTheory Finset

/-- LEAF. Step 1 of 6: the residue class periodicity of the prime phase. The
oscillation at the shifted point `a/q + z` splits into the oscillation at `a/q`,
which depends on the prime only through its residue modulo `q` and is written
there, times the oscillation at `z`. This is the pointwise identity
`exp (i x) * exp (i y) = exp (i (x + y))` for real `x` and `y`, together with the
integrality of `a * (p / q)` in the exponent; no sum and no convergence enters. -/
theorem prime_phase_periodic442 (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (z : ℝ) (p : Nat.Primes) :
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (((p : ℕ) % q) : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  sorry

/-- Page 155 equation 2.3 with the remainder explicitly taken in the natural numbers. -/
theorem prime_phase_nat_remainder468 (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (z : ℝ) (p : Nat.Primes) :
    Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (((p : ℕ) % q : ℕ) : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  set k : ℕ := (p : ℕ) / q
  set r : ℕ := (p : ℕ) % q
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((a * k : ℕ) : ℤ), ?_⟩
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hpq : ((p : ℕ) : ℝ) = (q : ℝ) * (k : ℝ) + (r : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (p : ℕ) q).symm
  have hpqC : ((p : ℕ) : ℂ) = (q : ℂ) * (k : ℂ) + (r : ℂ) := by
    exact_mod_cast hpq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqR
  push_cast
  rw [hpqC]
  field_simp
  ring

/-- LEAF. Step 2 of 6: the damped prime series of one residue class is
summable. Every term of the class series is at most the damping factor in
modulus, and the damping factors are dominated by a convergent geometric series
in the prime index. Nothing here refers to the shift or to the modulus beyond
the restriction to one class. -/
theorem prime_class_series_summable442 (N q : ℕ) (hN : 1 ≤ N) (z : ℝ) (b : ℕ) :
    Summable (fun p : Nat.Primes => if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  classical
  have h := (prime_fourier_summable111 N hN z).indicator {p : Nat.Primes | (p : ℕ) % q = b}
  convert h using 1
  ext p
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, neg_div]

/-- LEAF. Step 3 of 6: the same summability after multiplying the class series by
the class phase. The phase has modulus one, so the terms keep the modulus of the
damping factors and the restricted series is summable exactly as before. The
class phase is a fixed complex number for each pair of residues. -/
theorem prime_class_phase_series_summable442 (N q : ℕ) (hN : 1 ≤ N) (z : ℝ) (a b : ℕ) :
    Summable (fun p : Nat.Primes => if ((p : ℕ) % q = b) then Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  simpa only [mul_ite, mul_zero] using
    (prime_class_series_summable442 N q hN z b).mul_left
      (Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I))

/-- LEAF. Step 4 of 6: the collapse of the residue classes inside the damped prime
series. The prime Fourier series at the shifted reduced fraction is the double
series over the primes and over the residue classes of the modulus, each term
carrying the class phase of the residue and the damped oscillation in the shift.
This uses the periodicity of step 1 and the fact that the residue of a prime is
one of the residues of the modulus, so the inner finite sum collapses to its one
nonzero term; no coprimality of the residue is used and no estimate occurs. -/
theorem prime_fourier_class_collapse442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) (a : ℕ) :
    primeFourier111 N ((a : ℝ) / q + z) =
      (∑' p : Nat.Primes, ∑ b ∈ range q, (if ((p : ℕ) % q = b) then Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) := by
  classical
  unfold primeFourier111
  refine tsum_congr (fun p => ?_)
  rw [Finset.sum_eq_single ((p : ℕ) % q)]
  · rw [ite_eq_left rfl, prime_phase_nat_remainder468 q hq a z p]
    simp only [neg_div]
    ring
  · intro b hb hne
    simp only [ite_eq_right (Ne.symm hne)]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.mod_lt (p : ℕ) (by omega)))).elim

/-- LEAF. Step 5 of 6: the interchange of the prime sum with the finite sum over
the residue classes. A double series whose inner index ranges over a finite set
may be summed in either order once each class series is absolutely convergent,
so the prime Fourier series is the sum over the residues of the class series.
This is the convergence step alone; the class phases stay inside the inner
terms. -/
theorem prime_fourier_class_interchange442 (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) (a : ℕ) :
    (∑' p : Nat.Primes, ∑ b ∈ range q, (if ((p : ℕ) % q = b) then Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) =
      ∑ b ∈ range q, (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  exact Summable.tsum_finsetSum (fun b _ =>
    prime_class_phase_series_summable442 N q hN z a b)

/-- LEAF. Step 6 of 6: the class phase passes through the class series. The
class phase depends on the residue of the class and not on the prime, so it is a
constant factor of the summable class series and may be taken out of the sum.
This is the constant multiple rule for an absolutely convergent series, and it
keeps the damped oscillation of the shift inside the inner series. -/
theorem prime_class_phase_factor442 (N q : ℕ) (hN : 1 ≤ N) (z : ℝ) (a b : ℕ) :
    (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro p
  split_ifs <;> simp

/-- Assembly of `prime_class_split442` from the six leaves. The prime Fourier
series is rewritten as the double series over the primes and the residues, the
prime sum is interchanged with the finite residue sum, the class phase is pulled
out of each class series, and the residues coprime to the modulus are separated
from the others. Nothing here uses the original theorem, and no step of the
assembly is a leaf. -/
theorem prime_class_split442_split (N q : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (z : ℝ) (a : ℕ) :
    primeFourier111 N ((a : ℝ) / q + z) =
      (∑ b ∈ (range q).filter (fun b => Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0)) +
      (∑ b ∈ (range q).filter (fun b => ¬ Nat.Coprime b q), Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (b : ℝ)) / (q : ℝ))) : ℝ) *
          Complex.I) *
        (∑' p : Nat.Primes, if ((p : ℕ) % q = b) then
          ((Real.exp (-(((p : ℕ) : ℝ) / N)) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) else 0))  := by
  classical
  have hc := prime_fourier_class_collapse442 N q hN hq z a
  have hi := prime_fourier_class_interchange442 N q hN hq z a
  rw [hc, hi]
  rw [Finset.sum_congr rfl (fun b _ => prime_class_phase_factor442 N q hN z a b)]
  rw [← Finset.sum_filter_add_sum_filter_not (s := range q) (p := fun b => Nat.Coprime b q)]

/-- Audit of the sealed phase type at q two, a one, z zero and prime three.
The expected real type makes the remainder a real field remainder. -/
theorem prime_phase_periodic442_counterexample468 :
    Complex.exp ((-(2 * Real.pi * ((1 : ℝ) / 2 + 0) * (3 : ℝ)) : ℝ) * Complex.I) ≠
      Complex.exp ((-(2 * Real.pi * (((1 : ℝ) * (((3 : ℕ) % 2) : ℝ)) / (2 : ℝ))) : ℝ) * Complex.I) *
        Complex.exp ((-(2 * Real.pi * 0 * (3 : ℝ)) : ℝ) * Complex.I) := by
  have he : Complex.exp ((-(2 * Real.pi * ((1 : ℝ) / 2 + 0) * (3 : ℝ)) : ℝ) * Complex.I) = -1 := by
    have harg : ((-(2 * Real.pi * ((1 : ℝ) / 2 + 0) * (3 : ℝ)) : ℝ) : ℂ) * Complex.I =
        (3 : ℂ) * (-(Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [harg]
    have h := Complex.exp_nat_mul (-(Real.pi : ℂ) * Complex.I) 3
    norm_num [neg_mul, Complex.exp_neg_pi_mul_I] at h
    simpa only [mul_neg, neg_mul] using h
  rw [he]
  norm_num [Field.mod_eq]

/-- The exact quantified type of the sealed phase leaf is false.
This audits the Lean annotation of page 155 equation 2.3. -/
theorem prime_phase_periodic442_not_forall468 : ¬ (∀ (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (z : ℝ) (p : Nat.Primes),
Complex.exp ((-(2 * Real.pi * ((a : ℝ) / q + z) * ((p : ℕ) : ℝ)) : ℝ) * Complex.I) =
      Complex.exp ((-(2 * Real.pi * (((a : ℝ) * (((p : ℕ) % q) : ℝ)) / (q : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)) := by
  intro h
  apply prime_phase_periodic442_counterexample468
  simpa only [Nat.cast_ofNat, Nat.cast_one] using h 2 (by norm_num) 1 0 ⟨3, by norm_num⟩

end LeanLab.Linnik1951
