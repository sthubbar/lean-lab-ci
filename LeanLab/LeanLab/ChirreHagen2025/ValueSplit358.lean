import LeanLab.ChirreHagen2025.Summability272
import LeanLab.ChirreHagen2025.TailIntegral297
import LeanLab.ChirreHagen2025.TailNumeric297

/-!
P0075 page 13, the algebraic split of the convergent prime series.
The split below is valid for any prime-value cutoff. It asserts no Rosser tail
estimate and makes no claim about the inherited cutoff transcription.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.ValueSplit358
open TailIntegral297

/-- P0075 page 13, finite head plus complementary tail for the prime series.
This supporting algebraic identity holds for every prime-value cutoff. -/
theorem prime_value_split (N : ℕ) :
    (∑' p : Nat.Primes, weight p) =
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 N), weight p) +
      ∑' p : {p : Nat.Primes // N < (p : ℕ)}, weight (p : Nat.Primes) := by
  classical
  let s : Finset Nat.Primes :=
    Finset.subtype Nat.Prime (Finset.filter Nat.Prime (Finset.Icc 1 N))
  have hmem (p : Nat.Primes) : p ∉ s ↔ N < (p : ℕ) := by
    have hm : p ∈ s ↔ (p : ℕ) ∈ Finset.filter Nat.Prime (Finset.Icc 1 N) :=
      @Finset.mem_subtype ℕ Nat.Prime _ (Finset.filter Nat.Prime (Finset.Icc 1 N)) p
    exact hm.not.trans (by simp [p.property, p.property.one_lt.le])
  let e : {p : Nat.Primes // p ∉ s} ≃ {p : Nat.Primes // N < (p : ℕ)} :=
    { toFun := fun p => ⟨p.1, (hmem p.1).mp p.2⟩
      invFun := fun p => ⟨p.1, (hmem p.1).mpr p.2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have htail : (∑' p : {p : Nat.Primes // p ∉ s}, weight (p : Nat.Primes)) =
      ∑' p : {p : Nat.Primes // N < (p : ℕ)}, weight (p : Nat.Primes) :=
    e.tsum_eq (fun p => weight (p : Nat.Primes))
  have hhead : (∑ p ∈ s, weight p) =
      ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 N), weight p := by
    exact Finset.sum_subtype_of_mem (fun p : ℕ => weight p)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hs : Summable (fun p : Nat.Primes => weight p) := Summability272.part1_summable
  rw [← hs.sum_add_tsum_subtype_compl s, hhead, htail]

/-- P0075 page 13, algebraic split only. Exact target statement from DecompJ867.
This proof does not use the inherited prime lower bound or tail comparison. -/
theorem leaf_split_n0 (n0 : ℕ) (hn0 : n0 = 26355867) :
    (∑' p : Nat.Primes, Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) =
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 n0),
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) +
    (∑' p : {p : Nat.Primes // n0 < (p : ℕ)},
      Real.log (p : ℝ) / (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) := by
  simpa only [weight] using prime_value_split n0

/-- P0075 page 14, the numerical integral tail. Exact target from DecompJ867.
Reuse the proved task297 bound and the fact that an endpoint has measure zero. -/
theorem leaf_integral_bound (n0 : ℕ) (hn0 : n0 = 26355867) :
    (∫ x in Set.Ioi (n0 : ℝ), Real.log (x * Real.log x) /
      (Real.sqrt (x * Real.log x) * (x * Real.log x - 1))) < 0.000104 := by
  subst n0
  simpa only [Nat.cast_ofNat, MeasureTheory.integral_Ici_eq_integral_Ioi, TailIntegral297.tailWeight,
    TailIntegral297.weight] using TailNumeric297.tail_integral_lt

end LeanLab.ChirreHagen2025.ValueSplit358
