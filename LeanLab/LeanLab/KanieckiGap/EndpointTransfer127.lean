/-
P0022, page 371. The two Young-Potler endpoint conventions are equivalent
after certifying the one gap that crosses the stated cutoff.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.KanieckiGap.Boundary127
import LeanLab.KanieckiGap.PaperAssembly127

namespace LeanLab.KanieckiGap.EndpointTransfer127

/-- Page 371, the table endpoint. A pair of primes bracketing N bounds the
single gap crossing N. All gaps ending at most N use the given table.
CONDITIONAL ON that table. -/
theorem gap_le_of_boundary {N r q B : ℕ} (hr : r.Prime) (hq : q.Prime)
    (hrN : r ≤ N) (hNq : N < q) (hrq : q - r ≤ B)
    (hY : ∀ p : ℕ, p.Prime → nextPrime p ≤ N → gapAt p ≤ B)
    {p : ℕ} (hp : p.Prime) (hpN : p ≤ N) : gapAt p ≤ B := by
  by_cases hnext : nextPrime p ≤ N
  · exact hY p hp hnext
  · have hrp : r ≤ p := by
      by_contra hnot
      have hpr : p < r := by omega
      have h := nextPrime_min hpr hr
      omega
    have hnq : nextPrime p ≤ q := nextPrime_min (by omega) hq
    unfold gapAt
    omega

/-- Page 371 and reference 16. The assigned right endpoint input implies
the paper left endpoint input, using the certified boundary pair of width 60.
CONDITIONAL ON Young-Potler. -/
theorem paper_of_right (hY : KanieckiGap.YoungPotler) :
    LeanLab.Kaniecki1995.YoungPotler := by
  have hgap : ∀ p : ℕ, p.Prime → p ≤ 72630000000000 → gapAt p ≤ 778 := by
    intro p hp hpN
    exact gap_le_of_boundary Boundary127.prime_72629999999969
      Boundary127.prime_72630000000029 (by norm_num) (by norm_num) (by norm_num)
      hY hp hpN
  have hmax : KanieckiGap.lam 72630000000000 ≤ 778 := by
    unfold KanieckiGap.lam
    rw [if_neg (by norm_num)]
    apply Finset.sup_le
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hgap p hp.2 (by omega)
  unfold LeanLab.Kaniecki1995.YoungPotler
  have heq := Decomp127.lam_nat_eq (72630000000000 : ℕ)
  norm_num only [Nat.cast_ofNat] at heq
  rw [heq]
  exact_mod_cast hmax

/-- Page 371 and reference 16. The two finite table conventions are equivalent.
Neither table input is proved here. -/
theorem youngPotler_iff :
    KanieckiGap.YoungPotler ↔ LeanLab.Kaniecki1995.YoungPotler :=
  ⟨paper_of_right, Decomp127.youngPotler_of_paper⟩

/-- Page 371. The boundary data satisfy the required order and width constraints. -/
theorem boundary_instance :
    (72629999999969 : ℕ) ≤ 72630000000000 ∧
      (72630000000000 : ℕ) < 72630000000029 ∧
      (72630000000029 : ℕ) - 72629999999969 ≤ 778 := by
  norm_num

/-- Page 373. The exact cited interval input now uses the assigned folder's
right endpoint table. CONDITIONAL ON RH, Lemma 5, Schoenfeld61 and Young-Potler. -/
theorem interval_from_right_table (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.Lemma5) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) :
    IntervalProp (14045 * 10 ^ 8) ⌊LeanLab.Kaniecki1995.n0⌋₊ :=
  Decomp127.interval_from_paper hRH h5 hS (paper_of_right hY)

/-- Page 373. The original odd route with the assigned table convention.
CONDITIONAL ON RH, Lemma 5, Schoenfeld61, Young-Potler and Chen-Wang. -/
theorem odd_from_right_table (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.Lemma5) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang) :
    ∀ n : ℕ, Odd n → 1 < n → LeanLab.SchnirelmannConstant.AtMostPrimes 5 n :=
  PaperAssembly127.odd_from_paper hRH h5 hS (paper_of_right hY) hCW

/-- Page 373. The original even route with the assigned table convention.
CONDITIONAL ON RH, Lemma 5, Schoenfeld61, Young-Potler, Chen-Wang and the finite even check. -/
theorem even_from_right_table (hRH : RiemannHypothesis)
    (h5 : LeanLab.Kaniecki1995.Lemma5) (hS : LeanLab.DERZ1997.Schoenfeld61)
    (hY : KanieckiGap.YoungPotler) (hCW : LeanLab.Kaniecki1995.ChenWang)
    (hE : EvenGoldbachUpTo (1405 * 10 ^ 9)) :
    ∀ n : ℕ, Even n → LeanLab.SchnirelmannConstant.AtMostPrimes 4 n :=
  PaperAssembly127.even_from_paper hRH h5 hS (paper_of_right hY) hCW hE

end LeanLab.KanieckiGap.EndpointTransfer127

#print axioms LeanLab.KanieckiGap.EndpointTransfer127.gap_le_of_boundary
#print axioms LeanLab.KanieckiGap.EndpointTransfer127.paper_of_right
#print axioms LeanLab.KanieckiGap.EndpointTransfer127.youngPotler_iff
#print axioms LeanLab.KanieckiGap.EndpointTransfer127.boundary_instance
#print axioms LeanLab.KanieckiGap.EndpointTransfer127.interval_from_right_table
#print axioms LeanLab.KanieckiGap.EndpointTransfer127.odd_from_right_table
#print axioms LeanLab.KanieckiGap.EndpointTransfer127.even_from_right_table
