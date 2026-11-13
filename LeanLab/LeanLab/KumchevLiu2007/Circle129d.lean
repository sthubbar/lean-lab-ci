/-
Kumchev and Liu, arXiv 0801.0130, paper P0088. Route burst session 8, p3, 2026-11-12.
Upstream file for `Decomp129`: the circle method setup of Section 2.1, pages 4 to 7,
for the split of the leaf `prop1_meansq`, Proposition 1 display 33.
Proved here: the orthogonality identity display 13 for general weights on the
windows I1 and I2 of display 5, and the splitting of the unit interval of display 15
into major and minor arcs. The two new LEAF statements are display 28, the major
arc asymptotic, and display 32, the minor arc mean square, for the weights
varpi and lambda0 of page 15. The windows, weights, f2 and the truncated
singular series are copies of the definitions of `Decomp129`, which imports this
file; the bridges are proved there by rfl or by counting.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534c

namespace LeanLab.KumchevLiu2007.Task129d

open Real Complex MeasureTheory LeanLab.KumchevLiu2007
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The window I1 of page 2 display 5: integers m with X minus Y at most m less than X. -/
noncomputable def win1 (X Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊X⌋₊ + 1)).filter (fun m => X - Y ≤ (m : ℝ) ∧ (m : ℝ) < X)

/-- The window I2 of page 2 display 5: integers m with the square root of Y over 2
at most m less than the square root of Y. -/
noncomputable def win2 (Y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.sqrt Y⌋₊ + 1)).filter
    (fun m => Real.sqrt Y / 2 ≤ (m : ℝ) ∧ (m : ℝ) < Real.sqrt Y)

/-- The weight varpi of page 4, the characteristic function of the primes, used as
lambda1 on page 15. -/
noncomputable def lam1 (m : ℕ) : ℝ := if m.Prime then 1 else 0

/-- The weight lambda0 of page 8 display 34 used as lambda2 on page 15: the
indicator of m with all prime factors at least z0 equal to Y to the 1/4 times P to
the minus 2, matching `roughCount` of `Decomp129`. -/
noncomputable def lam2 (Y P : ℝ) (m : ℕ) : ℝ :=
  if ∀ p : ℕ, p.Prime → p ∣ m → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ) then 1 else 0

/-- The exponential sum S1 of page 4 after display 13, for a weight lam on I1. -/
noncomputable def expSum1 (lam : ℕ → ℝ) (X Y α : ℝ) : ℂ :=
  ∑ m ∈ win1 X Y, (lam m : ℂ) * U1534.ee (α * m)

/-- The exponential sum S2 of page 4 after display 13, for a weight lam on I2,
with the phase alpha m squared. -/
noncomputable def expSum2 (lam : ℕ → ℝ) (Y α : ℝ) : ℂ :=
  ∑ m ∈ win2 Y, (lam m : ℂ) * U1534.ee (α * (m : ℝ) ^ 2)

/-- The representation function R of n, lambda1, lambda2 of page 4 display 12,
written as a double sum over the windows. -/
noncomputable def repR (l1 l2 : ℕ → ℝ) (X Y : ℝ) (n : ℕ) : ℝ :=
  ∑ m1 ∈ win1 X Y, ∑ m2 ∈ win2 Y, if m1 + m2 ^ 2 = n then l1 m1 * l2 m2 else 0

/-- Orthogonality on any interval of length 1: the integral of e of k alpha is 1
when k is 0 and 0 otherwise. Used in display 13 of page 4. -/
theorem integral_ee_int (a : ℝ) (k : ℤ) :
    ∫ α in a..a + 1, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (α : ℂ)) =
      if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (a : ℂ)) := by
      have : 2 * Real.pi * Complex.I * (k : ℂ) * ((a + 1 : ℝ) : ℂ) =
          2 * Real.pi * Complex.I * (k : ℂ) * (a : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h1, sub_self, zero_div]

/-- The integrand of display 13 expanded as a double sum of characters. -/
theorem integrand_expand (l1 l2 : ℕ → ℝ) (X Y : ℝ) (n : ℕ) (α : ℝ) :
    expSum1 l1 X Y α * expSum2 l2 Y α * U1534.ee (-(α * n)) =
      ∑ m1 ∈ win1 X Y, ∑ m2 ∈ win2 Y, ((l1 m1 * l2 m2 : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((m1 + m2 ^ 2 : ℕ) : ℤ) - (n : ℤ) : ℤ) * (α : ℂ)) := by
  unfold expSum1 expSum2
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m1 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m2 _ => ?_)
  unfold U1534.ee
  have : Complex.exp (2 * Real.pi * Complex.I * (((m1 + m2 ^ 2 : ℕ) : ℤ) - (n : ℤ) : ℤ) *
      (α : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * ((α * m1 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((α * (m2 : ℝ) ^ 2 : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((-(α * n) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [this]
  push_cast; ring

/-- Continuity of the integrand of display 13. -/
theorem integrand_continuous (l1 l2 : ℕ → ℝ) (X Y : ℝ) (n : ℕ) :
    Continuous (fun α : ℝ => expSum1 l1 X Y α * expSum2 l2 Y α * U1534.ee (-(α * n))) := by
  unfold expSum1 expSum2 U1534.ee
  fun_prop

/-- Page 4 display 13, PROVED. The orthogonality identity: R of n, lambda1,
lambda2 equals the integral over any unit interval of S1 S2 e of minus alpha n.
The paper integrates over 0 to 1; the arcs of display 15 live in Q inverse to
1 plus Q inverse, and the identity holds on every interval of length 1. -/
theorem display13 (l1 l2 : ℕ → ℝ) (X Y : ℝ) (n : ℕ) (a : ℝ) :
    ∫ α in a..a + 1, expSum1 l1 X Y α * expSum2 l2 Y α * U1534.ee (-(α * n)) =
      (repR l1 l2 X Y n : ℂ) := by
  simp_rw [integrand_expand]
  rw [intervalIntegral.integral_finsetSum (fun m1 _ => by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun m2 _ => by fun_prop))]
  unfold repR
  simp only [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun m1 _ => ?_)
  rw [intervalIntegral.integral_finsetSum (fun m2 _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_congr rfl (fun m2 _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_ee_int]
  by_cases h : m1 + m2 ^ 2 = n
  · have : ((m1 + m2 ^ 2 : ℕ) : ℤ) - (n : ℤ) = 0 := by rw [h]; ring
    rw [if_pos this, if_pos h]; push_cast; ring
  · have : ((m1 + m2 ^ 2 : ℕ) : ℤ) - (n : ℤ) ≠ 0 := by
      intro h'; apply h; omega
    rw [if_neg this, if_neg h]; simp

/-- The major arcs M of page 4 display 15: alpha within 1 over q Q of a over q for
some q at most P and 1 at most a at most q with a coprime to q. -/
def majorArcs (P Q : ℝ) : Set ℝ :=
  {α | ∃ q a : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |α - a / q| < 1 / (q * Q)}

/-- The major arcs are open, hence measurable. -/
theorem majorArcs_isOpen (P Q : ℝ) : IsOpen (majorArcs P Q) := by
  have : majorArcs P Q = ⋃ q : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 1 ≤ q ∧ (q : ℝ) ≤ P ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q),
        {α : ℝ | |α - a / q| < 1 / (q * Q)} := by
    ext α; simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5, h6⟩; exact ⟨q, a, ⟨h1, h2, h3, h4, h5⟩, h6⟩
    · rintro ⟨q, a, ⟨h1, h2, h3, h4, h5⟩, h6⟩; exact ⟨q, a, h1, h2, h3, h4, h5, h6⟩
  rw [this]
  refine isOpen_iUnion (fun q => isOpen_iUnion (fun a => isOpen_iUnion (fun _ => ?_)))
  exact isOpen_lt (by fun_prop) continuous_const

/-- The unit interval Q inverse to 1 plus Q inverse of display 15, taken half open;
the endpoint has measure zero. -/
def unitArc (Q : ℝ) : Set ℝ := Set.Ioc (1 / Q) (1 / Q + 1)

/-- The integral of display 13 over the major arcs, the left side of display 28. -/
noncomputable def majorInt (X Y P Q : ℝ) (n : ℕ) : ℂ :=
  ∫ α in unitArc Q ∩ majorArcs P Q,
    expSum1 lam1 X Y α * expSum2 (lam2 Y P) Y α * U1534.ee (-(α * n))

/-- The integral of display 13 over the minor arcs m of display 15, the inner
integral of display 32. -/
noncomputable def minorInt (X Y P Q : ℝ) (n : ℕ) : ℂ :=
  ∫ α in unitArc Q \ majorArcs P Q,
    expSum1 lam1 X Y α * expSum2 (lam2 Y P) Y α * U1534.ee (-(α * n))

/-- Page 4 displays 13 and 15, PROVED. R of n, varpi, lambda0 is the major arc
integral plus the minor arc integral. -/
theorem rep_eq_major_add_minor (X Y P Q : ℝ) (n : ℕ) :
    (repR lam1 (lam2 Y P) X Y n : ℂ) = majorInt X Y P Q n + minorInt X Y P Q n := by
  rw [← display13 lam1 (lam2 Y P) X Y n (1 / Q),
    intervalIntegral.integral_of_le (by linarith)]
  unfold majorInt minorInt
  rw [integral_inter_add_sdiff (majorArcs_isOpen P Q).measurableSet]
  · rfl
  · exact ((integrand_continuous _ _ X Y n).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/-- The integer windows of pages 2 and 15: the paper's I of n, lambda1, lambda2
after display 27 with f1 of u equal to 1 over log u and f2 the weight of page 15,
as a double sum over the windows. -/
noncomputable def f2W (z0 u : ℝ) : ℝ :=
  1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))

/-- The singular integral I of n, varpi, lambda0 of page 6 after display 27, as a
double sum over the windows with f1 of u equal to 1 over log u and f2 equal to
`f2W` with z0 equal to Y to the 1/4 times P to the minus 2, page 15. -/
noncomputable def singIntW (X Y P : ℝ) (n : ℕ) : ℝ :=
  ∑ m1 ∈ win1 X Y, ∑ m2 ∈ win2 Y, if m1 + m2 ^ 2 = n then
    (1 / Real.log (m1 : ℝ)) * f2W (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m2 : ℝ) else 0

/-- The truncated singular series S2 of n, P of page 2 display 7. -/
noncomputable def series2W (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q

/-- LEAF, route burst session 8 p3. Page 6 display 28 for varpi and lambda0 with
eta equal to 1/4: the major arc integral equals S2 of n, P times I of n up to an
error at most C Y to the 1/2 P to the minus 1/4. P is L to the B, Y is X to the
7/12 plus epsilon over 2, Q is H over P, and H is at most Y P to the minus 2 as
display 14 needs. Pages 5 and 6 combine displays 20, 24, 26, 27 from A1.2 and A2.2,
which page 15 verifies by Siegel Walfisz; CITED. Larger H reduces to this case by
covering the range of n in shorter intervals, in `Decomp129`. -/
theorem major_arc_display28 : (
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      H ≤ X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2 → ∀ n : ℕ,
        ‖majorInt X (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B) (H / Real.log X ^ B) n -
          series2W n (Real.log X ^ B) *
            (singIntW X (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B) n : ℂ)‖ ≤
          C * Real.sqrt (X ^ (7 / 12 + ε / 2)) * (Real.log X ^ B) ^ (-(1 / 4 : ℝ))
  ) := by
  sorry

/- The statement above is proved in `Circle129f` from display 29 and a narrower
kernel leaf, route burst session 8 p3. -/

end LeanLab.KumchevLiu2007.Task129d

#print axioms LeanLab.KumchevLiu2007.Task129d.integral_ee_int
#print axioms LeanLab.KumchevLiu2007.Task129d.display13
#print axioms LeanLab.KumchevLiu2007.Task129d.majorArcs_isOpen
#print axioms LeanLab.KumchevLiu2007.Task129d.rep_eq_major_add_minor
