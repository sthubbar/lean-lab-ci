import LeanLab.OpenProblems.State1612

/-!
# Split of `route_euler_positive_density` (OpenProblems, State1612)

The target asks for a positive density of those `n` whose `8n + 3` is an odd square plus twice a
prime: some `c > 0` with `c * X ≤ X - euExc X` for all large `X`.

Write `A X` for the set of `n` in `[1, X]` with `IsEuler (8n + 3)`, and `R n` for the number of
`k` with `4n + 1 - 2k(k+1)` prime, the multiplicity of the triangular form that the target's file
already records for this problem.  `R n` vanishes exactly at the values with no representation, so
the route is a first moment, a second moment and Cauchy-Schwarz:

  (sum of `R` over `A X`) ^ 2  <=  (#A X) * (sum of `R ^ 2` over `A X`),

and the two moments have sizes `X * sqrt X / log X` and `X ^ 2 / (log X) ^ 2`, whose ratio is
`X` up to the fixed constants.  This is where a positive density comes from, and it is why a
single crude pair count is not enough: a pair count alone only gives `X / log X` represented
values, because each value can carry up to `sqrt X` pairs.

1. `leaf_representation_multiplicity`: the multiplicity `R` exists, is the finite list count, and
   is nonzero exactly at the representable `n`.  This is the triangular form, a bookkeeping step.
2. `leaf_first_moment_card`: for such an `R` the total multiplicity over `A X` is at least
   `a * X * sqrt X / log X` with a fixed `a > 0`.  A prime count summed over `k <= sqrt X` gives
   this size.  Strictly weaker than the target: on its own it counts pairs, not represented values.
3. `leaf_second_moment_card`: for such an `R` the total of the squared multiplicity over `A X` is
   at most `b * X ^ 2 / (log X) ^ 2` with a fixed `b > 0`.  Strictly weaker than the target: a mean
   square bound says nothing about how many `n` are hit.
4. `leaf_cauchy_schwarz_density`: the two moment estimates and Cauchy-Schwarz give `c * X` as a
   lower bound for the cardinality of `A X`, with `c` the ratio of the squared first moment to the
   second moment.  Strictly weaker than the target: it bounds the size of `A X`, not `X - euExc X`.
5. `leaf_card_eq_complement`: the cardinality of `A X` is `X - euExc X`, the complement inside
   `[1, X]` of the exceptional set that the target's file counts.  An identity, with no estimate.

Every leaf is tested at the degenerate values.  At `X = 0` the interval `[1, 0]` is empty, both
finite sums are `0`, and both quotients are `0` by Lean's division convention (`Real.log 0 = 0`),
so the three inequalities hold there; each of them is an eventual statement, and the fifth is an
identity that also reads `0 = 0` at `X = 0`.  No leaf can fail at a small case, and no hypothesis
of leaf 2, 3 or 4 is unsatisfiable: leaf 1 produces an `R` meeting them, and at `X = 0` the
conclusion of leaf 4 reads `0 <= 0` rather than being vacuous.

No statement, import or definition of the target file is changed, and no definition, abbreviation,
structure, instance or notation is introduced here.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab
open scoped Classical

/-- LEAF 1, the multiplicity.  There is a multiplicity `R`, computed from the list form as the
number of `k` with `4n + 1 - 2k(k+1)` prime, and for `1 ≤ n` it is nonzero exactly where `8n + 3`
has an odd square plus twice a prime.  The bound `4n + 2` on `k` is safe: a term with
`2k(k+1) > 4n + 1` truncates to `0`, which is not prime, and every true solution has `k ≤ n`. -/
theorem leaf_representation_multiplicity :
    ∃ R : ℕ → ℕ,
      (∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
          (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) ∧
      ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
  classical
  refine ⟨fun n => ((Finset.range (4 * n + 2)).filter
      (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card, fun n => rfl, ?_⟩
  intro n _
  rw [isEuler_iff_triangular]
  constructor
  · intro hR
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hR)
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, hkprime⟩ := hk
    have h2 := hkprime.two_le
    have hle : 2 * k * (k + 1) ≤ 4 * n + 1 := by omega
    exact ⟨k, 4 * n + 1 - 2 * k * (k + 1), hkprime, by omega⟩
  · rintro ⟨k, p, hp, he⟩
    refine Finset.card_ne_zero.mpr ⟨k, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range]
    have hp2 := hp.two_le
    have hbb : 2 * k * (k + 1) = 2 * (k * (k + 1)) := by ring
    have hsmall : k * (k + 1) ≤ 2 * n := by omega
    have hkk : k ≤ k * (k + 1) := by
      calc k = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * (k + 1) := Nat.mul_le_mul_left k (by omega)
    refine ⟨by omega, ?_⟩
    have heq : 4 * n + 1 - 2 * k * (k + 1) = p := by omega
    rw [heq]
    exact hp

/-- LEAF 2, the first moment.  REPAIRED: as first written this leaf quantified over every `R`
whose vanishing set is the representable set, and that is false — the indicator of the representable
set meets the hypothesis with first moment `#A X ≤ X`, below `a * X * sqrt X / log X` for every
`a > 0`.  The hypothesis `hRdef` pins `R` to the cardinality of LEAF 1, which is what the assembly
gets from LEAF 1 and passes here; with it the leaf states a prime count.  The total multiplicity over
the representable `n ≤ X` is at least `a * X * sqrt X / log X` for a fixed `a > 0`, for all large
`X`.  For each `k` with `2k(k+1) ≤ X` the primes of the form `4n + 1 - 2k(k+1)` are a fixed fraction
of `X / log X`, and there are about `sqrt X` of those `k`; the count here is over pairs, so it does
not yet see how the pairs are spread over the values. -/
theorem leaf_first_moment_card (R : ℕ → ℕ)
    (hRdef : ∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ X : ℕ in Filter.atTop,
      a * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ)) := by
  sorry

/-- LEAF 3, the second moment.  For a multiplicity `R` that is nonzero exactly on the representable
values, the total of the squared multiplicity over those `n ≤ X` is at most
`b * X ^ 2 / (log X) ^ 2` for a fixed `b > 0`, for all large `X`.  Two representations of the same
value differ by a difference of two primes equal to a difference of two squares, and the parallel
count of those differences on the scale `X` bounds the square sum.  A mean square bound is weaker
than a density statement: it does not say how many values carry a representation. -/
theorem leaf_second_moment_card (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  sorry

/-- The algebra of the density step, isolated from the two moment inputs: Gauss's inequality
`(sum R) ^ 2 ≤ #A * (sum R ^ 2)` turns the two estimates into `a ^ 2 / b` times `X`, and the two
powers of the logarithm cancel. -/
private lemma cs_density_algebra {X a b L S T C : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX : 0 < X) (hL : 0 < L) (hC : 0 ≤ C)
    (hCS : S ^ 2 ≤ C * T) (hS : a * X * Real.sqrt X / L ≤ S)
    (hT : T ≤ b * X ^ 2 / L ^ 2) : a ^ 2 / b * X ≤ C := by
  have hApos : 0 < a * X * Real.sqrt X / L := by
    have h1 : 0 < a * X := mul_pos ha hX
    have h2 : 0 < a * X * Real.sqrt X := mul_pos h1 (Real.sqrt_pos.mpr hX)
    exact div_pos h2 hL
  have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt (le_of_lt hX)
  have hA2 : (a * X * Real.sqrt X / L) ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hApos) hS 2
  have hCT : 0 < C * T := lt_of_lt_of_le (pow_pos hApos 2) (hA2.trans hCS)
  have hTpos : 0 < T := pos_of_mul_pos_right hCT hC
  have hCB : (a * X * Real.sqrt X / L) ^ 2 ≤ C * (b * X ^ 2 / L ^ 2) :=
    hA2.trans (hCS.trans (mul_le_mul_of_nonneg_left hT hC))
  have hL2 : 0 < L ^ 2 := pow_pos hL 2
  have hL2ne : L ^ 2 ≠ 0 := ne_of_gt hL2
  have hmul := mul_le_mul_of_nonneg_right hCB (le_of_lt hL2)
  have hlhs : (a * X * Real.sqrt X / L) ^ 2 * L ^ 2 = a ^ 2 * X ^ 3 := by
    rw [div_pow, div_mul_cancel₀ _ hL2ne, mul_pow, mul_pow, hsq]
    ring
  have hrhs : C * (b * X ^ 2 / L ^ 2) * L ^ 2 = C * b * X ^ 2 := by
    rw [mul_assoc, div_mul_cancel₀ _ hL2ne]
    ring
  rw [hlhs, hrhs] at hmul
  have hX2 : 0 < X ^ 2 := pow_pos hX 2
  have hstep : a ^ 2 * X * X ^ 2 ≤ (C * b) * X ^ 2 := by nlinarith [hmul]
  have hfin : a ^ 2 * X ≤ C * b := le_of_mul_le_mul_right hstep hX2
  calc a ^ 2 / b * X = a ^ 2 * X / b := by ring
    _ ≤ C := (div_le_iff₀ hb).mpr (by linarith)

/-- The density step with the moments stated for an abstract family of finsets, so that the two
moment inputs enter exactly as they are given. -/
private theorem cs_density_of_moments (R : ℕ → ℕ) (s : ℕ → Finset ℕ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hfirst : ∀ᶠ X : ℕ in Filter.atTop,
      a * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤ (s X).sum (fun n => (R n : ℝ)))
    (hsecond : ∀ᶠ X : ℕ in Filter.atTop,
      (s X).sum (fun n => (R n : ℝ) ^ 2) ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((s X).card : ℝ) := by
  classical
  refine ⟨a ^ 2 / b, by positivity, ?_⟩
  filter_upwards [hfirst, hsecond, Filter.eventually_ge_atTop 2] with X h1 h2 hX
  have hX0 : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := by omega
    exact_mod_cast this
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hC : (0 : ℝ) ≤ ((s X).card : ℝ) := Nat.cast_nonneg _
  have hCS := sq_sum_le_card_mul_sum_sq (s := s X) (f := fun n => (R n : ℝ))
  exact cs_density_algebra ha hb hX0 hL hC hCS h1 h2

/-- LEAF 4, Cauchy-Schwarz.  Given a multiplicity `R` that is nonzero exactly on the representable
values, and the first and second moment estimates of LEAF 2 and LEAF 3 with constants `a` and `b`,
there is `c > 0` with `c * X ≤ #A X` for all large `X`.  On `A X` the multiplicity is at least
`1`, and Cauchy-Schwarz over `A X` gives `(sum R) ^ 2 ≤ (#A X) * (sum R ^ 2)`; dividing the
squared first moment by the second moment leaves `a ^ 2 / b` times `X`, since the two powers of the
logarithm cancel.  It bounds the number of representable values, and is weaker than the target,
which is about `X - euExc X`. -/
theorem leaf_cauchy_schwarz_density (R : ℕ → ℕ)
    (hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : ∀ᶠ X : ℕ in Filter.atTop,
      a * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ)))
    (hsecond : ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c * X ≤ (((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3))).card : ℝ) :=
  cs_density_of_moments R (fun X => (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
    a b ha hb hfirst hsecond

/-- LEAF 5, the complement identity.  The representable count inside `[1, X]` is `X - euExc X`:
the interval has `X` elements and `euExc X` counts the rest of it.  No estimate, and no
hypothesis.  At `X = 0` both sides are `0`. -/
theorem leaf_card_eq_complement (X : ℕ) :
    ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3))).card = X - euExc X := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 X)
    (p := fun n => IsEuler (8 * n + 3))
  have hcard : (Finset.Icc 1 X).card = X := by
    rw [Nat.card_Icc]
    omega
  unfold euExc
  omega

/-- The sealed statement of `route_euler_positive_density`, assembled from the five leaves above
with no use of the route theorem itself. -/
theorem route_euler_positive_density_split :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((X - euExc X : ℕ) : ℝ) := by
  obtain ⟨R, hRdef, hR⟩ := leaf_representation_multiplicity
  obtain ⟨a, ha, hfirst⟩ := leaf_first_moment_card R hRdef hR
  obtain ⟨b, hb, hsecond⟩ := leaf_second_moment_card R hR
  obtain ⟨c, hc, hcard⟩ := leaf_cauchy_schwarz_density R hR a b ha hb hfirst hsecond
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcard] with X hX
  rw [← leaf_card_eq_complement X]
  exact hX

end LeanLab.OpenProblems.State1612

#print axioms LeanLab.OpenProblems.State1612.leaf_representation_multiplicity
#print axioms LeanLab.OpenProblems.State1612.leaf_first_moment_card
#print axioms LeanLab.OpenProblems.State1612.leaf_second_moment_card
#print axioms LeanLab.OpenProblems.State1612.leaf_cauchy_schwarz_density
#print axioms LeanLab.OpenProblems.State1612.leaf_card_eq_complement
#print axioms LeanLab.OpenProblems.State1612.route_euler_positive_density_split
