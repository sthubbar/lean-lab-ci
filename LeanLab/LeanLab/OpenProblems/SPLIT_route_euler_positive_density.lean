import LeanLab.OpenProblems.State1612
import LeanLab.PNTPort.PsiChi.SiegelWalfisz

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

private lemma eight_mul_mul_self_le {X u : ℕ} (hu : u * u ≤ X / 8) : 8 * (u * u) ≤ X :=
  (Nat.mul_le_mul_left 8 hu).trans (Nat.mul_div_le X 8)

private lemma two_mul_succ_le_eight_mul_sq {u : ℕ} (hu1 : 1 ≤ u) :
    2 * u * (2 * u + 1) ≤ 8 * (u * u) := by
  have h1 : 2 * u + 1 ≤ 4 * u := by omega
  calc 2 * u * (2 * u + 1) ≤ 2 * u * (4 * u) := Nat.mul_le_mul_left _ h1
    _ = 8 * (u * u) := by ring

private lemma le_of_sq_le {X u : ℕ} (hu1 : 1 ≤ u) (hu : u * u ≤ X / 8) : u ≤ X := by
  have h8 := eight_mul_mul_self_le hu
  have h1 : u ≤ u * u := by
    calc u = u * 1 := (Nat.mul_one u).symm
      _ ≤ u * u := Nat.mul_le_mul_left u hu1
  have h2 : u * u ≤ 8 * (u * u) := by
    have h6 := Nat.mul_le_mul_left (u * u) (by norm_num : 1 ≤ 8)
    calc u * u = u * u * 1 := (Nat.mul_one _).symm
      _ ≤ u * u * 8 := h6
      _ = 8 * (u * u) := by ring
  exact (h1.trans h2).trans h8

private lemma mem_k_of {X u : ℕ} (hu1 : 1 ≤ u) (hu : u * u ≤ X / 8) :
    u ∈ (Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X) := by
  have hle := le_of_sq_le hu1 hu
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
  exact (two_mul_succ_le_eight_mul_sq hu1).trans (eight_mul_mul_self_le hu)

private lemma card_k_lower_nat (X : ℕ) :
    Nat.sqrt (X / 8) ≤
      ((Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X)).card := by
  have hsub : Finset.Icc 1 (Nat.sqrt (X / 8)) ⊆
      (Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X) := by
    intro u hu
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
    have hu2 : u ≤ Nat.sqrt (X / 8) := (Finset.mem_Icc.mp hu).2
    exact mem_k_of hu1 (Nat.le_sqrt.mp hu2)
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  omega

private lemma card_k_ge (X : ℕ) (hX : 4096 ≤ X) :
    Real.sqrt (X : ℝ) / 16 ≤
      (((Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X)).card : ℝ) := by
  have hnat := card_k_lower_nat X
  have hcard : (Nat.sqrt (X / 8) : ℝ) ≤
      (((Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X)).card : ℝ) := by
    exact_mod_cast hnat
  refine le_trans ?_ hcard
  set m : ℕ := Nat.sqrt (X / 8) with hm
  have hsqrt_lt : X / 8 < (m + 1) ^ 2 := hm ▸ Nat.lt_succ_sqrt' (X / 8)
  have hexp : X < 8 * (m + 1) ^ 2 := by
    have h1 : X / 8 + 1 ≤ (m + 1) ^ 2 := by omega
    have h2 : 8 * (X / 8) + 8 ≤ 8 * ((m + 1) ^ 2) := by
      simpa [Nat.mul_add] using Nat.mul_le_mul_left 8 h1
    have h3 : X ≤ 8 * (X / 8) + 7 := by
      have h4 : X % 8 + 8 * (X / 8) = X := Nat.mod_add_div X 8
      have h5 : X % 8 < 8 := Nat.mod_lt X (by norm_num)
      omega
    omega
  have hXcast : (X : ℝ) < 8 * ((m : ℝ) + 1) ^ 2 := by
    have h6 : (X : ℝ) < ((8 * (m + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hexp
    push_cast at h6
    linarith
  have hpos8 : (0 : ℝ) < (X : ℝ) / 8 := by
    have h7 : (0 : ℕ) < X := by omega
    have h8 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast h7
    positivity
  have hsqrt_lt' : Real.sqrt ((X : ℝ) / 8) < (m : ℝ) + 1 := by
    rw [Real.sqrt_lt (le_of_lt hpos8) (by positivity)]
    linarith
  have hmono : Real.sqrt ((X : ℝ) / 64) ≤ Real.sqrt ((X : ℝ) / 8) := by
    refine Real.sqrt_le_sqrt ?_
    have h8 : (0 : ℝ) ≤ (X : ℝ) := by positivity
    linarith
  have h64 : Real.sqrt ((X : ℝ) / 64) = Real.sqrt (X : ℝ) / 8 := by
    rw [Real.sqrt_div' (X : ℝ) (by norm_num : (0:ℝ) ≤ 64)]
    norm_num
  have h256 : (256 : ℝ) ≤ (X : ℝ) := by
    have h9 : (4096 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hsqrt16 : (16 : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have h10 : Real.sqrt (256 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt h256
    have h11 : Real.sqrt (256 : ℝ) = 16 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h11] at h10
    exact h10
  have hstep : Real.sqrt (X : ℝ) / 16 ≤ Real.sqrt ((X : ℝ) / 8) - 1 := by
    rw [h64] at hmono
    linarith
  linarith

/-- **The counting half of the repaired first moment** (carried).  Pairs `(j, u)` with `4j+1` prime
and `2u(2u+1) ≤ X` inject into the representation pairs of the representable `n ≤ X`. -/
private theorem first_moment_pairs (X : ℕ) :
    (((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card
        * ((Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X)).card)
      ≤ ∑ n ∈ (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)),
          ((Finset.range (4 * n + 2)).filter (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card := by
  classical
  set s : Finset ℕ := (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)) with hs
  set t : ℕ → Finset ℕ :=
    fun n => (Finset.range (4 * n + 2)).filter (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)
    with ht
  set P : Finset ℕ := (Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime) with hP
  set K : Finset ℕ := (Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X) with hK
  set Q : Finset (ℕ × ℕ) := s.biUnion (fun n => (t n).image (fun k => (n, k))) with hQ
  have h1 : (P ×ˢ K).card ≤ Q.card := by
    refine Finset.card_le_card_of_injOn
      (fun p : ℕ × ℕ => (p.1 + p.2 * (2 * p.2 + 1), 2 * p.2)) ?_ ?_
    · rintro ⟨j, u⟩ hp
      obtain ⟨hjp, huk⟩ := Finset.mem_product.mp hp
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hjp).1
      have hprime : (4 * j + 1).Prime := (Finset.mem_filter.mp hjp).2
      have hu2 : 2 * u * (2 * u + 1) ≤ X := (Finset.mem_filter.mp huk).2
      have h2j : 2 * j ≤ X := by
        have hz := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hj2
        omega
      have hu_le : u * (2 * u + 1) ≤ X / 2 := by
        refine (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr ?_
        have hring : 2 * u * (2 * u + 1) = (u * (2 * u + 1)) * 2 := by ring
        omega
      have hnX : j + u * (2 * u + 1) ≤ X := by
        have hsum : j + u * (2 * u + 1) ≤ X / 2 + X / 2 := by omega
        have h2X : X / 2 + X / 2 ≤ X := by
          have h := Nat.div_mul_le_self X 2
          omega
        exact hsum.trans h2X
      have hmem : (j + u * (2 * u + 1), 2 * u) ∈ Q := by
        rw [hQ]
        refine Finset.mem_biUnion.mpr ⟨j + u * (2 * u + 1), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hnX⟩, ?_⟩
          rw [isEuler_iff_triangular]
          exact ⟨2 * u, 4 * j + 1, hprime, by ring⟩
        · refine Finset.mem_image.mpr ⟨2 * u, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
          · rcases Nat.eq_zero_or_pos u with hu0 | hu1
            · subst hu0
              omega
            · have hle : 2 * u ≤ u * (2 * u + 1) := by
                calc 2 * u = u * 2 := by ring
                  _ ≤ u * (2 * u + 1) := Nat.mul_le_mul_left u (by omega)
              omega
          · have hsub : 4 * (j + u * (2 * u + 1)) + 1 - 2 * (2 * u) * (2 * u + 1) = 4 * j + 1 := by
              have hone : 4 * (j + u * (2 * u + 1)) + 1
                  = (4 * j + 1) + 2 * (2 * u) * (2 * u + 1) := by ring
              omega
            rw [hsub]
            exact hprime
      exact hmem
    · rintro ⟨j1, u1⟩ - ⟨j2, u2⟩ - heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hne, hke⟩ := heq
      have hu : u1 = u2 := by omega
      have hj : j1 = j2 := by
        rw [hu] at hne
        omega
      rw [hj, hu]
  have h2 : Q.card ≤ ∑ n ∈ s, (t n).card := by
    rw [hQ]
    refine (Finset.card_biUnion_le).trans ?_
    refine Finset.sum_le_sum fun n _ => ?_
    exact le_of_eq (Finset.card_image_of_injOn (f := fun k => (n, k)) (by
      intro a _ b _ hab
      simpa using hab))
  rw [← Finset.card_product]
  exact h1.trans h2

/-! ### 2. The corrected forward reduction: the leaf follows from the prime count

The earlier pass's hypothesis here was `c * X ≤ #{j ≤ X / 2 : 4j + 1 prime}`, which is false: that
cardinality is `~ X / (2 log X)`.  The hypothesis below is the true shape of the missing input. -/

/-- **The repaired `leaf_first_moment_card`, from the prime count in the class `1 mod 4`.**  Given
`c * X / log X ≤ #{j ∈ [1, X/2] : (4j + 1).Prime}` and the cardinality form of `R` (the repair),
the first moment over the representable `n ≤ X` is at least `(c/16) * X * sqrt X / log X`: the
`k`-count is `sqrt X / 16` by `card_k_ge`, and the two factors multiply. -/
private theorem leaf_first_moment_card_of_prime_count (R : ℕ → ℕ)
    (hRdef : ∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card)
    (hpi : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c * (X : ℝ) / Real.log (X : ℝ)
        ≤ (((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ X : ℕ in Filter.atTop,
      a * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ) ≤
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ)) := by
  classical
  obtain ⟨c, hc, hpi⟩ := hpi
  refine ⟨c / 16, by positivity, ?_⟩
  filter_upwards [hpi, Filter.eventually_ge_atTop (4096 : ℕ)] with X hpiX hX
  have hsum : Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
        (fun n => (R n : ℝ))
      = ((∑ n ∈ (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)),
            ((Finset.range (4 * n + 2)).filter
              (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [hRdef n])
  rw [hsum]
  have hpairsR : (((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card : ℝ)
        * (((Finset.range (X + 1)).filter (fun u => 2 * u * (2 * u + 1) ≤ X)).card : ℝ)
      ≤ ((∑ n ∈ (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)),
            ((Finset.range (4 * n + 2)).filter
              (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card : ℕ) : ℝ) := by
    exact_mod_cast first_moment_pairs X
  have hK := card_k_ge X hX
  have hprod : c * (X : ℝ) / Real.log (X : ℝ) * (Real.sqrt (X : ℝ) / 16)
      ≤ ((∑ n ∈ (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)),
            ((Finset.range (4 * n + 2)).filter
              (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card : ℕ) : ℝ) :=
    (mul_le_mul hpiX hK (by positivity) (by positivity)).trans hpairsR
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have h0 : (0 : ℕ) < X := by omega
    exact_mod_cast h0
  have hLpos : 0 < Real.log (X : ℝ) := by
    refine Real.log_pos ?_
    have : (1 : ℝ) < (X : ℝ) := by
      have h1 : (1 : ℕ) < X := by omega
      exact_mod_cast h1
    linarith
  have hid : c / 16 * (X : ℝ) * Real.sqrt (X : ℝ) / Real.log (X : ℝ)
      = c * (X : ℝ) / Real.log (X : ℝ) * (Real.sqrt (X : ℝ) / 16) := by
    field_simp
  rw [hid]
  exact hprod

/-- On primes `Λ n = log n`, which converts the class-`1 mod 4` theta into a `Λ`-sum. -/
private lemma classTheta_eq_sum_classPsi_prime (x : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ n.Prime), Real.log n)
      = (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ n.Prime),
          ArithmeticFunction.vonMangoldt n) := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2.2).symm

/-- The class-`1 mod 4` theta is at most the class-`1 mod 4` psi. -/
private lemma classTheta_le_classPsi (x : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ n.Prime), Real.log n)
      ≤ (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4),
          ArithmeticFunction.vonMangoldt n) := by
  rw [classTheta_eq_sum_classPsi_prime]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Splitting the class-`1 mod 4` psi into its prime and non-prime parts. -/
private lemma classPsi_eq_add (x : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4),
        ArithmeticFunction.vonMangoldt n)
      = (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ n.Prime), Real.log n)
        + (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ ¬ n.Prime),
            ArithmeticFunction.vonMangoldt n) := by
  classical
  have hBB : ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4)).filter (fun n => ¬ n.Prime)
      = (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ ¬ n.Prime) := by
    rw [Finset.filter_filter]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4)) (p := fun n => n.Prime)
    (f := fun n => ArithmeticFunction.vonMangoldt n)
  rw [Finset.filter_filter] at hsplit
  rw [← hsplit, ← classTheta_eq_sum_classPsi_prime, hBB]

/-- The class-`1 mod 4` theta is at least the class psi minus the whole `ψ - θ`. -/
private lemma classTheta_ge_classPsi_sub (x : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4),
        ArithmeticFunction.vonMangoldt n) - (Chebyshev.psi x - Chebyshev.theta x)
      ≤ (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ n.Prime), Real.log n) := by
  classical
  rw [classPsi_eq_add]
  have h2 : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4 ∧ ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n) ≤ Chebyshev.psi x - Chebyshev.theta x := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
      exact ⟨by omega, hn.2.2⟩
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  linarith

/-- The prime count in the class `1 mod 4` up to `x`, multiplied by `log x`, dominates the class
theta: `θ₄ x ≤ #{p ≡ 1 (4), p ≤ x} · log x`. -/
private lemma classTheta_le_card_mul_log (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime), Real.log p)
      ≤ (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ)
          * Real.log x := by
  classical
  have hterm : ∀ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime),
      Real.log (p : ℝ) ≤ Real.log x := by
    intro p hp
    obtain ⟨hpI, -, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hpx⟩ := Finset.mem_Icc.mp hpI
    have hp1' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hle : (p : ℝ) ≤ x := by
      have h1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hpx
      have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      linarith
    exact Real.log_le_log hp1' hle
  calc (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime), Real.log p)
      ≤ ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime), Real.log x :=
        Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ)
          * Real.log x := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `j ↦ 4j+1` is a bijection from the `j`-set of the prime count onto the primes `1 mod 4` up to
`2X + 1`. -/
private lemma image_four_mul_add_one (X : ℕ) :
    ((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).image (fun j => 4 * j + 1)
      = (Finset.Icc 1 (2 * X + 1)).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hjI, hjp⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hjX⟩ := Finset.mem_Icc.mp hjI
    have hdiv : 4 * (X / 2) ≤ 2 * X := by
      have h := Nat.div_mul_le_self X 2
      omega
    have hle : 4 * j + 1 ≤ 2 * X + 1 := by
      have h1 : 4 * j ≤ 4 * (X / 2) := Nat.mul_le_mul_left 4 hjX
      omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_, hjp⟩
    simp [Nat.add_mod]
  · intro hp
    obtain ⟨hpI, hmod, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hpX⟩ := Finset.mem_Icc.mp hpI
    have hmod1 : p % 4 = 1 := by omega
    have hpform : p = 4 * (p / 4) + 1 := by omega
    have hp2 := hpp.two_le
    have hp5 : 5 ≤ p := by omega
    refine Finset.mem_image.mpr ⟨p / 4, ?_, by rw [← hpform]⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hpform ▸ hpp⟩
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega

/-- The cardinality of the `j`-set equals the number of primes `1 mod 4` up to `2X+1`. -/
private lemma card_four_mul_add_one (X : ℕ) :
    ((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card
      = ((Finset.Icc 1 (2 * X + 1)).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card := by
  classical
  have hinj : Function.Injective (fun j : ℕ => 4 * j + 1) := by
    intro a b hab
    simp only at hab
    omega
  rw [← image_four_mul_add_one X, Finset.card_image_of_injective _ hinj]

/-- `exp (-c √log x) → 0`, in the explicit form needed below. -/
private lemma exp_neg_sqrt_log_le_of_le {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∃ T : ℝ, ∀ x : ℝ, T ≤ x → Real.exp (-c * Real.sqrt (Real.log x)) ≤ r := by
  by_cases h1 : (1 : ℝ) ≤ r
  · refine ⟨1, fun x _ => ?_⟩
    have h0 : Real.exp (-c * Real.sqrt (Real.log x)) ≤ Real.exp 0 := by
      refine Real.exp_le_exp.mpr ?_
      have := Real.sqrt_nonneg (Real.log x)
      nlinarith
    calc Real.exp (-c * Real.sqrt (Real.log x)) ≤ Real.exp 0 := h0
      _ = 1 := Real.exp_zero
      _ ≤ r := h1
  · have hlogr : 0 < -Real.log r := by
      have hr1 : r < 1 := lt_of_not_ge h1
      have : Real.log r < Real.log 1 := by
        refine Real.log_lt_log hr hr1
      rw [Real.log_one] at this
      linarith
    refine ⟨max 1 (Real.exp (((-Real.log r) / c) ^ 2) + 1), fun x hx => ?_⟩
    have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have hM : ((-Real.log r) / c) ^ 2 ≤ Real.log x := by
      have hxe : Real.exp (((-Real.log r) / c) ^ 2) < x := by
        have := le_max_right (1 : ℝ) (Real.exp (((-Real.log r) / c) ^ 2) + 1)
        linarith
      calc ((-Real.log r) / c) ^ 2 = Real.log (Real.exp (((-Real.log r) / c) ^ 2)) :=
            (Real.log_exp _).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxe.le
    have hbase : 0 ≤ (-Real.log r) / c := by positivity
    have hsq : Real.sqrt (((-Real.log r) / c) ^ 2) = (-Real.log r) / c := Real.sqrt_sq hbase
    have hsqrt : (-Real.log r) / c ≤ Real.sqrt (Real.log x) := by
      rw [← hsq]
      exact Real.sqrt_le_sqrt hM
    have hstep : -c * Real.sqrt (Real.log x) ≤ Real.log r := by
      have hmul : c * ((-Real.log r) / c) ≤ c * Real.sqrt (Real.log x) :=
        mul_le_mul_of_nonneg_left hsqrt hc.le
      rw [mul_div_cancel₀ _ (ne_of_gt hc)] at hmul
      linarith
    calc Real.exp (-c * Real.sqrt (Real.log x)) ≤ Real.exp (Real.log r) :=
          Real.exp_le_exp.mpr hstep
      _ = r := Real.exp_log hr

/-- For `x ≥ 64⁴`, `2 √x log x ≤ x / 8`. -/
private lemma two_sqrt_mul_log_le {x : ℝ} (hx : (64 : ℝ) ^ 4 ≤ x) :
    2 * Real.sqrt x * Real.log x ≤ x / 8 := by
  have hx0 : 0 < x := by positivity
  have hlog : Real.log x ≤ 4 * x ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div (x := x) (ε := (1 : ℝ) / 4) hx0.le (by norm_num)
    calc Real.log x ≤ x ^ ((1 : ℝ) / 4) / (1 / 4) := h
      _ = 4 * x ^ ((1 : ℝ) / 4) := by ring
  have hquarter : (64 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by
    have h64 : ((64 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = 64 := by
      have h1 : ((64 : ℝ) ^ 4 : ℝ) = (64 : ℝ) ^ (4 : ℝ) :=
        (Real.rpow_natCast (64 : ℝ) 4).symm
      rw [h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 64)]
      norm_num
    rw [← h64]
    exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hsqroot : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
  have hcomb : x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 4) = x ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hb : 0 < x ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hx0 _
  have hxeq : x ^ ((3 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have key : x ^ ((3 : ℝ) / 4) ≤ x / 64 := by
    have h1 : x ^ ((3 : ℝ) / 4) = x / x ^ ((1 : ℝ) / 4) := by
      rw [eq_div_iff (ne_of_gt hb)]
      linarith [hxeq]
    rw [h1]
    exact div_le_div_of_nonneg_left hx0.le (by norm_num) hquarter
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h4 : 0 ≤ 4 * x ^ ((1 : ℝ) / 4) := by positivity
  calc 2 * Real.sqrt x * Real.log x
      ≤ 2 * Real.sqrt x * (4 * x ^ ((1 : ℝ) / 4)) := by nlinarith
    _ = 8 * (Real.sqrt x * x ^ ((1 : ℝ) / 4)) := by ring
    _ = 8 * x ^ ((3 : ℝ) / 4) := by rw [hsqroot, hcomb]
    _ ≤ 8 * (x / 64) := by linarith
    _ = x / 8 := by ring

/-- **The prime count in the class `1 mod 4`.**  From Siegel-Walfisz at modulus `4`: the class
`1 mod 4` theta at `2X + 1` is eventually at least `X / 2`, the prime-power part of the class psi is
at most `2 √(2X+1) log (2X+1)`, and hence the number of primes `1 mod 4` below `2X + 1` is at least
`X / (4 log X)`. -/
private lemma prime_count_mod_four_of_siegel :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c * (X : ℝ) / Real.log (X : ℝ)
        ≤ (((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card : ℝ) := by
  classical
  obtain ⟨c₁, hc₁, K, hK⟩ := LeanLab.PNTPort.PsiChi.siegelWalfisz 2 (by norm_num)
  set K' : ℝ := max K 1 with hK'def
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right K 1)
  have hKle : K ≤ K' := le_max_left K 1
  obtain ⟨T, hT⟩ := exp_neg_sqrt_log_le_of_le hc₁ (r := 1 / (8 * K')) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt T
  refine ⟨1 / 8, by norm_num, Filter.eventually_atTop.mpr ⟨max N (max 8 (64 ^ 4)), ?_⟩⟩
  intro X hX
  set x : ℝ := ((2 * X + 1 : ℕ) : ℝ) with hxdef
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hX8 : 8 ≤ X :=
    le_trans (le_trans (le_max_left 8 (64 ^ 4)) (le_max_right N (max 8 (64 ^ 4)))) hX
  have hX64 : 64 ^ 4 ≤ X :=
    le_trans (le_trans (le_max_right 8 (64 ^ 4)) (le_max_right N (max 8 (64 ^ 4)))) hX
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hTx : T ≤ x := by
    have h1 : T ≤ (N : ℝ) := le_of_lt hN
    have h2 : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXN
    have h3 : (X : ℝ) ≤ x := by rw [hxdef]; push_cast; linarith
    linarith
  have hxX : (X : ℝ) ≤ x := by rw [hxdef]; push_cast; linarith
  have hx0 : (0 : ℝ) < x := by
    have : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    linarith
  have hxbig : (64 : ℝ) ^ 4 ≤ x := by
    have h1 : (64 : ℝ) ^ 4 ≤ (X : ℝ) := by exact_mod_cast hX64
    linarith
  have hx2 : 2 ≤ x := by linarith
  have hfloor : ⌊x⌋₊ = 2 * X + 1 := by rw [hxdef, Nat.floor_natCast]
  have hlog_ge : (2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log ((64 : ℝ) ^ 4) ≤ Real.log x := Real.log_le_log (by positivity) hxbig
    have h64 : (2 : ℝ) ≤ Real.log ((64 : ℝ) ^ 4) := by
      have hlog4 : Real.log ((64 : ℝ) ^ 4) = 24 * Real.log 2 := by
        calc Real.log ((64 : ℝ) ^ 4) = 4 * Real.log (64 : ℝ) := Real.log_pow (64 : ℝ) 4
          _ = 4 * Real.log ((2 : ℝ) ^ 6) := by norm_num
          _ = 4 * (6 * Real.log 2) := by rw [Real.log_pow]; norm_num
          _ = 24 * Real.log 2 := by ring
      rw [hlog4]
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hlog4 : (4 : ℝ) ≤ Real.log x ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hpsi := hK x hx2 4 1 (by norm_num) (by norm_num) hlog4
  have htot : (Nat.totient 4 : ℝ) = 2 := by
    have h4 : Nat.totient 4 = 2 := by decide
    rw [h4]
    norm_num
  have hpsi' : |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4),
        ArithmeticFunction.vonMangoldt n) - x / 2|
      ≤ K * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) := by
    simp only [LeanLab.HeathBrown1985.psi, htot] at hpsi
    exact hpsi
  have hdecay : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ 1 / (8 * K') := hT x hTx
  have hKdecay : K * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ 1 / 8 := by
    have h1 : K * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ K' * (1 / (8 * K')) :=
      mul_le_mul hKle hdecay (Real.exp_pos _).le (by linarith)
    have h2 : K' * (1 / (8 * K')) = 1 / 8 := by
      field_simp
    linarith
  have herr : K * x * Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ x / 8 := by
    calc K * x * Real.exp (-c₁ * Real.sqrt (Real.log x))
        = x * (K * Real.exp (-c₁ * Real.sqrt (Real.log x))) := by ring
      _ ≤ x * (1 / 8) := mul_le_mul_of_nonneg_left hKdecay hx0.le
      _ = x / 8 := by ring
  have hpsi_lower : x / 2 - x / 8 ≤
      (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % 4 = 1 % 4),
        ArithmeticFunction.vonMangoldt n) := by
    have h := (abs_le.mp hpsi').1
    linarith
  have htheta_lower : x / 4 ≤
      (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime),
        Real.log (p : ℝ)) := by
    have h2 := classTheta_ge_classPsi_sub x
    have h3 : Chebyshev.psi x - Chebyshev.theta x ≤ 2 * Real.sqrt x * Real.log x :=
      Chebyshev.psi_sub_theta_le (by linarith)
    have h4 : 2 * Real.sqrt x * Real.log x ≤ x / 8 := two_sqrt_mul_log_le hxbig
    linarith
  have hcard_mul : (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime),
        Real.log (p : ℝ))
      ≤ (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ)
          * Real.log x := classTheta_le_card_mul_log x hx2
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog_ge
  have hcard_ge : x / (4 * Real.log x)
      ≤ (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ) := by
    have h : x / 4 ≤ (((Finset.Icc 1 ⌊x⌋₊).filter
        (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ) * Real.log x :=
      le_trans htheta_lower hcard_mul
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * Real.log x)]
    nlinarith [h]
  have hcard2 : (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ)
      = (((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card : ℝ) := by
    have h1 : ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card
        = ((Finset.Icc 1 (2 * X + 1)).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card := by
      rw [hfloor]
    rw [h1, ← card_four_mul_add_one X]
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlogx_le : Real.log x ≤ 2 * Real.log (X : ℝ) := by
    have hX3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
    have h3X : x ≤ 3 * (X : ℝ) := by rw [hxdef]; push_cast; linarith
    have hlog3X : Real.log x ≤ Real.log (3 * (X : ℝ)) :=
      Real.log_le_log (by linarith) h3X
    have hsplit : Real.log (3 * (X : ℝ)) = Real.log 3 + Real.log (X : ℝ) :=
      Real.log_mul (by norm_num) (by positivity)
    have hlog3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hX3
    linarith
  have hfinal : (1 / 8) * (X : ℝ) / Real.log (X : ℝ) ≤ x / (4 * Real.log x) := by
    rw [div_le_div_iff₀ hlogX (by linarith : (0:ℝ) < 4 * Real.log x)]
    have h1 : (1 / 8) * (X : ℝ) * (4 * Real.log x) ≤ (1 / 2) * (X : ℝ) * (2 * Real.log (X : ℝ)) :=
      by nlinarith [hlogx_le, hX0]
    have h2 : (1 / 2) * (X : ℝ) * (2 * Real.log (X : ℝ)) = (X : ℝ) * Real.log (X : ℝ) := by ring
    have h3 : (X : ℝ) * Real.log (X : ℝ) ≤ x * Real.log (X : ℝ) :=
      mul_le_mul_of_nonneg_right hxX hlogX.le
    linarith
  calc (1 / 8) * (X : ℝ) / Real.log (X : ℝ) ≤ x / (4 * Real.log x) := hfinal
    _ ≤ (((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p % 4 = 1 % 4 ∧ p.Prime)).card : ℝ) := hcard_ge
    _ = (((Finset.Icc 1 (X / 2)).filter (fun j => (4 * j + 1).Prime)).card : ℝ) := hcard2

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
          (fun n => (R n : ℝ)) :=
  leaf_first_moment_card_of_prime_count R hRdef prime_count_mod_four_of_siegel

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
