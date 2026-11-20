import LeanLab.OpenProblems.SPLIT_route_euler_positive_density

/-!
# Flag U-1733, OpenProblems, `leaf_second_moment_card`

AI wrote the Lean code. Goldbach is open.

Part A. The refutation.  The sealed leaf `leaf_second_moment_card` in
`SPLIT_route_euler_positive_density.lean` quantifies over every `R` whose zero set off `n = 0`
is the non representable set.  That hypothesis fixes only where `R` vanishes, not its size, so
`R n = n ^ 2` on representable `n` meets it and its square sum at a representable `X` is at least
`X ^ 4`, beyond `b * X ^ 2 / log X ^ 2` for every `b`.  Representable `n` are infinitely many:
`n = (p - 1) / 4` for each prime `p` that is `1 mod 4`, with odd square `1`.

Part B. The corrected sealed Prop `SecondMomentDQ1733`, which adds the cardinality hypothesis
`hRdef` that LEAF 2 already carries after its own repair.  The assembly
`route_euler_positive_density_split` gets that equation from LEAF 1, so the route survives with
the corrected leaf in place of the old one.  Part C proves the route from the corrected leaf.
-/

namespace LeanLab.OpenProblems.Flag1733

open LeanLab LeanLab.OpenProblems.State1612
open scoped Classical

/-- The exact sealed statement of `leaf_second_moment_card`, as a named Prop. -/
def SecondMomentAsSealed : Prop :=
  ∀ R : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2

/-- Match: the named Prop is the sealed leaf, so the sealed leaf's proof term inhabits it. -/
theorem secondMomentAsSealed_match :
    SecondMomentAsSealed ↔
      (∀ R : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
        ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
          Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
              (fun n => (R n : ℝ) ^ 2)
            ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := Iff.rfl

/-- Representable `n` are unbounded: `4n + 1` prime gives `8n + 3 = 1 + 2(4n + 1)`. -/
theorem isEuler_frequently : ∃ᶠ n : ℕ in Filter.atTop, IsEuler (8 * n + 3) := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨p, hp, hpN, hmod⟩ := Nat.exists_prime_gt_modEq_one (4 * N + 1) (by norm_num : 4 ≠ 0)
  have h1 : p % 4 = 1 := by
    have := hmod; unfold Nat.ModEq at this; simpa using this
  refine ⟨p / 4, by omega, 1, p, odd_one, hp, by omega⟩

/-- The counterexample multiplicity: `n ^ 2` where representable, else `0`. -/
noncomputable def badR (n : ℕ) : ℕ := if IsEuler (8 * n + 3) then n ^ 2 else 0

theorem badR_hyp : ∀ n : ℕ, 1 ≤ n → (badR n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
  intro n hn
  unfold badR
  split_ifs with h
  · simp [h]; omega
  · simp [h]

/-- FALSE: the sealed `leaf_second_moment_card` fails, with `badR` as witness. -/
theorem not_secondMomentAsSealed : ¬ SecondMomentAsSealed := by
  intro H
  obtain ⟨b, hb, hev⟩ := H badR badR_hyp
  have hev2 : ∀ᶠ X : ℕ in Filter.atTop, (b + 1 < (X : ℝ) ^ 2 ∧ 3 ≤ X) ∧
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (badR n : ℝ) ^ 2) ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
    refine Filter.Eventually.and ?_ hev
    have h1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (b + 1)
    filter_upwards [h1, Filter.eventually_ge_atTop 3] with X hX h3
    refine ⟨?_, h3⟩
    have : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
    nlinarith
  obtain ⟨X, ⟨⟨hXb, hX3⟩, hle⟩, hE⟩ := (hev2.and_frequently isEuler_frequently).exists
  have hmem : X ∈ (Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)) := by
    simp [hE]; omega
  have hterm : ((badR X : ℕ) : ℝ) ^ 2 ≤
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (badR n : ℝ) ^ 2) :=
    Finset.single_le_sum (f := fun n => (badR n : ℝ) ^ 2) (fun _ _ => by positivity) hmem
  have hbad : (badR X : ℝ) = (X : ℝ) ^ 2 := by simp [badR, hE]
  rw [hbad] at hterm
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlog1 : 1 ≤ Real.log (X : ℝ) := by
    rw [Real.le_log_iff_exp_le hX0]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : (3 : ℝ) ≤ X := by exact_mod_cast hX3
    linarith
  have hdiv : b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 ≤ b * (X : ℝ) ^ 2 := by
    apply div_le_self (by positivity)
    nlinarith
  have hX2 : (0 : ℝ) < (X : ℝ) ^ 2 := by positivity
  nlinarith

/-- CORRECTED LEAF 3, sealed open statement for provers.
Twin: for the multiplicity `R n` equal to the number of `k` with `4n + 1 - 2k(k+1)` prime, there is
a fixed `b > 0` such that, for all large `X`, the sum of `R n ^ 2` over representable `n` in
`[1, X]` is at most `b X ^ 2 / log X ^ 2`.
Source: `SPLIT_route_euler_positive_density.lean`, leaf 3, repaired the same way as leaf 2 by
the pinning hypothesis `hRdef`; the size claim is the standard upper sieve bound for pairs of
primes `p, q` with `p - q` a difference of two triangular numbers. -/
def SecondMomentDQ1733 : Prop :=
  ∀ R : ℕ → ℕ,
    (∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
        (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) →
    (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
      Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
          (fun n => (R n : ℝ) ^ 2)
        ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2

/-- Vacuity instance: the hypotheses of the corrected leaf are met by the `R` of LEAF 1. -/
theorem secondMomentDQ1733_hyps_satisfiable :
    ∃ R : ℕ → ℕ,
      (∀ n : ℕ, R n = ((Finset.range (4 * n + 2)).filter
          (fun k => (4 * n + 1 - 2 * k * (k + 1)).Prime)).card) ∧
      ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) :=
  leaf_representation_multiplicity

/-- Part C, route: the sealed target follows from the corrected leaf, through leaves 1, 2, 4, 5. -/
theorem route_of_SecondMomentDQ1733 (h : SecondMomentDQ1733) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop, c * X ≤ ((X - euExc X : ℕ) : ℝ) := by
  obtain ⟨R, hRdef, hR⟩ := leaf_representation_multiplicity
  obtain ⟨a, ha, hfirst⟩ := leaf_first_moment_card R hRdef hR
  obtain ⟨b, hb, hsecond⟩ := h R hRdef hR
  obtain ⟨c, hc, hcard⟩ := leaf_cauchy_schwarz_density R hR a b ha hb hfirst hsecond
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcard] with X hX
  rw [← leaf_card_eq_complement X]
  exact hX

end LeanLab.OpenProblems.Flag1733
