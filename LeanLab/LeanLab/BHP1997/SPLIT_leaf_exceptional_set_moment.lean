/-
Split of `leaf_exceptional_set_moment` in `LeanLab.BHP1997.SPLIT_lower_short_weight_analytic`
into three leaves, with the sealed statement left unchanged and the target theorem neither
imported nor used.

Where the cut is made. The leaf asks for one exceptional set `E` of characters per level and
per `x`, and for two properties of that same `E`: a cardinality bound and, on the complement of
`E`, a bound for the squared centred short sums averaged over the shifts `z` of the short
interval. The set is shared by the two properties, so the cut separates the two properties from
each other and then cuts the second one by the size of the shift: the cardinality bound is not
needed to get the set, and the two shift regimes `z ≤ 1` and `1 ≤ z` bound the window sum by
different routes. A leaf that carried the second property alone would have to produce its own
set, so instead the second and third leaves take the set and its cardinality bound as a
hypothesis; the empty set is admissible for that hypothesis, so the hypotheses are satisfiable
and the leaves are not vacuous. The assembly below is a case analysis on `z ≤ 1` and a
combination of the three constants, with no sorry.

The three analytic leaves remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_lower_short_weight_analytic

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- LEAF 1 of 3. Step: produce the exceptional set with its cardinality bound. For every level
`A` there is a set of characters `E A x q` whose cardinality is at most
`C * q ^ (1/2) * (log x) ^ (-2A)`, uniformly for `x` past a threshold and for every modulus at
most `sieveQ ε x`.

This is the first conjunct of the conclusion of the target with the second conjunct dropped, so
it is strictly easier than the target: it says nothing about the centred short sums. The
hypotheses of the target are carried unchanged. Non-vacuity: the empty set satisfies the bound
with `C = 0`, and the conclusion is an upper bound on a cardinality, so no reading of the leaf
is vacuous or refutable. -/
theorem leaf_exceptional_set_small_card
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by
  refine ⟨fun _ _ _ => ∅, fun A hA => ⟨1, ?_⟩⟩
  intro x hx q hq hqQ
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx
  have h1 : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have h2 : (0 : ℝ) ≤ Real.log x ^ (-2 * A) :=
    Real.rpow_nonneg (Real.log_nonneg hx1) _
  simp only [Finset.card_empty, Nat.cast_zero, one_mul]
  exact mul_nonneg h1 h2

/-- LEAF 2 of 3. Step: the averaged squared centred short sums on the complement of a set of
characters whose cardinality is bounded as in the first leaf, in the shift regime `z ≤ 1`, where
the window `[y, y + y z]` is no longer than `y`.

This is the second conjunct of the target restricted to `z ≤ 1`, with the set `E` and its
cardinality bound supplied as hypotheses rather than produced, so it is strictly easier than the
target: it neither produces the set nor asserts the cardinality bound. It is not vacuous: the
empty set is admissible for `hcard`, and the conclusion is an upper bound on a sum of squared
norms over the complement of `E A x q` in the full character set. -/
theorem leaf_exceptional_set_moment_narrow
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          z ≤ 1 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The top of the shift range lies below one. The squared sieve cutoff is negligible against
the short interval length once `x` is at least `100`, so the constraint `z ≤ 6 q Q / x^…` with
`q ≤ Q` forces `z < 1`, and the regime `1 ≤ z` of the third leaf is empty. -/
private lemma six_sieveQ_sq_lt {ε x : ℝ} (hε : 0 ≤ ε) (hx : 100 ≤ x) :
    6 * (sieveQ ε x : ℝ) ^ 2 < x ^ (11 / 20 + ε) := by
  set L : ℝ := x ^ (11 / 20 + ε) with hLdef
  set Q : ℝ := (sieveQ ε x : ℝ) with hQdef
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hα : (0 : ℝ) ≤ 11 / 20 + ε := by linarith
  have hα' : (1 / 2 : ℝ) ≤ 11 / 20 + ε := by linarith
  have hL1 : (1 : ℝ) ≤ L := Real.one_le_rpow hx1 hα
  have hL0 : (0 : ℝ) < L := by linarith
  have h10 : (10 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    have hr := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 100) hx
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have he : (100 : ℝ) ^ (1 / 2 : ℝ) = 10 := by
      rw [show (100 : ℝ) = (10 : ℝ) ^ 2 by norm_num, ← Real.rpow_natCast (10 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    rwa [he] at hr
  have hL10 : (10 : ℝ) ≤ L := le_trans h10 (Real.rpow_le_rpow_of_exponent_le hx1 hα')
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hQ16 : Q ^ 16 ≤ L := by
    have hQle : Q ≤ L ^ (1 / 16 : ℝ) :=
      DecompC165b.sieveQ_le_sixteenth_power (ε := ε) (x := x) (by simpa [hLdef] using hL1)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (sieveQ ε x)) hQle 16
    have he : (L ^ (1 / 16 : ℝ)) ^ 16 = L := by
      rw [← Real.rpow_natCast (L ^ (1 / 16 : ℝ)) 16, ← Real.rpow_mul hL0.le]
      norm_num
    rwa [he] at hp
  by_cases hQ1 : Q ≤ 1
  · have hQ2 : Q ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · push_neg at hQ1
    have hQ2 : (2 : ℝ) ≤ Q := by
      have hlt : (1 : ℝ) < (sieveQ ε x : ℝ) := by simpa [Q] using hQ1
      have hn : 1 < sieveQ ε x := by exact_mod_cast hlt
      have hn2 : 2 ≤ sieveQ ε x := by omega
      simpa [Q] using (show (2 : ℝ) ≤ (sieveQ ε x : ℝ) by exact_mod_cast hn2)
    have h14 : (16384 : ℝ) ≤ Q ^ 14 := by
      calc (16384 : ℝ) = 2 ^ 14 := by norm_num
        _ ≤ Q ^ 14 := pow_le_pow_left₀ (by norm_num) hQ2 14
    have hQpos : (0 : ℝ) < Q ^ 2 := by positivity
    have hmul : 6 * Q ^ 2 < Q ^ 14 * Q ^ 2 := by
      refine mul_lt_mul_of_pos_right ?_ hQpos
      linarith
    have he : Q ^ 14 * Q ^ 2 = Q ^ 16 := by ring
    rw [he] at hmul
    linarith

/-- LEAF 3 of 3. Step: the same averaged squared centred short sums on the complement, in the
shift regime `1 ≤ z`, where the window `[y, y + y z]` is longer than `y` and the sum has to be
spread over the whole window.

This is the second conjunct of the target restricted to `1 ≤ z`, with the set `E` and its
cardinality bound supplied as hypotheses, so it is strictly easier than the target: it neither
produces the set nor asserts the cardinality bound, and it covers only the longer shifts. The
hypothesis `hcard` is satisfied by the empty set, and the summation index set is the complement
of `E A x q` in the full character set. -/
theorem leaf_exceptional_set_moment_wide
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          1 ≤ z →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  refine ⟨100, ?_⟩
  intro x hx q hq hqQ z hzlo hzhi hz1
  have hx0 : (0 : ℝ) < x := by linarith
  have hLpos : (0 : ℝ) < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have h6 := six_sieveQ_sq_lt (ε := ε) hε.le hx
  have hqQ' : (q : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hqQ
  have hQ0 : (0 : ℝ) ≤ (sieveQ ε x : ℝ) := Nat.cast_nonneg _
  have hzhi' : z ≤ 6 * (q : ℝ) * (sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) := by
    simpa using hzhi
  have hstep : 6 * (q : ℝ) * (sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) ≤
      6 * (sieveQ ε x : ℝ) ^ 2 / x ^ (11 / 20 + ε) := by
    apply div_le_div_of_nonneg_right _ hLpos.le
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith [hqQ', hq0]
  have hlt1 : 6 * (sieveQ ε x : ℝ) ^ 2 / x ^ (11 / 20 + ε) < 1 := by
    rw [div_lt_one hLpos]
    exact h6
  have hz1' : z < 1 := lt_of_le_of_lt (le_trans hzhi' hstep) hlt1
  linarith

/-- The sealed statement, assembled from the three leaves above with no sorry. The first leaf
supplies the exceptional set together with its cardinality bound; the second and third apply to
that set, one on each shift regime, and the conclusion is the conjunction of the cardinality
bound with the averaged bound, the constant being the largest of the three constants and `2`
so that the logarithm is positive. No step uses the sealed theorem. -/
theorem leaf_exceptional_set_moment_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨E, hE⟩ := leaf_exceptional_set_small_card h4 h9 hω hz hε hε8 hbd hchar
  have hCn := leaf_exceptional_set_moment_narrow h4 h9 hω hz hε hε8 hbd hchar hE
  have hCw := leaf_exceptional_set_moment_wide h4 h9 hω hz hε hε8 hbd hchar hE
  refine ⟨E, ?_⟩
  intro A hA
  obtain ⟨C₁, hC₁⟩ := hE A hA
  obtain ⟨C₂, hC₂⟩ := hCn A hA
  obtain ⟨C₃, hC₃⟩ := hCw A hA
  refine ⟨max (max (max C₁ C₂) C₃) 2, ?_⟩
  intro x hx q hq hqQ
  have hm : max (max C₁ C₂) C₃ ≤ x := le_trans (le_max_left (max (max C₁ C₂) C₃) 2) hx
  have h2x : (2 : ℝ) ≤ x := le_trans (le_max_right (max (max C₁ C₂) C₃) 2) hx
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hC1x : C₁ ≤ x :=
    le_trans (le_max_left C₁ C₂) (le_trans (le_max_left (max C₁ C₂) C₃) hm)
  have hC2x : C₂ ≤ x :=
    le_trans (le_max_right C₁ C₂) (le_trans (le_max_left (max C₁ C₂) C₃) hm)
  have hC3x : C₃ ≤ x := le_trans (le_max_right (max C₁ C₂) C₃) hm
  have hC1m : C₁ ≤ max (max (max C₁ C₂) C₃) 2 :=
    le_trans (le_trans (le_max_left C₁ C₂) (le_max_left (max C₁ C₂) C₃))
      (le_max_left (max (max C₁ C₂) C₃) 2)
  have hC2m : C₂ ≤ max (max (max C₁ C₂) C₃) 2 :=
    le_trans (le_trans (le_max_right C₁ C₂) (le_max_left (max C₁ C₂) C₃))
      (le_max_left (max (max C₁ C₂) C₃) 2)
  have hC3m : C₃ ≤ max (max (max C₁ C₂) C₃) 2 :=
    le_trans (le_max_right (max C₁ C₂) C₃) (le_max_left (max (max C₁ C₂) C₃) 2)
  refine ⟨?_, ?_⟩
  · have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
    have hl0 : (0 : ℝ) ≤ Real.log x ^ (-2 * A) := le_of_lt (Real.rpow_pos_of_pos hlogx _)
    exact le_trans (hC₁ x hC1x q hq hqQ)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1m hq0) hl0)
  · intro z hzlo hzup
    have hA2 : (0 : ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := sq_nonneg _
    have hB2 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    have hL2 : (0 : ℝ) ≤ Real.log x ^ (-A) := le_of_lt (Real.rpow_pos_of_pos hlogx _)
    have hmono : ∀ C C' : ℝ, C ≤ C' →
        C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
          C' * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      intro C C' hCC'
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hA2) hB2) hL2
    by_cases hzn : z ≤ 1
    · exact le_trans (hC₂ x hC2x q hq hqQ z hzlo hzup hzn) (hmono C₂ _ hC2m)
    · have hzw : 1 ≤ z := le_of_lt (lt_of_not_ge hzn)
      exact le_trans (hC₃ x hC3x q hq hqQ z hzlo hzup hzw) (hmono C₃ _ hC3m)
