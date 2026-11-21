/-
P0069 Baker Harman Pintz 1997, Section 5, pages 43, 48, 49 and 53. The non-principal half
of 1.9 for `(v / D) b1`, used by Prep1121UpslackRoute, split along the paper's sentence on page 53,
"We use Lemma 34 to obtain (5.1) and (5.2) for g_m, h_m and j_m", with Lemma 33 for the kept part
of k_m, and Lemma 29 on page 43 turning 5.1 and 5.2 into the window mean square over the
characters of F, outside E_q and not principal. Leaves: one per piece g, h, j, kept, each Lemma 34 or
Lemma 33 followed by Lemma 29, and the transfer from b1 to `(v / D) b1`. PROVED here: the mean square bound is stable under sums and
negation, with the union of the exceptional sets, since a window integrand is integrable, hence
the bound holds for b1 = g - h + j - kept, and the assembly. New file, no new definition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- A window integrand of 1.9 on page 3 is interval integrable: it is the square of the norm of a
finite sum of constants times indicators of the sets `y <= m <= y + y z`, so it is measurable and
bounded. PROVED. -/
theorem upslack_window_integrable (s : Finset ℕ) (g : ℕ → ℂ) (z a b : ℝ) :
    IntervalIntegrable (fun y : ℝ =>
      ‖∑ m ∈ s.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), g m‖ ^ 2) volume a b := by
  have hrw : (fun y : ℝ =>
      ‖∑ m ∈ s.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), g m‖ ^ 2) =
      fun y : ℝ => ‖∑ m ∈ s, if (y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) then g m else 0‖ ^ 2 := by
    funext y; rw [Finset.sum_filter]
  rw [hrw, intervalIntegrable_iff]
  have hmeas : Measurable fun y : ℝ =>
      ‖∑ m ∈ s, if (y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) then g m else 0‖ ^ 2 := by
    refine (continuous_norm.measurable.comp (Finset.measurable_sum _ fun m _ => ?_)).pow_const 2
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_le (f := fun y : ℝ => y) (g := fun _ : ℝ => (m : ℝ))
      measurable_id measurable_const).inter
      (measurableSet_le (f := fun _ : ℝ => (m : ℝ)) (g := fun y : ℝ => y + y * z)
        measurable_const (measurable_id.add (measurable_id.mul_const z)))
  refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
    ((∑ m ∈ s, ‖g m‖) ^ 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : ‖∑ m ∈ s, if (y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) then g m else 0‖ ≤
      ∑ m ∈ s, ‖g m‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    split_ifs
    · exact le_rfl
    · simp
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- LEAF: P0069 page 53 with Lemma 34 on page 49, applied with a_n the indicator of n = 1, so that b_m is g_m = psi(m, Y^c1), giving 5.1 and 5.2 on page 43, and then Lemma 29 on page 43
for the characters of F = E_q^c minus the principal character, where the `delta chi` term is zero.
HARD. -/
theorem upslack_piece_g_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperG ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 53 with Lemma 34 on page 49, applied with a_n the indicator of the primes Y^c1 <= n < Y^c4, so that b_m is h_m, giving 5.1 and 5.2 on page 43, and then Lemma 29 on page 43
for the characters of F = E_q^c minus the principal character, where the `delta chi` term is zero.
HARD. -/
theorem upslack_piece_h_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperH ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 53 with Lemma 34 on page 49, applied with a_n counting n = p1 p2, Y^c1 <= p2 < p1 < Y^c4, so n < Y^(2 c4) = Y^(1/2 + theta2/4 - 2 eps), and b_m is j_m, giving 5.1 and 5.2 on page 43, and then Lemma 29 on page 43
for the characters of F = E_q^c minus the principal character, where the `delta chi` term is zero.
HARD. -/
theorem upslack_piece_j_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperJ ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 53 with Lemma 33 on page 48, case 5.13, the triangle R or the parallelograms P1, P2, for each kept term of k_m, those for which Lemma 33 applies to some arrangement of the variables, giving 5.1 and 5.2 on page 43, and then Lemma 29 on page 43
for the characters of F = E_q^c minus the principal character, where the `delta chi` term is zero.
HARD. -/
theorem upslack_piece_kept_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperKept ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 43, Lemma 29 and its range `z <= 6 q Q / Y`: the non-principal window mean
square passes from b1 to `(v / D) b1`. On a window `[y, y + y z]` the factor `v / D` moves by at
most `|v| |K| z / c^2` times a constant, so the window sum of `(v / D) b1 chi` is `v / D` at the
left end times that of `b1 chi`, plus `O(z (Y z + 1))` by the bound `|b1| <= 1 + 18 + 18^2 + 18^3`;
squared, integrated over `[Y/2, 3Y]` and summed over at most `q` characters this is
`O(q (q Q)^4 / Y)`, which is `O((q Q)^2 Y L^-A)` since `q Q <= Y^theta2`. The `delta chi` term
vanishes off the principal character. MEDIUM. -/
theorem upslack_nonprincipal_transfer
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    (hraw : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → q ≤ sieveQ ε x →
          ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
          ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
            z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
            ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
              ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
                ‖∑ m ∈ (rightInterval ε x).filter
                    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                  ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
                C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The square of the norm of a sum is at most twice the sum of the squares. PROVED. -/
theorem upslack_norm_add_sq (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- P0069 page 43: the non-principal window mean square bound of Lemma 29's conclusion is stable
under the sum of two coefficients, with the union of the two exceptional sets. PROVED from the
integrability leaf. -/
theorem upslack_np_add {ε : ℝ} (b1 b2 : ℝ → ℕ → ℝ)
    (h1 : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → q ≤ sieveQ ε x →
          ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
          ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
            z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
            ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
              ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
                ‖∑ m ∈ (rightInterval ε x).filter
                    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                  ((b1 x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
                C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    (h2 : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → q ≤ sieveQ ε x →
          ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
          ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
            z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
            ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
              ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
                ‖∑ m ∈ (rightInterval ε x).filter
                    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                  ((b2 x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
                C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b1 x m + b2 x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨E1, hE1⟩ := h1
  obtain ⟨E2, hE2⟩ := h2
  refine ⟨fun A x q => E1 A x q ∪ E2 A x q, fun A hA => ?_⟩
  obtain ⟨C1, k1⟩ := hE1 A hA
  obtain ⟨C2, k2⟩ := hE2 A hA
  set M := max (max C1 C2) 1 with hM
  have hC1 : C1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM1 : 1 ≤ M := le_max_right _ _
  refine ⟨4 * M, fun x hx q hq hqQ => ?_⟩
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨c1, m1⟩ := k1 x (by linarith) q hq hqQ
  obtain ⟨c2, m2⟩ := k2 x (by linarith) q hq hqQ
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hP : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hL _)
  have hR : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg hL _)
  refine ⟨?_, fun z hz1 hz2 => ?_⟩
  · have hu : ((E1 A x q ∪ E2 A x q).card : ℝ) ≤ (E1 A x q).card + (E2 A x q).card := by
      exact_mod_cast Finset.card_union_le _ _
    have e : ∀ c' : ℝ, c' * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) =
        c' * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := fun c' => by ring
    rw [e] at c1 c2 ⊢
    have := mul_le_mul_of_nonneg_right hC1 hP
    have := mul_le_mul_of_nonneg_right hC2 hP
    nlinarith
  have i1 := m1 z hz1 hz2
  have i2 := m2 z hz1 hz2
  set Y := x ^ (11 / 20 + ε) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hab : Y / 2 ≤ 3 * Y := by linarith
  set F : DirichletCharacter ℂ q → (ℝ → ℕ → ℝ) → ℝ := fun χ b =>
    ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
      ((b x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 with hF
  have hF0 : ∀ χ b, 0 ≤ F χ b := fun χ b =>
    intervalIntegral.integral_nonneg hab (fun y _ => sq_nonneg _)
  have hpt : ∀ χ : DirichletCharacter ℂ q,
      F χ (fun x m => b1 x m + b2 x m) ≤ 2 * F χ b1 + 2 * F χ b2 := by
    intro χ
    simp only [hF]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        ((upslack_window_integrable _ _ z _ _).const_mul 2)
        ((upslack_window_integrable _ _ z _ _).const_mul 2)]
    apply intervalIntegral.integral_mono_on hab (upslack_window_integrable _ _ z _ _)
      (((upslack_window_integrable _ _ z _ _).const_mul 2).add
        ((upslack_window_integrable _ _ z _ _).const_mul 2))
    intro y _
    have e : ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        (((b1 x m + b2 x m : ℝ)) : ℂ) * χ (m : ZMod q) =
        (∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((b1 x m : ℝ) : ℂ) * χ (m : ZMod q)) +
        ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((b2 x m : ℝ) : ℂ) * χ (m : ZMod q) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast; ring
    rw [e]
    exact upslack_norm_add_sq _ _
  set S := ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ (E1 A x q ∪ E2 A x q)).erase 1
  have hS1 : S ⊆ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E1 A x q).erase 1 := by
    intro χ hχ
    simp only [S, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_union, not_or] at hχ ⊢
    exact ⟨hχ.1, hχ.2.1, hχ.2.2.1⟩
  have hS2 : S ⊆ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E2 A x q).erase 1 := by
    intro χ hχ
    simp only [S, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_union, not_or] at hχ ⊢
    exact ⟨hχ.1, hχ.2.1, hχ.2.2.2⟩
  have s1 : ∑ χ ∈ S, F χ b1 ≤ C1 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS1 fun χ _ _ => hF0 χ b1) i1
  have s2 : ∑ χ ∈ S, F χ b2 ≤ C2 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS2 fun χ _ _ => hF0 χ b2) i2
  have s3 : ∑ χ ∈ S, F χ (fun x m => b1 x m + b2 x m) ≤
      2 * ∑ χ ∈ S, F χ b1 + 2 * ∑ χ ∈ S, F χ b2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun χ _ => hpt χ
  have e : ∀ c' : ℝ, c' * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) =
      c' * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) := fun c' => by ring
  rw [e] at s1 s2
  rw [e]
  have := mul_le_mul_of_nonneg_right hC1 hR
  have := mul_le_mul_of_nonneg_right hC2 hR
  exact le_trans s3 (by nlinarith)

/-- P0069 page 43: the same bound is stable under negation of the coefficient. PROVED. -/
theorem upslack_np_neg {ε : ℝ} (b : ℝ → ℕ → ℝ)
    (h : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
        ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
          1 ≤ q → q ≤ sieveQ ε x →
          ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
          ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
            z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
            ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
              ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
                ‖∑ m ∈ (rightInterval ε x).filter
                    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                  ((b x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
                C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((-b x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨E, hE⟩ := h
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA
  refine ⟨C, fun x hx q hq hqQ => ?_⟩
  obtain ⟨hc, hm⟩ := hC x hx q hq hqQ
  refine ⟨hc, fun z hz1 hz2 => ?_⟩
  have := hm z hz1 hz2
  simpa only [Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib, norm_neg] using this

/-- P0069 page 53: the bound for b1 = g - h + j - kept from the four piece leaves, through the
sum and negation lemmas. PROVED from the leaves. -/
theorem upslack_raw_nonprincipal_mean_square
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  have e : ∀ (x : ℝ) (m : ℕ), upperRawWeight ε (x ^ (11 / 20 + ε)) m =
      ((upperG ε (x ^ (11 / 20 + ε)) m + -upperH ε (x ^ (11 / 20 + ε)) m) + upperJ ε (x ^ (11 / 20 + ε)) m) +
        -upperKept ε (x ^ (11 / 20 + ε)) m := by
    intro x m; unfold upperRawWeight; ring
  simp only [e]
  have key := upslack_np_add (ε := ε) _ _
    (upslack_np_add (ε := ε) _ _
      (upslack_np_add (ε := ε) _ _ (upslack_piece_g_mean_square h4 h9 hε hε8)
        (upslack_np_neg (ε := ε) _ (upslack_piece_h_mean_square h4 h9 hε hε8)))
      (upslack_piece_j_mean_square h4 h9 hε hε8))
    (upslack_np_neg (ε := ε) _ (upslack_piece_kept_mean_square h4 h9 hε hε8))
  exact key

/-- Page 3 display 1.9 over the characters of F for `(v / D) b1`, from the four piece leaves through the bound for b1 and the transfer leaf. -/
theorem upslack_nonprincipal_mean_square_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (v : ℝ) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  upslack_nonprincipal_transfer hε hε8 v hc hDc hDLip
    (upslack_raw_nonprincipal_mean_square h4 h9 hε hε8)

end LeanLab.BHP1997.DecompC165d
