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

/-- With `q >= 1` the characters of `ZMod q` number at most `q`: they are the multiplicative
characters of the finite group `(ZMod q)^*`, of which there are `q.totient`. PROVED. -/
private theorem upslack_char_card_le (q : ℕ) [NeZero q] :
    (Finset.univ : Finset (DirichletCharacter ℂ q)).card ≤ q := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  exact Nat.totient_le q

/-- P0069 page 43, Lemma 29 and its range `z <= 6 q Q / Y`: on a window `s` inside the short
interval, with `D` at least `c` and Lipschitz with constant `K / Y`, the coefficient `v / D` may be
frozen at the smallest element `m0` of the window, at the cost of `|v| K / c^2` times the width
`3 Y z` of the window, taken against the mass `M (3 Y z + 2)` of the window. PROVED. -/
private theorem upslack_window_freeze
    {s : Finset ℕ} {D : ℕ → ℝ} {w : ℕ → ℝ} {ψ : ℕ → ℂ} {c K Y z v M : ℝ}
    (hc : 0 < c) (hDc : ∀ m ∈ s, c ≤ D m) (hDpos : ∀ m ∈ s, 0 < D m)
    (hLip : ∀ m ∈ s, ∀ m' ∈ s, |D m - D m'| ≤ K * |(m : ℝ) - (m' : ℝ)| / Y)
    (hY0 : 0 < Y) (hK0 : 0 ≤ K) (hz0 : 0 ≤ z)
    (hspan : ∀ m ∈ s, ∀ m' ∈ s, |(m : ℝ) - (m' : ℝ)| ≤ 3 * Y * z)
    (hcard : (s.card : ℝ) ≤ 3 * Y * z + 2)
    (hψ : ∀ m, ‖ψ m‖ ≤ 1) (hM0 : 0 ≤ M) (hw : ∀ m ∈ s, |w m| ≤ M) :
    ‖∑ m ∈ s, (((v / D m) * w m : ℝ) : ℂ) * ψ m‖ ≤
      (|v| / c) * ‖∑ m ∈ s, ((w m : ℝ) : ℂ) * ψ m‖ +
        (|v| * K / c ^ 2) * (3 * z) * (M * (3 * Y * z + 2)) := by
  have hR0 : 0 ≤ (|v| * K / c ^ 2) * (3 * z) * (M * (3 * Y * z + 2)) := by positivity
  rcases s.eq_empty_or_nonempty with h | hne
  · subst h
    simp only [Finset.sum_empty, norm_zero, mul_zero, zero_add]
    exact hR0
  · set m₀ := s.min' hne with hm₀def
    have hm₀ : m₀ ∈ s := Finset.min'_mem s hne
    have hDm0 : 0 < D m₀ := hDpos m₀ hm₀
    -- the width of the window bounds the change of `D`
    have hDev : ∀ m ∈ s, |D m - D m₀| ≤ K * (3 * z) := by
      intro m hm
      refine (hLip m hm m₀ hm₀).trans ?_
      have hsp := hspan m hm m₀ hm₀
      rw [div_le_iff₀ hY0]
      calc K * |(m : ℝ) - (m₀ : ℝ)| ≤ K * (3 * Y * z) :=
            mul_le_mul_of_nonneg_left hsp hK0
        _ = K * (3 * z) * Y := by ring
    -- the per-term deviation of the frozen coefficient
    have hTerm : ∀ m ∈ s, |v / D m - v / D m₀| ≤ (|v| * K / c ^ 2) * (3 * z) := by
      intro m hm
      have hDm : 0 < D m := hDpos m hm
      have hcc : 0 < c * c := by positivity
      have hden : 0 < D m * D m₀ := by positivity
      have hcc_le : c * c ≤ D m * D m₀ := by
        have h1 := hDc m hm
        have h2 := hDc m₀ hm₀
        nlinarith
      have hdiv : v / D m - v / D m₀ = v * (D m₀ - D m) / (D m * D m₀) := by
        field_simp
      have hval : |v / D m - v / D m₀| = |v| * |D m - D m₀| / (D m * D m₀) := by
        rw [hdiv, abs_div, abs_of_pos hden, abs_mul, abs_sub_comm (D m₀) (D m)]
      have hrhs : (|v| * K / c ^ 2) * (3 * z) = |v| * (K * (3 * z)) / (c * c) := by
        field_simp
      rw [hval, hrhs, div_le_div_iff₀ hden hcc]
      have h1 : |v| * |D m - D m₀| ≤ |v| * (K * (3 * z)) :=
        mul_le_mul_of_nonneg_left (hDev m hm) (abs_nonneg v)
      have h2 : |v| * |D m - D m₀| * (c * c) ≤ |v| * (K * (3 * z)) * (c * c) :=
        mul_le_mul_of_nonneg_right h1 hcc.le
      have h3 : |v| * (K * (3 * z)) * (c * c) ≤ |v| * (K * (3 * z)) * (D m * D m₀) :=
        mul_le_mul_of_nonneg_left hcc_le (by positivity)
      exact h2.trans h3
    -- split the window sum at the frozen coefficient
    have hsplit : ∑ m ∈ s, (((v / D m) * w m : ℝ) : ℂ) * ψ m =
        ((v / D m₀ : ℝ) : ℂ) * (∑ m ∈ s, ((w m : ℝ) : ℂ) * ψ m) +
          ∑ m ∈ s, (((v / D m - v / D m₀) * w m : ℝ) : ℂ) * ψ m := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hDm0]
      have hle : |v| / D m₀ ≤ |v| / c := by
        rw [div_le_div_iff₀ hDm0 hc]
        nlinarith [abs_nonneg v, hDc m₀ hm₀]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    · have hb0 : 0 ≤ (|v| * K / c ^ 2) * (3 * z) := by positivity
      have hstep : ∀ m ∈ s, ‖(((v / D m - v / D m₀) * w m : ℝ) : ℂ) * ψ m‖ ≤
          (|v| * K / c ^ 2) * (3 * z) * M := by
        intro m hm
        calc ‖(((v / D m - v / D m₀) * w m : ℝ) : ℂ) * ψ m‖
            = ‖(((v / D m - v / D m₀) * w m : ℝ) : ℂ)‖ * ‖ψ m‖ := norm_mul _ _
          _ = |(v / D m - v / D m₀) * w m| * ‖ψ m‖ := by
              rw [Complex.norm_real, Real.norm_eq_abs]
          _ = |v / D m - v / D m₀| * |w m| * ‖ψ m‖ := by rw [abs_mul]
          _ ≤ ((|v| * K / c ^ 2) * (3 * z)) * M * 1 := by
              refine mul_le_mul (mul_le_mul (hTerm m hm) (hw m hm) (abs_nonneg _) hb0)
                (hψ m) (norm_nonneg _) (by positivity)
          _ = (|v| * K / c ^ 2) * (3 * z) * M := by ring
      refine (norm_sum_le _ _).trans ?_
      calc ∑ m ∈ s, ‖(((v / D m - v / D m₀) * w m : ℝ) : ℂ) * ψ m‖
          ≤ ∑ _m ∈ s, (|v| * K / c ^ 2) * (3 * z) * M := Finset.sum_le_sum hstep
        _ = (s.card : ℝ) * ((|v| * K / c ^ 2) * (3 * z) * M) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (3 * Y * z + 2) * ((|v| * K / c ^ 2) * (3 * z) * M) := by
            refine mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (|v| * K / c ^ 2) * (3 * z) * (M * (3 * Y * z + 2)) := by ring

/-- P0069 page 3 with page 53, PROVED: a power of `log x` is eventually below the power `27/16` of
`Y = x^(11/20+eps)` that the transfer's error term leaves. A Mathlib lookup on
`log x ^ A = o(x ^ b)` for `b > 0`. -/
private theorem upslack_log_pow_lt_rpow {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Real.log x ^ A ≤ 1 / 2 * (x ^ (11 / 20 + ε)) ^ (27 / 16 : ℝ) := by
  have hb : 0 < (11 / 20 + ε) * (27 / 16) := by nlinarith
  have h := (isLittleO_log_rpow_rpow_atTop A hb).bound (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Filter.eventually_atTop] at h
  obtain ⟨X, hX⟩ := h
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
  have h1 := hX x (le_trans (le_max_left _ _) hx)
  rw [← Real.rpow_mul (by linarith)]
  have h2 : ‖Real.log x ^ A‖ = Real.log x ^ A := by
    rw [Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) A)]
  have h3 : ‖x ^ ((11 / 20 + ε) * (27 / 16))‖ = x ^ ((11 / 20 + ε) * (27 / 16)) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  rw [h2, h3] at h1
  exact h1

/-- P0069 page 3: `Q = floor(H^{1/2}/2)` with `H = Y^(2(1/16 - 10^-5))` is at most `Y^(1/16)`
for `Y = x^(11/20+eps)`. PROVED. -/
private theorem sieveQ_le_rpow {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hX0 : 0 ≤ (x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5)) := by positivity
  have h1 : (sieveQ ε x : ℝ) ≤
      ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 := by
    rw [sieveQ]
    exact Nat.floor_le (by positivity)
  have h2 : ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 ≤
      ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) := by
    have h3 : (0 : ℝ) ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) :=
      by positivity
    linarith
  have hXc : 0 ≤ x ^ (11 / 20 + ε) := by positivity
  have h3 : ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) =
      x ^ ((11 / 20 + ε) * ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5)) * (1 / 2)) := by
    rw [← Real.rpow_mul hXc, ← Real.rpow_mul hx0]
    congr 1
    ring
  have h4 : x ^ ((11 / 20 + ε) * ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5)) * (1 / 2)) ≤
      (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_mul hx0]
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    nlinarith [hε]
  linarith [h1, h2, h3.symm ▸ h4]
set_option maxHeartbeats 1600000 in
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
  obtain ⟨E, hE⟩ := hraw
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C, hC⟩ := hE A hA
  obtain ⟨X, hX⟩ := upslack_log_pow_lt_rpow hε A
  set M : ℝ := 1 + 18 + 18 ^ 2 + 18 ^ 3 with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; norm_num
  set aK : ℝ := |v| * |K| / c ^ 2 with haKdef
  have haK0 : 0 ≤ aK := by rw [haKdef]; positivity
  set Cbig : ℝ := 2 * (|v| / c) ^ 2 * C + 648000 * aK ^ 2 * M ^ 2 + 1 with hCbigdef
  refine ⟨max (max 4 X) (max C Cbig), fun x hx q hq hqQ => ?_⟩
  have hx4 : 4 ≤ x := ((le_max_left 4 X).trans (le_max_left _ _)).trans hx
  have hxX : X ≤ x := ((le_max_right 4 X).trans (le_max_left _ _)).trans hx
  have hxC : C ≤ x := ((le_max_left C Cbig).trans (le_max_right _ _)).trans hx
  have hCoutC : C ≤ max (max 4 X) (max C Cbig) :=
    (le_max_left C Cbig).trans (le_max_right _ _)
  have hCoutbig : Cbig ≤ max (max 4 X) (max C Cbig) :=
    (le_max_right C Cbig).trans (le_max_right _ _)
  obtain ⟨hEcard, hEz⟩ := hC x hxC q hq hqQ
  refine ⟨?_, fun z hz1 hz2 => ?_⟩
  · have hX : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)
        (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
    have h1 := mul_le_mul_of_nonneg_right hCoutC hX
    have e1 : C * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A))
        = C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by ring
    have e2 : (max (max 4 X) (max C Cbig)) * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A))
        = (max (max 4 X) (max C Cbig)) * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by ring
    linarith [hEcard, h1, e1, e2]
  · set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
    set L : ℝ := Real.log x with hLdef
    set Q : ℕ := sieveQ ε x with hQdef
    have hzw := hEz z hz1 hz2
    set S : Finset (DirichletCharacter ℂ q) :=
      ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1 with hSdef
    set W : ℝ → Finset ℕ := fun y : ℝ =>
      (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) with hW
    -- basic facts
    have hY2 : 2 ≤ Y := by rw [hYdef]; exact upper_Y_ge_two hε hx4
    have hY0 : 0 < Y := by linarith
    have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
    have hQcast : (1 : ℝ) ≤ (Q : ℝ) := by
      have h1 : 1 ≤ Q := le_trans hq hqQ
      exact_mod_cast h1
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hpq1 : (1 : ℝ) ≤ (q : ℝ) * (Q : ℝ) := by nlinarith [hq1, hQcast]
    have hpq0 : (0 : ℝ) < (q : ℝ) * (Q : ℝ) := by linarith
    have hzz0 : 0 ≤ z := by
      have h1 : (0 : ℝ) ≤ (q : ℝ) * (Q : ℝ) / (6 * Y) := by
        have h7 : (0 : ℝ) < 6 * Y := by linarith
        positivity
      exact le_trans h1 hz1
    -- the coefficient on the window
    have hcoef : ∀ m ∈ rightInterval ε x,
        upperNormCoeff ε (fun x m => v / D x m) x m
          = (v / D x m) * upperRawWeight ε Y m := by
      intro m hm
      rw [upperNormCoeff, if_pos ⟨by rw [← hYdef]; exact hY2, hm⟩]
    -- the weight is bounded on the short interval
    have hwle : ∀ m ∈ rightInterval ε x, |upperRawWeight ε Y m| ≤ M := by
      intro m hm
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hm
      have hYx : 2 ≤ x ^ (11 / 20 + ε) := by rw [← hYdef]; exact hY2
      have hm0 : m ≠ 0 := by omega
      have hmY : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
        have h1 : (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hhi
        exact h1.trans (Nat.floor_le (by positivity))
      have h := upper_raw_abs_le hε8 hYx hm0 hmY
      rw [← hYdef] at h
      rwa [hMdef]
    -- the window is inside the short interval, with width at most `3 Y z` and few points
    have hWsub : ∀ y : ℝ, W y ⊆ rightInterval ε x := fun y m hm =>
      (Finset.mem_filter.mp hm).1
    have hyspan : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ∀ m ∈ W y, ∀ m' ∈ W y,
        |(m : ℝ) - (m' : ℝ)| ≤ 3 * Y * z := by
      intro y hy m hm m' hm'
      have hy3 : y ≤ 3 * Y := hy.2
      have h1 := (Finset.mem_filter.mp hm).2
      have h2 := (Finset.mem_filter.mp hm').2
      have hspan : |(m : ℝ) - (m' : ℝ)| ≤ y * z := by
        rw [abs_le]
        constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
      calc |(m : ℝ) - (m' : ℝ)| ≤ y * z := hspan
        _ ≤ 3 * Y * z := mul_le_mul_of_nonneg_right hy3 hzz0
    have hycard : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ((W y).card : ℝ) ≤ 3 * Y * z + 2 := by
      intro y hy
      have hy0 : 0 ≤ y := by linarith [hy.1, hY0]
      have hy3 : y ≤ 3 * Y := hy.2
      have hyz : 0 ≤ y * z := mul_nonneg hy0 hzz0
      have hsub : W y ⊆ Finset.Icc ⌊y⌋₊ ⌊y + y * z⌋₊ := by
        intro m hm
        have h1 := (Finset.mem_filter.mp hm).2
        rw [Finset.mem_Icc]
        refine ⟨?_, Nat.le_floor (by exact_mod_cast h1.2)⟩
        have h2 : ⌊y⌋₊ ≤ ⌊((m : ℕ) : ℝ)⌋₊ := Nat.floor_mono h1.1
        rwa [Nat.floor_natCast] at h2
      have hc1 : (W y).card ≤ ⌊y + y * z⌋₊ + 1 - ⌊y⌋₊ := by
        calc (W y).card ≤ (Finset.Icc ⌊y⌋₊ ⌊y + y * z⌋₊).card := Finset.card_le_card hsub
          _ = ⌊y + y * z⌋₊ + 1 - ⌊y⌋₊ := Nat.card_Icc _ _
      have hmn : ⌊y⌋₊ ≤ ⌊y + y * z⌋₊ + 1 := by
        have h1 : ⌊y⌋₊ ≤ ⌊y + y * z⌋₊ := Nat.floor_mono (by linarith)
        omega
      have hcast : ((⌊y + y * z⌋₊ + 1 - ⌊y⌋₊ : ℕ) : ℝ)
          = (⌊y + y * z⌋₊ : ℝ) + 1 - (⌊y⌋₊ : ℝ) := by
        rw [Nat.cast_sub hmn]
        push_cast
        ring
      have hf2 : (⌊y + y * z⌋₊ : ℝ) ≤ y + y * z := Nat.floor_le (by linarith)
      have hf1 : y - 1 < (⌊y⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one y
        linarith
      calc ((W y).card : ℝ) ≤ ((⌊y + y * z⌋₊ + 1 - ⌊y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hc1
        _ = (⌊y + y * z⌋₊ : ℝ) + 1 - (⌊y⌋₊ : ℝ) := hcast
        _ ≤ y * z + 2 := by linarith
        _ ≤ 3 * Y * z + 2 := by linarith [mul_le_mul_of_nonneg_right hy3 hzz0]
    -- the error term of the freeze
    set Eerr : ℝ := aK * (3 * z) * (M * (3 * Y * z + 2)) with hEerrdef
    have hEerr0 : 0 ≤ Eerr := by rw [hEerrdef]; positivity
    -- the pointwise bound on the window
    have hpsi : ∀ χ : DirichletCharacter ℂ q, ∀ m : ℕ, ‖χ (m : ZMod q)‖ ≤ 1 := fun χ m =>
      DirichletCharacter.norm_le_one χ _
    have hpt : ∀ χ : DirichletCharacter ℂ q, ∀ y ∈ Set.Icc (Y / 2) (3 * Y),
        ‖∑ m ∈ W y, (((v / D x m) * upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
          2 * (|v| / c) ^ 2 *
              ‖∑ m ∈ W y, ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 +
            2 * Eerr ^ 2 := by
      intro χ y hy
      have hb := upslack_window_freeze (s := W y) (D := D x) (w := fun m => upperRawWeight ε Y m)
        (ψ := fun m => χ (m : ZMod q)) (v := v) (c := c) (K := |K|) (Y := Y) (z := z) (M := M)
        hc (fun m _ => hDc x m)
        (fun m _ => lt_of_lt_of_le hc (hDc x m))
        (fun m hm m' hm' => by
          refine (hDLip x m (hWsub y hm) m' (hWsub y hm')).trans ?_
          have h3 : K * |(m : ℝ) - (m' : ℝ)| ≤ |K| * |(m : ℝ) - (m' : ℝ)| :=
            mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
          rw [div_le_div_iff₀ hY0 hY0]
          nlinarith [h3])
        hY0 (abs_nonneg K) hzz0 (hyspan y hy) (hycard y hy) (hpsi χ) hM0
        (fun m hm => hwle m (hWsub y hm))
      rw [hEerrdef]
      have hn1 : (0 : ℝ) ≤ |v| / c := by positivity
      have hn2 : (0 : ℝ) ≤ aK * (3 * z) * (M * (3 * Y * z + 2)) := by positivity
      set T := ‖∑ m ∈ W y, (((v / D x m) * upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖
      set Ssum := ‖∑ m ∈ W y, ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖
      have hT0 : 0 ≤ T := norm_nonneg _
      have hS0 : 0 ≤ Ssum := norm_nonneg _
      have hle : T ≤ |v| / c * Ssum + aK * (3 * z) * (M * (3 * Y * z + 2)) := hb
      nlinarith [sq_nonneg (|v| / c * Ssum - aK * (3 * z) * (M * (3 * Y * z + 2))),
        sq_nonneg (T - (|v| / c * Ssum + aK * (3 * z) * (M * (3 * Y * z + 2))))]
    -- integrability of both window sums
    have iT : ∀ χ : DirichletCharacter ℂ q,
        IntervalIntegrable (fun y : ℝ => ‖∑ m ∈ W y,
          (((v / D x m) * upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
          volume (Y / 2) (3 * Y) := fun χ =>
      upslack_window_integrable (rightInterval ε x)
        (fun m => (((v / D x m) * upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)) z (Y/2) (3*Y)
    have iS : ∀ χ : DirichletCharacter ℂ q,
        IntervalIntegrable (fun y : ℝ => ‖∑ m ∈ W y,
          ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
          volume (Y / 2) (3 * Y) := fun χ =>
      upslack_window_integrable (rightInterval ε x)
        (fun m => ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)) z (Y/2) (3*Y)
    have hab : Y / 2 ≤ 3 * Y := by linarith
    -- the per-character bound
    have hperChi : ∀ χ : DirichletCharacter ℂ q,
        ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
            (((v / D x m) * upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2
          ≤ 2 * (|v| / c) ^ 2 * (∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) +
            2 * Eerr ^ 2 * (3 * Y - Y / 2) := by
      intro χ
      have hmono : ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
            (((v / D x m) * upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2
          ≤ ∫ y in (Y / 2)..(3 * Y), (2 * (|v| / c) ^ 2 * ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 + 2 * Eerr ^ 2) :=
        intervalIntegral.integral_mono_on hab (iT χ)
          (((iS χ).const_mul (2 * (|v| / c) ^ 2)).add intervalIntegrable_const)
          (fun y hy => hpt χ y hy)
      have heval : ∫ y in (Y / 2)..(3 * Y),
          (2 * (|v| / c) ^ 2 * ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 + 2 * Eerr ^ 2)
          = 2 * (|v| / c) ^ 2 * (∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) +
            2 * Eerr ^ 2 * (3 * Y - Y / 2) := by
        rw [intervalIntegral.integral_add ((iS χ).const_mul _) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [heval] at hmono
      exact hmono
    -- rewrite the goal's integrand
    have hcongr : ∀ χ ∈ S, ∀ y : ℝ,
        (∑ m ∈ W y, ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log Y))
          = ∑ m ∈ W y, ((((v / D x m) * upperRawWeight ε Y m : ℝ)) : ℂ) * χ (m : ZMod q) := by
      intro χ hχ y
      have hdel : Thm2.delta χ = 0 := by
        have h1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
        simp [Thm2.delta, h1]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hcoef m (Finset.mem_filter.mp hm).1, hdel]
      simp
    have hgoalEq : ∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y),
          ‖∑ m ∈ W y, ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log Y)‖ ^ 2
        = ∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
            ((((v / D x m) * upperRawWeight ε Y m : ℝ)) : ℂ) * χ (m : ZMod q)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun χ hχ => ?_
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [hcongr χ hχ y]
    rw [hgoalEq]
    -- the character count and the error algebra
    have hSq : (S.card : ℝ) ≤ (q : ℝ) := by
      haveI : NeZero q := ⟨by omega⟩
      have h1 : S.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
        Finset.card_le_univ S
      have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card ≤ q :=
        upslack_char_card_le q
      exact_mod_cast le_trans h1 h2
    have hEbound : Eerr ≤ 360 * aK * M * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y := by
      rw [hEerrdef, haKdef]
      have h1 : 3 * z ≤ 18 * ((q : ℝ) * (Q : ℝ)) / Y := by
        have h2 : 3 * z ≤ 3 * (6 * (q : ℝ) * (Q : ℝ) / Y) :=
          mul_le_mul_of_nonneg_left hz2 (by norm_num)
        calc 3 * z ≤ 3 * (6 * (q : ℝ) * (Q : ℝ) / Y) := h2
          _ = 18 * ((q : ℝ) * (Q : ℝ)) / Y := by ring
      have h2 : 3 * Y * z + 2 ≤ 20 * ((q : ℝ) * (Q : ℝ)) := by
        have h3 : 3 * Y * z ≤ 18 * ((q : ℝ) * (Q : ℝ)) := by
          have h4 : Y * (3 * z) ≤ Y * (18 * ((q : ℝ) * (Q : ℝ)) / Y) :=
            mul_le_mul_of_nonneg_left h1 hY0.le
          have h5 : Y * (18 * ((q : ℝ) * (Q : ℝ)) / Y) = 18 * ((q : ℝ) * (Q : ℝ)) := by
            field_simp
          nlinarith [h4, h5]
        nlinarith [h3, hpq1]
      have hA0 : 0 ≤ |v| * |K| / c ^ 2 := by positivity
      have hA1 : 0 ≤ 3 * z := by linarith
      have hA2 : 0 ≤ M := hM0
      have hA3 : 0 ≤ 3 * Y * z + 2 := by linarith [mul_nonneg hY0.le hzz0]
      have h4 : M * (3 * Y * z + 2) ≤ M * (20 * ((q : ℝ) * (Q : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hM0
      have h5 : (|v| * |K| / c ^ 2) * (3 * z) ≤
          (|v| * |K| / c ^ 2) * (18 * ((q : ℝ) * (Q : ℝ)) / Y) :=
        mul_le_mul_of_nonneg_left h1 hA0
      calc (|v| * |K| / c ^ 2) * (3 * z) * (M * (3 * Y * z + 2))
          ≤ (|v| * |K| / c ^ 2) * (18 * ((q : ℝ) * (Q : ℝ)) / Y) *
              (M * (20 * ((q : ℝ) * (Q : ℝ)))) := by
            refine mul_le_mul h5 h4 ?_ ?_
            · exact mul_nonneg hM0 (by linarith [mul_nonneg hY0.le hzz0])
            · positivity
        _ = 360 * (|v| * |K| / c ^ 2) * M * (((q : ℝ) * (Q : ℝ)) ^ 2 / Y) := by
            field_simp
            ring
        _ = 360 * (|v| * |K| / c ^ 2) * M * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y := by
            field_simp
    -- the polynomial gain over `Y`
    have hkey : (q : ℝ) * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y ^ 2 ≤ Y ^ (-(27 / 16) : ℝ) := by
      have hQle : (Q : ℝ) ≤ Y ^ (1 / 16 : ℝ) := by
        have h := sieveQ_le_rpow hε (by linarith : (1 : ℝ) ≤ x)
        rw [← hQdef, ← hYdef] at h
        exact h
      have hqQle : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
      have hq3 : (q : ℝ) ^ 3 ≤ (Q : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hqQle 3
      have hQ5 : (Q : ℝ) ^ 5 ≤ Y ^ (5 / 16 : ℝ) := by
        have h1 : (Q : ℝ) ^ 5 ≤ (Y ^ (1 / 16 : ℝ)) ^ 5 := pow_le_pow_left₀ (by positivity) hQle 5
        have h2 : (Y ^ (1 / 16 : ℝ)) ^ 5 = Y ^ (5 / 16 : ℝ) := by
          rw [← Real.rpow_natCast (Y ^ (1 / 16 : ℝ)) 5, ← Real.rpow_mul hY0.le]
          norm_num
        linarith [h1, h2]
      have hq5 : (q : ℝ) ^ 3 * (Q : ℝ) ^ 2 ≤ Y ^ (5 / 16 : ℝ) := by
        have h1 : (q : ℝ) ^ 3 * (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 3 * (Q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hq3 (by positivity)
        have h2 : (Q : ℝ) ^ 3 * (Q : ℝ) ^ 2 = (Q : ℝ) ^ 5 := by ring
        linarith [h1, h2, hQ5]
      have hY1 : 1 ≤ Y := by linarith
      have h56 : Y ^ (5 / 16 : ℝ) = Y ^ (-(27 / 16) : ℝ) * Y ^ 2 := by
        have h1 : Y ^ (5 / 16 : ℝ) = Y ^ (-(27 / 16) : ℝ) * Y ^ (2 : ℕ) := by
          rw [← Real.rpow_natCast (x := Y) 2, ← Real.rpow_add hY0]
          norm_num
        rw [h1]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Y ^ 2)]
      calc (q : ℝ) * ((q : ℝ) * (Q : ℝ)) ^ 2
          = (q : ℝ) ^ 3 * (Q : ℝ) ^ 2 := by ring
        _ ≤ Y ^ (5 / 16 : ℝ) := hq5
        _ = Y ^ (-(27 / 16) : ℝ) * Y ^ 2 := h56
    -- the comparison of the log power with `Y ^ (27/16)`
    have hcmp : Y ^ (-(27 / 16) : ℝ) ≤ 1 / 2 * L ^ (-A) := by
      have h1 : L ^ A ≤ 1 / 2 * Y ^ (27 / 16 : ℝ) := hX x hxX
      have hLY : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
      have hYp : 0 < Y ^ (27 / 16 : ℝ) := Real.rpow_pos_of_pos hY0 _
      rw [Real.rpow_neg hY0.le, Real.rpow_neg hL0.le]
      have h4 : (0 : ℝ) < 2 * L ^ A := by linarith
      have h5 : (1 / 2 * (L ^ A)⁻¹) = (2 * L ^ A)⁻¹ := by field_simp
      rw [h5, inv_le_inv₀ hYp h4]
      linarith
    -- assemble
    have hmain : ∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
            ((((v / D x m) * upperRawWeight ε Y m : ℝ)) : ℂ) * χ (m : ZMod q)‖ ^ 2
        ≤ Cbig * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) := by
      have h1 : ∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((((v / D x m) * upperRawWeight ε Y m : ℝ)) : ℂ) * χ (m : ZMod q)‖ ^ 2
          ≤ ∑ χ ∈ S, (2 * (|v| / c) ^ 2 * (∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) +
            2 * Eerr ^ 2 * (3 * Y - Y / 2)) :=
        Finset.sum_le_sum fun χ _ => hperChi χ
      have h2 : ∑ χ ∈ S, (2 * (|v| / c) ^ 2 * (∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) +
            2 * Eerr ^ 2 * (3 * Y - Y / 2))
          = 2 * (|v| / c) ^ 2 * (∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) +
            (S.card : ℝ) * (2 * Eerr ^ 2 * (3 * Y - Y / 2)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      have hB : 0 ≤ ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A) := by positivity
      have h3 : 2 * (|v| / c) ^ 2 * (∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
          ≤ 2 * (|v| / c) ^ 2 * (C * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine le_trans hzw (le_of_eq ?_)
        ring
      have h4 : (S.card : ℝ) * (2 * Eerr ^ 2 * (3 * Y - Y / 2))
          ≤ 648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) := by
        have h5 : (S.card : ℝ) * (2 * Eerr ^ 2 * (3 * Y - Y / 2))
            ≤ (q : ℝ) * (2 * (360 * aK * M * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y) ^ 2 *
                (3 * Y - Y / 2)) := by
          have hE2 : 2 * Eerr ^ 2 ≤
              2 * (360 * aK * M * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact pow_le_pow_left₀ hEerr0 hEbound 2
          have hd : (0 : ℝ) ≤ 3 * Y - Y / 2 := by linarith
          have hstep : (S.card : ℝ) * (2 * Eerr ^ 2 * (3 * Y - Y / 2))
              ≤ (S.card : ℝ) * (2 * (360 * aK * M * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y) ^ 2 *
                  (3 * Y - Y / 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE2 hd) (by positivity)
          refine hstep.trans (mul_le_mul_of_nonneg_right hSq ?_)
          exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hd
        have h5' : (q : ℝ) * (2 * (360 * aK * M * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y) ^ 2 *
              (3 * Y - Y / 2))
            = 648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 4 * (q : ℝ)) * Y / Y ^ 2 := by
          field_simp
          ring
        rw [h5'] at h5
        have h6 : 648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 4 * (q : ℝ)) * Y / Y ^ 2
            ≤ 648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) := by
          have h7 : ((q : ℝ) * (Q : ℝ)) ^ 4 * (q : ℝ) * Y / Y ^ 2
              ≤ ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A) := by
            have h9 : ((q : ℝ) * (Q : ℝ)) ^ 4 * (q : ℝ) * Y / Y ^ 2
                = ((q : ℝ) * (Q : ℝ)) ^ 2 * Y *
                  ((q : ℝ) * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y ^ 2) := by
              field_simp
            rw [h9]
            have h10 : 0 ≤ ((q : ℝ) * (Q : ℝ)) ^ 2 * Y := by positivity
            have h11 : (0 : ℝ) < L ^ (-A) := Real.rpow_pos_of_pos hL0 _
            calc ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * ((q : ℝ) * ((q : ℝ) * (Q : ℝ)) ^ 2 / Y ^ 2)
                ≤ ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * Y ^ (-(27 / 16) : ℝ) :=
                  mul_le_mul_of_nonneg_left hkey h10
              _ ≤ ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * (1 / 2 * L ^ (-A)) :=
                  mul_le_mul_of_nonneg_left hcmp h10
              _ ≤ ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A) := by
                  refine mul_le_mul_of_nonneg_left ?_ h10
                  linarith
          calc 648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 4 * (q : ℝ)) * Y / Y ^ 2
              = 648000 * aK ^ 2 * M ^ 2 *
                (((q : ℝ) * (Q : ℝ)) ^ 4 * (q : ℝ) * Y / Y ^ 2) := by ring
            _ ≤ 648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) :=
                mul_le_mul_of_nonneg_left h7 (by positivity)
        exact h5.trans h6
      calc ∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((((v / D x m) * upperRawWeight ε Y m : ℝ)) : ℂ) * χ (m : ZMod q)‖ ^ 2
          ≤ 2 * (|v| / c) ^ 2 * (∑ χ ∈ S, ∫ y in (Y / 2)..(3 * Y), ‖∑ m ∈ W y,
              ((upperRawWeight ε Y m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) +
            (S.card : ℝ) * (2 * Eerr ^ 2 * (3 * Y - Y / 2)) := h1.trans_eq h2
        _ ≤ 2 * (|v| / c) ^ 2 * (C * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A))) +
              648000 * aK ^ 2 * M ^ 2 * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) :=
            add_le_add h3 h4
        _ ≤ Cbig * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) := by
            rw [hCbigdef]
            nlinarith [hB]
    refine hmain.trans ?_
    calc Cbig * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A))
        ≤ (max (max 4 X) (max C Cbig)) * (((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A)) :=
          mul_le_mul_of_nonneg_right hCoutbig (by positivity)
      _ = (max (max 4 X) (max C Cbig)) * ((q : ℝ) * (Q : ℝ)) ^ 2 * Y * L ^ (-A) := by ring
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
