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

/-- The window lies strictly above `Y`. -/
private theorem upslack_window_gt {ε x : ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) :
    x ^ (11 / 20 + ε) < (m : ℝ) := by
  unfold rightInterval at hm
  have h1 : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hm).1
  have h2 : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
  have h3 : x ^ (11 / 20 + ε) < ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- The window lies at most `2 Y`. -/
private theorem upslack_window_le {ε x : ℝ} (hx : 0 ≤ x) {m : ℕ}
    (hm : m ∈ rightInterval ε x) : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
  unfold rightInterval at hm
  have h2 : m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := (Finset.mem_Ioc.mp hm).2
  have h3 : (m : ℝ) ≤ ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
  have h4 : ((⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
    Nat.floor_le (by have := Real.rpow_nonneg hx (11 / 20 + ε); linarith)
  linarith

/-- The window contains at most `y z + 1` integers. -/
private theorem upslack_window_card_le {S : Finset ℕ} {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ((S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ) ≤ y * z + 1 := by
  have hyz : 0 ≤ y + y * z := by nlinarith
  set W := S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) with hW
  have hsub : W ⊆ Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊ := by
    intro m hm
    simp only [hW, Finset.mem_filter] at hm
    obtain ⟨-, h1, h2⟩ := hm
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1, (Nat.le_floor_iff hyz).mpr h2⟩
  have hcard : W.card ≤ (Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊).card := Finset.card_le_card hsub
  have hc : ((Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊).card : ℝ) ≤ y * z + 1 := by
    by_cases h : ⌈y⌉₊ ≤ ⌊y + y * z⌋₊ + 1
    · rw [Nat.card_Icc]
      have hb : ((⌊y + y * z⌋₊ : ℕ) : ℝ) ≤ y + y * z := Nat.floor_le hyz
      have ha : y ≤ ((⌈y⌉₊ : ℕ) : ℝ) := Nat.le_ceil y
      have hsub' : ((⌊y + y * z⌋₊ + 1 - ⌈y⌉₊ : ℕ) : ℝ) =
          ((⌊y + y * z⌋₊ : ℕ) : ℝ) + 1 - ((⌈y⌉₊ : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub h]; ring
      rw [hsub']
      linarith
    · have hem : Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro m hm
        simp only [Finset.mem_Icc] at hm
        omega
      rw [hem]
      simp only [Finset.card_empty, Nat.cast_zero]
      nlinarith
  have hcard' : (W.card : ℝ) ≤ ((Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊).card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The raw weight is bounded on the support. -/
private theorem upslack_raw_abs {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (hx : 4 ≤ x)
    {m : ℕ} (hm : m ∈ rightInterval ε x) :
    |upperRawWeight ε (x ^ (11 / 20 + ε)) m| ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
  have hY2 : 2 ≤ x ^ (11 / 20 + ε) := upper_Y_ge_two hε hx
  have hm0 : m ≠ 0 := by
    have := upslack_window_gt hm
    have h0 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
    intro h; rw [h] at this; simp at this; linarith
  have hmY : (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := upslack_window_le (by linarith) hm
  exact upper_raw_abs_le hε8 hY2 hm0 hmY

/-- The local inverse difference of a Lipschitz denominator. -/
private lemma upslack_dev_le {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) {D : ℝ → ℕ → ℝ} {c K : ℝ}
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    {m m0 : ℕ} (hm : m ∈ rightInterval ε x) (hm0 : m0 ∈ rightInterval ε x) (v : ℝ) :
    |v / D x m - v / D x m0| ≤
      |v| * max K 0 * |(m : ℝ) - m0| / (x ^ (11 / 20 + ε) * c ^ 2) := by
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hDm : c ≤ D x m := hDc x m
  have hDm0 : c ≤ D x m0 := hDc x m0
  have hDmpos : 0 < D x m := lt_of_lt_of_le hc hDm
  have hDm0pos : 0 < D x m0 := lt_of_lt_of_le hc hDm0
  have heq : v / D x m - v / D x m0 = v * (D x m0 - D x m) / (D x m * D x m0) := by
    field_simp
  have hDl : |D x m0 - D x m| ≤ max K 0 * |(m : ℝ) - m0| / x ^ (11 / 20 + ε) := by
    have h1 := hDLip x m0 hm0 m hm
    rw [abs_sub_comm (m0 : ℝ) (m : ℝ)] at h1
    have hK : K * |(m : ℝ) - m0| ≤ max K 0 * |(m : ℝ) - m0| :=
      mul_le_mul_of_nonneg_right (le_max_left K 0) (abs_nonneg _)
    have := div_le_div_of_nonneg_right hK hY.le
    linarith
  have hc2 : 0 < c ^ 2 := by positivity
  have hden : c ^ 2 ≤ D x m * D x m0 := by nlinarith
  have habs : |D x m * D x m0| = D x m * D x m0 := abs_of_pos (by positivity)
  rw [heq, abs_div, abs_mul, habs]
  have hstep1 : |v| * |D x m0 - D x m| / (D x m * D x m0) ≤
      |v| * |D x m0 - D x m| / c ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hc2 hden
  have hstep2 : |v| * |D x m0 - D x m| / c ^ 2 ≤
      |v| * (max K 0 * |(m : ℝ) - m0| / x ^ (11 / 20 + ε)) / c ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDl (abs_nonneg _)) hc2.le
  refine le_trans hstep1 (le_trans hstep2 (le_of_eq ?_))
  simp only [show (11 : ℝ) / 20 + ε = (11 + 20 * ε) / 20 from by ring]
  ring_nf

/-- The raw bound `1 + 18 + 18^2 + 18^3` is nonnegative. -/
private lemma upslack_B0_nonneg : (0 : ℝ) ≤ (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by norm_num

/-- Page 43 Lemma 29 with the denominator frozen at the window's first integer: the window sum of
`(v / D) b1 chi` is the frozen factor times the window sum of `b1 chi`, plus an error of order
`|v| K B z^2 / c^2`. -/
private lemma upslack_pointwise_transfer
    {ε x v c K : ℝ} {D : ℝ → ℕ → ℝ} (hx : 4 ≤ x) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖
      ≤ (|v| / c) * ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖
        + |v| * max K 0 * ((1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) / (x ^ (11 / 20 + ε) * c ^ 2) *
            (y * z + 1) ^ 2 := by
  have hx1 : 1 ≤ x := by linarith
  have hY2 : 2 ≤ x ^ (11 / 20 + ε) := upper_Y_ge_two hε hx
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hB0 := upslack_B0_nonneg
  set W := (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) with hW
  -- the summand of the goal is the plain product
  have hsummand : ∀ m ∈ W,
      ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))
        = ((v / D x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) *
            χ (m : ZMod q) := by
    intro m hm
    obtain ⟨hmR, -⟩ := Finset.mem_filter.mp hm
    have hcoef : upperNormCoeff ε (fun x m => v / D x m) x m =
        v / D x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m := by
      unfold upperNormCoeff
      rw [if_pos ⟨hY2, hmR⟩]
    have hd : Thm2.delta χ = 0 := by
      unfold Thm2.delta
      rw [if_neg hχ]
    rw [hcoef, hd, zero_mul, zero_div, sub_zero]
  rw [Finset.sum_congr rfl hsummand]
  rcases W.eq_empty_or_nonempty with hem | hne
  · rw [hem]
    simp only [Finset.sum_empty, norm_zero]
    have h1 : 0 ≤ |v| / c := div_nonneg (abs_nonneg _) hc.le
    have h2 : 0 ≤ |v| * max K 0 * ((1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) /
        (x ^ (11 / 20 + ε) * c ^ 2) :=
      div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right K 0)) (upslack_B0_nonneg))
        (by positivity)
    have h3 : 0 ≤ (y * z + 1) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h1 (norm_nonneg (∑ m ∈ (∅ : Finset ℕ),
      ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)))]
  · set m0 := W.min' hne with hm0def
    have hm0 : m0 ∈ W := Finset.min'_mem W hne
    obtain ⟨hm0R, hy0, hy0'⟩ := Finset.mem_filter.mp hm0
    -- split off the frozen factor
    have hsplit : ∑ m ∈ W, ((v / D x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) *
          χ (m : ZMod q)
        = ∑ m ∈ W, (((v / D x m - v / D x m0) * upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ)
            * χ (m : ZMod q)
          + ((v / D x m0 : ℝ) : ℂ) * ∑ m ∈ W,
              ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      push_cast
      ring
    rw [hsplit]
    -- the deviation part
    have hdev : ‖∑ m ∈ W, (((v / D x m - v / D x m0) * upperRawWeight ε (x ^ (11 / 20 + ε)) m :
          ℝ) : ℂ) * χ (m : ZMod q)‖
        ≤ |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) / (x ^ (11 / 20 + ε) * c ^ 2) *
            (y * z + 1) ^ 2 := by
      have hterm : ∀ m ∈ W,
          ‖(((v / D x m - v / D x m0) * upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) *
              χ (m : ZMod q)‖
            ≤ |v| * max K 0 * |(m : ℝ) - m0| / (x ^ (11 / 20 + ε) * c ^ 2) *
                (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by
        intro m hm
        obtain ⟨hmR, -⟩ := Finset.mem_filter.mp hm
        have hdev' := upslack_dev_le (D := D) hε (by linarith : (0 : ℝ) < x) hc hDc hDLip hmR hm0R v
        have hraw := upslack_raw_abs hε hε8 hx hmR
        rw [norm_mul]
        have hχ1 : ‖χ (m : ZMod q)‖ ≤ 1 := χ.norm_le_one _
        calc ‖(((v / D x m - v / D x m0) * upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ)‖ *
              ‖χ (m : ZMod q)‖
            = |v / D x m - v / D x m0| * |upperRawWeight ε (x ^ (11 / 20 + ε)) m| *
                ‖χ (m : ZMod q)‖ := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
            _ ≤ (|v| * max K 0 * |(m : ℝ) - m0| / (x ^ (11 / 20 + ε) * c ^ 2)) *
                (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) * 1 := by
              gcongr
            _ = |v| * max K 0 * |(m : ℝ) - m0| / (x ^ (11 / 20 + ε) * c ^ 2) *
                (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) := by ring
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      have hdist : ∀ m ∈ W, |(m : ℝ) - m0| ≤ y * z := by
        intro m hm
        obtain ⟨-, hy1, hy2⟩ := Finset.mem_filter.mp hm
        rw [abs_le]
        constructor <;> linarith
      have hcardW : (W.card : ℝ) ≤ y * z + 1 := upslack_window_card_le hy hz
      have hyz0 : 0 ≤ y * z := mul_nonneg hy hz
      have hsumdist : ∑ m ∈ W, |(m : ℝ) - m0| ≤ (y * z + 1) ^ 2 := by
        refine le_trans (Finset.sum_le_sum hdist) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        nlinarith
      have hcoef0 : 0 ≤ |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
          (x ^ (11 / 20 + ε) * c ^ 2) :=
        div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right K 0)) upslack_B0_nonneg)
          (by positivity)
      have hfac : ∑ m ∈ W, |v| * max K 0 * |(m : ℝ) - m0| / (x ^ (11 / 20 + ε) * c ^ 2) *
            (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)
          = (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
              (x ^ (11 / 20 + ε) * c ^ 2)) * ∑ m ∈ W, |(m : ℝ) - m0| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hsumdist hcoef0
    -- the frozen part
    have hfroz : ‖((v / D x m0 : ℝ) : ℂ) * ∑ m ∈ W,
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖
        ≤ |v| / c * ‖∑ m ∈ W,
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div]
      have hD0 : 0 < D x m0 := lt_of_lt_of_le hc (hDc x m0)
      rw [abs_of_pos hD0]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (abs_nonneg _) hc (hDc x m0)) (norm_nonneg _)
    refine le_trans (norm_add_le _ _) ?_
    linarith [hdev, hfroz]

/-- Integrate the pointwise transfer bound over `[Y/2, 3Y]` for one non-principal character. -/
private lemma upslack_integrated_le
    {ε x v c K : ℝ} {D : ℝ → ℕ → ℝ} (hx : 4 ≤ x) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8)
    (hc : 0 < c) (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    {q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℝ}
    (hz1 : ((q : ℝ) * sieveQ ε x) / (6 * x ^ (11 / 20 + ε)) ≤ z)
    (hz2 : z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε)) :
    ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2
      ≤ 2 * (|v| / c) ^ 2 *
          (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
        + (3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
            (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
              ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4) := by
  have hx1 : 1 ≤ x := by linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := hYpos.le
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  have hQ1 : 1 ≤ sieveQ ε x := le_trans hq hqQ
  have hqQ1 : (1 : ℝ) ≤ (q : ℝ) * sieveQ ε x := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have h2 : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hQ1
    nlinarith
  have hcoef0 : 0 ≤ |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
      ((x ^ (11 / 20 + ε)) * c ^ 2) :=
    div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right K 0)) upslack_B0_nonneg)
      (by positivity)
  -- the pointwise bound, with the window length replaced by its maximum
  have hpt : ∀ y ∈ Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)),
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2
        ≤ 2 * (|v| / c) ^ 2 *
            ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2
          + 2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
                ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4 := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by linarith : (0:ℝ) ≤ x ^ (11 / 20 + ε) / 2) hy.1
    have hz0 : 0 ≤ z := by
      have : 0 ≤ ((q : ℝ) * sieveQ ε x) / (6 * x ^ (11 / 20 + ε)) := by positivity
      linarith
    have h := upslack_pointwise_transfer (D := D) (v := v) hx hε hε8 hc hDc hDLip χ hχ hy0 hz0
    -- the window is at most `19 q Q` long
    have hyz : y * z ≤ 18 * ((q : ℝ) * sieveQ ε x) := by
      have h1 : y * z ≤ (3 * x ^ (11 / 20 + ε)) * z :=
        mul_le_mul_of_nonneg_right hy.2 hz0
      have hz2' : z ≤ 6 * (q : ℝ) * sieveQ ε x / x ^ (11 / 20 + ε) := hz2
      have h2 : (3 * x ^ (11 / 20 + ε)) * z ≤
          (3 * x ^ (11 / 20 + ε)) * (6 * (q : ℝ) * sieveQ ε x / x ^ (11 / 20 + ε)) :=
        mul_le_mul_of_nonneg_left hz2' (by linarith)
      have h3 : (3 * x ^ (11 / 20 + ε)) * (6 * (q : ℝ) * sieveQ ε x / x ^ (11 / 20 + ε)) =
          18 * ((q : ℝ) * sieveQ ε x) := by
        field_simp
        ring
      linarith [h1, h2, h3]
    have hl1 : y * z + 1 ≤ 19 * ((q : ℝ) * sieveQ ε x) := by nlinarith [hqQ1]
    have hl0 : 0 ≤ y * z + 1 := by nlinarith [mul_nonneg hy0 hz0]
    have h4 : (y * z + 1) ^ 4 ≤ (19 * ((q : ℝ) * sieveQ ε x)) ^ 4 :=
      pow_le_pow_left₀ hl0 hl1 4
    have hB4 : (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
          ((x ^ (11 / 20 + ε)) * c ^ 2) * (y * z + 1) ^ 2) ^ 2 ≤
        (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
          ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4 := by
      rw [mul_pow]
      have e : ((y * z + 1) ^ 2) ^ 2 = (y * z + 1) ^ 4 := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have hbound : ‖∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
        2 * (|v| / c * ‖∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖) ^ 2
          + 2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
                ((x ^ (11 / 20 + ε)) * c ^ 2) * (y * z + 1) ^ 2) ^ 2 := by
      have h1 : ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖
          ≤ |v| / c * ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖
            + |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
                ((x ^ (11 / 20 + ε)) * c ^ 2) * (y * z + 1) ^ 2 := h
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (|v| / c * ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖
            + |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
                ((x ^ (11 / 20 + ε)) * c ^ 2) * (y * z + 1) ^ 2) ^ 2 ≤
          2 * (|v| / c * ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖) ^ 2
            + 2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
                ((x ^ (11 / 20 + ε)) * c ^ 2) * (y * z + 1) ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (|v| / c * ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖
            - |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
                ((x ^ (11 / 20 + ε)) * c ^ 2) * (y * z + 1) ^ 2)]
      linarith [h2, h3]
    nlinarith [hbound, hB4]
  -- integrability
  have hIntL : IntervalIntegrable (fun y : ℝ =>
      ‖∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2) volume
      (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
    have e : (fun y : ℝ =>
        ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2)
        = fun y : ℝ =>
          ‖∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((v / D x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 := by
      funext y
      refine congrArg (fun w : ℂ => ‖w‖ ^ 2) ?_
      refine Finset.sum_congr rfl fun m hm => ?_
      obtain ⟨hmR, -⟩ := Finset.mem_filter.mp hm
      have hY2 : 2 ≤ x ^ (11 / 20 + ε) := upper_Y_ge_two hε hx
      have hcoef : upperNormCoeff ε (fun x m => v / D x m) x m =
          v / D x m * upperRawWeight ε (x ^ (11 / 20 + ε)) m := by
        unfold upperNormCoeff
        rw [if_pos ⟨hY2, hmR⟩]
      have hd : Thm2.delta χ = 0 := by
        unfold Thm2.delta
        rw [if_neg hχ]
      rw [hcoef, hd, zero_mul, zero_div, sub_zero]
    rw [e]
    exact upslack_window_integrable _ _ z _ _
  have hIntR : IntervalIntegrable (fun y : ℝ =>
      ‖∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2) volume
      (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) :=
    upslack_window_integrable _ _ z _ _
  have hIntSum : IntervalIntegrable (fun y : ℝ =>
      2 * (|v| / c) ^ 2 *
          ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2
        + 2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
              ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4) volume
      (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) :=
    (hIntR.const_mul _).add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hIntL hIntSum hpt
  rw [intervalIntegral.integral_add (hIntR.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have test : (∫ (y : ℝ) in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
      = ∫ (x_1 : ℝ) in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => x_1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ x_1 + x_1 * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 := rfl
  have eA : (∫ (x_1 : ℝ) in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => x_1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ x_1 + x_1 * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
      = ∫ (y : ℝ) in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 := rfl
  rw [eA] at hmono
  have hex : (∫ (y : ℝ) in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            (↑(upperNormCoeff ε (fun x m => v / D x m) x m) * χ ↑m -
              Thm2.delta χ * ↑v / ↑(Real.log (x ^ (11 / 20 + ε))))‖ ^ 2)
      = ∫ (u : ℝ) in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u + u * z),
            (↑(upperNormCoeff ε (fun x m => v / D x m) x m) * χ ↑m -
              Thm2.delta χ * ↑v / ↑(Real.log (x ^ (11 / 20 + ε))))‖ ^ 2 := rfl
  exact hmono

/-- `sieveQ` is at most `Y^{1/16}`. -/
private lemma upslack_sieveQ_le {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx (by linarith)
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := le_trans zero_le_one hY1
  set Y := x ^ (11 / 20 + ε) with hYdef
  set σ : ℝ := 1 / 16 - 1 / 10 ^ 5 with hσdef
  have h1 : Y ^ σ = (Y ^ (2 * σ)) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul hY0 (2 * σ) (1 / 2)]
    rw [show (2 : ℝ) * σ * (1 / 2) = σ by ring]
  have h2 : (Y ^ (2 * σ)) ^ (1 / 2 : ℝ) ≤ Y ^ (1 / 16 : ℝ) := by
    rw [← h1]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num [hσdef])
  have harg : 0 ≤ (Y ^ (2 * σ)) ^ (1 / 2 : ℝ) / 2 :=
    div_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hY0 (2 * σ)) (1 / 2 : ℝ)) (by norm_num)
  calc (sieveQ ε x : ℝ) ≤ (Y ^ (2 * σ)) ^ (1 / 2 : ℝ) / 2 := by
        unfold sieveQ
        simp only [hYdef, hσdef]
        exact Nat.floor_le harg
    _ ≤ (Y ^ (2 * σ)) ^ (1 / 2 : ℝ) := by
        have h3 := Real.rpow_nonneg (Real.rpow_nonneg hY0 (2 * σ)) (1 / 2 : ℝ)
        linarith
    _ ≤ Y ^ (1 / 16 : ℝ) := h2
    _ = (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by rw [hYdef]

/-- A power of `log x` is absorbed by `x^{9/20}`. -/
private lemma upslack_log_pow_le {x A : ℝ} (hx : 1 ≤ x) (hA : 0 < A) :
    (Real.log x) ^ A ≤ (20 * A / 9) ^ A * x ^ (9 / 20 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hr : 0 < 9 / (20 * A) := by positivity
  have hlog : Real.log x ≤ x ^ (9 / (20 * A)) / (9 / (20 * A)) := Real.log_le_rpow_div hx0 hr
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hmono : (Real.log x) ^ A ≤ (x ^ (9 / (20 * A)) / (9 / (20 * A))) ^ A :=
    Real.rpow_le_rpow hL0 hlog hA.le
  have hxr : 0 ≤ x ^ (9 / (20 * A)) := Real.rpow_nonneg hx0 _
  have hinv0 : 0 ≤ (9 / (20 * A))⁻¹ := le_of_lt (inv_pos.mpr hr)
  have hsplit : (x ^ (9 / (20 * A)) / (9 / (20 * A))) ^ A =
      (x ^ (9 / (20 * A))) ^ A * ((9 / (20 * A))⁻¹) ^ A := by
    rw [div_eq_mul_inv, Real.mul_rpow hxr hinv0]
  rw [hsplit] at hmono
  have h1 : (x ^ (9 / (20 * A))) ^ A = x ^ (9 / 20 : ℝ) := by
    rw [← Real.rpow_mul hx0]
    congr 1
    field_simp
  have h2 : ((9 / (20 * A))⁻¹) ^ A = (20 * A / 9) ^ A := by
    have e : (9 / (20 * A))⁻¹ = 20 * A / 9 := by field_simp
    rw [e]
  rw [h1, h2] at hmono
  simpa only [mul_comm] using hmono

/-- The size of the error term against `(q Q)^2 Y L^{-A}`. -/
private lemma upslack_key {ε A x : ℝ} {q : ℕ} (hε : 0 < ε) (hx : 4 ≤ x) (hA : 0 < A)
    (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x) :
    (q : ℝ) * ((q : ℝ) * sieveQ ε x) ^ 2 * (Real.log x) ^ A / (x ^ (11 / 20 + ε)) ^ 2
      ≤ (20 * A / 9) ^ A := by
  have hx1 : 1 ≤ x := by linarith
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hQ1 : 1 ≤ sieveQ ε x := le_trans hq hqQ
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQ1' : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hQ1
  have hqQ' : (q : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hqQ
  -- step 1: `q (qQ)^2 <= Q^5`
  have h1 : (q : ℝ) * ((q : ℝ) * sieveQ ε x) ^ 2 ≤ (sieveQ ε x : ℝ) ^ 5 := by
    have hQ0 : (0 : ℝ) ≤ (sieveQ ε x : ℝ) := by positivity
    have hq3 : (q : ℝ) ^ 3 ≤ (sieveQ ε x : ℝ) ^ 3 :=
      pow_le_pow_left₀ (le_trans zero_le_one hq1) hqQ' 3
    have e1 : (q : ℝ) * ((q : ℝ) * sieveQ ε x) ^ 2 = (q : ℝ) ^ 3 * (sieveQ ε x : ℝ) ^ 2 := by
      ring
    have e2 : (sieveQ ε x : ℝ) ^ 5 = (sieveQ ε x : ℝ) ^ 3 * (sieveQ ε x : ℝ) ^ 2 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hq3 (by positivity)
  -- step 2: `Q^5 <= Y^{5/16}`
  have hsq : (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) :=
    upslack_sieveQ_le hε hx1
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
  have h2 : (sieveQ ε x : ℝ) ^ 5 ≤ (x ^ (11 / 20 + ε)) ^ (5 / 16 : ℝ) := by
    calc (sieveQ ε x : ℝ) ^ 5 ≤ ((x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ)) ^ 5 := by
          exact pow_le_pow_left₀ (by positivity) hsq 5
      _ = (x ^ (11 / 20 + ε)) ^ (5 / 16 : ℝ) := by
          rw [← Real.rpow_natCast ((x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ)) 5,
            ← Real.rpow_mul (le_of_lt hYpos)]
          norm_num
  -- step 3: the `Y` powers cancel down to `x^{-9/10}`
  have hY3 : (x ^ (11 / 20 + ε)) ^ (5 / 16 : ℝ) / (x ^ (11 / 20 + ε)) ^ 2 ≤
      x ^ (-(9 / 10) : ℝ) := by
    have hY2pos : 0 < (x ^ (11 / 20 + ε)) ^ 2 := by positivity
    rw [div_le_iff₀ hY2pos]
    have e1 : (x ^ (11 / 20 + ε)) ^ 2 = x ^ ((11 / 20 + ε) * 2) := by
      rw [← Real.rpow_natCast (x ^ (11 / 20 + ε)) 2,
        ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ x)]
      try norm_num
    have e2 : x ^ (-(9 / 10) : ℝ) * x ^ ((11 / 20 + ε) * 2) =
        x ^ (-(9 / 10) + (11 / 20 + ε) * 2) := by
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < x)]
    have e3 : (x ^ (11 / 20 + ε)) ^ (5 / 16 : ℝ) = x ^ ((11 / 20 + ε) * (5 / 16)) := by
      rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ x)]
    rw [e1, e2, e3]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    nlinarith [hε]
  -- step 4: the logarithm
  have h4 := upslack_log_pow_le hx1 hA
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hLA0 : 0 ≤ (Real.log x) ^ A := Real.rpow_nonneg hL0 A
  have hpos2 : 0 < (x ^ (11 / 20 + ε)) ^ 2 := by positivity
  calc (q : ℝ) * ((q : ℝ) * sieveQ ε x) ^ 2 * (Real.log x) ^ A / (x ^ (11 / 20 + ε)) ^ 2
      ≤ (sieveQ ε x : ℝ) ^ 5 * (Real.log x) ^ A / (x ^ (11 / 20 + ε)) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hpos2.le
        exact mul_le_mul_of_nonneg_right h1 hLA0
    _ ≤ (x ^ (11 / 20 + ε)) ^ (5 / 16 : ℝ) * (Real.log x) ^ A /
          (x ^ (11 / 20 + ε)) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hpos2.le
        exact mul_le_mul_of_nonneg_right h2 hLA0
    _ = ((x ^ (11 / 20 + ε)) ^ (5 / 16 : ℝ) / (x ^ (11 / 20 + ε)) ^ 2) * (Real.log x) ^ A := by
        field_simp
    _ ≤ x ^ (-(9 / 10) : ℝ) * (Real.log x) ^ A :=
        mul_le_mul_of_nonneg_right hY3 hLA0
    _ ≤ x ^ (-(9 / 10) : ℝ) * ((20 * A / 9) ^ A * x ^ (9 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (by linarith) _)
    _ = (20 * A / 9) ^ A * (x ^ (-(9 / 10) : ℝ) * x ^ (9 / 20 : ℝ)) := by ring
    _ ≤ (20 * A / 9) ^ A * 1 := by
        have hxle : x ^ (-(9 / 10) : ℝ) * x ^ (9 / 20 : ℝ) = x ^ (-(9 / 20) : ℝ) := by
          rw [← Real.rpow_add (by linarith : (0:ℝ) < x)]
          try norm_num
        have hle1 : x ^ (-(9 / 20) : ℝ) ≤ 1 := by
          calc x ^ (-(9 / 20) : ℝ) = (x ^ (9 / 20 : ℝ))⁻¹ := by
                rw [← Real.rpow_neg (by linarith : (0:ℝ) ≤ x)]
                try norm_num
            _ ≤ 1 := by
                rw [inv_le_one₀ (Real.rpow_pos_of_pos (by linarith) _)]
                exact Real.one_le_rpow hx1 (by norm_num)
        rw [hxle]
        exact mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg (by positivity) A)
    _ = (20 * A / 9) ^ A := by ring

/-- There are at most `q` Dirichlet characters of level `q`. -/
private lemma upslack_card_univ_le (q : ℕ) (hq : 1 ≤ q) :
    (Finset.univ : Finset (DirichletCharacter ℂ q)).card ≤ q := by
  have hq0 : q ≠ 0 := by omega
  haveI : NeZero q := ⟨hq0⟩
  have h1 : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := q)
  rw [Finset.card_univ, h1]
  exact Nat.totient_le q

/-- The summed bound over a set `F` of non-principal characters. -/
private lemma upslack_sum_le {ε x v c K A C0 : ℝ} {D : ℝ → ℕ → ℝ}
    (hx : 4 ≤ x) (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) (hc : 0 < c)
    (hDc : ∀ x m, c ≤ D x m)
    (hDLip : ∀ x : ℝ, ∀ m ∈ rightInterval ε x, ∀ m' ∈ rightInterval ε x,
      |D x m - D x m'| ≤ K * |(m : ℝ) - m'| / x ^ (11 / 20 + ε))
    {q : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x)
    (F : Finset (DirichletCharacter ℂ q)) (hF : ∀ χ ∈ F, χ ≠ 1) {z : ℝ}
    (hz1 : ((q : ℝ) * sieveQ ε x) / (6 * x ^ (11 / 20 + ε)) ≤ z)
    (hz2 : z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε))
    (hR : ∑ χ ∈ F,
        (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
        ≤ C0 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A)) :
    ∑ χ ∈ F,
        (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2)
      ≤ 2 * (|v| / c) ^ 2 *
          (C0 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A))
        + (F.card : ℝ) *
          ((3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
            (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
              ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4)) := by
  set cst := (3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
      (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
        ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4) with hcst
  have hstep : ∑ χ ∈ F,
        (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperNormCoeff ε (fun x m => v / D x m) x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * (v : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2)
      ≤ ∑ χ ∈ F, (2 * (|v| / c) ^ 2 *
          (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
        + cst) := by
    refine Finset.sum_le_sum fun χ hχ => ?_
    exact upslack_integrated_le (D := D) hx hε hε8 hc hDc hDLip hq hqQ χ (hF χ hχ) hz1 hz2
  have hsplit : ∑ χ ∈ F, (2 * (|v| / c) ^ 2 *
        (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
      + cst)
      = 2 * (|v| / c) ^ 2 *
          (∑ χ ∈ F,
            (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2))
        + (F.card : ℝ) * cst := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit] at hstep
  have hcst0 : 0 ≤ cst := by
    rw [hcst]
    have h1 : 0 ≤ |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
        ((x ^ (11 / 20 + ε)) * c ^ 2) :=
      div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right K 0)) upslack_B0_nonneg)
        (by positivity)
    have h2 := (le_max_right K 0)
    have h3 : (0:ℝ) ≤ (19 * ((q : ℝ) * sieveQ ε x)) ^ 4 := by positivity
    have h4 : 0 ≤ 3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2 := by
      have : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
      linarith
    positivity
  have hab : 0 ≤ |v| / c ^ 2 * 2 * 0 + 2 * (|v| / c) ^ 2 := by positivity
  refine le_trans hstep ?_
  have hcoe : 0 ≤ 2 * (|v| / c) ^ 2 := by positivity
  have hcard : (F.card : ℝ) ≤ (q : ℝ) := by
    have h1 : F.card ≤ q := by
      calc F.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := Finset.card_le_univ F
        _ ≤ q := upslack_card_univ_le q hq
    exact_mod_cast h1
  have h1 : 2 * (|v| / c) ^ 2 * (∑ χ ∈ F,
      (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2))
      ≤ 2 * (|v| / c) ^ 2 *
        (C0 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A)) :=
    mul_le_mul_of_nonneg_left hR hcoe
  have h2 : (F.card : ℝ) * cst ≤ (q : ℝ) * cst :=
    mul_le_mul_of_nonneg_right hcard hcst0
  linarith [h1, h2]

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
  obtain ⟨C0, hC0⟩ := hE A hA
  set K2 : ℝ := 5 * 19 ^ 4 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ)) ^ 2 / c ^ 4 with hK2def
  refine ⟨max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4, fun x hx q hq hqQ => ?_⟩
  -- basic facts
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hx1 : 1 ≤ x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hC0x : C0 ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hC0C : C0 ≤ max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hK1C : 2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A ≤
      max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨hcard0, hrawz⟩ := hC0 x hC0x q hq hqQ
  refine ⟨?_, fun z hz1 hz2 => ?_⟩
  · -- the cardinality of the exceptional set
    have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hL2 : (0 : ℝ) ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hLpos.le _
    refine le_trans hcard0 ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hq2) hL2
  · -- the mean square
    have hkey := upslack_key (ε := ε) (A := A) (x := x) (q := q) hε hx4 hA hq hqQ
    have hLmul : (Real.log x) ^ A * (Real.log x) ^ (-A) = 1 := by
      rw [← Real.rpow_add hLpos]
      simp
    have hR : ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
        (∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((upperRawWeight ε (x ^ (11 / 20 + ε)) m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2)
        ≤ C0 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A) :=
      hrawz z hz1 hz2
    have hstep := upslack_sum_le (D := D) (v := v) (A := A) (C0 := C0) hx4 hε hε8 hc hDc hDLip hq hqQ
      (((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1)
      (fun χ hχ => (Finset.mem_erase.mp hχ).1) hz1 hz2 hR
    -- the two pieces of the constant
    have hS0 : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A) := by
      have h1 : 0 ≤ (q : ℝ) * sieveQ ε x := by positivity
      have h2 : (0:ℝ) ≤ (Real.log x) ^ (-A) := Real.rpow_nonneg hLpos.le _
      positivity
    have hK2nn : 0 ≤ K2 := by
      rw [hK2def]
      have h1 : 0 ≤ |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right K 0)) upslack_B0_nonneg
      positivity
    have hcst0 : 0 ≤ (3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
        (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
          ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4) := by
      have h1 : 0 ≤ |v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
          ((x ^ (11 / 20 + ε)) * c ^ 2) :=
        div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right K 0)) upslack_B0_nonneg)
          (by positivity)
      have h4 : 0 ≤ 3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2 := by
        have : 0 ≤ x ^ (11 / 20 + ε) := hYpos.le
        linarith
      positivity
    -- the error piece, measured in the scale of the right-hand side
    set T : ℝ := ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A) with hT
    have hT0 : 0 ≤ T := by rw [hT]; exact hS0
    have herr : (q : ℝ) * ((3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
          (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
            ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4))
        ≤ (K2 * (20 * A / 9) ^ A) * T := by
      have e : (q : ℝ) * ((3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
            (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
              ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4))
          = (K2 * ((q : ℝ) * ((q : ℝ) * sieveQ ε x) ^ 2 * (Real.log x) ^ A /
              (x ^ (11 / 20 + ε)) ^ 2)) * T := by
        have hinv : (Real.log x) ^ (-A) = ((Real.log x) ^ A)⁻¹ := by
          rw [← Real.rpow_neg hLpos.le]
          try congr 1
          try ring
        rw [hT, hK2def, hinv]
        field_simp
        try ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hK2nn) hT0
    -- assemble
    have hrew : C0 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A) =
        C0 * T := by rw [hT]; ring
    rw [hrew] at hstep
    have hcardq : (((((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1).card : ℕ) : ℝ)
        ≤ (q : ℝ) := by
      have h1 : (((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1).card ≤ q := by
        refine le_trans (Finset.card_le_univ _) ?_
        exact upslack_card_univ_le q hq
      exact_mod_cast h1
    have hsub : (((((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1).card : ℕ) : ℝ) *
        ((3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
          (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
            ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4))
        ≤ (q : ℝ) * ((3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
          (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
            ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4)) :=
      mul_le_mul_of_nonneg_right hcardq hcst0
    have hmain : (2 * (|v| / c) ^ 2 * C0) * T + (K2 * (20 * A / 9) ^ A) * T ≤
        (max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4) * T := by
      have h := mul_le_mul_of_nonneg_right hK1C hT0
      have e : (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A) * T =
          (2 * (|v| / c) ^ 2 * C0) * T + (K2 * (20 * A / 9) ^ A) * T := by ring
      rw [e] at h
      exact h
    have e1 : 2 * (|v| / c) ^ 2 * (C0 * T) = (2 * (|v| / c) ^ 2 * C0) * T := by ring
    have hcomb : 2 * (|v| / c) ^ 2 * (C0 * T) +
        (q : ℝ) * ((3 * x ^ (11 / 20 + ε) - x ^ (11 / 20 + ε) / 2) *
          (2 * (|v| * max K 0 * (1 + 18 + 18 ^ 2 + 18 ^ 3 : ℝ) /
            ((x ^ (11 / 20 + ε)) * c ^ 2)) ^ 2 * (19 * ((q : ℝ) * sieveQ ε x)) ^ 4))
        ≤ (max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4) * T := by
      have h1 := add_le_add (le_refl (2 * (|v| / c) ^ 2 * (C0 * T))) herr
      rw [e1] at h1 ⊢
      exact le_trans h1 hmain
    refine le_trans hstep ?_
    refine le_trans (add_le_add (le_refl _) hsub) ?_
    refine le_trans hcomb ?_
    rw [show (max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4) * T =
        (max (max C0 (2 * (|v| / c) ^ 2 * C0 + K2 * (20 * A / 9) ^ A)) 4) *
          ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * (Real.log x) ^ (-A) from by
      rw [hT]; ring]


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
