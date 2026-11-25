import LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada

/-!
S136 split of `leaf_minor_arcs` of `Decomp598Theorem6LeavesKawada`, Halupczok P0077
pages 338 to 339, Theorem 2.2, display 2.4, adapted from Kawada 1993 Theorem 2.
https://doi.org/10.5802/jtnb.839

Kawada section 3 deduces the minor arc part of Theorem 2 in two steps.
* Display 3.5, proved in Kawada section 4 with Lemma 2, Bessel's inequality and the
  minor arc bound for the prime exponential sum: the weighted mean square
  `∑_{q ≤ Q} q ∑_b |I_{m}|^2 ≪ y^{k+1} (log x)^{-C+2k+1}`, here with `k = 2`.
  This is the new LEAF `leaf_kawada_display35`.
* Display 3.6, Cauchy Schwarz:
  `∑_{q ≤ Q} ∑_b |I_m| ≪ (∑_{q ≤ Q} 1/q)^{1/2} (y^{k-1} S_m)^{1/2}`.
  This step is proved here, `cauchy_schwarz_display36`, together with the harmonic bound
  `∑_{q ≤ Q} 1/q ≤ 1 + log Q` and the count of `kRange`.
The assembly `leaf_minor_arcs_of_leaves` has the statement of `leaf_minor_arcs` byte for byte.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136Minor

open Finset MeasureTheory
open scoped Classical
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada

/-- LEAF: Kawada 1993 display 3.5 for k = 2, proved in Kawada section 4, displays 4.1 to 4.5,
with Lemma 2 and Bessel's inequality; adapted as on Halupczok P0077 pages 338 to 339, where only
`Y ≫ X1^{2/3+ε}` is used on the minor arcs. Class HARD. The weighted mean square over the
minor arcs `unitDom X1 \ kMajor A C Y` is `≪ Y^{k+1} L^{-C+2k+1} = Y^3 L^{5-C}`; Kawada writes
`log x`, which is `≍ L` here since `X1^{2/3} ≪ Y ≤ X1`. -/
theorem leaf_kawada_display35 :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (q2 : ℝ) * ∑ k ∈ kRange X1 Y,
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ^ 2 ≤
          K * Y ^ 3 * Real.log Y ^ (5 - C) := by
  sorry

/-- Kawada display 3.6, Cauchy Schwarz twice, for nonnegative reals `I q k`. -/
theorem cauchy_schwarz_display36 (s T : Finset ℕ) (I : ℕ → ℕ → ℝ) (_hI : ∀ q k, 0 ≤ I q k)
    (hs : ∀ q ∈ s, 0 < q) :
    (∑ q ∈ s, ∑ k ∈ T, I q k) ^ 2 ≤
      (∑ q ∈ s, (1 / (q : ℝ))) * ((T.card : ℝ) * ∑ q ∈ s, (q : ℝ) * ∑ k ∈ T, I q k ^ 2) := by
  have hinner : ∀ q, (∑ k ∈ T, I q k) ^ 2 ≤ (T.card : ℝ) * ∑ k ∈ T, I q k ^ 2 := by
    intro q
    have := sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun k => I q k)
    simpa using this
  have hsplit : ∑ q ∈ s, ∑ k ∈ T, I q k =
      ∑ q ∈ s, (1 / Real.sqrt q) * (Real.sqrt q * ∑ k ∈ T, I q k) := by
    refine sum_congr rfl fun q hq => ?_
    have hq0 : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hs q hq)
    field_simp
  rw [hsplit]
  refine (sum_mul_sq_le_sq_mul_sq s _ _).trans ?_
  have h1 : ∑ q ∈ s, (1 / Real.sqrt q) ^ 2 = ∑ q ∈ s, (1 / (q : ℝ)) := by
    refine sum_congr rfl fun q hq => ?_
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg q), one_pow]
  have h2 : ∑ q ∈ s, (Real.sqrt q * ∑ k ∈ T, I q k) ^ 2 ≤
      (T.card : ℝ) * ∑ q ∈ s, (q : ℝ) * ∑ k ∈ T, I q k ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun q _ => ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
    have := hinner q
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (sum_nonneg fun q _ => by positivity)

/-- Harmonic bound used in Kawada display 3.6: `∑_{q ≤ N} 1/q ≤ 1 + log N`. -/
theorem sum_inv_Icc_le (N : ℕ) : ∑ q ∈ Icc 1 N, (1 / (q : ℝ)) ≤ 1 + Real.log N := by
  have := harmonic_le_one_add_log N
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
  simpa [one_div] using this

/-- The number of integers `k` with `X < k ≤ X + R` is at most `R + 1`, for `0 ≤ X`, `0 ≤ R`. -/
theorem kRange_card_le (X R : ℝ) (hX : 0 ≤ X) (hR : 0 ≤ R) :
    ((kRange X R).card : ℝ) ≤ R + 1 := by
  have hsub : kRange X R ⊆ Ioc ⌊X⌋₊ ⌊X + R⌋₊ := by
    intro k hk
    simp only [kRange, mem_filter] at hk
    simp only [mem_Ioc]
    refine ⟨?_, Nat.le_floor hk.2.2⟩
    exact (Nat.floor_lt hX).mpr hk.2.1
  have hc := card_le_card hsub
  rw [Nat.card_Ioc] at hc
  have hc' : ((kRange X R).card : ℝ) ≤ (⌊X + R⌋₊ : ℝ) - ⌊X⌋₊ := by
    have : ⌊X⌋₊ ≤ ⌊X + R⌋₊ := Nat.floor_le_floor (by linarith)
    have h := (Nat.cast_le (α := ℝ)).mpr hc
    rw [Nat.cast_sub this] at h
    exact h
  have h1 : (⌊X + R⌋₊ : ℝ) ≤ X + R := Nat.floor_le (by linarith)
  have h2 : X - 1 < (⌊X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one X
    linarith
  linarith

/-- Assembly: `leaf_minor_arcs` from Kawada display 3.5 and the Cauchy Schwarz step 3.6.
Statement identical to `Decomp598Theorem6LeavesKawada.leaf_minor_arcs`. -/
theorem leaf_minor_arcs_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  intro A ε hA hε
  obtain ⟨C0, hC0⟩ := leaf_kawada_display35 A ε hA hε
  refine ⟨max C0 (2 * A + 6), fun C hC => ?_⟩
  obtain ⟨B, hB, h35⟩ := hC0 C (le_trans (le_max_left _ _) hC)
  refine ⟨B, hB, fun c1 c3 hc1 hc3 a2 => ?_⟩
  obtain ⟨K, Y0, hK⟩ := h35 c1 c3 hc1 hc3 a2
  set D : ℝ := (2 + |Real.log c3|) * 2 * |K| with hD
  refine ⟨Real.sqrt D, max Y0 (Real.exp 1), ?_⟩
  intro X1 X2 Y Q2 hY0 h1 h2 h3 h4 hQ1 hQ2
  have hYe : Real.exp 1 ≤ Y := le_trans (le_max_right _ _) hY0
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos 1) hYe
  have hY1 : 1 ≤ Y := le_trans (by have := Real.add_one_le_exp 1; linarith) hYe
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYe
  have hLpos : 0 < Real.log Y := by linarith
  have hX2 : 1 ≤ X2 := le_trans hY1 h3
  have hX1 : 0 ≤ X1 := by linarith
  have hS := hK X1 X2 Y Q2 (le_trans (le_max_left _ _) hY0) h1 h2 h3 h4 hQ1 hQ2
  -- the harmonic sum
  have hQc : Q2 ≤ c3 * Y := by
    have ha : X2 ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX2 (by norm_num)
    have hb : Real.log Y ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    have ha0 : 0 ≤ X2 ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
    have hb0 : 0 ≤ Real.log Y ^ (-B) := Real.rpow_nonneg (by linarith) _
    calc Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) := hQ2
      _ ≤ c3 * Y * 1 * 1 := by gcongr
      _ = c3 * Y := by ring
  have hN1 : 1 ≤ ⌊Q2⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
  have hNle : (⌊Q2⌋₊ : ℝ) ≤ c3 * Y := (Nat.floor_le (by linarith)).trans hQc
  have hH : ∑ q ∈ Icc 1 ⌊Q2⌋₊, (1 / (q : ℝ)) ≤ (2 + |Real.log c3|) * Real.log Y := by
    refine (sum_inv_Icc_le _).trans ?_
    have hNpos : (0 : ℝ) < ⌊Q2⌋₊ := by exact_mod_cast hN1
    have : Real.log ⌊Q2⌋₊ ≤ Real.log c3 + Real.log Y := by
      rw [← Real.log_mul hc3.ne' hYpos.ne']
      exact Real.log_le_log hNpos hNle
    have := le_abs_self (Real.log c3)
    nlinarith [abs_nonneg (Real.log c3)]
  have hcard : ((kRange X1 Y).card : ℝ) ≤ 2 * Y := by
    have := kRange_card_le X1 Y hX1 hYpos.le
    linarith
  have hCS := cauchy_schwarz_display36 (Icc 1 ⌊Q2⌋₊) (kRange X1 Y)
    (fun q k => ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q a2 (2 * k) α‖)
    (fun _ _ => norm_nonneg _) (fun q hq => by simp at hq; omega)
  set S1 := ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ with hS1
  set W := ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (q2 : ℝ) * ∑ k ∈ kRange X1 Y,
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ^ 2 with hW
  have hW0 : 0 ≤ W := sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _)
    (sum_nonneg fun k _ => sq_nonneg _)
  have hS0 : 0 ≤ S1 := sum_nonneg fun q _ => sum_nonneg fun k _ => norm_nonneg _
  have hLC : Real.log Y ^ (5 - C) ≤ Real.log Y ^ (-2 * A - 1) :=
    Real.rpow_le_rpow_of_exponent_le hL (by have := le_max_right C0 (2 * A + 6); linarith)
  have hWb : W ≤ |K| * Y ^ 3 * Real.log Y ^ (-2 * A - 1) := by
    refine hS.trans ?_
    have hK' : K ≤ |K| := le_abs_self K
    have hp : 0 ≤ Real.log Y ^ (5 - C) := Real.rpow_nonneg hLpos.le _
    have hY3 : 0 ≤ Y ^ 3 := by positivity
    calc K * Y ^ 3 * Real.log Y ^ (5 - C) ≤ |K| * Y ^ 3 * Real.log Y ^ (5 - C) := by gcongr
      _ ≤ |K| * Y ^ 3 * Real.log Y ^ (-2 * A - 1) := by gcongr
  have hHn : 0 ≤ ∑ q ∈ Icc 1 ⌊Q2⌋₊, (1 / (q : ℝ)) := sum_nonneg fun q _ => by positivity
  have hsq : S1 ^ 2 ≤ D * (Y ^ 2 * Real.log Y ^ (-A)) ^ 2 := by
    refine hCS.trans ?_
    have e1 : Real.log Y * Real.log Y ^ (-2 * A - 1) = (Real.log Y ^ (-A)) ^ 2 := by
      calc Real.log Y * Real.log Y ^ (-2 * A - 1)
          = Real.log Y ^ (1 : ℝ) * Real.log Y ^ (-2 * A - 1) := by rw [Real.rpow_one]
        _ = Real.log Y ^ ((1 : ℝ) + (-2 * A - 1)) := (Real.rpow_add hLpos _ _).symm
        _ = Real.log Y ^ ((-A) + (-A)) := by ring_nf
        _ = Real.log Y ^ (-A) * Real.log Y ^ (-A) := Real.rpow_add hLpos _ _
        _ = (Real.log Y ^ (-A)) ^ 2 := by ring
    have hcard0 : (0 : ℝ) ≤ (kRange X1 Y).card := Nat.cast_nonneg _
    calc (∑ q ∈ Icc 1 ⌊Q2⌋₊, (1 / (q : ℝ))) * (((kRange X1 Y).card : ℝ) * W)
        ≤ ((2 + |Real.log c3|) * Real.log Y) * ((2 * Y) * (|K| * Y ^ 3 *
            Real.log Y ^ (-2 * A - 1))) := by
          gcongr
      _ = (2 + |Real.log c3|) * 2 * |K| * (Y ^ 4 *
            (Real.log Y * Real.log Y ^ (-2 * A - 1))) := by ring
      _ = D * (Y ^ 2 * Real.log Y ^ (-A)) ^ 2 := by rw [e1, hD]; ring
  have hD0 : 0 ≤ D := by positivity
  have hR0 : 0 ≤ Real.sqrt D * Y ^ 2 * Real.log Y ^ (-A) := by
    have := Real.rpow_nonneg hLpos.le (-A)
    positivity
  refine (pow_le_pow_iff_left₀ hS0 hR0 (n := 2) (by norm_num)).mp ?_
  rw [mul_assoc, mul_pow, Real.sq_sqrt hD0]
  exact hsq

end LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136Minor
