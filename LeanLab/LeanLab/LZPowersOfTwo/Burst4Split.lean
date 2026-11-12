/-
ROUTE BURST session 4, split of the cited main theorem `lz_theorem_tr`.
Paper: P0079 A. Languasco and A. Zaccagnini, "On a Diophantine problem with two primes and
s powers of two", arXiv 0811.3663v2, 2 Apr 2009.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

The paper's own top-level structure, Section 2 and Section 8, is
* (11) to (13): the integral `I(X; R)` is at most `η log² X · N(X)`,
* (16): the major arc lower bound with `c1 = (1 - 4 λ1 ε) / (2 |λ1 λ2|)`,
* (17): the trivial arc is `o(X L^s)`,
* (18): the minor arc upper bound with `c2(s) = ν^{s-2} C(q1, q2)`,
* (19): `c1 η - c2(s) > 0` for `s ≥ s0`, Section 8.

Step (19) at the exact `s0` of (2) is the old endpoint QUESTION of the folder, see
`endpoint_margin_negative293`: with the printed constant `C = 10.0219168340` the margin can be
negative at `s = s0`. The paper's own Lemma 4 proof, display (28), gives the constant
`2 B (1 + A(1))` with `B = 3.9171` and the strict bound `A(1) < 0.2792521041` of (22), and the
printed `C` is a rounding up of `2 · 3.9171 · 1.2792521041`. Using that constant in the minor
arc input, display (41), gives a strictly smaller `c2(s)`, and then the margin of (19) is
positive at every `s ≥ s0` once `ε` is small; this is `margin_B4` below, PROVED.

Sorry leaves the final theorem depends on:
* `paired_second_moment_sharpB4`, NEW: Lemma 4 with the constant of display (28).
* `minor_bad353`, existing: displays (38) to (40) and (43), exceptional part of the minor arc.
* `prime_integer_l2_small418`, existing: Lemmas 6 and 7 for the major arc J2, J3.
Everything else is proved here or in earlier folder files.
-/
import LeanLab.LZPowersOfTwo.Decomp418e

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst4Split

open LeanLab.LZPowersOfTwo

/-! ### The constant of display (28) -/

/-- P0079 page 6, proof of Lemma 4: `C = 2 B (1 + A(1))` with Chen's `B = 3.9171`, page 6,
and the bound `A(1) < 0.2792521041` of display (22), page 5. -/
def bigCSharpB4 : ℝ := 2 * 3.9171 * (1 + 0.2792521041)

/-- The printed `C = 10.0219168340` of (4) is strictly above `2 · 3.9171 · 1.2792521041`. -/
theorem bigCSharp_lt_bigC : bigCSharpB4 < bigC := by
  norm_num [bigCSharpB4, bigC]

theorem bigCSharp_pos : 0 < bigCSharpB4 := by
  norm_num [bigCSharpB4]

/-- (4) with the constant of display (28) in place of the printed `C`. -/
def CqSharpB4 (q1 q2 : ℕ) : ℝ :=
  √(log 2 + bigCSharpB4 * Sprime q1) * √(log 2 + bigCSharpB4 * Sprime q2)

theorem CqSharp_pos (q1 q2 : ℕ) : 0 < CqSharpB4 q1 q2 := by
  unfold CqSharpB4
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  apply mul_pos
  · exact sqrt_pos.mpr (add_pos_of_pos_of_nonneg h2
      (mul_nonneg bigCSharp_pos.le (Sprime_pos293 _).le))
  · exact sqrt_pos.mpr (add_pos_of_pos_of_nonneg h2
      (mul_nonneg bigCSharp_pos.le (Sprime_pos293 _).le))

/-- The sharper `C(q1, q2)` is strictly below the printed one. -/
theorem CqSharp_lt_Cq (q1 q2 : ℕ) : CqSharpB4 q1 q2 < Cq q1 q2 := by
  unfold CqSharpB4 Cq
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hS1 := Sprime_pos293 q1
  have hS2 := Sprime_pos293 q2
  have hC := bigCSharp_lt_bigC
  have hCp := bigCSharp_pos
  have a1 : 0 < log 2 + bigCSharpB4 * Sprime q1 := by positivity
  have a2 : 0 < log 2 + bigCSharpB4 * Sprime q2 := by positivity
  have l1 : √(log 2 + bigCSharpB4 * Sprime q1) < √(log 2 + bigC * Sprime q1) :=
    sqrt_lt_sqrt a1.le (by nlinarith)
  have l2 : √(log 2 + bigCSharpB4 * Sprime q2) < √(log 2 + bigC * Sprime q2) :=
    sqrt_lt_sqrt a2.le (by nlinarith)
  exact mul_lt_mul'' l1 l2 (sqrt_nonneg _) (sqrt_nonneg _)

/-! ### The remaining new leaf -/

/-- LEAF, sorry. P0079 pages 6 to 7, Lemma 4, with the constant as the proof derives it in
displays (25) to (28): the diagonal (26) gives `(1 - ε) log 2 · η X L²` plus `O(η X L)`, and
(27) to (28) with Lemma 1, Lemma 3 and the strict bound (22) give at most
`2 B (1 + A(1)) S'(q) η X L²` for large `X` with `A(1) < 0.2792521041`.
The `ε log 2` slack absorbs the `O(η X L)` remainder. This is the same statement as the
existing folder leaf `paired_second_moment396` except that the constant is the one of
display (28) instead of its printed rounding `C = 10.0219168340`. -/
theorem paired_second_moment_sharpB4 (s : ℕ) (μ : ℕ → ℝ) (l m η ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hl : l ≠ 0) (hm : m ≠ 0)
    (r : ℚ) (hr : (r : ℝ) = l / m) (hη : 0 < η) (hη' : η < |l / r.num|)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ᶠ X : ℝ in atTop,
      (∫ α : ℝ, pairedMoment396 l m (cutoff293 s μ ε X) η ε X α) ≤
        (log 2 + bigCSharpB4 * Sprime r.den) * η * X * (cutoff293 s μ ε X) ^ 2 := by
  sorry

/-! ### (18), the minor arc, with the constant of (28) -/

/-- P0079 page 11, display (41), ordinary part of the minor arc.
CONDITIONAL ON `paired_second_moment_sharpB4`. The proof is the one of `minor_good396`
with the constant of display (28). -/
theorem minor_good_sharpB4 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1)
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X),
        integrand293 s l1 l2 μ γ η ε X α‖ ≤
          (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  have hν : 0 ≤ ν := by
    rcases hc with h | h
    · rw [h.1]; exact nuTr_pos.le
    · rw [h.1]; exact nuAlg_pos.le
  have hA : 0 < log 2 + bigCSharpB4 * Sprime r1.den := add_pos_of_pos_of_nonneg
    (log_pos (by norm_num)) (mul_nonneg bigCSharp_pos.le (Sprime_pos293 _).le)
  have hB : 0 < log 2 + bigCSharpB4 * Sprime r2.den := add_pos_of_pos_of_nonneg
    (log_pos (by norm_num)) (mul_nonneg bigCSharp_pos.le (Sprime_pos293 _).le)
  let a := sqrt (log 2 + bigCSharpB4 * Sprime r1.den)
  let b := sqrt (log 2 + bigCSharpB4 * Sprime r2.den)
  have ha : 0 < a := sqrt_pos.mpr hA
  have hb : 0 < b := sqrt_pos.mpr hB
  intro δ hδ
  filter_upwards [paired_second_moment_sharpB4 s μ l1 (μ 0) η ε hM (by linarith) (hμ 0)
    r1 hr1 hη hη1 hε hε1,
    paired_second_moment_sharpB4 s μ l2 (μ 1) η ε hM (by linarith) (hμ 1)
    r2 hr2 hη hη2 hε hε1,
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (2 : ℝ)] with X hm1 hm2 hL hX
  let E := minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hE : MeasurableSet E := by
    apply MeasurableSet.diff _ hbad
    unfold minor293
    measurability
  have hG : ∀ α ∈ E, ∀ i : Fin s,
      ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤ ν * cutoff293 s μ ε X := by
    intro α hα i
    by_contra H
    exact hα.2 ⟨i, lt_of_not_ge H⟩
  have hm1' : (∫ α : ℝ, pairedMoment396 l1 (μ 0) (cutoff293 s μ ε X) η ε X α) ≤
      a ^ 2 * (η * X * (cutoff293 s μ ε X) ^ 2) := by
    simpa only [a, sq_sqrt hA.le, mul_assoc] using hm1
  have hm2' : (∫ α : ℝ, pairedMoment396 l2 (μ 1) (cutoff293 s μ ε X) η ε X α) ≤
      b ^ 2 * (η * X * (cutoff293 s μ ε X) ^ 2) := by
    simpa only [b, sq_sqrt hB.le, mul_assoc] using hm2
  have H := paired_integral_bound396 s l1 l2 μ γ η ε X (ν * cutoff293 s μ ε X)
    a b (η * X * (cutoff293 s μ ε X) ^ 2) E hE hs (mul_nonneg hν hL) ha hb hG hm1' hm2'
  have hp : (cutoff293 s μ ε X) ^ (s - 2) * (cutoff293 s μ ε X) ^ 2 =
      (cutoff293 s μ ε X) ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have he : (ν * cutoff293 s μ ε X) ^ (s - 2) * a * b *
      (η * X * (cutoff293 s μ ε X) ^ 2) =
        ν ^ (s - 2) * CqSharpB4 r1.den r2.den * η * X * (cutoff293 s μ ε X) ^ s := by
    calc
      _ = ν ^ (s - 2) * CqSharpB4 r1.den r2.den * η * X *
          ((cutoff293 s μ ε X) ^ (s - 2) * (cutoff293 s μ ε X) ^ 2) := by
        dsimp [a, b, CqSharpB4]
        rw [mul_pow]
        ring
      _ = _ := by rw [hp]
  apply H.trans
  rw [he]
  have hW : 0 ≤ η * X * (cutoff293 s μ ε X) ^ s := by positivity
  nlinarith only [mul_nonneg hδ.le hW]

/-- P0079 pages 11 to 12, displays (41) to (43), the conclusion (18) with the constant of
display (28). CONDITIONAL ON `paired_second_moment_sharpB4` and `minor_bad353`. -/
theorem minor_upper_sharpB4 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [minor_good_sharpB4 ν s l1 l2 μ γ η ε hs h1 h2 hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity),
    minor_bad353 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity)] with X hg hb
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  have hsplit := integral_inter_add_sdiff (s := minor293 X (cutoff293 s μ ε X)) hbad
    (integrand_integrable293 s l1 l2 μ γ η ε X).integrableOn
  rw [← hsplit]
  calc
    _ ≤ ‖∫ α in minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ +
      ‖∫ α in minor293 X (cutoff293 s μ ε X) \ badPower353 s ν μ ε X,
        integrand293 s l1 l2 μ γ η ε X α‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### (19), Section 8, the threshold, PROVED -/

/-- P0079 page 2, (2), and page 12, Section 8. For `s ≥ s0` the printed formula gives
`ν^{s-2} C(q1, q2) ≤ η / (2 |λ1 λ2|)`. PROVED, no analytic input. -/
theorem threshold_B4 (ν l1 l2 η : ℝ) (q1 q2 s : ℕ) (hν0 : 0 < ν) (hν1 : ν < 1)
    (hl : 0 < |l1 * l2|) (hη : 0 < η) (hs : 2 ≤ s) (hs0 : s0 ν l1 l2 q1 q2 η ≤ s) :
    ν ^ (s - 2) * Cq q1 q2 ≤ η / (2 * |l1 * l2|) := by
  have hC := Cq_pos293 q1 q2
  have hK : 0 < 2 * Cq q1 q2 * |l1 * l2| := by positivity
  have hd : 0 < -log ν := neg_pos.mpr (log_neg hν0 hν1)
  unfold s0 at hs0
  have hceil : ⌈(log (2 * Cq q1 q2 * |l1 * l2|) - log η) / (-log ν)⌉ ≤ (s : ℤ) - 2 := by
    omega
  have hx := Int.ceil_le.mp hceil
  have hcast : (((s : ℤ) - 2 : ℤ) : ℝ) = ((s - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hs]; push_cast; ring
  rw [hcast] at hx
  set k : ℕ := s - 2
  have hx' : log (2 * Cq q1 q2 * |l1 * l2|) - log η ≤ (k : ℝ) * (-log ν) :=
    (div_le_iff₀ hd).mp hx
  have hpow : 0 < ν ^ k := pow_pos hν0 k
  have hlog : log (ν ^ k * (2 * Cq q1 q2 * |l1 * l2|)) ≤ log η := by
    rw [log_mul hpow.ne' hK.ne', log_pow]
    linarith
  have hle : ν ^ k * (2 * Cq q1 q2 * |l1 * l2|) ≤ η :=
    (log_le_log_iff (by positivity) hη).mp hlog
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- P0079 page 5, display (19), at the exact `s0` of (2): with `ε` chosen small and the
minor constant of display (28), the margin `c1 η - c2(s)` is positive for `s ≥ s0`.
PROVED, no analytic input. -/
theorem margin_B4 (ν l1 l2 η : ℝ) (q1 q2 s : ℕ) (hν0 : 0 < ν) (hν1 : ν < 1)
    (h1 : 1 < l1) (hl : 0 < |l1 * l2|) (hη : 0 < η) (hs : 2 ≤ s)
    (hs0 : s0 ν l1 l2 q1 q2 η ≤ s) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / (8 * l1) ∧
      0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * CqSharpB4 q1 q2 := by
  have hT := threshold_B4 ν l1 l2 η q1 q2 s hν0 hν1 hl hη hs hs0
  have hC := Cq_pos293 q1 q2
  have hS := CqSharp_pos q1 q2
  have hlt := CqSharp_lt_Cq q1 q2
  have hP : 0 < ν ^ (s - 2) := pow_pos hν0 _
  have hl1 : 0 < l1 := by linarith
  set d := Cq q1 q2 - CqSharpB4 q1 q2 with hd
  have hd0 : 0 < d := by linarith
  have hdC : d < Cq q1 q2 := by linarith
  refine ⟨d / (16 * l1 * Cq q1 q2), by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have h4 : 4 * l1 * (d / (16 * l1 * Cq q1 q2)) = d / (4 * Cq q1 q2) := by
      field_simp; ring
    rw [h4]
    have hfrac : d / (4 * Cq q1 q2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have hT' : ν ^ (s - 2) * Cq q1 q2 ≤ η / (2 * |l1 * l2|) := hT
    have hmain : (1 - d / (4 * Cq q1 q2)) / (2 * |l1 * l2|) * η =
        (1 - d / (4 * Cq q1 q2)) * (η / (2 * |l1 * l2|)) := by ring
    rw [hmain]
    have hstep : (1 - d / (4 * Cq q1 q2)) * (ν ^ (s - 2) * Cq q1 q2) ≤
        (1 - d / (4 * Cq q1 q2)) * (η / (2 * |l1 * l2|)) :=
      mul_le_mul_of_nonneg_left hT' (by linarith)
    have hexp : (1 - d / (4 * Cq q1 q2)) * (ν ^ (s - 2) * Cq q1 q2) =
        ν ^ (s - 2) * Cq q1 q2 - ν ^ (s - 2) * d / 4 := by
      field_simp
    have hS' : ν ^ (s - 2) * CqSharpB4 q1 q2 = ν ^ (s - 2) * Cq q1 q2 - ν ^ (s - 2) * d := by
      rw [hd]; ring
    have hpd : 0 < ν ^ (s - 2) * d := mul_pos hP hd0
    linarith

/-! ### Assembly of (13), (16), (17), (18), (19) -/

/-- P0079 pages 4 to 5, displays (13) to (19), with the minor constant of display (28).
CONDITIONAL ON `prime_integer_l2_small418`, `paired_second_moment_sharpB4` and
`minor_bad353`. Counting, display (13), is `count_integral353`, PROVED; the trivial arc,
display (17), is `trivial_small418`, PROVED; the major arc, display (16), is
`major_lower418`. The proof follows `count_bound_at_margin418`. -/
theorem count_bound_sharpB4 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1))
    (hM : 0 < ∑ i : Fin s, |μ i|)
    (hgap : 0 < (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η -
      ν ^ (s - 2) * CqSharpB4 r1.den r2.den) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c * X * (cutoff293 s μ ε X) ^ s ≤
        η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  let gap := (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - ν ^ (s - 2) * CqSharpB4 r1.den r2.den
  have hg : 0 < gap := hgap
  have hε1 : ε < 1 := by
    have hd : 1 / (8 * l1) < (1 : ℝ) := (div_lt_one (by positivity)).mpr (by linarith)
    exact hε'.trans hd
  have Hmajor := major_lower418 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
  have Hminor := minor_upper_sharpB4 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (gap / 4) (by positivity)
  have Htrivial := trivial_small418 s l1 l2 μ γ η ε hs (by linarith) (by linarith)
    hμ hη hε hε1 (gap * η / 4) (by positivity)
  refine ⟨gap * η / 2, by positivity, ?_⟩
  filter_upwards [Hmajor, Hminor, Htrivial, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2 * ∑ i : Fin s, |μ i|) / ε)] with X hmajor hminor htrivial hX hXM
  obtain ⟨hint, hcount⟩ := count_integral353 s l1 l2 μ γ η ε X hη hε hX
  have hL : 0 ≤ cutoff293 s μ ε X := cutoff_nonneg293 s μ ε X hM
    (by simpa [mul_comm] using (div_le_iff₀ hε).mp hXM)
  have hW : 0 ≤ X * (cutoff293 s μ ε X) ^ s := mul_nonneg (by linarith) (pow_nonneg hL _)
  have hbound := arc_lower293 (integrand293 s l1 l2 μ γ η ε X) hint X
    (cutoff293 s μ ε X)
    ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2)
    ((ν ^ (s - 2) * CqSharpB4 r1.den r2.den + gap / 4) * η)
    (gap * η / 4) (X * (cutoff293 s μ ε X) ^ s)
    (by nlinarith only [hmajor]) (by nlinarith only [hminor]) (by nlinarith only [htrivial])
  have heq : ((1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η ^ 2 -
      (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + gap / 4) * η - gap * η / 4) = gap * η / 2 := by
    dsimp [gap]
    ring
  rw [heq] at hbound
  nlinarith only [hbound, hcount]

/-! ### The main theorem from the split -/

/-- P0079 Theorem, `λ1/λ2` transcendental, `s0` from (2), the exact type of
`LeanLab.LZPowersOfTwo.lz_theorem_tr`. CONDITIONAL ON `prime_integer_l2_small418`,
`paired_second_moment_sharpB4` and `minor_bad353`; this proof itself has no sorry.
The threshold `η0` is `1`: every `η` allowed by the lattice bounds works. -/
theorem lz_theorem_tr_of_split : MainStatement nuTr IsTr := by
  intro l1 l2 μ h1 h2 hr hi hk hμ r1 r2 hr1 hr2
  refine ⟨1, one_pos, fun η hη _ hη1 hη2 γ s hs hs0 => ?_⟩
  have hη1' : η < |l1 / r1.num| := hη1.trans_le (le_abs_self _)
  have hl : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  obtain ⟨ε, hε, hε', hgap⟩ := margin_B4 nuTr l1 l2 η r1.den r2.den s nuTr_pos nuTr_lt_one
    h1 hl hη hs hs0
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hc : (nuTr = nuTr ∧ IsTr (l1 / l2)) ∨ (nuTr = nuAlg ∧ IsAlg (l1 / l2)) :=
    Or.inl ⟨rfl, hk⟩
  obtain ⟨c, hc', H⟩ := count_bound_sharpB4 nuTr s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ
    r1 r2 hr1 hr2 hη hη1' hη2 hε hε' hM hgap
  exact infinite_of_NX_lower293 (count_to_density293 s l1 l2 μ γ η ε c hs hM hη hε hc' H)

/-- The type agrees with the cited statement. -/
example : MainStatement nuTr IsTr := lz_theorem_tr_of_split

end LeanLab.LZPowersOfTwo.Burst4Split
