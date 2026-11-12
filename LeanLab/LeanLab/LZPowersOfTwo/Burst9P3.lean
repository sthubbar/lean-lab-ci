/-
ROUTE BURST session 9, LZPowersOfTwo table step: the new top assembly.
Paper: P0079 A. Languasco and A. Zaccagnini, "On a Diophantine problem with two primes and
s powers of two", arXiv 0811.3663v2, 2 Apr 2009.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

`lz_theorem_tr_of_p3 : MainStatement nuTr IsTr` is the burst 8 assembly
`Burst8P2.lz_theorem_tr_of_p2` with the cited leaf `khalfalah_pintz_lemma1_p2` replaced by
`Burst9Table.khalfalah_pintz_lemma1_p3`, which has the same statement and is CONDITIONAL ON
the reduced LEAF `kp_mean_leaf_p3` only. The proofs below are copies of the burst 8 proofs
of `S1_eventually_p2`, `paired_second_moment_p2`, `minor_good_p2`, `minor_upper_p2`,
`count_bound_p2` and `lz_theorem_tr_of_p2`, with only the names of the replaced inputs
changed. No statement is new.
-/
import LeanLab.LZPowersOfTwo.Burst8P2
import LeanLab.LZPowersOfTwo.Burst9KP

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst9Table

open LeanLab.LZPowersOfTwo LeanLab.LZPowersOfTwo.Burst4Split LeanLab.LZPowersOfTwo.Burst8P2

/-- P0079 page 7, display (28): from Lemma 1 and (22), eventually
`S(1, N) ≤ 2 (1 + 0.2792521041) N²`. CONDITIONAL ON `kp_mean_leaf_p3`. -/
theorem S1_eventually_p3 :
    ∀ᶠ N : ℕ in atTop, S1 N ≤ 2 * (1 + 0.2792521041) * (N : ℝ) ^ 2 := by
  obtain ⟨A, hA, hA'⟩ := khalfalah_pintz_lemma1_p3
  have h := hA.eventually (eventually_lt_nhds hA')
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  have := (div_lt_iff₀ hN0).mp (by linarith : S1 N / (2 * (N : ℝ) ^ 2) < 1 + 0.2792521041)
  linarith

/-! ### Lemma 4 with the constant of display (28) -/

/-- P0079 pages 6 to 7, Lemma 4 with the constant `2 B (1 + A(1))` of display (28), the exact
statement of the session 4 leaf `Burst4Split.paired_second_moment_sharpB4`.
CONDITIONAL ON `chen_lemma3_p2` and `khalfalah_pintz_lemma1_p3`; `theta_pnt_p2` is
PROVED. This proof has no sorry of its own. -/
theorem paired_second_moment_p3 (s : ℕ) (μ : ℕ → ℝ) (l m η ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hl : l ≠ 0) (hm : m ≠ 0)
    (r : ℚ) (hr : (r : ℝ) = l / m) (hη : 0 < η) (hη' : η < |l / r.num|)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ᶠ X : ℝ in atTop,
      (∫ α : ℝ, pairedMoment396 l m (cutoff293 s μ ε X) η ε X α) ≤
        (log 2 + bigCSharpB4 * Sprime r.den) * η * X * (cutoff293 s μ ε X) ^ 2 := by
  set M := ∑ i : Fin s, |μ i|
  set c := log (2 * M) - log ε
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  set K := max 0 (c * (1 - ε / 4) / (ε / 4 * log 2))
  have hcut := cutoff_tendsto353 s μ ε hM hε
  have hfloor : Tendsto (fun X => ⌊cutoff293 s μ ε X⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hcut
  have hhalf : Tendsto (fun X : ℝ => ε * X / 2) atTop atTop := by
    have : Tendsto (fun X : ℝ => (ε / 2) * X) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_id
    convert this using 2; ring
  filter_upwards [chen_lemma3_p2 ε hε hε', eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (2 / ε),
    theta_bounds_p2 (ε / 8) (by positivity),
    hhalf.eventually (theta_bounds_p2 (ε / 8) (by positivity)),
    hfloor.eventually S1_eventually_p3,
    hcut.eventually (eventually_ge_atTop K)] with X H3 hX1 hXe hθ hθh hS1 hLK
  set L := cutoff293 s μ ε X with hL
  set N := ⌊L⌋₊
  have hX0 : 0 ≤ X := by linarith
  have hXε : 2 < ε * X := by
    have := (div_lt_iff₀ hε).mp hXe; linarith
  have hL0 : 0 ≤ L := le_trans (le_max_left _ _) hLK
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hL0
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- `log X = L log 2 + c`
  have hlogX : log X = L * log 2 + c := by
    have hpos : 0 < ε * X / (2 * M) := by positivity
    have h := Real.log_div_log (b := 2) (x := ε * X / (2 * M))
    rw [hL]
    unfold cutoff293
    rw [← h, div_mul_cancel₀ _ hlog2.ne', Real.log_div (by positivity) (by positivity),
      Real.log_mul hε.ne' (by positivity)]
    ring
  have hlogX0 : 0 ≤ log X := log_nonneg hX1
  -- the diagonal
  have hD : (∑ p ∈ boxP ε X, log p * log p) ≤ log X * (X * (1 - ε / 4)) := by
    refine (diag_theta_p2 ε X hε hε' hX1).trans (mul_le_mul_of_nonneg_left ?_ hlogX0)
    have h1 := hθ.2
    have h2 := hθh.1
    nlinarith
  have hLc : c * (1 - ε / 4) ≤ ε / 4 * log 2 * L := by
    have h := le_trans (le_max_right _ _) hLK
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hdiag : (N : ℝ) * (∑ p ∈ boxP ε X, log p * log p) ≤ log 2 * X * L ^ 2 := by
    calc (N : ℝ) * (∑ p ∈ boxP ε X, log p * log p)
        ≤ L * (log X * (X * (1 - ε / 4))) := by
          apply mul_le_mul hNL hD (sum_nonneg (fun p _ =>
            mul_nonneg (log_nat_nonneg_p2 p) (log_nat_nonneg_p2 p))) hL0
      _ = X * (L * ((L * log 2 + c) * (1 - ε / 4))) := by rw [hlogX]; ring
      _ ≤ X * (L * (L * log 2)) := by
          apply mul_le_mul_of_nonneg_left _ hX0
          apply mul_le_mul_of_nonneg_left _ hL0
          nlinarith
      _ = log 2 * X * L ^ 2 := by ring
  -- the off-diagonal
  have hS1' : S1 N ≤ 2 * (1 + 0.2792521041) * L ^ 2 := by
    refine hS1.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact pow_le_pow_left₀ hN0 hNL 2
  have hoff : 3.9171 * Sprime r.den * X * S1 N ≤ bigCSharpB4 * Sprime r.den * X * L ^ 2 := by
    have hq := (Sprime_pos293 r.den).le
    have : 0 ≤ 3.9171 * Sprime r.den * X := by positivity
    calc 3.9171 * Sprime r.den * X * S1 N
        ≤ 3.9171 * Sprime r.den * X * (2 * (1 + 0.2792521041) * L ^ 2) :=
          mul_le_mul_of_nonneg_left hS1' this
      _ = bigCSharpB4 * Sprime r.den * X * L ^ 2 := by unfold bigCSharpB4; ring
  rw [moment_eq_solutions_p2 l m L η ε X r hl hm hr hη hη']
  have hW := solutions_le_p2 l m ε X r hl hm hr hX0 hXε H3 N
  calc η * ∑ m1 ∈ Icc 1 N, ∑ m2 ∈ Icc 1 N, solV l m ε X m1 m2
      ≤ η * (log 2 * X * L ^ 2 + bigCSharpB4 * Sprime r.den * X * L ^ 2) :=
        mul_le_mul_of_nonneg_left (hW.trans (by linarith)) hη.le
    _ = (log 2 + bigCSharpB4 * Sprime r.den) * η * X * L ^ 2 := by ring


/-! ### (18), the minor arc, with the constant of (28) -/

/-- P0079 page 11, display (41), ordinary part of the minor arc.
CONDITIONAL ON `paired_second_moment_p3`. The proof is the one of `minor_good396`
with the constant of display (28). -/
theorem minor_good_p3 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
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
  filter_upwards [paired_second_moment_p3 s μ l1 (μ 0) η ε hM (by linarith) (hμ 0)
    r1 hr1 hη hη1 hε hε1,
    paired_second_moment_p3 s μ l2 (μ 1) η ε hM (by linarith) (hμ 1)
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
display (28), for `λ1/λ2` transcendental, section 7.
CONDITIONAL ON `paired_second_moment_p3` and `minor_bad_tr_p2`. -/
theorem minor_upper_p3 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : ν = nuTr ∧ IsTr (l1 / l2))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in minor293 X (cutoff293 s μ ε X), integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (ν ^ (s - 2) * CqSharpB4 r1.den r2.den + δ) * η * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  filter_upwards [minor_good_p3 ν s l1 l2 μ γ η ε hs h1 h2 (Or.inl hc) hμ r1 r2
    hr1 hr2 hη hη1 hη2 hε hε' (δ / 2) (by positivity),
    minor_bad_tr_p2 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
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

/-! ### Assembly of (13), (16), (17), (18), (19) -/

/-- P0079 pages 4 to 5, displays (13) to (19), with the minor constant of display (28).
CONDITIONAL ON `prime_integer_l2_small_p3`, `paired_second_moment_p3` and
`minor_bad_tr_p2`. Counting, display (13), is `count_integral353`, PROVED; the trivial arc,
display (17), is `trivial_small418`, PROVED; the major arc, display (16), is
`major_lower_p2`. The proof follows `count_bound_at_margin418`. -/
theorem count_bound_p3 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : ν = nuTr ∧ IsTr (l1 / l2))
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
  have Hmajor := major_lower_p2 s l1 l2 μ γ η ε hs h1 h2 hr hμ hη hε hε'
  have Hminor := minor_upper_p3 ν s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ r1 r2
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
`LeanLab.LZPowersOfTwo.lz_theorem_tr`. CONDITIONAL ON `prime_integer_l2_small_p3`,
`paired_second_moment_p3` and `minor_bad_tr_p2`; this proof itself has no sorry.
The threshold `η0` is `1`: every `η` allowed by the lattice bounds works. -/
theorem lz_theorem_tr_of_p3 : MainStatement nuTr IsTr := by
  intro l1 l2 μ h1 h2 hr hi hk hμ r1 r2 hr1 hr2
  refine ⟨1, one_pos, fun η hη _ hη1 hη2 γ s hs hs0 => ?_⟩
  have hη1' : η < |l1 / r1.num| := hη1.trans_le (le_abs_self _)
  have hl : 0 < |l1 * l2| := abs_pos.mpr (mul_ne_zero (by linarith) (by linarith))
  obtain ⟨ε, hε, hε', hgap⟩ := margin_B4 nuTr l1 l2 η r1.den r2.den s nuTr_pos nuTr_lt_one
    h1 hl hη hs hs0
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hc : nuTr = nuTr ∧ IsTr (l1 / l2) := ⟨rfl, hk⟩
  obtain ⟨c, hc', H⟩ := count_bound_p3 nuTr s l1 l2 μ γ η ε hs h1 h2 hr hi hc hμ
    r1 r2 hr1 hr2 hη hη1' hη2 hε hε' hM hgap
  exact infinite_of_NX_lower293 (count_to_density293 s l1 l2 μ γ η ε c hs hM hη hε hc' H)

/-- The type agrees with the cited statement. -/
example : MainStatement nuTr IsTr := lz_theorem_tr_of_p3

end LeanLab.LZPowersOfTwo.Burst9Table
