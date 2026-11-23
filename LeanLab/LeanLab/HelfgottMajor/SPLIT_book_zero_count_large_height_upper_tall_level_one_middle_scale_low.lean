import LeanLab.HelfgottMajor.SPLIT_book_zero_count_large_height_upper_tall_level_one_middle_scale
import LeanLab.PNTPort.DirichletZF.SiegelSigns

/-!
# Split of `book_zero_count_large_height_upper_tall_level_one_middle_scale_low`

At level one the `L`-function is the Riemann zeta function, and the upper side of the book
count on the middle scale is a published explicit Riemann von Mangoldt estimate. This file holds
the shared pieces for the four height subranges of the middle scale and the split of the low
subrange `10 ^ 7 ≤ T ≤ 10 ^ 8`:

* three CITED leaves, the explicit counts of Trudgian, J. Number Theory 134 (2014) 280 to 292,
  stated for the open count `0 < γ < T` of the lab, which is Trudgian's `N T`: Corollary 1,
  and the two forms obtained from display 1.2 and from Table 2 by display 2.5, exactly as
  Corollary 1 is obtained from Theorem 1;
* the proved fact that zeta has no zero on the open real segment `0 < σ < 1`;
* the proved bridge from the open count to the half weighted `bookCount` by the right limit in
  the height, and the proved arithmetic that each published error fits the book error
  `0.15 log T + 3.389` on its range.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.ZeroCount1623
open Complex Set Filter Topology
open scoped ComplexConjugate LSeries.notation

variable {q : ℕ} [NeZero q]

/-! ### Leaves -/

/-- Bridging step, the zeta function has no zero on the open real segment, so the half weight
of `bookCount` at height `0` sees nothing. Proved from the lab lemma
`LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg`, `ζ σ < 0` for `0 < σ < 1`. -/
theorem level_one_no_real_zero (χ : DirichletCharacter ℂ 1) {σ : ℝ} (h0 : 0 < σ)
    (h1 : σ < 1) : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  intro hL
  rw [DirichletCharacter.LFunction_modOne_eq] at hL
  have hneg := (LeanLab.PNTPort.DirichletZF.riemannZeta_real_neg h0 h1).2
  rw [hL] at hneg
  simp at hneg

/-- LEAF: the explicit Riemann von Mangoldt formula of Trudgian. HARD. CITED: Trudgian, An
improved upper bound for the argument of the Riemann zeta-function on the critical line II,
J. Number Theory 134 (2014), Corollary 1, section 1: for `T ≥ e`,
`|N T - T / (2π) log (T / (2π e)) - 7/8| ≤ 0.112 log T + 0.278 log log T + 2.510 + 0.2 / T`,
where `N T` counts the zeros `β + iγ`, `0 < β < 1`, `0 < γ < T`, with multiplicity. At level
one `DirichletCharacter.LFunction χ` is `riemannZeta`, so the sum below is `N T`. -/
theorem trudgian2014_corollary1 (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : Real.exp 1 ≤ T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im < T),
        (mult χ ρ : ℝ)) - T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) - 7 / 8|
      ≤ 0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.510 + 0.2 / T := by
  sorry

/-- LEAF: the explicit count at moderate height from the computed bound on `S T`. HARD.
CITED: Trudgian, J. Number Theory 134 (2014), display 1.2 third line, `|S T| ≤ 2.31366` for
`0 ≤ T ≤ 5.45 × 10 ^ 8`, quoted there from the computations of Brent, van de Lune, te Riele
and Winter, combined with display 2.5 of the same paper, which for `T ≥ 1` bounds
`|N T - T / (2π) log (T / (2π e)) - 7/8|` by `|S T|` plus
`(4π)⁻¹ arctan (1 / (2T)) + T / (4π) log (1 + 1 / (4 T ^ 2)) + 1 / (3π T) ≤ 0.2 / T`.
This is how Corollary 1 is deduced from Theorem 1 in the paper. -/
theorem trudgian2014_eq12_count (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 1 ≤ T)
    (hT' : T ≤ 5.45e8) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im < T),
        (mult χ ρ : ℝ)) - T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) - 7 / 8|
      ≤ 2.31366 + 0.2 / T := by
  sorry

/-- LEAF: the explicit count from the pure logarithmic bound on `S T`. HARD. CITED: Trudgian,
J. Number Theory 134 (2014), Table 2, row `T₀ = 10 ^ 8`: `|S T| ≤ 0.234 log T` for
`T > 10 ^ 8`, combined with display 2.5 as in `trudgian2014_eq12_count`. -/
theorem trudgian2014_table2_count (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 10 ^ 8 < T) :
    |(∑ ρ ∈ (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im < T),
        (mult χ ρ : ℝ)) - T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) - 7 / 8|
      ≤ 0.234 * Real.log T + 0.2 / T := by
  sorry

/-! ### Bridge from the open count to `bookCount`. Proved. -/

/-- If no strip zero lies on the real axis and the open count `0 < γ < t` is bounded by a
function continuous at `T` for all `t` just above `T`, then the half weighted `bookCount` at
`T` is bounded by the value at `T`. -/
lemma bookCount_le_of_open (χ : DirichletCharacter ℂ q) {T : ℝ}
    (hreal : ∀ ρ ∈ stripZeros χ T, ρ.im ≠ 0) (F : ℝ → ℝ) (hF : ContinuousAt F T)
    (hb : ∀ᶠ t in 𝓝[>] T, (∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter
        (fun ρ => 0 < ρ.im ∧ ρ.im < t), (mult χ ρ : ℝ)) ≤ F t) :
    bookCount χ T ≤ F T := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap χ T
  have hle : ∀ t, T < t → t < T + ε → bookCount χ T ≤
      ∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im < t),
        (mult χ ρ : ℝ) := by
    intro t ht1 ht2
    have he := hgap t ht1 ht2
    have hfs : (stripZeros_finite χ t).toFinset = (stripZeros_finite χ T).toFinset := by
      ext ρ; simp [he]
    rw [hfs]
    unfold bookCount
    have hfil : (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 < ρ.im ∧ ρ.im < t) =
        (stripZeros_finite χ T).toFinset.filter (fun ρ => 0 ≤ ρ.im) := by
      ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨h, h1, _⟩; exact ⟨h, h1.le⟩
      · rintro ⟨h, h1⟩
        refine ⟨h, lt_of_le_of_ne h1 (hreal ρ h).symm, ?_⟩
        exact lt_of_le_of_lt ((le_abs_self _).trans h.2.2.2) ht1
    rw [hfil]
    apply Finset.sum_le_sum
    intro ρ _
    have hw : halfWeight T ρ.im ≤ 1 := by unfold halfWeight; split_ifs <;> norm_num
    have hm : (0 : ℝ) ≤ (mult χ ρ : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hev : ∀ᶠ t in 𝓝[>] T, bookCount χ T ≤ F t := by
    have hmem : Ioo T (T + ε) ∈ 𝓝[>] T := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hmem, hb] with t ht hbt
    exact (hle t ht.1 ht.2).trans hbt
  exact ge_of_tendsto (hF.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- At level one no strip zero is real, from the leaf `level_one_no_real_zero`. -/
lemma level_one_strip_im_ne_zero (χ : DirichletCharacter ℂ 1) (T : ℝ) :
    ∀ ρ ∈ stripZeros χ T, ρ.im ≠ 0 := by
  intro ρ hρ him
  have hcast : ρ = ((ρ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hL : DirichletCharacter.LFunction χ ((ρ.re : ℝ) : ℂ) = 0 := by
    rw [← hcast]; exact hρ.1
  exact level_one_no_real_zero χ hρ.2.1 hρ.2.2.1 hL

/-- The level one upper side from an upper bound `B` on the open count error just above `T`,
continuous at `T`, that fits the book budget at `T`. -/
lemma level_one_upper_of_bound (χ : DirichletCharacter ℂ 1) {T : ℝ} (hT : 1 ≤ T)
    (B : ℝ → ℝ) (hB : ContinuousAt B T)
    (hb : ∀ᶠ t in 𝓝[>] T, (∑ ρ ∈ (stripZeros_finite χ t).toFinset.filter
        (fun ρ => 0 < ρ.im ∧ ρ.im < t), (mult χ ρ : ℝ)) -
        t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) - 7 / 8 ≤ B t)
    (hbud : 7 / 8 + B T ≤ 0.15 * Real.log T + 3.389) :
    bookCount χ T - bookMain 1 T ≤ bookError 1 T := by
  have hT0 : 0 < T := by linarith
  set M : ℝ → ℝ := fun t => t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1))
    with hM
  have hMc : ContinuousAt M T := by
    have hne : T / (2 * Real.pi * Real.exp 1) ≠ 0 := div_ne_zero hT0.ne' (by positivity)
    exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) hne)
  have key := bookCount_le_of_open χ (level_one_strip_im_ne_zero χ T)
    (fun t => M t + 7 / 8 + B t) ((hMc.add continuousAt_const).add hB)
    (by filter_upwards [hb] with t ht; simp only [hM]; linarith)
  have hmain : bookMain 1 T = M T := by simp [bookMain, hM]
  have herr : bookError 1 T = 0.15 * Real.log T + 3.389 := by simp [bookError]
  rw [hmain, herr]
  linarith

/-! ### Arithmetic. Proved. -/

/-- `log T ≤ 24` for `T ≤ 10 ^ 10`. -/
lemma log_le_24_of_le {T : ℝ} (hT : 0 < T) (hT' : T ≤ 10 ^ 10) : Real.log T ≤ 24 := by
  have he : (10 : ℝ) ^ 10 ≤ Real.exp 24 := by
    have h1 : Real.exp 24 = Real.exp 1 ^ 24 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 : (2.7182818283 : ℝ) ^ 24 ≤ Real.exp 1 ^ 24 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 24
    exact le_trans (by norm_num) h2
  calc Real.log T ≤ Real.log (Real.exp 24) := Real.log_le_log hT (hT'.trans he)
    _ = 24 := Real.log_exp 24

/-- `23 ≤ log T` for `10 ^ 10 ≤ T`. -/
lemma le_log_of_ge_1e10 {T : ℝ} (hT : 10 ^ 10 ≤ T) : 23 ≤ Real.log T := by
  have he : Real.exp 23 ≤ 10 ^ 10 := by
    have h1 : Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    have h2 : Real.exp 1 ^ 23 ≤ (2.7182818286 : ℝ) ^ 23 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 23
    exact h2.trans (by norm_num)
  calc (23 : ℝ) = Real.log (Real.exp 23) := (Real.log_exp 23).symm
    _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 23) (he.trans hT)

/-- `log 23 ≤ 3.14`. -/
lemma log_23_le : Real.log 23 ≤ 3.14 := by
  have he : (23 : ℝ) ≤ Real.exp 3.14 := by
    have h1 : Real.exp 3.14 = Real.exp 1 ^ 3 * Real.exp 0.14 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [h1]
    have h2 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3
    have h3 : 1 + 0.14 + (0.14 : ℝ) ^ 2 / 2 ≤ Real.exp 0.14 :=
      Real.quadratic_le_exp_of_nonneg (by norm_num)
    have h4 : (0 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    calc (23 : ℝ) ≤ 2.7182818283 ^ 3 * (1 + 0.14 + (0.14 : ℝ) ^ 2 / 2) := by norm_num
      _ ≤ Real.exp 1 ^ 3 * Real.exp 0.14 :=
        mul_le_mul h2 h3 (by norm_num) (by positivity)
  calc Real.log 23 ≤ Real.log (Real.exp 3.14) := Real.log_le_log (by norm_num) he
    _ = 3.14 := Real.log_exp _

/-- The budget of display 1.2: `7/8 + 2.31366 + 0.2 / T ≤ 0.15 log T + 3.389` for `T ≥ 1`. -/
lemma eq12_budget {T : ℝ} (hT : 1 ≤ T) :
    7 / 8 + (2.31366 + 0.2 / T) ≤ 0.15 * Real.log T + 3.389 := by
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have hd : 0.2 / T ≤ 0.2 := div_le_self (by norm_num) hT
  linarith

/-- The budget of Table 2 row `10 ^ 8`: `7/8 + 0.234 log T + 0.2 / T ≤ 0.15 log T + 3.389` for
`1 ≤ T ≤ 10 ^ 10`. -/
lemma table2_budget {T : ℝ} (hT : 1 ≤ T) (hT' : T ≤ 10 ^ 10) :
    7 / 8 + (0.234 * Real.log T + 0.2 / T) ≤ 0.15 * Real.log T + 3.389 := by
  have hl := log_le_24_of_le (by linarith) hT'
  have hd : 0.2 / T ≤ 0.2 := div_le_self (by norm_num) hT
  linarith

/-- The budget of Corollary 1: `7/8 + 0.112 log T + 0.278 log log T + 2.510 + 0.2 / T` is at
most `0.15 log T + 3.389` for `T ≥ 10 ^ 10`. It fails near `T = 10 ^ 9`, which is why the
lower subranges use display 1.2 and Table 2 instead. -/
lemma corollary1_budget {T : ℝ} (hT : 10 ^ 10 ≤ T) :
    7 / 8 + (0.112 * Real.log T + 0.278 * Real.log (Real.log T) + 2.510 + 0.2 / T) ≤
      0.15 * Real.log T + 3.389 := by
  have hL := le_log_of_ge_1e10 hT
  have hLL : Real.log (Real.log T) ≤ Real.log 23 + (Real.log T / 23 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log T / 23 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    linarith
  have h23 := log_23_le
  have hd : 0.2 / T ≤ 0.2 / 10 ^ 10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hT
  have hd' : (0.2 : ℝ) / 10 ^ 10 ≤ 0.001 := by norm_num
  nlinarith

/-! ### The low subrange -/

/-- Split of the low subrange `10 ^ 7 ≤ T ≤ 10 ^ 8`, from display 1.2 of Trudgian 2014. -/
theorem book_zero_count_large_height_upper_tall_level_one_middle_scale_low_split
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) {T : ℝ} (hT : 1 ≤ T)
    (hT6 : 10 ^ 6 ≤ T) (hq1 : q = 1) (hT7 : 10 ^ 7 ≤ T) (hT8 : T ≤ 10 ^ 8)
    (hmain : 2 * Real.pi * Real.exp 1 ≤ (q : ℝ) * T) :
    bookCount χ T - bookMain q T ≤ bookError q T := by
  subst hq1
  have hT0 : 0 < T := by linarith
  refine level_one_upper_of_bound χ hT (fun t => 2.31366 + 0.2 / t)
    (continuousAt_const.add (continuousAt_const.div continuousAt_id hT0.ne')) ?_ (eq12_budget hT)
  have hmem : Ioo T 5.45e8 ∈ 𝓝[>] T := Ioo_mem_nhdsGT (by norm_num at hT8 ⊢; linarith)
  filter_upwards [hmem] with t ht
  have h := (abs_le.mp (trudgian2014_eq12_count χ (hT.trans ht.1.le) ht.2.le)).2
  linarith

end LeanLab.HelfgottMajor.ZeroCount1623
