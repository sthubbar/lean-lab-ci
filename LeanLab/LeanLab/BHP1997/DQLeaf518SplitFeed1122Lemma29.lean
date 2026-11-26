/-
Burst 2026-11-22 S82 feed1122, BHP1997, a finer split of `Prep1121LowExc.leaf_char_nonprincipal`,
the open per character step of `DQLeaf518Split.leaf_lemma29`, P0069 Baker Harman Pintz 1997,
Lemma 29 on page 43, proof on pages 43 and 44, case `χ ∈ F = E_q^c \ {χ0}`.

`DQLeaf518Split.leaf_lemma29` is already PROVED from leaves as
`Prep1121LowExc.leaf_lemma29_split`; that file imports `DQLeaf518Split`, so the original file
cannot import it without a cycle and keeps its sorry. This file separates the two cited
inputs of the per character leaf:
* `leaf_perron_window`, HARD, CITED [30] Lemma 3.19: the window sum is the Perron integral at
  height `Y` up to `O(Y^(1/100))`, integrated over `y`;
* `leaf_harman_mean`, HARD, CITED variant of [8] Lemma 2 with the kernel bound: the mean square
  of the Perron integral;
* `leaf_window_integrable`, MEDIUM, tacit in the paper: the two integrands are interval
  integrable in `y`.
`sq_norm_integral_le` is PROVED, and `leaf_char_nonprincipal_of_leaves` has exactly the type of
`Prep1121LowExc.leaf_char_nonprincipal` and is PROVED from the three leaves.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.Prep1121LowExcLemma29

namespace LeanLab.BHP1997.DQLeaf518SplitFeed1122
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43, first step of the proof of Lemma 29, class HARD, CITED [30] Lemma 3.19,
Titchmarsh 1986 book p. 70. P0069 Baker Harman Pintz 1997: for `χ ≠ χ0` the window sum
`Σ_{m ∈ J_y} b(m) χ(m)` equals `(1/2πi) ∫_{1/2-iY}^{1/2+iY} G(s, χ) ((y+yz)^s - y^s)/s ds
+ O(Y^ε)`, here with `ε = 1/100`, so the mean square over `y ∈ [Y/2, 3Y]` of the difference is
at most a constant times `Y^(1+1/50)`. Here `δχ = 0`. -/
theorem leaf_perron_window (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) - (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  sorry

/-- LEAF: page 44, display after 5.4, class HARD, CITED variant of [8] Lemma 2, Harman 1982
p. 339, with the kernel bound `lemma29_ineq_six`. P0069 Baker Harman Pintz 1997: the mean
square over `y ∈ [Y/2, 3Y]` of the Perron integral is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, with `T2 = Y / qQ`; the form without
the factor `L` follows by Plancherel after `y = e^v`, see NOTE U-1744 in `DQLeaf518Split`. -/
theorem leaf_harman_mean (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
  sorry

/-- S129: the truncated Perron integral is continuous in `y` on `[a, ∞)` for `a > 0`, `z ≥ 0`. PROVED. -/
theorem perron_contOn (S : Finset ℕ) (hS : ∀ m ∈ S, 1 ≤ m) (c : ℕ → ℂ) (T z a : ℝ)
    (hz : 0 ≤ z) (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T,
      (∑ m ∈ S, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
        ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
          (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))) (Set.Ici a) := by
  have hs : Continuous fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I := by fun_prop
  have hs0 : ∀ t : ℝ, (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  have hG : Continuous fun t : ℝ => ∑ m ∈ S, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    refine continuous_finsetSum _ (fun m hm => ?_)
    have hm0 : (m : ℂ) ≠ 0 := by
      have := hS m hm
      exact_mod_cast (by omega : m ≠ 0)
    refine continuous_const.div (hs.const_cpow (Or.inl hm0)) ?_
    intro t
    exact Complex.cpow_ne_zero_iff.2 (Or.inl hm0)
  have hslit : ∀ u : ℝ, 0 < u → ((u : ℂ)) ∈ Complex.slitPlane := by
    intro u hu; exact Complex.ofReal_mem_slitPlane.2 hu
  have hF : Continuous (Function.uncurry fun (y : ℝ) (t : ℝ) =>
      (∑ m ∈ S, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
        ((((max y a + max y a * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
          ((max y a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    show Continuous fun p : ℝ × ℝ =>
      (∑ m ∈ S, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (p.2 : ℂ) * I)) *
        ((((max p.1 a + max p.1 a * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (p.2 : ℂ) * I) -
          ((max p.1 a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (p.2 : ℂ) * I)) / ((1 / 2 : ℂ) + (p.2 : ℂ) * I)
    have hmax : Continuous fun p : ℝ × ℝ => max p.1 a := by fun_prop
    have hpos : ∀ p : ℝ × ℝ, 0 < max p.1 a := fun p => lt_of_lt_of_le ha (le_max_right _ _)
    refine Continuous.div ((hG.comp continuous_snd).mul (Continuous.sub ?_ ?_))
      (hs.comp continuous_snd) (fun p => hs0 _)
    · refine Continuous.cpow (by fun_prop) (hs.comp continuous_snd) (fun p => hslit _ ?_)
      have := hpos p; positivity
    · exact Continuous.cpow (by fun_prop) (hs.comp continuous_snd) (fun p => hslit _ (hpos p))
  have hcont := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := -T) (μ := volume) hF (continuous_const (y := T))).const_smul (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  refine hcont.continuousOn.congr (fun y hy => ?_)
  have : max y a = y := max_eq_left hy
  simp only [Pi.smul_apply, smul_eq_mul, this]

/-- S129: the window sum is measurable in `y`, a finite sum of indicators of closed sets. PROVED. -/
theorem window_measurable (S : Finset ℕ) (d : ℕ → ℂ) (z : ℝ) :
    Measurable (fun y : ℝ => ∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d m) := by
  have : (fun y : ℝ => ∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d m) =
      fun y => ∑ m ∈ S, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then d m else 0 := by
    funext y; rw [Finset.sum_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun m _ => Measurable.ite ?_ measurable_const measurable_const)
  exact (measurableSet_le measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_id.add (measurable_id.mul_const z)))

/-- S129: the window sum is bounded by the full sum of norms. PROVED. -/
theorem window_bound (S : Finset ℕ) (d : ℕ → ℂ) (z y : ℝ) :
    ‖∑ m ∈ S.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), d m‖ ≤ ∑ m ∈ S, ‖d m‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => norm_nonneg _))

/-- S129: `‖W - g‖^2` is interval integrable for `W` measurable bounded, `g` continuous. PROVED. -/
theorem sq_norm_intInt {W g : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hW : Measurable W)
    (hWb : ∀ y, ‖W y‖ ≤ M) (hg : ContinuousOn g (Set.Icc a b)) :
    IntervalIntegrable (fun y => ‖W y - g y‖ ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hm : AEStronglyMeasurable (fun y => W y - g y) (volume.restrict (Set.Icc a b)) :=
    hW.aestronglyMeasurable.sub (hg.aestronglyMeasurable measurableSet_Icc)
  refine Integrable.of_bound ?_ ((M + Mg) ^ 2) ?_
  · exact (continuous_pow 2).comp_aestronglyMeasurable hm.norm
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun y hy => ?_)
    have h1 : ‖W y - g y‖ ≤ M + Mg := (norm_sub_le _ _).trans (add_le_add (hWb y) (hMg y hy))
    have h0 : 0 ≤ ‖W y - g y‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
/-- LEAF: page 43 to 44, tacit in the paper, class MEDIUM. P0069 Baker Harman Pintz 1997:
the squared Perron error and the squared Perron integral are interval integrable in `y` on
`[Y/2, 3Y]`; the window sum is piecewise constant in `y` and the Perron integral is continuous
in `y > 0`. PROVED in burst S129 wave 13 from the helper lemmas above. -/
theorem leaf_window_integrable (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          IntervalIntegrable (fun y : ℝ => ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) - (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2)
            MeasureTheory.volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
          IntervalIntegrable (fun y : ℝ => ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2)
            MeasureTheory.volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
  refine ⟨1, fun x hx q hq1 hqQ z hz1 hz2 χ hχ => ?_⟩
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hz : 0 ≤ z := le_trans (by positivity) hz1
  have ha : 0 < x ^ (11 / 20 + ε) / 2 := by positivity
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
  have hS : ∀ m ∈ rightInterval ε x, 1 ≤ m := by
    intro m hm
    simp only [rightInterval, Finset.mem_Ioc] at hm
    omega
  have hg := (perron_contOn (rightInterval ε x) hS (fun m => (b x m : ℂ) * χ (m : ZMod q))
    (x ^ (11 / 20 + ε)) z (x ^ (11 / 20 + ε) / 2) hz ha).mono
    (show Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ⊆ Set.Ici (x ^ (11 / 20 + ε) / 2)
      from fun y hy => hy.1)
  have hW := window_measurable (rightInterval ε x) (fun m => (b x m : ℂ) * χ (m : ZMod q)) z
  have hWb := window_bound (rightInterval ε x) (fun m => (b x m : ℂ) * χ (m : ZMod q)) z
  simp only [hd, zero_mul, sub_zero]
  refine ⟨sq_norm_intInt hab hW hWb hg, ?_⟩
  simpa using sq_norm_intInt (W := fun _ => (0 : ℂ)) (M := 0) hab measurable_const
    (fun _ => by simp) hg

/-- `∫ ‖f‖^2 ≤ 2 ∫ ‖f - g‖^2 + 2 ∫ ‖g‖^2` on an interval. PROVED. -/
theorem sq_norm_integral_le {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (h1 : IntervalIntegrable (fun y => ‖f y - g y‖ ^ 2) volume a b)
    (h2 : IntervalIntegrable (fun y => ‖g y‖ ^ 2) volume a b) :
    ∫ y in a..b, ‖f y‖ ^ 2 ≤
      2 * (∫ y in a..b, ‖f y - g y‖ ^ 2) + 2 * ∫ y in a..b, ‖g y‖ ^ 2 := by
  have hn1 : 0 ≤ ∫ y in a..b, ‖f y - g y‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun y _ => by positivity)
  have hn2 : 0 ≤ ∫ y in a..b, ‖g y‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun y _ => by positivity)
  by_cases hf : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume a b
  · rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (h1.const_mul 2) (h2.const_mul 2)]
    refine intervalIntegral.integral_mono_on hab hf
      ((h1.const_mul 2).add (h2.const_mul 2)) ?_
    intro y _
    have htri : ‖f y‖ ≤ ‖f y - g y‖ + ‖g y‖ := by
      calc ‖f y‖ = ‖(f y - g y) + g y‖ := by rw [sub_add_cancel]
        _ ≤ ‖f y - g y‖ + ‖g y‖ := norm_add_le _ _
    have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖f y - g y‖ - ‖g y‖), norm_nonneg (f y - g y), norm_nonneg (g y)]
  · rw [intervalIntegral.integral_undef hf]
    linarith

/-- P0069 page 43 to 44, PROVED from the three LEAFs above: exactly the statement of
`Prep1121LowExc.leaf_char_nonprincipal`. -/
theorem leaf_char_nonprincipal_of_leaves (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
                ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
                  (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                      (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ)  := by
  obtain ⟨K1, hK1, C1, hC1⟩ := leaf_perron_window b hε hb
  obtain ⟨K2, hK2, C2, hC2⟩ := leaf_harman_mean b hε hb
  obtain ⟨C3, hC3⟩ := leaf_window_integrable b hε hb
  refine ⟨2 * (K1 + K2), by positivity, max (max C1 C2) (max C3 1), ?_⟩
  intro x hx q hq1 hqQ z hz1 hz2 χ hχ
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : (1 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  obtain ⟨hi1, hi2⟩ := hC3 x hx3 q hq1 hqQ z hz1 hz2 χ hχ
  have e1 := hC1 x hx1 q hq1 hqQ z hz1 hz2 χ hχ
  have e2 := hC2 x hx2 q hq1 hqQ z hz1 hz2 χ hχ
  refine (sq_norm_integral_le hab hi1 hi2).trans ?_
  have hG : 0 ≤ ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hE : 0 ≤ x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by positivity
  have hYG : 0 ≤ (x ^ (11 / 20 + ε)) ^ 2 * ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by positivity
  nlinarith [mul_nonneg hK1 hYG, mul_nonneg hK2 hE]

end LeanLab.BHP1997.DQLeaf518SplitFeed1122
