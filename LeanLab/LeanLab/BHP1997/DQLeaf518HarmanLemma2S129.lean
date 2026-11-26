/-
Burst 2026-11-22 S129 wave 13 pass two, BHP1997, a split of
`DQLeaf518HarmanMeanS129.leaf_harman_plancherel`, P0069 Baker Harman Pintz 1997, Lemma 29,
page 44, case `χ ≠ χ0`.

The factorization `(y+yz)^s - y^s = y^(1/2) y^(it) ((1+z)^s - 1)` and the bound `y ≤ 3Y` are
PROVED here; what is left is the new LEAF `leaf_harman_lemma2`, the multiplicative form of
[8] Harman 1982 Lemma 2 for a continuous function on `[-T, T]`, a finite range Plancherel
inequality. `leaf_harman_plancherel_split` has exactly the type of the parent leaf.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.DQLeaf518HarmanMeanS129

namespace LeanLab.BHP1997.DQLeaf518HarmanLemma2S129
open Classical Complex DecompC165b LowerShortC165 DQLeaf518HarmanMeanS129
open scoped BigOperators
open MeasureTheory

/-- For `y > 0`, `z ≥ 0`: `(y+yz)^s - y^s = y^(1/2) y^(it) (e^(s log(1+z)) - 1)`, P0069 page 44.
PROVED. -/
theorem diff_factor {y z t : ℝ} (hy : 0 < y) (hz : 0 ≤ z) :
    ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (y : ℂ) ^ (1 / 2 : ℂ) * (y : ℂ) ^ ((t : ℂ) * I) *
        (Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1) := by
  have h1 : (((y + y * z : ℝ)) : ℂ) = (y : ℂ) * ((1 + z : ℝ) : ℂ) := by push_cast; ring
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hz1 : ((1 + z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + z : ℝ) ≠ 0)
  rw [h1, Complex.mul_cpow_ofReal_nonneg hy.le (by linarith), Complex.cpow_add _ _ hy0,
    Complex.cpow_def_of_ne_zero hz1, Complex.ofReal_log (by linarith)]
  ring_nf

/-- `y ↦ ∫_{-T}^{T} H(t) y^(it) dt` is continuous on `[a, ∞)` for `a > 0`, `H` continuous.
PROVED. -/
theorem mellin_contOn (H : ℝ → ℂ) (hH : Continuous H) (T a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun y : ℝ => ∫ t in (-T)..T, H t * (y : ℂ) ^ ((t : ℂ) * I)) (Set.Ici a) := by
  have hF : Continuous (Function.uncurry fun (y : ℝ) (t : ℝ) =>
      H t * ((max y a : ℝ) : ℂ) ^ ((t : ℂ) * I)) := by
    show Continuous fun p : ℝ × ℝ => H p.2 * ((max p.1 a : ℝ) : ℂ) ^ ((p.2 : ℂ) * I)
    refine (hH.comp continuous_snd).mul (Continuous.cpow (by fun_prop) (by fun_prop) ?_)
    intro p
    exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le ha (le_max_right _ _))
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := -T) (μ := volume) hF (continuous_const (y := T))
  refine hcont.continuousOn.congr (fun y hy => ?_)
  have : max y a = y := max_eq_left hy
  simp only [this]
/-- LEAF: page 44, display after 5.4, class HARD, CITED [8] Harman 1982 Lemma 2 p. 339 in
the variant used by P0069 Baker Harman Pintz 1997: for `H` continuous on `[-T, T]` and `A > 0`,
`∫_{A/2}^{3A} |∫_{-T}^{T} H(t) y^(it) dt|^2 dy ≪ A ∫_{-T}^{T} |H(t)|^2 dt`. After `y = e^v`,
`dy ≤ 3A dv`, it is the full line Plancherel theorem restricted to a finite `v` range, so
`K = 6π` works. -/
theorem leaf_harman_lemma2 : ∃ K : ℝ, 0 ≤ K ∧ ∀ H : ℝ → ℂ, Continuous H → ∀ T A : ℝ, 0 < T → 0 < A →
    ∫ y in (A / 2)..(3 * A), ‖∫ t in (-T)..T, H t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 ≤
      K * A * ∫ t in (-T)..T, ‖H t‖ ^ 2 := by
  sorry

/-- P0069 page 44, PROVED from `leaf_harman_lemma2` and `diff_factor`: exactly the statement
of `DQLeaf518HarmanMeanS129.leaf_harman_plancherel`, constant `3 K`. -/
theorem leaf_harman_plancherel_split (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
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
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 *
                  (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
                    ‖(1 / 2 + t * I : ℂ)‖ ^ 2)) := by
  obtain ⟨K, hK, hL⟩ := leaf_harman_lemma2
  refine ⟨3 * K, by positivity, 1, ?_⟩
  intro x hx q hq1 hqQ z hz1 hz2 χ hχ
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hz : 0 ≤ z := le_trans (by positivity) hz1
  set Y := x ^ (11 / 20 + ε) with hYdef
  set G : ℝ → ℂ := fun t => ∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) with hGdef
  have hs0 : ∀ t : ℝ, (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  have hG : Continuous G := by
    refine continuous_finsetSum _ (fun m hm => ?_)
    have hm0 : (m : ℂ) ≠ 0 := by
      simp only [rightInterval, Finset.mem_Ioc] at hm
      exact_mod_cast (by omega : m ≠ 0)
    refine continuous_const.div ((by fun_prop : Continuous fun t : ℝ =>
      (1 / 2 : ℂ) + (t : ℂ) * I).const_cpow (Or.inl hm0)) ?_
    intro t
    exact Complex.cpow_ne_zero_iff.2 (Or.inl hm0)
  set Hf : ℝ → ℂ := fun t => G t * ((Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1) /
      ((1 / 2 : ℂ) + (t : ℂ) * I)) with hHf
  have hHc : Continuous Hf :=
    hG.mul (Continuous.div (by fun_prop) (by fun_prop) hs0)
  have hLx := hL Hf hHc Y Y hY hY
  have hnorm : ∀ t : ℝ, ‖Hf t‖ ^ 2 = ‖G t‖ ^ 2 *
      (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2) := by
    intro t; simp only [hHf, norm_mul, norm_div, mul_pow, div_pow]
  have hRint : (∫ t in (-Y)..Y, ‖Hf t‖ ^ 2) = ∫ t in (-Y)..Y, ‖G t‖ ^ 2 *
      (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2) :=
    intervalIntegral.integral_congr (fun t _ => hnorm t)
  rw [← hRint]
  have hab : Y / 2 ≤ 3 * Y := by linarith
  have hpt : ∀ y : ℝ, Y / 2 ≤ y → y ≤ 3 * Y →
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-Y)..Y, G t *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
        3 * Y * ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 := by
    intro y hy1 hy2
    have hy : 0 < y := by linarith
    have heq : (∫ t in (-Y)..Y, G t *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) =
        (y : ℂ) ^ (1 / 2 : ℂ) * ∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only [hHf]
      rw [diff_factor (t := t) hy hz]
      field_simp
    rw [heq, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [hre]
    have hsq : (y ^ (1 / 2 : ℝ)) ^ 2 = y := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hy.le]
    have hc : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
    have hc0 : 0 ≤ ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ := norm_nonneg _
    have hI0 : 0 ≤ ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 := by positivity
    rw [mul_pow, mul_pow, hsq]
    have hc2 : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ^ 2 ≤ 1 := by nlinarith
    calc ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ^ 2 * (y *
          ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2) ≤ 1 * (y *
          ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ ≤ 3 * Y * ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 := by nlinarith
  have hRc : ContinuousOn (fun y : ℝ => 3 * Y * ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2)
      (Set.uIcc (Y / 2) (3 * Y)) := by
    rw [Set.uIcc_of_le hab]
    have h1 := ((mellin_contOn Hf hHc Y (Y / 2) (by positivity)).mono
      (show Set.Icc (Y / 2) (3 * Y) ⊆ Set.Ici (Y / 2) from fun y hy => hy.1)).norm
    exact continuousOn_const.mul (h1.pow 2)
  have hIn : 0 ≤ ∫ y in (Y / 2)..(3 * Y), ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun y _ => by positivity)
  have hRn : 0 ≤ ∫ t in (-Y)..Y, ‖Hf t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => by positivity)
  have hstep : (∫ y in (Y / 2)..(3 * Y),
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-Y)..Y, G t *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2) ≤
      3 * Y * ∫ y in (Y / 2)..(3 * Y), ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    by_cases hi : IntervalIntegrable (fun y : ℝ => ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-Y)..Y, G t *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2)
          volume (Y / 2) (3 * Y)
    · exact intervalIntegral.integral_mono_on hab hi (hRc.intervalIntegrable)
        (fun y hy => hpt y hy.1 hy.2)
    · rw [intervalIntegral.integral_undef hi]
      exact intervalIntegral.integral_nonneg hab (fun y _ => by positivity)
  calc _ ≤ 3 * Y * ∫ y in (Y / 2)..(3 * Y), ‖∫ t in (-Y)..Y, Hf t * (y : ℂ) ^ ((t : ℂ) * I)‖ ^ 2 :=
        hstep
    _ ≤ 3 * Y * (K * Y * ∫ t in (-Y)..Y, ‖Hf t‖ ^ 2) := mul_le_mul_of_nonneg_left hLx (by positivity)
    _ = 3 * K * Y ^ 2 * ∫ t in (-Y)..Y, ‖Hf t‖ ^ 2 := by ring

/-- The split has exactly the type of the parent leaf. -/
theorem leaf_harman_plancherel_split_twin :
    type_of% @LeanLab.BHP1997.DQLeaf518HarmanMeanS129.leaf_harman_plancherel :=
  @leaf_harman_plancherel_split

end LeanLab.BHP1997.DQLeaf518HarmanLemma2S129
