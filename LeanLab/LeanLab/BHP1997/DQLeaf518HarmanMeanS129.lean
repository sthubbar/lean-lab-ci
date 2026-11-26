/-
Burst 2026-11-22 S129 wave 13 pass two, BHP1997, a split of
`DQLeaf518SplitFeed1122.leaf_harman_mean`, P0069 Baker Harman Pintz 1997, Lemma 29, page 44,
the mean square of the truncated Perron integral, case `χ ≠ χ0`.

The paper bounds the mean square by a variant of [8] Harman 1982 Lemma 2, then inserts the kernel
bound `|((1+z)^s - 1)/s|^2 ≪ 1/(T2^2 + t^2)`. This file isolates the first step as the new LEAF
`leaf_harman_plancherel`, with the exact kernel `|e^(s log(1+z)) - 1|^2/|s|^2` still inside the
`t` integral, and PROVES `leaf_harman_mean_split`, with exactly the type of the parent leaf, from it
and the PROVED kernel bound `DQLeaf518Split.lemma29_ineq_six`.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.DQLeaf518SplitFeed1122Lemma29

namespace LeanLab.BHP1997.DQLeaf518HarmanMeanS129
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 44, the display after 5.4 before the kernel bound, class HARD, CITED variant of
[8] Harman 1982 Lemma 2 p. 339. P0069 Baker Harman Pintz 1997: for `y > 0` one has
`(y+yz)^s - y^s = y^(1/2) y^(it) ((1+z)^s - 1)`, and after `y = e^v`, `dy ≤ 3Y dv`, a finite range
Plancherel inequality in `v` over `[log(Y/2), log 3Y]` gives that the mean square over
`y ∈ [Y/2, 3Y]` of the Perron integral is `≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 |((1+z)^s - 1)/s|^2 dt`,
with `(1+z)^s = e^(s log(1+z))`. -/
theorem leaf_harman_plancherel (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
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
  sorry

/-- Page 3, the definition of Q: `Q ≤ Y^(1/16)` when `Y ≥ 1`. Same proof as
`DecompC165b.sieveQ_le_sixteenth_power`, outside this file's import closure. PROVED. -/
theorem sieveQ_le_sixteenth518 {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
    (sieveQ ε x : ℝ) ≤ (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) := by
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := by linarith
  unfold sieveQ
  calc
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2 :=
      Nat.floor_le (by positivity)
    _ ≤ ((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) :=
      div_le_self (by positivity) (by norm_num)
    _ = (x ^ (11 / 20 + ε)) ^ ((1 / 16 : ℝ) - 1 / 10 ^ 5) := by
      rw [← Real.rpow_mul hY0]
      congr 1
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)

/-- For `x ≥ 65536` the window parameter satisfies `6 q Q ≤ Y`, so `z ≤ 1` in the range of
1.9. PROVED. -/
theorem six_qQ_le_Y {ε x : ℝ} (hε : 0 < ε) (hx : 65536 ≤ x) {q : ℕ} (hqQ : q ≤ sieveQ ε x) :
    6 * (q : ℝ) * sieveQ ε x ≤ x ^ (11 / 20 + ε) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hYge : x ^ (1 / 2 : ℝ) ≤ x ^ (11 / 20 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : (256 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY : (256 : ℝ) ≤ Y := le_trans hsq hYge
  have hY0 : 0 ≤ Y := by linarith
  have hQ := sieveQ_le_sixteenth518 (ε := ε) (x := x) (by linarith)
  set u := Y ^ (1 / 16 : ℝ) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hY0 _
  have hu16 : u ^ 16 = Y := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
  have hu2 : 2 ≤ u ^ 2 := by
    by_contra h
    rw [not_le] at h
    have : (u ^ 2) ^ 8 < 2 ^ 8 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    rw [← pow_mul] at this
    norm_num at this
    linarith
  have hq : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hqQ2 : (q : ℝ) * sieveQ ε x ≤ u ^ 2 := by
    calc (q : ℝ) * sieveQ ε x ≤ (sieveQ ε x : ℝ) * sieveQ ε x :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ ≤ u * u := mul_le_mul hQ hQ (by positivity) hu0
      _ = u ^ 2 := by ring
  have h8 : 6 * u ^ 2 ≤ u ^ 16 := by
    have hv : 2 ≤ u ^ 2 := hu2
    have : u ^ 16 = u ^ 2 * (u ^ 2) ^ 7 := by ring
    rw [this]
    have h7 : (2 : ℝ) ^ 7 ≤ (u ^ 2) ^ 7 := pow_le_pow_left₀ (by norm_num) hv 7
    nlinarith
  nlinarith

/-- P0069 page 44, PROVED from `leaf_harman_plancherel` and the PROVED kernel bound
`DQLeaf518Split.lemma29_ineq_six`: exactly the statement of
`DQLeaf518SplitFeed1122.leaf_harman_mean`, with constant `324 K`. -/
theorem leaf_harman_mean_split (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
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
  obtain ⟨K, hK, C, hC⟩ := leaf_harman_plancherel b hε hb
  refine ⟨324 * K, by positivity, max C 65536, ?_⟩
  intro x hx q hq1 hqQ z hz1 hz2 χ hχ
  have hxC : C ≤ x := le_trans (le_max_left _ _) hx
  have hx6 : (65536 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hQ1 : (1 : ℝ) ≤ sieveQ ε x := by exact_mod_cast le_trans hq1 hqQ
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hz : 0 ≤ z := le_trans (by positivity) hz1
  have h6 := six_qQ_le_Y hε hx6 hqQ
  have hzle1 : z ≤ 1 := by
    refine hz2.trans ?_
    rw [div_le_one hY]; linarith
  set T := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT
  have hTpos : 0 < T := by positivity
  have hzT : z ≤ 6 / T := by
    refine hz2.trans (le_of_eq ?_)
    rw [hT]; field_simp
  refine (hC x hxC q hq1 hqQ z hz1 hz2 χ hχ).trans ?_
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
  have hn0 : ∀ t : ℝ, ‖(1 / 2 + t * I : ℂ)‖ ^ 2 ≠ 0 := fun t => by
    have := hs0 t
    positivity
  have hk : Continuous fun t : ℝ =>
      ‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2 :=
    Continuous.div (by fun_prop) (by fun_prop) hn0
  have hden : ∀ t : ℝ, 0 < T ^ 2 + t ^ 2 := fun t => by positivity
  have hr : Continuous fun t : ℝ => ‖G t‖ ^ 2 / (T ^ 2 + t ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun t => (hden t).ne')
  have hl : Continuous fun t : ℝ => ‖G t‖ ^ 2 *
      (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2) := (by fun_prop : Continuous fun t => ‖G t‖ ^ 2).mul hk
  have hYab : -x ^ (11 / 20 + ε) ≤ x ^ (11 / 20 + ε) := by linarith
  have hmono : (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)), ‖G t‖ ^ 2 *
      (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2)) ≤
      324 * ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)), ‖G t‖ ^ 2 / (T ^ 2 + t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hYab (hl.intervalIntegrable _ _)
      ((hr.const_mul 324).intervalIntegrable _ _) (fun t _ => ?_)
    have hker := LeanLab.BHP1997.DQLeaf518Split.lemma29_ineq_six (t := t) hz hzle1 hTpos hzT
    have hGn : 0 ≤ ‖G t‖ ^ 2 := by positivity
    calc ‖G t‖ ^ 2 * (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
          ‖(1 / 2 + t * I : ℂ)‖ ^ 2) ≤ ‖G t‖ ^ 2 * (324 / (T ^ 2 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left hker hGn
      _ = 324 * (‖G t‖ ^ 2 / (T ^ 2 + t ^ 2)) := by ring
  have hY2 : 0 ≤ K * (x ^ (11 / 20 + ε)) ^ 2 := by positivity
  calc K * (x ^ (11 / 20 + ε)) ^ 2 * (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
        ‖G t‖ ^ 2 * (‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
          ‖(1 / 2 + t * I : ℂ)‖ ^ 2))
      ≤ K * (x ^ (11 / 20 + ε)) ^ 2 *
          (324 * ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)), ‖G t‖ ^ 2 / (T ^ 2 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono hY2
    _ = 324 * K * (x ^ (11 / 20 + ε)) ^ 2 *
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)), ‖G t‖ ^ 2 / (T ^ 2 + t ^ 2) := by ring

/-- The split has exactly the type of the parent leaf. -/
theorem leaf_harman_mean_split_twin :
    type_of% @LeanLab.BHP1997.DQLeaf518SplitFeed1122.leaf_harman_mean :=
  @leaf_harman_mean_split

end LeanLab.BHP1997.DQLeaf518HarmanMeanS129
