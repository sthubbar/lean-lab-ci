/-
Route burst burst-20261122, session S64, BHP1997, route step
`LowerShortC165.lower_exceptional_mean_square`, next open LEAF `Prep1121LowExc.leaf_char_nonprincipal`.

P0069 Baker Harman Pintz 1997, proof of Lemma 29 on pages 43 and 44, the case
`χ ∈ F = E_q^c \ {χ0}`. The paper's proof has two cited steps, which become two LEAFs here:
* `leaf_perron_window`: page 43 to 44, "by [29] Lemma 3.19" the window sum equals the Perron
  integral at height `Y` plus `O(Y^ε)`, pointwise in `y`; CITED Titchmarsh Lemma 3.19;
* `leaf_mellin_mean_value`: page 44, "By a variant of [8], Lemma 2", for any continuous
  `g`; CITED Gallagher [8] Lemma 2.
`leaf_perron_mean_square` is PROVED from `leaf_mellin_mean_value` and the proved kernel bound
`DQLeaf518Split.lemma29_ineq_six`: the mean square over `y` of the Perron integral is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, the first step of the display after 5.4.
`leaf_char_nonprincipal_of_leaves` is PROVED from the two leaves, with exactly the statement
of `Prep1121LowExc.leaf_char_nonprincipal`, checked by `leaf_char_nonprincipal_split_twin`.
The step that joins them, `|a|^2 ≤ 2|a-b|^2 + 2|b|^2` integrated over `[Y/2, 3Y]`, is the
tacit triangle step of page 44.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.
-/
import LeanLab.BHP1997.Prep1121LowExcLemma29
import LeanLab.BHP1997.MellinCore

namespace LeanLab.BHP1997.S64LowExcCharNP
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 43 to 44, proof of Lemma 29, the truncated Perron formula, class HARD.
P0069 Baker Harman Pintz 1997, "by [29] Lemma 3.19": for `y` in `[Y/2, 3Y]` the window sum
`Σ_{m ∈ J, y ≤ m ≤ y + yz} b(m) χ(m)` equals
`(1/2πi) ∫_{1/2-iY}^{1/2+iY} G(s, χ) ((y+yz)^s - y^s)/s ds + O(Y^ε)`, with `G` the Dirichlet
polynomial of `b χ` over J. Written with `s = 1/2 + it`, `ds = i dt`. The error `O(Y^ε)` is
taken with `ε = 1/100`; it holds since `|b(m)| ≪ d(m)^B` by 3.1, so every coefficient is
`O(Y^(1/200))`, and the Perron error of Titchmarsh Lemma 3.19 at height `Y` is
`≪ max |b(m)| log Y`. CITED [29] Lemma 3.19. -/
theorem leaf_perron_window (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y →
          y ≤ 3 * x ^ (11 / 20 + ε) →
          ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (b x m : ℂ) * χ (m : ZMod q)) -
            ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
            K * (x ^ (11 / 20 + ε)) ^ (1 / 100 : ℝ) := by
  sorry

/-- LEAF: page 44, proof of Lemma 29, the variant of [8] Lemma 2, class HARD. P0069 Baker
Harman Pintz 1997, "By a variant of [8], Lemma 2,
`∫_{Y/2}^{3Y} |∫_T^{T'} g(t) y^(it) dt|^2 dy ≪ Y L ∫_T^{T'} |g(t)|^2 dt` whenever `g` is
continuous". Here with the factor `y^(1/2)` of `y^s`, `s = 1/2 + it`, kept inside, so the
bound is `Y^2` instead of `Y`, since `|y^(1/2)|^2 ≤ 3Y`, and with the `t` range `[-T, T]` in
which the paper applies it. The printed variant has a factor `L`; this leaf takes the form
without `L`, which the lab statement of `leaf_char_nonprincipal` needs and which holds by
Plancherel after `y = e^u`, with an absolute constant: QUESTION 1 of the note. CITED [8]
Lemma 2, Gallagher 1970. -/
theorem leaf_mellin_mean_value :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ T : ℝ, 0 ≤ T → ∀ g : ℝ → ℂ, Continuous g →
      ∫ y in (Y / 2)..(3 * Y),
          ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        K * Y ^ 2 * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
  exact MellinCore.leaf_mellin_mean_value_of_leaves

/-- Page 3, the definition of Q: `Q ≤ Y^(1/16)` when `Y ≥ 1`. -/
theorem sieveQ_le_sixteenth {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
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

/-- For `Y ≥ 6^16`, `6 Y^(1/8) ≤ Y`. -/
theorem six_mul_eighth_le {Y : ℝ} (hY : (6 : ℝ) ^ 16 ≤ Y) :
    6 * Y ^ (1 / 8 : ℝ) ≤ Y := by
  have hY0 : 0 ≤ Y := le_trans (by positivity) hY
  have hY1 : 1 ≤ Y := le_trans (by norm_num) hY
  have e : (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ := by norm_num
  have h1 : (6 : ℝ) ≤ Y ^ (1 / 16 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hY (by norm_num : (0:ℝ) ≤ 1 / 16)
    rw [e, Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
    rw [e]; exact this
  have h2 : Y ^ (1 / 16 : ℝ) ≤ Y ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have h3 : Y = Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : 0 ≤ Y ^ (1 / 8 : ℝ) := Real.rpow_nonneg hY0 _
  calc 6 * Y ^ (1 / 8 : ℝ) ≤ Y ^ (7 / 8 : ℝ) * Y ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) h4
    _ = Y := h3.symm


/-- Page 44, proof of Lemma 29, the step "the left hand side of (5.3) is
`≪ Y^2 ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt`, where we used
`|((1+z)^(1/2+it) - 1)/(1/2+it)|^2 ≪ 1/(T2^2 + t^2)` in the first step", for one character.
PROVED from the LEAF `leaf_mellin_mean_value` and the kernel bound
`DQLeaf518Split.lemma29_ineq_six`: `(y+yz)^s - y^s = y^s ((1+z)^s - 1)`, and `z ≤ 1` for
large `x` since `qQ ≤ Q^2 ≤ Y^(1/8)`. -/
theorem leaf_perron_mean_square (b : ℝ → ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∀ χ : DirichletCharacter ℂ q,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
            K * (x ^ (11 / 20 + ε)) ^ 2 *
              (∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
                  ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
  obtain ⟨K, hK, hgen⟩ := leaf_mellin_mean_value
  set c : ℝ := ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨K * (c * 324), by positivity, max ((6 ^ 16 : ℝ) ^ ((11 / 20 + ε)⁻¹)) 1,
    fun x hx q hq hqQ z hz1 hz2 χ => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have ha : 0 < 11 / 20 + ε := by linarith
  have hY6 : (6 : ℝ) ^ 16 ≤ x ^ (11 / 20 + ε) := by
    have h := Real.rpow_le_rpow (by positivity) (le_trans (le_max_left _ _) hx) ha.le
    rwa [Real.rpow_inv_rpow (by positivity) ha.ne'] at h
  have hY : 0 < x ^ (11 / 20 + ε) := lt_of_lt_of_le (by positivity) hY6
  have hY1 : 1 ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY6
  have hQ := sieveQ_le_sixteenth hY1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQr : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hQ1 : (1 : ℝ) ≤ sieveQ ε x := hq1.trans hqQr
  have hqQ0 : 0 < (q : ℝ) * sieveQ ε x := by positivity
  have hT2 : 0 < x ^ (11 / 20 + ε) / (q * sieveQ ε x) := div_pos hY hqQ0
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
  have h16 : (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) * (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) =
      (x ^ (11 / 20 + ε)) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hY]; norm_num
  have h6qQ : 6 * q * (sieveQ ε x : ℝ) ≤ x ^ (11 / 20 + ε) := by
    have hQ0 : (0 : ℝ) ≤ sieveQ ε x := by positivity
    calc 6 * q * (sieveQ ε x : ℝ) ≤ 6 * ((x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ) *
          (x ^ (11 / 20 + ε)) ^ (1 / 16 : ℝ)) := by
          have := mul_le_mul (hqQr.trans hQ) hQ hQ0 (Real.rpow_nonneg hY.le _)
          nlinarith
      _ = 6 * (x ^ (11 / 20 + ε)) ^ (1 / 8 : ℝ) := by rw [h16]
      _ ≤ _ := six_mul_eighth_le hY6
  have hz1' : z ≤ 1 := hz2.trans ((div_le_one hY).2 h6qQ)
  have hzT : z ≤ 6 / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) := by
    rw [div_div_eq_mul_div]
    calc z ≤ _ := hz2
      _ = _ := by ring
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have h1zne : (((1 + z : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h1z.ne'
  -- the Dirichlet polynomial and the weight `g`
  have hs : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  have hG := DQLeaf518Split.dirichlet_poly_continuous (rightInterval ε x)
    (fun m => (b x m : ℂ) * χ (m : ZMod q))
  have hc1 : Continuous fun t : ℝ => (((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hs.const_cpow (Or.inl h1zne)
  have hgc : Continuous fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ((∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
        ((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
          ((1 / 2 : ℂ) + (t : ℂ) * I)) :=
    continuous_const.mul ((hG.mul (hc1.sub continuous_const)).div hs
      DQLeaf518Split.half_line_ne_zero)
  have hA := hgen (x ^ (11 / 20 + ε)) hY (x ^ (11 / 20 + ε)) hY.le _ hgc
  -- step A: rewrite the Perron integral
  have hEq : ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
                (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                    (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
                  ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                    (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
        ‖∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ((∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
              ((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
                ((1 / 2 : ℂ) + (t : ℂ) * I)) *
          (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le (by linarith)] at hy
      linarith [hy.1]
    rw [← intervalIntegral.integral_const_mul]
    congr 2
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hm : ((y + y * z : ℝ) : ℂ) = ((y : ℝ) : ℂ) * (((1 + z : ℝ)) : ℂ) := by
      push_cast; ring
    rw [hm, Complex.mul_cpow_ofReal_nonneg hy0 h1z.le]
    ring
  -- step C: the kernel bound
  have hk : ∀ t : ℝ, ‖(((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 /
      ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ^ 2 ≤
        324 / ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) := by
    intro t
    have h := DQLeaf518Split.lemma29_ineq_six (t := t) hz0 hz1' hT2 hzT
    rw [Complex.cpow_def_of_ne_zero h1zne, ← Complex.ofReal_log h1z.le,
      mul_comm (((Real.log (1 + z)) : ℝ) : ℂ)]
    exact h
  have hRc : Continuous fun t : ℝ =>
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
    (hG.norm.pow 2).div (by fun_prop) fun t => by positivity
  have hC : ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
        ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ((∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
            ((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
              ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2 ≤
      ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)), (c * 324) *
        (‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
    refine intervalIntegral.integral_mono_on (by linarith) ((hgc.norm.pow 2).intervalIntegrable _ _)
      ((continuous_const.mul hRc).intervalIntegrable _ _) fun t _ => ?_
    have hD : 0 < (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2 := by positivity
    rw [norm_mul, norm_div, norm_mul, mul_pow, div_pow, mul_pow, ← hc]
    have hG0 : 0 ≤ ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by positivity
    calc _ = c * ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          (‖(((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1‖ ^ 2 /
            ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ^ 2) := by ring
      _ ≤ c * ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 *
          (324 / ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (hk t) (mul_nonneg hc0 hG0)
      _ = _ := by ring
  rw [intervalIntegral.integral_const_mul] at hC
  rw [hEq]
  calc _ ≤ _ := hA
    _ ≤ K * (x ^ (11 / 20 + ε)) ^ 2 * ((c * 324) * ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
        ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := by
      gcongr
    _ = _ := by ring

/-- Page 44, the tacit triangle step: `|a|^2 ≤ 2 |b|^2 + 2 |a - b|^2`. -/
theorem norm_sq_le_two_mul (a c : ℂ) {E : ℝ} (h : ‖a - c‖ ≤ E) :
    ‖a‖ ^ 2 ≤ 2 * ‖c‖ ^ 2 + 2 * E ^ 2 := by
  have h1 : ‖a‖ ≤ ‖c‖ + ‖a - c‖ := by
    calc ‖a‖ = ‖c + (a - c)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have h0 : 0 ≤ ‖a - c‖ := norm_nonneg _
  have hc : 0 ≤ ‖c‖ := norm_nonneg _
  have h2 : ‖a‖ ≤ ‖c‖ + E := h1.trans (by linarith)
  have h3 : 0 ≤ ‖a‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖c‖ - E), mul_le_mul h2 h2 h3 (by linarith)]

/-- PROVED from the two LEAFs: exactly the statement of
`Prep1121LowExc.leaf_char_nonprincipal`, P0069 pages 43 and 44, the case `χ ∈ F`. Here
`δχ = 0`, the window sum is the Perron integral plus `O(Y^(1/100))` pointwise, and the square
of the error integrated over `[Y/2, 3Y]` is `(5Y/2) Y^(1/50)` times a constant. -/
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
            K * x ^ (11 / 20 + ε) * (x ^ (11 / 20 + ε)) ^ (1 / 50 : ℝ) := by
  obtain ⟨K1, hK1, C1, h1⟩ := leaf_perron_window b hε hb
  obtain ⟨K2, hK2, C2, h2⟩ := leaf_perron_mean_square b hε
  refine ⟨2 * K2 + 5 * K1 ^ 2, by positivity, max (max C1 C2) 1,
    fun x hx q hq hqQ z hz1 hz2 χ hχ => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hδ : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  -- integrability of the left integrand
  have hS := DQLeaf518Split.leaf_lemma29_integrable b ε x hx3 q χ z hz0
  simp only [hδ, zero_mul, sub_zero] at hS ⊢
  -- integrability of the Perron integral
  have hP := DQLeaf518Split.lemma29_integrable_aux (rightInterval ε x) (fun _ => 0)
    (fun m => (b x m : ℂ) * χ (m : ZMod q)) 1 (((2 * Real.pi : ℝ) : ℂ)⁻¹)
    (a := x ^ (11 / 20 + ε) / 2) (b := 3 * x ^ (11 / 20 + ε)) (T := x ^ (11 / 20 + ε))
    (z := z) (by linarith) hab hY.le hz0
  simp only [Finset.sum_const_zero, zero_sub, one_mul, norm_neg] at hP
  have hM := h2 x hx2 q hq hqQ z hz1 hz2 χ
  set Y := x ^ (11 / 20 + ε) with hYdef
  set E := K1 * Y ^ (1 / 100 : ℝ) with hE
  have hpt : ∀ y ∈ Set.Icc (Y / 2) (3 * Y),
      ‖∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), (b x m : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
        2 * ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-Y)..Y,
            (∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 +
          2 * E ^ 2 := fun y hy =>
    norm_sq_le_two_mul _ _ (h1 x hx1 q hq hqQ z hz1 hz2 χ y hy.1 hy.2)
  have hmono := intervalIntegral.integral_mono_on hab hS
    ((hP.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add (hP.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hI0 : 0 ≤ ∫ t in (-Y)..Y,
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        ((Y / (q * sieveQ ε x)) ^ 2 + t ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
  have hR2 : (Y ^ (1 / 100 : ℝ)) ^ 2 = Y ^ (1 / 50 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
    norm_num
  have hE2 : E ^ 2 = K1 ^ 2 * Y ^ (1 / 50 : ℝ) := by
    rw [hE, mul_pow, hR2]
  have hR0 : 0 ≤ Y ^ (1 / 50 : ℝ) := Real.rpow_nonneg hY.le _
  rw [hE2] at hmono
  have hY2 : 0 ≤ Y ^ 2 := sq_nonneg Y
  calc _ ≤ _ := hmono
    _ ≤ 2 * (K2 * Y ^ 2 * (∫ t in (-Y)..Y,
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((Y / (q * sieveQ ε x)) ^ 2 + t ^ 2))) +
        (3 * Y - Y / 2) * (2 * (K1 ^ 2 * Y ^ (1 / 50 : ℝ))) := by
      linarith [hM]
    _ ≤ _ := by
      have hK1s : 0 ≤ K1 ^ 2 := sq_nonneg K1
      have hA : 0 ≤ Y ^ 2 * (∫ t in (-Y)..Y,
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((Y / (q * sieveQ ε x)) ^ 2 + t ^ 2)) := mul_nonneg hY2 hI0
      have hB : 0 ≤ Y * Y ^ (1 / 50 : ℝ) := mul_nonneg hY.le hR0
      nlinarith [mul_nonneg hK2 hB, mul_nonneg hK1s hA]

/-- Twin check: the assembly has exactly the type of the open LEAF. -/
theorem leaf_char_nonprincipal_split_twin :
    type_of% @Prep1121LowExc.leaf_char_nonprincipal :=
  @leaf_char_nonprincipal_of_leaves

end LeanLab.BHP1997.S64LowExcCharNP
