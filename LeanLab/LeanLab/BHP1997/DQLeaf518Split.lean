/-
Burst 2026-11-20b, BHP1997, unit U3a, leaf `leaf_518` of
`DQLowerExceptionalMeanSquareDecisions`. SPLIT along the paper's own steps.

P0069 Baker Harman Pintz 1997, page 52: "We have proved (5.1) and (5.2) for b0(m). Lemma 29
yields (5.18)." Page 43 Lemma 29: if `G(s, χ) = Σ_{m ≍ Y} b_m χ(m) m^(-s)` satisfies (3.1),
and (5.1) over `F = E_q^c \ {χ0}` and (5.2) hold with `T2 = Y / qQ`, then the mean square of
`Σ_{m ∈ J_y} b(m) χ(m) - δχ W(y, z)` over `χ ∉ E_q` is `≪ (qQ)^2 Y L^(-A)`. Page 19 chooses
`E_q` and bounds its size, page 3 asks for `O(q^(1/2) L^(-2A))`.

Three sub-leaves, each a cited piece of that argument, and one PROVED lemma:
* `leaf_518_M1`: display 5.2 for b0, Lemmas 30 to 35 and 5.15 for the principal character;
* `leaf_518_E_M0`: the page 19 choice of `E_q` with its size, and display 5.1 for b0 over
  `E_q^c \ {χ0}`, Lemmas 30 to 35 and 5.15;
* `leaf_lemma29`: Lemma 29 on page 43, for any coefficients with (3.1), proved in the paper
  from [30] Lemma 3.19 and a variant of [8] Lemma 2, both CITED;
* `leaf_lemma29_integrable`, PROVED here: the integrand of Lemma 29 is interval integrable,
  tacit in the paper.

The statements spell out `G` and `W` instead of using `lowerG` and `perronW` of
`DQLowerExceptionalMeanSquareDecisions`, so that file can import this one; there the two
spellings agree by unfolding.

AI wrote the Lean code. Binary Goldbach is open; nothing here changes that.

NOTE U-1745, 2026-11-22: P0069 pages 20 and 43 print `[29], Lemma 3.19`, but [29] is Saffari and
Vaughan 1977, which has no Lemma 3.19. The result used is Titchmarsh [30], second edition 1986,
Lemma 3.19, book p. 70, the finite Perron formula with error, which follows from Lemma 3.12,
book p. 60, display 3.12.1. Page 22 of P0069 calls it Theorem 3.19 of [30]. Read from
copies/Titchmarsh1986-chIII.pdf, page images. Below, [30] Lemma 3.19 replaces the printed label.
NOTE U-1744, 2026-11-22: [8] is Harman, Primes in short intervals, Math. Z. 180, 1982, 335-348,
Lemma 2 on p. 339: for continuous g and 0 < T0 < T < X, the mean of the square of the integral of
g(s) x^s over c+iT0 to c+iT, c = 1 + 1/log X, over X to 2X is at most X^2 log X times the integral
of |g|^2. The variant on P0069 p. 44 has y^(it), a factor Y L, and prints [T, T'] in [Y/2, 3Y].
The leaves here use t in [-Y, Y] and no factor L: a stronger, still true form, by Plancherel
after y = e^v. MISMATCH with the printed statements, no statement change; see PROGRESS.md.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.Lemma29

namespace LeanLab.BHP1997.DQLeaf518Split
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators
open MeasureTheory

/-- LEAF: page 52 "We have proved (5.1) and (5.2) for b0(m)", the part (5.2) on page 43.
P0069 Baker Harman Pintz 1997: Lemmas 30 to 35 with the decomposition 5.15 on pages 50 and 51
give, for the principal character, `∫_{[-Y,Y] \ [-T0,T0]} |G(1/2+it, χ0)|^2 / (T2^2 + t^2) dt
≪ (Y / T2^2) L^(-A)`, with `G` the Dirichlet polynomial of b0 over J, `T2 = Y / qQ` and
`T0 = exp(L^(1/3))`. CONDITIONAL on the cited Theorem 4 and Lemma 9. -/
theorem leaf_518_M1 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  sorry

/-- LEAF: page 19 the choice of `E_q` with `|E_q| ≪ q^(1/2) L^(-2A)`, from Prachar [25] and
Montgomery [21] Theorem 12.1, and page 52 "We have proved (5.1) ... for b0(m)", display 5.1 on
page 43 over `F = E_q^c \ {χ0}`. P0069 Baker Harman Pintz 1997: Lemmas 30 to 35 with 5.15 give
`Σ_{χ ∈ F} ∫_{-Y}^{Y} |G(1/2+it, χ)|^2 / (T2^2 + t^2) dt ≪ (Y / T2^2) L^(-A')` for every `A'`.
The paper's `E_q` does not depend on `A`; here it may, and 5.1 holds for every `A'` at each
fixed set. CONDITIONAL on the cited Theorem 4 and Lemma 9; the zero free region of Prachar
and the zero density bound of Montgomery that page 19 uses are CITED inside this leaf. -/
theorem leaf_518_E_M0 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A') := by
  sorry

/-- Page 44, the scalar kernel estimate with the factor six in the range of 1.9. -/
theorem lemma29_ineq_six {t z T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hT : 0 < T) (hzT : z ≤ 6 / T) :
    ‖Complex.exp ((1 / 2 + t * I) * (Real.log (1 + z) : ℝ)) - 1‖ ^ 2 /
        ‖(1 / 2 + t * I : ℂ)‖ ^ 2 ≤ 324 / (T ^ 2 + t ^ 2) := by
  have hT6 : 0 < T / 6 := by positivity
  have hzT6 : z ≤ 1 / (T / 6) := by
    convert hzT using 1 <;> field_simp
  have hkernel := Lemma29.lemma29_ineq (t := t) hz hz1 hT6 hzT6
  refine hkernel.trans ?_
  have hd6 : 0 < (T / 6) ^ 2 + t ^ 2 := by positivity
  have hd : 0 < T ^ 2 + t ^ 2 := by positivity
  apply (div_le_div_iff₀ hd6 hd).mpr
  nlinarith [sq_nonneg t]

/-- LEAF: page 43 Lemma 29, the mean square bound. P0069 Baker Harman Pintz 1997: for a
Dirichlet polynomial over J with coefficients satisfying (3.1), (5.1) over `E^c \ {χ0}` and
(5.2) give `Σ_{χ ∉ E} ∫_{Y/2}^{3Y} |Σ_{m ∈ J_y} b(m) χ(m) - δχ W(y, z)|^2 dy ≪ (qQ)^2 Y L^(-A)`
for `z` in the range of 1.9. The paper's proof: the truncated Perron formula [30] Lemma 3.19 at
height `Y` with error `O(Y^ε)`, then 5.3 and 5.4 from a variant of [8] Lemma 2 and the bound
`|((1+z)^s - 1)/s|^2 ≪ 1/(T2^2 + t^2)`, which is `Lemma29.lemma29_ineq` in the lab. Both
citations are CITED inside this leaf. The norm is taken over `[Y/2, 3Y]` as in 1.9 and 5.18;
page 43 prints `[Y/2, 3Y/2]`, QUESTION 2 of the 2026-11-20 notes. -/
theorem leaf_lemma29 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q))
    (h51 : ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → q ≤ sieveQ ε x →
      ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
        ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A'))
    (h52 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
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
            C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- The line `Re s = 1/2` of Lemma 29 avoids `s = 0`. -/
theorem half_line_ne_zero (t : ℝ) : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- A Dirichlet polynomial is continuous on the line `Re s = 1/2`. -/
theorem dirichlet_poly_continuous (J : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (fun t : ℝ => ∑ m ∈ J, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
  refine continuous_finsetSum _ fun m _ => ?_
  by_cases hm : (m : ℂ) = 0
  · have : (fun t : ℝ => c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) = fun _ => 0 := by
      funext t; rw [hm, Complex.zero_cpow (half_line_ne_zero t)]; simp
    rw [this]; exact continuous_const
  · refine continuous_const.div (Continuous.const_cpow (by fun_prop) (Or.inl hm)) fun t => ?_
    exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (half_line_ne_zero t)).mpr hm

/-- The integrand of Lemma 29 is interval integrable: a step function minus a constant
times a parametric integral over a compact segment of a jointly continuous integrand. -/
theorem lemma29_integrable_aux (J : Finset ℕ) (c c1 : ℕ → ℂ) (d e : ℂ) {a b T z : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hT : 0 ≤ T) (hz : 0 ≤ z) :
    IntervalIntegrable (fun y =>
      ‖(∑ m ∈ J.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m) -
        d * (e * ∫ t in (-T)..T,
          (∑ m ∈ J, c1 m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
            ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
              (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2)
      volume a b := by
  set G : ℝ → ℂ := fun t => ∑ m ∈ J, c1 m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) with hG
  set F : ℝ → ℝ → ℂ := fun y t => G t *
      ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I) with hF
  set S : ℝ → ℂ := fun y =>
    ∑ m ∈ J.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m with hS
  show IntervalIntegrable (fun y => ‖S y - d * (e * ∫ t in (-T)..T, F y t)‖ ^ 2) volume a b
  have hGc : Continuous G := dirichlet_poly_continuous J c1
  -- measurability of the step function
  have hSm : Measurable S := by
    have : S = fun y => ∑ m ∈ J, if (y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) then c m else 0 := by
      funext y; simp only [hS, Finset.sum_filter]
    rw [this]
    refine Finset.measurable_sum _ fun m _ => Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_le (f := fun y : ℝ => y) (g := fun _ : ℝ => (m : ℝ))
      measurable_id measurable_const).inter
      (measurableSet_le (f := fun _ : ℝ => (m : ℝ)) (g := fun y : ℝ => y + y * z)
        measurable_const (by fun_prop))
  have hSb : ∀ y, ‖S y‖ ≤ ∑ m ∈ J, ‖c m‖ := fun y =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => norm_nonneg _)
  -- measurability of the parametric integral
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    have := hGc.measurable
    fun_prop
  have hWm : StronglyMeasurable (fun y => ∫ t in (-T)..T, F y t) := by
    have : (fun y => ∫ t in (-T)..T, F y t) =
        fun y => ∫ t, F y t ∂(volume.restrict (Set.Ioc (-T) T)) := by
      funext y; exact intervalIntegral.integral_of_le (by linarith)
    rw [this]
    exact hFm.stronglyMeasurable.integral_prod_right
  -- a bound for the parametric integral on [a, b]
  have hFc : ContinuousOn (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc (-T) T) := by
    intro p hp
    have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
    have hp2 : 0 < p.1 + p.1 * z := by positivity
    apply ContinuousAt.continuousWithinAt
    simp only [hF, Function.uncurry_def]
    refine ContinuousAt.div ?_ (by fun_prop) (half_line_ne_zero p.2)
    refine ContinuousAt.mul (hGc.continuousAt.comp (by fun_prop)) (ContinuousAt.sub ?_ ?_)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop)
        (Complex.ofReal_mem_slitPlane.mpr hp2)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop)
        (Complex.ofReal_mem_slitPlane.mpr hp1)
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hFc
  have hWb : ∀ y ∈ Set.Icc a b, ‖∫ t in (-T)..T, F y t‖ ≤ K * |T - -T| := by
    intro y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    have ht' : t ∈ Set.Icc (-T) T := by
      rw [Set.uIoc_of_le (by linarith)] at ht; exact ⟨ht.1.le, ht.2⟩
    exact hK (y, t) ⟨hy, ht'⟩
  set M : ℝ := ((∑ m ∈ J, ‖c m‖) + ‖d‖ * (‖e‖ * (K * |T - -T|))) ^ 2 with hM
  refine IntervalIntegrable.mono_fun' (g := fun _ => M) intervalIntegrable_const ?_ ?_
  · exact ((hSm.sub (measurable_const.mul (measurable_const.mul hWm.measurable))).norm.pow_const
      2).aestronglyMeasurable
  · rw [Set.uIoc_of_le hab]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => ?_
    have hy' : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2⟩
    have h1 : ‖S y - d * (e * ∫ t in (-T)..T, F y t)‖ ≤
        (∑ m ∈ J, ‖c m‖) + ‖d‖ * (‖e‖ * (K * |T - -T|)) := by
      calc _ ≤ ‖S y‖ + ‖d * (e * ∫ t in (-T)..T, F y t)‖ := norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_mul, norm_mul]
          gcongr
          · exact hSb y
          · exact hWb y hy'
    simp only [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- The integrand of Lemma 29 on page 43 is interval integrable on `[Y/2, 3Y]`. P0069
Baker Harman Pintz 1997, tacit in the paper: the window sum is a step function of `y` with
finitely many jumps, and `W(y, z)` is an integral over the compact segment `[-T0, T0]` of an
integrand continuous in `(y, t)` for `y > 0`, so both are bounded and measurable. -/
theorem leaf_lemma29_integrable (b : ℝ → ℕ → ℝ) (ε x : ℝ) (hx : 1 ≤ x) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (z : ℝ) (hz : 0 ≤ z) :
    IntervalIntegrable (fun y =>
      ‖(∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        (b x m : ℂ) * χ (m : ZMod q)) -
        Thm2.delta χ * (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
            (∑ m ∈ rightInterval ε x, (b x m : ℂ) *
                (1 : DirichletCharacter ℂ q) (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) *
              ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
                (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))‖ ^ 2)
      volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  exact lemma29_integrable_aux (rightInterval ε x) (fun m => (b x m : ℂ) * χ (m : ZMod q))
    (fun m => (b x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) (Thm2.delta χ)
    (((2 * Real.pi : ℝ) : ℂ)⁻¹) (by positivity) (by linarith) (Real.exp_pos _).le hz

end LeanLab.BHP1997.DQLeaf518Split
