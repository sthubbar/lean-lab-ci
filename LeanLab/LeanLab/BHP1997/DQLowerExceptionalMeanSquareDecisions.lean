/-
Cited wall session 2026-11-20, BHP1997, step `lower_exceptional_mean_square`.
Verdict FORMALIZE. Source: P0069 Baker Harman Pintz 1997, page 3 display 1.9, page 22 the
definition of `T0`, page 43 Lemma 29 with the definitions of `G` and `W`, page 52 displays
5.18 to 5.23 with the definition of `H`.

The sealed open leaf `LowerShortC165.lower_exceptional_mean_square` is not a cited external
theorem: it is the paper's own argument on page 52. The elementary skeleton, "Now (1.9)
follows from (5.18), (5.23) and (5.22)", is already PROVED in `LowerShortMeanSquare` with `W`
and `H` as free parameters. The burst of 2026-11-15 stopped there because the lab had no
definition of `W` and `H`, and leaves with `W` and `H` existential would restate the target.

This file gives the definitions, so `W` and `H` are now concrete, and splits page 52 into
five LEAF statements along the printed steps:
* `leaf_518`, display 5.18, Lemma 29 on page 43 applied to b0 after Lemmas 33 to 35;
* `leaf_520`, display 5.20 at `z0`, from 5.19 and 5.17, in the lab form with the main term
  restricted to J;
* `leaf_521`, display 5.21, "the proof of (4.4)", pointwise in `y`;
* `leaf_count_scale`, the step "and consequently (5.22)" from `z0` to `z` for the lab's
  J-restricted main term, an elementary counting fact;
* `leaf_regularity`, interval integrability of the two continuous-minus-step integrands.
The steps 5.22 at `z0`, 5.22 at `z` and 5.23 are PROVED here from the leaves, and the
assembly `lower_exceptional_mean_square_split` has exactly the type of the sealed leaf.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerShortMeanSquare
import LeanLab.BHP1997.DecompC165d

namespace LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open scoped BigOperators
open MeasureTheory

/-! ### Definitions, each one a printed display -/

/-- P0069 page 22, "In the remainder of the paper we write `T0 = exp(L^(1/3))`", with
`L = log x`. -/
noncomputable def perronT0 (x : ℝ) : ℝ := Real.exp (Real.log x ^ (1 / 3 : ℝ))

/-- P0069 page 52, after 5.19, `z0 = 1 / T0^2`. -/
noncomputable def perronZ0 (x : ℝ) : ℝ := 1 / perronT0 x ^ 2

/-- P0069 page 43, Lemma 29, the Dirichlet polynomial `G(s, χ) = Σ_{m ~ Y} b_m χ(m) m^(-s)`,
here for b0, the lab's `lowerShortWeight`, summed over the lab's interval J. -/
noncomputable def lowerG (ω : ℝ → ℝ) (ε x : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    ℂ :=
  ∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) / (m : ℂ) ^ s

/-- P0069 page 43, Lemma 29, `W(y, z) = (1/2πi) ∫_{1/2-iT0}^{1/2+iT0} G(s, χ0)
((y + yz)^s - y^s) / s ds`, written with `s = 1/2 + it`, so `ds = i dt`. Here `χ0` is the
principal character modulo `q`. -/
noncomputable def perronW (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) (y z : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-perronT0 x)..(perronT0 x),
    lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) *
      ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)

/-- P0069 page 52, after 5.21, `H(y) = (1/2πi) ∫_{1/2-iT0}^{1/2+iT0} G(s, χ0) y^s ds`.
QUESTION 4 of the 2026-11-15 burst: the page image prints `y^(s-1)`, but 5.21 to 5.23 compare
`z H(y)` with `W(y, z)` and with `v0 y z / L'`, which fits `y^s` only. This definition takes
`y^s`, the reading under which 5.21 to 5.23 are consistent. -/
noncomputable def perronH (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) (y : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-perronT0 x)..(perronT0 x),
    lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)

/-! ### The leaves -/

/-- LEAF: page 52 display 5.18. P0069 Baker Harman Pintz 1997, "Lemma 29 yields (5.18)":
Lemmas 33 to 35 and the decomposition 5.15 give 5.1 and 5.2 for b0, and Lemma 29 on page 43,
via [29] Lemma 3.19, bounds the mean square of the J window sum of `b0 χ` minus `δχ W(y, z)`
outside an exceptional set of `O(q^(1/2) L^(-2A))` characters, page 3. Integrability included.
CONDITIONAL on the cited Theorem 4 and Lemma 9 as in the sealed leaf. -/
theorem leaf_518 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          (∀ χ : DirichletCharacter ℂ q, IntervalIntegrable (fun y =>
            ‖(∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q)) -
              Thm2.delta χ * perronW ω ε x q y z‖ ^ 2) volume
            (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε))) ∧
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖(∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q)) -
                Thm2.delta χ * perronW ω ε x q y z‖ ^ 2 ≤
                  C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: page 52 display 5.20 at `z0 = 1/T0^2`. P0069 Baker Harman Pintz 1997, "Combining
(5.19), (5.17)": 5.19 is Lemma 29 again with `T2` replaced by the smaller `1 / z0^(1/2)`, so
the window sum of `b0 χ0` over `[y, y + y z0]` is close to `W(y, z0)` in mean square, and 5.17
on page 51 says that window sum is `v0 y z0 / L'` up to `O(y (T0^(-5) + z0^2))`. Lab form: the
main term is `v0 / L'` summed over the integers of J in the window, as in the lab's 1.9; for
`y` outside J the printed main term `v0 y z0 / L'` would not be small. Only the principal
character carries `δχ`, so the leaf is the principal term. CONDITIONAL on the cited
Theorem 4 and Lemma 9 as in the sealed leaf. -/
theorem leaf_520 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      IntervalIntegrable (fun y => ‖perronW ω ε x q y (perronZ0 x) -
          ∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
            ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2) volume
        (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖perronW ω ε x q y (perronZ0 x) -
            ∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2 ≤
        C * perronZ0 x ^ 2 * (x ^ (11 / 20 + ε)) ^ 3 * Real.log x ^ (-A) := by
  sorry

/-- LEAF: page 52 display 5.21. P0069 Baker Harman Pintz 1997, "The proof of (4.4) yields
`|W(y, z') - z' H(y)| ≪ z' y L^(-A)` if `z ≤ z' ≤ z0`". Taken here for `z'` in the range of
1.9 and for `z' = z0`; for large `x` the range lies below `z0`, so this is a sub-case of the
printed 5.21. The route: `((1 + z')^s - 1)/s - z'` is `O(|s| z'^2)` on the contour, and the
mean value of `G` on `[-T0, T0]` gives a saving `T0^(-1/2)`. -/
theorem leaf_521 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z' : ℝ, (((q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z' ∧
          z' ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε)) ∨ z' = perronZ0 x) →
        ∀ y ∈ Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)),
          ‖perronW ω ε x q y z' - (z' : ℂ) * perronH ω ε x q y‖ ≤
            C * z' * y * Real.log x ^ (-A) := by
  sorry

/-- LEAF: page 52 the step "and consequently (5.22)", from `z0` to `z`, for the lab's main
term restricted to J. P0069 Baker Harman Pintz 1997: with the printed main term
`v0 y z / L'` the step is exact scaling, PROVED as `mean_square_scale_z`. With the lab's
main term, `v0 / L'` times the number of integers of J in `[y, y + y z]`, the scaled count
`(z / z0) N(y, z0)` and the count `N(y, z)` differ by `O(v0 / L')` inside J and by at most the
main term on a set of `y` of measure `O(Y z0)` near the ends of J. So the mean square of the
difference is `O(Y + z^2 Y^3 z0)`, far below `(qQ)^2 Y L^(-A)`. Elementary; integrability of
the step function included. -/
theorem leaf_count_scale (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        IntervalIntegrable (fun y => ‖((z / perronZ0 x : ℝ) : ℂ) *
            (∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)) -
            ∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2) volume
          (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
        ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖((z / perronZ0 x : ℝ) : ℂ) *
              (∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
                ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)) -
              ∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2 ≤
          C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-! ### Helpers for the regularity leaf: positivity, norms of the `t`-integrand, continuity -/

/-- `T0 = exp(L^(1/3)) > 0`. -/
theorem perronT0_pos (x : ℝ) : 0 < perronT0 x := by
  unfold perronT0
  positivity

/-- The integers of `J = (x^(11/20+ε), 2 x^(11/20+ε)]` are positive. -/
private lemma one_le_of_mem_rightInterval {ε x : ℝ} {m : ℕ} (hm : m ∈ rightInterval ε x) :
    1 ≤ m := by
  unfold rightInterval at hm
  rw [Finset.mem_Ioc] at hm
  omega

/-- For `m ≥ 1` and `s = 1/2 + it`, `‖m^s‖ = m^(1/2)`. -/
private lemma norm_natCast_cpow_half {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    ‖(m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ = (m : ℝ) ^ (1 / 2 : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : ((m : ℂ)) = ((m : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
  have hre : (((1 / 2 : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
  rw [hre]

/-- For `m ≥ 1` and `s = 1/2 + it`, `‖m^s‖ ≥ 1`. -/
private lemma one_le_norm_natCast_cpow_half {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    (1 : ℝ) ≤ ‖(m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ := by
  rw [norm_natCast_cpow_half hm t]
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  calc (1 : ℝ) = (1 : ℝ) ^ (1 / 2 : ℝ) := by simp
    _ ≤ (m : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

/-- `‖G(1/2 + it, χ)‖` is bounded uniformly in `t` by the sum of the absolute weights:
each term is `b_m χ(m)` times `m^(-1/2-it)`, of modulus `m^(-1/2) ≤ 1`. -/
private lemma norm_lowerG_le (ω : ℝ → ℝ) (ε x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖lowerG ω ε x χ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      ∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m| := by
  unfold lowerG
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm1 := one_le_of_mem_rightInterval hm
  have hden1 := one_le_norm_natCast_cpow_half hm1 t
  have hχ : ‖χ (m : ZMod q)‖ ≤ 1 := χ.norm_le_one (m : ZMod q)
  have hb : (0 : ℝ) ≤ |lowerShortWeight ω ε x m| := abs_nonneg _
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |lowerShortWeight ω ε x m| * ‖χ (m : ZMod q)‖ ≤ |lowerShortWeight ω ε x m| := by
    nlinarith [hχ, hb]
  have h2 : |lowerShortWeight ω ε x m| * ‖χ (m : ZMod q)‖ /
      ‖(m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        |lowerShortWeight ω ε x m| * ‖χ (m : ZMod q)‖ := by
    rw [div_le_iff₀ (by linarith)]
    have h := mul_le_mul_of_nonneg_left hden1 (by positivity :
      (0 : ℝ) ≤ |lowerShortWeight ω ε x m| * ‖χ (m : ZMod q)‖)
    simpa using h
  exact h2.trans h1

/-- `t ↦ G(1/2 + it, χ)` is continuous: a finite sum of `t ↦ m^(-1/2-it)`. -/
private lemma continuous_lowerG (ω : ℝ → ℝ) (ε x : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    Continuous fun t : ℝ => lowerG ω ε x χ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  unfold lowerG
  refine continuous_finsetSum _ fun m hm => ?_
  have hm1 := one_le_of_mem_rightInterval hm
  have hexp : Continuous fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  have hmne : ((m : ℂ)) ≠ 0 := by
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have h := ne_of_gt hm0
    exact_mod_cast h
  have hcp : Continuous fun t : ℝ => (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hexp.const_cpow (Or.inl hmne)
  have hne : ∀ t : ℝ, ((m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) ≠ 0 := by
    intro t h
    have h1 := one_le_norm_natCast_cpow_half hm1 t
    rw [h, norm_zero] at h1
    linarith
  exact (continuous_const.mul continuous_const).div hcp hne

/-- `‖(y : ℂ)^(1/2+it)‖ = y^(1/2)` for `y > 0`. -/
private lemma norm_ofReal_cpow_half {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖(y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ = y ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have : (((1 / 2 : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
  rw [this]

/-- `1/2 + it` is never zero. -/
private lemma half_add_mul_I_ne_zero (t : ℝ) : ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  intro h
  have hre : (((1 / 2 : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
  rw [h] at hre
  norm_num at hre

/-- `‖1/2 + it‖ ≥ 1/2`. -/
private lemma half_le_norm_half_add_mul_I (t : ℝ) :
    (1 / 2 : ℝ) ≤ ‖((1 / 2 : ℂ) + (t : ℂ) * I)‖ := by
  have hre : (((1 / 2 : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
  calc (1 / 2 : ℝ) = (((1 / 2 : ℂ) + (t : ℂ) * I)).re := by rw [hre]
    _ ≤ ‖((1 / 2 : ℂ) + (t : ℂ) * I)‖ := Complex.re_le_norm _

/-- `H` is continuous at every `y > 0`: its integrand is continuous in `t`, bounded by a
constant on the contour, and continuous in `y`. -/
private lemma continuousAt_perronH (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) {y₀ : ℝ} (hy : 0 < y₀) :
    ContinuousAt (fun y => perronH ω ε x q y) y₀ := by
  set β := ∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m| with hβdef
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hy₀ : (0 : ℝ) < 3 / 2 * y₀ := by linarith
  set B := β * ((3 / 2 * y₀) ^ (1 / 2 : ℝ)) with hBdef
  have hG : Continuous fun t : ℝ => lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    continuous_lowerG ω ε x (1 : DirichletCharacter ℂ q)
  unfold perronH
  refine ContinuousAt.const_mul (intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (y : ℝ) t => lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) *
      ((y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I))) (bound := fun _ => B) (μ := volume)
    ?_ ?_ intervalIntegrable_const ?_) (((2 * Real.pi : ℝ)) : ℂ)⁻¹
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 : Continuous fun t : ℝ => ((y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
      have hexp : Continuous fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
      exact hexp.const_cpow (Or.inr half_add_mul_I_ne_zero)
    exact (hG.mul h1).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (by linarith : y₀ / 2 < y₀) (by linarith : y₀ < 3 / 2 * y₀)]
      with y hy'
    refine Filter.Eventually.of_forall fun t _ => ?_
    have hy0 : 0 < y := by linarith [hy'.1]
    have hyle : y ≤ 3 / 2 * y₀ := by linarith [hy'.2]
    rw [norm_mul, norm_ofReal_cpow_half hy0 t]
    calc ‖lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ * y ^ (1 / 2 : ℝ)
        ≤ β * y ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (norm_lowerG_le ω ε x 1 t)
            (Real.rpow_nonneg hy0.le _)
      _ ≤ β * ((3 / 2 * y₀) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le hyle (by norm_num)) hβ0
      _ = B := by rw [hBdef]
  · refine Filter.Eventually.of_forall fun t _ => ?_
    exact continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt).cpow
      continuousAt_const (Complex.ofReal_mem_slitPlane.2 hy))

/-- `W` is continuous at every `y > 0`, uniformly in `z ≥ 0`. -/
private lemma continuousAt_perronW (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) (z : ℝ) {y₀ : ℝ}
    (hy : 0 < y₀) (hz : 0 ≤ z) :
    ContinuousAt (fun y => perronW ω ε x q y z) y₀ := by
  set β := ∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m| with hβdef
  have hβ0 : 0 ≤ β := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hy₀ : (0 : ℝ) < 3 / 2 * y₀ := by linarith
  set B := β * (((3 / 2 * y₀) * (1 + z)) ^ (1 / 2 : ℝ) +
    (3 / 2 * y₀) ^ (1 / 2 : ℝ)) * 2 with hBdef
  have hG : Continuous fun t : ℝ => lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    continuous_lowerG ω ε x (1 : DirichletCharacter ℂ q)
  unfold perronW
  refine ContinuousAt.const_mul (intervalIntegral.continuousAt_of_dominated_interval
    (F := fun (y : ℝ) t => lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) *
      ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I))
    (bound := fun _ => B) (μ := volume) ?_ ?_ intervalIntegrable_const ?_) (((2 * Real.pi : ℝ)) : ℂ)⁻¹
  · refine Filter.Eventually.of_forall fun y => ?_
    have hexp : Continuous fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
    have h1 : Continuous fun t : ℝ =>
        (((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
      hexp.const_cpow (Or.inr half_add_mul_I_ne_zero)
    have h2 : Continuous fun t : ℝ => ((y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) :=
      hexp.const_cpow (Or.inr half_add_mul_I_ne_zero)
    exact ((hG.mul (h1.sub h2)).div hexp half_add_mul_I_ne_zero).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (by linarith : y₀ / 2 < y₀) (by linarith : y₀ < 3 / 2 * y₀)]
      with y hy'
    refine Filter.Eventually.of_forall fun t _ => ?_
    have hy0 : 0 < y := by linarith [hy'.1]
    have hyle : y ≤ 3 / 2 * y₀ := by linarith [hy'.2]
    have hyz0 : 0 < y + y * z := by nlinarith
    have hAnorm : ‖(((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ =
        (y + y * z) ^ (1 / 2 : ℝ) := norm_ofReal_cpow_half hyz0 t
    have hBnorm : ‖(y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ = y ^ (1 / 2 : ℝ) :=
      norm_ofReal_cpow_half hy0 t
    have hle1 : (y + y * z) ^ (1 / 2 : ℝ) ≤ ((3 / 2 * y₀) * (1 + z)) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      nlinarith
    have hle2 : y ^ (1 / 2 : ℝ) ≤ (3 / 2 * y₀) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hy0.le hyle (by norm_num)
    have hS : ‖(((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        ((3 / 2 * y₀) * (1 + z)) ^ (1 / 2 : ℝ) + (3 / 2 * y₀) ^ (1 / 2 : ℝ) := by
      calc _ ≤ ‖(((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ +
            ‖(y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ := norm_sub_le _ _
        _ = (y + y * z) ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) := by rw [hAnorm, hBnorm]
        _ ≤ _ := add_le_add hle1 hle2
    have hs := half_le_norm_half_add_mul_I t
    have hspos : (0 : ℝ) < ‖((1 / 2 : ℂ) + (t : ℂ) * I)‖ := by linarith
    rw [norm_div, norm_mul]
    have h1 : ‖lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
        ‖(((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
          (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        β * (((3 / 2 * y₀) * (1 + z)) ^ (1 / 2 : ℝ) + (3 / 2 * y₀) ^ (1 / 2 : ℝ)) :=
      mul_le_mul (norm_lowerG_le ω ε x 1 t) hS (norm_nonneg _) hβ0
    have h2 : ‖lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
        ‖(((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
          (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ /
        ‖((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        β * (((3 / 2 * y₀) * (1 + z)) ^ (1 / 2 : ℝ) + (3 / 2 * y₀) ^ (1 / 2 : ℝ)) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hs
    have h3 : β * (((3 / 2 * y₀) * (1 + z)) ^ (1 / 2 : ℝ) + (3 / 2 * y₀) ^ (1 / 2 : ℝ)) /
        (1 / 2) = B := by
      rw [hBdef]; ring
    calc ‖lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
          ‖(((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
            (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ / ‖((1 / 2 : ℂ) + (t : ℂ) * I)‖
        ≤ _ := h2
      _ = B := h3
  · refine Filter.Eventually.of_forall fun t _ => ?_
    have hbase : ContinuousAt (fun y : ℝ => ((y + y * z : ℝ) : ℂ)) y₀ :=
      Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
    have hmem : ((y₀ + y₀ * z : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 (by nlinarith)
    have h1 : ContinuousAt (fun y : ℝ =>
        ((y + y * z : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) y₀ :=
      hbase.cpow continuousAt_const hmem
    have h2 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) y₀ :=
      Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 hy)
    exact ((continuousAt_const.mul (h1.sub h2)).div continuousAt_const
      (half_add_mul_I_ne_zero t))


/-! ### Bounds for `H` and for the window count, and integrability of a bounded integrand -/

/-- `‖H(y)‖ ≤ (2π)^(-1) 2 T0 β y^(1/2)` for `y > 0`, where `β = Σ |b0(m)|` bounds `G` on the
contour. -/
private lemma norm_perronH_le (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖perronH ω ε x q y‖ ≤ (2 * Real.pi)⁻¹ * (2 * perronT0 x) *
      ((∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m|) * y ^ (1 / 2 : ℝ)) := by
  have hT0 := perronT0_pos x
  unfold perronH
  rw [norm_mul]
  have hc : ‖(((2 * Real.pi : ℝ)) : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  have hInt : ‖∫ t in (-perronT0 x)..(perronT0 x),
      lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) *
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      ((∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m|) * y ^ (1 / 2 : ℝ)) *
        |perronT0 x - -perronT0 x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => ?_
    rw [norm_mul, norm_ofReal_cpow_half hy t]
    exact mul_le_mul_of_nonneg_right (norm_lowerG_le ω ε x 1 t) (Real.rpow_nonneg hy.le _)
  refine le_trans (mul_le_mul_of_nonneg_left hInt (by positivity)) (le_of_eq ?_)
  rw [abs_of_pos (by linarith)]
  ring

/-- The window count of numbers of `J` in `[y, y + yz]`, times the constant `c`, is bounded by
`#J · ‖c‖`. -/
private lemma norm_windowCount_le (s : Finset ℕ) (z : ℝ) (c : ℂ) (y : ℝ) :
    ‖∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0‖ ≤ (s.card : ℝ) * ‖c‖ := by
  classical
  rw [← Finset.sum_filter]
  refine (norm_sum_le _ _).trans ?_
  have h2 : ∑ m ∈ s.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ‖c‖ =
      ((s.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ) * ‖c‖ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  have h3 : ((s.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ) ≤
      (s.card : ℝ) := by
    exact_mod_cast Finset.card_filter_le s _
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg c)

/-- The window count, as a function of `y`, is measurable. -/
private lemma measurable_windowCount (s : Finset ℕ) (z : ℝ) (c : ℂ) :
    Measurable fun y : ℝ => ∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0 := by
  classical
  refine Finset.measurable_sum _ fun m _ => ?_
  have h1 : MeasurableSet {y : ℝ | y ≤ (m : ℝ)} :=
    measurableSet_le measurable_id measurable_const
  have h2 : MeasurableSet {y : ℝ | (m : ℝ) ≤ y + y * z} :=
    measurableSet_le measurable_const
      (measurable_id.add (measurable_id.mul measurable_const) :
        Measurable fun y : ℝ => y + y * z)
  exact Measurable.ite (h1.inter h2) measurable_const measurable_const

/-- A measurable function bounded on `Ioc a b` has interval integrable squared norm. -/
private lemma intervalIntegrable_norm_sq_of_bounded {f : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    (hbdd : ∀ y ∈ Set.Ioc a b, ‖f y‖ ≤ C) :
    IntervalIntegrable (fun y : ℝ => ‖f y‖ ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine IntegrableOn.of_bound ?_ ?_ (C ^ 2) ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · exact hmeas.norm.pow 2
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have h1 := hbdd y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg (f y)) h1 2

/-- LEAF: the definitions of `W` on page 43 and `H` on page 52, regularity in `y`. P0069
Baker Harman Pintz 1997: for `y > 0` both are integrals over the compact segment
`[-T0, T0]` of integrands continuous in `(y, t)`, so they are continuous in `y`; the window
count is a step function with finitely many jumps. So the two integrands below are interval
integrable on `[Y/2, 3Y]`. Not a printed step; the paper uses it tacitly when it integrates
5.21 to get 5.23 and 5.20 to get 5.22. -/
theorem leaf_regularity (ω : ℝ → ℝ) (ε : ℝ) :
    ∀ x : ℝ, 1 ≤ x → ∀ q : ℕ, ∀ z : ℝ, 0 ≤ z →
      IntervalIntegrable (fun y => ‖perronW ω ε x q y z - (z : ℂ) * perronH ω ε x q y‖ ^ 2)
        volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
      IntervalIntegrable (fun y => ‖(z : ℂ) * perronH ω ε x q y -
          ∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2) volume
        (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) := by
  classical
  intro x hx q z hz
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  have hβ : 0 ≤ ∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · have hcont : ContinuousOn
        (fun y => perronW ω ε x q y z - (z : ℂ) * perronH ω ε x q y)
        (Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε))) := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1, hY]
      exact ((continuousAt_perronW ω ε x q z hy0 hz).sub
        (continuousAt_const.mul (continuousAt_perronH ω ε x q hy0))).continuousWithinAt
    exact (hcont.norm.pow 2).intervalIntegrable_of_Icc hab
  · simp only [Finset.sum_filter]
    set c : ℂ := ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) with hc
    set s : Finset ℕ := rightInterval ε x with hs
    have hmeasH : AEStronglyMeasurable (fun y => perronH ω ε x q y)
        (volume.restrict (Set.Ioc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      intro y hy
      exact (continuousAt_perronH ω ε x q (by linarith [hy.1, hY])).continuousWithinAt
    have hmeasS : AEStronglyMeasurable
        (fun y : ℝ => ∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0)
        (volume.restrict (Set.Ioc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)))) :=
      (measurable_windowCount s z c).aestronglyMeasurable
    refine intervalIntegrable_norm_sq_of_bounded (f := fun y =>
      (z : ℂ) * perronH ω ε x q y -
        ∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0)
      (C := |z| * ((2 * Real.pi)⁻¹ * (2 * perronT0 x) *
        ((∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m|) *
          (3 * x ^ (11 / 20 + ε)) ^ (1 / 2 : ℝ))) + (s.card : ℝ) * ‖c‖) hab ?_ ?_
    · exact (hmeasH.const_mul (z : ℂ)).sub hmeasS
    · intro y hy
      have hy0 : 0 < y := by linarith [hy.1, hY]
      have hyle : y ≤ 3 * x ^ (11 / 20 + ε) := hy.2
      have hHy : ‖perronH ω ε x q y‖ ≤ (2 * Real.pi)⁻¹ * (2 * perronT0 x) *
          ((∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m|) *
            (3 * x ^ (11 / 20 + ε)) ^ (1 / 2 : ℝ)) := by
        refine (norm_perronH_le ω ε x q hy0).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by
          have h1 : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
          have h2 : (0 : ℝ) < 2 * perronT0 x := by
            have := perronT0_pos x; linarith
          positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hy0.le hyle (by norm_num)) hβ
      calc ‖(z : ℂ) * perronH ω ε x q y -
            ∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0‖
          ≤ ‖(z : ℂ) * perronH ω ε x q y‖ +
            ‖∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0‖ := norm_sub_le _ _
        _ = |z| * ‖perronH ω ε x q y‖ +
            ‖∑ m ∈ s, if y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z then c else 0‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |z| * ((2 * Real.pi)⁻¹ * (2 * perronT0 x) *
              ((∑ m ∈ rightInterval ε x, |lowerShortWeight ω ε x m|) *
                (3 * x ^ (11 / 20 + ε)) ^ (1 / 2 : ℝ))) + (s.card : ℝ) * ‖c‖ :=
              add_le_add (mul_le_mul_of_nonneg_left hHy (abs_nonneg z))
                (norm_windowCount_le s z c y)

/-! ### Proved steps -/

/-- `T0 > 0`, so `z0 > 0`. -/
theorem perronZ0_pos (x : ℝ) : 0 < perronZ0 x := by
  unfold perronZ0 perronT0
  positivity

/-- `(L^(-A/2))^2 = L^(-A)` for `L ≥ 0`. -/
theorem rpow_neg_half_sq {L : ℝ} (A : ℝ) (hL : 0 ≤ L) :
    (L ^ (-(A / 2))) ^ 2 = L ^ (-A) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  congr 1
  push_cast
  ring

/-- With `z ≤ 6 a b / Y` and `z ≥ 0`, `z^2 Y^3 ≤ 36 (a b)^2 Y`: the printed `z^2 Y^3` of
5.18 to 5.23 against the `(qQ)^2 Y` of 1.9. -/
theorem z_sq_Y_cube_le {z Y a b : ℝ} (hY : 0 < Y) (hz0 : 0 ≤ z) (hz : z ≤ 6 * a * b / Y) :
    z ^ 2 * Y ^ 3 ≤ 36 * (a * b) ^ 2 * Y := by
  have h1 : z * Y ≤ 6 * a * b := (le_div_iff₀ hY).mp hz
  have h0 : 0 ≤ z * Y := by positivity
  have h2 : (z * Y) ^ 2 ≤ (6 * a * b) ^ 2 := pow_le_pow_left₀ h0 h1 2
  calc z ^ 2 * Y ^ 3 = (z * Y) ^ 2 * Y := by ring
    _ ≤ (6 * a * b) ^ 2 * Y := mul_le_mul_of_nonneg_right h2 hY.le
    _ = 36 * (a * b) ^ 2 * Y := by ring

/-- P0069 page 52, "Another consequence of (5.21) is (5.23)", one integral: a pointwise bound
`|f(y)| ≤ c z y L` on `[Y/2, 3Y]` gives `∫ |f|^2 ≤ (45/2) c^2 z^2 Y^3 L^2`. -/
theorem mean_square_of_521 {Y z c L : ℝ} (hY : 0 < Y) (hz0 : 0 ≤ z) (hL : 0 ≤ L)
    (f : ℝ → ℂ) (hf : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ‖f y‖ ≤ c * z * y * L) :
    ∫ y in (Y / 2)..(3 * Y), ‖f y‖ ^ 2 ≤ 45 / 2 * c ^ 2 * z ^ 2 * Y ^ 3 * L ^ 2 := by
  have hB : 0 ≤ |c| * z * L := by positivity
  have hf' : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ‖f y‖ ≤ (|c| * z * L) * y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by linarith) hy.1
    have hzyL : 0 ≤ z * y * L := by positivity
    calc ‖f y‖ ≤ c * z * y * L := hf y hy
      _ = c * (z * y * L) := by ring
      _ ≤ |c| * (z * y * L) := mul_le_mul_of_nonneg_right (le_abs_self c) hzyL
      _ = (|c| * z * L) * y := by ring
  have h := mean_square_of_pointwise (a := Y / 2) (b := 3 * Y) (by linarith) (by linarith) hB
    f hf'
  calc _ ≤ (|c| * z * L) ^ 2 * (3 * Y) ^ 2 * (3 * Y - Y / 2) := h
    _ = 45 / 2 * c ^ 2 * z ^ 2 * Y ^ 3 * L ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring

/-- P0069 page 52, "Combining (5.20) with (5.21) for z = z0" and "consequently (5.22)",
pointwise: if `f = r (g2 - g1) + g3` then `|f|^2 ≤ 4 r^2 |g1|^2 + 4 r^2 |g2|^2 + 2 |g3|^2`.
With `f = z H - N(z)`, `g1 = W(z0) - z0 H`, `g2 = W(z0) - N(z0)`, `g3 = (z/z0) N(z0) - N(z)` and
`r = z / z0`. -/
theorem pointwise_522 (r : ℝ) (f g1 g2 g3 : ℂ) (hf : f = (r : ℂ) * (g2 - g1) + g3) :
    ‖f‖ ^ 2 ≤ 4 * r ^ 2 * ‖g1‖ ^ 2 + 4 * r ^ 2 * ‖g2‖ ^ 2 + 2 * ‖g3‖ ^ 2 := by
  have h1 := norm_add_sq_le_two ((r : ℂ) * (g2 - g1)) g3
  have h2 := norm_add_sq_le_two g2 (-g1)
  rw [norm_neg, ← sub_eq_add_neg] at h2
  have hn : ‖(r : ℂ) * (g2 - g1)‖ ^ 2 = r ^ 2 * ‖g2 - g1‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hr : 0 ≤ r ^ 2 := sq_nonneg r
  rw [hf]
  have h3 : r ^ 2 * ‖g2 - g1‖ ^ 2 ≤ r ^ 2 * (2 * (‖g2‖ ^ 2 + ‖g1‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left h2 hr
  nlinarith

/-- The integrated form of `pointwise_522` on `[a, b]`. The left side need not be integrable:
if it is not, its integral is zero. -/
theorem mean_square_522 {a b : ℝ} (hab : a ≤ b) (r : ℝ) (f g1 g2 g3 : ℝ → ℂ)
    (hf : ∀ y, f y = (r : ℂ) * (g2 y - g1 y) + g3 y)
    (h1 : IntervalIntegrable (fun y => ‖g1 y‖ ^ 2) volume a b)
    (h2 : IntervalIntegrable (fun y => ‖g2 y‖ ^ 2) volume a b)
    (h3 : IntervalIntegrable (fun y => ‖g3 y‖ ^ 2) volume a b) :
    ∫ y in a..b, ‖f y‖ ^ 2 ≤
      4 * r ^ 2 * (∫ y in a..b, ‖g1 y‖ ^ 2) + 4 * r ^ 2 * (∫ y in a..b, ‖g2 y‖ ^ 2) +
        2 * (∫ y in a..b, ‖g3 y‖ ^ 2) := by
  have hR : IntervalIntegrable (fun y => 4 * r ^ 2 * ‖g1 y‖ ^ 2 + 4 * r ^ 2 * ‖g2 y‖ ^ 2 +
      2 * ‖g3 y‖ ^ 2) volume a b :=
    ((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _)
  have hRint : ∫ y in a..b, (4 * r ^ 2 * ‖g1 y‖ ^ 2 + 4 * r ^ 2 * ‖g2 y‖ ^ 2 +
      2 * ‖g3 y‖ ^ 2) =
      4 * r ^ 2 * (∫ y in a..b, ‖g1 y‖ ^ 2) + 4 * r ^ 2 * (∫ y in a..b, ‖g2 y‖ ^ 2) +
        2 * (∫ y in a..b, ‖g3 y‖ ^ 2) := by
    rw [intervalIntegral.integral_add ((h1.const_mul _).add (h2.const_mul _)) (h3.const_mul _),
      intervalIntegral.integral_add (h1.const_mul _) (h2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [← hRint]
  by_cases hL : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume a b
  · exact intervalIntegral.integral_mono_on hab hL hR fun y _ =>
      pointwise_522 r (f y) (g1 y) (g2 y) (g3 y) (hf y)
  · rw [intervalIntegral.integral_undef hL]
    exact intervalIntegral.integral_nonneg hab fun _ _ => by positivity

/-- The constant bookkeeping of 5.22: the three bounds give `K P` with
`K = 3240 c3^2 + 144 |c2| + 2 |c4|`. -/
theorem arith_522 {I1 I2 I3 r z0 z Y Lr P c2 c3 c4 : ℝ} (hz0 : z0 ≠ 0) (hr : r = z / z0)
    (hI1 : I1 ≤ 45 / 2 * c3 ^ 2 * z0 ^ 2 * Y ^ 3 * Lr)
    (hI2 : I2 ≤ c2 * z0 ^ 2 * Y ^ 3 * Lr) (hI3 : I3 ≤ c4 * P)
    (hZ0 : 0 ≤ z ^ 2 * Y ^ 3 * Lr) (hZ : z ^ 2 * Y ^ 3 * Lr ≤ 36 * P) :
    4 * r ^ 2 * I1 + 4 * r ^ 2 * I2 + 2 * I3 ≤
      (3240 * c3 ^ 2 + 144 * |c2| + 2 * |c4|) * P := by
  have hrz : r ^ 2 * z0 ^ 2 = z ^ 2 := by
    rw [hr, div_pow]; field_simp
  have hr0 : 0 ≤ 4 * r ^ 2 := by positivity
  have hP : 0 ≤ P := by linarith
  have e1 : 4 * r ^ 2 * I1 ≤ 90 * c3 ^ 2 * (z ^ 2 * Y ^ 3 * Lr) := by
    calc 4 * r ^ 2 * I1 ≤ 4 * r ^ 2 * (45 / 2 * c3 ^ 2 * z0 ^ 2 * Y ^ 3 * Lr) :=
          mul_le_mul_of_nonneg_left hI1 hr0
      _ = 90 * c3 ^ 2 * ((r ^ 2 * z0 ^ 2) * Y ^ 3 * Lr) := by ring
      _ = 90 * c3 ^ 2 * (z ^ 2 * Y ^ 3 * Lr) := by rw [hrz]
  have e2 : 4 * r ^ 2 * I2 ≤ 4 * |c2| * (z ^ 2 * Y ^ 3 * Lr) := by
    calc 4 * r ^ 2 * I2 ≤ 4 * r ^ 2 * (c2 * z0 ^ 2 * Y ^ 3 * Lr) :=
          mul_le_mul_of_nonneg_left hI2 hr0
      _ = 4 * c2 * ((r ^ 2 * z0 ^ 2) * Y ^ 3 * Lr) := by ring
      _ = 4 * c2 * (z ^ 2 * Y ^ 3 * Lr) := by rw [hrz]
      _ ≤ 4 * |c2| * (z ^ 2 * Y ^ 3 * Lr) := by
        apply mul_le_mul_of_nonneg_right _ hZ0
        linarith [le_abs_self c2]
  have e3 : 2 * I3 ≤ 2 * |c4| * P := by
    have : c4 * P ≤ |c4| * P := mul_le_mul_of_nonneg_right (le_abs_self c4) hP
    linarith
  have f1 : 90 * c3 ^ 2 * (z ^ 2 * Y ^ 3 * Lr) ≤ 90 * c3 ^ 2 * (36 * P) :=
    mul_le_mul_of_nonneg_left hZ (by positivity)
  have f2 : 4 * |c2| * (z ^ 2 * Y ^ 3 * Lr) ≤ 4 * |c2| * (36 * P) :=
    mul_le_mul_of_nonneg_left hZ (by positivity)
  nlinarith

/-- P0069 page 52, display 5.23, "Another consequence of (5.21)", in the form of the
hypothesis `h523` of `lower_exceptional_mean_square_of_518_522_523` with the concrete `W` and
`H`. CONDITIONAL on `leaf_521` and `leaf_regularity`. -/
theorem step_523 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          IntervalIntegrable (fun y => ‖perronW ω ε x q y z - z * perronH ω ε x q y‖ ^ 2)
            volume (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖perronW ω ε x q y z - z * perronH ω ε x q y‖ ^ 2 ≤
            C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C3, hC3⟩ := leaf_521 ω hω hz hε hε8 (A / 2) (by linarith)
  refine ⟨max (max C3 1) (810 * C3 ^ 2), fun x hx q hq hqQ z hz1 hz2 => ?_⟩
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
  have hz0 : 0 ≤ z := le_trans (by positivity) hz1
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hLr : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL _
  refine ⟨(leaf_regularity ω ε x hx1 q z hz0).1, ?_⟩
  have hpt := hC3 x hx3 q hq hqQ z (Or.inl ⟨hz1, hz2⟩)
  have hms := mean_square_of_521 hY hz0 (Real.rpow_nonneg hL (-(A / 2)))
    (fun y => perronW ω ε x q y z - z * perronH ω ε x q y) hpt
  rw [rpow_neg_half_sq A hL] at hms
  have hZ := z_sq_Y_cube_le hY hz0 hz2
  have hZ' : z ^ 2 * Y ^ 3 * Real.log x ^ (-A) ≤
      36 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) :=
    mul_le_mul_of_nonneg_right hZ hLr
  have hP : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) := by positivity
  have hc : 810 * C3 ^ 2 ≤ max (max C3 1) (810 * C3 ^ 2) := le_max_right _ _
  have hc3 : 0 ≤ C3 ^ 2 := sq_nonneg _
  calc _ ≤ 45 / 2 * C3 ^ 2 * z ^ 2 * Y ^ 3 * Real.log x ^ (-A) := hms
    _ = 45 / 2 * C3 ^ 2 * (z ^ 2 * Y ^ 3 * Real.log x ^ (-A)) := by ring
    _ ≤ 45 / 2 * C3 ^ 2 * (36 * ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_left hZ' (by positivity)
    _ = 810 * C3 ^ 2 * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) := by ring
    _ ≤ max (max C3 1) (810 * C3 ^ 2) * (((q : ℝ) * sieveQ ε x) ^ 2 * Y *
          Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right hc hP
    _ = _ := by ring

/-- P0069 page 52, display 5.22, "Combining (5.20) with (5.21) for z = z0" and "consequently
(5.22)", in the form of the hypothesis `h522` of `lower_exceptional_mean_square_of_518_522_523`
with the concrete `H` and the lab's main term restricted to J. CONDITIONAL on `leaf_520`,
`leaf_521`, `leaf_count_scale` and `leaf_regularity`. -/
theorem step_522 (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          IntervalIntegrable (fun y => ‖z * perronH ω ε x q y -
              ∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2) volume
            (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖z * perronH ω ε x q y -
                ∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                  ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2 ≤
            C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C2, hC2⟩ := leaf_520 h4 h9 ω hω hz hε hε8 A hA
  obtain ⟨C3, hC3⟩ := leaf_521 ω hω hz hε hε8 (A / 2) (by linarith)
  obtain ⟨C4, hC4⟩ := leaf_count_scale ω hε hε8 A hA
  set M := max (max C2 C3) (max C4 1) with hM
  set K := 3240 * C3 ^ 2 + 144 * |C2| + 2 * |C4| with hK
  have hK0 : 0 ≤ K := by positivity
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨M + K, fun x hx q hq hqQ z hz1 hz2 => ?_⟩
  have hxM : M ≤ x := by linarith
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxM
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxM
  have hx4 : C4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxM
  have hx1 : 1 ≤ x := le_trans hM1 hxM
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
  have hz0 : 0 ≤ z := le_trans (by positivity) hz1
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hLr : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL _
  have hZ0pos := perronZ0_pos x
  have hZ0ne : perronZ0 x ≠ 0 := hZ0pos.ne'
  refine ⟨(leaf_regularity ω ε x hx1 q z hz0).2, ?_⟩
  set c : ℂ := ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) with hc
  set N : ℝ → ℝ → ℂ := fun y w => ∑ m ∈ (rightInterval ε x).filter
    (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w), c with hN
  set z0 := perronZ0 x with hz0def
  set r := z / z0 with hr
  have hz0C : (z0 : ℂ) ≠ 0 := by exact_mod_cast hZ0ne
  have hrz : (r : ℂ) * (z0 : ℂ) = z := by
    rw [hr, Complex.ofReal_div]; exact div_mul_cancel₀ _ hz0C
  obtain ⟨hint2, hb2⟩ := hC2 x hx2 q hq hqQ
  obtain ⟨hint4, hb4⟩ := hC4 x hx4 q hq hqQ z hz1 hz2
  have hint1 := (leaf_regularity ω ε x hx1 q z0 hZ0pos.le).1
  have hpt := hC3 x hx3 q hq hqQ z0 (Or.inr rfl)
  have hms1 := mean_square_of_521 hY hZ0pos.le (Real.rpow_nonneg hL (-(A / 2)))
    (fun y => perronW ω ε x q y z0 - z0 * perronH ω ε x q y) hpt
  rw [rpow_neg_half_sq A hL] at hms1
  have hmain := mean_square_522 (a := Y / 2) (b := 3 * Y) (by linarith) r
    (fun y => (z : ℂ) * perronH ω ε x q y - N y z)
    (fun y => perronW ω ε x q y z0 - z0 * perronH ω ε x q y)
    (fun y => perronW ω ε x q y z0 - N y z0)
    (fun y => (r : ℂ) * N y z0 - N y z)
    (fun y => by
      linear_combination (-(perronH ω ε x q y)) * hrz)
    hint1 hint2 hint4
  have hZ := z_sq_Y_cube_le hY hz0 hz2
  have hZ' : z ^ 2 * Y ^ 3 * Real.log x ^ (-A) ≤
      36 * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) := by
    have := mul_le_mul_of_nonneg_right hZ hLr
    linarith
  have hP : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A) := by positivity
  have hb4' : ∫ y in (Y / 2)..(3 * Y), ‖(r : ℂ) * N y z0 - N y z‖ ^ 2 ≤
      C4 * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) := by
    have := hb4; rw [mul_assoc, mul_assoc] at this
    simpa only [mul_assoc] using this
  have hfin := arith_522 (P := ((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A))
    hZ0ne hr hms1 hb2 hb4' (by positivity) hZ'
  calc _ ≤ _ := hmain
    _ ≤ K * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) := hfin
    _ ≤ (M + K) * (((q : ℝ) * sieveQ ε x) ^ 2 * Y * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right (by linarith) hP
    _ = _ := by ring

/-! ### Assembly -/

/-- P0069 Baker Harman Pintz 1997, Section 5, page 52, "Now (1.9) follows from (5.18), (5.23)
and (5.22)", for b0: the exact statement of the sealed leaf
`LowerShortC165.lower_exceptional_mean_square`, from the proved skeleton
`LowerShortMeanSquare.lower_exceptional_mean_square_of_518_522_523` with `W = perronW` and
`H = perronH`. No sorry in this proof. CONDITIONAL ON the five leaves of this file and on
the cited Theorem 4 and Lemma 9. -/
theorem lower_exceptional_mean_square_split (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  lower_exceptional_mean_square_of_518_522_523 ω (perronW ω ε) (perronH ω ε)
    (leaf_518 h4 h9 ω hω hz hε hε8) (step_523 ω hω hz hε hε8)
    (step_522 h4 h9 ω hω hz hε hε8)

/-- Twin check: the assembly has exactly the type of the sealed leaf. -/
theorem lower_exceptional_mean_square_split_twin (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    lower_exceptional_mean_square_split h4 h9 ω hω hz hε hε8 =
      LowerShortC165.lower_exceptional_mean_square h4 h9 ω hω hz hε hε8 := rfl

/-- Route assembly, P0069 pages 43 to 52: the statement of the sealed
`DecompC165d.lower_short_weight_analytic`, by its own proof with the sealed
`lower_exceptional_mean_square` replaced by `lower_exceptional_mean_square_split`. No sorry in
this proof. CONDITIONAL ON the five leaves of this file, on whatever open leaves remain under
`LowerShortC165.lower_short_distribution`, and on the cited Theorem 4 and Lemma 9. -/
theorem lower_short_weight_analytic_split (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9) :
    ∃ ω : ℝ → ℝ,
      LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω ∧
      LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω ∧
      ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
        ∃ (v0 : ℝ) (b0 : ℝ → ℕ → ℝ),
          1 - lowerTwoDeletedIntegral ω ε - lowerFourDeletedIntegral ω ε ≤ v0 ∧
          RightConditions ε B v0 b0 ∧
          ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
            ∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m := by
  obtain ⟨ω, hω, hz⟩ := Task308.buchstab_model_exists
  refine ⟨ω, hω, hz, 4, 1/10^8, by norm_num, ?_⟩
  intro B ε hB hε hεη
  have hε8 : ε ≤ 1/10^8 := hεη.le
  refine ⟨LowerShortC165.lowerV0 ω ε, LowerShortC165.lowerShortWeight ω ε, le_rfl,
    ⟨LowerShortC165.lowerShortWeight_divisor_bound ω ε hB,
      LowerShortC165.lower_short_distribution ω hω hz hε hε8,
      lower_exceptional_mean_square_split h4 h9 ω hω hz hε hε8⟩,
    0, fun x _ m _ => LowerShortC165.lowerShortWeight_le_primeWeight ω ε x m⟩

/-- Twin check against the sealed route theorem. -/
theorem lower_short_weight_analytic_split_twin (h4 : Thm4.Theorem4Paper)
    (h9 : MeanValue132.Lemma9) :
    lower_short_weight_analytic_split h4 h9 =
      DecompC165d.lower_short_weight_analytic h4 h9 := rfl

end LeanLab.BHP1997.DQLowerExceptionalMeanSquare
