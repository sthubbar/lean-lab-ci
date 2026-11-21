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

Update, burst 2026-11-20b: `leaf_count_scale` and `leaf_regularity` are PROVED. `leaf_518` is
proved from three LEAFs in DQLeaf518Split.lean and `leaf_521` from one cited LEAF in
SPLIT_leaf_521.lean. `leaf_520` keeps its sorry here; DQLowerExceptional520Split.lean proves
its exact type from two LEAFs, `leaf_520_of_subleaves`. See notes/burst-20261120b/.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerShortMeanSquare
import LeanLab.BHP1997.DecompC165d
import LeanLab.BHP1997.SPLIT_leaf_521
import LeanLab.BHP1997.DQLeaf518Split

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
  -- Burst 2026-11-20b, U3a: SPLIT into `DQLeaf518Split`, "Lemma 29 yields (5.18)".
  obtain ⟨E, hE⟩ := DQLeaf518Split.leaf_518_E_M0 h4 h9 ω hω hz hε hε8
  have h29 := DQLeaf518Split.leaf_lemma29 (lowerShortWeight ω ε) (B := 4) hε
    (lowerShortWeight_divisor_bound ω ε (le_refl 4)) E
    (fun A hA A' hA' => by
      obtain ⟨C, hC⟩ := hE A hA A' hA'
      exact ⟨C, fun x hx q hq1 hqQ => (hC x hx q hq1 hqQ).2⟩)
    (DQLeaf518Split.leaf_518_M1 h4 h9 ω hω hz hε hε8)
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C1, hC1⟩ := hE A hA A hA
  obtain ⟨C2, hC2⟩ := h29 A hA
  refine ⟨max (max C1 C2) 1, fun x hx q hq1 hqQ => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hM1 : C1 ≤ max (max C1 C2) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : C2 ≤ max (max C1 C2) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hL : ∀ r : ℝ, 0 ≤ Real.log x ^ r := fun r => Real.rpow_nonneg (Real.log_nonneg hx3) r
  refine ⟨?_, fun z hz1 hz2 => ⟨fun χ => ?_, ?_⟩⟩
  · refine ((hC1 x hx1 q hq1 hqQ).1).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hM1 (Real.rpow_nonneg (Nat.cast_nonneg q) _)) (hL _)
  · have hz0 : 0 ≤ z := le_trans (div_nonneg (by positivity) (by positivity)) hz1
    unfold perronW lowerG perronT0
    exact DQLeaf518Split.leaf_lemma29_integrable (lowerShortWeight ω ε) ε x hx3 q χ z hz0
  · unfold perronW lowerG perronT0
    refine (hC2 x hx2 q hq1 hqQ z hz1 hz2).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hM2 (by positivity)) hY.le) (hL _)

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

/-! ### Helpers for `leaf_521`, burst 2026-11-20b unit U3c. AI wrote the Lean code. -/

/-- Copied pattern of `Decomp312c.eventually_low_height_le_power`, which is private there. -/
theorem eventually_T0_le_power521 {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℝ in Filter.atTop, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ α := by
  have hs : ∀ᶠ u : ℝ in Filter.atTop, u ^ (-(2 / 3 : ℝ)) < α :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually
      (eventually_lt_nhds hα)
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Filter.eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 < Real.log x := Real.log_pos hx1
  have he : Real.log x ^ (1 / 3 : ℝ) = Real.log x * Real.log x ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = Real.log x ^ ((1 : ℝ) + (-(2 / 3 : ℝ))) := by norm_num
      _ = _ := by rw [Real.rpow_add hl, Real.rpow_one]
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  apply Real.exp_le_exp.mpr
  rw [he]
  exact mul_le_mul_of_nonneg_left hx.le hl.le

/-- Copied pattern of `Decomp312c.eventually_log_power_le_low_height`, with the square root
of the low height. -/
theorem eventually_log_power_le_sqrt_T0_521 (D : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ D ≤ Real.sqrt (Real.exp (Real.log x ^ (1 / 3 : ℝ))) := by
  have hs : ∀ᶠ u : ℝ in Filter.atTop, (2 * D) * Real.log u ≤ u ^ (1 / 3 : ℝ) := by
    filter_upwards [((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul_left
      (2 * D)).bound (by norm_num : (0 : ℝ) < 1), Filter.eventually_ge_atTop (0 : ℝ)] with u hu hu0
    have h : |(2 * D) * Real.log u| ≤ u ^ (1 / 3 : ℝ) := by
      simpa only [one_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hu0 _)] using hu
    exact (le_abs_self _).trans h
  filter_upwards [Real.tendsto_log_atTop.eventually hs,
    Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with x hx hx0
  have hsq : Real.sqrt (Real.exp (Real.log x ^ (1 / 3 : ℝ))) =
      Real.exp (Real.log x ^ (1 / 3 : ℝ) / 2) := by
    rw [show Real.exp (Real.log x ^ (1 / 3 : ℝ)) = Real.exp (Real.log x ^ (1 / 3 : ℝ) / 2) ^ 2 by
      rw [sq, ← Real.exp_add]; ring_nf]
    exact Real.sqrt_sq (Real.exp_pos _).le
  rw [hsq, Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Page 52, continuity of `y^s` on the contour `s = 1/2 + it`. -/
theorem cont_cpow521 {b : ℝ} (hb : 0 < b) :
    Continuous fun t : ℝ => (b : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
  Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hb.ne'))

/-- Page 52, `s = 1/2 + it` is never zero. -/
theorem s_ne_zero521 (t : ℝ) : (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- Pages 43 and 52, `W(y, z) - z H(y)` is the contour integral of `G y^s k(s)`,
`k(s) = ((1 + z)^s - 1)/s - z`, for any continuous `G`. -/
theorem diff_identity521 (g : ℝ → ℂ) (hg : Continuous g) (y z T : ℝ) (hy : 0 < y)
    (hz : 0 ≤ z) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, g t *
      ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I)) -
      (z : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T,
        g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
        ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ)) := by
  have hyz : 0 < y + y * z := by positivity
  have hs : Continuous fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I := by fun_prop
  have hA : Continuous fun t : ℝ => g t *
      ((((y + y * z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) -
        (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) / ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    (hg.mul ((cont_cpow521 hyz).sub (cont_cpow521 hy))).div hs s_ne_zero521
  have hB : Continuous fun t : ℝ => g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) :=
    hg.mul (cont_cpow521 hy)
  have e1 : (z : ℂ) * (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T,
        g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T,
        (z : ℂ) * (g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    rw [intervalIntegral.integral_const_mul]; ring
  have hB' : Continuous fun t : ℝ => (z : ℂ) * (g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) :=
    continuous_const.mul hB
  rw [e1, ← mul_sub, ← intervalIntegral.integral_sub (hA.intervalIntegrable (-T) T)
      (hB'.intervalIntegrable (-T) T)]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hsplit : (((y + y * z : ℝ)) : ℂ) = (y : ℂ) * (((1 + z : ℝ)) : ℂ) := by
    push_cast; ring

  rw [hsplit, Complex.mul_cpow_ofReal_nonneg hy.le (by linarith)]
  have := s_ne_zero521 t
  field_simp
/-- Page 52, display 5.21, the kernel: `|((1 + z)^s - 1)/s - z| ≤ (|s| + 1) z^2` when
`|s| z ≤ 1`. -/
theorem kernel521 (z : ℝ) (hz : 0 ≤ z) (s : ℂ) (hs : s ≠ 0) (hsz : ‖s‖ * z ≤ 1) :
    ‖((((1 + z : ℝ)) : ℂ) ^ s - 1) / s - (z : ℂ)‖ ≤ (‖s‖ + 1) * z ^ 2 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  set ℓ : ℝ := Real.log (1 + z) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓz : ℓ ≤ z := by
    have := Real.log_le_sub_one_of_pos h1z; linarith
  have hzℓ : z - ℓ ≤ z ^ 2 := by
    have h := Real.one_sub_inv_le_log_of_pos h1z
    have : 1 - (1 + z)⁻¹ = z / (1 + z) := by field_simp; ring
    rw [this] at h
    have h2 : z - z / (1 + z) = z ^ 2 / (1 + z) := by field_simp; ring
    have h3 : z ^ 2 / (1 + z) ≤ z ^ 2 := div_le_self (by positivity) (by linarith)
    linarith
  have hcp : (((1 + z : ℝ)) : ℂ) ^ s = cexp ((ℓ : ℂ) * s) := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast h1z.ne'), hℓ, ofReal_log h1z.le]
  set w : ℂ := (ℓ : ℂ) * s with hw
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hwn : ‖w‖ = ℓ * ‖s‖ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ0]
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hwn]; nlinarith
  have hE := norm_exp_sub_one_sub_id_le hw1
  have hsplit : (cexp w - 1) / s - (z : ℂ) = (cexp w - 1 - w) / s + ((ℓ : ℂ) - z) := by
    rw [hw]; field_simp; ring
  rw [hcp, hsplit]
  calc ‖(cexp w - 1 - w) / s + ((ℓ : ℂ) - z)‖
      ≤ ‖(cexp w - 1 - w) / s‖ + ‖((ℓ : ℂ) - z)‖ := norm_add_le _ _
    _ ≤ ‖s‖ * z ^ 2 + z ^ 2 := by
        gcongr
        · rw [norm_div]
          rw [div_le_iff₀ hsn]
          calc ‖cexp w - 1 - w‖ ≤ ‖w‖ ^ 2 := hE
            _ = ℓ ^ 2 * ‖s‖ ^ 2 := by rw [hwn]; ring
            _ ≤ z ^ 2 * ‖s‖ ^ 2 := by gcongr
            _ = ‖s‖ * z ^ 2 * ‖s‖ := by ring
        · rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          linarith
    _ = (‖s‖ + 1) * z ^ 2 := by ring
/-- Page 52, the mean value step: `∫ |F| ≤ K (T λ + M / (2 λ))` when `|F| ≤ K |g|` and
`∫ |g|^2 ≤ M`, by `2|g| ≤ λ + |g|^2/λ`. -/
theorem amgm_integral521 (g F : ℝ → ℂ) (hg : Continuous g) (T lam M K : ℝ) (hT : 0 ≤ T)
    (hlam : 0 < lam) (hK : 0 ≤ K)
    (hF : ∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ K * ‖g t‖) (hFi : Continuous F)
    (hM : ∫ t in (-T)..T, ‖g t‖ ^ 2 ≤ M) :
    ‖∫ t in (-T)..T, F t‖ ≤ K * (T * lam + M / (2 * lam)) := by
  have hTT : -T ≤ T := by linarith
  have hgi : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (-T) T :=
    ((hg.norm).pow 2).intervalIntegrable _ _
  have h1 : ‖∫ t in (-T)..T, F t‖ ≤ ∫ t in (-T)..T, ‖F t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hTT
  have h2 : ∫ t in (-T)..T, ‖F t‖ ≤
      ∫ t in (-T)..T, (K * (lam / 2) + (K / (2 * lam)) * ‖g t‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hTT (hFi.norm.intervalIntegrable _ _)
    · exact (continuous_const.add (continuous_const.mul ((hg.norm).pow 2))).intervalIntegrable _ _
    intro t ht
    have hpt := hF t ht
    have hsq : ‖g t‖ ≤ lam / 2 + ‖g t‖ ^ 2 / (2 * lam) := by
      rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖g t‖ - lam)]
    calc ‖F t‖ ≤ K * ‖g t‖ := hpt
      _ ≤ K * (lam / 2 + ‖g t‖ ^ 2 / (2 * lam)) := mul_le_mul_of_nonneg_left hsq hK
      _ = K * (lam / 2) + (K / (2 * lam)) * ‖g t‖ ^ 2 := by ring
  have h3 : ∫ t in (-T)..T, (K * (lam / 2) + (K / (2 * lam)) * ‖g t‖ ^ 2) =
      (T - -T) * (K * (lam / 2)) + (K / (2 * lam)) * ∫ t in (-T)..T, ‖g t‖ ^ 2 := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hgi.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  have h4 : (K / (2 * lam)) * ∫ t in (-T)..T, ‖g t‖ ^ 2 ≤ (K / (2 * lam)) * M :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  calc ‖∫ t in (-T)..T, F t‖ ≤ _ := h1.trans (h2.trans_eq h3)
    _ ≤ (T - -T) * (K * (lam / 2)) + (K / (2 * lam)) * M := by linarith
    _ = K * (T * lam + M / (2 * lam)) := by field_simp; ring

/-- Page 52, display 5.21 for a continuous `G` with mean square at most `M` on `[-T, T]`:
the contour integral is at most `2 z (y + M/2) / √T` when `z ≤ 1/T^2`, `T ≥ 2`. -/
theorem contour_bound521 (g : ℝ → ℂ) (hg : Continuous g) (y z T M : ℝ) (hy : 0 < y)
    (hz : 0 ≤ z) (hT : 2 ≤ T) (hzT : z ≤ 1 / T ^ 2)
    (hM : ∫ t in (-T)..T, ‖g t‖ ^ 2 ≤ M) :
    ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
        ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ))‖ ≤ 2 * z * (y + M / 2) / Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hTT : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0.le
  have hzT2 : z * T ^ 2 ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hzT; linarith
  set K : ℝ := Real.sqrt y * (T + 2) * z ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ t ∈ Set.Icc (-T) T, ‖g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
        ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ))‖ ≤ K * ‖g t‖ := by
    intro t ht
    have hts : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have hsn : ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ≤ T + 1 := by
      calc ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = 1 / 2 + |t| := by simp
        _ ≤ T + 1 := by linarith
    have hsz : ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ * z ≤ 1 := by
      calc ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ * z ≤ (T + 1) * z := mul_le_mul_of_nonneg_right hsn hz
        _ ≤ 1 := by nlinarith
    have hk := kernel521 z hz _ (s_ne_zero521 t) hsz
    have hy2 : ‖(y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ = Real.sqrt y := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, Real.sqrt_eq_rpow]; simp
    rw [norm_mul, norm_mul, hy2]
    calc ‖g t‖ * Real.sqrt y * ‖(((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
          ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ))‖
        ≤ ‖g t‖ * Real.sqrt y * ((‖(1 / 2 : ℂ) + (t : ℂ) * I‖ + 1) * z ^ 2) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ ‖g t‖ * Real.sqrt y * ((T + 2) * z ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = K * ‖g t‖ := by rw [hK]; ring
  have hc : Continuous fun t : ℝ => g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
        ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ)) := by
    have h1z : (0 : ℝ) < 1 + z := by linarith
    exact (hg.mul (cont_cpow521 hy)).mul ((((cont_cpow521 h1z).sub continuous_const).div
      (by fun_prop) s_ne_zero521).sub continuous_const)
  have hlam : 0 < Real.sqrt y / Real.sqrt T := div_pos hsy hsT
  have hA := amgm_integral521 g _ hg T (Real.sqrt y / Real.sqrt T) M K hT0.le hlam hK0 hpt hc hM
  have hcn : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    nlinarith [Real.pi_gt_three]
  rw [norm_mul]
  have hI0 : 0 ≤ ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
        ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ))‖ := norm_nonneg _
  have hM0 : 0 ≤ M := le_trans (intervalIntegral.integral_nonneg (by linarith)
    (fun t _ => by positivity)) hM
  have heq : K * (T * (Real.sqrt y / Real.sqrt T) + M / (2 * (Real.sqrt y / Real.sqrt T))) =
      (T + 2) * z ^ 2 * Real.sqrt T * (y + M / 2) := by
    have halg : ∀ a b : ℝ, 0 < a → 0 < b → a * (b ^ 2 + 2) * z ^ 2 *
        (b ^ 2 * (a / b) + M / (2 * (a / b))) = (b ^ 2 + 2) * z ^ 2 * b * (a ^ 2 + M / 2) := by
      intro a b ha hb
      field_simp
    have := halg (Real.sqrt y) (Real.sqrt T) hsy hsT
    rw [hTT, hyy] at this
    rw [hK]; exact this
  have hfin : (T + 2) * z ^ 2 * Real.sqrt T * (y + M / 2) ≤ 2 * z * (y + M / 2) / Real.sqrt T := by
    rw [le_div_iff₀ hsT]
    have hA0 : 0 ≤ y + M / 2 := by positivity
    have : (T + 2) * z ^ 2 * Real.sqrt T * Real.sqrt T ≤ 2 * z := by
      rw [mul_assoc _ (Real.sqrt T), ← sq, hTT]
      have h1 : (T + 2) * z ^ 2 * T ≤ (2 * T) * z ^ 2 * T := by
        apply mul_le_mul_of_nonneg_right _ hT0.le
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg z)
        linarith
      have h2 : (2 * T) * z ^ 2 * T = 2 * z * (z * T ^ 2) := by ring
      have h3 : 2 * z * (z * T ^ 2) ≤ 2 * z * 1 := mul_le_mul_of_nonneg_left hzT2 (by linarith)
      linarith
    nlinarith
  calc _ ≤ 1 * ‖∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
      (((((1 + z : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
        ((1 / 2 : ℂ) + (t : ℂ) * I) - (z : ℂ))‖ := mul_le_mul_of_nonneg_right hcn hI0
    _ ≤ _ := by rw [one_mul]; exact hA.trans (heq ▸ hfin)

/-- Page 3, the definition of Q: `Q ≤ Y^(1/16)` when `Y ≥ 1`. Same proof as
`DecompC165b.sieveQ_le_sixteenth_power`, which is outside this file's import closure. -/
theorem sieveQ_le_sixteenth521 {ε x : ℝ} (hY : 1 ≤ x ^ (11 / 20 + ε)) :
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
  intro A hA
  obtain ⟨c, CG, hG⟩ := SPLITLeaf521.lowerG_mean_square ω hε
  set c0 : ℝ := max c 0 with hc0
  have ev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 10 : ℝ) ∧ 6 ≤ x ^ (1 / 10 : ℝ) ∧
      Real.log x ^ (c0 + A) ≤ Real.sqrt (Real.exp (Real.log x ^ (1 / 3 : ℝ))) ∧
      Real.exp 1 ≤ x ∧ CG ≤ x := by
    have h6 : ∀ᶠ x : ℝ in Filter.atTop, 6 ≤ x ^ (1 / 10 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop 6
    filter_upwards [eventually_T0_le_power521 (by norm_num : (0 : ℝ) < 1 / 10), h6,
      eventually_log_power_le_sqrt_T0_521 (c0 + A), Filter.eventually_ge_atTop (Real.exp 1),
      Filter.eventually_ge_atTop CG] with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ev
  refine ⟨max X (2 * (1 + |CG|)), ?_⟩
  intro x hx q hq1 hqQ z' hz' y hy
  obtain ⟨hT10, h610, hLD, hxe, hxCG⟩ := hX x (le_trans (le_max_left _ _) hx)
  have hx1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  have hL0 : 0 < Real.log x := by linarith
  set T : ℝ := perronT0 x with hTdef
  have hTe : T = Real.exp (Real.log x ^ (1 / 3 : ℝ)) := rfl
  set Y : ℝ := x ^ (11 / 20 + ε) with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hx1 (by linarith)
  have hT2 : 2 ≤ T := by
    rw [hTe]
    have h1 : 1 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have h2 : Real.exp 1 ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) := Real.exp_le_exp.mpr h1
    have h3 := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hT0 : 0 < T := by linarith
  have hTY : T ≤ Y := by
    rw [← hTe] at hT10
    exact hT10.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hy0 : 0 < y := by have := hy.1; linarith
  have hYy : Y ≤ 2 * y := by have := hy.1; linarith
  -- the range of z'
  have hzT : 0 ≤ z' ∧ z' ≤ 1 / T ^ 2 := by
    rcases hz' with ⟨hlo, hhi⟩ | rfl
    · refine ⟨le_trans (by positivity) hlo, hhi.trans ?_⟩
      have hQ := sieveQ_le_sixteenth521 (ε := ε) (x := x) hY1
      have hqQ' : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
      have hQ0 : (0 : ℝ) ≤ sieveQ ε x := Nat.cast_nonneg _
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      have hY16 : 0 ≤ Y ^ (1 / 16 : ℝ) := Real.rpow_nonneg (by linarith) _
      have hqQY : (q : ℝ) * sieveQ ε x ≤ Y ^ (1 / 16 : ℝ) * Y ^ (1 / 16 : ℝ) :=
        mul_le_mul (hqQ'.trans hQ) hQ hQ0 hY16
      have hYY : Y ^ (1 / 16 : ℝ) * Y ^ (1 / 16 : ℝ) = x ^ ((11 / 20 + ε) / 8) := by
        rw [← Real.rpow_add (by linarith), hYdef, ← Real.rpow_mul hx0.le]; ring_nf
      have hT2' : T ^ 2 ≤ x ^ (2 / 10 : ℝ) := by
        rw [← hTe] at hT10
        calc T ^ 2 ≤ (x ^ (1 / 10 : ℝ)) ^ 2 := pow_le_pow_left₀ hT0.le hT10 2
          _ = x ^ (2 / 10 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
      have hsum : x ^ ((11 / 20 + ε) / 8) * x ^ (2 / 10 : ℝ) * x ^ (1 / 10 : ℝ) ≤ Y := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hYdef]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hYpos : 0 < Y := by linarith
      rw [div_le_div_iff₀ hYpos (by positivity)]
      have hx10 : 0 ≤ x ^ (1 / 10 : ℝ) := Real.rpow_nonneg hx0.le _
      have hxa : 0 ≤ x ^ ((11 / 20 + ε) / 8) := Real.rpow_nonneg hx0.le _
      have hxb : 0 ≤ x ^ (2 / 10 : ℝ) := Real.rpow_nonneg hx0.le _
      calc 6 * ↑q * ↑(sieveQ ε x) * T ^ 2 = 6 * ((q : ℝ) * sieveQ ε x) * T ^ 2 := by ring
        _ ≤ x ^ (1 / 10 : ℝ) * x ^ ((11 / 20 + ε) / 8) * x ^ (2 / 10 : ℝ) := by
          apply mul_le_mul _ hT2' (by positivity) (by positivity)
          apply mul_le_mul h610 (hqQY.trans_eq hYY) (by positivity) hx10
        _ ≤ Y := by linarith [hsum, mul_comm (x ^ (1 / 10 : ℝ)) (x ^ ((11 / 20 + ε) / 8))]
        _ = 1 * Y := by ring
    · exact ⟨by unfold perronZ0; positivity, le_of_eq (by rw [perronZ0])⟩
  obtain ⟨hz0, hzT2⟩ := hzT
  -- G on the contour
  set g : ℝ → ℂ := fun t => lowerG ω ε x (1 : DirichletCharacter ℂ q)
    ((1 / 2 : ℂ) + (t : ℂ) * I) with hg
  have hgc : Continuous g := by
    rw [hg]
    unfold lowerG
    refine continuous_finsetSum _ fun m hm => ?_
    have hm1 : 1 ≤ m := by
      unfold rightInterval at hm; rw [Finset.mem_Ioc] at hm; omega
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    exact continuous_const.div (Continuous.const_cpow (by fun_prop) (Or.inl hm0))
      (fun t => Complex.cpow_ne_zero_iff.mpr (Or.inl hm0))
  have hM : ∫ t in (-T)..T, ‖g t‖ ^ 2 ≤ CG * Y * Real.log x ^ c :=
    hG x hxCG q 1 T hT0.le hTY
  have hid : perronW ω ε x q y z' - (z' : ℂ) * perronH ω ε x q y =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, g t * (y : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) *
        (((((1 + z' : ℝ)) : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) - 1) /
          ((1 / 2 : ℂ) + (t : ℂ) * I) - (z' : ℂ)) :=
    diff_identity521 g hgc y z' T hy0 hz0
  rw [hid]
  have hB := contour_bound521 g hgc y z' T (CG * Y * Real.log x ^ c) hy0 hz0 hT2 hzT2 hM
  refine hB.trans ?_
  -- the arithmetic
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have hLc : Real.log x ^ c ≤ Real.log x ^ c0 :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hLc1 : 1 ≤ Real.log x ^ c0 := Real.one_le_rpow hL1 (le_max_right _ _)
  have hLcpos : 0 ≤ Real.log x ^ c := Real.rpow_nonneg hL0.le _
  have hMy : CG * Y * Real.log x ^ c / 2 ≤ |CG| * y * Real.log x ^ c0 := by
    have h1 : CG * Y * Real.log x ^ c ≤ |CG| * Y * Real.log x ^ c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
        hLcpos
    have h2 : |CG| * Y * Real.log x ^ c ≤ |CG| * (2 * y) * Real.log x ^ c0 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hYy (abs_nonneg _)) hLc hLcpos (by positivity)
    linarith
  have hyM : y + CG * Y * Real.log x ^ c / 2 ≤ (1 + |CG|) * y * Real.log x ^ c0 := by
    have : y ≤ y * Real.log x ^ c0 := by nlinarith
    nlinarith
  have hsplit : Real.log x ^ c0 = Real.log x ^ (c0 + A) * Real.log x ^ (-A) := by
    rw [← Real.rpow_add hL0]; ring_nf
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hTD : Real.log x ^ (c0 + A) ≤ Real.sqrt T := by rw [hTe]; exact hLD
  have hkey : Real.log x ^ c0 / Real.sqrt T ≤ Real.log x ^ (-A) := by
    rw [div_le_iff₀ hsT, hsplit]
    calc Real.log x ^ (c0 + A) * Real.log x ^ (-A) ≤ Real.sqrt T * Real.log x ^ (-A) :=
          mul_le_mul_of_nonneg_right hTD hLA
      _ = Real.log x ^ (-A) * Real.sqrt T := by ring
  have hCbig : 2 * (1 + |CG|) ≤ max X (2 * (1 + |CG|)) := le_max_right _ _
  calc 2 * z' * (y + CG * Y * Real.log x ^ c / 2) / Real.sqrt T
      ≤ 2 * z' * ((1 + |CG|) * y * Real.log x ^ c0) / Real.sqrt T := by
        apply div_le_div_of_nonneg_right _ hsT.le
        exact mul_le_mul_of_nonneg_left hyM (by positivity)
    _ = 2 * (1 + |CG|) * z' * y * (Real.log x ^ c0 / Real.sqrt T) := by ring
    _ ≤ 2 * (1 + |CG|) * z' * y * Real.log x ^ (-A) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ max X (2 * (1 + |CG|)) * z' * y * Real.log x ^ (-A) := by
        apply mul_le_mul_of_nonneg_right _ hLA
        apply mul_le_mul_of_nonneg_right _ hy0.le
        exact mul_le_mul_of_nonneg_right hCbig hz0

/-! ### Helpers for `leaf_count_scale`, elementary counting, PROVED. AI wrote the Lean code. -/

theorem countScale_card_zero_low (a b : ℕ) {y w : ℝ} (h : y + y * w < (a : ℝ) + 1) :
    ((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hp
  have h1 : a < m := (Finset.mem_Ioc.mp hm).1
  have h2 : (a : ℝ) + 1 ≤ m := by exact_mod_cast h1
  linarith [hp.2]

theorem countScale_card_zero_high (a b : ℕ) {y w : ℝ} (h : (b : ℝ) < y) :
    ((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m hm hp
  have h1 : m ≤ b := (Finset.mem_Ioc.mp hm).2
  have h2 : (m : ℝ) ≤ b := by exact_mod_cast h1
  linarith [hp.1]

theorem countScale_card_mono (a b : ℕ) {y w w' : ℝ} (hy : 0 ≤ y) (hw : w ≤ w') :
    ((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w)).card ≤
      ((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w')).card := by
  apply Finset.card_le_card
  intro m
  simp only [Finset.mem_filter]
  rintro ⟨hm, h1, h2⟩
  refine ⟨hm, h1, le_trans h2 ?_⟩
  nlinarith

theorem countScale_filter_sub (a b : ℕ) {y w : ℝ} (hy : 0 ≤ y) (hw : 0 ≤ w) :
    (Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w) ⊆
      Finset.Icc ⌈y⌉₊ ⌊y + y * w⌋₊ := by
  intro m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rintro ⟨_, h1, h2⟩
  exact ⟨Nat.ceil_le.mpr h1, (Nat.le_floor_iff (by positivity)).mpr h2⟩

theorem countScale_filter_eq (a b : ℕ) {y w : ℝ} (hy : 0 ≤ y) (hw : 0 ≤ w)
    (ha : (a : ℝ) + 1 ≤ y) (hb : y + y * w ≤ b) :
    (Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w) =
      Finset.Icc ⌈y⌉₊ ⌊y + y * w⌋₊ := by
  apply le_antisymm (countScale_filter_sub a b hy hw)
  intro m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  rintro ⟨h1, h2⟩
  have h1' : y ≤ m := Nat.ceil_le.mp h1
  have h2' : (m : ℝ) ≤ y + y * w := (Nat.le_floor_iff (by positivity)).mp h2
  refine ⟨⟨?_, ?_⟩, h1', h2'⟩
  · have : (a : ℝ) < m := by linarith
    exact_mod_cast this
  · have : (m : ℝ) ≤ b := by linarith
    exact_mod_cast this

/-- Real bounds for the number of integers in `[y, u]`. -/
theorem countScale_Icc_card_bounds {y u : ℝ} (hy : 0 ≤ y) (hyu : y ≤ u) :
    u - y - 1 ≤ ((Finset.Icc ⌈y⌉₊ ⌊u⌋₊).card : ℝ) ∧
      ((Finset.Icc ⌈y⌉₊ ⌊u⌋₊).card : ℝ) ≤ u - y + 1 := by
  rw [Nat.card_Icc]
  have hu : 0 ≤ u := le_trans hy hyu
  have c1 := Nat.le_ceil y
  have c2 := Nat.ceil_lt_add_one hy
  have f1 := Nat.floor_le hu
  have f2 := Nat.lt_floor_add_one u
  have hle : ⌈y⌉₊ ≤ ⌊u⌋₊ + 1 := by
    have : (⌈y⌉₊ : ℝ) < (⌊u⌋₊ : ℝ) + 2 := by linarith
    have : ⌈y⌉₊ < ⌊u⌋₊ + 2 := by exact_mod_cast this
    omega
  rw [Nat.cast_sub hle]
  push_cast
  constructor <;> linarith

theorem countScale_card_le (a b : ℕ) {y w : ℝ} (hy : 0 ≤ y) (hw : 0 ≤ w) :
    (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w)).card : ℝ) ≤
      y * w + 1 := by
  have h := Finset.card_le_card (countScale_filter_sub a b hy hw)
  have h' : (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧
      (m : ℝ) ≤ y + y * w)).card : ℝ) ≤ (Finset.Icc ⌈y⌉₊ ⌊y + y * w⌋₊).card := by
    exact_mod_cast h
  have := (countScale_Icc_card_bounds hy (le_add_of_nonneg_right (mul_nonneg hy hw))).2
  linarith

theorem countScale_card_near (a b : ℕ) {y w : ℝ} (hy : 0 ≤ y) (hw : 0 ≤ w)
    (ha : (a : ℝ) + 1 ≤ y) (hb : y + y * w ≤ b) :
    |(((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w)).card : ℝ)
      - y * w| ≤ 1 := by
  rw [countScale_filter_eq a b hy hw ha hb]
  have := countScale_Icc_card_bounds hy (le_add_of_nonneg_right (mul_nonneg hy hw))
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

/-- Pointwise bound for the scaled count minus the count. -/
theorem countScale_pointwise (a b : ℕ) {y z z0 : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (hzz : z ≤ z0)
    (hz0 : 0 < z0) :
    |z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)|
      ≤ z / z0 + 1 + 2 * y * z *
        ((Set.Icc (((a : ℝ) + 1) / (1 + z0)) ((a : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y +
          (Set.Icc ((b : ℝ) / (1 + z0)) (b : ℝ)).indicator (fun _ => (1 : ℝ)) y) := by
  set N0 := (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) with hN0
  set N := (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ) with hN
  have hr : 0 ≤ z / z0 := div_nonneg hz hz0.le
  have hrz : z / z0 * z0 = z := div_mul_cancel₀ z hz0.ne'
  have h1z : 0 < 1 + z0 := by linarith
  have i1 : 0 ≤ (Set.Icc (((a : ℝ) + 1) / (1 + z0)) ((a : ℝ) + 1)).indicator
      (fun _ => (1 : ℝ)) y := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have i2 : 0 ≤ (Set.Icc ((b : ℝ) / (1 + z0)) (b : ℝ)).indicator
      (fun _ => (1 : ℝ)) y := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hyz : 0 ≤ 2 * y * z := by positivity
  have hmono : N ≤ N0 := Nat.cast_le.mpr (countScale_card_mono a b hy hzz)
  have hNn : 0 ≤ N := by positivity
  -- the crude bound
  have crude : |z / z0 * N0 - N| ≤ z / z0 + 1 + 2 * y * z := by
    have e0 := countScale_card_le a b hy hz0.le
    have e1 := countScale_card_le a b hy hz
    have hN0n : 0 ≤ N0 := by positivity
    rw [abs_le]
    have : z / z0 * N0 ≤ z / z0 * (y * z0 + 1) := mul_le_mul_of_nonneg_left e0 hr
    have : z / z0 * (y * z0 + 1) = y * z + z / z0 := by
      calc z / z0 * (y * z0 + 1) = y * (z / z0 * z0) + z / z0 := by ring
        _ = y * z + z / z0 := by rw [hrz]
    constructor <;> nlinarith
  by_cases hlow : y < ((a : ℝ) + 1) / (1 + z0)
  · have hl : y + y * z0 < (a : ℝ) + 1 := by
      have := (lt_div_iff₀ h1z).mp hlow; linarith
    have h0 : N0 = 0 := by rw [hN0, countScale_card_zero_low a b hl]; simp
    have h0' : N = 0 := le_antisymm (h0 ▸ hmono) hNn
    rw [h0, h0']; simp; positivity
  by_cases hhigh : (b : ℝ) < y
  · have h0 : N0 = 0 := by rw [hN0, countScale_card_zero_high a b hhigh]; simp
    have h0' : N = 0 := le_antisymm (h0 ▸ hmono) hNn
    rw [h0, h0']; simp; positivity
  rw [not_lt] at hlow hhigh
  by_cases hS1 : y ≤ (a : ℝ) + 1
  · have : (Set.Icc (((a : ℝ) + 1) / (1 + z0)) ((a : ℝ) + 1)).indicator
        (fun _ => (1 : ℝ)) y = 1 := Set.indicator_of_mem (show y ∈ Set.Icc (((a : ℝ) + 1) / (1 + z0)) ((a : ℝ) + 1) from ⟨hlow, hS1⟩) _
    rw [this]; nlinarith
  by_cases hS2 : (b : ℝ) / (1 + z0) ≤ y
  · have : (Set.Icc ((b : ℝ) / (1 + z0)) (b : ℝ)).indicator
        (fun _ => (1 : ℝ)) y = 1 := Set.indicator_of_mem (show y ∈ Set.Icc ((b : ℝ) / (1 + z0)) (b : ℝ) from ⟨hS2, hhigh⟩) _
    rw [this]; nlinarith
  rw [not_le] at hS1 hS2
  have hb0 : y + y * z0 ≤ b := by
    have := (lt_div_iff₀ h1z).mp hS2; linarith
  have hb : y + y * z ≤ b := by nlinarith
  have e0 := countScale_card_near a b hy hz0.le hS1.le hb0
  have e1 := countScale_card_near a b hy hz hS1.le hb
  have key : z / z0 * N0 - N = z / z0 * (N0 - y * z0) - (N - y * z) := by
    calc z / z0 * N0 - N = z / z0 * (N0 - y * z0) + y * (z / z0 * z0) - N := by ring
      _ = _ := by rw [hrz]; ring
  rw [key]
  have : |z / z0 * (N0 - y * z0)| ≤ z / z0 := by
    rw [abs_mul, abs_of_nonneg hr]
    calc z / z0 * |N0 - y * z0| ≤ z / z0 * 1 := mul_le_mul_of_nonneg_left e0 hr
      _ = z / z0 := mul_one _
  have := abs_sub (z / z0 * (N0 - y * z0)) (N - y * z)
  nlinarith


theorem countScale_meas (a b : ℕ) (w : ℝ) : Measurable (fun y : ℝ =>
    (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * w)).card : ℝ)) := by
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.measurable_sum
  intro m _
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_id.add (measurable_id.mul_const w)))

theorem countScale_int_indicator_le {lo hi p q : ℝ} (hlh : lo ≤ hi) (hpq : p ≤ q) :
    ∫ y in lo..hi, (Set.Icc p q).indicator (fun _ => (1 : ℝ)) y ≤ q - p := by
  rw [intervalIntegral.integral_of_le hlh, integral_indicator_const _ measurableSet_Icc,
    measureReal_restrict_apply measurableSet_Icc, smul_eq_mul, mul_one]
  calc volume.real (Set.Icc p q ∩ Set.Ioc lo hi) ≤ volume.real (Set.Icc p q) :=
        measureReal_mono Set.inter_subset_left
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    _ = q - p := Real.volume_real_Icc_of_le hpq

theorem countScale_ii_indicator (lo hi p q : ℝ) :
    IntervalIntegrable ((Set.Icc p q).indicator (fun _ => (1 : ℝ))) volume lo hi := by
  have hc : IntervalIntegrable (fun _ => (1 : ℝ)) volume lo hi := intervalIntegrable_const
  exact intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp hc).indicator measurableSet_Icc)

theorem countScale_norm_eq (a b : ℕ) (y z z0 v : ℝ) :
    ‖((z / z0 : ℝ) : ℂ) * (∑ m ∈ (Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0), ((v : ℝ) : ℂ)) -
      ∑ m ∈ (Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        ((v : ℝ) : ℂ)‖ ^ 2 =
      (v * (z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)))
        ^ 2 := by
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have : ((z / z0 : ℝ) : ℂ) * ((((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℂ) * ((v : ℝ) : ℂ)) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℂ) *
        ((v : ℝ) : ℂ) =
      (((v * (z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)))
        : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The mean square of the scaled count minus the count on `[Y/2, 3Y]`. -/
theorem countScale_mean_square (a b : ℕ) {Y z z0 v : ℝ} (hY : 0 < Y) (hz : 0 ≤ z) (hzz : z ≤ z0)
    (hz0 : 0 < z0) :
    IntervalIntegrable (fun y => ‖((z / z0 : ℝ) : ℂ) * (∑ m ∈ (Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0), ((v : ℝ) : ℂ)) -
      ∑ m ∈ (Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        ((v : ℝ) : ℂ)‖ ^ 2) volume (Y / 2) (3 * Y) ∧
    ∫ y in (Y / 2)..(3 * Y), ‖((z / z0 : ℝ) : ℂ) * (∑ m ∈ (Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0), ((v : ℝ) : ℂ)) -
      ∑ m ∈ (Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        ((v : ℝ) : ℂ)‖ ^ 2 ≤
      v ^ 2 * (5 * Y * (z / z0 + 1) ^ 2 + 144 * Y ^ 2 * z ^ 2 * (((a : ℝ) + 1) * z0 + b * z0))
      := by
  simp_rw [countScale_norm_eq]
  set p1 := ((a : ℝ) + 1) / (1 + z0)
  set p2 := (b : ℝ) / (1 + z0)
  set α := z / z0 + 1 with hα
  set β := 144 * Y ^ 2 * z ^ 2 with hβ
  set g : ℝ → ℝ := fun y => v ^ 2 * (2 * α ^ 2 + β *
    ((Set.Icc p1 ((a : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y +
      (Set.Icc p2 (b : ℝ)).indicator (fun _ => (1 : ℝ)) y)) with hg
  have hab : Y / 2 ≤ 3 * Y := by linarith
  have hgi : IntervalIntegrable g volume (Y / 2) (3 * Y) :=
    (intervalIntegrable_const.add
      (((countScale_ii_indicator _ _ _ _).add (countScale_ii_indicator _ _ _ _)).const_mul _)).const_mul _
  have hpt : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), (v * (z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)))
        ^ 2 ≤ g y := by
    intro y hy
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have h := countScale_pointwise a b hy0 hz hzz hz0
    set d := z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)
    set i1 := (Set.Icc p1 ((a : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y
    set i2 := (Set.Icc p2 (b : ℝ)).indicator (fun _ => (1 : ℝ)) y
    have i1b : i1 = 0 ∨ i1 = 1 := by
      simp only [i1, Set.indicator_apply]; split_ifs <;> simp
    have i2b : i2 = 0 ∨ i2 = 1 := by
      simp only [i2, Set.indicator_apply]; split_ifs <;> simp
    have hii : (i1 + i2) ^ 2 ≤ 2 * (i1 + i2) := by
      rcases i1b with h1 | h1 <;> rcases i2b with h2 | h2 <;> rw [h1, h2] <;> norm_num
    have hi0 : 0 ≤ i1 + i2 := by
      rcases i1b with h1 | h1 <;> rcases i2b with h2 | h2 <;> rw [h1, h2] <;> norm_num
    have hα0 : 0 ≤ α := by positivity
    have hyz : 2 * y * z ≤ 6 * Y * z := by nlinarith [hy.2]
    have hyz0 : 0 ≤ 2 * y * z := by positivity
    have hd : d ^ 2 ≤ (α + 2 * y * z * (i1 + i2)) ^ 2 := by
      have := abs_le.mp h
      nlinarith [abs_nonneg d, sq_abs d]
    have h2 : (α + 2 * y * z * (i1 + i2)) ^ 2 ≤ 2 * α ^ 2 + 2 * (2 * y * z) ^ 2 * (i1 + i2) ^ 2 :=
      by nlinarith [sq_nonneg (α - 2 * y * z * (i1 + i2))]
    have h3 : (2 * y * z) ^ 2 ≤ (6 * Y * z) ^ 2 := pow_le_pow_left₀ hyz0 hyz 2
    have h4 : 2 * (2 * y * z) ^ 2 * (i1 + i2) ^ 2 ≤ β * (i1 + i2) := by
      have : 2 * (2 * y * z) ^ 2 * (i1 + i2) ^ 2 ≤ 2 * (6 * Y * z) ^ 2 * (2 * (i1 + i2)) := by
        apply mul_le_mul (by linarith) hii (sq_nonneg _) (by positivity)
      rw [hβ]; nlinarith
    have : d ^ 2 ≤ 2 * α ^ 2 + β * (i1 + i2) := by linarith
    calc (v * d) ^ 2 = v ^ 2 * d ^ 2 := by ring
      _ ≤ v ^ 2 * (2 * α ^ 2 + β * (i1 + i2)) := mul_le_mul_of_nonneg_left this (sq_nonneg v)
  have hmeas : Measurable (fun y => (v * (z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)))
        ^ 2) :=
    ((measurable_const.mul ((measurable_const.mul (countScale_meas a b z0)).sub (countScale_meas a b z))).pow_const 2)
  have hFi : IntervalIntegrable (fun y => (v * (z / z0 * (((Finset.Ioc a b).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0)).card : ℝ) -
      (((Finset.Ioc a b).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)).card : ℝ)))
        ^ 2) volume (Y / 2) (3 * Y) := by
    refine hgi.mono_fun hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hab]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => ?_
    have hgy := hpt y ⟨hy.1.le, hy.2⟩
    dsimp only
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (le_trans (sq_nonneg _) hgy)]
    exact hgy
  refine ⟨hFi, ?_⟩
  have hz0' : 0 ≤ z0 := hz0.le
  have hp1 : p1 ≤ (a : ℝ) + 1 := div_le_self (by positivity) (by linarith)
  have hp2 : p2 ≤ (b : ℝ) := div_le_self (by positivity) (by linarith)
  have hl1 : (a : ℝ) + 1 - p1 ≤ ((a : ℝ) + 1) * z0 := by
    have : ((a : ℝ) + 1) - ((a : ℝ) + 1) * z0 ≤ p1 := by
      rw [le_div_iff₀ (by linarith)]; nlinarith [sq_nonneg z0, (by positivity : (0:ℝ) ≤ (a:ℝ) + 1)]
    linarith
  have hl2 : (b : ℝ) - p2 ≤ b * z0 := by
    have : (b : ℝ) - b * z0 ≤ p2 := by
      rw [le_div_iff₀ (by linarith)]; nlinarith [sq_nonneg z0, (by positivity : (0:ℝ) ≤ (b:ℝ))]
    linarith
  have I1 := countScale_int_indicator_le hab hp1
  have I2 := countScale_int_indicator_le hab hp2
  have hgint : ∫ y in (Y / 2)..(3 * Y), g y = v ^ 2 * (2 * α ^ 2 * (3 * Y - Y / 2) + β *
      ((∫ y in (Y / 2)..(3 * Y), (Set.Icc p1 ((a : ℝ) + 1)).indicator (fun _ => (1 : ℝ)) y) +
       (∫ y in (Y / 2)..(3 * Y), (Set.Icc p2 (b : ℝ)).indicator (fun _ => (1 : ℝ)) y))) := by
    rw [hg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const
        (((countScale_ii_indicator _ _ _ _).add (countScale_ii_indicator _ _ _ _)).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (countScale_ii_indicator _ _ _ _) (countScale_ii_indicator _ _ _ _),
      smul_eq_mul]
    ring
  have hβ0 : 0 ≤ β := by positivity
  calc _ ≤ ∫ y in (Y / 2)..(3 * Y), g y := intervalIntegral.integral_mono_on hab hFi hgi hpt
    _ = _ := hgint
    _ ≤ v ^ 2 * (2 * α ^ 2 * (3 * Y - Y / 2) + β * (((a : ℝ) + 1) * z0 + b * z0)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg v)
        have : β * ((∫ y in (Y / 2)..(3 * Y), (Set.Icc p1 ((a : ℝ) + 1)).indicator
            (fun _ => (1 : ℝ)) y) + (∫ y in (Y / 2)..(3 * Y), (Set.Icc p2 (b : ℝ)).indicator
            (fun _ => (1 : ℝ)) y)) ≤ β * (((a : ℝ) + 1) * z0 + b * z0) :=
          mul_le_mul_of_nonneg_left (by linarith) hβ0
        linarith
    _ = _ := by ring


/-- Final arithmetic for the mean square bound. -/
theorem countScale_arith {Y z z0 T v V M ℓ a b Lr : ℝ}
    (hY : 1 ≤ Y) (hz : 0 ≤ z) (hYz : Y * z ≤ 6 * M) (hz0 : z0 = 1 / T ^ 2) (hT : 0 < T)
    (hv : v ^ 2 ≤ V) (hM : ℓ ≤ M) (hℓ : 0 < ℓ) (hLr : Lr = 1 / ℓ ^ 2) (hℓT : ℓ ≤ T)
    (h6 : 6 * T ^ 2 * ℓ ≤ Y) (hab : a + 1 + b ≤ 3 * Y + 1) (ha0 : 0 ≤ a + 1) (hb0 : 0 ≤ b) :
    v ^ 2 * (5 * Y * (z / z0 + 1) ^ 2 + 144 * Y ^ 2 * z ^ 2 * ((a + 1) * z0 + b * z0)) ≤
      (20736 * V + 20 * V) * (M ^ 2 * Y * Lr) := by
  have hY0 : 0 < Y := by linarith
  have hM0 : 0 < M := by linarith
  have hT2 : 0 < T ^ 2 := by positivity
  have hzz : z / z0 = z * T ^ 2 := by rw [hz0]; field_simp
  -- z T^2 ≤ M / ℓ
  have e1 : z * T ^ 2 ≤ M / ℓ := by
    rw [le_div_iff₀ hℓ]
    have : (Y * z) * (6 * T ^ 2 * ℓ) ≤ (6 * M) * Y := by
      apply mul_le_mul hYz h6 (by positivity) (by positivity)
    nlinarith
  have e2 : 1 ≤ M / ℓ := by rw [le_div_iff₀ hℓ]; linarith
  have e3 : (z / z0 + 1) ^ 2 ≤ 4 * M ^ 2 * Lr := by
    rw [hzz, hLr]
    have h0 : 0 ≤ z * T ^ 2 + 1 := by positivity
    have : z * T ^ 2 + 1 ≤ 2 * (M / ℓ) := by linarith
    calc (z * T ^ 2 + 1) ^ 2 ≤ (2 * (M / ℓ)) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 4 * M ^ 2 * (1 / ℓ ^ 2) := by field_simp; ring
  have e4 : (a + 1) * z0 + b * z0 ≤ 4 * Y * Lr := by
    have hz0' : z0 ≤ Lr := by
      rw [hz0, hLr]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hℓ.le hℓT 2)
    have hz00 : 0 ≤ z0 := by rw [hz0]; positivity
    have : (a + 1) * z0 + b * z0 = (a + 1 + b) * z0 := by ring
    rw [this]
    calc (a + 1 + b) * z0 ≤ (4 * Y) * z0 :=
          mul_le_mul_of_nonneg_right (by linarith) hz00
      _ ≤ 4 * Y * Lr := mul_le_mul_of_nonneg_left hz0' (by positivity)
  have hLr0 : 0 ≤ Lr := by rw [hLr]; positivity
  have e5 : Y ^ 2 * z ^ 2 ≤ 36 * M ^ 2 := by
    have : (Y * z) ^ 2 ≤ (6 * M) ^ 2 := pow_le_pow_left₀ (by positivity) hYz 2
    nlinarith
  have hV : 0 ≤ V := le_trans (sq_nonneg v) hv
  have t1 : 5 * Y * (z / z0 + 1) ^ 2 ≤ 20 * (M ^ 2 * Y * Lr) := by
    have := mul_le_mul_of_nonneg_left e3 (by positivity : (0:ℝ) ≤ 5 * Y)
    nlinarith
  have t2 : 144 * Y ^ 2 * z ^ 2 * ((a + 1) * z0 + b * z0) ≤ 20736 * (M ^ 2 * Y * Lr) := by
    have h1 : 144 * Y ^ 2 * z ^ 2 * ((a + 1) * z0 + b * z0) ≤
        144 * (Y ^ 2 * z ^ 2) * (4 * Y * Lr) := by
      have := mul_le_mul_of_nonneg_left e4 (by positivity : (0:ℝ) ≤ 144 * (Y ^ 2 * z ^ 2))
      nlinarith
    have h2 : 144 * (Y ^ 2 * z ^ 2) * (4 * Y * Lr) ≤ 144 * (36 * M ^ 2) * (4 * Y * Lr) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hP : 0 ≤ M ^ 2 * Y * Lr := by positivity
  have hS : 0 ≤ 5 * Y * (z / z0 + 1) ^ 2 + 144 * Y ^ 2 * z ^ 2 * ((a + 1) * z0 + b * z0) := by
    have : 0 ≤ (a + 1) * z0 + b * z0 := by
      have hz00 : 0 ≤ z0 := by rw [hz0]; positivity
      positivity
    positivity
  calc v ^ 2 * (5 * Y * (z / z0 + 1) ^ 2 + 144 * Y ^ 2 * z ^ 2 * ((a + 1) * z0 + b * z0))
      ≤ V * (5 * Y * (z / z0 + 1) ^ 2 + 144 * Y ^ 2 * z ^ 2 * ((a + 1) * z0 + b * z0)) :=
        mul_le_mul_of_nonneg_right hv hS
    _ ≤ V * (20 * (M ^ 2 * Y * Lr) + 20736 * (M ^ 2 * Y * Lr)) :=
        mul_le_mul_of_nonneg_left (by linarith) hV
    _ = (20736 * V + 20 * V) * (M ^ 2 * Y * Lr) := by ring

/-- Large `x`: with `L = log x`, `L^(A/2) ≤ exp(L^(1/3))`, `6 exp(L^(1/3))^3 ≤ exp(k e L)` and
`1 ≤ e L`. -/
theorem countScale_large {A e k x : ℝ} (hA : 0 < A) (he : 1 / 2 ≤ e) (hk : 1 / 20 ≤ k)
    (hx : Real.exp (max (3 * A) 4 ^ 6) ≤ x) :
    Real.log x ^ (A / 2) ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) ∧
      6 * Real.exp (Real.log x ^ (1 / 3 : ℝ)) ^ 3 ≤ Real.exp (k * e * Real.log x) ∧
      1 ≤ e * Real.log x := by
  set m := max (3 * A) 4 with hm
  have hm4 : 4 ≤ m := le_max_right _ _
  have hmA : 3 * A ≤ m := le_max_left _ _
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  set L := Real.log x with hL
  have hLm : m ^ 6 ≤ L := by
    rw [hL, ← Real.log_exp (m ^ 6)]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hL0 : 0 ≤ L := le_trans (by positivity) hLm
  set s := L ^ (1 / 6 : ℝ) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hL0 _
  have hs6 : s ^ 6 = L := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hs3 : L ^ (1 / 3 : ℝ) = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hsm : m ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 6 < m ^ 6 := pow_lt_pow_left₀ h hs0 (by norm_num)
    linarith
  have hs4 : 4 ≤ s := le_trans hm4 hsm
  have hsA : 3 * A ≤ s := le_trans hmA hsm
  have hlog : Real.log L ≤ 6 * s := by
    have := Real.log_le_rpow_div hL0 (by norm_num : (0:ℝ) < 1 / 6)
    rw [← hs] at this; linarith
  have hLpos : 0 < L := by nlinarith [pow_pos (by linarith : (0:ℝ) < s) 6]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs3, Real.rpow_def_of_pos hLpos]
    apply Real.exp_le_exp.mpr
    have : Real.log L * (A / 2) ≤ 6 * s * (A / 2) :=
      mul_le_mul_of_nonneg_right hlog (by linarith)
    nlinarith
  · rw [hs3, ← Real.exp_nat_mul, ← hs6]
    have h6 : (6 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2
      have h2 := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    calc 6 * Real.exp (((3 : ℕ) : ℝ) * s ^ 2) ≤ Real.exp 2 * Real.exp (((3 : ℕ) : ℝ) * s ^ 2) :=
          mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
      _ = Real.exp (2 + 3 * s ^ 2) := by rw [← Real.exp_add]; norm_num
      _ ≤ Real.exp (k * e * s ^ 6) := by
        apply Real.exp_le_exp.mpr
        have hke : 1 / 40 ≤ k * e := by nlinarith
        have hs2 : 16 ≤ s ^ 2 := by nlinarith
        have hs4' : 256 ≤ s ^ 4 := by nlinarith
        have : 5 * s ^ 2 ≤ k * e * s ^ 6 := by
          have : k * e * s ^ 6 = (k * e * s ^ 4) * s ^ 2 := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        nlinarith
  · have : (4:ℝ) ^ 6 ≤ m ^ 6 := pow_le_pow_left₀ (by norm_num) hm4 6
    nlinarith

set_option maxHeartbeats 1000000 in
/-- The body of `leaf_count_scale` at one `x`, `q`, `z`, with the explicit constant. -/
theorem countScale_leaf_at (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (A : ℝ) (hA : 0 < A) (x : ℝ)
    (hx : max (Real.exp (max (3 * A) 4 ^ 6)) (20736 * lowerV0 ω ε ^ 2 + 20 * lowerV0 ω ε ^ 2) ≤ x)
    (q : ℕ) (hq : 1 ≤ q) (hqQ : q ≤ sieveQ ε x) (z : ℝ)
    (hz1 : (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z)
    (hz2 : z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε)) :
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
          max (Real.exp (max (3 * A) 4 ^ 6)) (20736 * lowerV0 ω ε ^ 2 + 20 * lowerV0 ω ε ^ 2) *
            ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  set V := lowerV0 ω ε ^ 2 with hVdef
  have hxL : Real.exp (max (3 * A) 4 ^ 6) ≤ x := le_trans (le_max_left _ _) hx
  have hxC : 20736 * V + 20 * V ≤ max (Real.exp (max (3 * A) 4 ^ 6)) (20736 * V + 20 * V) :=
    le_max_right _ _
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxL
  have hk : (1 : ℝ) / 20 ≤ 1 / 16 - 1 / 10 ^ 5 := by norm_num
  have he2 : (1 : ℝ) / 2 ≤ 11 / 20 + ε := by linarith
  obtain ⟨hℓT, h6R, heL⟩ := countScale_large hA he2 hk hxL
  have hL0 : 0 < Real.log x := by
    by_contra h; push Not at h; nlinarith
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hYexp : Y = Real.exp ((11 / 20 + ε) * Real.log x) := by
    rw [hYdef, Real.rpow_def_of_pos hxpos]; ring_nf
  have hY1 : 1 ≤ Y := by rw [hYexp]; exact Real.one_le_exp (by linarith)
  have hY0 : 0 < Y := by linarith
  set T := perronT0 x with hTdef
  have hTexp : T = Real.exp (Real.log x ^ (1 / 3 : ℝ)) := rfl
  rw [← hTexp] at hℓT h6R
  have hT1 : 1 ≤ T := Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hT0 : 0 < T := by linarith
  set R := (Y ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) with hRdef
  have hRexp : R = Real.exp ((1 / 16 - 1 / 10 ^ 5) * (11 / 20 + ε) * Real.log x) := by
    rw [hRdef, ← Real.rpow_mul hY0.le, hYdef, ← Real.rpow_mul hxpos.le,
      Real.rpow_def_of_pos hxpos]
    ring_nf
  have h6R' : 6 * T ^ 3 ≤ R := by rw [hRexp]; exact h6R
  have hRY : R ≤ Y := by
    rw [hRexp, hYexp]; apply Real.exp_le_exp.mpr; nlinarith
  have hR3 : R ^ 3 ≤ Y := by
    rw [hRexp, hYexp, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; nlinarith
  have hR0 : 0 ≤ R := by rw [hRexp]; exact (Real.exp_pos _).le
  set Q := (sieveQ ε x : ℝ) with hQdef
  have hQR : Q = (⌊R / 2⌋₊ : ℝ) := rfl
  have hQle : Q ≤ R / 2 := by rw [hQR]; exact Nat.floor_le (by positivity)
  have hQge : R / 2 - 1 < Q := by
    rw [hQR]; have := Nat.lt_floor_add_one (R / 2); linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQ' : (q : ℝ) ≤ Q := by rw [hQdef]; exact_mod_cast hqQ
  set ℓ := Real.log x ^ (A / 2) with hℓdef
  have hℓ0 : 0 < ℓ := Real.rpow_pos_of_pos hL0 _
  have hT3 : T ≤ T ^ 3 := by
    have h := mul_nonneg (mul_nonneg hT0.le (sub_nonneg.2 hT1)) (by linarith : (0 : ℝ) ≤ T + 1)
    have e : T * (T - 1) * (T + 1) = T ^ 3 - T := by ring
    linarith
  have hℓQ : ℓ ≤ Q := by linarith
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact Nat.cast_nonneg _
  set M := (q : ℝ) * Q with hMdef
  have hℓM : ℓ ≤ M := by
    have := mul_le_mul_of_nonneg_right hq1 hQ0
    rw [hMdef]; linarith
  have h6 : 6 * T ^ 2 * ℓ ≤ Y := by
    have h1 := mul_le_mul_of_nonneg_left hℓT (by positivity : (0 : ℝ) ≤ 6 * T ^ 2)
    have e : 6 * T ^ 2 * T = 6 * T ^ 3 := by ring
    linarith
  have hz0 : 0 ≤ z := le_trans (by positivity) hz1
  have hYz : Y * z ≤ 6 * M := by
    have := (le_div_iff₀ hY0).mp hz2
    rw [hMdef]; linarith
  have hZ0 : perronZ0 x = 1 / T ^ 2 := rfl
  have hzz0 : z ≤ perronZ0 x := by
    rw [hZ0, le_div_iff₀ (by positivity)]
    have hQ2 : M ≤ Q * Q := mul_le_mul_of_nonneg_right hqQ' (by positivity)
    have hQ2' : Q * Q ≤ (R / 2) * (R / 2) := mul_le_mul hQle hQle (by positivity) (by positivity)
    have h15 : 3 / 2 * T ^ 2 ≤ R := by
      have h1 : T ^ 2 * 1 ≤ T ^ 2 * T := mul_le_mul_of_nonneg_left hT1 (by positivity)
      have e : T ^ 2 * T = T ^ 3 := by ring
      have h2 : (0 : ℝ) ≤ T ^ 2 := by positivity
      linarith
    have hzY : Y * z ≤ 3 / 2 * R ^ 2 := by
      have e : (R / 2) * (R / 2) = R ^ 2 / 4 := by ring
      linarith
    have : Y * (z * T ^ 2) ≤ Y * 1 := by
      have e1 : Y * (z * T ^ 2) = (Y * z) * T ^ 2 := by ring
      rw [e1]
      calc (Y * z) * T ^ 2 ≤ (3 / 2 * R ^ 2) * T ^ 2 :=
            mul_le_mul_of_nonneg_right hzY (by positivity)
        _ = R ^ 2 * (3 / 2 * T ^ 2) := by ring
        _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left h15 (by positivity)
        _ = R ^ 3 := by ring
        _ ≤ Y := hR3
        _ = Y * 1 := (mul_one Y).symm
    exact le_of_mul_le_mul_left this hY0
  have hlogY : Real.log Y = (11 / 20 + ε) * Real.log x := by
    rw [hYdef, Real.log_rpow hxpos]
  have hv : (lowerV0 ω ε / Real.log Y) ^ 2 ≤ V := by
    rw [div_pow, hVdef]
    apply div_le_self (sq_nonneg _)
    rw [hlogY]; nlinarith
  have hLr : Real.log x ^ (-A) = 1 / ℓ ^ 2 := by
    have e : Real.log x ^ A = ℓ ^ 2 := by
      rw [hℓdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    rw [Real.rpow_neg hL0.le, e, one_div]
  have hab : ((⌊Y⌋₊ : ℕ) : ℝ) + 1 + ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ 3 * Y + 1 := by
    have h1 : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0.le
    have h2Y : (0 : ℝ) ≤ 2 * Y := by linarith
    have h2 : ((⌊2 * Y⌋₊ : ℕ) : ℝ) ≤ 2 * Y := Nat.floor_le h2Y
    linarith
  obtain ⟨hint, hbd⟩ := countScale_mean_square ⌊Y⌋₊ ⌊2 * Y⌋₊ (v := lowerV0 ω ε / Real.log Y)
    hY0 hz0 hzz0 (by rw [hZ0]; positivity)
  have harith := countScale_arith (v := lowerV0 ω ε / Real.log Y) (V := V)
    (a := ((⌊Y⌋₊ : ℕ) : ℝ)) (b := ((⌊2 * Y⌋₊ : ℕ) : ℝ)) (Lr := Real.log x ^ (-A))
    hY1 hz0 hYz hZ0 hT0 hv hℓM hℓ0 hLr hℓT h6 hab (by positivity) (by positivity)
  have hP : 0 ≤ M ^ 2 * Y * Real.log x ^ (-A) := by
    have := Real.rpow_nonneg hL0.le (-A); positivity
  refine ⟨hint, ?_⟩
  calc _ ≤ _ := hbd
    _ ≤ (20736 * V + 20 * V) * (M ^ 2 * Y * Real.log x ^ (-A)) := harith
    _ ≤ max (Real.exp (max (3 * A) 4 ^ 6)) (20736 * V + 20 * V) *
          (M ^ 2 * Y * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_right hxC hP
    _ = _ := by rw [hMdef]; ring

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
  intro A hA
  exact ⟨_, fun x hx q hq hqQ z hz1 hz2 =>
    countScale_leaf_at ω hε A hA x hx q hq hqQ z hz1 hz2⟩

/-- Helper for `leaf_regularity`: `t ↦ G(1/2 + it, χ0)` is continuous, a finite sum of
`b_m m^(-s)` with `s = 1/2 + it ≠ 0`. -/
theorem lowerG_line_continuous (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) :
    Continuous fun t : ℝ =>
      lowerG ω ε x (1 : DirichletCharacter ℂ q) ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  have hs : Continuous fun t : ℝ => -((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
  have hne : ∀ t : ℝ, -((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  unfold lowerG
  simp_rw [div_eq_mul_inv, ← Complex.cpow_neg]
  exact continuous_finset_sum _ fun m _ =>
    continuous_const.mul (hs.const_cpow (Or.inr hne))

/-- Helper for `leaf_regularity`: the window count is a measurable function of `y`. -/
theorem windowCount_measurable (J : Finset ℕ) (z : ℝ) (κ : ℂ) :
    Measurable fun y : ℝ =>
      ∑ m ∈ J.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), κ := by
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ fun m _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_id.add (measurable_id.mul_const z)))

/-- Helper for `leaf_regularity`: the window count is bounded by the full sum over `J`. -/
theorem windowCount_norm_le (J : Finset ℕ) (z : ℝ) (κ : ℂ) (y : ℝ) :
    ‖∑ m ∈ J.filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), κ‖ ≤
      ∑ _m ∈ J, ‖κ‖ :=
  (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => norm_nonneg _))

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
  intro x hx q z hz
  set κ : ℂ := ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) with hκ
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
  set c := Y / 2 with hc_def
  have hc : 0 < c := by positivity
  have hab : c ≤ 3 * Y := by linarith
  have hs : Continuous fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I := by fun_prop
  have hne : ∀ t : ℝ, (1 / 2 : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
  have hG := lowerG_line_continuous ω ε x q
  have hm : Continuous fun p : ℝ × ℝ => max p.1 c := by fun_prop
  have hmpos : ∀ p : ℝ × ℝ, 0 < max p.1 c := fun p => lt_of_lt_of_le hc (le_max_right _ _)
  -- `W` and `H` with `y` replaced by `max y c` are continuous on all of `ℝ`
  have hWc : Continuous fun y => perronW ω ε x q (max y c) z := by
    unfold perronW
    refine continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
    rw [Function.uncurry_def]
    refine ((hG.comp continuous_snd).mul (Continuous.sub ?_ ?_)).div
      (hs.comp continuous_snd) (fun p => hne p.2)
    · refine Continuous.cpow (by fun_prop) (hs.comp continuous_snd) (fun p => ?_)
      rw [Complex.ofReal_mem_slitPlane]
      have := hmpos p
      positivity
    · refine Continuous.cpow (by fun_prop) (hs.comp continuous_snd) (fun p => ?_)
      rw [Complex.ofReal_mem_slitPlane]
      exact hmpos p
  have hHc : Continuous fun y => perronH ω ε x q (max y c) := by
    unfold perronH
    refine continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
    rw [Function.uncurry_def]
    refine (hG.comp continuous_snd).mul ?_
    refine Continuous.cpow (by fun_prop) (hs.comp continuous_snd) (fun p => ?_)
    rw [Complex.ofReal_mem_slitPlane]
    exact hmpos p
  have hmax : ∀ y, c ≤ y → max y c = y := fun y hy => max_eq_left hy
  constructor
  · have hA : Continuous fun y =>
        ‖perronW ω ε x q (max y c) z - (z : ℂ) * perronH ω ε x q (max y c)‖ ^ 2 :=
      ((hWc.sub (continuous_const.mul hHc)).norm).pow 2
    refine ContinuousOn.intervalIntegrable (hA.continuousOn.congr ?_)
    intro y hy
    rw [Set.uIcc_of_le hab] at hy
    simp only [hmax y hy.1]
  · have hSm := windowCount_measurable (rightInterval ε x) z κ
    have hHz : Continuous fun y => (z : ℂ) * perronH ω ε x q (max y c) :=
      continuous_const.mul hHc
    obtain ⟨MH, hMH⟩ := (isCompact_Icc (a := c) (b := 3 * Y)).exists_bound_of_continuousOn
      hHz.continuousOn
    set B : ℝ := ∑ _m ∈ rightInterval ε x, ‖κ‖ with hB
    have hshift : IntervalIntegrable (fun y => ‖(z : ℂ) * perronH ω ε x q (max y c) -
        ∑ m ∈ (rightInterval ε x).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), κ‖ ^ 2) volume c (3 * Y) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine Measure.integrableOn_of_bounded (M := (MH + B) ^ 2) measure_Ioc_lt_top.ne
        (((hHz.measurable.sub hSm).norm.pow_const 2).aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
      intro y hy
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sub_le _ _).trans (add_le_add (hMH y (Set.Ioc_subset_Icc_self hy))
          (windowCount_norm_le _ z κ y))) 2
    refine (intervalIntegrable_congr ?_).mp hshift
    intro y hy
    rw [Set.uIoc_of_le hab] at hy
    simp only [hmax y hy.1.le]

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
