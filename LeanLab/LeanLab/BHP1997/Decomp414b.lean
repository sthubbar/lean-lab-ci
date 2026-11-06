/-
P0069, page 25, displays 4.3 to 4.5. The two upstream analytic inputs remain OPEN.
Upstream task386 already supplies the analytic split. Reuse its proofs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp312a
import LeanLab.BHP1997.Decomp386b

namespace LeanLab.BHP1997.Decomp414b
open Classical Complex Decomp312c Decomp312a DecompC165c
open scoped BigOperators

/-- Page 25, E of x and chi in display 4.4, parametrized by real height.
The vertical contour differential cancels the factor i in its prefactor. -/
noncomputable def perronCenter (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(Real.exp (Real.log x ^ (1 / 3 : ℝ))),
      (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t) *
        (x : ℂ) ^ (Thm4.half t - 1)

/-- Page 25, the full truncated vertical integral in display 4.3.
Its height is x to the power 0.45 minus two epsilon divided by three.
Source QUESTION: 4.3 prints denominator y. Use denominator s from 4.4
and Heath-Brown 1982 page 1372 display 17. No sealed statement changes. -/
noncomputable def suffixContour (ε : ℝ) (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-x ^ (0.45 - 2 * ε / 3))..(x ^ (0.45 - 2 * ε / 3)),
      (∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
        (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half t) *
        (((x : ℂ) ^ Thm4.half t - ((x - y : ℝ) : ℂ) ^ Thm4.half t) / Thm4.half t)

/-- Page 25, display 4.3. Heath-Brown 1982, page 1372,
displays 15 and 16, supplies the written truncation proof.
The error x to 1 plus epsilon over 4 divided by T1 is exactly the power below.
CONDITIONAL bridge to the existing Decomp386b.truncated_perron_window input.
No duplicate analytic sorry is introduced. -/
theorem truncated_perron (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
          ‖(∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
            suffixContour ε a x χ y‖ ≤
          C * x ^ (0.55 + 11 * ε / 12) := by
  obtain ⟨η, hη, ht⟩ := Decomp386b.truncated_perron_window B
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη a ha A hA
  obtain ⟨C, X, hC⟩ := ht ε hε hεη a ha
  refine ⟨C, X, ?_⟩
  intro x hx q hq hqx χ y hy hyw
  simpa only [suffixContour, Decomp386b.windowContour, Decomp386b.criticalPolynomial] using
    hC x hx q hq χ y hy hyw

/-- Page 25, display 4.4 and the high-height estimate using 4.1.
Heath-Brown 1982, page 1372, displays 17 to 19, writes out this split.
The full integral is compared with its common low-height linear center.
CONDITIONAL on the existing divisor_polynomial_log_bound input in Decomp386b.
Reuse its proved low-height and high-height transfers. -/
theorem contour_center_comparison (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a →
      ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
          ‖suffixContour ε a x χ y -
            (y : ℂ) * perronCenter a x χ‖ ≤
          C * y * Real.log x ^ (-A) := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro ε hε hεu a ha hm A hA
  obtain ⟨Cl, Xl, hl⟩ := Decomp386b.low_height_comparison B a ha A hA
  obtain ⟨Ch, Xh, hh⟩ := Decomp386b.high_height_comparison hε hεu a hm A hA
  refine ⟨|Cl| + |Ch|, max Xl (max Xh 3), ?_⟩
  intro x hx q hq hqx χ y hy hyw
  have hxl : Xl ≤ x := (le_max_left _ _).trans hx
  have hxh : Xh ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : 3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hl0 := hl x hxl q hq χ y hy hyw
  have hh0 := hh x hxh q hq hqx χ y hy hyw
  have hp : 0 ≤ y * Real.log x ^ (-A) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (Decomp386b.windowContour a x y (x ^ (0.45 - 2 * ε / 3)) χ)
    (Decomp386b.windowContour a x y (Real.exp (Real.log x ^ (1 / 3 : ℝ))) χ)
    ((y : ℂ) * Decomp386b.lowCenter a x χ)
  have hbound :
      ‖Decomp386b.windowContour a x y (x ^ (0.45 - 2 * ε / 3)) χ -
        (y : ℂ) * Decomp386b.lowCenter a x χ‖ ≤
        (|Cl| + |Ch|) * y * Real.log x ^ (-A) := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cl) hp,
      mul_le_mul_of_nonneg_right (le_abs_self Ch) hp]
  simpa only [suffixContour, perronCenter, Decomp386b.windowContour,
    Decomp386b.lowCenter, Decomp386b.criticalPolynomial] using hbound

/-- Page 25, display 4.5 before comparing y with y1.
The existing contour supplies give the one-suffix common-center estimate.
CONDITIONAL on the two existing Decomp386b analytic inputs. -/
theorem perron_suffix_center (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a →
      ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ y : ℝ, 2 ≤ y → y ≤ referenceWidth x →
          ‖(∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
            (y : ℂ) * perronCenter a x χ‖ ≤
          C * (y * Real.log x ^ (-A) + x ^ (0.55 + 11 * ε / 12)) := by
  obtain ⟨η0, hη0, ht⟩ := truncated_perron B
  obtain ⟨η1, hη1, hc⟩ := contour_center_comparison B
  refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
  intro ε hε hεη a ha hm A hA
  obtain ⟨C0, X0, h0⟩ := ht ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) a ha A hA
  obtain ⟨C1, X1, h1⟩ := hc ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) a ha hm A hA
  refine ⟨|C0| + |C1|, max X0 (max X1 3), ?_⟩
  intro x hx q hq hqx χ y hy hyw
  have hx0 : X0 ≤ x := (le_max_left _ _).trans hx
  have hx1 : X1 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx3 : 3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hp : 0 ≤ x ^ (0.55 + 11 * ε / 12) := Real.rpow_nonneg (by linarith) _
  have hl : 0 ≤ y * Real.log x ^ (-A) := by
    apply mul_nonneg (by linarith)
    exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have ht0 := h0 x hx0 q hq hqx χ y hy hyw
  have hc0 := h1 x hx1 q hq hqx χ y hy hyw
  calc
    _ ≤ ‖(∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊, (a x k : ℂ) * χ (k : ZMod q)) -
          suffixContour ε a x χ y‖ +
        ‖suffixContour ε a x χ y - (y : ℂ) * perronCenter a x χ‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C0 * x ^ (0.55 + 11 * ε / 12) + C1 * y * Real.log x ^ (-A) := add_le_add ht0 hc0
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C0) hp,
        mul_le_mul_of_nonneg_right (le_abs_self C1) hl,
        mul_nonneg (abs_nonneg C0) hl, mul_nonneg (abs_nonneg C1) hp]

/-- Page 25, finite endpoint correction for a suffix with nonnegative endpoints.
The conservative bound 2 follows from the two Mathlib floor error bounds. -/
theorem suffix_card_error {x y : ℝ} (hy : 0 ≤ y) (hxy : 0 ≤ x - y) :
    |((Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊).card : ℝ) - y| ≤ 2 := by
  exact (Decomp386a.suffix_card_error hy (by linarith)).trans (by norm_num)

/-- Pages 11 and 25, the divisor hypothesis implies a uniform quarter-power
bound for positive-index coefficients. Reuse coeff_small_power_any. -/
theorem coefficient_quarter_bound (B : ℝ) (a : ℝ → ℕ → ℝ)
    (ha : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ x →
      |a x k| ≤ D * x ^ (1 / 4 : ℝ) := by
  obtain ⟨D, hD, hd⟩ := Decomp386b.twisted_coefficient_bound B (1 / 4) (by norm_num) a ha
  refine ⟨D + 1, by linarith, ?_⟩
  intro x k hk hkx
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 1 ≤ x := hkR.trans hkx
  have h := hd x hx1 1 (1 : DirichletCharacter ℂ 1) k hk (by linarith)
  have hχ : (1 : DirichletCharacter ℂ 1) (k : ZMod 1) = 1 := by
    rw [Subsingleton.elim (k : ZMod 1) 1, map_one]
  simp only [hχ, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  nlinarith [Real.rpow_nonneg (show 0 ≤ x by linarith) (1 / 4 : ℝ)]

/-- Page 25, cancel the common contour center between two suffix estimates.
This is finite complex algebra and the triangle inequality. -/
theorem common_center_cancel {s r E : ℂ} {y w e e1 : ℝ}
    (hw : 0 < w) (hy : 0 ≤ y) (hyw : y ≤ w)
    (hs : ‖s - (y : ℂ) * E‖ ≤ e) (hr : ‖r - (w : ℂ) * E‖ ≤ e1) :
    ‖s - ((y / w : ℝ) : ℂ) * r‖ ≤ e + (y / w) * e1 := by
  have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw)
  have hid : s - ((y / w : ℝ) : ℂ) * r =
      (s - (y : ℂ) * E) - ((y / w : ℝ) : ℂ) * (r - (w : ℂ) * E) := by
    push_cast
    field_simp
    <;> ring
  rw [hid]
  calc
    _ ≤ ‖s - (y : ℂ) * E‖ + ‖((y / w : ℝ) : ℂ) * (r - (w : ℂ) * E)‖ := norm_sub_le _ _
    _ = ‖s - (y : ℂ) * E‖ + (y / w) * ‖r - (w : ℂ) * E‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hy hw.le)]
    _ ≤ e + (y / w) * e1 := add_le_add hs (mul_le_mul_of_nonneg_left hr (div_nonneg hy hw.le))

/-- Page 25, the exact original Perron window comparison follows from
one-suffix contour estimates, the divisor bound and finite endpoint algebra.
CONDITIONAL bridge to the exact existing Decomp386b supply.
No direct sorry in this assembly. -/
theorem perron_window_comparison (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a → WindowComparison ε a := by
  exact Decomp386b.perron_window_comparison B

end LeanLab.BHP1997.Decomp414b
