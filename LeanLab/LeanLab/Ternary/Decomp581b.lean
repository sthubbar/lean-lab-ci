/-
MMS https://arxiv.org/abs/1610.02017v2 pages 11 and 12.
Uniform cofactor estimates and ordered prime quadrature are separate inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp571a
import LeanLab.PNTSieve.MertensLower

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory

/-- The ordered prime triples in MMS page 11 equation 5.1.
The fixed bound contains every prime below the fourth root of x. -/
noncomputable def primeTriples (x : ℝ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact ((range (⌊x ^ (1 / 4 : ℝ)⌋₊ + 1)).product
    ((range (⌊x ^ (1 / 4 : ℝ)⌋₊ + 1)).product
      (range (⌊x ^ (1 / 4 : ℝ)⌋₊ + 1)))).filter fun p =>
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧
      x ^ (1 / 10 : ℝ) < p.1 ∧ p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        (p.2.2 : ℝ) < x ^ (1 / 4 : ℝ)

/-- The modulus attached to one ordered prime triple.
MMS page 11 equation 5.1, n equals p one p two p three m. -/
def tripleProduct (p : ℕ × ℕ × ℕ) : ℕ := p.1 * p.2.1 * p.2.2

/-- The actual normalized weighted cofactor sum for a fixed prime triple.
MMS page 11 equation 5.1, before summing over the three primes. -/
noncomputable def cofactorMean (x : ℝ) (p : ℕ × ℕ × ℕ) : ℝ :=
  Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
    if tripleProduct p ∣ n then
      Task379.referenceWeight x n * Task361.roughIndicator (n / tripleProduct p) p.1
    else 0) /
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t)

/-- The Buchstab density for one ordered triple, frozen at the left endpoint.
MMS page 11 bottom display before replacing the prime sums by integrals.
The Jacobian gives log x divided by the modulus and log p one. -/
noncomputable def cofactorModel (x : ℝ) (p : ℕ × ℕ × ℕ) : ℝ :=
  Real.log x / ((tripleProduct p : ℝ) * Real.log p.1) *
    Task571.buchstabModel (Real.log (x / tripleProduct p) / Real.log p.1)

/-- The reciprocal modulus mass controls accumulation of uniform local errors.
Derived error budget for MMS page 11 bottom Buchstab display. -/
noncomputable def tripleMass (x : ℝ) : ℝ :=
  ∑ p ∈ primeTriples x, 1 / (tripleProduct p : ℝ)

/-- The reciprocal modulus mass is nonnegative.
Derived sign check for MMS page 11 bottom display. -/
theorem tripleMass_nonneg (x : ℝ) : 0 ≤ tripleMass x := by
  exact sum_nonneg fun p hp => by positivity

/-- An admissible prime triple has positive modulus.
MMS page 11 equation 5.1. -/
theorem tripleProduct_pos {x : ℝ} {p : ℕ × ℕ × ℕ} (hp : p ∈ primeTriples x) :
    0 < tripleProduct p := by
  classical
  have h := (mem_filter.mp hp).2
  exact Nat.mul_pos (Nat.mul_pos h.1.pos h.2.1.pos) h.2.2.1.pos

/-- The logarithm of a natural floor loses at most log two above two.
Derived endpoint rounding for the prime sum passage on MMS page 11. -/
theorem log_floor_lower {r : ℝ} (hr : 2 ≤ r) :
    Real.log r - Real.log 2 ≤ Real.log (⌊r⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one r
  have hhalf : r / 2 ≤ (⌊r⌋₊ : ℝ) := by linarith
  have hpos : 0 < r / 2 := by linarith
  have hl := Real.log_le_log hpos hhalf
  rwa [Real.log_div (by linarith : r ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at hl

/-- The prime reciprocal mass between the tenth and fourth roots is bounded.
Derived prime sum error budget for MMS page 11 bottom display.
The proved lab Mertens block estimate supplies the arithmetic input. -/
theorem prime_window_mass_le {x : ℝ} (hx : Real.exp 100 ≤ x) :
    (∑ p ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
      (1 : ℝ) / p) ≤ 4 := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 ≤ x := by
    have he := Real.add_one_le_exp (100 : ℝ)
    linarith
  have hlx : 100 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 100) hx
  have hrlog : Real.log (x ^ (1 / 10 : ℝ)) = Real.log x / 10 := by
    rw [Real.log_rpow hx0]; ring
  have hslog : Real.log (x ^ (1 / 4 : ℝ)) = Real.log x / 4 := by
    rw [Real.log_rpow hx0]; ring
  have hr : 3 ≤ x ^ (1 / 10 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    have he := Real.add_one_le_exp (Real.log x * (1 / 10 : ℝ))
    linarith
  have hy : 2 ≤ ⌊x ^ (1 / 10 : ℝ)⌋₊ := Nat.le_floor (by linarith)
  have hys : ⌊x ^ (1 / 10 : ℝ)⌋₊ ≤ ⌊x ^ (1 / 4 : ℝ)⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hly := log_floor_lower (r := x ^ (1 / 10 : ℝ)) (by linarith)
  rw [hrlog] at hly
  have hl2 : Real.log 2 ≤ (1 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hw0 : (0 : ℝ) < ⌊x ^ (1 / 4 : ℝ)⌋₊ := by exact_mod_cast (show 0 < ⌊x ^ (1 / 4 : ℝ)⌋₊ by omega)
  have hlw : Real.log (⌊x ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ Real.log x / 4 := by
    rw [← hslog]
    exact Real.log_le_log hw0 (Nat.floor_le (Real.rpow_nonneg hx0.le _))
  have hly0 : 0 < Real.log (⌊x ^ (1 / 10 : ℝ)⌋₊ : ℝ) := by linarith
  have hM := LeanLab.PNTSieve.Mertens.sum_inv_primes_block
    ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊ hy hys
  apply hM.trans
  apply (div_le_iff₀ hly0).mpr
  linarith

/-- The ordered reciprocal modulus mass is at most the cube of the prime mass.
Derived positive sum comparison for MMS page 11 bottom display. -/
theorem tripleMass_le_cube (x : ℝ) :
    tripleMass x ≤
      (∑ p ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
        (1 : ℝ) / p) ^ 3 := by
  classical
  let S := (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime
  have hsub : primeTriples x ⊆ S.product (S.product S) := by
    intro p hp
    have h := (mem_filter.mp hp).2
    have hmem (q : ℕ) (hq : q.Prime) (hl : x ^ (1 / 10 : ℝ) < q)
        (hu : (q : ℝ) < x ^ (1 / 4 : ℝ)) : q ∈ S := by
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨?_, Nat.le_floor hu.le⟩, hq⟩
      exact (Nat.floor_lt' hq.ne_zero).mpr hl
    have hab : (p.1 : ℝ) < p.2.1 := by exact_mod_cast h.2.2.2.2.1
    have hbc : (p.2.1 : ℝ) < p.2.2 := by exact_mod_cast h.2.2.2.2.2.1
    have ha := hmem p.1 h.1 h.2.2.2.1 ((hab.trans hbc).trans h.2.2.2.2.2.2)
    have hb := hmem p.2.1 h.2.1 (h.2.2.2.1.trans hab) (hbc.trans h.2.2.2.2.2.2)
    have hc := hmem p.2.2 h.2.2.1 (h.2.2.2.1.trans (hab.trans hbc)) h.2.2.2.2.2.2
    exact mem_product.mpr ⟨ha, mem_product.mpr ⟨hb, hc⟩⟩
  calc
    tripleMass x ≤ ∑ p ∈ S.product (S.product S), 1 / (tripleProduct p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hp hp' => by positivity)
    _ = (∑ p ∈ S, (1 : ℝ) / p) ^ 3 := by
      change (∑ p ∈ S ×ˢ (S ×ˢ S), 1 / (tripleProduct p : ℝ)) = _
      simp only [Finset.sum_product, tripleProduct, Nat.cast_mul, one_div, mul_inv_rev]
      simp only [← mul_sum, ← sum_mul]
      ring

/-- Logarithmic prime coordinates lie in the ordered integration region.
MMS page 11 bottom Buchstab display, with beta i equal to log p i over log x. -/
theorem primeTriple_log_coordinates {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ primeTriples x) :
    1 / 10 ≤ Real.log p.1 / Real.log x ∧
      Real.log p.1 / Real.log x ≤ Real.log p.2.1 / Real.log x ∧
      Real.log p.2.1 / Real.log x ≤ Real.log p.2.2 / Real.log x ∧
      Real.log p.2.2 / Real.log x ≤ 1 / 4 := by
  classical
  have h := (mem_filter.mp hp).2
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have h₁ : (0 : ℝ) < p.1 := by exact_mod_cast h.1.pos
  have h₂ : (0 : ℝ) < p.2.1 := by exact_mod_cast h.2.1.pos
  have h₃ : (0 : ℝ) < p.2.2 := by exact_mod_cast h.2.2.1.pos
  have hlo := Real.log_le_log (Real.rpow_pos_of_pos hx0 (1 / 10 : ℝ)) h.2.2.2.1.le
  have hab : Real.log (p.1 : ℝ) ≤ Real.log (p.2.1 : ℝ) :=
    Real.log_le_log h₁ (by exact_mod_cast h.2.2.2.2.1.le)
  have hbc : Real.log (p.2.1 : ℝ) ≤ Real.log (p.2.2 : ℝ) :=
    Real.log_le_log h₂ (by exact_mod_cast h.2.2.2.2.2.1.le)
  have hhi := Real.log_le_log h₃ h.2.2.2.2.2.2.le
  rw [Real.log_rpow hx0] at hlo hhi
  exact ⟨(le_div_iff₀ hlx).mpr (by linarith), div_le_div_of_nonneg_right hab hlx.le,
    div_le_div_of_nonneg_right hbc hlx.le, (div_le_iff₀ hlx).mpr (by linarith)⟩

/-- The frozen cofactor model is exactly the logarithmic coordinate kernel.
MMS page 11 bottom display before the prime density Jacobians are inserted. -/
theorem cofactorModel_log_coordinates {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ primeTriples x) :
    cofactorModel x p =
      Task571.buchstabModel
        ((1 - Real.log p.1 / Real.log x - Real.log p.2.1 / Real.log x -
          Real.log p.2.2 / Real.log x) / (Real.log p.1 / Real.log x)) /
        ((tripleProduct p : ℝ) * (Real.log p.1 / Real.log x)) := by
  classical
  have h := (mem_filter.mp hp).2
  have hx0 : 0 < x := by linarith
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have h₁ : (0 : ℝ) < p.1 := by exact_mod_cast h.1.pos
  have h₂ : (0 : ℝ) < p.2.1 := by exact_mod_cast h.2.1.pos
  have h₃ : (0 : ℝ) < p.2.2 := by exact_mod_cast h.2.2.1.pos
  have hlog : Real.log (p.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast h.1.one_lt)).ne'
  have hprod : (tripleProduct p : ℝ) ≠ 0 := by exact_mod_cast (tripleProduct_pos hp).ne'
  have hpLog : Real.log (tripleProduct p : ℝ) =
      Real.log p.1 + Real.log p.2.1 + Real.log p.2.2 := by
    simp only [tripleProduct, Nat.cast_mul]
    rw [Real.log_mul (mul_ne_zero h₁.ne' h₂.ne') h₃.ne', Real.log_mul h₁.ne' h₂.ne']
  have harg : Real.log (x / tripleProduct p) / Real.log p.1 =
      (1 - Real.log p.1 / Real.log x - Real.log p.2.1 / Real.log x -
        Real.log p.2.2 / Real.log x) / (Real.log p.1 / Real.log x) := by
    rw [Real.log_div hx0.ne' hprod, hpLog]
    field_simp
    <;> ring
  unfold cofactorModel
  rw [harg]
  field_simp
  <;> ring

/-- Every cofactor Buchstab argument lies in the finite model's valid range.
Derived domain check for MMS page 11 bottom display. -/
theorem cofactor_argument_bounds {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ}
    (hp : p ∈ primeTriples x) :
    1 ≤ (1 - Real.log p.1 / Real.log x - Real.log p.2.1 / Real.log x -
      Real.log p.2.2 / Real.log x) / (Real.log p.1 / Real.log x) ∧
    (1 - Real.log p.1 / Real.log x - Real.log p.2.1 / Real.log x -
      Real.log p.2.2 / Real.log x) / (Real.log p.1 / Real.log x) ≤ 7 := by
  obtain ⟨ha, hab, hbc, hc⟩ := primeTriple_log_coordinates hx hp
  exact Task571.profile_argument_bounds ha (hab.trans (hbc.trans hc)) hab (hbc.trans hc) hbc hc

/-- LEAF. Short interval rough cofactor asymptotics hold uniformly over the triples.
MMS page 11 bottom Buchstab display from equation 5.1, continued on page 12.
Apply the Buchstab identity and the prime number theorem in the rescaled
reference interval with the fixed smooth weight. This estimates one cofactor
sum with reciprocal modulus error. It does not sum over the primes and
does not evaluate the ordered triple integral. -/
theorem cofactorMean_uniform :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ p ∈ primeTriples x,
        |cofactorMean x p - cofactorModel x p| ≤ δ / (tripleProduct p : ℝ) := by
  sorry

/-- The ordered prime reciprocal modulus mass stays bounded.
MMS page 11 bottom display, reciprocal modulus bound for the prime sum
to integral passage, used only to control uniform cofactor errors.
This states no rough number asymptotic and no Buchstab integral evaluation. -/
theorem tripleMass_bounded :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → tripleMass x ≤ C := by
  refine ⟨64, by norm_num, Real.exp 100, fun x hx => ?_⟩
  apply (tripleMass_le_cube x).trans
  have h := prime_window_mass_le hx
  have hc := pow_le_pow_left₀
    (show 0 ≤ ∑ p ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
      (1 : ℝ) / p from sum_nonneg fun p hp => by positivity) h 3
  norm_num at hc ⊢
  exact hc

/-- LEAF. The three ordered prime sums of the frozen Buchstab density
converge to the displayed integral.
MMS page 11 bottom display, continued on page 12. Partial summation applies
the prime number theorem successively in each prime coordinate. The
logarithmic coordinates range from one tenth to one quarter in order.
This is only the prime sum to integral passage. The rough cofactor estimate
and its uniform error are excluded. -/
theorem cofactorModel_sum_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x, cofactorModel x p) -
        Task571.profileIntegral Task571.buchstabModel| ≤ δ := by
  sorry

/-- Uniform cofactor errors sum with the reciprocal modulus mass.
Derived finite error estimate for MMS page 11 bottom display.
CONDITIONAL ON the explicitly supplied local cofactor estimates. -/
theorem cofactor_sum_error {x δ : ℝ}
    (h : ∀ p ∈ primeTriples x,
      |cofactorMean x p - cofactorModel x p| ≤ δ / (tripleProduct p : ℝ)) :
    |(∑ p ∈ primeTriples x, cofactorMean x p) -
      ∑ p ∈ primeTriples x, cofactorModel x p| ≤ δ * tripleMass x := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ primeTriples x, |cofactorMean x p - cofactorModel x p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primeTriples x, δ / (tripleProduct p : ℝ) := sum_le_sum h
    _ = δ * tripleMass x := by simp [tripleMass, div_eq_mul_inv, mul_sum]

/-- The summed cofactor mean has the integral limit from two analytic inputs.
The reciprocal modulus mass bound is proved independently.
MMS page 11 bottom display and page 12.
CONDITIONAL ON cofactorMean_uniform and cofactorModel_sum_limit. -/
theorem cofactor_sum_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x, cofactorMean x p) -
        Task571.profileIntegral Task571.buchstabModel| ≤ δ := by
  intro δ hδ
  obtain ⟨C, hC, Xm, hm⟩ := tripleMass_bounded
  obtain ⟨Xu, hu⟩ := cofactorMean_uniform (δ / (2 * C)) (by positivity)
  obtain ⟨Xi, hi⟩ := cofactorModel_sum_limit (δ / 2) (by linarith)
  refine ⟨max Xm (max Xu Xi), fun x hx => ?_⟩
  have hm' := hm x ((le_max_left _ _).trans hx)
  have hu' := hu x ((le_max_left Xu Xi).trans ((le_max_right _ _).trans hx))
  have hi' := hi x ((le_max_right Xu Xi).trans ((le_max_right _ _).trans hx))
  have he := cofactor_sum_error hu'
  have hb : δ / (2 * C) * tripleMass x ≤ δ / 2 := by
    calc
      _ ≤ δ / (2 * C) * C := mul_le_mul_of_nonneg_left hm' (by positivity)
      _ = δ / 2 := by field_simp
  have ha := abs_add_le
    ((∑ p ∈ primeTriples x, cofactorMean x p) - ∑ p ∈ primeTriples x, cofactorModel x p)
    ((∑ p ∈ primeTriples x, cofactorModel x p) - Task571.profileIntegral Task571.buchstabModel)
  rw [sub_add_sub_cancel] at ha
  exact ha.trans (by linarith)

/-- The logarithm weighted prime mass of an integer block has bounded error.
Derived first coordinate prime quadrature step for MMS page 11 bottom display.
The existing lab Mertens upper and lower estimates are reused. -/
theorem prime_log_block_error (y w : ℕ) (hy : 1 ≤ y) (hyw : y ≤ w) :
    |(∑ p ∈ (Ioc y w).filter Nat.Prime, Real.log p / p) -
      (Real.log w - Real.log y)| ≤ 14 := by
  classical
  have hsplit : LeanLab.PNTSieve.Mertens.C w = LeanLab.PNTSieve.Mertens.C y +
      ∑ n ∈ Ioc y w, LeanLab.PNTSieve.Mertens.c n := by
    unfold LeanLab.PNTSieve.Mertens.C
    rw [← sum_union]
    · congr 1
      ext n
      simp only [mem_union, mem_Icc, mem_Ioc]
      omega
    · apply disjoint_left.mpr
      intro n h₁ h₂
      have h₁' := mem_Icc.mp h₁
      have h₂' := mem_Ioc.mp h₂
      omega
  have hblock : (∑ n ∈ Ioc y w, LeanLab.PNTSieve.Mertens.c n) =
      ∑ p ∈ (Ioc y w).filter Nat.Prime, Real.log p / p := by
    rw [sum_filter]
    rfl
  rw [hblock] at hsplit
  have hylo := LeanLab.PNTSieve.Mertens.C_ge y
  have hyhi := LeanLab.PNTSieve.Mertens.C_le y hy
  have hwlo := LeanLab.PNTSieve.Mertens.C_ge w
  have hwhi := LeanLab.PNTSieve.Mertens.C_le w (hy.trans hyw)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Prime logarithm mass on a fixed exponent window has an explicit error.
Derived first coordinate prime sum to integral passage for MMS page 11.
The main term is the length b minus a in logarithmic coordinates.
This is an estimate for the measure used in quadrature, with no Buchstab kernel. -/
theorem prime_log_power_window_error {x a b : ℝ} (hx : 1 < x) (ha : 0 < a)
    (hab : a ≤ b) (hsize : 2 ≤ x ^ a) :
    |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
      Real.log p / p) / Real.log x - (b - a)| ≤
        (14 + 2 * Real.log 2) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hpow : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab
  have hy : 1 ≤ ⌊x ^ a⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hyw := Nat.floor_mono hpow
  have herr := prime_log_block_error ⌊x ^ a⌋₊ ⌊x ^ b⌋₊ hy hyw
  have hloA := log_floor_lower hsize
  have hloB := log_floor_lower (hsize.trans hpow)
  have hfloorA : (0 : ℝ) < ⌊x ^ a⌋₊ := by exact_mod_cast (show 0 < ⌊x ^ a⌋₊ by omega)
  have hfloorB : (0 : ℝ) < ⌊x ^ b⌋₊ := by exact_mod_cast (show 0 < ⌊x ^ b⌋₊ by omega)
  have hhiA := Real.log_le_log hfloorA (Nat.floor_le (Real.rpow_nonneg hx0.le a))
  have hhiB := Real.log_le_log hfloorB (Nat.floor_le (Real.rpow_nonneg hx0.le b))
  rw [Real.log_rpow hx0] at hloA hloB hhiA hhiB
  have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hb : |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
      Real.log p / p) - (b - a) * Real.log x| ≤ 14 + 2 * Real.log 2 := by
    rcases abs_le.mp herr with ⟨h₁, h₂⟩
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have he : (∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
      Real.log p / p) / Real.log x - (b - a) =
      ((∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) - (b - a) * Real.log x) / Real.log x := by
    field_simp
  rw [he, abs_div, abs_of_pos hlx]
  exact div_le_div_of_nonneg_right hb hlx.le

/-- The logarithm weighted prime mass converges to exponent interval length.
Derived primitive quadrature limit for MMS page 11 bottom display.
This supplies interval tests for one prime coordinate, without any rough
cofactor or ordered triple kernel. No cited asymptotic hypothesis is used. -/
theorem prime_log_power_window_limit (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x - (b - a)| ≤ δ := by
  intro δ hδ
  apply Filter.eventually_atTop.mp
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop ha).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop ((14 + 2 * Real.log 2) / δ)]
    with x hx hp hl
  have hx1 : 1 < x := by linarith
  apply (prime_log_power_window_error hx1 ha hab hp).trans
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have h := (div_le_iff₀ hδ).mp hl
  linarith

/-- One equal prime diagonal has small reciprocal modulus mass.
Derived boundary control for the ordered prime quadrature on MMS page 11.
The full prime window is used, so this also bounds every ordered subset. -/
theorem prime_diagonal_mass_le {x : ℝ} (hx : Real.exp 100 ≤ x) :
    (∑ p ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
      ∑ q ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
        1 / ((p : ℝ) ^ 2 * q)) ≤ 16 / x ^ (1 / 10 : ℝ) := by
  classical
  let S := (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx
  have hz : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hS : ∀ p ∈ S, x ^ (1 / 10 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    have h := mem_filter.mp hp
    exact ((Nat.floor_lt' h.2.ne_zero).mp (mem_Ioc.mp h.1).1).le
  have hmass : (∑ p ∈ S, (1 : ℝ) / p) ≤ 4 := prime_window_mass_le hx
  have hmass0 : 0 ≤ ∑ p ∈ S, (1 : ℝ) / p := sum_nonneg fun p hp => by positivity
  have hsquare : (∑ p ∈ S, (1 : ℝ) / p) ^ 2 ≤ 16 := by nlinarith
  calc
    _ ≤ ∑ p ∈ S, ∑ q ∈ S,
        (1 / x ^ (1 / 10 : ℝ)) * ((1 / (p : ℝ)) * (1 / (q : ℝ))) := by
      apply sum_le_sum
      intro p hp
      apply sum_le_sum
      intro q hq
      have hp0 : (0 : ℝ) < p := hz.trans_le (hS p hp)
      have hq0 : (0 : ℝ) < q := hz.trans_le (hS q hq)
      have hi : 1 / (p : ℝ) ≤ 1 / x ^ (1 / 10 : ℝ) :=
        one_div_le_one_div_of_le hz (hS p hp)
      have hm := mul_le_mul_of_nonneg_right hi
        (show 0 ≤ (1 / (p : ℝ)) * (1 / (q : ℝ)) by positivity)
      convert hm using 1 <;> field_simp <;> ring
    _ = (∑ p ∈ S, (1 : ℝ) / p) ^ 2 / x ^ (1 / 10 : ℝ) := by
      simp only [← mul_sum, ← sum_mul]
      ring
    _ ≤ 16 / x ^ (1 / 10 : ℝ) := div_le_div_of_nonneg_right hsquare hz.le

/-- Each equal prime diagonal has vanishing reciprocal modulus mass.
Derived boundary step for MMS page 11 ordered prime sum to integral passage.
This contains no rough number input and no Buchstab kernel approximation. -/
theorem prime_diagonal_mass_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (∑ p ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
        ∑ q ∈ (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime,
          1 / ((p : ℝ) ^ 2 * q)) ≤ δ := by
  intro δ hδ
  apply Filter.eventually_atTop.mp
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 100),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop (16 / δ)]
    with x hx hp
  apply (prime_diagonal_mass_le hx).trans
  apply (div_le_iff₀ (Real.rpow_pos_of_pos ((Real.exp_pos 100).trans_le hx) _)).mpr
  have h := (div_le_iff₀ hδ).mp hp
  linarith

/-- The rescaled reference interval exceeds a fixed short interval power.
Derived interval admissibility for the uniform cofactor step on MMS page 11.
Every ordered triple modulus is at most the three quarter power of x.
This comparison proves no prime distribution estimate. -/
theorem reference_rescaled_length_ge_three_quarters {x d : ℝ}
    (hx : Real.exp 256 ≤ x) (hd : 0 < d) (hdu : d ≤ x ^ (3 / 4 : ℝ)) :
    (x / d) ^ (3 / 4 : ℝ) ≤ Task379.referenceLength x / d := by
  have hx0 : 0 < x := (Real.exp_pos 256).trans_le hx
  have hL : 256 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 256) hx
  have hdlog : Real.log d ≤ (3 / 4 : ℝ) * Real.log x := by
    have h := Real.log_le_log hd hdu
    rwa [Real.log_rpow hx0] at h
  have hm : 0 < x / d := div_pos hx0 hd
  have hmlog : Real.log x / 4 ≤ Real.log (x / d) := by
    rw [Real.log_div hx0.ne' hd.ne']
    linarith
  have hroot : Real.sqrt (Real.log x) ≤ Real.log x / 16 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith, ?_⟩
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log x)
      (by linarith : 0 ≤ Real.log x - 256)]
  calc
    _ = Real.exp (Real.log (x / d) * (3 / 4 : ℝ)) := Real.rpow_def_of_pos hm _
    _ ≤ Real.exp (Real.log (x / d) - Real.sqrt (Real.log x)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Task379.referenceLength x / d := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hm]
      unfold Task379.referenceLength
      ring

end LeanLab.Ternary.MMS.Task581
