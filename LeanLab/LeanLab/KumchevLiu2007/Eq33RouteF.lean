/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 5 hypothesis A2.2 and
page 15, first paragraph of Section 4, with the function f2 after display 51.

RESULT OF THIS FILE. The statement of `Task556a.rough_short_interval_character`
is refuted: see `rough_short_interval_character_fails` for every B > 1/2 and
0 < ε ≤ 11/36, and `rough_short_interval_character_statement_fails` for the
exact statement on main.

REASON. Hypothesis A2.2 as printed on page 5 multiplies the smooth term by the
character, (λ(m) - D(χ) f(m)) χ(m). Take the principal character modulo 1 and
the principal character modulo 2 with the same δ = (H / P) / Y and
H = X^(7/18 + ε). The rough weight of display 10 vanishes on even m once the
cutoff z0 exceeds 2, so the difference of the two defects is minus the sum of
f2(m) over the even m with t < m^2 ≤ t + δ t. For Y/4 ≤ t ≤ Y/3 there are at
least Y^(1/2) δ / 24 such m and f2(m) ≥ 1 / log X. Integrating the square over
that range gives at least Q^2 / (6912 (log X)^2) with Q = H / P, against the
claimed 10 C Q^2 P^(-4) with P = (log X)^B. That fails for large X when B > 1/2.

Every declaration below is proved in full. No definition is introduced.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a

namespace LeanLab.KumchevLiu2007.Eq33RouteF

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 15, the function f2 after display 51: when the lower limit z0
exceeds one and is at most the square root of u, the integral term is
nonnegative, so f2(u) is at least 1 / log u. -/
theorem f2Weight_ge {z0 u : ℝ} (h1 : 1 < z0) (h2 : z0 ^ 2 ≤ u) :
    1 / Real.log u ≤ f2Weight z0 u := by
  have hz0 : 0 < z0 := by linarith
  have hsu : z0 ≤ Real.sqrt u := (Real.le_sqrt' hz0).mpr h2
  have hsu1 : 1 < Real.sqrt u := lt_of_lt_of_le h1 hsu
  have hu0 : 0 ≤ u := le_trans (sq_nonneg z0) h2
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
  unfold f2Weight
  have hint : 0 ≤ ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t)) := by
    apply intervalIntegral.integral_nonneg hsu
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le h1 ht.1
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos ht1
    have hut : 1 < u / t := by
      rw [one_lt_div ht0]
      nlinarith [ht.2, mul_pos (sub_pos.mpr hsu1) (show (0 : ℝ) < Real.sqrt u by linarith)]
    have hlu : 0 < Real.log (u / t) := Real.log_pos hut
    exact (one_div_pos.mpr (mul_pos (mul_pos ht0 hlt) hlu)).le
  linarith

/-- P0088 page 4 display 14: a fixed power of log X is eventually below any
positive multiple of any positive power of X. -/
theorem log_rpow_le_eventually (s e c : ℝ) (he : 0 < e) (hc : 0 < c) :
    ∀ᶠ X : ℝ in Filter.atTop, Real.log X ^ s ≤ c * X ^ e := by
  have ht := (isLittleO_log_rpow_rpow_atTop s he).bound hc
  filter_upwards [ht, Filter.eventually_gt_atTop (1 : ℝ)] with X hsmall hX
  have hL : 0 < Real.log X := Real.log_pos hX
  have hy : 0 < X ^ e := Real.rpow_pos_of_pos (by linarith) _
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL s), abs_of_pos hy]
    using hsmall

/-- P0088 page 5 hypothesis A2.2 with page 4 display 10: for the principal
characters modulo 1 and modulo 2 and a rough cutoff above 2, the difference of
the two defects is minus the sum of f2 over the even integers of the short
square window, where the character modulo 2 vanishes. -/
theorem defect_sub_eq (Y P δ t : ℝ) (hz : 2 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) :
    roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t -
        roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t =
      -((∑ m ∈ ((squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
            (fun m : ℕ => 2 ∣ m),
          f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ) := by
  have hR : (∑ m ∈ ((squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
            (fun m : ℕ => 2 ∣ m),
          f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ)) =
      ∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t),
        if 2 ∣ m then f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) else 0 :=
    Finset.sum_filter _ _
  rw [hR]
  unfold roughCharacterDefect
  rw [← Finset.sum_sub_distrib, Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  by_cases hm : 2 ∣ m
  · have h2 : (1 : DirichletCharacter ℂ 2) (m : ZMod 2) = 0 := by
      apply MulChar.map_nonunit
      obtain ⟨k, rfl⟩ := hm
      intro hu
      have h0 : ((2 * k : ℕ) : ZMod 2) = 0 := by
        push_cast
        rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
      rw [h0, isUnit_zero_iff] at hu
      exact absurd hu (by decide)
    have hr : roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m = 0 :=
      roughWeight_eq_zero_of_small_prime Nat.prime_two hm (by exact_mod_cast hz)
    simp only [h1, h2, hr, hm, ↓reduceIte]
    ring
  · have h2 : (1 : DirichletCharacter ℂ 2) (m : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod m 2, show m % 2 = 1 by omega, Nat.cast_one, map_one]
    simp only [h1, h2, hm, ↓reduceIte, Complex.ofReal_zero]
    ring

/-- P0088 page 5 hypothesis A2.2: a sum over a filtered window is bounded in
norm by the full sum of norms, uniformly in the filter. -/
theorem filter_sum_norm_le (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (c : ℕ → ℂ) :
    ‖∑ m ∈ s.filter p, c m‖ ≤ ∑ m ∈ s, ‖c m‖ :=
  (norm_sum_le _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => norm_nonneg _)

/-- P0088 page 5 hypothesis A2.2: the squared defect is a bounded measurable
step function of t, hence integrable on every interval. This makes the
integral in the hypothesis a genuine integral. -/
theorem defect_sq_intervalIntegrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Y P δ a b : ℝ) :
    IntervalIntegrable (fun t => ‖roughCharacterDefect χ Y P δ t‖ ^ 2) volume a b := by
  have hmeas : Measurable (fun t => ‖roughCharacterDefect χ Y P δ t‖ ^ 2) := by
    unfold roughCharacterDefect
    simp only [Finset.sum_filter]
    refine (Measurable.norm (Finset.measurable_sum _ fun m _ => ?_)).pow_const 2
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_lt (f := fun t : ℝ => t) (g := fun _ : ℝ => (m : ℝ) ^ 2)
      measurable_id measurable_const).inter
      (measurableSet_le (f := fun _ : ℝ => (m : ℝ) ^ 2) (g := fun t : ℝ => t + δ * t)
        measurable_const (by fun_prop))
  have hb : ∀ t, ‖roughCharacterDefect χ Y P δ t‖ ≤
      ∑ m ∈ squareWindow Y, ‖(roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m -
        (if χ = 1 then (f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℂ)
         else 0)) * χ m‖ := fun t => by
    unfold roughCharacterDefect
    exact filter_sum_norm_le (squareWindow Y)
      (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t) _
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := (∑ m ∈ squareWindow Y,
      ‖(roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m -
        (if χ = 1 then (f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℂ)
         else 0)) * χ m‖) ^ 2) ?_ hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  · rw [Set.uIoc]
    exact measure_Ioc_lt_top.ne
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2

/-- P0088 page 5 hypothesis A2.2 with page 2 display 5: for Y/4 ≤ t ≤ Y/3 and
0 < δ ≤ 1 the short square window t < m^2 ≤ t + δ t inside the square root
interval holds at least the integer part of Y^(1/2) δ / 12 even integers. -/
theorem even_window_card_ge {Y δ t : ℝ} (hY : 0 < Y) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ht1 : Y / 4 ≤ t) (ht2 : t ≤ Y / 3) :
    ⌊Real.sqrt Y * δ / 12⌋₊ ≤ (((squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
          (fun m : ℕ => 2 ∣ m)).card := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hsY0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hsYY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY.le
  have hsl : Real.sqrt Y / 2 ≤ Real.sqrt t := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hN : (⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) ≤ Real.sqrt Y * δ / 12 :=
    Nat.floor_le (by positivity)
  have hj1 : (⌊Real.sqrt t / 2⌋₊ : ℝ) ≤ Real.sqrt t / 2 := Nat.floor_le (by positivity)
  have hj2 : Real.sqrt t / 2 < (⌊Real.sqrt t / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine le_of_eq_of_le (Finset.card_range _).symm
    (Finset.card_le_card_of_injOn (fun k => 2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k)) ?_ ?_)
  · intro k hk
    have hk' : k < ⌊Real.sqrt Y * δ / 12⌋₊ := by simpa using hk
    have hk1 : (k : ℝ) + 1 ≤ (⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) := by exact_mod_cast hk'
    have hx : ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) =
        2 * ((⌊Real.sqrt t / 2⌋₊ : ℝ) + 1 + k) := by
      push_cast
      ring
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hxl : Real.sqrt t < ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) := by
      rw [hx]
      linarith
    have hδs : Real.sqrt Y / 2 * (δ / 3) ≤ Real.sqrt t * (δ / 3) :=
      mul_le_mul_of_nonneg_right hsl (by positivity)
    have hxu : ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) ≤
        Real.sqrt t * (1 + δ / 3) := by
      rw [hx]
      linarith
    have hx0 : (0 : ℝ) ≤ ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hx2l : t < ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) ^ 2 := by
      have h := pow_lt_pow_left₀ hxl hs0.le (by norm_num : (2 : ℕ) ≠ 0)
      rw [hss] at h
      exact h
    have hx2u : ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) ^ 2 ≤ t + δ * t := by
      have h := pow_le_pow_left₀ hx0 hxu 2
      rw [mul_pow, hss] at h
      have h3 : (1 + δ / 3) ^ 2 ≤ 1 + δ := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 ht0.le
      linarith
    have hxY : ((2 * (⌊Real.sqrt t / 2⌋₊ + 1 + k) : ℕ) : ℝ) < Real.sqrt Y := by
      apply Real.lt_sqrt_of_sq_lt
      have h5 : δ * t ≤ 1 * t := mul_le_mul_of_nonneg_right hδ1 ht0.le
      linarith
    rw [Finset.mem_coe]
    simp only [Finset.mem_filter, squareWindow, Finset.mem_range]
    exact ⟨⟨⟨Nat.lt_succ_of_le (Nat.le_floor hxY.le), by linarith, hxY⟩, hx2l, hx2u⟩,
      Nat.dvd_mul_right _ _⟩
  · intro a _ b _ h
    have h' : 2 * (⌊Real.sqrt t / 2⌋₊ + 1 + a) = 2 * (⌊Real.sqrt t / 2⌋₊ + 1 + b) := h
    omega

/-- P0088 page 15, the function f2 after display 51, summed over the even
integers of the short square window of hypothesis A2.2 on page 5: for
Y/4 ≤ t ≤ Y/3 the sum is at least the integer part of Y^(1/2) δ / 12 divided
by log X. -/
theorem even_sum_ge {X Y z δ t : ℝ} (hY16 : 16 ≤ Y) (hYX : Y ≤ X) (hz1 : 1 < z)
    (hz2 : z ^ 2 ≤ Real.sqrt Y / 2) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ht1 : Y / 4 ≤ t) (ht2 : t ≤ Y / 3) :
    (⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) * (1 / Real.log X) ≤
      ∑ m ∈ ((squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
            (fun m : ℕ => 2 ∣ m), f2Weight z (m : ℝ) := by
  have hY0 : 0 < Y := by linarith
  have hsY : 4 ≤ Real.sqrt Y :=
    (Real.le_sqrt' (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num; linarith)
  have hsYY : Real.sqrt Y ≤ Y := by nlinarith [Real.sq_sqrt hY0.le]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hcard := even_window_card_ge hY0 hδ0 hδ1 ht1 ht2
  have hcr : (⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) ≤ ((((squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
          (fun m : ℕ => 2 ∣ m)).card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ ((((squareWindow Y).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
          (fun m : ℕ => 2 ∣ m)).card : ℝ) * (1 / Real.log X) :=
      mul_le_mul_of_nonneg_right hcr (by positivity)
    _ = ∑ _m ∈ ((squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + δ * t)).filter
            (fun m : ℕ => 2 ∣ m), 1 / Real.log X := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      refine Finset.sum_le_sum fun m hm => ?_
      simp only [Finset.mem_filter, squareWindow, Finset.mem_range] at hm
      obtain ⟨⟨⟨-, hl, hu⟩, -⟩, -⟩ := hm
      have hm1 : 1 < (m : ℝ) := by linarith
      have hlm : 0 < Real.log (m : ℝ) := Real.log_pos hm1
      have hlmX : Real.log (m : ℝ) ≤ Real.log X :=
        Real.log_le_log (by linarith) (by linarith)
      exact (one_div_le_one_div_of_le hlm hlmX).trans (f2Weight_ge hz1 (hz2.trans hl))

/-- P0088 page 5 hypothesis A2.2: the elementary inequality used to pass from
the difference of two defects to the sum of their squares. -/
theorem sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- P0088 page 5 hypothesis A2.2 for the principal characters modulo 1 and
modulo 2: for Y/4 ≤ t ≤ Y/3 the two squared defects together are at least the
square of the even sum of f2, which is at least the integer part of
Y^(1/2) δ / 12 divided by log X. -/
theorem defect_pointwise {X Y P δ t : ℝ} (hY16 : 16 ≤ Y) (hYX : Y ≤ X)
    (hz2 : 2 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ))
    (hzsq : (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) ^ 2 ≤ Real.sqrt Y / 2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : t ∈ Set.Icc (Y / 4) (Y / 3)) :
    ((⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) * (1 / Real.log X)) ^ 2 ≤
      2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t‖ ^ 2 +
        2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t‖ ^ 2 := by
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hS := even_sum_ge (X := X) hY16 hYX
    (by linarith : 1 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) hzsq hδ0 hδ1 ht.1 ht.2
  have hd := defect_sub_eq Y P δ t hz2
  have hn := congrArg norm hd
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at hn
  have htri := norm_sub_le (roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t)
    (roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t)
  rw [hn] at htri
  have hlow := hS.trans ((le_abs_self _).trans htri)
  have h0 : 0 ≤ (⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) * (1 / Real.log X) := by positivity
  exact (pow_le_pow_left₀ h0 hlow 2).trans (sq_add_le _ _)

/-- P0088 page 5 hypothesis A2.2: a pointwise lower bound K for the two squared
defects on Y/4 ≤ t ≤ Y/3 gives the lower bound Y K / 12 for the two mean
squares over Y/4 ≤ t ≤ Y of the hypothesis. -/
theorem defect_mean_square_ge {Y P δ K : ℝ} (hY : 0 < Y)
    (hpt : ∀ t ∈ Set.Icc (Y / 4) (Y / 3), K ≤
      2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t‖ ^ 2 +
        2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t‖ ^ 2) :
    (Y / 3 - Y / 4) * K ≤
      2 * (∫ t in Y / 4..Y,
        ‖roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t‖ ^ 2) +
      2 * (∫ t in Y / 4..Y,
        ‖roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t‖ ^ 2) := by
  have i1 := fun a b => defect_sq_intervalIntegrable (1 : DirichletCharacter ℂ 1) Y P δ a b
  have i2 := fun a b => defect_sq_intervalIntegrable (1 : DirichletCharacter ℂ 2) Y P δ a b
  have ig := fun a b => ((i1 a b).const_mul 2).add ((i2 a b).const_mul 2)
  have hstep1 := intervalIntegral.integral_mono_on (μ := volume)
    (by linarith : Y / 4 ≤ Y / 3) intervalIntegrable_const (ig (Y / 4) (Y / 3)) hpt
  have hadj := intervalIntegral.integral_add_adjacent_intervals (ig (Y / 4) (Y / 3))
    (ig (Y / 3) Y)
  have hnn : 0 ≤ ∫ t in Y / 3..Y,
      (2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t‖ ^ 2 +
        2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t‖ ^ 2) :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
  have hsplit : (∫ t in Y / 4..Y,
      (2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t‖ ^ 2 +
        2 * ‖roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t‖ ^ 2)) =
      2 * (∫ t in Y / 4..Y,
        ‖roughCharacterDefect (1 : DirichletCharacter ℂ 1) Y P δ t‖ ^ 2) +
      2 * (∫ t in Y / 4..Y,
        ‖roughCharacterDefect (1 : DirichletCharacter ℂ 2) Y P δ t‖ ^ 2) := by
    rw [intervalIntegral.integral_add ((i1 _ _).const_mul 2) ((i2 _ _).const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hstep1
  linarith

/-- P0088 page 5 hypothesis A2.2, the closing arithmetic: a mean square of
size Q^2 / (6912 (log X)^2) cannot be at most 10 C Q^2 P^(-4) when
P^4 = T (log X)^2 with T above 69120 C. -/
theorem mean_square_contra {Y δ L Q P C T : ℝ} (hY0 : 0 < Y) (hL0 : 0 < L)
    (hQ : 0 < Q) (hC : 0 < C) (hδQ : δ * Y = Q) (hP4 : P ^ 4 = T * L ^ 2)
    (hT : 69120 * C < T)
    (hfin : (Y / 3 - Y / 4) * (Real.sqrt Y * δ / 24 * (1 / L)) ^ 2 ≤
      10 * C * Q ^ 2 * (P ^ 4)⁻¹) : False := by
  have hsYY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
  have hL2 : 0 < L ^ 2 := by positivity
  have hT0 : 0 < T := by nlinarith
  have hlhs : (Y / 3 - Y / 4) * (Real.sqrt Y * δ / 24 * (1 / L)) ^ 2 =
      Q ^ 2 * (1 / (6912 * L ^ 2)) := by
    have e1 : (Y / 3 - Y / 4) * (Real.sqrt Y * δ / 24 * (1 / L)) ^ 2 =
        (Real.sqrt Y ^ 2 * Y * δ ^ 2) * (1 / (6912 * L ^ 2)) := by
      field_simp
      ring
    rw [e1, hsYY, ← hδQ]
    ring
  have hrhs : 10 * C * Q ^ 2 * (P ^ 4)⁻¹ = Q ^ 2 * (10 * C / (T * L ^ 2)) := by
    rw [hP4]
    ring
  rw [hlhs, hrhs] at hfin
  have hcancel := le_of_mul_le_mul_left hfin (by positivity : 0 < Q ^ 2)
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcancel
  have h := mul_lt_mul_of_pos_right hT hL2
  linarith

/-- P0088 page 5 hypothesis A2.2 as transcribed in
`Task556a.rough_short_interval_character`, with the page 15 choices of λ0 and
f2: the mean square bound fails for every B > 1/2 and 0 < ε ≤ 11/36. The
principal characters modulo 1 and modulo 2 with H = X^(7/18 + ε) and
δ = (H / P) / Y cannot both satisfy it, since their defects differ by the sum
of f2 over even integers. -/
theorem rough_short_interval_character_fails (B ε : ℝ) (hB : 1 / 2 < B) (hε : 0 < ε)
    (hε1 : ε ≤ 11 / 36) :
    ¬ ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughCharacterDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 *
              (Real.log X ^ B) ^ (-4 : ℤ) := by
  rintro ⟨C, X0, hC, hX0, hall⟩
  have hθ : (0 : ℝ) < 7 / 12 + ε / 2 := by linarith
  have hκ : (0 : ℝ) < 7 / 72 + 3 * ε / 4 := by linarith
  have e1 := log_rpow_le_eventually (2 * B) ((7 / 12 + ε / 2) * (1 / 4)) (1 / 4)
    (by positivity) (by norm_num)
  have e2 := log_rpow_le_eventually B (7 / 72 + 3 * ε / 4) (1 / 24) hκ (by norm_num)
  have e3 : ∀ᶠ X : ℝ in Filter.atTop, 69120 * C < Real.log X ^ (4 * B - 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < 4 * B - 2)).comp
      Real.tendsto_log_atTop).eventually_gt_atTop (69120 * C)
  have e4 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ Real.log X ^ B :=
    ((tendsto_rpow_atTop (by linarith : 0 < B)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop 2
  have e5 : ∀ᶠ X : ℝ in Filter.atTop, 16 ≤ X ^ (7 / 12 + ε / 2) :=
    (tendsto_rpow_atTop hθ).eventually_ge_atTop 16
  have e6 := Filter.eventually_ge_atTop (max X0 3)
  obtain ⟨X, h1, h2, h3, h4, h5, h6⟩ :=
    (e1.and (e2.and (e3.and (e4.and (e5.and e6))))).exists
  have hXX0 : X0 ≤ X := (le_max_left _ _).trans h6
  have hX3 : 3 ≤ X := (le_max_right _ _).trans h6
  have hXpos : 0 < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hYeq : windowY X ε = X ^ (7 / 12 + ε / 2) := rfl
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = windowY X ε := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ, H = X ^ (7 / 18 + ε) := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = Real.log X ^ B := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Y ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = H / P / Y := ⟨_, rfl⟩
  have hY16 : 16 ≤ Y := by rw [hYdef, hYeq]; exact h5
  have hY0 : 0 < Y := by linarith
  have hP2 : 2 ≤ P := by rw [hPdef]; exact h4
  have hPpos : 0 < P := by linarith
  have hHpos : 0 < H := by rw [hHdef]; exact Real.rpow_pos_of_pos hXpos _
  have hQpos : 0 < H / P := div_pos hHpos hPpos
  have hYX : Y ≤ X := by
    have h := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith : 7 / 12 + ε / 2 ≤ 1)
    rw [Real.rpow_one] at h
    rw [hYdef, hYeq]
    exact h
  have hHY : H ≤ Y := by
    rw [hHdef, hYdef, hYeq]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hHu : H ≤ X ^ (1 - ε) := by
    rw [hHdef]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hPsq : P ^ 2 = Real.log X ^ (2 * B) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  have hP4 : 4 ≤ P ^ 2 := by
    have h := mul_le_mul hP2 hP2 (by norm_num) hPpos.le
    rw [sq]
    linarith
  have hP2pos : 0 < P ^ 2 := by positivity
  have hWeq : W = X ^ ((7 / 12 + ε / 2) * (1 / 4)) := by
    rw [hWdef, hYdef, hYeq, ← Real.rpow_mul hXpos.le]
  have hPW : P ^ 2 ≤ 1 / 4 * W := by rw [hPsq, hWeq]; exact h1
  have hW0 : 0 < W := by linarith
  have hWW : W ^ 2 = Real.sqrt Y := by
    rw [hWdef, Real.sqrt_eq_rpow, sq, ← Real.rpow_add hY0]
    norm_num
  have hzdef : Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) = W / P ^ 2 := by
    rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv, hWdef]
  have hz2 : 2 < Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) := by
    rw [hzdef, lt_div_iff₀ hP2pos]
    linarith
  have hzsq : (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) ^ 2 ≤ Real.sqrt Y / 2 := by
    rw [hzdef]
    have hle : W / P ^ 2 ≤ W / 4 := by
      rw [div_le_div_iff₀ hP2pos (by norm_num)]
      have h := mul_le_mul_of_nonneg_left hP4 hW0.le
      linarith
    have hq0 : 0 ≤ W / P ^ 2 := by positivity
    have hsq := pow_le_pow_left₀ hq0 hle 2
    have hexp : (W / 4) ^ 2 = W ^ 2 / 16 := by ring
    rw [hexp, hWW] at hsq
    linarith [Real.sqrt_nonneg Y]
  have hsY0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hsYY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0.le
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hY0]
    have h : H / P ≤ H := div_le_self hHpos.le (by linarith)
    linarith
  have hδQ : δ * Y = H / P := by
    rw [hδdef]
    field_simp
  -- the size of the window
  have hsYeq : Real.sqrt Y = X ^ ((7 / 12 + ε / 2) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, hYdef, hYeq, ← Real.rpow_mul hXpos.le]
  have hHeq : H = X ^ (7 / 72 + 3 * ε / 4) * Real.sqrt Y := by
    rw [hsYeq, hHdef, ← Real.rpow_add hXpos]
    congr 1
    ring
  have hXκ : 24 * P ≤ X ^ (7 / 72 + 3 * ε / 4) := by
    rw [hPdef]
    linarith
  have hbig : 24 ≤ Real.sqrt Y * δ := by
    have h : Real.sqrt Y * δ * (P * Real.sqrt Y) = H := by
      have hc : Real.sqrt Y * δ * (P * Real.sqrt Y) = Real.sqrt Y ^ 2 * δ * P := by ring
      rw [hc, hsYY, mul_comm Y δ, hδQ]
      exact div_mul_cancel₀ H hPpos.ne'
    rw [hHeq] at h
    have h' : Real.sqrt Y * δ * P = X ^ (7 / 72 + 3 * ε / 4) := by
      have hc : Real.sqrt Y * δ * (P * Real.sqrt Y) =
          (Real.sqrt Y * δ * P) * Real.sqrt Y := by ring
      rw [hc] at h
      exact mul_right_cancel₀ hsY0.ne' h
    have h3' : 24 * P ≤ Real.sqrt Y * δ * P := by
      rw [h']
      exact hXκ
    exact le_of_mul_le_mul_right h3' hPpos
  have hNA : Real.sqrt Y * δ / 24 ≤ (⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.sqrt Y * δ / 12)
    linarith
  -- the two instances of the hypothesis
  have hI1 := hall X H hXX0 (by rw [hHdef]) hHu 1 le_rfl
    (by rw [← hPdef]; push_cast; linarith) 1 δ hδ0
    (by rw [← hPdef, ← hYdef, hδdef]; push_cast; rw [one_mul])
  have hI2 := hall X H hXX0 (by rw [hHdef]) hHu 2 (by norm_num)
    (by rw [← hPdef]; push_cast; linarith) 1 δ hδ0
    (by
      rw [← hPdef, ← hYdef, hδdef]
      push_cast
      apply div_le_div_of_nonneg_right _ hY0.le
      linarith)
  rw [← hYdef, ← hPdef] at hI1 hI2
  push_cast at hI1 hI2
  -- pointwise lower bound and integration
  have hmean := defect_mean_square_ge (P := P) (δ := δ) hY0
    (fun t ht => defect_pointwise (X := X) hY16 hYX hz2 hzsq hδ0 hδ1 ht)
  have hKK : (Real.sqrt Y * δ / 24 * (1 / Real.log X)) ^ 2 ≤
      ((⌊Real.sqrt Y * δ / 12⌋₊ : ℝ) * (1 / Real.log X)) ^ 2 :=
    pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hNA (by positivity)) 2
  have hKK' := mul_le_mul_of_nonneg_left hKK (by linarith : 0 ≤ Y / 3 - Y / 4)
  have hfin : (Y / 3 - Y / 4) * (Real.sqrt Y * δ / 24 * (1 / Real.log X)) ^ 2 ≤
      10 * C * (H / P) ^ 2 * P ^ (-4 : ℤ) := by
    have hc : 10 * C * (H / P) ^ 2 * P ^ (-4 : ℤ) =
        2 * (C * (1 * (H / P)) ^ 2 * P ^ (-4 : ℤ)) +
          2 * (C * (2 * (H / P)) ^ 2 * P ^ (-4 : ℤ)) := by ring
    rw [hc]
    linarith
  -- arithmetic
  have hP4' : P ^ 4 = Real.log X ^ (4 * B - 2) * Real.log X ^ 2 := by
    rw [hPdef, ← Real.rpow_natCast (Real.log X ^ B) 4, ← Real.rpow_mul hL0.le,
      ← Real.rpow_natCast (Real.log X) 2, ← Real.rpow_add hL0]
    congr 1
    push_cast
    ring
  rw [zpow_neg, zpow_ofNat] at hfin
  exact mean_square_contra hY0 hL0 hQpos hC hδQ hP4' h3 hfin

/-- P0088 page 5 hypothesis A2.2 with page 15, first paragraph of Section 4:
the exact statement of `Task556a.rough_short_interval_character` on main is
false. It fails at B = 1 and ε = 1/10. -/
theorem rough_short_interval_character_statement_fails :
    ¬ ∀ (B ε : ℝ) (_hB : 0 < B) (_hε : 0 < ε),
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
      ∀ χ : DirichletCharacter ℂ q, ∀ δ : ℝ,
        0 < δ → δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughCharacterDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) ≤
            C * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2 *
              (Real.log X ^ B) ^ (-4 : ℤ) := by
  intro hall
  exact rough_short_interval_character_fails 1 (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (hall 1 (1 / 10) (by norm_num) (by norm_num))

end LeanLab.KumchevLiu2007.Eq33RouteF
