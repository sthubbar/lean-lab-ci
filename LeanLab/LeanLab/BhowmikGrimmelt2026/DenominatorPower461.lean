/-
Arbitrary power decay in the ratio of the selected denominator to R.
Source: P0029 page 26 displays 7.5 and 7.6.
The square root denominator threshold is a derived sufficient range.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.DenominatorGap461

namespace LeanLab.BhowmikGrimmelt2026

/-- A distance gap gives any prescribed power of a small ratio while leaving shell decay. -/
theorem decay_ratio461 {d u A : ℝ} (hd : 0 ≤ d) (hu : 0 < u) (hA : 0 ≤ A)
    (hgap : 1 / (2 * u) ≤ d) :
    (1 + d) ^ (-(4 + A)) ≤ (2 * u) ^ A * (1 + d) ^ (-(4 : ℝ)) := by
  have hdp : 0 < 1 + d := by positivity
  have hh : 1 ≤ (2 * u) * (1 + d) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * u)).mp hgap
    nlinarith
  have hinv : (1 + d)⁻¹ ≤ 2 * u := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hdp).mpr
    nlinarith only [hh]
  have hp := Real.rpow_le_rpow (inv_nonneg.mpr hdp.le) hinv hA
  rw [Real.inv_rpow hdp.le, ← Real.rpow_neg hdp.le] at hp
  rw [show -(4 + A) = -A + -(4 : ℝ) by ring, Real.rpow_add hdp]
  exact mul_le_mul_of_nonneg_right hp (by positivity)

/-- The complete continuous off rational sum decays in the central denominator ratio.
The implied constant depends on the chosen exponent and the fixed smooth weight only. -/
theorem denominator_off_sum_decay461 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ D : ℝ, 0 < D ∧ ∀ R X η α : ℝ, 1 ≤ R → 0 < X → 0 < η →
      10 * R ^ 2 ≤ X → R ^ 2 ≤ η * X →
      ∀ p₀ ∈ reducedPairs ⌊R⌋₊,
      (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤ R / X →
      ‖∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
        centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1)‖ ≤
        D * ((p₀.1 : ℝ) / R) ^ A := by
  classical
  obtain ⟨C, hC, hc⟩ := fourier_decay hG.supp hG.smooth (4 + A)
  let Z : ℝ := 6 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => by positivity))
  refine ⟨C * (2 : ℝ) ^ A * (Z + 1), by positivity, ?_⟩
  intro R X η α hR hX hη hscale hK p₀ hp₀ hclose
  have hRp : 0 < R := by linarith
  have hrp : (0 : ℝ) < p₀.1 := by
    exact_mod_cast ((mem_reducedPairs _ _).mp hp₀).1
  have hu : 0 < (p₀.1 : ℝ) / R := div_pos hrp hRp
  have hgap : ∀ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
      1 / (2 * ((p₀.1 : ℝ) / R)) ≤ R * p.1 * intDist (α - p.2 / p.1) := by
    intro p hp
    obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
    have hh := central_denominator_gap461 hRp hX (Nat.floor_le hRp.le)
      hscale hp₀ hp hne hclose
    convert hh using 1 <;> field_simp
  have hterm : ∀ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
      ‖centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1)‖ ≤
      (C * (2 * ((p₀.1 : ℝ) / R)) ^ A) *
        (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ)) := by
    intro p hp
    have hd := intDist_nonneg (α - p.2 / p.1)
    have hT : R * p.1 ≤ η * X * p.1 / R := by
      apply (le_div_iff₀ hRp).mpr
      nlinarith [mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg p.1)]
    have hx : |-(η * X * p.1 / R) *
        ((α - p.2 / p.1) - round (α - p.2 / p.1))| =
        (η * X * p.1 / R) * intDist (α - p.2 / p.1) := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
      rfl
    have harg := mul_le_mul_of_nonneg_right hT hd
    calc
      _ ≤ C * (1 + (η * X * p.1 / R) * intDist (α - p.2 / p.1)) ^ (-(4 + A)) := by
        simpa only [centeredFourier405, hx] using
          hc (-(η * X * p.1 / R) * ((α - p.2 / p.1) - round (α - p.2 / p.1)))
      _ ≤ C * (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 + A)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)) hC.le
      _ ≤ _ := by
        have hh := decay_ratio461 (d := R * p.1 * intDist (α - p.2 / p.1))
          (mul_nonneg (mul_nonneg hRp.le (Nat.cast_nonneg _)) hd) hu hA (hgap p hp)
        nlinarith [mul_le_mul_of_nonneg_left hh hC.le]
  have hk := weighted_pair_kernel451 hR α
  have herase : (∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
      (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ))) ≤ Z := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun p _ _ => Real.rpow_nonneg (by
        have hd := intDist_nonneg (α - p.2 / p.1)
        positivity) _)).trans hk
  calc
    _ ≤ ∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
      (C * (2 * ((p₀.1 : ℝ) / R)) ^ A) *
        (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ)) :=
        norm_sum_le_of_le _ hterm
    _ ≤ (C * (2 * ((p₀.1 : ℝ) / R)) ^ A) * Z := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left herase (by positivity)
    _ ≤ _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le]
      convert mul_le_mul_of_nonneg_left (show Z ≤ Z + 1 by linarith)
        (show 0 ≤ C * (2 : ℝ) ^ A * ((p₀.1 : ℝ) / R) ^ A by positivity) using 1 <;> ring

/-- Denominators through square root R give the eta squared saving at every allowed scale.
Here R is X to theta and theta is fixed and positive. -/
theorem sqrt_denominator_power461 {x ϑ η q : ℝ} (hx : 1 ≤ x) (hϑ : 0 < ϑ)
    (hη : 0 < η) (hq : 0 ≤ q) (hsmall : q ≤ Real.sqrt (x ^ ϑ))
    (hscale : 10 * (x ^ ϑ) ^ 2 ≤ η * x) :
    (q / x ^ ϑ) ^ (4 / ϑ) ≤ η ^ 2 := by
  have hxp : 0 < x := by linarith
  have hRp : 0 < x ^ ϑ := Real.rpow_pos_of_pos hxp ϑ
  have hR1 : 1 ≤ x ^ ϑ := Real.one_le_rpow hx hϑ.le
  have hden : q / x ^ ϑ ≤ (x ^ ϑ) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ Real.sqrt (x ^ ϑ) / x ^ ϑ := div_le_div_of_nonneg_right hsmall hRp.le
      _ = _ := by
        rw [Real.sqrt_eq_rpow, show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num,
          Real.rpow_sub hRp, Real.rpow_one]
  have hp := Real.rpow_le_rpow (div_nonneg hq hRp.le) hden
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hϑ.le)
  have he : ((x ^ ϑ) ^ (-(1 / 2 : ℝ))) ^ (4 / ϑ) = (1 / x) ^ 2 := by
    rw [← Real.rpow_mul hRp.le, ← Real.rpow_mul hxp.le]
    have hh : ϑ * (-(1 / 2 : ℝ) * (4 / ϑ)) = -(2 : ℝ) := by field_simp <;> ring
    rw [hh, Real.rpow_neg hxp.le, Real.rpow_two]
    simp [one_div, inv_pow]
  have hinv : 1 / x ≤ η := by
    apply (div_le_iff₀ hxp).mpr
    nlinarith [sq_nonneg (x ^ ϑ - 1)]
  exact (hp.trans_eq he).trans (pow_le_pow_left₀ (by positivity) hinv 2)

/-- Every central denominator through square root R has a uniform off rational eta saving. -/
theorem sqrt_denominator_off_sum461 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ D : ℝ, 0 < D ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α : ℝ,
      ∀ p₀ ∈ reducedPairs ⌊(X : ℝ) ^ ϑ⌋₊,
      (p₀.1 : ℝ) ≤ Real.sqrt ((X : ℝ) ^ ϑ) →
      (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤ (X : ℝ) ^ ϑ / X →
      ‖∑ p ∈ (reducedPairs ⌊(X : ℝ) ^ ϑ⌋₊).erase p₀,
        centeredFourier405 G (η * X * p.1 / (X : ℝ) ^ ϑ) (α - p.2 / p.1)‖ ≤
        D * η ^ 2 := by
  obtain ⟨D, hD, hb⟩ := denominator_off_sum_decay461 hG (4 / ϑ) (by positivity)
  refine ⟨D, hD, ?_⟩
  intro X hX η hη hη1 hscale α p₀ hp₀ hden hclose
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have hR : 1 ≤ (X : ℝ) ^ ϑ := Real.one_le_rpow hX1 hϑ.le
  have hηX : η * X ≤ (X : ℝ) := by nlinarith
  have hh := hb ((X : ℝ) ^ ϑ) X η α hR hXp hη (hscale.trans hηX)
    (by nlinarith [sq_nonneg ((X : ℝ) ^ ϑ)]) p₀ hp₀ hclose
  exact hh.trans (mul_le_mul_of_nonneg_left
    (sqrt_denominator_power461 hX1 hϑ hη (Nat.cast_nonneg _) hden hscale) hD.le)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.decay_ratio461
#print axioms LeanLab.BhowmikGrimmelt2026.denominator_off_sum_decay461
#print axioms LeanLab.BhowmikGrimmelt2026.sqrt_denominator_power461
#print axioms LeanLab.BhowmikGrimmelt2026.sqrt_denominator_off_sum461
