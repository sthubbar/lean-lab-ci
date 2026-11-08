/-
A denominator sensitive off rational estimate for P0029 page 26 displays 7.5 and 7.6.
The threshold q zero at most eta R is a derived sufficient condition.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.UniformMinorWeight451
import LeanLab.BhowmikGrimmelt2026.OffRational432

namespace LeanLab.BhowmikGrimmelt2026

open scoped FourierTransform

/-- A central rational with small denominator pushes every other weighted distance away.
This strengthens the constant Farey gap on page 26 without counting all pairs. -/
theorem central_denominator_gap461 {M : ℕ} {R X α : ℝ}
    (hR : 0 < R) (hX : 0 < X) (hMR : (M : ℝ) ≤ R)
    (hscale : 10 * R ^ 2 ≤ X)
    {p₀ p : Σ _ : ℕ, ℕ} (hp₀ : p₀ ∈ reducedPairs M)
    (hp : p ∈ reducedPairs M) (hne : p ≠ p₀)
    (hclose : (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤ R / X) :
    R / (2 * p₀.1) ≤ R * p.1 * intDist (α - p.2 / p.1) := by
  obtain ⟨hq1, hqM, ha, hcop⟩ := (mem_reducedPairs M p).mp hp
  obtain ⟨hr1, hrM, hb, hcopr⟩ := (mem_reducedPairs M p₀).mp hp₀
  have hqp : (0 : ℝ) < p.1 := by exact_mod_cast hq1
  have hrp : (0 : ℝ) < p₀.1 := by exact_mod_cast hr1
  have hqR : (p.1 : ℝ) ≤ R := (by exact_mod_cast hqM : (p.1 : ℝ) ≤ M).trans hMR
  have hne' : (p.2, p.1) ≠ (p₀.2, p₀.1) := by
    intro heq
    exact hne (Sigma.ext (congrArg Prod.snd heq) (by simpa using congrArg Prod.fst heq))
  have hs := farey_intDist_separation ha hb hcop hcopr hne'
  have ht := intDist_sub_le (α - p₀.2 / p₀.1) (α - p.2 / p.1)
  rw [show (α - (p₀.2 : ℝ) / p₀.1) - (α - p.2 / p.1) =
    (p.2 : ℝ) / p.1 - p₀.2 / p₀.1 by ring] at ht
  have htri : 1 ≤ ((p.1 : ℝ) * p₀.1) *
      (intDist (α - p.2 / p.1) + intDist (α - p₀.2 / p₀.1)) := by
    have hh := (div_le_iff₀ (mul_pos hqp hrp)).mp
      (hs.trans (by simpa only [add_comm] using ht))
    nlinarith only [hh]
  have hc := (le_div_iff₀ hX).mp hclose
  have hqsmall : 2 * (p.1 : ℝ) * R ≤ X := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left htri hX.le
  have h2 := mul_le_mul_of_nonneg_left hc hqp.le
  have hcent : (p.1 : ℝ) * p₀.1 * intDist (α - p₀.2 / p₀.1) ≤ 1 / 2 := by
    apply (mul_le_mul_iff_right₀ hX).mp
    nlinarith only [h2, hqsmall]
  have hgap : 1 / 2 ≤ (p.1 : ℝ) * p₀.1 * intDist (α - p.2 / p.1) := by
    nlinarith only [htri, hcent]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p₀.1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hgap hR.le]

/-- An inverse sixth power beyond the eta gap saves eta squared over a fourth power. -/
theorem decay_gap461 {d η : ℝ} (hd : 0 ≤ d) (hη : 0 < η)
    (hgap : 1 / (2 * η) ≤ d) :
    (1 + d) ^ (-(6 : ℝ)) ≤ 4 * η ^ 2 * (1 + d) ^ (-(4 : ℝ)) := by
  have hdp : 0 < 1 + d := by positivity
  have hh : 1 ≤ (2 * η) * (1 + d) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * η)).mp hgap
    nlinarith
  have hinv : (1 + d)⁻¹ ≤ 2 * η := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hdp).mpr
    nlinarith only [hh]
  have hs := pow_le_pow_left₀ (inv_nonneg.mpr hdp.le) hinv 2
  have he : (1 + d) ^ (-(6 : ℝ)) =
      ((1 + d)⁻¹) ^ 2 * (1 + d) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul hdp.le,
      ← Real.rpow_add hdp]
    norm_num
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hs
    (by positivity : 0 ≤ (1 + d) ^ (-(4 : ℝ)))]

/-- A small central denominator gives an eta squared bound for the continuous off sum.
This retains every nonselected pair and uses the proved weighted shell count. -/
theorem small_denominator_off_sum461 {G : ℝ → ℝ} (hG : IsMajorWeight G) :
    ∃ D : ℝ, 0 < D ∧ ∀ R X η α : ℝ, 1 ≤ R → 0 < X → 0 < η →
      10 * R ^ 2 ≤ X → R ^ 2 ≤ η * X →
      ∀ p₀ ∈ reducedPairs ⌊R⌋₊,
      (p₀.1 : ℝ) ≤ η * R →
      (p₀.1 : ℝ) * intDist (α - p₀.2 / p₀.1) ≤ R / X →
      ‖∑ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
        centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1)‖ ≤ D * η ^ 2 := by
  classical
  obtain ⟨C, hC, hc⟩ := fourier_decay hG.supp hG.smooth 6
  let Z : ℝ := 6 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  refine ⟨4 * C * (Z + 1), by positivity, ?_⟩
  intro R X η α hR hX hη hscale hK p₀ hp₀ hden hclose
  have hRp : 0 < R := by linarith
  have hrp : (0 : ℝ) < p₀.1 := by
    exact_mod_cast ((mem_reducedPairs _ _).mp hp₀).1
  have hgap : ∀ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
      1 / (2 * η) ≤ R * p.1 * intDist (α - p.2 / p.1) := by
    intro p hp
    obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
    have hh := central_denominator_gap461 hRp hX (Nat.floor_le hRp.le)
      hscale hp₀ hp hne hclose
    have hd : 1 / (2 * η) ≤ R / (2 * p₀.1) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * η)
        (by positivity : (0 : ℝ) < 2 * p₀.1)).mpr
      nlinarith
    exact hd.trans hh
  have hterm : ∀ p ∈ (reducedPairs ⌊R⌋₊).erase p₀,
      ‖centeredFourier405 G (η * X * p.1 / R) (α - p.2 / p.1)‖ ≤
      (4 * C * η ^ 2) *
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
      _ ≤ C * (1 + (η * X * p.1 / R) * intDist (α - p.2 / p.1)) ^ (-(6 : ℝ)) := by
        simpa only [centeredFourier405, hx] using
          hc (-(η * X * p.1 / R) * ((α - p.2 / p.1) - round (α - p.2 / p.1)))
      _ ≤ C * (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(6 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)) hC.le
      _ ≤ _ := by
        have hh := decay_gap461 (d := R * p.1 * intDist (α - p.2 / p.1))
          (mul_nonneg (mul_nonneg hRp.le (Nat.cast_nonneg _)) hd) hη (hgap p hp)
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
      (4 * C * η ^ 2) * (1 + R * p.1 * intDist (α - p.2 / p.1)) ^ (-(4 : ℝ)) :=
        norm_sum_le_of_le _ hterm
    _ ≤ (4 * C * η ^ 2) * Z := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left herase (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg η]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.central_denominator_gap461
#print axioms LeanLab.BhowmikGrimmelt2026.decay_gap461
#print axioms LeanLab.BhowmikGrimmelt2026.small_denominator_off_sum461
