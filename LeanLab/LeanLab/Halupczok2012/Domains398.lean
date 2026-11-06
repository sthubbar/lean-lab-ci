import LeanLab.Halupczok2012.Circle398

/-!
Perelli Pintz page 43, nonempty major and minor arc domains.
These checks rule out empty arc sets as the explanation for either open energy leaf.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Domains398

open Decomp398a

/-- The rational centre 1 belongs to the major arcs in the large parameter regime of page 43. -/
theorem major_one (N Y ε A : ℝ) (hN : Real.exp 1 ≤ N) (hY : 0 < Y)
    (hε : 0 < ε) (hA : 0 < A) (hH : 4 ≤ Y ^ (1 / 3 + ε)) :
    (1 : ℝ) ∈ majorArcs N Y ε A := by
  have hL : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hN
  have hLp : 0 < Real.log N := by linarith
  have hB : 0 < 3 / ε * (2 * A + 25) := by positivity
  have hroot : 2 ≤ Real.sqrt (Y ^ (1 / 3 + ε)) := by
    have h := Real.sqrt_le_sqrt hH
    norm_num at h
    exact h
  have hQ : 1 ≤ Real.sqrt (Y ^ (1 / 3 + ε)) / 2 := by linarith
  have hQp : 0 < Real.sqrt (Y ^ (1 / 3 + ε)) / 2 := by linarith
  refine ⟨⟨?_, ?_⟩, 1, 1, le_rfl, ?_, le_rfl, le_rfl, (by decide : Nat.Coprime 1 1), ?_⟩
  · exact (div_le_one hQp).mpr hQ
  · have h := div_pos one_pos hQp
    linarith
  · simpa using Real.one_le_rpow hL hB.le
  · norm_num only [Nat.cast_one, div_one, sub_self, abs_zero, one_mul]
    positivity

/-- Page 43, an explicit minor arc point when the base offset and total major arc widths are small.
The hypotheses hold for N = Y = exp t, epsilon = 1/12 and A = 1 for large t. -/
theorem minor_point (N Y ε A : ℝ) (hY : 0 < Y)
    (hD : 1 ≤ Real.log N ^ (3 / ε * (2 * A + 25)))
    (hu : 1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2) <
      1 / (4 * Real.log N ^ (3 / ε * (2 * A + 25))))
    (hw : Real.log N ^ (2 * (3 / ε * (2 * A + 25))) / Y <
      1 / (4 * Real.log N ^ (3 / ε * (2 * A + 25)))) :
    2 * (1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2)) ∈
      arcBase Y ε \ majorArcs N Y ε A := by
  let D := Real.log N ^ (3 / ε * (2 * A + 25))
  let u := 1 / (Real.sqrt (Y ^ (1 / 3 + ε)) / 2)
  let w := Real.log N ^ (2 * (3 / ε * (2 * A + 25))) / Y
  change 1 ≤ D at hD
  change u < 1 / (4 * D) at hu
  change w < 1 / (4 * D) at hw
  have hDp : 0 < D := by linarith
  have hup : 0 < u := by
    dsimp [u]
    exact div_pos one_pos (div_pos (Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hY _)) (by norm_num))
  have huD : u * (4 * D) < 1 := (lt_div_iff₀ (by positivity : 0 < 4 * D)).mp hu
  have hwD : w * (4 * D) < 1 := (lt_div_iff₀ (by positivity : 0 < 4 * D)).mp hw
  have huDu : u ≤ u * D := le_mul_of_one_le_right hup.le hD
  have hu1 : u < 1 := by nlinarith
  change 2 * u ∈ arcBase Y ε ∧ 2 * u ∉ majorArcs N Y ε A
  refine ⟨⟨by change u ≤ 2 * u; linarith, by change 2 * u ≤ 1 + u; linarith⟩, ?_⟩
  rintro ⟨_, q, a, hq1, hqD, ha1, haq, hcop, hα⟩
  change (q : ℝ) ≤ D at hqD
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqp : (0 : ℝ) < q := by linarith
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hmD : 1 ≤ D * ((a : ℝ) / q) := by
    rw [← mul_div_assoc, le_div_iff₀ hqp]
    have hDa : D ≤ D * (a : ℝ) := le_mul_of_one_le_right hDp.le har
    nlinarith
  have he : Real.log N ^ (2 * (3 / ε * (2 * A + 25))) / ((q : ℝ) * Y) = w / q := by
    dsimp [w]
    field_simp [hY.ne', hqp.ne'] <;> ring
  change |2 * u - (a : ℝ) / q| < _ at hα
  rw [he] at hα
  have hw0 : 0 ≤ w := by
    have hp := mul_pos ((abs_nonneg _).trans_lt hα) hqp
    rw [div_mul_cancel₀ _ hqp.ne'] at hp
    exact hp.le
  have hwq : w / q ≤ w := div_le_self hw0 hqr
  have hg := neg_le_abs (2 * u - (a : ℝ) / q)
  have hgap : (a : ℝ) / q - 2 * u < w := by linarith
  have hmul := mul_lt_mul_of_pos_left hgap hDp
  nlinarith

end LeanLab.Halupczok2012.Domains398
