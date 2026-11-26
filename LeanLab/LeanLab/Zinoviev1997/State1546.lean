/-
AI wrote this Lean code. Codex task575, 2026-11-15.
Codex task705 added the proved support below, 2026-11-24.
Prerequisites moved verbatim to Decomp575a for the acyclic supply split.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.Decomp575a
import LeanLab.Zinoviev1997.Decomp575b

namespace LeanLab.Zinoviev1997.State1546
open Complex MeasureTheory

/-- LEAF. The absolute error form of Proposition 1.4, pp. 339 to 341.
The missing inputs are character orthogonality with explicit psi errors, Abel summation,
and the Schoenfeld 1976 estimates of reference 4 for the cases q = 1 and q = 2.
The modulus range must be checked throughout the integral, not only at its upper endpoint. -/
theorem prop14_error_bound (hG : LeanLab.DERZ1997.GRH) {q l : ℕ}
    (hq : 1 ≤ q) (hl : Nat.Coprime l q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  sorry

/-- LEAF. Unit U-1546. Proposition 1.4, p. 339: under GRH, for `q ≥ 1`, `(l, q) = 1`,
`x ≥ 10⁹` and `q ≤ x^0.37`, there are `|θ₁| ≤ 1`, `|θ₂| ≤ 1` with
`π(x; q, l) = Li(x)/φ(q) + 1.3 θ₁ √x ln x + θ₂ 10⁸`. -/
theorem prop14 (hG : LeanLab.DERZ1997.GRH) {q l : ℕ} (hq : 1 ≤ q) (hl : Nat.Coprime l q)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) (hqx : (q : ℝ) ≤ x ^ (0.37 : ℝ)) :
    ∃ θ₁ θ₂ : ℝ, |θ₁| ≤ 1 ∧ |θ₂| ≤ 1 ∧
      (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ)
        + 1.3 * θ₁ * Real.sqrt x * Real.log x + θ₂ * 10 ^ 8 := by
  let E : ℝ := 1.3 * Real.sqrt x * Real.log x
  let F : ℝ := 10 ^ 8
  let r : ℝ := (piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)
  let θ : ℝ := r / (E + F)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hEF : 0 < E + F := by dsimp [E, F]; positivity
  have hr : |r| ≤ E + F := prop14_error_bound hG hq hl hx hqx
  have hθ : |θ| ≤ 1 := by
    dsimp [θ]
    rw [abs_div, abs_of_pos hEF, div_le_one hEF]
    exact hr
  have he : r = E*θ + F*θ := by
    dsimp [θ]
    field_simp [hEF.ne']
    <;> ring
  refine ⟨θ, θ, hθ, hθ, ?_⟩
  calc
    (piMod x q l : ℝ) = zinLi x / (Nat.totient q : ℝ) + r := by dsimp [r]; ring
    _ = zinLi x / (Nat.totient q : ℝ) + (E*θ + F*θ) := by rw [← he]
    _ = _ := by dsimp [E, F]; ring

end LeanLab.Zinoviev1997.State1546

namespace LeanLab.Zinoviev1997.State1546.Task705
open MeasureTheory

/-- The progression Mangoldt sum is nonnegative and is at most ordinary psi.
Supporting the lower interval estimate on p. 341. -/
theorem progression_psi_bounds (u : ℝ) (q l : ℕ) :
    0 ≤ Decomp575b.psiMod u q l ∧ Decomp575b.psiMod u q l ≤ Chebyshev.psi u := by
  constructor
  · unfold Decomp575b.psiMod
    exact Finset.sum_nonneg (fun n hn => by split_ifs <;>
      simp [ArithmeticFunction.vonMangoldt_nonneg])
  · rw [Chebyshev.psi_eq_sum_Icc]
    unfold Decomp575b.psiMod
    apply Finset.sum_le_sum
    intro n hn
    split_ifs
    · exact le_rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg

/-- A uniform elementary centered error for the bounded lower interval on p. 341. -/
theorem progression_error_trivial {u : ℝ} (hu : 0 ≤ u) {q : ℕ} (hq : 1 ≤ q) (l : ℕ) :
    |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| ≤ 6 * u := by
  have hφ : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hmain : 0 ≤ u / (Nat.totient q : ℝ) := div_nonneg hu (by positivity)
  have hmain' : u / (Nat.totient q : ℝ) ≤ u := div_le_self hu hφ
  have hψ := progression_psi_bounds u q l
  have hupper := Chebyshev.psi_le_const_mul_self hu
  have hlog : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_lt_d9]
  rw [abs_le]
  constructor <;> nlinarith

/-- Integrability of the absolute centered progression kernel on p. 341. -/
theorem progression_error_kernel_integrable {x : ℝ} (hx : 2 ≤ x) (q l : ℕ) :
    IntervalIntegrable (fun u : ℝ =>
      |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| /
        (u * Real.log u ^ 2)) volume 2 x := by
  have hi := (Decomp575b.psiMod_kernel_integrable hx q l).sub
    ((Decomp575b.logarithmic_kernels hx).1.div_const (Nat.totient q : ℝ))
  have he : IntervalIntegrable (fun u : ℝ =>
      (Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)) /
        (u * Real.log u ^ 2)) volume 2 x := by
    apply (intervalIntegrable_congr (g := fun u : ℝ =>
      Decomp575b.psiMod u q l / (u * Real.log u ^ 2) -
        (1 / Real.log u ^ 2) / (Nat.totient q : ℝ)) ?_).mpr hi
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [Set.uIoc_of_le hx] at hu
      linarith [hu.1]
    field_simp
  apply (intervalIntegrable_congr (g := fun u : ℝ =>
    |(Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)) /
      (u * Real.log u ^ 2)|) ?_).mpr he.abs
  intro u hu
  have hu0 : 0 ≤ u := by
    rw [Set.uIoc_of_le hx] at hu
    linarith [hu.1]
  dsimp only
  rw [abs_div, abs_of_nonneg (mul_nonneg hu0 (sq_nonneg _))]

/-- Elementary domination of the absolute error kernel used below the cutoff on p. 341. -/
theorem progression_error_kernel_trivial {u : ℝ} (hu : 2 ≤ u) {q : ℕ}
    (hq : 1 ≤ q) (l : ℕ) :
    |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| /
      (u * Real.log u ^ 2) ≤ 6 / Real.log u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have hlog : 0 < Real.log u := Real.log_pos (by linarith)
  calc
    _ ≤ (6 * u) / (u * Real.log u ^ 2) :=
      div_le_div_of_nonneg_right (progression_error_trivial hu0.le hq l) (by positivity)
    _ = _ := by field_simp <;> ring

/-- The entire bounded lower interval costs less than the reserved constant on p. 341.
This supporting estimate uses the elementary six times u bound, without GRH. -/
theorem progression_lower_integral {q : ℕ} (hq : 1 ≤ q) (l : ℕ) :
    (∫ u in (2 : ℝ)..(10 ^ 9 : ℝ),
      |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| /
        (u * Real.log u ^ 2)) ≤ 7 * 10 ^ 7 := by
  let f : ℝ → ℝ := fun u =>
    |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| /
      (u * Real.log u ^ 2)
  have hi : IntervalIntegrable f volume 2 (10 ^ 9) :=
    progression_error_kernel_integrable (by norm_num) q l
  have hsmall : IntervalIntegrable f volume 2 (10 ^ 6) := by
    apply hi.mono_set
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 10 ^ 6)] at hu
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 10 ^ 9)]
    exact ⟨hu.1, hu.2.trans (by norm_num)⟩
  have hlarge : IntervalIntegrable f volume (10 ^ 6) (10 ^ 9) := by
    apply hi.mono_set
    rw [Set.uIcc_of_le (by norm_num : (10 ^ 6 : ℝ) ≤ 10 ^ 9),
      Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 10 ^ 9)]
    exact Set.Icc_subset_Icc_left (by norm_num)
  have h1 : (∫ u in (2 : ℝ)..(10 ^ 6 : ℝ), f u) ≤ 16 * (10 ^ 6 - 2) := by
    calc
      _ ≤ ∫ _u in (2 : ℝ)..(10 ^ 6 : ℝ), (16 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hsmall intervalIntegrable_const
        intro u hu
        apply (progression_error_kernel_trivial hu.1 hq l).trans
        have hlog : (0.69 : ℝ) ≤ Real.log u := by
          exact (show (0.69 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
            (Real.log_le_log (by norm_num) hu.1)
        apply (div_le_iff₀ (by positivity : 0 < Real.log u ^ 2)).mpr
        nlinarith
      _ = _ := by simp <;> ring
  have h2 : (∫ u in (10 ^ 6 : ℝ)..(10 ^ 9 : ℝ), f u) ≤
      (1 / 20 : ℝ) * (10 ^ 9 - 10 ^ 6) := by
    calc
      _ ≤ ∫ _u in (10 ^ 6 : ℝ)..(10 ^ 9 : ℝ), (1 / 20 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hlarge intervalIntegrable_const
        intro u hu
        apply (progression_error_kernel_trivial (by linarith [hu.1]) hq l).trans
        have hlog : (12 : ℝ) ≤ Real.log u := by
          have hpow : (2 : ℝ) ^ 18 ≤ u := by linarith [hu.1]
          have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 18) hpow
          rw [Real.log_pow] at hh
          norm_num only [Nat.cast_ofNat] at hh
          linarith [Real.log_two_gt_d9]
        apply (div_le_iff₀ (by positivity : 0 < Real.log u ^ 2)).mpr
        nlinarith
      _ = _ := by simp; ring
  change (∫ u in (2 : ℝ)..(10 ^ 9 : ℝ), f u) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hsmall hlarge]
  norm_num at h1 h2 ⊢
  linarith

/-- The elementary integral transfer in Proposition 1.4, p. 341.
CONDITIONAL ON the displayed uniform progression estimate throughout the upper interval.
The endpoint modulus condition alone does not supply this hypothesis. -/
theorem progression_integral_of_uniform {q l : ℕ} (hq : 1 ≤ q) {x : ℝ}
    (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| ≤
        0.85 * Real.sqrt u * Real.log u ^ 2) :
    (∫ u in (2 : ℝ)..x,
      |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| /
        (u * Real.log u ^ 2)) ≤
      0.1 * Real.sqrt x * Real.log x + 10 ^ 8 -
        2 / ((Nat.totient q : ℝ) * Real.log 2) := by
  let f : ℝ → ℝ := fun u =>
    |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| /
      (u * Real.log u ^ 2)
  have hx2 : 2 ≤ x := by linarith
  have hi : IntervalIntegrable f volume 2 x :=
    progression_error_kernel_integrable hx2 q l
  have hi0 : IntervalIntegrable f volume 2 (10 ^ 9) :=
    progression_error_kernel_integrable (by norm_num) q l
  have hi1 : IntervalIntegrable f volume (10 ^ 9) x := by
    apply hi.mono_set
    rw [Set.uIcc_of_le hx, Set.uIcc_of_le hx2]
    exact Set.Icc_subset_Icc_left (by norm_num)
  have hg : IntervalIntegrable (fun u : ℝ => 0.85 / Real.sqrt u) volume (10 ^ 9) x := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
    intro u hu
    rw [Set.uIcc_of_le hx] at hu
    exact (Real.sqrt_pos.mpr (by linarith [hu.1])).ne'
  have hup : (∫ u in (10 ^ 9 : ℝ)..x, f u) ≤ 1.7 * Real.sqrt x := by
    have hm := intervalIntegral.integral_mono_on hx hi1 hg (fun u hu => by
      have hu0 : 0 < u := by linarith [hu.1]
      have hlog : 0 < Real.log u := Real.log_pos (by linarith [hu.1])
      apply (div_le_div_of_nonneg_right (hB u hu) (by positivity : 0 ≤ u * Real.log u ^ 2)).trans
      have hs := Real.sq_sqrt hu0.le
      have hsp : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
      apply le_of_eq
      field_simp
      nlinarith)
    have he : (∫ u in (10 ^ 9 : ℝ)..x, 0.85 / Real.sqrt u) =
        1.7 * (Real.sqrt x - Real.sqrt (10 ^ 9)) := by
      have hc : (∫ u in (10 ^ 9 : ℝ)..x, 0.85 / Real.sqrt u) =
          ∫ u in (10 ^ 9 : ℝ)..x, 0.85 * u ^ ((-1 : ℝ) / 2) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hx] at hu
        change 0.85 / Real.sqrt u = 0.85 * u ^ ((-1 : ℝ) / 2)
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg (by linarith [hu.1] : 0 ≤ u)]
        norm_num
      rw [hc, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
      norm_num only [show (-1 : ℝ) / 2 + 1 = (1 : ℝ) / 2 by norm_num]
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      ring
    rw [he] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (Real.sqrt_nonneg _)) (by norm_num))
  have hφ : (1 : ℝ) ≤ Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hconst : 2 / ((Nat.totient q : ℝ) * Real.log 2) ≤ 3 := by
    have hl : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hφ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  have hL : 20 ≤ Real.log x := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 29)
      (show (2 : ℝ) ^ 29 ≤ x by norm_num at hx ⊢; linarith)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_gt_d9]
  change (∫ u in (2 : ℝ)..x, f u) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  have hlow := progression_lower_integral hq l
  change (∫ u in (2 : ℝ)..(10 ^ 9 : ℝ), f u) ≤ _ at hlow
  norm_num at hlow hup ⊢
  nlinarith [mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg x), Real.sqrt_nonneg x]

/-- Costa and Pereira plus the elementary Chebyshev upper bound give this
supporting prime power mass estimate for p. 340. -/
theorem psi_sub_theta_six_sqrt {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 6 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have h30 : (30 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hx0 (by norm_num : (0 : ℝ) < 6)).mpr
    norm_num at hx ⊢
    linarith
  have h3 : x ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt x / 30 := by
    have he : Real.sqrt x = x ^ ((6 : ℝ)⁻¹) * x ^ ((3 : ℝ)⁻¹) := by
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < x), Real.sqrt_eq_rpow]
      norm_num
    rw [he, le_div_iff₀ (by norm_num : (0 : ℝ) < 30)]
    nlinarith [Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹)]
  have h5 : x ^ ((5 : ℝ)⁻¹) ≤ x ^ ((3 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hp (y : ℝ) (hy : 0 ≤ y) : Chebyshev.psi y ≤ 5.4 * y := by
    have h := Chebyshev.psi_le_const_mul_self hy
    have hlog : Real.log (4 : ℝ) ≤ 1.4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      linarith [Real.log_two_lt_d9]
    nlinarith
  have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  rw [show ((2 : ℝ)⁻¹) = (1 : ℝ) / 2 by norm_num, ← Real.sqrt_eq_rpow] at hcp
  nlinarith [hp (Real.sqrt x) (Real.sqrt_nonneg x),
    hp (x ^ ((3 : ℝ)⁻¹)) (Real.rpow_nonneg hx0 _),
    hp (x ^ ((5 : ℝ)⁻¹)) (Real.rpow_nonneg hx0 _), Real.sqrt_nonneg x]


open Decomp575b ArithmeticFunction in
/-- The sharper global prime power correction discharges the burst Abel budget on p. 340. -/
theorem progression_prime_power_error {x : ℝ} (hx : 10 ^ 9 ≤ x) (q l : ℕ) :
    |Decomp575b.weightedMod x q l - (piMod x q l : ℝ)| ≤
      0.1 * Real.sqrt x * Real.log x := by
  rw [abs_of_nonneg (Decomp575b.correction_nonneg x q l)]
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hterm : ∀ n : ℕ,
      (if ¬n.Prime ∧ n % q = l % q then vonMangoldt n / Real.log n else 0) ≤
      (if (n : ℝ) ≤ Real.sqrt x then 1 else 0) +
        2 / Real.log x * (if ¬n.Prime then vonMangoldt n else 0) := by
    intro n
    by_cases hn : (n : ℝ) ≤ Real.sqrt x
    · have hpos : 0 ≤ 2 / Real.log x * (if ¬n.Prime then vonMangoldt n else 0) := by
        positivity
      rw [ite_eq_left hn]
      have ha : (if ¬n.Prime ∧ n % q = l % q then vonMangoldt n / Real.log n else 0) ≤ 1 := by
        split_ifs
        · exact (mangoldt_log_ratio n).2
        · norm_num
      exact ha.trans (le_add_of_nonneg_right hpos)
    · have hn0 : 0 < (n : ℝ) := lt_trans hsqrt (lt_of_not_ge hn)
      have hln : Real.log x / 2 ≤ Real.log n := by
        rw [← Real.log_sqrt hx0.le]
        exact Real.log_le_log hsqrt (le_of_lt (lt_of_not_ge hn))
      have hln0 : 0 < Real.log (n : ℝ) := by linarith
      rw [ite_eq_right hn]
      by_cases hp : ¬n.Prime ∧ n % q = l % q
      · simp only [ite_eq_left hp, ite_eq_left hp.1, zero_add]
        have hv : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
        have he : vonMangoldt n / Real.log n ≤ 2 / Real.log x * vonMangoldt n := by
          rw [div_le_iff₀ hln0]
          have hh := mul_le_mul_of_nonneg_left hln hv
          field_simp
          nlinarith
        exact he
      · rw [ite_eq_right hp]
        positivity
  rw [correction_eq]
  calc
    _ ≤ ∑ n ∈ Finset.Iic ⌊x⌋₊,
        ((if (n : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) +
          2 / Real.log x * (if ¬n.Prime then vonMangoldt n else 0)) :=
      Finset.sum_le_sum (fun n hn => hterm n)
    _ = (∑ n ∈ Finset.Iic ⌊x⌋₊, if (n : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) +
        2 / Real.log x * (Chebyshev.psi x - Chebyshev.theta x) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, mangoldt_nonprime_sum]
    _ ≤ Real.sqrt x + 1 + 2 / Real.log x * (6 * Real.sqrt x) := by
      apply add_le_add
      · have hh : ((Finset.Iic ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt x)).card ≤
            (Finset.Iic ⌊Real.sqrt x⌋₊).card := by
          apply Finset.card_le_card
          intro n hn
          exact Finset.mem_Iic.mpr (Nat.le_floor (Finset.mem_filter.mp hn).2)
        simp only [Nat.card_Iic] at hh
        have hh' : (∑ n ∈ Finset.Iic ⌊x⌋₊, if (n : ℝ) ≤ Real.sqrt x then (1 : ℝ) else 0) ≤
            (⌊Real.sqrt x⌋₊ : ℝ) + 1 := by
          have hcast : (((Finset.Iic ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ Real.sqrt x)).card : ℝ) ≤
              (⌊Real.sqrt x⌋₊ : ℝ) + 1 := by exact_mod_cast hh
          simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hcast
        exact hh'.trans (by linarith [Nat.floor_le hsqrt.le])
      · exact mul_le_mul_of_nonneg_left (psi_sub_theta_six_sqrt hx) (by positivity)
    _ ≤ _ := by
      have hL : 20 ≤ Real.log x := by
        have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 29)
          (show (2 : ℝ) ^ 29 ≤ x by norm_num at hx ⊢; linarith)
        rw [Real.log_pow] at hh
        norm_num only [Nat.cast_ofNat] at hh
        linarith [Real.log_two_gt_d9]
      have hs : 10 ≤ Real.sqrt x := by
        rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) by norm_num]
        exact Real.sqrt_le_sqrt (by linarith)
      have hsmall : 2 / Real.log x * (6 * Real.sqrt x) ≤ 0.6 * Real.sqrt x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hlog]
        nlinarith [mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg x)]
      nlinarith [mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg x)]

/-- The Abel and prime power leaf of the Claude burst, p. 340, display 1.10.
The supporting coefficient 0.1 uses no GRH or progression estimate. -/
theorem prop14_abel {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x) :
    |(piMod x q l : ℝ) - (Decomp575b.psiMod x q l / Real.log x +
        ∫ u in (2 : ℝ)..x, Decomp575b.psiMod u q l / (u * Real.log u ^ 2))| ≤
      0.1 * Real.sqrt x * Real.log x := by
  rw [← Decomp575b.weightedMod_abel (show 2 ≤ x by linarith) q l, abs_sub_comm]
  exact progression_prime_power_error hx q l

/-- The elementary remainder leaf of the Claude burst, p. 341.
CONDITIONAL ON the uniform progression estimate supplied explicitly in hB. -/
theorem prop14_remainder {q l : ℕ} (hq : 1 ≤ q) {x : ℝ} (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| ≤
        0.85 * Real.sqrt u * Real.log u ^ 2) :
    |(∫ u in (2 : ℝ)..x, Decomp575b.psiMod u q l / (u * Real.log u ^ 2)) -
        (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) / (Nat.totient q : ℝ)| ≤
      0.15 * Real.sqrt x * Real.log x + (10 ^ 8 - 3) := by
  have hx2 : 2 ≤ x := by linarith
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have he : (∫ u in (2 : ℝ)..x, Decomp575b.psiMod u q l / (u * Real.log u ^ 2)) -
      (∫ u in (2 : ℝ)..x, 1 / Real.log u ^ 2) / (Nat.totient q : ℝ) =
      ∫ u in (2 : ℝ)..x,
        (Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)) / (u * Real.log u ^ 2) := by
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      (Decomp575b.psiMod_kernel_integrable hx2 q l)
      ((Decomp575b.logarithmic_kernels hx2).1.div_const _)]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by
      rw [Set.uIcc_of_le hx2] at hu
      linarith [hu.1]
    dsimp only
    field_simp
  have ht := (Decomp575b.centered_integral_abs hx2 q l).trans
    (progression_integral_of_uniform hq hx hB)
  rw [← he] at ht
  apply ht.trans
  have hs : 10 ≤ Real.sqrt x := by
    rw [show (10 : ℝ) = Real.sqrt (10 ^ 2) by norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  have hL : 20 ≤ Real.log x := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 29)
      (show (2 : ℝ) ^ 29 ≤ x by norm_num at hx ⊢; linarith)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_gt_d9]
  have hC : 0 ≤ 2 / ((Nat.totient q : ℝ) * Real.log 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg x)]

/-- The p. 340 character average retains the proportion of nonprincipal characters.
CONDITIONAL ON the supplied primitive character estimates, with no Schoenfeld input. -/
theorem progression_orthogonality_explicit {q l : ℕ} (hq : 3 ≤ q)
    (hl : Nat.Coprime l q) {u : ℝ} (hu : 10 ^ 9 ≤ u)
    (hqu : (q : ℝ) ≤ u ^ (0.37 : ℝ))
    (h13 : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), χ.IsPrimitive →
      3 ≤ k → k ∣ q → ‖psiChi χ u‖ ≤ 0.83 * Real.sqrt u * Real.log u ^ 2) :
    |Decomp575b.psiMod u q l - Chebyshev.psi u / (Nat.totient q : ℝ)| ≤
      ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) *
        0.83 * Real.sqrt u * Real.log u ^ 2 + 2 * Real.log u ^ 2 := by
  classical
  have : NeZero q := ⟨by omega⟩
  let B : ℝ := 0.83 * Real.sqrt u * Real.log u ^ 2
  let C : ℝ := Real.log u ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hprincipal : ‖psiChi (1 : DirichletCharacter ℂ q) u - (Chebyshev.psi u : ℂ)‖ ≤ C := by
    have hd := Decomp575c.induced_psi_difference (q := q) (d := 1) (one_dvd q)
      (1 : DirichletCharacter ℂ 1) hu hqu
    rw [DirichletCharacter.changeLevel_one, Decomp575c.psiChi_level_one] at hd
    exact hd
  have hnonprincipal (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : ‖psiChi χ u‖ ≤ B + C := by
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hp := h13 χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      (Decomp575c.nonprincipal_conductor χ hχ) χ.conductor_dvd_level
    have hd := Decomp575c.induced_psi_difference χ.conductor_dvd_level χ.primitiveCharacter hu hqu
    rw [χ.changeLevel_primitiveCharacter] at hd
    have ht := norm_add_le (psiChi χ u - psiChi χ.primitiveCharacter u) (psiChi χ.primitiveCharacter u)
    rw [sub_add_cancel] at ht
    calc
      _ ≤ ‖psiChi χ u - psiChi χ.primitiveCharacter u‖ + ‖psiChi χ.primitiveCharacter u‖ := ht
      _ ≤ C + B := add_le_add hd hp
      _ = B + C := add_comm _ _
  have hlunit : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  have hlinv : IsUnit ((l : ZMod q)⁻¹) := by
    rcases hlunit with ⟨v, hv⟩
    rw [← hv, ZMod.inv_coe_unit]
    exact Units.isUnit _
  have hmain : (∑ χ : DirichletCharacter ℂ q,
      χ ((l : ZMod q)⁻¹) * (if χ = 1 then (Chebyshev.psi u : ℂ) else 0)) =
        (Chebyshev.psi u : ℂ) := by
    simp [MulChar.one_apply hlinv]
  have he : (Nat.totient q : ℂ) * (Decomp575b.psiMod u q l : ℂ) - (Chebyshev.psi u : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((l : ZMod q)⁻¹) *
        (psiChi χ u - if χ = 1 then (Chebyshev.psi u : ℂ) else 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hmain, Decomp575b.progression_orthogonality hl u]
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hsum : (∑ χ : DirichletCharacter ℂ q, if χ = 1 then C else B + C) =
      (Nat.totient q : ℝ) * (B + C) - B := by
    calc
      _ = ∑ χ : DirichletCharacter ℂ q, ((B + C) - if χ = 1 then B else 0) := by
        apply Finset.sum_congr rfl
        intro χ hχ
        split_ifs <;> ring
      _ = _ := by simp [Finset.sum_sub_distrib, hcard] <;> ring
  have hn : ‖(Nat.totient q : ℂ) * (Decomp575b.psiMod u q l : ℂ) - (Chebyshev.psi u : ℂ)‖ ≤
      (Nat.totient q : ℝ) * (B + C) - B := by
    rw [he, ← hsum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro χ hχ
    have hw := mul_le_mul_of_nonneg_right (χ.norm_le_one ((l : ZMod q)⁻¹))
      (norm_nonneg (psiChi χ u - if χ = 1 then (Chebyshev.psi u : ℂ) else 0))
    rw [one_mul] at hw
    rw [norm_mul]
    apply hw.trans
    by_cases h : χ = 1
    · simpa [h] using hprincipal
    · simpa [h] using hnonprincipal χ h
  have he' : (Nat.totient q : ℂ) * (Decomp575b.psiMod u q l : ℂ) - (Chebyshev.psi u : ℂ) =
      ((Nat.totient q : ℝ) *
        (Decomp575b.psiMod u q l - Chebyshev.psi u / (Nat.totient q : ℝ)) : ℝ) := by
    have hpC : (Nat.totient q : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    push_cast
    field_simp [hpC]
  rw [he', Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hφ] at hn
  have hr : |Decomp575b.psiMod u q l - Chebyshev.psi u / (Nat.totient q : ℝ)| ≤
      ((Nat.totient q : ℝ) * (B + C) - B) / (Nat.totient q : ℝ) := by
    apply (le_div_iff₀ hφ).mpr
    nlinarith
  have heq : ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) * B + 2 * C =
      ((Nat.totient q : ℝ) * (B + C) - B) / (Nat.totient q : ℝ) + C := by
    field_simp [hφ.ne'] <;> ring
  have hres := hr.trans (show ((Nat.totient q : ℝ) * (B + C) - B) / (Nat.totient q : ℝ) ≤
      ((Nat.totient q : ℝ) - 1) / (Nat.totient q : ℝ) * B + 2 * C by rw [heq]; linarith)
  convert hres using 1 <;> dsimp [B, C] <;> ring

/-- A positive length concrete domain for the uniform integral transfer.
The large modulus is a diagnostic for that transfer and is not in Proposition 1.4's endpoint range. -/
theorem uniform_progression_instance :
    (1 : ℕ) ≤ 2 ^ 40 ∧ Nat.Coprime 1 (2 ^ 40) ∧
      ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) (10 ^ 9 + 1),
        |Decomp575b.psiMod u (2 ^ 40) 1 - u / (Nat.totient (2 ^ 40) : ℝ)| ≤
          0.85 * Real.sqrt u * Real.log u ^ 2 := by
  refine ⟨by norm_num, by simp, ?_⟩
  intro u hu
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hzero : Decomp575b.psiMod u (2 ^ 40) 1 = 0 := by
    unfold Decomp575b.psiMod
    apply Finset.sum_eq_zero
    intro n hn
    split_ifs with he
    · have hnu : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0).mp (Finset.mem_Iic.mp hn)
      have hnlt : n < 2 ^ 40 := by
        have hbig : (10 ^ 9 : ℝ) + 1 < ((2 ^ 40 : ℕ) : ℝ) := by norm_num
        have hnreal : (n : ℝ) < ((2 ^ 40 : ℕ) : ℝ) := hnu.trans_lt (hu.2.trans_lt hbig)
        exact_mod_cast hnreal
      rw [Nat.mod_eq_of_lt hnlt] at he
      norm_num at he
      simp [he]
    · rfl
  have hφ : Nat.totient (2 ^ 40) = 2 ^ 39 := by
    rw [Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < (40 : ℕ))]
    norm_num
  have hmain : u / (Nat.totient (2 ^ 40) : ℝ) ≤ 1 := by
    rw [hφ]
    apply (div_le_one (by positivity)).mpr
    exact hu.2.trans (by norm_num)
  have hL : 20 ≤ Real.log u := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 29)
      (show (2 : ℝ) ^ 29 ≤ u by norm_num at hu ⊢; linarith [hu.1])
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.log_two_gt_d9]
  have hs : 1 ≤ Real.sqrt u := Real.one_le_sqrt.mpr (by linarith [hu.1])
  have hφpos : (0 : ℝ) < Nat.totient (2 ^ 40) := by rw [hφ]; positivity
  rw [hzero, zero_sub, abs_neg, abs_of_nonneg (div_nonneg hu0 hφpos.le)]
  have hLs : 400 ≤ Real.log u ^ 2 := by nlinarith only [hL]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.log u))
  exact hmain.trans (by nlinarith only [hLs, hm])

/-- Proposition 1.4 follows from the explicit uniform upper interval estimate.
CONDITIONAL ON that estimate. All Abel and scalar steps are proved. -/
theorem prop14_error_bound_of_uniform {q l : ℕ} (hq : 1 ≤ q) {x : ℝ}
    (hx : 10 ^ 9 ≤ x)
    (hB : ∀ u ∈ Set.Icc (10 ^ 9 : ℝ) x,
      |Decomp575b.psiMod u q l - u / (Nat.totient q : ℝ)| ≤
        0.85 * Real.sqrt u * Real.log u ^ 2) :
    |(piMod x q l : ℝ) - zinLi x / (Nat.totient q : ℝ)| ≤
      1.3 * Real.sqrt x * Real.log x + 10 ^ 8 := by
  exact Decomp575b.error_bound_of_budgets hq (by linarith)
    (hB x ⟨hx, le_rfl⟩) (progression_integral_of_uniform hq hx hB)
    (Decomp575b.weighted_prime_power_error hx)

/-- A failed route diagnostic for p. 341. The elementary six times u majorant
already exceeds the desired uniform square root budget at the lower cutoff. -/
theorem trivial_bound_exceeds_uniform_budget :
    0.85 * Real.sqrt (10 ^ 9 : ℝ) * Real.log (10 ^ 9 : ℝ) ^ 2 <
      6 * (10 ^ 9 : ℝ) := by
  have hs : Real.sqrt (10 ^ 9 : ℝ) ≤ 100000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hL : Real.log (10 ^ 9 : ℝ) ≤ 81 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hLn : 0 ≤ Real.log (10 ^ 9 : ℝ) := Real.log_nonneg (by norm_num)
  have hLs : Real.log (10 ^ 9 : ℝ) ^ 2 ≤ 6561 := by nlinarith only [hL, hLn]
  have hm := mul_le_mul hs hLs (sq_nonneg (Real.log (10 ^ 9 : ℝ)))
    (by norm_num : (0 : ℝ) ≤ 100000)
  norm_num at hm ⊢
  nlinarith only [hm]

end LeanLab.Zinoviev1997.State1546.Task705
